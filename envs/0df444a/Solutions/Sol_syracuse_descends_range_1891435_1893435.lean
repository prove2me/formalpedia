-- Prove2me | solution 1 for syracuse_descends_range_1891435_1893435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:46:42.009572+00:00
-- url     : https://prove2.me/submissions/d14a1d12-25bb-41a4-bb9c-abfb4394869f

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

theorem B2127865 : Blo 1891435 2127865 := bbase (se 2 (by rfl) ⟨797949, by rfl⟩ : syracuseStep 2127865 = 1595899) (by norm_num)
theorem B2837153 : Blo 1891435 2837153 := bstep (se 2 (by rfl) ⟨1063932, by rfl⟩ : syracuseStep 2837153 = 2127865) B2127865
theorem B1891435 : Blo 1891435 1891435 := bstep (se 1 (by rfl) ⟨1418576, by rfl⟩ : syracuseStep 1891435 = 2837153) B2837153
theorem B3408437 : Blo 1891435 3408437 := bbase (se 5 (by rfl) ⟨159770, by rfl⟩ : syracuseStep 3408437 = 319541) (by norm_num)
theorem B9089165 : Blo 1891435 9089165 := bstep (se 3 (by rfl) ⟨1704218, by rfl⟩ : syracuseStep 9089165 = 3408437) B3408437
theorem B6059443 : Blo 1891435 6059443 := bstep (se 1 (by rfl) ⟨4544582, by rfl⟩ : syracuseStep 6059443 = 9089165) B9089165
theorem B8079257 : Blo 1891435 8079257 := bstep (se 2 (by rfl) ⟨3029721, by rfl⟩ : syracuseStep 8079257 = 6059443) B6059443
theorem B5386171 : Blo 1891435 5386171 := bstep (se 1 (by rfl) ⟨4039628, by rfl⟩ : syracuseStep 5386171 = 8079257) B8079257
theorem B7181561 : Blo 1891435 7181561 := bstep (se 2 (by rfl) ⟨2693085, by rfl⟩ : syracuseStep 7181561 = 5386171) B5386171
theorem B4787707 : Blo 1891435 4787707 := bstep (se 1 (by rfl) ⟨3590780, by rfl⟩ : syracuseStep 4787707 = 7181561) B7181561
theorem B6383609 : Blo 1891435 6383609 := bstep (se 2 (by rfl) ⟨2393853, by rfl⟩ : syracuseStep 6383609 = 4787707) B4787707
theorem B4255739 : Blo 1891435 4255739 := bstep (se 1 (by rfl) ⟨3191804, by rfl⟩ : syracuseStep 4255739 = 6383609) B6383609
theorem B2837159 : Blo 1891435 2837159 := bstep (se 1 (by rfl) ⟨2127869, by rfl⟩ : syracuseStep 2837159 = 4255739) B4255739
theorem B1891439 : Blo 1891435 1891439 := bstep (se 1 (by rfl) ⟨1418579, by rfl⟩ : syracuseStep 1891439 = 2837159) B2837159
theorem B2837165 : Blo 1891435 2837165 := bbase (se 3 (by rfl) ⟨531968, by rfl⟩ : syracuseStep 2837165 = 1063937) (by norm_num)
theorem B1891443 : Blo 1891435 1891443 := bstep (se 1 (by rfl) ⟨1418582, by rfl⟩ : syracuseStep 1891443 = 2837165) B2837165
theorem B4255757 : Blo 1891435 4255757 := bbase (se 3 (by rfl) ⟨797954, by rfl⟩ : syracuseStep 4255757 = 1595909) (by norm_num)
theorem B2837171 : Blo 1891435 2837171 := bstep (se 1 (by rfl) ⟨2127878, by rfl⟩ : syracuseStep 2837171 = 4255757) B4255757
theorem B1891447 : Blo 1891435 1891447 := bstep (se 1 (by rfl) ⟨1418585, by rfl⟩ : syracuseStep 1891447 = 2837171) B2837171
theorem B2393869 : Blo 1891435 2393869 := bbase (se 3 (by rfl) ⟨448850, by rfl⟩ : syracuseStep 2393869 = 897701) (by norm_num)
theorem B3191825 : Blo 1891435 3191825 := bstep (se 2 (by rfl) ⟨1196934, by rfl⟩ : syracuseStep 3191825 = 2393869) B2393869
theorem B2127883 : Blo 1891435 2127883 := bstep (se 1 (by rfl) ⟨1595912, by rfl⟩ : syracuseStep 2127883 = 3191825) B3191825
theorem B2837177 : Blo 1891435 2837177 := bstep (se 2 (by rfl) ⟨1063941, by rfl⟩ : syracuseStep 2837177 = 2127883) B2127883
theorem B1891451 : Blo 1891435 1891451 := bstep (se 1 (by rfl) ⟨1418588, by rfl⟩ : syracuseStep 1891451 = 2837177) B2837177
theorem B2556349 : Blo 1891435 2556349 := bbase (se 3 (by rfl) ⟨479315, by rfl⟩ : syracuseStep 2556349 = 958631) (by norm_num)
theorem B13633861 : Blo 1891435 13633861 := bstep (se 4 (by rfl) ⟨1278174, by rfl⟩ : syracuseStep 13633861 = 2556349) B2556349
theorem B18178481 : Blo 1891435 18178481 := bstep (se 2 (by rfl) ⟨6816930, by rfl⟩ : syracuseStep 18178481 = 13633861) B13633861
theorem B12118987 : Blo 1891435 12118987 := bstep (se 1 (by rfl) ⟨9089240, by rfl⟩ : syracuseStep 12118987 = 18178481) B18178481
theorem B16158649 : Blo 1891435 16158649 := bstep (se 2 (by rfl) ⟨6059493, by rfl⟩ : syracuseStep 16158649 = 12118987) B12118987
theorem B21544865 : Blo 1891435 21544865 := bstep (se 2 (by rfl) ⟨8079324, by rfl⟩ : syracuseStep 21544865 = 16158649) B16158649
theorem B14363243 : Blo 1891435 14363243 := bstep (se 1 (by rfl) ⟨10772432, by rfl⟩ : syracuseStep 14363243 = 21544865) B21544865
theorem B9575495 : Blo 1891435 9575495 := bstep (se 1 (by rfl) ⟨7181621, by rfl⟩ : syracuseStep 9575495 = 14363243) B14363243
theorem B6383663 : Blo 1891435 6383663 := bstep (se 1 (by rfl) ⟨4787747, by rfl⟩ : syracuseStep 6383663 = 9575495) B9575495
theorem B4255775 : Blo 1891435 4255775 := bstep (se 1 (by rfl) ⟨3191831, by rfl⟩ : syracuseStep 4255775 = 6383663) B6383663
theorem B2837183 : Blo 1891435 2837183 := bstep (se 1 (by rfl) ⟨2127887, by rfl⟩ : syracuseStep 2837183 = 4255775) B4255775
theorem B1891455 : Blo 1891435 1891455 := bstep (se 1 (by rfl) ⟨1418591, by rfl⟩ : syracuseStep 1891455 = 2837183) B2837183
theorem B2837189 : Blo 1891435 2837189 := bbase (se 4 (by rfl) ⟨265986, by rfl⟩ : syracuseStep 2837189 = 531973) (by norm_num)
theorem B1891459 : Blo 1891435 1891459 := bstep (se 1 (by rfl) ⟨1418594, by rfl⟩ : syracuseStep 1891459 = 2837189) B2837189
theorem B3191845 : Blo 1891435 3191845 := bbase (se 4 (by rfl) ⟨299235, by rfl⟩ : syracuseStep 3191845 = 598471) (by norm_num)
theorem B4255793 : Blo 1891435 4255793 := bstep (se 2 (by rfl) ⟨1595922, by rfl⟩ : syracuseStep 4255793 = 3191845) B3191845
theorem B2837195 : Blo 1891435 2837195 := bstep (se 1 (by rfl) ⟨2127896, by rfl⟩ : syracuseStep 2837195 = 4255793) B4255793
theorem B1891463 : Blo 1891435 1891463 := bstep (se 1 (by rfl) ⟨1418597, by rfl⟩ : syracuseStep 1891463 = 2837195) B2837195
theorem B2127901 : Blo 1891435 2127901 := bbase (se 3 (by rfl) ⟨398981, by rfl⟩ : syracuseStep 2127901 = 797963) (by norm_num)
theorem B2837201 : Blo 1891435 2837201 := bstep (se 2 (by rfl) ⟨1063950, by rfl⟩ : syracuseStep 2837201 = 2127901) B2127901
theorem B1891467 : Blo 1891435 1891467 := bstep (se 1 (by rfl) ⟨1418600, by rfl⟩ : syracuseStep 1891467 = 2837201) B2837201
theorem B6383717 : Blo 1891435 6383717 := bbase (se 4 (by rfl) ⟨598473, by rfl⟩ : syracuseStep 6383717 = 1196947) (by norm_num)
theorem B4255811 : Blo 1891435 4255811 := bstep (se 1 (by rfl) ⟨3191858, by rfl⟩ : syracuseStep 4255811 = 6383717) B6383717
theorem B2837207 : Blo 1891435 2837207 := bstep (se 1 (by rfl) ⟨2127905, by rfl⟩ : syracuseStep 2837207 = 4255811) B4255811
theorem B1891471 : Blo 1891435 1891471 := bstep (se 1 (by rfl) ⟨1418603, by rfl⟩ : syracuseStep 1891471 = 2837207) B2837207
theorem B2837213 : Blo 1891435 2837213 := bbase (se 3 (by rfl) ⟨531977, by rfl⟩ : syracuseStep 2837213 = 1063955) (by norm_num)
theorem B1891475 : Blo 1891435 1891475 := bstep (se 1 (by rfl) ⟨1418606, by rfl⟩ : syracuseStep 1891475 = 2837213) B2837213
theorem B4255829 : Blo 1891435 4255829 := bbase (se 8 (by rfl) ⟨24936, by rfl⟩ : syracuseStep 4255829 = 49873) (by norm_num)
theorem B2837219 : Blo 1891435 2837219 := bstep (se 1 (by rfl) ⟨2127914, by rfl⟩ : syracuseStep 2837219 = 4255829) B4255829
theorem B1891479 : Blo 1891435 1891479 := bstep (se 1 (by rfl) ⟨1418609, by rfl⟩ : syracuseStep 1891479 = 2837219) B2837219
theorem B3408517 : Blo 1891435 3408517 := bbase (se 4 (by rfl) ⟨319548, by rfl⟩ : syracuseStep 3408517 = 639097) (by norm_num)
theorem B4544689 : Blo 1891435 4544689 := bstep (se 2 (by rfl) ⟨1704258, by rfl⟩ : syracuseStep 4544689 = 3408517) B3408517
theorem B6059585 : Blo 1891435 6059585 := bstep (se 2 (by rfl) ⟨2272344, by rfl⟩ : syracuseStep 6059585 = 4544689) B4544689
theorem B4039723 : Blo 1891435 4039723 := bstep (se 1 (by rfl) ⟨3029792, by rfl⟩ : syracuseStep 4039723 = 6059585) B6059585
theorem B5386297 : Blo 1891435 5386297 := bstep (se 2 (by rfl) ⟨2019861, by rfl⟩ : syracuseStep 5386297 = 4039723) B4039723
theorem B7181729 : Blo 1891435 7181729 := bstep (se 2 (by rfl) ⟨2693148, by rfl⟩ : syracuseStep 7181729 = 5386297) B5386297
theorem B4787819 : Blo 1891435 4787819 := bstep (se 1 (by rfl) ⟨3590864, by rfl⟩ : syracuseStep 4787819 = 7181729) B7181729
theorem B3191879 : Blo 1891435 3191879 := bstep (se 1 (by rfl) ⟨2393909, by rfl⟩ : syracuseStep 3191879 = 4787819) B4787819
theorem B2127919 : Blo 1891435 2127919 := bstep (se 1 (by rfl) ⟨1595939, by rfl⟩ : syracuseStep 2127919 = 3191879) B3191879
theorem B2837225 : Blo 1891435 2837225 := bstep (se 2 (by rfl) ⟨1063959, by rfl⟩ : syracuseStep 2837225 = 2127919) B2127919
theorem B1891483 : Blo 1891435 1891483 := bstep (se 1 (by rfl) ⟨1418612, by rfl⟩ : syracuseStep 1891483 = 2837225) B2837225
theorem B3834589 : Blo 1891435 3834589 := bbase (se 3 (by rfl) ⟨718985, by rfl⟩ : syracuseStep 3834589 = 1437971) (by norm_num)
theorem B5112785 : Blo 1891435 5112785 := bstep (se 2 (by rfl) ⟨1917294, by rfl⟩ : syracuseStep 5112785 = 3834589) B3834589
theorem B3408523 : Blo 1891435 3408523 := bstep (se 1 (by rfl) ⟨2556392, by rfl⟩ : syracuseStep 3408523 = 5112785) B5112785
theorem B18178789 : Blo 1891435 18178789 := bstep (se 4 (by rfl) ⟨1704261, by rfl⟩ : syracuseStep 18178789 = 3408523) B3408523
theorem B24238385 : Blo 1891435 24238385 := bstep (se 2 (by rfl) ⟨9089394, by rfl⟩ : syracuseStep 24238385 = 18178789) B18178789
theorem B16158923 : Blo 1891435 16158923 := bstep (se 1 (by rfl) ⟨12119192, by rfl⟩ : syracuseStep 16158923 = 24238385) B24238385
theorem B10772615 : Blo 1891435 10772615 := bstep (se 1 (by rfl) ⟨8079461, by rfl⟩ : syracuseStep 10772615 = 16158923) B16158923
theorem B7181743 : Blo 1891435 7181743 := bstep (se 1 (by rfl) ⟨5386307, by rfl⟩ : syracuseStep 7181743 = 10772615) B10772615
theorem B9575657 : Blo 1891435 9575657 := bstep (se 2 (by rfl) ⟨3590871, by rfl⟩ : syracuseStep 9575657 = 7181743) B7181743
theorem B6383771 : Blo 1891435 6383771 := bstep (se 1 (by rfl) ⟨4787828, by rfl⟩ : syracuseStep 6383771 = 9575657) B9575657
theorem B4255847 : Blo 1891435 4255847 := bstep (se 1 (by rfl) ⟨3191885, by rfl⟩ : syracuseStep 4255847 = 6383771) B6383771
theorem B2837231 : Blo 1891435 2837231 := bstep (se 1 (by rfl) ⟨2127923, by rfl⟩ : syracuseStep 2837231 = 4255847) B4255847
theorem B1891487 : Blo 1891435 1891487 := bstep (se 1 (by rfl) ⟨1418615, by rfl⟩ : syracuseStep 1891487 = 2837231) B2837231
theorem B2837237 : Blo 1891435 2837237 := bbase (se 5 (by rfl) ⟨132995, by rfl⟩ : syracuseStep 2837237 = 265991) (by norm_num)
theorem B1891491 : Blo 1891435 1891491 := bstep (se 1 (by rfl) ⟨1418618, by rfl⟩ : syracuseStep 1891491 = 2837237) B2837237
theorem B19412693 : Blo 1891435 19412693 := bbase (se 7 (by rfl) ⟨227492, by rfl⟩ : syracuseStep 19412693 = 454985) (by norm_num)
theorem B12941795 : Blo 1891435 12941795 := bstep (se 1 (by rfl) ⟨9706346, by rfl⟩ : syracuseStep 12941795 = 19412693) B19412693
theorem B34511453 : Blo 1891435 34511453 := bstep (se 3 (by rfl) ⟨6470897, by rfl⟩ : syracuseStep 34511453 = 12941795) B12941795
theorem B23007635 : Blo 1891435 23007635 := bstep (se 1 (by rfl) ⟨17255726, by rfl⟩ : syracuseStep 23007635 = 34511453) B34511453
theorem B15338423 : Blo 1891435 15338423 := bstep (se 1 (by rfl) ⟨11503817, by rfl⟩ : syracuseStep 15338423 = 23007635) B23007635
theorem B10225615 : Blo 1891435 10225615 := bstep (se 1 (by rfl) ⟨7669211, by rfl⟩ : syracuseStep 10225615 = 15338423) B15338423
theorem B13634153 : Blo 1891435 13634153 := bstep (se 2 (by rfl) ⟨5112807, by rfl⟩ : syracuseStep 13634153 = 10225615) B10225615
theorem B9089435 : Blo 1891435 9089435 := bstep (se 1 (by rfl) ⟨6817076, by rfl⟩ : syracuseStep 9089435 = 13634153) B13634153
theorem B6059623 : Blo 1891435 6059623 := bstep (se 1 (by rfl) ⟨4544717, by rfl⟩ : syracuseStep 6059623 = 9089435) B9089435
theorem B8079497 : Blo 1891435 8079497 := bstep (se 2 (by rfl) ⟨3029811, by rfl⟩ : syracuseStep 8079497 = 6059623) B6059623
theorem B5386331 : Blo 1891435 5386331 := bstep (se 1 (by rfl) ⟨4039748, by rfl⟩ : syracuseStep 5386331 = 8079497) B8079497
theorem B3590887 : Blo 1891435 3590887 := bstep (se 1 (by rfl) ⟨2693165, by rfl⟩ : syracuseStep 3590887 = 5386331) B5386331
theorem B4787849 : Blo 1891435 4787849 := bstep (se 2 (by rfl) ⟨1795443, by rfl⟩ : syracuseStep 4787849 = 3590887) B3590887
theorem B3191899 : Blo 1891435 3191899 := bstep (se 1 (by rfl) ⟨2393924, by rfl⟩ : syracuseStep 3191899 = 4787849) B4787849
theorem B4255865 : Blo 1891435 4255865 := bstep (se 2 (by rfl) ⟨1595949, by rfl⟩ : syracuseStep 4255865 = 3191899) B3191899
theorem B2837243 : Blo 1891435 2837243 := bstep (se 1 (by rfl) ⟨2127932, by rfl⟩ : syracuseStep 2837243 = 4255865) B4255865
theorem B1891495 : Blo 1891435 1891495 := bstep (se 1 (by rfl) ⟨1418621, by rfl⟩ : syracuseStep 1891495 = 2837243) B2837243
theorem B2127937 : Blo 1891435 2127937 := bbase (se 2 (by rfl) ⟨797976, by rfl⟩ : syracuseStep 2127937 = 1595953) (by norm_num)
theorem B2837249 : Blo 1891435 2837249 := bstep (se 2 (by rfl) ⟨1063968, by rfl⟩ : syracuseStep 2837249 = 2127937) B2127937
theorem B1891499 : Blo 1891435 1891499 := bstep (se 1 (by rfl) ⟨1418624, by rfl⟩ : syracuseStep 1891499 = 2837249) B2837249
theorem B4787869 : Blo 1891435 4787869 := bbase (se 3 (by rfl) ⟨897725, by rfl⟩ : syracuseStep 4787869 = 1795451) (by norm_num)
theorem B6383825 : Blo 1891435 6383825 := bstep (se 2 (by rfl) ⟨2393934, by rfl⟩ : syracuseStep 6383825 = 4787869) B4787869
theorem B4255883 : Blo 1891435 4255883 := bstep (se 1 (by rfl) ⟨3191912, by rfl⟩ : syracuseStep 4255883 = 6383825) B6383825
theorem B2837255 : Blo 1891435 2837255 := bstep (se 1 (by rfl) ⟨2127941, by rfl⟩ : syracuseStep 2837255 = 4255883) B4255883
theorem B1891503 : Blo 1891435 1891503 := bstep (se 1 (by rfl) ⟨1418627, by rfl⟩ : syracuseStep 1891503 = 2837255) B2837255
theorem B2837261 : Blo 1891435 2837261 := bbase (se 3 (by rfl) ⟨531986, by rfl⟩ : syracuseStep 2837261 = 1063973) (by norm_num)
theorem B1891507 : Blo 1891435 1891507 := bstep (se 1 (by rfl) ⟨1418630, by rfl⟩ : syracuseStep 1891507 = 2837261) B2837261
theorem B4255901 : Blo 1891435 4255901 := bbase (se 3 (by rfl) ⟨797981, by rfl⟩ : syracuseStep 4255901 = 1595963) (by norm_num)
theorem B2837267 : Blo 1891435 2837267 := bstep (se 1 (by rfl) ⟨2127950, by rfl⟩ : syracuseStep 2837267 = 4255901) B4255901
theorem B1891511 : Blo 1891435 1891511 := bstep (se 1 (by rfl) ⟨1418633, by rfl⟩ : syracuseStep 1891511 = 2837267) B2837267
theorem B3191933 : Blo 1891435 3191933 := bbase (se 3 (by rfl) ⟨598487, by rfl⟩ : syracuseStep 3191933 = 1196975) (by norm_num)
theorem B2127955 : Blo 1891435 2127955 := bstep (se 1 (by rfl) ⟨1595966, by rfl⟩ : syracuseStep 2127955 = 3191933) B3191933
theorem B2837273 : Blo 1891435 2837273 := bstep (se 2 (by rfl) ⟨1063977, by rfl⟩ : syracuseStep 2837273 = 2127955) B2127955
theorem B1891515 : Blo 1891435 1891515 := bstep (se 1 (by rfl) ⟨1418636, by rfl⟩ : syracuseStep 1891515 = 2837273) B2837273
theorem B3408581 : Blo 1891435 3408581 := bbase (se 4 (by rfl) ⟨319554, by rfl⟩ : syracuseStep 3408581 = 639109) (by norm_num)
theorem B9089549 : Blo 1891435 9089549 := bstep (se 3 (by rfl) ⟨1704290, by rfl⟩ : syracuseStep 9089549 = 3408581) B3408581
theorem B6059699 : Blo 1891435 6059699 := bstep (se 1 (by rfl) ⟨4544774, by rfl⟩ : syracuseStep 6059699 = 9089549) B9089549
theorem B4039799 : Blo 1891435 4039799 := bstep (se 1 (by rfl) ⟨3029849, by rfl⟩ : syracuseStep 4039799 = 6059699) B6059699
theorem B10772797 : Blo 1891435 10772797 := bstep (se 3 (by rfl) ⟨2019899, by rfl⟩ : syracuseStep 10772797 = 4039799) B4039799
theorem B14363729 : Blo 1891435 14363729 := bstep (se 2 (by rfl) ⟨5386398, by rfl⟩ : syracuseStep 14363729 = 10772797) B10772797
theorem B9575819 : Blo 1891435 9575819 := bstep (se 1 (by rfl) ⟨7181864, by rfl⟩ : syracuseStep 9575819 = 14363729) B14363729
theorem B6383879 : Blo 1891435 6383879 := bstep (se 1 (by rfl) ⟨4787909, by rfl⟩ : syracuseStep 6383879 = 9575819) B9575819
theorem B4255919 : Blo 1891435 4255919 := bstep (se 1 (by rfl) ⟨3191939, by rfl⟩ : syracuseStep 4255919 = 6383879) B6383879
theorem B2837279 : Blo 1891435 2837279 := bstep (se 1 (by rfl) ⟨2127959, by rfl⟩ : syracuseStep 2837279 = 4255919) B4255919
theorem B1891519 : Blo 1891435 1891519 := bstep (se 1 (by rfl) ⟨1418639, by rfl⟩ : syracuseStep 1891519 = 2837279) B2837279
theorem B2837285 : Blo 1891435 2837285 := bbase (se 4 (by rfl) ⟨265995, by rfl⟩ : syracuseStep 2837285 = 531991) (by norm_num)
theorem B1891523 : Blo 1891435 1891523 := bstep (se 1 (by rfl) ⟨1418642, by rfl⟩ : syracuseStep 1891523 = 2837285) B2837285
theorem B2393965 : Blo 1891435 2393965 := bbase (se 3 (by rfl) ⟨448868, by rfl⟩ : syracuseStep 2393965 = 897737) (by norm_num)
theorem B3191953 : Blo 1891435 3191953 := bstep (se 2 (by rfl) ⟨1196982, by rfl⟩ : syracuseStep 3191953 = 2393965) B2393965
theorem B4255937 : Blo 1891435 4255937 := bstep (se 2 (by rfl) ⟨1595976, by rfl⟩ : syracuseStep 4255937 = 3191953) B3191953
theorem B2837291 : Blo 1891435 2837291 := bstep (se 1 (by rfl) ⟨2127968, by rfl⟩ : syracuseStep 2837291 = 4255937) B4255937
theorem B1891527 : Blo 1891435 1891527 := bstep (se 1 (by rfl) ⟨1418645, by rfl⟩ : syracuseStep 1891527 = 2837291) B2837291
theorem B2127973 : Blo 1891435 2127973 := bbase (se 4 (by rfl) ⟨199497, by rfl⟩ : syracuseStep 2127973 = 398995) (by norm_num)
theorem B2837297 : Blo 1891435 2837297 := bstep (se 2 (by rfl) ⟨1063986, by rfl⟩ : syracuseStep 2837297 = 2127973) B2127973
theorem B1891531 : Blo 1891435 1891531 := bstep (se 1 (by rfl) ⟨1418648, by rfl⟩ : syracuseStep 1891531 = 2837297) B2837297
theorem B2019917 : Blo 1891435 2019917 := bbase (se 3 (by rfl) ⟨378734, by rfl⟩ : syracuseStep 2019917 = 757469) (by norm_num)
theorem B5386445 : Blo 1891435 5386445 := bstep (se 3 (by rfl) ⟨1009958, by rfl⟩ : syracuseStep 5386445 = 2019917) B2019917
theorem B3590963 : Blo 1891435 3590963 := bstep (se 1 (by rfl) ⟨2693222, by rfl⟩ : syracuseStep 3590963 = 5386445) B5386445
theorem B2393975 : Blo 1891435 2393975 := bstep (se 1 (by rfl) ⟨1795481, by rfl⟩ : syracuseStep 2393975 = 3590963) B3590963
theorem B6383933 : Blo 1891435 6383933 := bstep (se 3 (by rfl) ⟨1196987, by rfl⟩ : syracuseStep 6383933 = 2393975) B2393975
theorem B4255955 : Blo 1891435 4255955 := bstep (se 1 (by rfl) ⟨3191966, by rfl⟩ : syracuseStep 4255955 = 6383933) B6383933
theorem B2837303 : Blo 1891435 2837303 := bstep (se 1 (by rfl) ⟨2127977, by rfl⟩ : syracuseStep 2837303 = 4255955) B4255955
theorem B1891535 : Blo 1891435 1891535 := bstep (se 1 (by rfl) ⟨1418651, by rfl⟩ : syracuseStep 1891535 = 2837303) B2837303
theorem B2837309 : Blo 1891435 2837309 := bbase (se 3 (by rfl) ⟨531995, by rfl⟩ : syracuseStep 2837309 = 1063991) (by norm_num)
theorem B1891539 : Blo 1891435 1891539 := bstep (se 1 (by rfl) ⟨1418654, by rfl⟩ : syracuseStep 1891539 = 2837309) B2837309
theorem B4255973 : Blo 1891435 4255973 := bbase (se 4 (by rfl) ⟨398997, by rfl⟩ : syracuseStep 4255973 = 797995) (by norm_num)
theorem B2837315 : Blo 1891435 2837315 := bstep (se 1 (by rfl) ⟨2127986, by rfl⟩ : syracuseStep 2837315 = 4255973) B4255973
theorem B1891543 : Blo 1891435 1891543 := bstep (se 1 (by rfl) ⟨1418657, by rfl⟩ : syracuseStep 1891543 = 2837315) B2837315
theorem B4787981 : Blo 1891435 4787981 := bbase (se 3 (by rfl) ⟨897746, by rfl⟩ : syracuseStep 4787981 = 1795493) (by norm_num)
theorem B3191987 : Blo 1891435 3191987 := bstep (se 1 (by rfl) ⟨2393990, by rfl⟩ : syracuseStep 3191987 = 4787981) B4787981
theorem B2127991 : Blo 1891435 2127991 := bstep (se 1 (by rfl) ⟨1595993, by rfl⟩ : syracuseStep 2127991 = 3191987) B3191987
theorem B2837321 : Blo 1891435 2837321 := bstep (se 2 (by rfl) ⟨1063995, by rfl⟩ : syracuseStep 2837321 = 2127991) B2127991
theorem B1891547 : Blo 1891435 1891547 := bstep (se 1 (by rfl) ⟨1418660, by rfl⟩ : syracuseStep 1891547 = 2837321) B2837321
theorem B2693245 : Blo 1891435 2693245 := bbase (se 3 (by rfl) ⟨504983, by rfl⟩ : syracuseStep 2693245 = 1009967) (by norm_num)
theorem B3590993 : Blo 1891435 3590993 := bstep (se 2 (by rfl) ⟨1346622, by rfl⟩ : syracuseStep 3590993 = 2693245) B2693245
theorem B9575981 : Blo 1891435 9575981 := bstep (se 3 (by rfl) ⟨1795496, by rfl⟩ : syracuseStep 9575981 = 3590993) B3590993
theorem B6383987 : Blo 1891435 6383987 := bstep (se 1 (by rfl) ⟨4787990, by rfl⟩ : syracuseStep 6383987 = 9575981) B9575981
theorem B4255991 : Blo 1891435 4255991 := bstep (se 1 (by rfl) ⟨3191993, by rfl⟩ : syracuseStep 4255991 = 6383987) B6383987
theorem B2837327 : Blo 1891435 2837327 := bstep (se 1 (by rfl) ⟨2127995, by rfl⟩ : syracuseStep 2837327 = 4255991) B4255991
theorem B1891551 : Blo 1891435 1891551 := bstep (se 1 (by rfl) ⟨1418663, by rfl⟩ : syracuseStep 1891551 = 2837327) B2837327
theorem B2837333 : Blo 1891435 2837333 := bbase (se 9 (by rfl) ⟨8312, by rfl⟩ : syracuseStep 2837333 = 16625) (by norm_num)
theorem B1891555 : Blo 1891435 1891555 := bstep (se 1 (by rfl) ⟨1418666, by rfl⟩ : syracuseStep 1891555 = 2837333) B2837333
theorem B4039885 : Blo 1891435 4039885 := bbase (se 3 (by rfl) ⟨757478, by rfl⟩ : syracuseStep 4039885 = 1514957) (by norm_num)
theorem B5386513 : Blo 1891435 5386513 := bstep (se 2 (by rfl) ⟨2019942, by rfl⟩ : syracuseStep 5386513 = 4039885) B4039885
theorem B7182017 : Blo 1891435 7182017 := bstep (se 2 (by rfl) ⟨2693256, by rfl⟩ : syracuseStep 7182017 = 5386513) B5386513
theorem B4788011 : Blo 1891435 4788011 := bstep (se 1 (by rfl) ⟨3591008, by rfl⟩ : syracuseStep 4788011 = 7182017) B7182017
theorem B3192007 : Blo 1891435 3192007 := bstep (se 1 (by rfl) ⟨2394005, by rfl⟩ : syracuseStep 3192007 = 4788011) B4788011
theorem B4256009 : Blo 1891435 4256009 := bstep (se 2 (by rfl) ⟨1596003, by rfl⟩ : syracuseStep 4256009 = 3192007) B3192007
theorem B2837339 : Blo 1891435 2837339 := bstep (se 1 (by rfl) ⟨2128004, by rfl⟩ : syracuseStep 2837339 = 4256009) B4256009
theorem B1891559 : Blo 1891435 1891559 := bstep (se 1 (by rfl) ⟨1418669, by rfl⟩ : syracuseStep 1891559 = 2837339) B2837339
theorem B2128009 : Blo 1891435 2128009 := bbase (se 2 (by rfl) ⟨798003, by rfl⟩ : syracuseStep 2128009 = 1596007) (by norm_num)
theorem B2837345 : Blo 1891435 2837345 := bstep (se 2 (by rfl) ⟨1064004, by rfl⟩ : syracuseStep 2837345 = 2128009) B2128009
theorem B1891563 : Blo 1891435 1891563 := bstep (se 1 (by rfl) ⟨1418672, by rfl⟩ : syracuseStep 1891563 = 2837345) B2837345
theorem B9213797 : Blo 1891435 9213797 := bbase (se 4 (by rfl) ⟨863793, by rfl⟩ : syracuseStep 9213797 = 1727587) (by norm_num)
theorem B24570125 : Blo 1891435 24570125 := bstep (se 3 (by rfl) ⟨4606898, by rfl⟩ : syracuseStep 24570125 = 9213797) B9213797
theorem B16380083 : Blo 1891435 16380083 := bstep (se 1 (by rfl) ⟨12285062, by rfl⟩ : syracuseStep 16380083 = 24570125) B24570125
theorem B43680221 : Blo 1891435 43680221 := bstep (se 3 (by rfl) ⟨8190041, by rfl⟩ : syracuseStep 43680221 = 16380083) B16380083
theorem B29120147 : Blo 1891435 29120147 := bstep (se 1 (by rfl) ⟨21840110, by rfl⟩ : syracuseStep 29120147 = 43680221) B43680221
theorem B19413431 : Blo 1891435 19413431 := bstep (se 1 (by rfl) ⟨14560073, by rfl⟩ : syracuseStep 19413431 = 29120147) B29120147
theorem B12942287 : Blo 1891435 12942287 := bstep (se 1 (by rfl) ⟨9706715, by rfl⟩ : syracuseStep 12942287 = 19413431) B19413431
theorem B8628191 : Blo 1891435 8628191 := bstep (se 1 (by rfl) ⟨6471143, by rfl⟩ : syracuseStep 8628191 = 12942287) B12942287
theorem B5752127 : Blo 1891435 5752127 := bstep (se 1 (by rfl) ⟨4314095, by rfl⟩ : syracuseStep 5752127 = 8628191) B8628191
theorem B3834751 : Blo 1891435 3834751 := bstep (se 1 (by rfl) ⟨2876063, by rfl⟩ : syracuseStep 3834751 = 5752127) B5752127
theorem B5113001 : Blo 1891435 5113001 := bstep (se 2 (by rfl) ⟨1917375, by rfl⟩ : syracuseStep 5113001 = 3834751) B3834751
theorem B13634669 : Blo 1891435 13634669 := bstep (se 3 (by rfl) ⟨2556500, by rfl⟩ : syracuseStep 13634669 = 5113001) B5113001
theorem B36359117 : Blo 1891435 36359117 := bstep (se 3 (by rfl) ⟨6817334, by rfl⟩ : syracuseStep 36359117 = 13634669) B13634669
theorem B24239411 : Blo 1891435 24239411 := bstep (se 1 (by rfl) ⟨18179558, by rfl⟩ : syracuseStep 24239411 = 36359117) B36359117
theorem B16159607 : Blo 1891435 16159607 := bstep (se 1 (by rfl) ⟨12119705, by rfl⟩ : syracuseStep 16159607 = 24239411) B24239411
theorem B10773071 : Blo 1891435 10773071 := bstep (se 1 (by rfl) ⟨8079803, by rfl⟩ : syracuseStep 10773071 = 16159607) B16159607
theorem B7182047 : Blo 1891435 7182047 := bstep (se 1 (by rfl) ⟨5386535, by rfl⟩ : syracuseStep 7182047 = 10773071) B10773071
theorem B4788031 : Blo 1891435 4788031 := bstep (se 1 (by rfl) ⟨3591023, by rfl⟩ : syracuseStep 4788031 = 7182047) B7182047
theorem B6384041 : Blo 1891435 6384041 := bstep (se 2 (by rfl) ⟨2394015, by rfl⟩ : syracuseStep 6384041 = 4788031) B4788031
theorem B4256027 : Blo 1891435 4256027 := bstep (se 1 (by rfl) ⟨3192020, by rfl⟩ : syracuseStep 4256027 = 6384041) B6384041
theorem B2837351 : Blo 1891435 2837351 := bstep (se 1 (by rfl) ⟨2128013, by rfl⟩ : syracuseStep 2837351 = 4256027) B4256027
theorem B1891567 : Blo 1891435 1891567 := bstep (se 1 (by rfl) ⟨1418675, by rfl⟩ : syracuseStep 1891567 = 2837351) B2837351
theorem B2837357 : Blo 1891435 2837357 := bbase (se 3 (by rfl) ⟨532004, by rfl⟩ : syracuseStep 2837357 = 1064009) (by norm_num)
theorem B1891571 : Blo 1891435 1891571 := bstep (se 1 (by rfl) ⟨1418678, by rfl⟩ : syracuseStep 1891571 = 2837357) B2837357
theorem B4256045 : Blo 1891435 4256045 := bbase (se 3 (by rfl) ⟨798008, by rfl⟩ : syracuseStep 4256045 = 1596017) (by norm_num)
theorem B2837363 : Blo 1891435 2837363 := bstep (se 1 (by rfl) ⟨2128022, by rfl⟩ : syracuseStep 2837363 = 4256045) B4256045
theorem B1891575 : Blo 1891435 1891575 := bstep (se 1 (by rfl) ⟨1418681, by rfl⟩ : syracuseStep 1891575 = 2837363) B2837363
theorem B6059893 : Blo 1891435 6059893 := bbase (se 5 (by rfl) ⟨284057, by rfl⟩ : syracuseStep 6059893 = 568115) (by norm_num)
theorem B8079857 : Blo 1891435 8079857 := bstep (se 2 (by rfl) ⟨3029946, by rfl⟩ : syracuseStep 8079857 = 6059893) B6059893
theorem B5386571 : Blo 1891435 5386571 := bstep (se 1 (by rfl) ⟨4039928, by rfl⟩ : syracuseStep 5386571 = 8079857) B8079857
theorem B3591047 : Blo 1891435 3591047 := bstep (se 1 (by rfl) ⟨2693285, by rfl⟩ : syracuseStep 3591047 = 5386571) B5386571
theorem B2394031 : Blo 1891435 2394031 := bstep (se 1 (by rfl) ⟨1795523, by rfl⟩ : syracuseStep 2394031 = 3591047) B3591047
theorem B3192041 : Blo 1891435 3192041 := bstep (se 2 (by rfl) ⟨1197015, by rfl⟩ : syracuseStep 3192041 = 2394031) B2394031
theorem B2128027 : Blo 1891435 2128027 := bstep (se 1 (by rfl) ⟨1596020, by rfl⟩ : syracuseStep 2128027 = 3192041) B3192041
theorem B2837369 : Blo 1891435 2837369 := bstep (se 2 (by rfl) ⟨1064013, by rfl⟩ : syracuseStep 2837369 = 2128027) B2128027
theorem B1891579 : Blo 1891435 1891579 := bstep (se 1 (by rfl) ⟨1418684, by rfl⟩ : syracuseStep 1891579 = 2837369) B2837369
theorem B19946933 : Blo 1891435 19946933 := bbase (se 5 (by rfl) ⟨935012, by rfl⟩ : syracuseStep 19946933 = 1870025) (by norm_num)
theorem B13297955 : Blo 1891435 13297955 := bstep (se 1 (by rfl) ⟨9973466, by rfl⟩ : syracuseStep 13297955 = 19946933) B19946933
theorem B141844853 : Blo 1891435 141844853 := bstep (se 5 (by rfl) ⟨6648977, by rfl⟩ : syracuseStep 141844853 = 13297955) B13297955
theorem B94563235 : Blo 1891435 94563235 := bstep (se 1 (by rfl) ⟨70922426, by rfl⟩ : syracuseStep 94563235 = 141844853) B141844853
theorem B126084313 : Blo 1891435 126084313 := bstep (se 2 (by rfl) ⟨47281617, by rfl⟩ : syracuseStep 126084313 = 94563235) B94563235
theorem B168112417 : Blo 1891435 168112417 := bstep (se 2 (by rfl) ⟨63042156, by rfl⟩ : syracuseStep 168112417 = 126084313) B126084313
theorem B224149889 : Blo 1891435 224149889 := bstep (se 2 (by rfl) ⟨84056208, by rfl⟩ : syracuseStep 224149889 = 168112417) B168112417
theorem B597733037 : Blo 1891435 597733037 := bstep (se 3 (by rfl) ⟨112074944, by rfl⟩ : syracuseStep 597733037 = 224149889) B224149889
theorem B398488691 : Blo 1891435 398488691 := bstep (se 1 (by rfl) ⟨298866518, by rfl⟩ : syracuseStep 398488691 = 597733037) B597733037
theorem B1062636509 : Blo 1891435 1062636509 := bstep (se 3 (by rfl) ⟨199244345, by rfl⟩ : syracuseStep 1062636509 = 398488691) B398488691
theorem B2833697357 : Blo 1891435 2833697357 := bstep (se 3 (by rfl) ⟨531318254, by rfl⟩ : syracuseStep 2833697357 = 1062636509) B1062636509
theorem B1889131571 : Blo 1891435 1889131571 := bstep (se 1 (by rfl) ⟨1416848678, by rfl⟩ : syracuseStep 1889131571 = 2833697357) B2833697357
theorem B1259421047 : Blo 1891435 1259421047 := bstep (se 1 (by rfl) ⟨944565785, by rfl⟩ : syracuseStep 1259421047 = 1889131571) B1889131571
theorem B839614031 : Blo 1891435 839614031 := bstep (se 1 (by rfl) ⟨629710523, by rfl⟩ : syracuseStep 839614031 = 1259421047) B1259421047
theorem B559742687 : Blo 1891435 559742687 := bstep (se 1 (by rfl) ⟨419807015, by rfl⟩ : syracuseStep 559742687 = 839614031) B839614031
theorem B373161791 : Blo 1891435 373161791 := bstep (se 1 (by rfl) ⟨279871343, by rfl⟩ : syracuseStep 373161791 = 559742687) B559742687
theorem B248774527 : Blo 1891435 248774527 := bstep (se 1 (by rfl) ⟨186580895, by rfl⟩ : syracuseStep 248774527 = 373161791) B373161791
theorem B331699369 : Blo 1891435 331699369 := bstep (se 2 (by rfl) ⟨124387263, by rfl⟩ : syracuseStep 331699369 = 248774527) B248774527
theorem B442265825 : Blo 1891435 442265825 := bstep (se 2 (by rfl) ⟨165849684, by rfl⟩ : syracuseStep 442265825 = 331699369) B331699369
theorem B294843883 : Blo 1891435 294843883 := bstep (se 1 (by rfl) ⟨221132912, by rfl⟩ : syracuseStep 294843883 = 442265825) B442265825
theorem B393125177 : Blo 1891435 393125177 := bstep (se 2 (by rfl) ⟨147421941, by rfl⟩ : syracuseStep 393125177 = 294843883) B294843883
theorem B262083451 : Blo 1891435 262083451 := bstep (se 1 (by rfl) ⟨196562588, by rfl⟩ : syracuseStep 262083451 = 393125177) B393125177
theorem B349444601 : Blo 1891435 349444601 := bstep (se 2 (by rfl) ⟨131041725, by rfl⟩ : syracuseStep 349444601 = 262083451) B262083451
theorem B232963067 : Blo 1891435 232963067 := bstep (se 1 (by rfl) ⟨174722300, by rfl⟩ : syracuseStep 232963067 = 349444601) B349444601
theorem B155308711 : Blo 1891435 155308711 := bstep (se 1 (by rfl) ⟨116481533, by rfl⟩ : syracuseStep 155308711 = 232963067) B232963067
theorem B207078281 : Blo 1891435 207078281 := bstep (se 2 (by rfl) ⟨77654355, by rfl⟩ : syracuseStep 207078281 = 155308711) B155308711
theorem B138052187 : Blo 1891435 138052187 := bstep (se 1 (by rfl) ⟨103539140, by rfl⟩ : syracuseStep 138052187 = 207078281) B207078281
theorem B92034791 : Blo 1891435 92034791 := bstep (se 1 (by rfl) ⟨69026093, by rfl⟩ : syracuseStep 92034791 = 138052187) B138052187
theorem B61356527 : Blo 1891435 61356527 := bstep (se 1 (by rfl) ⟨46017395, by rfl⟩ : syracuseStep 61356527 = 92034791) B92034791
theorem B40904351 : Blo 1891435 40904351 := bstep (se 1 (by rfl) ⟨30678263, by rfl⟩ : syracuseStep 40904351 = 61356527) B61356527
theorem B27269567 : Blo 1891435 27269567 := bstep (se 1 (by rfl) ⟨20452175, by rfl⟩ : syracuseStep 27269567 = 40904351) B40904351
theorem B18179711 : Blo 1891435 18179711 := bstep (se 1 (by rfl) ⟨13634783, by rfl⟩ : syracuseStep 18179711 = 27269567) B27269567
theorem B12119807 : Blo 1891435 12119807 := bstep (se 1 (by rfl) ⟨9089855, by rfl⟩ : syracuseStep 12119807 = 18179711) B18179711
theorem B32319485 : Blo 1891435 32319485 := bstep (se 3 (by rfl) ⟨6059903, by rfl⟩ : syracuseStep 32319485 = 12119807) B12119807
theorem B21546323 : Blo 1891435 21546323 := bstep (se 1 (by rfl) ⟨16159742, by rfl⟩ : syracuseStep 21546323 = 32319485) B32319485
theorem B14364215 : Blo 1891435 14364215 := bstep (se 1 (by rfl) ⟨10773161, by rfl⟩ : syracuseStep 14364215 = 21546323) B21546323
theorem B9576143 : Blo 1891435 9576143 := bstep (se 1 (by rfl) ⟨7182107, by rfl⟩ : syracuseStep 9576143 = 14364215) B14364215
theorem B6384095 : Blo 1891435 6384095 := bstep (se 1 (by rfl) ⟨4788071, by rfl⟩ : syracuseStep 6384095 = 9576143) B9576143
theorem B4256063 : Blo 1891435 4256063 := bstep (se 1 (by rfl) ⟨3192047, by rfl⟩ : syracuseStep 4256063 = 6384095) B6384095
theorem B2837375 : Blo 1891435 2837375 := bstep (se 1 (by rfl) ⟨2128031, by rfl⟩ : syracuseStep 2837375 = 4256063) B4256063
theorem B1891583 : Blo 1891435 1891583 := bstep (se 1 (by rfl) ⟨1418687, by rfl⟩ : syracuseStep 1891583 = 2837375) B2837375
theorem B2837381 : Blo 1891435 2837381 := bbase (se 4 (by rfl) ⟨266004, by rfl⟩ : syracuseStep 2837381 = 532009) (by norm_num)
theorem B1891587 : Blo 1891435 1891587 := bstep (se 1 (by rfl) ⟨1418690, by rfl⟩ : syracuseStep 1891587 = 2837381) B2837381
theorem B3192061 : Blo 1891435 3192061 := bbase (se 3 (by rfl) ⟨598511, by rfl⟩ : syracuseStep 3192061 = 1197023) (by norm_num)
theorem B4256081 : Blo 1891435 4256081 := bstep (se 2 (by rfl) ⟨1596030, by rfl⟩ : syracuseStep 4256081 = 3192061) B3192061
theorem B2837387 : Blo 1891435 2837387 := bstep (se 1 (by rfl) ⟨2128040, by rfl⟩ : syracuseStep 2837387 = 4256081) B4256081
theorem B1891591 : Blo 1891435 1891591 := bstep (se 1 (by rfl) ⟨1418693, by rfl⟩ : syracuseStep 1891591 = 2837387) B2837387
theorem B2128045 : Blo 1891435 2128045 := bbase (se 3 (by rfl) ⟨399008, by rfl⟩ : syracuseStep 2128045 = 798017) (by norm_num)
theorem B2837393 : Blo 1891435 2837393 := bstep (se 2 (by rfl) ⟨1064022, by rfl⟩ : syracuseStep 2837393 = 2128045) B2128045
theorem B1891595 : Blo 1891435 1891595 := bstep (se 1 (by rfl) ⟨1418696, by rfl⟩ : syracuseStep 1891595 = 2837393) B2837393
theorem B6384149 : Blo 1891435 6384149 := bbase (se 6 (by rfl) ⟨149628, by rfl⟩ : syracuseStep 6384149 = 299257) (by norm_num)
theorem B4256099 : Blo 1891435 4256099 := bstep (se 1 (by rfl) ⟨3192074, by rfl⟩ : syracuseStep 4256099 = 6384149) B6384149
theorem B2837399 : Blo 1891435 2837399 := bstep (se 1 (by rfl) ⟨2128049, by rfl⟩ : syracuseStep 2837399 = 4256099) B4256099
theorem B1891599 : Blo 1891435 1891599 := bstep (se 1 (by rfl) ⟨1418699, by rfl⟩ : syracuseStep 1891599 = 2837399) B2837399
theorem B2837405 : Blo 1891435 2837405 := bbase (se 3 (by rfl) ⟨532013, by rfl⟩ : syracuseStep 2837405 = 1064027) (by norm_num)
theorem B1891603 : Blo 1891435 1891603 := bstep (se 1 (by rfl) ⟨1418702, by rfl⟩ : syracuseStep 1891603 = 2837405) B2837405
theorem B4256117 : Blo 1891435 4256117 := bbase (se 5 (by rfl) ⟨199505, by rfl⟩ : syracuseStep 4256117 = 399011) (by norm_num)
theorem B2837411 : Blo 1891435 2837411 := bstep (se 1 (by rfl) ⟨2128058, by rfl⟩ : syracuseStep 2837411 = 4256117) B4256117
theorem B1891607 : Blo 1891435 1891607 := bstep (se 1 (by rfl) ⟨1418705, by rfl⟩ : syracuseStep 1891607 = 2837411) B2837411
theorem B12119989 : Blo 1891435 12119989 := bbase (se 5 (by rfl) ⟨568124, by rfl⟩ : syracuseStep 12119989 = 1136249) (by norm_num)
theorem B16159985 : Blo 1891435 16159985 := bstep (se 2 (by rfl) ⟨6059994, by rfl⟩ : syracuseStep 16159985 = 12119989) B12119989
theorem B10773323 : Blo 1891435 10773323 := bstep (se 1 (by rfl) ⟨8079992, by rfl⟩ : syracuseStep 10773323 = 16159985) B16159985
theorem B7182215 : Blo 1891435 7182215 := bstep (se 1 (by rfl) ⟨5386661, by rfl⟩ : syracuseStep 7182215 = 10773323) B10773323
theorem B4788143 : Blo 1891435 4788143 := bstep (se 1 (by rfl) ⟨3591107, by rfl⟩ : syracuseStep 4788143 = 7182215) B7182215
theorem B3192095 : Blo 1891435 3192095 := bstep (se 1 (by rfl) ⟨2394071, by rfl⟩ : syracuseStep 3192095 = 4788143) B4788143
theorem B2128063 : Blo 1891435 2128063 := bstep (se 1 (by rfl) ⟨1596047, by rfl⟩ : syracuseStep 2128063 = 3192095) B3192095
theorem B2837417 : Blo 1891435 2837417 := bstep (se 2 (by rfl) ⟨1064031, by rfl⟩ : syracuseStep 2837417 = 2128063) B2128063
theorem B1891611 : Blo 1891435 1891611 := bstep (se 1 (by rfl) ⟨1418708, by rfl⟩ : syracuseStep 1891611 = 2837417) B2837417
theorem B7182229 : Blo 1891435 7182229 := bbase (se 6 (by rfl) ⟨168333, by rfl⟩ : syracuseStep 7182229 = 336667) (by norm_num)
theorem B9576305 : Blo 1891435 9576305 := bstep (se 2 (by rfl) ⟨3591114, by rfl⟩ : syracuseStep 9576305 = 7182229) B7182229
theorem B6384203 : Blo 1891435 6384203 := bstep (se 1 (by rfl) ⟨4788152, by rfl⟩ : syracuseStep 6384203 = 9576305) B9576305
theorem B4256135 : Blo 1891435 4256135 := bstep (se 1 (by rfl) ⟨3192101, by rfl⟩ : syracuseStep 4256135 = 6384203) B6384203
theorem B2837423 : Blo 1891435 2837423 := bstep (se 1 (by rfl) ⟨2128067, by rfl⟩ : syracuseStep 2837423 = 4256135) B4256135
theorem B1891615 : Blo 1891435 1891615 := bstep (se 1 (by rfl) ⟨1418711, by rfl⟩ : syracuseStep 1891615 = 2837423) B2837423
theorem B2837429 : Blo 1891435 2837429 := bbase (se 5 (by rfl) ⟨133004, by rfl⟩ : syracuseStep 2837429 = 266009) (by norm_num)
theorem B1891619 : Blo 1891435 1891619 := bstep (se 1 (by rfl) ⟨1418714, by rfl⟩ : syracuseStep 1891619 = 2837429) B2837429
theorem B4788173 : Blo 1891435 4788173 := bbase (se 3 (by rfl) ⟨897782, by rfl⟩ : syracuseStep 4788173 = 1795565) (by norm_num)
theorem B3192115 : Blo 1891435 3192115 := bstep (se 1 (by rfl) ⟨2394086, by rfl⟩ : syracuseStep 3192115 = 4788173) B4788173
theorem B4256153 : Blo 1891435 4256153 := bstep (se 2 (by rfl) ⟨1596057, by rfl⟩ : syracuseStep 4256153 = 3192115) B3192115
theorem B2837435 : Blo 1891435 2837435 := bstep (se 1 (by rfl) ⟨2128076, by rfl⟩ : syracuseStep 2837435 = 4256153) B4256153
theorem B1891623 : Blo 1891435 1891623 := bstep (se 1 (by rfl) ⟨1418717, by rfl⟩ : syracuseStep 1891623 = 2837435) B2837435
theorem B2128081 : Blo 1891435 2128081 := bbase (se 2 (by rfl) ⟨798030, by rfl⟩ : syracuseStep 2128081 = 1596061) (by norm_num)
theorem B2837441 : Blo 1891435 2837441 := bstep (se 2 (by rfl) ⟨1064040, by rfl⟩ : syracuseStep 2837441 = 2128081) B2128081
theorem B1891627 : Blo 1891435 1891627 := bstep (se 1 (by rfl) ⟨1418720, by rfl⟩ : syracuseStep 1891627 = 2837441) B2837441
theorem B9707045 : Blo 1891435 9707045 := bbase (se 4 (by rfl) ⟨910035, by rfl⟩ : syracuseStep 9707045 = 1820071) (by norm_num)
theorem B25885453 : Blo 1891435 25885453 := bstep (se 3 (by rfl) ⟨4853522, by rfl⟩ : syracuseStep 25885453 = 9707045) B9707045
theorem B34513937 : Blo 1891435 34513937 := bstep (se 2 (by rfl) ⟨12942726, by rfl⟩ : syracuseStep 34513937 = 25885453) B25885453
theorem B23009291 : Blo 1891435 23009291 := bstep (se 1 (by rfl) ⟨17256968, by rfl⟩ : syracuseStep 23009291 = 34513937) B34513937
theorem B15339527 : Blo 1891435 15339527 := bstep (se 1 (by rfl) ⟨11504645, by rfl⟩ : syracuseStep 15339527 = 23009291) B23009291
theorem B10226351 : Blo 1891435 10226351 := bstep (se 1 (by rfl) ⟨7669763, by rfl⟩ : syracuseStep 10226351 = 15339527) B15339527
theorem B6817567 : Blo 1891435 6817567 := bstep (se 1 (by rfl) ⟨5113175, by rfl⟩ : syracuseStep 6817567 = 10226351) B10226351
theorem B9090089 : Blo 1891435 9090089 := bstep (se 2 (by rfl) ⟨3408783, by rfl⟩ : syracuseStep 9090089 = 6817567) B6817567
theorem B6060059 : Blo 1891435 6060059 := bstep (se 1 (by rfl) ⟨4545044, by rfl⟩ : syracuseStep 6060059 = 9090089) B9090089
theorem B4040039 : Blo 1891435 4040039 := bstep (se 1 (by rfl) ⟨3030029, by rfl⟩ : syracuseStep 4040039 = 6060059) B6060059
theorem B2693359 : Blo 1891435 2693359 := bstep (se 1 (by rfl) ⟨2020019, by rfl⟩ : syracuseStep 2693359 = 4040039) B4040039
theorem B3591145 : Blo 1891435 3591145 := bstep (se 2 (by rfl) ⟨1346679, by rfl⟩ : syracuseStep 3591145 = 2693359) B2693359
theorem B4788193 : Blo 1891435 4788193 := bstep (se 2 (by rfl) ⟨1795572, by rfl⟩ : syracuseStep 4788193 = 3591145) B3591145
theorem B6384257 : Blo 1891435 6384257 := bstep (se 2 (by rfl) ⟨2394096, by rfl⟩ : syracuseStep 6384257 = 4788193) B4788193
theorem B4256171 : Blo 1891435 4256171 := bstep (se 1 (by rfl) ⟨3192128, by rfl⟩ : syracuseStep 4256171 = 6384257) B6384257
theorem B2837447 : Blo 1891435 2837447 := bstep (se 1 (by rfl) ⟨2128085, by rfl⟩ : syracuseStep 2837447 = 4256171) B4256171
theorem B1891631 : Blo 1891435 1891631 := bstep (se 1 (by rfl) ⟨1418723, by rfl⟩ : syracuseStep 1891631 = 2837447) B2837447
theorem B2837453 : Blo 1891435 2837453 := bbase (se 3 (by rfl) ⟨532022, by rfl⟩ : syracuseStep 2837453 = 1064045) (by norm_num)
theorem B1891635 : Blo 1891435 1891635 := bstep (se 1 (by rfl) ⟨1418726, by rfl⟩ : syracuseStep 1891635 = 2837453) B2837453
theorem B4256189 : Blo 1891435 4256189 := bbase (se 3 (by rfl) ⟨798035, by rfl⟩ : syracuseStep 4256189 = 1596071) (by norm_num)
theorem B2837459 : Blo 1891435 2837459 := bstep (se 1 (by rfl) ⟨2128094, by rfl⟩ : syracuseStep 2837459 = 4256189) B4256189
theorem B1891639 : Blo 1891435 1891639 := bstep (se 1 (by rfl) ⟨1418729, by rfl⟩ : syracuseStep 1891639 = 2837459) B2837459
theorem B3192149 : Blo 1891435 3192149 := bbase (se 13 (by rfl) ⟨584, by rfl⟩ : syracuseStep 3192149 = 1169) (by norm_num)
theorem B2128099 : Blo 1891435 2128099 := bstep (se 1 (by rfl) ⟨1596074, by rfl⟩ : syracuseStep 2128099 = 3192149) B3192149
theorem B2837465 : Blo 1891435 2837465 := bstep (se 2 (by rfl) ⟨1064049, by rfl⟩ : syracuseStep 2837465 = 2128099) B2128099
theorem B1891643 : Blo 1891435 1891643 := bstep (se 1 (by rfl) ⟨1418732, by rfl⟩ : syracuseStep 1891643 = 2837465) B2837465
theorem B2272541 : Blo 1891435 2272541 := bbase (se 3 (by rfl) ⟨426101, by rfl⟩ : syracuseStep 2272541 = 852203) (by norm_num)
theorem B6060109 : Blo 1891435 6060109 := bstep (se 3 (by rfl) ⟨1136270, by rfl⟩ : syracuseStep 6060109 = 2272541) B2272541
theorem B8080145 : Blo 1891435 8080145 := bstep (se 2 (by rfl) ⟨3030054, by rfl⟩ : syracuseStep 8080145 = 6060109) B6060109
theorem B5386763 : Blo 1891435 5386763 := bstep (se 1 (by rfl) ⟨4040072, by rfl⟩ : syracuseStep 5386763 = 8080145) B8080145
theorem B14364701 : Blo 1891435 14364701 := bstep (se 3 (by rfl) ⟨2693381, by rfl⟩ : syracuseStep 14364701 = 5386763) B5386763
theorem B9576467 : Blo 1891435 9576467 := bstep (se 1 (by rfl) ⟨7182350, by rfl⟩ : syracuseStep 9576467 = 14364701) B14364701
theorem B6384311 : Blo 1891435 6384311 := bstep (se 1 (by rfl) ⟨4788233, by rfl⟩ : syracuseStep 6384311 = 9576467) B9576467
theorem B4256207 : Blo 1891435 4256207 := bstep (se 1 (by rfl) ⟨3192155, by rfl⟩ : syracuseStep 4256207 = 6384311) B6384311
theorem B2837471 : Blo 1891435 2837471 := bstep (se 1 (by rfl) ⟨2128103, by rfl⟩ : syracuseStep 2837471 = 4256207) B4256207
theorem B1891647 : Blo 1891435 1891647 := bstep (se 1 (by rfl) ⟨1418735, by rfl⟩ : syracuseStep 1891647 = 2837471) B2837471
theorem B2837477 : Blo 1891435 2837477 := bbase (se 4 (by rfl) ⟨266013, by rfl⟩ : syracuseStep 2837477 = 532027) (by norm_num)
theorem B1891651 : Blo 1891435 1891651 := bstep (se 1 (by rfl) ⟨1418738, by rfl⟩ : syracuseStep 1891651 = 2837477) B2837477
theorem B8080181 : Blo 1891435 8080181 := bbase (se 5 (by rfl) ⟨378758, by rfl⟩ : syracuseStep 8080181 = 757517) (by norm_num)
theorem B5386787 : Blo 1891435 5386787 := bstep (se 1 (by rfl) ⟨4040090, by rfl⟩ : syracuseStep 5386787 = 8080181) B8080181
theorem B3591191 : Blo 1891435 3591191 := bstep (se 1 (by rfl) ⟨2693393, by rfl⟩ : syracuseStep 3591191 = 5386787) B5386787
theorem B2394127 : Blo 1891435 2394127 := bstep (se 1 (by rfl) ⟨1795595, by rfl⟩ : syracuseStep 2394127 = 3591191) B3591191
theorem B3192169 : Blo 1891435 3192169 := bstep (se 2 (by rfl) ⟨1197063, by rfl⟩ : syracuseStep 3192169 = 2394127) B2394127
theorem B4256225 : Blo 1891435 4256225 := bstep (se 2 (by rfl) ⟨1596084, by rfl⟩ : syracuseStep 4256225 = 3192169) B3192169
theorem B2837483 : Blo 1891435 2837483 := bstep (se 1 (by rfl) ⟨2128112, by rfl⟩ : syracuseStep 2837483 = 4256225) B4256225
theorem B1891655 : Blo 1891435 1891655 := bstep (se 1 (by rfl) ⟨1418741, by rfl⟩ : syracuseStep 1891655 = 2837483) B2837483
theorem B2128117 : Blo 1891435 2128117 := bbase (se 5 (by rfl) ⟨99755, by rfl⟩ : syracuseStep 2128117 = 199511) (by norm_num)
theorem B2837489 : Blo 1891435 2837489 := bstep (se 2 (by rfl) ⟨1064058, by rfl⟩ : syracuseStep 2837489 = 2128117) B2128117
theorem B1891659 : Blo 1891435 1891659 := bstep (se 1 (by rfl) ⟨1418744, by rfl⟩ : syracuseStep 1891659 = 2837489) B2837489
theorem B2394137 : Blo 1891435 2394137 := bbase (se 2 (by rfl) ⟨897801, by rfl⟩ : syracuseStep 2394137 = 1795603) (by norm_num)
theorem B6384365 : Blo 1891435 6384365 := bstep (se 3 (by rfl) ⟨1197068, by rfl⟩ : syracuseStep 6384365 = 2394137) B2394137
theorem B4256243 : Blo 1891435 4256243 := bstep (se 1 (by rfl) ⟨3192182, by rfl⟩ : syracuseStep 4256243 = 6384365) B6384365
theorem B2837495 : Blo 1891435 2837495 := bstep (se 1 (by rfl) ⟨2128121, by rfl⟩ : syracuseStep 2837495 = 4256243) B4256243
theorem B1891663 : Blo 1891435 1891663 := bstep (se 1 (by rfl) ⟨1418747, by rfl⟩ : syracuseStep 1891663 = 2837495) B2837495
theorem B2837501 : Blo 1891435 2837501 := bbase (se 3 (by rfl) ⟨532031, by rfl⟩ : syracuseStep 2837501 = 1064063) (by norm_num)
theorem B1891667 : Blo 1891435 1891667 := bstep (se 1 (by rfl) ⟨1418750, by rfl⟩ : syracuseStep 1891667 = 2837501) B2837501
theorem B4256261 : Blo 1891435 4256261 := bbase (se 4 (by rfl) ⟨399024, by rfl⟩ : syracuseStep 4256261 = 798049) (by norm_num)
theorem B2837507 : Blo 1891435 2837507 := bstep (se 1 (by rfl) ⟨2128130, by rfl⟩ : syracuseStep 2837507 = 4256261) B4256261
theorem B1891671 : Blo 1891435 1891671 := bstep (se 1 (by rfl) ⟨1418753, by rfl⟩ : syracuseStep 1891671 = 2837507) B2837507
theorem B3591229 : Blo 1891435 3591229 := bbase (se 3 (by rfl) ⟨673355, by rfl⟩ : syracuseStep 3591229 = 1346711) (by norm_num)
theorem B4788305 : Blo 1891435 4788305 := bstep (se 2 (by rfl) ⟨1795614, by rfl⟩ : syracuseStep 4788305 = 3591229) B3591229
theorem B3192203 : Blo 1891435 3192203 := bstep (se 1 (by rfl) ⟨2394152, by rfl⟩ : syracuseStep 3192203 = 4788305) B4788305
theorem B2128135 : Blo 1891435 2128135 := bstep (se 1 (by rfl) ⟨1596101, by rfl⟩ : syracuseStep 2128135 = 3192203) B3192203
theorem B2837513 : Blo 1891435 2837513 := bstep (se 2 (by rfl) ⟨1064067, by rfl⟩ : syracuseStep 2837513 = 2128135) B2128135
theorem B1891675 : Blo 1891435 1891675 := bstep (se 1 (by rfl) ⟨1418756, by rfl⟩ : syracuseStep 1891675 = 2837513) B2837513
theorem B9576629 : Blo 1891435 9576629 := bbase (se 5 (by rfl) ⟨448904, by rfl⟩ : syracuseStep 9576629 = 897809) (by norm_num)
theorem B6384419 : Blo 1891435 6384419 := bstep (se 1 (by rfl) ⟨4788314, by rfl⟩ : syracuseStep 6384419 = 9576629) B9576629
theorem B4256279 : Blo 1891435 4256279 := bstep (se 1 (by rfl) ⟨3192209, by rfl⟩ : syracuseStep 4256279 = 6384419) B6384419
theorem B2837519 : Blo 1891435 2837519 := bstep (se 1 (by rfl) ⟨2128139, by rfl⟩ : syracuseStep 2837519 = 4256279) B4256279
theorem B1891679 : Blo 1891435 1891679 := bstep (se 1 (by rfl) ⟨1418759, by rfl⟩ : syracuseStep 1891679 = 2837519) B2837519
theorem B2837525 : Blo 1891435 2837525 := bbase (se 6 (by rfl) ⟨66504, by rfl⟩ : syracuseStep 2837525 = 133009) (by norm_num)
theorem B1891683 : Blo 1891435 1891683 := bstep (se 1 (by rfl) ⟨1418762, by rfl⟩ : syracuseStep 1891683 = 2837525) B2837525
theorem B3071461 : Blo 1891435 3071461 := bbase (se 4 (by rfl) ⟨287949, by rfl⟩ : syracuseStep 3071461 = 575899) (by norm_num)
theorem B4095281 : Blo 1891435 4095281 := bstep (se 2 (by rfl) ⟨1535730, by rfl⟩ : syracuseStep 4095281 = 3071461) B3071461
theorem B2730187 : Blo 1891435 2730187 := bstep (se 1 (by rfl) ⟨2047640, by rfl⟩ : syracuseStep 2730187 = 4095281) B4095281
theorem B3640249 : Blo 1891435 3640249 := bstep (se 2 (by rfl) ⟨1365093, by rfl⟩ : syracuseStep 3640249 = 2730187) B2730187
theorem B4853665 : Blo 1891435 4853665 := bstep (se 2 (by rfl) ⟨1820124, by rfl⟩ : syracuseStep 4853665 = 3640249) B3640249
theorem B25886213 : Blo 1891435 25886213 := bstep (se 4 (by rfl) ⟨2426832, by rfl⟩ : syracuseStep 25886213 = 4853665) B4853665
theorem B17257475 : Blo 1891435 17257475 := bstep (se 1 (by rfl) ⟨12943106, by rfl⟩ : syracuseStep 17257475 = 25886213) B25886213
theorem B46019933 : Blo 1891435 46019933 := bstep (se 3 (by rfl) ⟨8628737, by rfl⟩ : syracuseStep 46019933 = 17257475) B17257475
theorem B30679955 : Blo 1891435 30679955 := bstep (se 1 (by rfl) ⟨23009966, by rfl⟩ : syracuseStep 30679955 = 46019933) B46019933
theorem B20453303 : Blo 1891435 20453303 := bstep (se 1 (by rfl) ⟨15339977, by rfl⟩ : syracuseStep 20453303 = 30679955) B30679955
theorem B13635535 : Blo 1891435 13635535 := bstep (se 1 (by rfl) ⟨10226651, by rfl⟩ : syracuseStep 13635535 = 20453303) B20453303
theorem B18180713 : Blo 1891435 18180713 := bstep (se 2 (by rfl) ⟨6817767, by rfl⟩ : syracuseStep 18180713 = 13635535) B13635535
theorem B12120475 : Blo 1891435 12120475 := bstep (se 1 (by rfl) ⟨9090356, by rfl⟩ : syracuseStep 12120475 = 18180713) B18180713
theorem B16160633 : Blo 1891435 16160633 := bstep (se 2 (by rfl) ⟨6060237, by rfl⟩ : syracuseStep 16160633 = 12120475) B12120475
theorem B10773755 : Blo 1891435 10773755 := bstep (se 1 (by rfl) ⟨8080316, by rfl⟩ : syracuseStep 10773755 = 16160633) B16160633
theorem B7182503 : Blo 1891435 7182503 := bstep (se 1 (by rfl) ⟨5386877, by rfl⟩ : syracuseStep 7182503 = 10773755) B10773755
theorem B4788335 : Blo 1891435 4788335 := bstep (se 1 (by rfl) ⟨3591251, by rfl⟩ : syracuseStep 4788335 = 7182503) B7182503
theorem B3192223 : Blo 1891435 3192223 := bstep (se 1 (by rfl) ⟨2394167, by rfl⟩ : syracuseStep 3192223 = 4788335) B4788335
theorem B4256297 : Blo 1891435 4256297 := bstep (se 2 (by rfl) ⟨1596111, by rfl⟩ : syracuseStep 4256297 = 3192223) B3192223
theorem B2837531 : Blo 1891435 2837531 := bstep (se 1 (by rfl) ⟨2128148, by rfl⟩ : syracuseStep 2837531 = 4256297) B4256297
theorem B1891687 : Blo 1891435 1891687 := bstep (se 1 (by rfl) ⟨1418765, by rfl⟩ : syracuseStep 1891687 = 2837531) B2837531
theorem B2128153 : Blo 1891435 2128153 := bbase (se 2 (by rfl) ⟨798057, by rfl⟩ : syracuseStep 2128153 = 1596115) (by norm_num)
theorem B2837537 : Blo 1891435 2837537 := bstep (se 2 (by rfl) ⟨1064076, by rfl⟩ : syracuseStep 2837537 = 2128153) B2128153
theorem B1891691 : Blo 1891435 1891691 := bstep (se 1 (by rfl) ⟨1418768, by rfl⟩ : syracuseStep 1891691 = 2837537) B2837537
theorem B7182533 : Blo 1891435 7182533 := bbase (se 4 (by rfl) ⟨673362, by rfl⟩ : syracuseStep 7182533 = 1346725) (by norm_num)
theorem B4788355 : Blo 1891435 4788355 := bstep (se 1 (by rfl) ⟨3591266, by rfl⟩ : syracuseStep 4788355 = 7182533) B7182533
theorem B6384473 : Blo 1891435 6384473 := bstep (se 2 (by rfl) ⟨2394177, by rfl⟩ : syracuseStep 6384473 = 4788355) B4788355
theorem B4256315 : Blo 1891435 4256315 := bstep (se 1 (by rfl) ⟨3192236, by rfl⟩ : syracuseStep 4256315 = 6384473) B6384473
theorem B2837543 : Blo 1891435 2837543 := bstep (se 1 (by rfl) ⟨2128157, by rfl⟩ : syracuseStep 2837543 = 4256315) B4256315
theorem B1891695 : Blo 1891435 1891695 := bstep (se 1 (by rfl) ⟨1418771, by rfl⟩ : syracuseStep 1891695 = 2837543) B2837543
theorem B2837549 : Blo 1891435 2837549 := bbase (se 3 (by rfl) ⟨532040, by rfl⟩ : syracuseStep 2837549 = 1064081) (by norm_num)
theorem B1891699 : Blo 1891435 1891699 := bstep (se 1 (by rfl) ⟨1418774, by rfl⟩ : syracuseStep 1891699 = 2837549) B2837549
theorem B4256333 : Blo 1891435 4256333 := bbase (se 3 (by rfl) ⟨798062, by rfl⟩ : syracuseStep 4256333 = 1596125) (by norm_num)
theorem B2837555 : Blo 1891435 2837555 := bstep (se 1 (by rfl) ⟨2128166, by rfl⟩ : syracuseStep 2837555 = 4256333) B4256333
theorem B1891703 : Blo 1891435 1891703 := bstep (se 1 (by rfl) ⟨1418777, by rfl⟩ : syracuseStep 1891703 = 2837555) B2837555
theorem B2394193 : Blo 1891435 2394193 := bbase (se 2 (by rfl) ⟨897822, by rfl⟩ : syracuseStep 2394193 = 1795645) (by norm_num)
theorem B3192257 : Blo 1891435 3192257 := bstep (se 2 (by rfl) ⟨1197096, by rfl⟩ : syracuseStep 3192257 = 2394193) B2394193
theorem B2128171 : Blo 1891435 2128171 := bstep (se 1 (by rfl) ⟨1596128, by rfl⟩ : syracuseStep 2128171 = 3192257) B3192257
theorem B2837561 : Blo 1891435 2837561 := bstep (se 2 (by rfl) ⟨1064085, by rfl⟩ : syracuseStep 2837561 = 2128171) B2128171
theorem B1891707 : Blo 1891435 1891707 := bstep (se 1 (by rfl) ⟨1418780, by rfl⟩ : syracuseStep 1891707 = 2837561) B2837561
theorem B3030157 : Blo 1891435 3030157 := bbase (se 3 (by rfl) ⟨568154, by rfl⟩ : syracuseStep 3030157 = 1136309) (by norm_num)
theorem B4040209 : Blo 1891435 4040209 := bstep (se 2 (by rfl) ⟨1515078, by rfl⟩ : syracuseStep 4040209 = 3030157) B3030157
theorem B21547781 : Blo 1891435 21547781 := bstep (se 4 (by rfl) ⟨2020104, by rfl⟩ : syracuseStep 21547781 = 4040209) B4040209
theorem B14365187 : Blo 1891435 14365187 := bstep (se 1 (by rfl) ⟨10773890, by rfl⟩ : syracuseStep 14365187 = 21547781) B21547781
theorem B9576791 : Blo 1891435 9576791 := bstep (se 1 (by rfl) ⟨7182593, by rfl⟩ : syracuseStep 9576791 = 14365187) B14365187
theorem B6384527 : Blo 1891435 6384527 := bstep (se 1 (by rfl) ⟨4788395, by rfl⟩ : syracuseStep 6384527 = 9576791) B9576791
theorem B4256351 : Blo 1891435 4256351 := bstep (se 1 (by rfl) ⟨3192263, by rfl⟩ : syracuseStep 4256351 = 6384527) B6384527
theorem B2837567 : Blo 1891435 2837567 := bstep (se 1 (by rfl) ⟨2128175, by rfl⟩ : syracuseStep 2837567 = 4256351) B4256351
theorem B1891711 : Blo 1891435 1891711 := bstep (se 1 (by rfl) ⟨1418783, by rfl⟩ : syracuseStep 1891711 = 2837567) B2837567
theorem B2837573 : Blo 1891435 2837573 := bbase (se 4 (by rfl) ⟨266022, by rfl⟩ : syracuseStep 2837573 = 532045) (by norm_num)
theorem B1891715 : Blo 1891435 1891715 := bstep (se 1 (by rfl) ⟨1418786, by rfl⟩ : syracuseStep 1891715 = 2837573) B2837573
theorem B3192277 : Blo 1891435 3192277 := bbase (se 7 (by rfl) ⟨37409, by rfl⟩ : syracuseStep 3192277 = 74819) (by norm_num)
theorem B4256369 : Blo 1891435 4256369 := bstep (se 2 (by rfl) ⟨1596138, by rfl⟩ : syracuseStep 4256369 = 3192277) B3192277
theorem B2837579 : Blo 1891435 2837579 := bstep (se 1 (by rfl) ⟨2128184, by rfl⟩ : syracuseStep 2837579 = 4256369) B4256369
theorem B1891719 : Blo 1891435 1891719 := bstep (se 1 (by rfl) ⟨1418789, by rfl⟩ : syracuseStep 1891719 = 2837579) B2837579
theorem B2128189 : Blo 1891435 2128189 := bbase (se 3 (by rfl) ⟨399035, by rfl⟩ : syracuseStep 2128189 = 798071) (by norm_num)
theorem B2837585 : Blo 1891435 2837585 := bstep (se 2 (by rfl) ⟨1064094, by rfl⟩ : syracuseStep 2837585 = 2128189) B2128189
theorem B1891723 : Blo 1891435 1891723 := bstep (se 1 (by rfl) ⟨1418792, by rfl⟩ : syracuseStep 1891723 = 2837585) B2837585
theorem B6384581 : Blo 1891435 6384581 := bbase (se 4 (by rfl) ⟨598554, by rfl⟩ : syracuseStep 6384581 = 1197109) (by norm_num)
theorem B4256387 : Blo 1891435 4256387 := bstep (se 1 (by rfl) ⟨3192290, by rfl⟩ : syracuseStep 4256387 = 6384581) B6384581
theorem B2837591 : Blo 1891435 2837591 := bstep (se 1 (by rfl) ⟨2128193, by rfl⟩ : syracuseStep 2837591 = 4256387) B4256387
theorem B1891727 : Blo 1891435 1891727 := bstep (se 1 (by rfl) ⟨1418795, by rfl⟩ : syracuseStep 1891727 = 2837591) B2837591
theorem B2837597 : Blo 1891435 2837597 := bbase (se 3 (by rfl) ⟨532049, by rfl⟩ : syracuseStep 2837597 = 1064099) (by norm_num)
theorem B1891731 : Blo 1891435 1891731 := bstep (se 1 (by rfl) ⟨1418798, by rfl⟩ : syracuseStep 1891731 = 2837597) B2837597
theorem B4256405 : Blo 1891435 4256405 := bbase (se 6 (by rfl) ⟨99759, by rfl⟩ : syracuseStep 4256405 = 199519) (by norm_num)
theorem B2837603 : Blo 1891435 2837603 := bstep (se 1 (by rfl) ⟨2128202, by rfl⟩ : syracuseStep 2837603 = 4256405) B4256405
theorem B1891735 : Blo 1891435 1891735 := bstep (se 1 (by rfl) ⟨1418801, by rfl⟩ : syracuseStep 1891735 = 2837603) B2837603
theorem B4095397 : Blo 1891435 4095397 := bbase (se 4 (by rfl) ⟨383943, by rfl⟩ : syracuseStep 4095397 = 767887) (by norm_num)
theorem B5460529 : Blo 1891435 5460529 := bstep (se 2 (by rfl) ⟨2047698, by rfl⟩ : syracuseStep 5460529 = 4095397) B4095397
theorem B7280705 : Blo 1891435 7280705 := bstep (se 2 (by rfl) ⟨2730264, by rfl⟩ : syracuseStep 7280705 = 5460529) B5460529
theorem B4853803 : Blo 1891435 4853803 := bstep (se 1 (by rfl) ⟨3640352, by rfl⟩ : syracuseStep 4853803 = 7280705) B7280705
theorem B6471737 : Blo 1891435 6471737 := bstep (se 2 (by rfl) ⟨2426901, by rfl⟩ : syracuseStep 6471737 = 4853803) B4853803
theorem B4314491 : Blo 1891435 4314491 := bstep (se 1 (by rfl) ⟨3235868, by rfl⟩ : syracuseStep 4314491 = 6471737) B6471737
theorem B2876327 : Blo 1891435 2876327 := bstep (se 1 (by rfl) ⟨2157245, by rfl⟩ : syracuseStep 2876327 = 4314491) B4314491
theorem B1917551 : Blo 1891435 1917551 := bstep (se 1 (by rfl) ⟨1438163, by rfl⟩ : syracuseStep 1917551 = 2876327) B2876327
theorem B5113469 : Blo 1891435 5113469 := bstep (se 3 (by rfl) ⟨958775, by rfl⟩ : syracuseStep 5113469 = 1917551) B1917551
theorem B3408979 : Blo 1891435 3408979 := bstep (se 1 (by rfl) ⟨2556734, by rfl⟩ : syracuseStep 3408979 = 5113469) B5113469
theorem B4545305 : Blo 1891435 4545305 := bstep (se 2 (by rfl) ⟨1704489, by rfl⟩ : syracuseStep 4545305 = 3408979) B3408979
theorem B3030203 : Blo 1891435 3030203 := bstep (se 1 (by rfl) ⟨2272652, by rfl⟩ : syracuseStep 3030203 = 4545305) B4545305
theorem B2020135 : Blo 1891435 2020135 := bstep (se 1 (by rfl) ⟨1515101, by rfl⟩ : syracuseStep 2020135 = 3030203) B3030203
theorem B2693513 : Blo 1891435 2693513 := bstep (se 2 (by rfl) ⟨1010067, by rfl⟩ : syracuseStep 2693513 = 2020135) B2020135
theorem B7182701 : Blo 1891435 7182701 := bstep (se 3 (by rfl) ⟨1346756, by rfl⟩ : syracuseStep 7182701 = 2693513) B2693513
theorem B4788467 : Blo 1891435 4788467 := bstep (se 1 (by rfl) ⟨3591350, by rfl⟩ : syracuseStep 4788467 = 7182701) B7182701
theorem B3192311 : Blo 1891435 3192311 := bstep (se 1 (by rfl) ⟨2394233, by rfl⟩ : syracuseStep 3192311 = 4788467) B4788467
theorem B2128207 : Blo 1891435 2128207 := bstep (se 1 (by rfl) ⟨1596155, by rfl⟩ : syracuseStep 2128207 = 3192311) B3192311
theorem B2837609 : Blo 1891435 2837609 := bstep (se 2 (by rfl) ⟨1064103, by rfl⟩ : syracuseStep 2837609 = 2128207) B2128207
theorem B1891739 : Blo 1891435 1891739 := bstep (se 1 (by rfl) ⟨1418804, by rfl⟩ : syracuseStep 1891739 = 2837609) B2837609
theorem B5113477 : Blo 1891435 5113477 := bbase (se 4 (by rfl) ⟨479388, by rfl⟩ : syracuseStep 5113477 = 958777) (by norm_num)
theorem B6817969 : Blo 1891435 6817969 := bstep (se 2 (by rfl) ⟨2556738, by rfl⟩ : syracuseStep 6817969 = 5113477) B5113477
theorem B9090625 : Blo 1891435 9090625 := bstep (se 2 (by rfl) ⟨3408984, by rfl⟩ : syracuseStep 9090625 = 6817969) B6817969
theorem B12120833 : Blo 1891435 12120833 := bstep (se 2 (by rfl) ⟨4545312, by rfl⟩ : syracuseStep 12120833 = 9090625) B9090625
theorem B8080555 : Blo 1891435 8080555 := bstep (se 1 (by rfl) ⟨6060416, by rfl⟩ : syracuseStep 8080555 = 12120833) B12120833
theorem B10774073 : Blo 1891435 10774073 := bstep (se 2 (by rfl) ⟨4040277, by rfl⟩ : syracuseStep 10774073 = 8080555) B8080555
theorem B7182715 : Blo 1891435 7182715 := bstep (se 1 (by rfl) ⟨5387036, by rfl⟩ : syracuseStep 7182715 = 10774073) B10774073
theorem B9576953 : Blo 1891435 9576953 := bstep (se 2 (by rfl) ⟨3591357, by rfl⟩ : syracuseStep 9576953 = 7182715) B7182715
theorem B6384635 : Blo 1891435 6384635 := bstep (se 1 (by rfl) ⟨4788476, by rfl⟩ : syracuseStep 6384635 = 9576953) B9576953
theorem B4256423 : Blo 1891435 4256423 := bstep (se 1 (by rfl) ⟨3192317, by rfl⟩ : syracuseStep 4256423 = 6384635) B6384635
theorem B2837615 : Blo 1891435 2837615 := bstep (se 1 (by rfl) ⟨2128211, by rfl⟩ : syracuseStep 2837615 = 4256423) B4256423
theorem B1891743 : Blo 1891435 1891743 := bstep (se 1 (by rfl) ⟨1418807, by rfl⟩ : syracuseStep 1891743 = 2837615) B2837615
theorem B2837621 : Blo 1891435 2837621 := bbase (se 5 (by rfl) ⟨133013, by rfl⟩ : syracuseStep 2837621 = 266027) (by norm_num)
theorem B1891747 : Blo 1891435 1891747 := bstep (se 1 (by rfl) ⟨1418810, by rfl⟩ : syracuseStep 1891747 = 2837621) B2837621
theorem B3591373 : Blo 1891435 3591373 := bbase (se 3 (by rfl) ⟨673382, by rfl⟩ : syracuseStep 3591373 = 1346765) (by norm_num)
theorem B4788497 : Blo 1891435 4788497 := bstep (se 2 (by rfl) ⟨1795686, by rfl⟩ : syracuseStep 4788497 = 3591373) B3591373
theorem B3192331 : Blo 1891435 3192331 := bstep (se 1 (by rfl) ⟨2394248, by rfl⟩ : syracuseStep 3192331 = 4788497) B4788497
theorem B4256441 : Blo 1891435 4256441 := bstep (se 2 (by rfl) ⟨1596165, by rfl⟩ : syracuseStep 4256441 = 3192331) B3192331
theorem B2837627 : Blo 1891435 2837627 := bstep (se 1 (by rfl) ⟨2128220, by rfl⟩ : syracuseStep 2837627 = 4256441) B4256441
theorem B1891751 : Blo 1891435 1891751 := bstep (se 1 (by rfl) ⟨1418813, by rfl⟩ : syracuseStep 1891751 = 2837627) B2837627
theorem B2128225 : Blo 1891435 2128225 := bbase (se 2 (by rfl) ⟨798084, by rfl⟩ : syracuseStep 2128225 = 1596169) (by norm_num)
theorem B2837633 : Blo 1891435 2837633 := bstep (se 2 (by rfl) ⟨1064112, by rfl⟩ : syracuseStep 2837633 = 2128225) B2128225
theorem B1891755 : Blo 1891435 1891755 := bstep (se 1 (by rfl) ⟨1418816, by rfl⟩ : syracuseStep 1891755 = 2837633) B2837633
theorem B4788517 : Blo 1891435 4788517 := bbase (se 4 (by rfl) ⟨448923, by rfl⟩ : syracuseStep 4788517 = 897847) (by norm_num)
theorem B6384689 : Blo 1891435 6384689 := bstep (se 2 (by rfl) ⟨2394258, by rfl⟩ : syracuseStep 6384689 = 4788517) B4788517
theorem B4256459 : Blo 1891435 4256459 := bstep (se 1 (by rfl) ⟨3192344, by rfl⟩ : syracuseStep 4256459 = 6384689) B6384689
theorem B2837639 : Blo 1891435 2837639 := bstep (se 1 (by rfl) ⟨2128229, by rfl⟩ : syracuseStep 2837639 = 4256459) B4256459
theorem B1891759 : Blo 1891435 1891759 := bstep (se 1 (by rfl) ⟨1418819, by rfl⟩ : syracuseStep 1891759 = 2837639) B2837639
theorem B2837645 : Blo 1891435 2837645 := bbase (se 3 (by rfl) ⟨532058, by rfl⟩ : syracuseStep 2837645 = 1064117) (by norm_num)
theorem B1891763 : Blo 1891435 1891763 := bstep (se 1 (by rfl) ⟨1418822, by rfl⟩ : syracuseStep 1891763 = 2837645) B2837645
theorem B4256477 : Blo 1891435 4256477 := bbase (se 3 (by rfl) ⟨798089, by rfl⟩ : syracuseStep 4256477 = 1596179) (by norm_num)
theorem B2837651 : Blo 1891435 2837651 := bstep (se 1 (by rfl) ⟨2128238, by rfl⟩ : syracuseStep 2837651 = 4256477) B4256477
theorem B1891767 : Blo 1891435 1891767 := bstep (se 1 (by rfl) ⟨1418825, by rfl⟩ : syracuseStep 1891767 = 2837651) B2837651
theorem B3192365 : Blo 1891435 3192365 := bbase (se 3 (by rfl) ⟨598568, by rfl⟩ : syracuseStep 3192365 = 1197137) (by norm_num)
theorem B2128243 : Blo 1891435 2128243 := bstep (se 1 (by rfl) ⟨1596182, by rfl⟩ : syracuseStep 2128243 = 3192365) B3192365
theorem B2837657 : Blo 1891435 2837657 := bstep (se 2 (by rfl) ⟨1064121, by rfl⟩ : syracuseStep 2837657 = 2128243) B2128243
theorem B1891771 : Blo 1891435 1891771 := bstep (se 1 (by rfl) ⟨1418828, by rfl⟩ : syracuseStep 1891771 = 2837657) B2837657
theorem B2426945 : Blo 1891435 2426945 := bbase (se 2 (by rfl) ⟨910104, by rfl⟩ : syracuseStep 2426945 = 1820209) (by norm_num)
theorem B25887413 : Blo 1891435 25887413 := bstep (se 5 (by rfl) ⟨1213472, by rfl⟩ : syracuseStep 25887413 = 2426945) B2426945
theorem B17258275 : Blo 1891435 17258275 := bstep (se 1 (by rfl) ⟨12943706, by rfl⟩ : syracuseStep 17258275 = 25887413) B25887413
theorem B92044133 : Blo 1891435 92044133 := bstep (se 4 (by rfl) ⟨8629137, by rfl⟩ : syracuseStep 92044133 = 17258275) B17258275
theorem B61362755 : Blo 1891435 61362755 := bstep (se 1 (by rfl) ⟨46022066, by rfl⟩ : syracuseStep 61362755 = 92044133) B92044133
theorem B40908503 : Blo 1891435 40908503 := bstep (se 1 (by rfl) ⟨30681377, by rfl⟩ : syracuseStep 40908503 = 61362755) B61362755
theorem B27272335 : Blo 1891435 27272335 := bstep (se 1 (by rfl) ⟨20454251, by rfl⟩ : syracuseStep 27272335 = 40908503) B40908503
theorem B36363113 : Blo 1891435 36363113 := bstep (se 2 (by rfl) ⟨13636167, by rfl⟩ : syracuseStep 36363113 = 27272335) B27272335
theorem B24242075 : Blo 1891435 24242075 := bstep (se 1 (by rfl) ⟨18181556, by rfl⟩ : syracuseStep 24242075 = 36363113) B36363113
theorem B16161383 : Blo 1891435 16161383 := bstep (se 1 (by rfl) ⟨12121037, by rfl⟩ : syracuseStep 16161383 = 24242075) B24242075
theorem B10774255 : Blo 1891435 10774255 := bstep (se 1 (by rfl) ⟨8080691, by rfl⟩ : syracuseStep 10774255 = 16161383) B16161383
theorem B14365673 : Blo 1891435 14365673 := bstep (se 2 (by rfl) ⟨5387127, by rfl⟩ : syracuseStep 14365673 = 10774255) B10774255
theorem B9577115 : Blo 1891435 9577115 := bstep (se 1 (by rfl) ⟨7182836, by rfl⟩ : syracuseStep 9577115 = 14365673) B14365673
theorem B6384743 : Blo 1891435 6384743 := bstep (se 1 (by rfl) ⟨4788557, by rfl⟩ : syracuseStep 6384743 = 9577115) B9577115
theorem B4256495 : Blo 1891435 4256495 := bstep (se 1 (by rfl) ⟨3192371, by rfl⟩ : syracuseStep 4256495 = 6384743) B6384743
theorem B2837663 : Blo 1891435 2837663 := bstep (se 1 (by rfl) ⟨2128247, by rfl⟩ : syracuseStep 2837663 = 4256495) B4256495
theorem B1891775 : Blo 1891435 1891775 := bstep (se 1 (by rfl) ⟨1418831, by rfl⟩ : syracuseStep 1891775 = 2837663) B2837663
theorem B2837669 : Blo 1891435 2837669 := bbase (se 4 (by rfl) ⟨266031, by rfl⟩ : syracuseStep 2837669 = 532063) (by norm_num)
theorem B1891779 : Blo 1891435 1891779 := bstep (se 1 (by rfl) ⟨1418834, by rfl⟩ : syracuseStep 1891779 = 2837669) B2837669
theorem B2394289 : Blo 1891435 2394289 := bbase (se 2 (by rfl) ⟨897858, by rfl⟩ : syracuseStep 2394289 = 1795717) (by norm_num)
theorem B3192385 : Blo 1891435 3192385 := bstep (se 2 (by rfl) ⟨1197144, by rfl⟩ : syracuseStep 3192385 = 2394289) B2394289
theorem B4256513 : Blo 1891435 4256513 := bstep (se 2 (by rfl) ⟨1596192, by rfl⟩ : syracuseStep 4256513 = 3192385) B3192385
theorem B2837675 : Blo 1891435 2837675 := bstep (se 1 (by rfl) ⟨2128256, by rfl⟩ : syracuseStep 2837675 = 4256513) B4256513
theorem B1891783 : Blo 1891435 1891783 := bstep (se 1 (by rfl) ⟨1418837, by rfl⟩ : syracuseStep 1891783 = 2837675) B2837675
theorem B2128261 : Blo 1891435 2128261 := bbase (se 4 (by rfl) ⟨199524, by rfl⟩ : syracuseStep 2128261 = 399049) (by norm_num)
theorem B2837681 : Blo 1891435 2837681 := bstep (se 2 (by rfl) ⟨1064130, by rfl⟩ : syracuseStep 2837681 = 2128261) B2128261
theorem B1891787 : Blo 1891435 1891787 := bstep (se 1 (by rfl) ⟨1418840, by rfl⟩ : syracuseStep 1891787 = 2837681) B2837681
theorem B4040381 : Blo 1891435 4040381 := bbase (se 3 (by rfl) ⟨757571, by rfl⟩ : syracuseStep 4040381 = 1515143) (by norm_num)
theorem B2693587 : Blo 1891435 2693587 := bstep (se 1 (by rfl) ⟨2020190, by rfl⟩ : syracuseStep 2693587 = 4040381) B4040381
theorem B3591449 : Blo 1891435 3591449 := bstep (se 2 (by rfl) ⟨1346793, by rfl⟩ : syracuseStep 3591449 = 2693587) B2693587
theorem B2394299 : Blo 1891435 2394299 := bstep (se 1 (by rfl) ⟨1795724, by rfl⟩ : syracuseStep 2394299 = 3591449) B3591449
theorem B6384797 : Blo 1891435 6384797 := bstep (se 3 (by rfl) ⟨1197149, by rfl⟩ : syracuseStep 6384797 = 2394299) B2394299
theorem B4256531 : Blo 1891435 4256531 := bstep (se 1 (by rfl) ⟨3192398, by rfl⟩ : syracuseStep 4256531 = 6384797) B6384797
theorem B2837687 : Blo 1891435 2837687 := bstep (se 1 (by rfl) ⟨2128265, by rfl⟩ : syracuseStep 2837687 = 4256531) B4256531
theorem B1891791 : Blo 1891435 1891791 := bstep (se 1 (by rfl) ⟨1418843, by rfl⟩ : syracuseStep 1891791 = 2837687) B2837687
theorem B2837693 : Blo 1891435 2837693 := bbase (se 3 (by rfl) ⟨532067, by rfl⟩ : syracuseStep 2837693 = 1064135) (by norm_num)
theorem B1891795 : Blo 1891435 1891795 := bstep (se 1 (by rfl) ⟨1418846, by rfl⟩ : syracuseStep 1891795 = 2837693) B2837693
theorem B4256549 : Blo 1891435 4256549 := bbase (se 4 (by rfl) ⟨399051, by rfl⟩ : syracuseStep 4256549 = 798103) (by norm_num)
theorem B2837699 : Blo 1891435 2837699 := bstep (se 1 (by rfl) ⟨2128274, by rfl⟩ : syracuseStep 2837699 = 4256549) B4256549
theorem B1891799 : Blo 1891435 1891799 := bstep (se 1 (by rfl) ⟨1418849, by rfl⟩ : syracuseStep 1891799 = 2837699) B2837699
theorem B4788629 : Blo 1891435 4788629 := bbase (se 6 (by rfl) ⟨112233, by rfl⟩ : syracuseStep 4788629 = 224467) (by norm_num)
theorem B3192419 : Blo 1891435 3192419 := bstep (se 1 (by rfl) ⟨2394314, by rfl⟩ : syracuseStep 3192419 = 4788629) B4788629
theorem B2128279 : Blo 1891435 2128279 := bstep (se 1 (by rfl) ⟨1596209, by rfl⟩ : syracuseStep 2128279 = 3192419) B3192419
theorem B2837705 : Blo 1891435 2837705 := bstep (se 2 (by rfl) ⟨1064139, by rfl⟩ : syracuseStep 2837705 = 2128279) B2128279
theorem B1891803 : Blo 1891435 1891803 := bstep (se 1 (by rfl) ⟨1418852, by rfl⟩ : syracuseStep 1891803 = 2837705) B2837705
theorem B2876429 : Blo 1891435 2876429 := bbase (se 3 (by rfl) ⟨539330, by rfl⟩ : syracuseStep 2876429 = 1078661) (by norm_num)
theorem B7670477 : Blo 1891435 7670477 := bstep (se 3 (by rfl) ⟨1438214, by rfl⟩ : syracuseStep 7670477 = 2876429) B2876429
theorem B5113651 : Blo 1891435 5113651 := bstep (se 1 (by rfl) ⟨3835238, by rfl⟩ : syracuseStep 5113651 = 7670477) B7670477
theorem B6818201 : Blo 1891435 6818201 := bstep (se 2 (by rfl) ⟨2556825, by rfl⟩ : syracuseStep 6818201 = 5113651) B5113651
theorem B4545467 : Blo 1891435 4545467 := bstep (se 1 (by rfl) ⟨3409100, by rfl⟩ : syracuseStep 4545467 = 6818201) B6818201
theorem B3030311 : Blo 1891435 3030311 := bstep (se 1 (by rfl) ⟨2272733, by rfl⟩ : syracuseStep 3030311 = 4545467) B4545467
theorem B8080829 : Blo 1891435 8080829 := bstep (se 3 (by rfl) ⟨1515155, by rfl⟩ : syracuseStep 8080829 = 3030311) B3030311
theorem B5387219 : Blo 1891435 5387219 := bstep (se 1 (by rfl) ⟨4040414, by rfl⟩ : syracuseStep 5387219 = 8080829) B8080829
theorem B3591479 : Blo 1891435 3591479 := bstep (se 1 (by rfl) ⟨2693609, by rfl⟩ : syracuseStep 3591479 = 5387219) B5387219
theorem B9577277 : Blo 1891435 9577277 := bstep (se 3 (by rfl) ⟨1795739, by rfl⟩ : syracuseStep 9577277 = 3591479) B3591479
theorem B6384851 : Blo 1891435 6384851 := bstep (se 1 (by rfl) ⟨4788638, by rfl⟩ : syracuseStep 6384851 = 9577277) B9577277
theorem B4256567 : Blo 1891435 4256567 := bstep (se 1 (by rfl) ⟨3192425, by rfl⟩ : syracuseStep 4256567 = 6384851) B6384851
theorem B2837711 : Blo 1891435 2837711 := bstep (se 1 (by rfl) ⟨2128283, by rfl⟩ : syracuseStep 2837711 = 4256567) B4256567
theorem B1891807 : Blo 1891435 1891807 := bstep (se 1 (by rfl) ⟨1418855, by rfl⟩ : syracuseStep 1891807 = 2837711) B2837711
theorem B2837717 : Blo 1891435 2837717 := bbase (se 7 (by rfl) ⟨33254, by rfl⟩ : syracuseStep 2837717 = 66509) (by norm_num)
theorem B1891811 : Blo 1891435 1891811 := bstep (se 1 (by rfl) ⟨1418858, by rfl⟩ : syracuseStep 1891811 = 2837717) B2837717
theorem B2693621 : Blo 1891435 2693621 := bbase (se 5 (by rfl) ⟨126263, by rfl⟩ : syracuseStep 2693621 = 252527) (by norm_num)
theorem B7182989 : Blo 1891435 7182989 := bstep (se 3 (by rfl) ⟨1346810, by rfl⟩ : syracuseStep 7182989 = 2693621) B2693621
theorem B4788659 : Blo 1891435 4788659 := bstep (se 1 (by rfl) ⟨3591494, by rfl⟩ : syracuseStep 4788659 = 7182989) B7182989
theorem B3192439 : Blo 1891435 3192439 := bstep (se 1 (by rfl) ⟨2394329, by rfl⟩ : syracuseStep 3192439 = 4788659) B4788659
theorem B4256585 : Blo 1891435 4256585 := bstep (se 2 (by rfl) ⟨1596219, by rfl⟩ : syracuseStep 4256585 = 3192439) B3192439
theorem B2837723 : Blo 1891435 2837723 := bstep (se 1 (by rfl) ⟨2128292, by rfl⟩ : syracuseStep 2837723 = 4256585) B4256585
theorem B1891815 : Blo 1891435 1891815 := bstep (se 1 (by rfl) ⟨1418861, by rfl⟩ : syracuseStep 1891815 = 2837723) B2837723
theorem B2128297 : Blo 1891435 2128297 := bbase (se 2 (by rfl) ⟨798111, by rfl⟩ : syracuseStep 2128297 = 1596223) (by norm_num)
theorem B2837729 : Blo 1891435 2837729 := bstep (se 2 (by rfl) ⟨1064148, by rfl⟩ : syracuseStep 2837729 = 2128297) B2128297
theorem B1891819 : Blo 1891435 1891819 := bstep (se 1 (by rfl) ⟨1418864, by rfl⟩ : syracuseStep 1891819 = 2837729) B2837729
theorem B6472021 : Blo 1891435 6472021 := bbase (se 10 (by rfl) ⟨9480, by rfl⟩ : syracuseStep 6472021 = 18961) (by norm_num)
theorem B8629361 : Blo 1891435 8629361 := bstep (se 2 (by rfl) ⟨3236010, by rfl⟩ : syracuseStep 8629361 = 6472021) B6472021
theorem B5752907 : Blo 1891435 5752907 := bstep (se 1 (by rfl) ⟨4314680, by rfl⟩ : syracuseStep 5752907 = 8629361) B8629361
theorem B3835271 : Blo 1891435 3835271 := bstep (se 1 (by rfl) ⟨2876453, by rfl⟩ : syracuseStep 3835271 = 5752907) B5752907
theorem B2556847 : Blo 1891435 2556847 := bstep (se 1 (by rfl) ⟨1917635, by rfl⟩ : syracuseStep 2556847 = 3835271) B3835271
theorem B3409129 : Blo 1891435 3409129 := bstep (se 2 (by rfl) ⟨1278423, by rfl⟩ : syracuseStep 3409129 = 2556847) B2556847
theorem B4545505 : Blo 1891435 4545505 := bstep (se 2 (by rfl) ⟨1704564, by rfl⟩ : syracuseStep 4545505 = 3409129) B3409129
theorem B6060673 : Blo 1891435 6060673 := bstep (se 2 (by rfl) ⟨2272752, by rfl⟩ : syracuseStep 6060673 = 4545505) B4545505
theorem B8080897 : Blo 1891435 8080897 := bstep (se 2 (by rfl) ⟨3030336, by rfl⟩ : syracuseStep 8080897 = 6060673) B6060673
theorem B10774529 : Blo 1891435 10774529 := bstep (se 2 (by rfl) ⟨4040448, by rfl⟩ : syracuseStep 10774529 = 8080897) B8080897
theorem B7183019 : Blo 1891435 7183019 := bstep (se 1 (by rfl) ⟨5387264, by rfl⟩ : syracuseStep 7183019 = 10774529) B10774529
theorem B4788679 : Blo 1891435 4788679 := bstep (se 1 (by rfl) ⟨3591509, by rfl⟩ : syracuseStep 4788679 = 7183019) B7183019
theorem B6384905 : Blo 1891435 6384905 := bstep (se 2 (by rfl) ⟨2394339, by rfl⟩ : syracuseStep 6384905 = 4788679) B4788679
theorem B4256603 : Blo 1891435 4256603 := bstep (se 1 (by rfl) ⟨3192452, by rfl⟩ : syracuseStep 4256603 = 6384905) B6384905
theorem B2837735 : Blo 1891435 2837735 := bstep (se 1 (by rfl) ⟨2128301, by rfl⟩ : syracuseStep 2837735 = 4256603) B4256603
theorem B1891823 : Blo 1891435 1891823 := bstep (se 1 (by rfl) ⟨1418867, by rfl⟩ : syracuseStep 1891823 = 2837735) B2837735
theorem B2837741 : Blo 1891435 2837741 := bbase (se 3 (by rfl) ⟨532076, by rfl⟩ : syracuseStep 2837741 = 1064153) (by norm_num)
theorem B1891827 : Blo 1891435 1891827 := bstep (se 1 (by rfl) ⟨1418870, by rfl⟩ : syracuseStep 1891827 = 2837741) B2837741
theorem B4256621 : Blo 1891435 4256621 := bbase (se 3 (by rfl) ⟨798116, by rfl⟩ : syracuseStep 4256621 = 1596233) (by norm_num)
theorem B2837747 : Blo 1891435 2837747 := bstep (se 1 (by rfl) ⟨2128310, by rfl⟩ : syracuseStep 2837747 = 4256621) B4256621
theorem B1891831 : Blo 1891435 1891831 := bstep (se 1 (by rfl) ⟨1418873, by rfl⟩ : syracuseStep 1891831 = 2837747) B2837747
theorem B3591533 : Blo 1891435 3591533 := bbase (se 3 (by rfl) ⟨673412, by rfl⟩ : syracuseStep 3591533 = 1346825) (by norm_num)
theorem B2394355 : Blo 1891435 2394355 := bstep (se 1 (by rfl) ⟨1795766, by rfl⟩ : syracuseStep 2394355 = 3591533) B3591533
theorem B3192473 : Blo 1891435 3192473 := bstep (se 2 (by rfl) ⟨1197177, by rfl⟩ : syracuseStep 3192473 = 2394355) B2394355
theorem B2128315 : Blo 1891435 2128315 := bstep (se 1 (by rfl) ⟨1596236, by rfl⟩ : syracuseStep 2128315 = 3192473) B3192473
theorem B2837753 : Blo 1891435 2837753 := bstep (se 2 (by rfl) ⟨1064157, by rfl⟩ : syracuseStep 2837753 = 2128315) B2128315
theorem B1891835 : Blo 1891435 1891835 := bstep (se 1 (by rfl) ⟨1418876, by rfl⟩ : syracuseStep 1891835 = 2837753) B2837753
theorem B5535317 : Blo 1891435 5535317 := bbase (se 8 (by rfl) ⟨32433, by rfl⟩ : syracuseStep 5535317 = 64867) (by norm_num)
theorem B3690211 : Blo 1891435 3690211 := bstep (se 1 (by rfl) ⟨2767658, by rfl⟩ : syracuseStep 3690211 = 5535317) B5535317
theorem B4920281 : Blo 1891435 4920281 := bstep (se 2 (by rfl) ⟨1845105, by rfl⟩ : syracuseStep 4920281 = 3690211) B3690211
theorem B3280187 : Blo 1891435 3280187 := bstep (se 1 (by rfl) ⟨2460140, by rfl⟩ : syracuseStep 3280187 = 4920281) B4920281
theorem B8747165 : Blo 1891435 8747165 := bstep (se 3 (by rfl) ⟨1640093, by rfl⟩ : syracuseStep 8747165 = 3280187) B3280187
theorem B5831443 : Blo 1891435 5831443 := bstep (se 1 (by rfl) ⟨4373582, by rfl⟩ : syracuseStep 5831443 = 8747165) B8747165
theorem B7775257 : Blo 1891435 7775257 := bstep (se 2 (by rfl) ⟨2915721, by rfl⟩ : syracuseStep 7775257 = 5831443) B5831443
theorem B10367009 : Blo 1891435 10367009 := bstep (se 2 (by rfl) ⟨3887628, by rfl⟩ : syracuseStep 10367009 = 7775257) B7775257
theorem B6911339 : Blo 1891435 6911339 := bstep (se 1 (by rfl) ⟨5183504, by rfl⟩ : syracuseStep 6911339 = 10367009) B10367009
theorem B18430237 : Blo 1891435 18430237 := bstep (se 3 (by rfl) ⟨3455669, by rfl⟩ : syracuseStep 18430237 = 6911339) B6911339
theorem B98294597 : Blo 1891435 98294597 := bstep (se 4 (by rfl) ⟨9215118, by rfl⟩ : syracuseStep 98294597 = 18430237) B18430237
theorem B65529731 : Blo 1891435 65529731 := bstep (se 1 (by rfl) ⟨49147298, by rfl⟩ : syracuseStep 65529731 = 98294597) B98294597
theorem B43686487 : Blo 1891435 43686487 := bstep (se 1 (by rfl) ⟨32764865, by rfl⟩ : syracuseStep 43686487 = 65529731) B65529731
theorem B58248649 : Blo 1891435 58248649 := bstep (se 2 (by rfl) ⟨21843243, by rfl⟩ : syracuseStep 58248649 = 43686487) B43686487
theorem B77664865 : Blo 1891435 77664865 := bstep (se 2 (by rfl) ⟨29124324, by rfl⟩ : syracuseStep 77664865 = 58248649) B58248649
theorem B103553153 : Blo 1891435 103553153 := bstep (se 2 (by rfl) ⟨38832432, by rfl⟩ : syracuseStep 103553153 = 77664865) B77664865
theorem B69035435 : Blo 1891435 69035435 := bstep (se 1 (by rfl) ⟨51776576, by rfl⟩ : syracuseStep 69035435 = 103553153) B103553153
theorem B46023623 : Blo 1891435 46023623 := bstep (se 1 (by rfl) ⟨34517717, by rfl⟩ : syracuseStep 46023623 = 69035435) B69035435
theorem B30682415 : Blo 1891435 30682415 := bstep (se 1 (by rfl) ⟨23011811, by rfl⟩ : syracuseStep 30682415 = 46023623) B46023623
theorem B20454943 : Blo 1891435 20454943 := bstep (se 1 (by rfl) ⟨15341207, by rfl⟩ : syracuseStep 20454943 = 30682415) B30682415
theorem B27273257 : Blo 1891435 27273257 := bstep (se 2 (by rfl) ⟨10227471, by rfl⟩ : syracuseStep 27273257 = 20454943) B20454943
theorem B18182171 : Blo 1891435 18182171 := bstep (se 1 (by rfl) ⟨13636628, by rfl⟩ : syracuseStep 18182171 = 27273257) B27273257
theorem B48485789 : Blo 1891435 48485789 := bstep (se 3 (by rfl) ⟨9091085, by rfl⟩ : syracuseStep 48485789 = 18182171) B18182171
theorem B32323859 : Blo 1891435 32323859 := bstep (se 1 (by rfl) ⟨24242894, by rfl⟩ : syracuseStep 32323859 = 48485789) B48485789
theorem B21549239 : Blo 1891435 21549239 := bstep (se 1 (by rfl) ⟨16161929, by rfl⟩ : syracuseStep 21549239 = 32323859) B32323859
theorem B14366159 : Blo 1891435 14366159 := bstep (se 1 (by rfl) ⟨10774619, by rfl⟩ : syracuseStep 14366159 = 21549239) B21549239
theorem B9577439 : Blo 1891435 9577439 := bstep (se 1 (by rfl) ⟨7183079, by rfl⟩ : syracuseStep 9577439 = 14366159) B14366159
theorem B6384959 : Blo 1891435 6384959 := bstep (se 1 (by rfl) ⟨4788719, by rfl⟩ : syracuseStep 6384959 = 9577439) B9577439
theorem B4256639 : Blo 1891435 4256639 := bstep (se 1 (by rfl) ⟨3192479, by rfl⟩ : syracuseStep 4256639 = 6384959) B6384959
theorem B2837759 : Blo 1891435 2837759 := bstep (se 1 (by rfl) ⟨2128319, by rfl⟩ : syracuseStep 2837759 = 4256639) B4256639
theorem B1891839 : Blo 1891435 1891839 := bstep (se 1 (by rfl) ⟨1418879, by rfl⟩ : syracuseStep 1891839 = 2837759) B2837759
theorem B2837765 : Blo 1891435 2837765 := bbase (se 4 (by rfl) ⟨266040, by rfl⟩ : syracuseStep 2837765 = 532081) (by norm_num)
theorem B1891843 : Blo 1891435 1891843 := bstep (se 1 (by rfl) ⟨1418882, by rfl⟩ : syracuseStep 1891843 = 2837765) B2837765
theorem B3192493 : Blo 1891435 3192493 := bbase (se 3 (by rfl) ⟨598592, by rfl⟩ : syracuseStep 3192493 = 1197185) (by norm_num)
theorem B4256657 : Blo 1891435 4256657 := bstep (se 2 (by rfl) ⟨1596246, by rfl⟩ : syracuseStep 4256657 = 3192493) B3192493
theorem B2837771 : Blo 1891435 2837771 := bstep (se 1 (by rfl) ⟨2128328, by rfl⟩ : syracuseStep 2837771 = 4256657) B4256657
theorem B1891847 : Blo 1891435 1891847 := bstep (se 1 (by rfl) ⟨1418885, by rfl⟩ : syracuseStep 1891847 = 2837771) B2837771
theorem B2128333 : Blo 1891435 2128333 := bbase (se 3 (by rfl) ⟨399062, by rfl⟩ : syracuseStep 2128333 = 798125) (by norm_num)
theorem B2837777 : Blo 1891435 2837777 := bstep (se 2 (by rfl) ⟨1064166, by rfl⟩ : syracuseStep 2837777 = 2128333) B2128333
theorem B1891851 : Blo 1891435 1891851 := bstep (se 1 (by rfl) ⟨1418888, by rfl⟩ : syracuseStep 1891851 = 2837777) B2837777
theorem B6385013 : Blo 1891435 6385013 := bbase (se 5 (by rfl) ⟨299297, by rfl⟩ : syracuseStep 6385013 = 598595) (by norm_num)
theorem B4256675 : Blo 1891435 4256675 := bstep (se 1 (by rfl) ⟨3192506, by rfl⟩ : syracuseStep 4256675 = 6385013) B6385013
theorem B2837783 : Blo 1891435 2837783 := bstep (se 1 (by rfl) ⟨2128337, by rfl⟩ : syracuseStep 2837783 = 4256675) B4256675
theorem B1891855 : Blo 1891435 1891855 := bstep (se 1 (by rfl) ⟨1418891, by rfl⟩ : syracuseStep 1891855 = 2837783) B2837783
theorem B2837789 : Blo 1891435 2837789 := bbase (se 3 (by rfl) ⟨532085, by rfl⟩ : syracuseStep 2837789 = 1064171) (by norm_num)
theorem B1891859 : Blo 1891435 1891859 := bstep (se 1 (by rfl) ⟨1418894, by rfl⟩ : syracuseStep 1891859 = 2837789) B2837789
theorem B4256693 : Blo 1891435 4256693 := bbase (se 5 (by rfl) ⟨199532, by rfl⟩ : syracuseStep 4256693 = 399065) (by norm_num)
theorem B2837795 : Blo 1891435 2837795 := bstep (se 1 (by rfl) ⟨2128346, by rfl⟩ : syracuseStep 2837795 = 4256693) B4256693
theorem B1891863 : Blo 1891435 1891863 := bstep (se 1 (by rfl) ⟨1418897, by rfl⟩ : syracuseStep 1891863 = 2837795) B2837795
theorem B20455253 : Blo 1891435 20455253 := bbase (se 9 (by rfl) ⟨59927, by rfl⟩ : syracuseStep 20455253 = 119855) (by norm_num)
theorem B13636835 : Blo 1891435 13636835 := bstep (se 1 (by rfl) ⟨10227626, by rfl⟩ : syracuseStep 13636835 = 20455253) B20455253
theorem B9091223 : Blo 1891435 9091223 := bstep (se 1 (by rfl) ⟨6818417, by rfl⟩ : syracuseStep 9091223 = 13636835) B13636835
theorem B6060815 : Blo 1891435 6060815 := bstep (se 1 (by rfl) ⟨4545611, by rfl⟩ : syracuseStep 6060815 = 9091223) B9091223
theorem B4040543 : Blo 1891435 4040543 := bstep (se 1 (by rfl) ⟨3030407, by rfl⟩ : syracuseStep 4040543 = 6060815) B6060815
theorem B10774781 : Blo 1891435 10774781 := bstep (se 3 (by rfl) ⟨2020271, by rfl⟩ : syracuseStep 10774781 = 4040543) B4040543
theorem B7183187 : Blo 1891435 7183187 := bstep (se 1 (by rfl) ⟨5387390, by rfl⟩ : syracuseStep 7183187 = 10774781) B10774781
theorem B4788791 : Blo 1891435 4788791 := bstep (se 1 (by rfl) ⟨3591593, by rfl⟩ : syracuseStep 4788791 = 7183187) B7183187
theorem B3192527 : Blo 1891435 3192527 := bstep (se 1 (by rfl) ⟨2394395, by rfl⟩ : syracuseStep 3192527 = 4788791) B4788791
theorem B2128351 : Blo 1891435 2128351 := bstep (se 1 (by rfl) ⟨1596263, by rfl⟩ : syracuseStep 2128351 = 3192527) B3192527
theorem B2837801 : Blo 1891435 2837801 := bstep (se 2 (by rfl) ⟨1064175, by rfl⟩ : syracuseStep 2837801 = 2128351) B2128351
theorem B1891867 : Blo 1891435 1891867 := bstep (se 1 (by rfl) ⟨1418900, by rfl⟩ : syracuseStep 1891867 = 2837801) B2837801
theorem B10367189 : Blo 1891435 10367189 := bbase (se 7 (by rfl) ⟨121490, by rfl⟩ : syracuseStep 10367189 = 242981) (by norm_num)
theorem B6911459 : Blo 1891435 6911459 := bstep (se 1 (by rfl) ⟨5183594, by rfl⟩ : syracuseStep 6911459 = 10367189) B10367189
theorem B4607639 : Blo 1891435 4607639 := bstep (se 1 (by rfl) ⟨3455729, by rfl⟩ : syracuseStep 4607639 = 6911459) B6911459
theorem B3071759 : Blo 1891435 3071759 := bstep (se 1 (by rfl) ⟨2303819, by rfl⟩ : syracuseStep 3071759 = 4607639) B4607639
theorem B32765429 : Blo 1891435 32765429 := bstep (se 5 (by rfl) ⟨1535879, by rfl⟩ : syracuseStep 32765429 = 3071759) B3071759
theorem B87374477 : Blo 1891435 87374477 := bstep (se 3 (by rfl) ⟨16382714, by rfl⟩ : syracuseStep 87374477 = 32765429) B32765429
theorem B58249651 : Blo 1891435 58249651 := bstep (se 1 (by rfl) ⟨43687238, by rfl⟩ : syracuseStep 58249651 = 87374477) B87374477
theorem B77666201 : Blo 1891435 77666201 := bstep (se 2 (by rfl) ⟨29124825, by rfl⟩ : syracuseStep 77666201 = 58249651) B58249651
theorem B51777467 : Blo 1891435 51777467 := bstep (se 1 (by rfl) ⟨38833100, by rfl⟩ : syracuseStep 51777467 = 77666201) B77666201
theorem B34518311 : Blo 1891435 34518311 := bstep (se 1 (by rfl) ⟨25888733, by rfl⟩ : syracuseStep 34518311 = 51777467) B51777467
theorem B23012207 : Blo 1891435 23012207 := bstep (se 1 (by rfl) ⟨17259155, by rfl⟩ : syracuseStep 23012207 = 34518311) B34518311
theorem B15341471 : Blo 1891435 15341471 := bstep (se 1 (by rfl) ⟨11506103, by rfl⟩ : syracuseStep 15341471 = 23012207) B23012207
theorem B10227647 : Blo 1891435 10227647 := bstep (se 1 (by rfl) ⟨7670735, by rfl⟩ : syracuseStep 10227647 = 15341471) B15341471
theorem B6818431 : Blo 1891435 6818431 := bstep (se 1 (by rfl) ⟨5113823, by rfl⟩ : syracuseStep 6818431 = 10227647) B10227647
theorem B9091241 : Blo 1891435 9091241 := bstep (se 2 (by rfl) ⟨3409215, by rfl⟩ : syracuseStep 9091241 = 6818431) B6818431
theorem B6060827 : Blo 1891435 6060827 := bstep (se 1 (by rfl) ⟨4545620, by rfl⟩ : syracuseStep 6060827 = 9091241) B9091241
theorem B4040551 : Blo 1891435 4040551 := bstep (se 1 (by rfl) ⟨3030413, by rfl⟩ : syracuseStep 4040551 = 6060827) B6060827
theorem B5387401 : Blo 1891435 5387401 := bstep (se 2 (by rfl) ⟨2020275, by rfl⟩ : syracuseStep 5387401 = 4040551) B4040551
theorem B7183201 : Blo 1891435 7183201 := bstep (se 2 (by rfl) ⟨2693700, by rfl⟩ : syracuseStep 7183201 = 5387401) B5387401
theorem B9577601 : Blo 1891435 9577601 := bstep (se 2 (by rfl) ⟨3591600, by rfl⟩ : syracuseStep 9577601 = 7183201) B7183201
theorem B6385067 : Blo 1891435 6385067 := bstep (se 1 (by rfl) ⟨4788800, by rfl⟩ : syracuseStep 6385067 = 9577601) B9577601
theorem B4256711 : Blo 1891435 4256711 := bstep (se 1 (by rfl) ⟨3192533, by rfl⟩ : syracuseStep 4256711 = 6385067) B6385067
theorem B2837807 : Blo 1891435 2837807 := bstep (se 1 (by rfl) ⟨2128355, by rfl⟩ : syracuseStep 2837807 = 4256711) B4256711
theorem B1891871 : Blo 1891435 1891871 := bstep (se 1 (by rfl) ⟨1418903, by rfl⟩ : syracuseStep 1891871 = 2837807) B2837807
theorem B2837813 : Blo 1891435 2837813 := bbase (se 5 (by rfl) ⟨133022, by rfl⟩ : syracuseStep 2837813 = 266045) (by norm_num)
theorem B1891875 : Blo 1891435 1891875 := bstep (se 1 (by rfl) ⟨1418906, by rfl⟩ : syracuseStep 1891875 = 2837813) B2837813
theorem B4788821 : Blo 1891435 4788821 := bbase (se 8 (by rfl) ⟨28059, by rfl⟩ : syracuseStep 4788821 = 56119) (by norm_num)
theorem B3192547 : Blo 1891435 3192547 := bstep (se 1 (by rfl) ⟨2394410, by rfl⟩ : syracuseStep 3192547 = 4788821) B4788821
theorem B4256729 : Blo 1891435 4256729 := bstep (se 2 (by rfl) ⟨1596273, by rfl⟩ : syracuseStep 4256729 = 3192547) B3192547
theorem B2837819 : Blo 1891435 2837819 := bstep (se 1 (by rfl) ⟨2128364, by rfl⟩ : syracuseStep 2837819 = 4256729) B4256729
theorem B1891879 : Blo 1891435 1891879 := bstep (se 1 (by rfl) ⟨1418909, by rfl⟩ : syracuseStep 1891879 = 2837819) B2837819
theorem B2128369 : Blo 1891435 2128369 := bbase (se 2 (by rfl) ⟨798138, by rfl⟩ : syracuseStep 2128369 = 1596277) (by norm_num)
theorem B2837825 : Blo 1891435 2837825 := bstep (se 2 (by rfl) ⟨1064184, by rfl⟩ : syracuseStep 2837825 = 2128369) B2128369
theorem B1891883 : Blo 1891435 1891883 := bstep (se 1 (by rfl) ⟨1418912, by rfl⟩ : syracuseStep 1891883 = 2837825) B2837825
theorem B2157413 : Blo 1891435 2157413 := bbase (se 4 (by rfl) ⟨202257, by rfl⟩ : syracuseStep 2157413 = 404515) (by norm_num)
theorem B5753101 : Blo 1891435 5753101 := bstep (se 3 (by rfl) ⟨1078706, by rfl⟩ : syracuseStep 5753101 = 2157413) B2157413
theorem B7670801 : Blo 1891435 7670801 := bstep (se 2 (by rfl) ⟨2876550, by rfl⟩ : syracuseStep 7670801 = 5753101) B5753101
theorem B5113867 : Blo 1891435 5113867 := bstep (se 1 (by rfl) ⟨3835400, by rfl⟩ : syracuseStep 5113867 = 7670801) B7670801
theorem B6818489 : Blo 1891435 6818489 := bstep (se 2 (by rfl) ⟨2556933, by rfl⟩ : syracuseStep 6818489 = 5113867) B5113867
theorem B4545659 : Blo 1891435 4545659 := bstep (se 1 (by rfl) ⟨3409244, by rfl⟩ : syracuseStep 4545659 = 6818489) B6818489
theorem B12121757 : Blo 1891435 12121757 := bstep (se 3 (by rfl) ⟨2272829, by rfl⟩ : syracuseStep 12121757 = 4545659) B4545659
theorem B8081171 : Blo 1891435 8081171 := bstep (se 1 (by rfl) ⟨6060878, by rfl⟩ : syracuseStep 8081171 = 12121757) B12121757
theorem B5387447 : Blo 1891435 5387447 := bstep (se 1 (by rfl) ⟨4040585, by rfl⟩ : syracuseStep 5387447 = 8081171) B8081171
theorem B3591631 : Blo 1891435 3591631 := bstep (se 1 (by rfl) ⟨2693723, by rfl⟩ : syracuseStep 3591631 = 5387447) B5387447
theorem B4788841 : Blo 1891435 4788841 := bstep (se 2 (by rfl) ⟨1795815, by rfl⟩ : syracuseStep 4788841 = 3591631) B3591631
theorem B6385121 : Blo 1891435 6385121 := bstep (se 2 (by rfl) ⟨2394420, by rfl⟩ : syracuseStep 6385121 = 4788841) B4788841
theorem B4256747 : Blo 1891435 4256747 := bstep (se 1 (by rfl) ⟨3192560, by rfl⟩ : syracuseStep 4256747 = 6385121) B6385121
theorem B2837831 : Blo 1891435 2837831 := bstep (se 1 (by rfl) ⟨2128373, by rfl⟩ : syracuseStep 2837831 = 4256747) B4256747
theorem B1891887 : Blo 1891435 1891887 := bstep (se 1 (by rfl) ⟨1418915, by rfl⟩ : syracuseStep 1891887 = 2837831) B2837831
theorem B2837837 : Blo 1891435 2837837 := bbase (se 3 (by rfl) ⟨532094, by rfl⟩ : syracuseStep 2837837 = 1064189) (by norm_num)
theorem B1891891 : Blo 1891435 1891891 := bstep (se 1 (by rfl) ⟨1418918, by rfl⟩ : syracuseStep 1891891 = 2837837) B2837837
theorem B4256765 : Blo 1891435 4256765 := bbase (se 3 (by rfl) ⟨798143, by rfl⟩ : syracuseStep 4256765 = 1596287) (by norm_num)
theorem B2837843 : Blo 1891435 2837843 := bstep (se 1 (by rfl) ⟨2128382, by rfl⟩ : syracuseStep 2837843 = 4256765) B4256765
theorem B1891895 : Blo 1891435 1891895 := bstep (se 1 (by rfl) ⟨1418921, by rfl⟩ : syracuseStep 1891895 = 2837843) B2837843
theorem B3192581 : Blo 1891435 3192581 := bbase (se 4 (by rfl) ⟨299304, by rfl⟩ : syracuseStep 3192581 = 598609) (by norm_num)
theorem B2128387 : Blo 1891435 2128387 := bstep (se 1 (by rfl) ⟨1596290, by rfl⟩ : syracuseStep 2128387 = 3192581) B3192581
theorem B2837849 : Blo 1891435 2837849 := bstep (se 2 (by rfl) ⟨1064193, by rfl⟩ : syracuseStep 2837849 = 2128387) B2128387
theorem B1891899 : Blo 1891435 1891899 := bstep (se 1 (by rfl) ⟨1418924, by rfl⟩ : syracuseStep 1891899 = 2837849) B2837849
theorem B14366645 : Blo 1891435 14366645 := bbase (se 5 (by rfl) ⟨673436, by rfl⟩ : syracuseStep 14366645 = 1346873) (by norm_num)
theorem B9577763 : Blo 1891435 9577763 := bstep (se 1 (by rfl) ⟨7183322, by rfl⟩ : syracuseStep 9577763 = 14366645) B14366645
theorem B6385175 : Blo 1891435 6385175 := bstep (se 1 (by rfl) ⟨4788881, by rfl⟩ : syracuseStep 6385175 = 9577763) B9577763
theorem B4256783 : Blo 1891435 4256783 := bstep (se 1 (by rfl) ⟨3192587, by rfl⟩ : syracuseStep 4256783 = 6385175) B6385175
theorem B2837855 : Blo 1891435 2837855 := bstep (se 1 (by rfl) ⟨2128391, by rfl⟩ : syracuseStep 2837855 = 4256783) B4256783
theorem B1891903 : Blo 1891435 1891903 := bstep (se 1 (by rfl) ⟨1418927, by rfl⟩ : syracuseStep 1891903 = 2837855) B2837855
theorem B2837861 : Blo 1891435 2837861 := bbase (se 4 (by rfl) ⟨266049, by rfl⟩ : syracuseStep 2837861 = 532099) (by norm_num)
theorem B1891907 : Blo 1891435 1891907 := bstep (se 1 (by rfl) ⟨1418930, by rfl⟩ : syracuseStep 1891907 = 2837861) B2837861
theorem B3591677 : Blo 1891435 3591677 := bbase (se 3 (by rfl) ⟨673439, by rfl⟩ : syracuseStep 3591677 = 1346879) (by norm_num)
theorem B2394451 : Blo 1891435 2394451 := bstep (se 1 (by rfl) ⟨1795838, by rfl⟩ : syracuseStep 2394451 = 3591677) B3591677
theorem B3192601 : Blo 1891435 3192601 := bstep (se 2 (by rfl) ⟨1197225, by rfl⟩ : syracuseStep 3192601 = 2394451) B2394451
theorem B4256801 : Blo 1891435 4256801 := bstep (se 2 (by rfl) ⟨1596300, by rfl⟩ : syracuseStep 4256801 = 3192601) B3192601
theorem B2837867 : Blo 1891435 2837867 := bstep (se 1 (by rfl) ⟨2128400, by rfl⟩ : syracuseStep 2837867 = 4256801) B4256801
theorem B1891911 : Blo 1891435 1891911 := bstep (se 1 (by rfl) ⟨1418933, by rfl⟩ : syracuseStep 1891911 = 2837867) B2837867
theorem B2128405 : Blo 1891435 2128405 := bbase (se 6 (by rfl) ⟨49884, by rfl⟩ : syracuseStep 2128405 = 99769) (by norm_num)
theorem B2837873 : Blo 1891435 2837873 := bstep (se 2 (by rfl) ⟨1064202, by rfl⟩ : syracuseStep 2837873 = 2128405) B2128405
theorem B1891915 : Blo 1891435 1891915 := bstep (se 1 (by rfl) ⟨1418936, by rfl⟩ : syracuseStep 1891915 = 2837873) B2837873
theorem B2394461 : Blo 1891435 2394461 := bbase (se 3 (by rfl) ⟨448961, by rfl⟩ : syracuseStep 2394461 = 897923) (by norm_num)
theorem B6385229 : Blo 1891435 6385229 := bstep (se 3 (by rfl) ⟨1197230, by rfl⟩ : syracuseStep 6385229 = 2394461) B2394461
theorem B4256819 : Blo 1891435 4256819 := bstep (se 1 (by rfl) ⟨3192614, by rfl⟩ : syracuseStep 4256819 = 6385229) B6385229
theorem B2837879 : Blo 1891435 2837879 := bstep (se 1 (by rfl) ⟨2128409, by rfl⟩ : syracuseStep 2837879 = 4256819) B4256819
theorem B1891919 : Blo 1891435 1891919 := bstep (se 1 (by rfl) ⟨1418939, by rfl⟩ : syracuseStep 1891919 = 2837879) B2837879
theorem B2837885 : Blo 1891435 2837885 := bbase (se 3 (by rfl) ⟨532103, by rfl⟩ : syracuseStep 2837885 = 1064207) (by norm_num)
theorem B1891923 : Blo 1891435 1891923 := bstep (se 1 (by rfl) ⟨1418942, by rfl⟩ : syracuseStep 1891923 = 2837885) B2837885
theorem B4256837 : Blo 1891435 4256837 := bbase (se 4 (by rfl) ⟨399078, by rfl⟩ : syracuseStep 4256837 = 798157) (by norm_num)
theorem B2837891 : Blo 1891435 2837891 := bstep (se 1 (by rfl) ⟨2128418, by rfl⟩ : syracuseStep 2837891 = 4256837) B4256837
theorem B1891927 : Blo 1891435 1891927 := bstep (se 1 (by rfl) ⟨1418945, by rfl⟩ : syracuseStep 1891927 = 2837891) B2837891
theorem B5387573 : Blo 1891435 5387573 := bbase (se 5 (by rfl) ⟨252542, by rfl⟩ : syracuseStep 5387573 = 505085) (by norm_num)
theorem B3591715 : Blo 1891435 3591715 := bstep (se 1 (by rfl) ⟨2693786, by rfl⟩ : syracuseStep 3591715 = 5387573) B5387573
theorem B4788953 : Blo 1891435 4788953 := bstep (se 2 (by rfl) ⟨1795857, by rfl⟩ : syracuseStep 4788953 = 3591715) B3591715
theorem B3192635 : Blo 1891435 3192635 := bstep (se 1 (by rfl) ⟨2394476, by rfl⟩ : syracuseStep 3192635 = 4788953) B4788953
theorem B2128423 : Blo 1891435 2128423 := bstep (se 1 (by rfl) ⟨1596317, by rfl⟩ : syracuseStep 2128423 = 3192635) B3192635
theorem B2837897 : Blo 1891435 2837897 := bstep (se 2 (by rfl) ⟨1064211, by rfl⟩ : syracuseStep 2837897 = 2128423) B2128423
theorem B1891931 : Blo 1891435 1891931 := bstep (se 1 (by rfl) ⟨1418948, by rfl⟩ : syracuseStep 1891931 = 2837897) B2837897
theorem B9577925 : Blo 1891435 9577925 := bbase (se 4 (by rfl) ⟨897930, by rfl⟩ : syracuseStep 9577925 = 1795861) (by norm_num)
theorem B6385283 : Blo 1891435 6385283 := bstep (se 1 (by rfl) ⟨4788962, by rfl⟩ : syracuseStep 6385283 = 9577925) B9577925
theorem B4256855 : Blo 1891435 4256855 := bstep (se 1 (by rfl) ⟨3192641, by rfl⟩ : syracuseStep 4256855 = 6385283) B6385283
theorem B2837903 : Blo 1891435 2837903 := bstep (se 1 (by rfl) ⟨2128427, by rfl⟩ : syracuseStep 2837903 = 4256855) B4256855
theorem B1891935 : Blo 1891435 1891935 := bstep (se 1 (by rfl) ⟨1418951, by rfl⟩ : syracuseStep 1891935 = 2837903) B2837903
theorem B2837909 : Blo 1891435 2837909 := bbase (se 6 (by rfl) ⟨66513, by rfl⟩ : syracuseStep 2837909 = 133027) (by norm_num)
theorem B1891939 : Blo 1891435 1891939 := bstep (se 1 (by rfl) ⟨1418954, by rfl⟩ : syracuseStep 1891939 = 2837909) B2837909
theorem B2272897 : Blo 1891435 2272897 := bbase (se 2 (by rfl) ⟨852336, by rfl⟩ : syracuseStep 2272897 = 1704673) (by norm_num)
theorem B3030529 : Blo 1891435 3030529 := bstep (se 2 (by rfl) ⟨1136448, by rfl⟩ : syracuseStep 3030529 = 2272897) B2272897
theorem B4040705 : Blo 1891435 4040705 := bstep (se 2 (by rfl) ⟨1515264, by rfl⟩ : syracuseStep 4040705 = 3030529) B3030529
theorem B10775213 : Blo 1891435 10775213 := bstep (se 3 (by rfl) ⟨2020352, by rfl⟩ : syracuseStep 10775213 = 4040705) B4040705
theorem B7183475 : Blo 1891435 7183475 := bstep (se 1 (by rfl) ⟨5387606, by rfl⟩ : syracuseStep 7183475 = 10775213) B10775213
theorem B4788983 : Blo 1891435 4788983 := bstep (se 1 (by rfl) ⟨3591737, by rfl⟩ : syracuseStep 4788983 = 7183475) B7183475
theorem B3192655 : Blo 1891435 3192655 := bstep (se 1 (by rfl) ⟨2394491, by rfl⟩ : syracuseStep 3192655 = 4788983) B4788983
theorem B4256873 : Blo 1891435 4256873 := bstep (se 2 (by rfl) ⟨1596327, by rfl⟩ : syracuseStep 4256873 = 3192655) B3192655
theorem B2837915 : Blo 1891435 2837915 := bstep (se 1 (by rfl) ⟨2128436, by rfl⟩ : syracuseStep 2837915 = 4256873) B4256873
theorem B1891943 : Blo 1891435 1891943 := bstep (se 1 (by rfl) ⟨1418957, by rfl⟩ : syracuseStep 1891943 = 2837915) B2837915
theorem B2128441 : Blo 1891435 2128441 := bbase (se 2 (by rfl) ⟨798165, by rfl⟩ : syracuseStep 2128441 = 1596331) (by norm_num)
theorem B2837921 : Blo 1891435 2837921 := bstep (se 2 (by rfl) ⟨1064220, by rfl⟩ : syracuseStep 2837921 = 2128441) B2128441
theorem B1891947 : Blo 1891435 1891947 := bstep (se 1 (by rfl) ⟨1418960, by rfl⟩ : syracuseStep 1891947 = 2837921) B2837921
theorem B2020361 : Blo 1891435 2020361 := bbase (se 2 (by rfl) ⟨757635, by rfl⟩ : syracuseStep 2020361 = 1515271) (by norm_num)
theorem B5387629 : Blo 1891435 5387629 := bstep (se 3 (by rfl) ⟨1010180, by rfl⟩ : syracuseStep 5387629 = 2020361) B2020361
theorem B7183505 : Blo 1891435 7183505 := bstep (se 2 (by rfl) ⟨2693814, by rfl⟩ : syracuseStep 7183505 = 5387629) B5387629
theorem B4789003 : Blo 1891435 4789003 := bstep (se 1 (by rfl) ⟨3591752, by rfl⟩ : syracuseStep 4789003 = 7183505) B7183505
theorem B6385337 : Blo 1891435 6385337 := bstep (se 2 (by rfl) ⟨2394501, by rfl⟩ : syracuseStep 6385337 = 4789003) B4789003
theorem B4256891 : Blo 1891435 4256891 := bstep (se 1 (by rfl) ⟨3192668, by rfl⟩ : syracuseStep 4256891 = 6385337) B6385337
theorem B2837927 : Blo 1891435 2837927 := bstep (se 1 (by rfl) ⟨2128445, by rfl⟩ : syracuseStep 2837927 = 4256891) B4256891
theorem B1891951 : Blo 1891435 1891951 := bstep (se 1 (by rfl) ⟨1418963, by rfl⟩ : syracuseStep 1891951 = 2837927) B2837927
theorem B2837933 : Blo 1891435 2837933 := bbase (se 3 (by rfl) ⟨532112, by rfl⟩ : syracuseStep 2837933 = 1064225) (by norm_num)
theorem B1891955 : Blo 1891435 1891955 := bstep (se 1 (by rfl) ⟨1418966, by rfl⟩ : syracuseStep 1891955 = 2837933) B2837933
theorem B4256909 : Blo 1891435 4256909 := bbase (se 3 (by rfl) ⟨798170, by rfl⟩ : syracuseStep 4256909 = 1596341) (by norm_num)
theorem B2837939 : Blo 1891435 2837939 := bstep (se 1 (by rfl) ⟨2128454, by rfl⟩ : syracuseStep 2837939 = 4256909) B4256909
theorem B1891959 : Blo 1891435 1891959 := bstep (se 1 (by rfl) ⟨1418969, by rfl⟩ : syracuseStep 1891959 = 2837939) B2837939
theorem B2394517 : Blo 1891435 2394517 := bbase (se 6 (by rfl) ⟨56121, by rfl⟩ : syracuseStep 2394517 = 112243) (by norm_num)
theorem B3192689 : Blo 1891435 3192689 := bstep (se 2 (by rfl) ⟨1197258, by rfl⟩ : syracuseStep 3192689 = 2394517) B2394517
theorem B2128459 : Blo 1891435 2128459 := bstep (se 1 (by rfl) ⟨1596344, by rfl⟩ : syracuseStep 2128459 = 3192689) B3192689
theorem B2837945 : Blo 1891435 2837945 := bstep (se 2 (by rfl) ⟨1064229, by rfl⟩ : syracuseStep 2837945 = 2128459) B2128459
theorem B1891963 : Blo 1891435 1891963 := bstep (se 1 (by rfl) ⟨1418972, by rfl⟩ : syracuseStep 1891963 = 2837945) B2837945
theorem B3740813 : Blo 1891435 3740813 := bbase (se 3 (by rfl) ⟨701402, by rfl⟩ : syracuseStep 3740813 = 1402805) (by norm_num)
theorem B2493875 : Blo 1891435 2493875 := bstep (se 1 (by rfl) ⟨1870406, by rfl⟩ : syracuseStep 2493875 = 3740813) B3740813
theorem B6650333 : Blo 1891435 6650333 := bstep (se 3 (by rfl) ⟨1246937, by rfl⟩ : syracuseStep 6650333 = 2493875) B2493875
theorem B4433555 : Blo 1891435 4433555 := bstep (se 1 (by rfl) ⟨3325166, by rfl⟩ : syracuseStep 4433555 = 6650333) B6650333
theorem B2955703 : Blo 1891435 2955703 := bstep (se 1 (by rfl) ⟨2216777, by rfl⟩ : syracuseStep 2955703 = 4433555) B4433555
theorem B3940937 : Blo 1891435 3940937 := bstep (se 2 (by rfl) ⟨1477851, by rfl⟩ : syracuseStep 3940937 = 2955703) B2955703
theorem B42036661 : Blo 1891435 42036661 := bstep (se 5 (by rfl) ⟨1970468, by rfl⟩ : syracuseStep 42036661 = 3940937) B3940937
theorem B56048881 : Blo 1891435 56048881 := bstep (se 2 (by rfl) ⟨21018330, by rfl⟩ : syracuseStep 56048881 = 42036661) B42036661
theorem B74731841 : Blo 1891435 74731841 := bstep (se 2 (by rfl) ⟨28024440, by rfl⟩ : syracuseStep 74731841 = 56048881) B56048881
theorem B49821227 : Blo 1891435 49821227 := bstep (se 1 (by rfl) ⟨37365920, by rfl⟩ : syracuseStep 49821227 = 74731841) B74731841
theorem B33214151 : Blo 1891435 33214151 := bstep (se 1 (by rfl) ⟨24910613, by rfl⟩ : syracuseStep 33214151 = 49821227) B49821227
theorem B22142767 : Blo 1891435 22142767 := bstep (se 1 (by rfl) ⟨16607075, by rfl⟩ : syracuseStep 22142767 = 33214151) B33214151
theorem B29523689 : Blo 1891435 29523689 := bstep (se 2 (by rfl) ⟨11071383, by rfl⟩ : syracuseStep 29523689 = 22142767) B22142767
theorem B19682459 : Blo 1891435 19682459 := bstep (se 1 (by rfl) ⟨14761844, by rfl⟩ : syracuseStep 19682459 = 29523689) B29523689
theorem B13121639 : Blo 1891435 13121639 := bstep (se 1 (by rfl) ⟨9841229, by rfl⟩ : syracuseStep 13121639 = 19682459) B19682459
theorem B8747759 : Blo 1891435 8747759 := bstep (se 1 (by rfl) ⟨6560819, by rfl⟩ : syracuseStep 8747759 = 13121639) B13121639
theorem B5831839 : Blo 1891435 5831839 := bstep (se 1 (by rfl) ⟨4373879, by rfl⟩ : syracuseStep 5831839 = 8747759) B8747759
theorem B7775785 : Blo 1891435 7775785 := bstep (se 2 (by rfl) ⟨2915919, by rfl⟩ : syracuseStep 7775785 = 5831839) B5831839
theorem B10367713 : Blo 1891435 10367713 := bstep (se 2 (by rfl) ⟨3887892, by rfl⟩ : syracuseStep 10367713 = 7775785) B7775785
theorem B13823617 : Blo 1891435 13823617 := bstep (se 2 (by rfl) ⟨5183856, by rfl⟩ : syracuseStep 13823617 = 10367713) B10367713
theorem B18431489 : Blo 1891435 18431489 := bstep (se 2 (by rfl) ⟨6911808, by rfl⟩ : syracuseStep 18431489 = 13823617) B13823617
theorem B12287659 : Blo 1891435 12287659 := bstep (se 1 (by rfl) ⟨9215744, by rfl⟩ : syracuseStep 12287659 = 18431489) B18431489
theorem B16383545 : Blo 1891435 16383545 := bstep (se 2 (by rfl) ⟨6143829, by rfl⟩ : syracuseStep 16383545 = 12287659) B12287659
theorem B10922363 : Blo 1891435 10922363 := bstep (se 1 (by rfl) ⟨8191772, by rfl⟩ : syracuseStep 10922363 = 16383545) B16383545
theorem B7281575 : Blo 1891435 7281575 := bstep (se 1 (by rfl) ⟨5461181, by rfl⟩ : syracuseStep 7281575 = 10922363) B10922363
theorem B4854383 : Blo 1891435 4854383 := bstep (se 1 (by rfl) ⟨3640787, by rfl⟩ : syracuseStep 4854383 = 7281575) B7281575
theorem B3236255 : Blo 1891435 3236255 := bstep (se 1 (by rfl) ⟨2427191, by rfl⟩ : syracuseStep 3236255 = 4854383) B4854383
theorem B34520053 : Blo 1891435 34520053 := bstep (se 5 (by rfl) ⟨1618127, by rfl⟩ : syracuseStep 34520053 = 3236255) B3236255
theorem B46026737 : Blo 1891435 46026737 := bstep (se 2 (by rfl) ⟨17260026, by rfl⟩ : syracuseStep 46026737 = 34520053) B34520053
theorem B30684491 : Blo 1891435 30684491 := bstep (se 1 (by rfl) ⟨23013368, by rfl⟩ : syracuseStep 30684491 = 46026737) B46026737
theorem B20456327 : Blo 1891435 20456327 := bstep (se 1 (by rfl) ⟨15342245, by rfl⟩ : syracuseStep 20456327 = 30684491) B30684491
theorem B54550205 : Blo 1891435 54550205 := bstep (se 3 (by rfl) ⟨10228163, by rfl⟩ : syracuseStep 54550205 = 20456327) B20456327
theorem B36366803 : Blo 1891435 36366803 := bstep (se 1 (by rfl) ⟨27275102, by rfl⟩ : syracuseStep 36366803 = 54550205) B54550205
theorem B24244535 : Blo 1891435 24244535 := bstep (se 1 (by rfl) ⟨18183401, by rfl⟩ : syracuseStep 24244535 = 36366803) B36366803
theorem B16163023 : Blo 1891435 16163023 := bstep (se 1 (by rfl) ⟨12122267, by rfl⟩ : syracuseStep 16163023 = 24244535) B24244535
theorem B21550697 : Blo 1891435 21550697 := bstep (se 2 (by rfl) ⟨8081511, by rfl⟩ : syracuseStep 21550697 = 16163023) B16163023
theorem B14367131 : Blo 1891435 14367131 := bstep (se 1 (by rfl) ⟨10775348, by rfl⟩ : syracuseStep 14367131 = 21550697) B21550697
theorem B9578087 : Blo 1891435 9578087 := bstep (se 1 (by rfl) ⟨7183565, by rfl⟩ : syracuseStep 9578087 = 14367131) B14367131
theorem B6385391 : Blo 1891435 6385391 := bstep (se 1 (by rfl) ⟨4789043, by rfl⟩ : syracuseStep 6385391 = 9578087) B9578087
theorem B4256927 : Blo 1891435 4256927 := bstep (se 1 (by rfl) ⟨3192695, by rfl⟩ : syracuseStep 4256927 = 6385391) B6385391
theorem B2837951 : Blo 1891435 2837951 := bstep (se 1 (by rfl) ⟨2128463, by rfl⟩ : syracuseStep 2837951 = 4256927) B4256927
theorem B1891967 : Blo 1891435 1891967 := bstep (se 1 (by rfl) ⟨1418975, by rfl⟩ : syracuseStep 1891967 = 2837951) B2837951
theorem B2837957 : Blo 1891435 2837957 := bbase (se 4 (by rfl) ⟨266058, by rfl⟩ : syracuseStep 2837957 = 532117) (by norm_num)
theorem B1891971 : Blo 1891435 1891971 := bstep (se 1 (by rfl) ⟨1418978, by rfl⟩ : syracuseStep 1891971 = 2837957) B2837957
theorem B3192709 : Blo 1891435 3192709 := bbase (se 4 (by rfl) ⟨299316, by rfl⟩ : syracuseStep 3192709 = 598633) (by norm_num)
theorem B4256945 : Blo 1891435 4256945 := bstep (se 2 (by rfl) ⟨1596354, by rfl⟩ : syracuseStep 4256945 = 3192709) B3192709
theorem B2837963 : Blo 1891435 2837963 := bstep (se 1 (by rfl) ⟨2128472, by rfl⟩ : syracuseStep 2837963 = 4256945) B4256945
theorem B1891975 : Blo 1891435 1891975 := bstep (se 1 (by rfl) ⟨1418981, by rfl⟩ : syracuseStep 1891975 = 2837963) B2837963
theorem B2128477 : Blo 1891435 2128477 := bbase (se 3 (by rfl) ⟨399089, by rfl⟩ : syracuseStep 2128477 = 798179) (by norm_num)
theorem B2837969 : Blo 1891435 2837969 := bstep (se 2 (by rfl) ⟨1064238, by rfl⟩ : syracuseStep 2837969 = 2128477) B2128477
theorem B1891979 : Blo 1891435 1891979 := bstep (se 1 (by rfl) ⟨1418984, by rfl⟩ : syracuseStep 1891979 = 2837969) B2837969
theorem B6385445 : Blo 1891435 6385445 := bbase (se 4 (by rfl) ⟨598635, by rfl⟩ : syracuseStep 6385445 = 1197271) (by norm_num)
theorem B4256963 : Blo 1891435 4256963 := bstep (se 1 (by rfl) ⟨3192722, by rfl⟩ : syracuseStep 4256963 = 6385445) B6385445
theorem B2837975 : Blo 1891435 2837975 := bstep (se 1 (by rfl) ⟨2128481, by rfl⟩ : syracuseStep 2837975 = 4256963) B4256963
theorem B1891983 : Blo 1891435 1891983 := bstep (se 1 (by rfl) ⟨1418987, by rfl⟩ : syracuseStep 1891983 = 2837975) B2837975
theorem B2837981 : Blo 1891435 2837981 := bbase (se 3 (by rfl) ⟨532121, by rfl⟩ : syracuseStep 2837981 = 1064243) (by norm_num)
theorem B1891987 : Blo 1891435 1891987 := bstep (se 1 (by rfl) ⟨1418990, by rfl⟩ : syracuseStep 1891987 = 2837981) B2837981
theorem B4256981 : Blo 1891435 4256981 := bbase (se 7 (by rfl) ⟨49886, by rfl⟩ : syracuseStep 4256981 = 99773) (by norm_num)
theorem B2837987 : Blo 1891435 2837987 := bstep (se 1 (by rfl) ⟨2128490, by rfl⟩ : syracuseStep 2837987 = 4256981) B4256981
theorem B1891991 : Blo 1891435 1891991 := bstep (se 1 (by rfl) ⟨1418993, by rfl⟩ : syracuseStep 1891991 = 2837987) B2837987
theorem B7281685 : Blo 1891435 7281685 := bbase (se 6 (by rfl) ⟨170664, by rfl⟩ : syracuseStep 7281685 = 341329) (by norm_num)
theorem B9708913 : Blo 1891435 9708913 := bstep (se 2 (by rfl) ⟨3640842, by rfl⟩ : syracuseStep 9708913 = 7281685) B7281685
theorem B51780869 : Blo 1891435 51780869 := bstep (se 4 (by rfl) ⟨4854456, by rfl⟩ : syracuseStep 51780869 = 9708913) B9708913
theorem B34520579 : Blo 1891435 34520579 := bstep (se 1 (by rfl) ⟨25890434, by rfl⟩ : syracuseStep 34520579 = 51780869) B51780869
theorem B23013719 : Blo 1891435 23013719 := bstep (se 1 (by rfl) ⟨17260289, by rfl⟩ : syracuseStep 23013719 = 34520579) B34520579
theorem B15342479 : Blo 1891435 15342479 := bstep (se 1 (by rfl) ⟨11506859, by rfl⟩ : syracuseStep 15342479 = 23013719) B23013719
theorem B10228319 : Blo 1891435 10228319 := bstep (se 1 (by rfl) ⟨7671239, by rfl⟩ : syracuseStep 10228319 = 15342479) B15342479
theorem B6818879 : Blo 1891435 6818879 := bstep (se 1 (by rfl) ⟨5114159, by rfl⟩ : syracuseStep 6818879 = 10228319) B10228319
theorem B4545919 : Blo 1891435 4545919 := bstep (se 1 (by rfl) ⟨3409439, by rfl⟩ : syracuseStep 4545919 = 6818879) B6818879
theorem B6061225 : Blo 1891435 6061225 := bstep (se 2 (by rfl) ⟨2272959, by rfl⟩ : syracuseStep 6061225 = 4545919) B4545919
theorem B8081633 : Blo 1891435 8081633 := bstep (se 2 (by rfl) ⟨3030612, by rfl⟩ : syracuseStep 8081633 = 6061225) B6061225
theorem B5387755 : Blo 1891435 5387755 := bstep (se 1 (by rfl) ⟨4040816, by rfl⟩ : syracuseStep 5387755 = 8081633) B8081633
theorem B7183673 : Blo 1891435 7183673 := bstep (se 2 (by rfl) ⟨2693877, by rfl⟩ : syracuseStep 7183673 = 5387755) B5387755
theorem B4789115 : Blo 1891435 4789115 := bstep (se 1 (by rfl) ⟨3591836, by rfl⟩ : syracuseStep 4789115 = 7183673) B7183673
theorem B3192743 : Blo 1891435 3192743 := bstep (se 1 (by rfl) ⟨2394557, by rfl⟩ : syracuseStep 3192743 = 4789115) B4789115
theorem B2128495 : Blo 1891435 2128495 := bstep (se 1 (by rfl) ⟨1596371, by rfl⟩ : syracuseStep 2128495 = 3192743) B3192743
theorem B2837993 : Blo 1891435 2837993 := bstep (se 2 (by rfl) ⟨1064247, by rfl⟩ : syracuseStep 2837993 = 2128495) B2128495
theorem B1891995 : Blo 1891435 1891995 := bstep (se 1 (by rfl) ⟨1418996, by rfl⟩ : syracuseStep 1891995 = 2837993) B2837993
theorem B30685013 : Blo 1891435 30685013 := bbase (se 9 (by rfl) ⟨89897, by rfl⟩ : syracuseStep 30685013 = 179795) (by norm_num)
theorem B20456675 : Blo 1891435 20456675 := bstep (se 1 (by rfl) ⟨15342506, by rfl⟩ : syracuseStep 20456675 = 30685013) B30685013
theorem B13637783 : Blo 1891435 13637783 := bstep (se 1 (by rfl) ⟨10228337, by rfl⟩ : syracuseStep 13637783 = 20456675) B20456675
theorem B9091855 : Blo 1891435 9091855 := bstep (se 1 (by rfl) ⟨6818891, by rfl⟩ : syracuseStep 9091855 = 13637783) B13637783
theorem B12122473 : Blo 1891435 12122473 := bstep (se 2 (by rfl) ⟨4545927, by rfl⟩ : syracuseStep 12122473 = 9091855) B9091855
theorem B16163297 : Blo 1891435 16163297 := bstep (se 2 (by rfl) ⟨6061236, by rfl⟩ : syracuseStep 16163297 = 12122473) B12122473
theorem B10775531 : Blo 1891435 10775531 := bstep (se 1 (by rfl) ⟨8081648, by rfl⟩ : syracuseStep 10775531 = 16163297) B16163297
theorem B7183687 : Blo 1891435 7183687 := bstep (se 1 (by rfl) ⟨5387765, by rfl⟩ : syracuseStep 7183687 = 10775531) B10775531
theorem B9578249 : Blo 1891435 9578249 := bstep (se 2 (by rfl) ⟨3591843, by rfl⟩ : syracuseStep 9578249 = 7183687) B7183687
theorem B6385499 : Blo 1891435 6385499 := bstep (se 1 (by rfl) ⟨4789124, by rfl⟩ : syracuseStep 6385499 = 9578249) B9578249
theorem B4256999 : Blo 1891435 4256999 := bstep (se 1 (by rfl) ⟨3192749, by rfl⟩ : syracuseStep 4256999 = 6385499) B6385499
theorem B2837999 : Blo 1891435 2837999 := bstep (se 1 (by rfl) ⟨2128499, by rfl⟩ : syracuseStep 2837999 = 4256999) B4256999
theorem B1891999 : Blo 1891435 1891999 := bstep (se 1 (by rfl) ⟨1418999, by rfl⟩ : syracuseStep 1891999 = 2837999) B2837999
theorem B2838005 : Blo 1891435 2838005 := bbase (se 5 (by rfl) ⟨133031, by rfl⟩ : syracuseStep 2838005 = 266063) (by norm_num)
theorem B1892003 : Blo 1891435 1892003 := bstep (se 1 (by rfl) ⟨1419002, by rfl⟩ : syracuseStep 1892003 = 2838005) B2838005
theorem B2020421 : Blo 1891435 2020421 := bbase (se 4 (by rfl) ⟨189414, by rfl⟩ : syracuseStep 2020421 = 378829) (by norm_num)
theorem B5387789 : Blo 1891435 5387789 := bstep (se 3 (by rfl) ⟨1010210, by rfl⟩ : syracuseStep 5387789 = 2020421) B2020421
theorem B3591859 : Blo 1891435 3591859 := bstep (se 1 (by rfl) ⟨2693894, by rfl⟩ : syracuseStep 3591859 = 5387789) B5387789
theorem B4789145 : Blo 1891435 4789145 := bstep (se 2 (by rfl) ⟨1795929, by rfl⟩ : syracuseStep 4789145 = 3591859) B3591859
theorem B3192763 : Blo 1891435 3192763 := bstep (se 1 (by rfl) ⟨2394572, by rfl⟩ : syracuseStep 3192763 = 4789145) B4789145
theorem B4257017 : Blo 1891435 4257017 := bstep (se 2 (by rfl) ⟨1596381, by rfl⟩ : syracuseStep 4257017 = 3192763) B3192763
theorem B2838011 : Blo 1891435 2838011 := bstep (se 1 (by rfl) ⟨2128508, by rfl⟩ : syracuseStep 2838011 = 4257017) B4257017
theorem B1892007 : Blo 1891435 1892007 := bstep (se 1 (by rfl) ⟨1419005, by rfl⟩ : syracuseStep 1892007 = 2838011) B2838011
theorem B2128513 : Blo 1891435 2128513 := bbase (se 2 (by rfl) ⟨798192, by rfl⟩ : syracuseStep 2128513 = 1596385) (by norm_num)
theorem B2838017 : Blo 1891435 2838017 := bstep (se 2 (by rfl) ⟨1064256, by rfl⟩ : syracuseStep 2838017 = 2128513) B2128513
theorem B1892011 : Blo 1891435 1892011 := bstep (se 1 (by rfl) ⟨1419008, by rfl⟩ : syracuseStep 1892011 = 2838017) B2838017
theorem B4789165 : Blo 1891435 4789165 := bbase (se 3 (by rfl) ⟨897968, by rfl⟩ : syracuseStep 4789165 = 1795937) (by norm_num)
theorem B6385553 : Blo 1891435 6385553 := bstep (se 2 (by rfl) ⟨2394582, by rfl⟩ : syracuseStep 6385553 = 4789165) B4789165
theorem B4257035 : Blo 1891435 4257035 := bstep (se 1 (by rfl) ⟨3192776, by rfl⟩ : syracuseStep 4257035 = 6385553) B6385553
theorem B2838023 : Blo 1891435 2838023 := bstep (se 1 (by rfl) ⟨2128517, by rfl⟩ : syracuseStep 2838023 = 4257035) B4257035
theorem B1892015 : Blo 1891435 1892015 := bstep (se 1 (by rfl) ⟨1419011, by rfl⟩ : syracuseStep 1892015 = 2838023) B2838023
theorem B2838029 : Blo 1891435 2838029 := bbase (se 3 (by rfl) ⟨532130, by rfl⟩ : syracuseStep 2838029 = 1064261) (by norm_num)
theorem B1892019 : Blo 1891435 1892019 := bstep (se 1 (by rfl) ⟨1419014, by rfl⟩ : syracuseStep 1892019 = 2838029) B2838029
theorem B4257053 : Blo 1891435 4257053 := bbase (se 3 (by rfl) ⟨798197, by rfl⟩ : syracuseStep 4257053 = 1596395) (by norm_num)
theorem B2838035 : Blo 1891435 2838035 := bstep (se 1 (by rfl) ⟨2128526, by rfl⟩ : syracuseStep 2838035 = 4257053) B4257053
theorem B1892023 : Blo 1891435 1892023 := bstep (se 1 (by rfl) ⟨1419017, by rfl⟩ : syracuseStep 1892023 = 2838035) B2838035
theorem B3192797 : Blo 1891435 3192797 := bbase (se 3 (by rfl) ⟨598649, by rfl⟩ : syracuseStep 3192797 = 1197299) (by norm_num)
theorem B2128531 : Blo 1891435 2128531 := bstep (se 1 (by rfl) ⟨1596398, by rfl⟩ : syracuseStep 2128531 = 3192797) B3192797
theorem B2838041 : Blo 1891435 2838041 := bstep (se 2 (by rfl) ⟨1064265, by rfl⟩ : syracuseStep 2838041 = 2128531) B2128531
theorem B1892027 : Blo 1891435 1892027 := bstep (se 1 (by rfl) ⟨1419020, by rfl⟩ : syracuseStep 1892027 = 2838041) B2838041
theorem B24576149 : Blo 1891435 24576149 := bbase (se 6 (by rfl) ⟨576003, by rfl⟩ : syracuseStep 24576149 = 1152007) (by norm_num)
theorem B16384099 : Blo 1891435 16384099 := bstep (se 1 (by rfl) ⟨12288074, by rfl⟩ : syracuseStep 16384099 = 24576149) B24576149
theorem B21845465 : Blo 1891435 21845465 := bstep (se 2 (by rfl) ⟨8192049, by rfl⟩ : syracuseStep 21845465 = 16384099) B16384099
theorem B14563643 : Blo 1891435 14563643 := bstep (se 1 (by rfl) ⟨10922732, by rfl⟩ : syracuseStep 14563643 = 21845465) B21845465
theorem B38836381 : Blo 1891435 38836381 := bstep (se 3 (by rfl) ⟨7281821, by rfl⟩ : syracuseStep 38836381 = 14563643) B14563643
theorem B51781841 : Blo 1891435 51781841 := bstep (se 2 (by rfl) ⟨19418190, by rfl⟩ : syracuseStep 51781841 = 38836381) B38836381
theorem B34521227 : Blo 1891435 34521227 := bstep (se 1 (by rfl) ⟨25890920, by rfl⟩ : syracuseStep 34521227 = 51781841) B51781841
theorem B23014151 : Blo 1891435 23014151 := bstep (se 1 (by rfl) ⟨17260613, by rfl⟩ : syracuseStep 23014151 = 34521227) B34521227
theorem B15342767 : Blo 1891435 15342767 := bstep (se 1 (by rfl) ⟨11507075, by rfl⟩ : syracuseStep 15342767 = 23014151) B23014151
theorem B10228511 : Blo 1891435 10228511 := bstep (se 1 (by rfl) ⟨7671383, by rfl⟩ : syracuseStep 10228511 = 15342767) B15342767
theorem B6819007 : Blo 1891435 6819007 := bstep (se 1 (by rfl) ⟨5114255, by rfl⟩ : syracuseStep 6819007 = 10228511) B10228511
theorem B9092009 : Blo 1891435 9092009 := bstep (se 2 (by rfl) ⟨3409503, by rfl⟩ : syracuseStep 9092009 = 6819007) B6819007
theorem B6061339 : Blo 1891435 6061339 := bstep (se 1 (by rfl) ⟨4546004, by rfl⟩ : syracuseStep 6061339 = 9092009) B9092009
theorem B8081785 : Blo 1891435 8081785 := bstep (se 2 (by rfl) ⟨3030669, by rfl⟩ : syracuseStep 8081785 = 6061339) B6061339
theorem B10775713 : Blo 1891435 10775713 := bstep (se 2 (by rfl) ⟨4040892, by rfl⟩ : syracuseStep 10775713 = 8081785) B8081785
theorem B14367617 : Blo 1891435 14367617 := bstep (se 2 (by rfl) ⟨5387856, by rfl⟩ : syracuseStep 14367617 = 10775713) B10775713
theorem B9578411 : Blo 1891435 9578411 := bstep (se 1 (by rfl) ⟨7183808, by rfl⟩ : syracuseStep 9578411 = 14367617) B14367617
theorem B6385607 : Blo 1891435 6385607 := bstep (se 1 (by rfl) ⟨4789205, by rfl⟩ : syracuseStep 6385607 = 9578411) B9578411
theorem B4257071 : Blo 1891435 4257071 := bstep (se 1 (by rfl) ⟨3192803, by rfl⟩ : syracuseStep 4257071 = 6385607) B6385607
theorem B2838047 : Blo 1891435 2838047 := bstep (se 1 (by rfl) ⟨2128535, by rfl⟩ : syracuseStep 2838047 = 4257071) B4257071
theorem B1892031 : Blo 1891435 1892031 := bstep (se 1 (by rfl) ⟨1419023, by rfl⟩ : syracuseStep 1892031 = 2838047) B2838047
theorem B2838053 : Blo 1891435 2838053 := bbase (se 4 (by rfl) ⟨266067, by rfl⟩ : syracuseStep 2838053 = 532135) (by norm_num)
theorem B1892035 : Blo 1891435 1892035 := bstep (se 1 (by rfl) ⟨1419026, by rfl⟩ : syracuseStep 1892035 = 2838053) B2838053
theorem B2394613 : Blo 1891435 2394613 := bbase (se 5 (by rfl) ⟨112247, by rfl⟩ : syracuseStep 2394613 = 224495) (by norm_num)
theorem B3192817 : Blo 1891435 3192817 := bstep (se 2 (by rfl) ⟨1197306, by rfl⟩ : syracuseStep 3192817 = 2394613) B2394613
theorem B4257089 : Blo 1891435 4257089 := bstep (se 2 (by rfl) ⟨1596408, by rfl⟩ : syracuseStep 4257089 = 3192817) B3192817
theorem B2838059 : Blo 1891435 2838059 := bstep (se 1 (by rfl) ⟨2128544, by rfl⟩ : syracuseStep 2838059 = 4257089) B4257089
theorem B1892039 : Blo 1891435 1892039 := bstep (se 1 (by rfl) ⟨1419029, by rfl⟩ : syracuseStep 1892039 = 2838059) B2838059
theorem B2128549 : Blo 1891435 2128549 := bbase (se 4 (by rfl) ⟨199551, by rfl⟩ : syracuseStep 2128549 = 399103) (by norm_num)
theorem B2838065 : Blo 1891435 2838065 := bstep (se 2 (by rfl) ⟨1064274, by rfl⟩ : syracuseStep 2838065 = 2128549) B2128549
theorem B1892043 : Blo 1891435 1892043 := bstep (se 1 (by rfl) ⟨1419032, by rfl⟩ : syracuseStep 1892043 = 2838065) B2838065
theorem B4854589 : Blo 1891435 4854589 := bbase (se 3 (by rfl) ⟨910235, by rfl⟩ : syracuseStep 4854589 = 1820471) (by norm_num)
theorem B103564565 : Blo 1891435 103564565 := bstep (se 6 (by rfl) ⟨2427294, by rfl⟩ : syracuseStep 103564565 = 4854589) B4854589
theorem B69043043 : Blo 1891435 69043043 := bstep (se 1 (by rfl) ⟨51782282, by rfl⟩ : syracuseStep 69043043 = 103564565) B103564565
theorem B46028695 : Blo 1891435 46028695 := bstep (se 1 (by rfl) ⟨34521521, by rfl⟩ : syracuseStep 46028695 = 69043043) B69043043
theorem B61371593 : Blo 1891435 61371593 := bstep (se 2 (by rfl) ⟨23014347, by rfl⟩ : syracuseStep 61371593 = 46028695) B46028695
theorem B40914395 : Blo 1891435 40914395 := bstep (se 1 (by rfl) ⟨30685796, by rfl⟩ : syracuseStep 40914395 = 61371593) B61371593
theorem B27276263 : Blo 1891435 27276263 := bstep (se 1 (by rfl) ⟨20457197, by rfl⟩ : syracuseStep 27276263 = 40914395) B40914395
theorem B18184175 : Blo 1891435 18184175 := bstep (se 1 (by rfl) ⟨13638131, by rfl⟩ : syracuseStep 18184175 = 27276263) B27276263
theorem B12122783 : Blo 1891435 12122783 := bstep (se 1 (by rfl) ⟨9092087, by rfl⟩ : syracuseStep 12122783 = 18184175) B18184175
theorem B8081855 : Blo 1891435 8081855 := bstep (se 1 (by rfl) ⟨6061391, by rfl⟩ : syracuseStep 8081855 = 12122783) B12122783
theorem B5387903 : Blo 1891435 5387903 := bstep (se 1 (by rfl) ⟨4040927, by rfl⟩ : syracuseStep 5387903 = 8081855) B8081855
theorem B3591935 : Blo 1891435 3591935 := bstep (se 1 (by rfl) ⟨2693951, by rfl⟩ : syracuseStep 3591935 = 5387903) B5387903
theorem B2394623 : Blo 1891435 2394623 := bstep (se 1 (by rfl) ⟨1795967, by rfl⟩ : syracuseStep 2394623 = 3591935) B3591935
theorem B6385661 : Blo 1891435 6385661 := bstep (se 3 (by rfl) ⟨1197311, by rfl⟩ : syracuseStep 6385661 = 2394623) B2394623
theorem B4257107 : Blo 1891435 4257107 := bstep (se 1 (by rfl) ⟨3192830, by rfl⟩ : syracuseStep 4257107 = 6385661) B6385661
theorem B2838071 : Blo 1891435 2838071 := bstep (se 1 (by rfl) ⟨2128553, by rfl⟩ : syracuseStep 2838071 = 4257107) B4257107
theorem B1892047 : Blo 1891435 1892047 := bstep (se 1 (by rfl) ⟨1419035, by rfl⟩ : syracuseStep 1892047 = 2838071) B2838071
theorem B2838077 : Blo 1891435 2838077 := bbase (se 3 (by rfl) ⟨532139, by rfl⟩ : syracuseStep 2838077 = 1064279) (by norm_num)
theorem B1892051 : Blo 1891435 1892051 := bstep (se 1 (by rfl) ⟨1419038, by rfl⟩ : syracuseStep 1892051 = 2838077) B2838077
theorem B4257125 : Blo 1891435 4257125 := bbase (se 4 (by rfl) ⟨399105, by rfl⟩ : syracuseStep 4257125 = 798211) (by norm_num)
theorem B2838083 : Blo 1891435 2838083 := bstep (se 1 (by rfl) ⟨2128562, by rfl⟩ : syracuseStep 2838083 = 4257125) B4257125
theorem B1892055 : Blo 1891435 1892055 := bstep (se 1 (by rfl) ⟨1419041, by rfl⟩ : syracuseStep 1892055 = 2838083) B2838083
theorem B4789277 : Blo 1891435 4789277 := bbase (se 3 (by rfl) ⟨897989, by rfl⟩ : syracuseStep 4789277 = 1795979) (by norm_num)
theorem B3192851 : Blo 1891435 3192851 := bstep (se 1 (by rfl) ⟨2394638, by rfl⟩ : syracuseStep 3192851 = 4789277) B4789277
theorem B2128567 : Blo 1891435 2128567 := bstep (se 1 (by rfl) ⟨1596425, by rfl⟩ : syracuseStep 2128567 = 3192851) B3192851
theorem B2838089 : Blo 1891435 2838089 := bstep (se 2 (by rfl) ⟨1064283, by rfl⟩ : syracuseStep 2838089 = 2128567) B2128567
theorem B1892059 : Blo 1891435 1892059 := bstep (se 1 (by rfl) ⟨1419044, by rfl⟩ : syracuseStep 1892059 = 2838089) B2838089
theorem B3591965 : Blo 1891435 3591965 := bbase (se 3 (by rfl) ⟨673493, by rfl⟩ : syracuseStep 3591965 = 1346987) (by norm_num)
theorem B9578573 : Blo 1891435 9578573 := bstep (se 3 (by rfl) ⟨1795982, by rfl⟩ : syracuseStep 9578573 = 3591965) B3591965
theorem B6385715 : Blo 1891435 6385715 := bstep (se 1 (by rfl) ⟨4789286, by rfl⟩ : syracuseStep 6385715 = 9578573) B9578573
theorem B4257143 : Blo 1891435 4257143 := bstep (se 1 (by rfl) ⟨3192857, by rfl⟩ : syracuseStep 4257143 = 6385715) B6385715
theorem B2838095 : Blo 1891435 2838095 := bstep (se 1 (by rfl) ⟨2128571, by rfl⟩ : syracuseStep 2838095 = 4257143) B4257143
theorem B1892063 : Blo 1891435 1892063 := bstep (se 1 (by rfl) ⟨1419047, by rfl⟩ : syracuseStep 1892063 = 2838095) B2838095
theorem B2838101 : Blo 1891435 2838101 := bbase (se 8 (by rfl) ⟨16629, by rfl⟩ : syracuseStep 2838101 = 33259) (by norm_num)
theorem B1892067 : Blo 1891435 1892067 := bstep (se 1 (by rfl) ⟨1419050, by rfl⟩ : syracuseStep 1892067 = 2838101) B2838101
theorem B8081957 : Blo 1891435 8081957 := bbase (se 4 (by rfl) ⟨757683, by rfl⟩ : syracuseStep 8081957 = 1515367) (by norm_num)
theorem B5387971 : Blo 1891435 5387971 := bstep (se 1 (by rfl) ⟨4040978, by rfl⟩ : syracuseStep 5387971 = 8081957) B8081957
theorem B7183961 : Blo 1891435 7183961 := bstep (se 2 (by rfl) ⟨2693985, by rfl⟩ : syracuseStep 7183961 = 5387971) B5387971
theorem B4789307 : Blo 1891435 4789307 := bstep (se 1 (by rfl) ⟨3591980, by rfl⟩ : syracuseStep 4789307 = 7183961) B7183961
theorem B3192871 : Blo 1891435 3192871 := bstep (se 1 (by rfl) ⟨2394653, by rfl⟩ : syracuseStep 3192871 = 4789307) B4789307
theorem B4257161 : Blo 1891435 4257161 := bstep (se 2 (by rfl) ⟨1596435, by rfl⟩ : syracuseStep 4257161 = 3192871) B3192871
theorem B2838107 : Blo 1891435 2838107 := bstep (se 1 (by rfl) ⟨2128580, by rfl⟩ : syracuseStep 2838107 = 4257161) B4257161
theorem B1892071 : Blo 1891435 1892071 := bstep (se 1 (by rfl) ⟨1419053, by rfl⟩ : syracuseStep 1892071 = 2838107) B2838107
theorem B2128585 : Blo 1891435 2128585 := bbase (se 2 (by rfl) ⟨798219, by rfl⟩ : syracuseStep 2128585 = 1596439) (by norm_num)
theorem B2838113 : Blo 1891435 2838113 := bstep (se 2 (by rfl) ⟨1064292, by rfl⟩ : syracuseStep 2838113 = 2128585) B2128585
theorem B1892075 : Blo 1891435 1892075 := bstep (se 1 (by rfl) ⟨1419056, by rfl⟩ : syracuseStep 1892075 = 2838113) B2838113
theorem B6061493 : Blo 1891435 6061493 := bbase (se 5 (by rfl) ⟨284132, by rfl⟩ : syracuseStep 6061493 = 568265) (by norm_num)
theorem B16163981 : Blo 1891435 16163981 := bstep (se 3 (by rfl) ⟨3030746, by rfl⟩ : syracuseStep 16163981 = 6061493) B6061493
theorem B10775987 : Blo 1891435 10775987 := bstep (se 1 (by rfl) ⟨8081990, by rfl⟩ : syracuseStep 10775987 = 16163981) B16163981
theorem B7183991 : Blo 1891435 7183991 := bstep (se 1 (by rfl) ⟨5387993, by rfl⟩ : syracuseStep 7183991 = 10775987) B10775987
theorem B4789327 : Blo 1891435 4789327 := bstep (se 1 (by rfl) ⟨3591995, by rfl⟩ : syracuseStep 4789327 = 7183991) B7183991
theorem B6385769 : Blo 1891435 6385769 := bstep (se 2 (by rfl) ⟨2394663, by rfl⟩ : syracuseStep 6385769 = 4789327) B4789327
theorem B4257179 : Blo 1891435 4257179 := bstep (se 1 (by rfl) ⟨3192884, by rfl⟩ : syracuseStep 4257179 = 6385769) B6385769
theorem B2838119 : Blo 1891435 2838119 := bstep (se 1 (by rfl) ⟨2128589, by rfl⟩ : syracuseStep 2838119 = 4257179) B4257179
theorem B1892079 : Blo 1891435 1892079 := bstep (se 1 (by rfl) ⟨1419059, by rfl⟩ : syracuseStep 1892079 = 2838119) B2838119
theorem B2838125 : Blo 1891435 2838125 := bbase (se 3 (by rfl) ⟨532148, by rfl⟩ : syracuseStep 2838125 = 1064297) (by norm_num)
theorem B1892083 : Blo 1891435 1892083 := bstep (se 1 (by rfl) ⟨1419062, by rfl⟩ : syracuseStep 1892083 = 2838125) B2838125
theorem B4257197 : Blo 1891435 4257197 := bbase (se 3 (by rfl) ⟨798224, by rfl⟩ : syracuseStep 4257197 = 1596449) (by norm_num)
theorem B2838131 : Blo 1891435 2838131 := bstep (se 1 (by rfl) ⟨2128598, by rfl⟩ : syracuseStep 2838131 = 4257197) B4257197
theorem B1892087 : Blo 1891435 1892087 := bstep (se 1 (by rfl) ⟨1419065, by rfl⟩ : syracuseStep 1892087 = 2838131) B2838131
theorem B13824533 : Blo 1891435 13824533 := bbase (se 6 (by rfl) ⟨324012, by rfl⟩ : syracuseStep 13824533 = 648025) (by norm_num)
theorem B9216355 : Blo 1891435 9216355 := bstep (se 1 (by rfl) ⟨6912266, by rfl⟩ : syracuseStep 9216355 = 13824533) B13824533
theorem B12288473 : Blo 1891435 12288473 := bstep (se 2 (by rfl) ⟨4608177, by rfl⟩ : syracuseStep 12288473 = 9216355) B9216355
theorem B8192315 : Blo 1891435 8192315 := bstep (se 1 (by rfl) ⟨6144236, by rfl⟩ : syracuseStep 8192315 = 12288473) B12288473
theorem B5461543 : Blo 1891435 5461543 := bstep (se 1 (by rfl) ⟨4096157, by rfl⟩ : syracuseStep 5461543 = 8192315) B8192315
theorem B7282057 : Blo 1891435 7282057 := bstep (se 2 (by rfl) ⟨2730771, by rfl⟩ : syracuseStep 7282057 = 5461543) B5461543
theorem B9709409 : Blo 1891435 9709409 := bstep (se 2 (by rfl) ⟨3641028, by rfl⟩ : syracuseStep 9709409 = 7282057) B7282057
theorem B25891757 : Blo 1891435 25891757 := bstep (se 3 (by rfl) ⟨4854704, by rfl⟩ : syracuseStep 25891757 = 9709409) B9709409
theorem B17261171 : Blo 1891435 17261171 := bstep (se 1 (by rfl) ⟨12945878, by rfl⟩ : syracuseStep 17261171 = 25891757) B25891757
theorem B11507447 : Blo 1891435 11507447 := bstep (se 1 (by rfl) ⟨8630585, by rfl⟩ : syracuseStep 11507447 = 17261171) B17261171
theorem B7671631 : Blo 1891435 7671631 := bstep (se 1 (by rfl) ⟨5753723, by rfl⟩ : syracuseStep 7671631 = 11507447) B11507447
theorem B10228841 : Blo 1891435 10228841 := bstep (se 2 (by rfl) ⟨3835815, by rfl⟩ : syracuseStep 10228841 = 7671631) B7671631
theorem B6819227 : Blo 1891435 6819227 := bstep (se 1 (by rfl) ⟨5114420, by rfl⟩ : syracuseStep 6819227 = 10228841) B10228841
theorem B4546151 : Blo 1891435 4546151 := bstep (se 1 (by rfl) ⟨3409613, by rfl⟩ : syracuseStep 4546151 = 6819227) B6819227
theorem B3030767 : Blo 1891435 3030767 := bstep (se 1 (by rfl) ⟨2273075, by rfl⟩ : syracuseStep 3030767 = 4546151) B4546151
theorem B2020511 : Blo 1891435 2020511 := bstep (se 1 (by rfl) ⟨1515383, by rfl⟩ : syracuseStep 2020511 = 3030767) B3030767
theorem B5388029 : Blo 1891435 5388029 := bstep (se 3 (by rfl) ⟨1010255, by rfl⟩ : syracuseStep 5388029 = 2020511) B2020511
theorem B3592019 : Blo 1891435 3592019 := bstep (se 1 (by rfl) ⟨2694014, by rfl⟩ : syracuseStep 3592019 = 5388029) B5388029
theorem B2394679 : Blo 1891435 2394679 := bstep (se 1 (by rfl) ⟨1796009, by rfl⟩ : syracuseStep 2394679 = 3592019) B3592019
theorem B3192905 : Blo 1891435 3192905 := bstep (se 2 (by rfl) ⟨1197339, by rfl⟩ : syracuseStep 3192905 = 2394679) B2394679
theorem B2128603 : Blo 1891435 2128603 := bstep (se 1 (by rfl) ⟨1596452, by rfl⟩ : syracuseStep 2128603 = 3192905) B3192905
theorem B2838137 : Blo 1891435 2838137 := bstep (se 2 (by rfl) ⟨1064301, by rfl⟩ : syracuseStep 2838137 = 2128603) B2128603
theorem B1892091 : Blo 1891435 1892091 := bstep (se 1 (by rfl) ⟨1419068, by rfl⟩ : syracuseStep 1892091 = 2838137) B2838137
theorem B14762837 : Blo 1891435 14762837 := bbase (se 9 (by rfl) ⟨43250, by rfl⟩ : syracuseStep 14762837 = 86501) (by norm_num)
theorem B39367565 : Blo 1891435 39367565 := bstep (se 3 (by rfl) ⟨7381418, by rfl⟩ : syracuseStep 39367565 = 14762837) B14762837
theorem B26245043 : Blo 1891435 26245043 := bstep (se 1 (by rfl) ⟨19683782, by rfl⟩ : syracuseStep 26245043 = 39367565) B39367565
theorem B17496695 : Blo 1891435 17496695 := bstep (se 1 (by rfl) ⟨13122521, by rfl⟩ : syracuseStep 17496695 = 26245043) B26245043
theorem B46657853 : Blo 1891435 46657853 := bstep (se 3 (by rfl) ⟨8748347, by rfl⟩ : syracuseStep 46657853 = 17496695) B17496695
theorem B31105235 : Blo 1891435 31105235 := bstep (se 1 (by rfl) ⟨23328926, by rfl⟩ : syracuseStep 31105235 = 46657853) B46657853
theorem B20736823 : Blo 1891435 20736823 := bstep (se 1 (by rfl) ⟨15552617, by rfl⟩ : syracuseStep 20736823 = 31105235) B31105235
theorem B27649097 : Blo 1891435 27649097 := bstep (se 2 (by rfl) ⟨10368411, by rfl⟩ : syracuseStep 27649097 = 20736823) B20736823
theorem B18432731 : Blo 1891435 18432731 := bstep (se 1 (by rfl) ⟨13824548, by rfl⟩ : syracuseStep 18432731 = 27649097) B27649097
theorem B49153949 : Blo 1891435 49153949 := bstep (se 3 (by rfl) ⟨9216365, by rfl⟩ : syracuseStep 49153949 = 18432731) B18432731
theorem B32769299 : Blo 1891435 32769299 := bstep (se 1 (by rfl) ⟨24576974, by rfl⟩ : syracuseStep 32769299 = 49153949) B49153949
theorem B21846199 : Blo 1891435 21846199 := bstep (se 1 (by rfl) ⟨16384649, by rfl⟩ : syracuseStep 21846199 = 32769299) B32769299
theorem B29128265 : Blo 1891435 29128265 := bstep (se 2 (by rfl) ⟨10923099, by rfl⟩ : syracuseStep 29128265 = 21846199) B21846199
theorem B19418843 : Blo 1891435 19418843 := bstep (se 1 (by rfl) ⟨14564132, by rfl⟩ : syracuseStep 19418843 = 29128265) B29128265
theorem B51783581 : Blo 1891435 51783581 := bstep (se 3 (by rfl) ⟨9709421, by rfl⟩ : syracuseStep 51783581 = 19418843) B19418843
theorem B138089549 : Blo 1891435 138089549 := bstep (se 3 (by rfl) ⟨25891790, by rfl⟩ : syracuseStep 138089549 = 51783581) B51783581
theorem B92059699 : Blo 1891435 92059699 := bstep (se 1 (by rfl) ⟨69044774, by rfl⟩ : syracuseStep 92059699 = 138089549) B138089549
theorem B122746265 : Blo 1891435 122746265 := bstep (se 2 (by rfl) ⟨46029849, by rfl⟩ : syracuseStep 122746265 = 92059699) B92059699
theorem B81830843 : Blo 1891435 81830843 := bstep (se 1 (by rfl) ⟨61373132, by rfl⟩ : syracuseStep 81830843 = 122746265) B122746265
theorem B54553895 : Blo 1891435 54553895 := bstep (se 1 (by rfl) ⟨40915421, by rfl⟩ : syracuseStep 54553895 = 81830843) B81830843
theorem B36369263 : Blo 1891435 36369263 := bstep (se 1 (by rfl) ⟨27276947, by rfl⟩ : syracuseStep 36369263 = 54553895) B54553895
theorem B24246175 : Blo 1891435 24246175 := bstep (se 1 (by rfl) ⟨18184631, by rfl⟩ : syracuseStep 24246175 = 36369263) B36369263
theorem B32328233 : Blo 1891435 32328233 := bstep (se 2 (by rfl) ⟨12123087, by rfl⟩ : syracuseStep 32328233 = 24246175) B24246175
theorem B21552155 : Blo 1891435 21552155 := bstep (se 1 (by rfl) ⟨16164116, by rfl⟩ : syracuseStep 21552155 = 32328233) B32328233
theorem B14368103 : Blo 1891435 14368103 := bstep (se 1 (by rfl) ⟨10776077, by rfl⟩ : syracuseStep 14368103 = 21552155) B21552155
theorem B9578735 : Blo 1891435 9578735 := bstep (se 1 (by rfl) ⟨7184051, by rfl⟩ : syracuseStep 9578735 = 14368103) B14368103
theorem B6385823 : Blo 1891435 6385823 := bstep (se 1 (by rfl) ⟨4789367, by rfl⟩ : syracuseStep 6385823 = 9578735) B9578735
theorem B4257215 : Blo 1891435 4257215 := bstep (se 1 (by rfl) ⟨3192911, by rfl⟩ : syracuseStep 4257215 = 6385823) B6385823
theorem B2838143 : Blo 1891435 2838143 := bstep (se 1 (by rfl) ⟨2128607, by rfl⟩ : syracuseStep 2838143 = 4257215) B4257215
theorem B1892095 : Blo 1891435 1892095 := bstep (se 1 (by rfl) ⟨1419071, by rfl⟩ : syracuseStep 1892095 = 2838143) B2838143
theorem B2838149 : Blo 1891435 2838149 := bbase (se 4 (by rfl) ⟨266076, by rfl⟩ : syracuseStep 2838149 = 532153) (by norm_num)
theorem B1892099 : Blo 1891435 1892099 := bstep (se 1 (by rfl) ⟨1419074, by rfl⟩ : syracuseStep 1892099 = 2838149) B2838149
theorem B3192925 : Blo 1891435 3192925 := bbase (se 3 (by rfl) ⟨598673, by rfl⟩ : syracuseStep 3192925 = 1197347) (by norm_num)
theorem B4257233 : Blo 1891435 4257233 := bstep (se 2 (by rfl) ⟨1596462, by rfl⟩ : syracuseStep 4257233 = 3192925) B3192925
theorem B2838155 : Blo 1891435 2838155 := bstep (se 1 (by rfl) ⟨2128616, by rfl⟩ : syracuseStep 2838155 = 4257233) B4257233
theorem B1892103 : Blo 1891435 1892103 := bstep (se 1 (by rfl) ⟨1419077, by rfl⟩ : syracuseStep 1892103 = 2838155) B2838155
theorem B2128621 : Blo 1891435 2128621 := bbase (se 3 (by rfl) ⟨399116, by rfl⟩ : syracuseStep 2128621 = 798233) (by norm_num)
theorem B2838161 : Blo 1891435 2838161 := bstep (se 2 (by rfl) ⟨1064310, by rfl⟩ : syracuseStep 2838161 = 2128621) B2128621
theorem B1892107 : Blo 1891435 1892107 := bstep (se 1 (by rfl) ⟨1419080, by rfl⟩ : syracuseStep 1892107 = 2838161) B2838161
theorem B6385877 : Blo 1891435 6385877 := bbase (se 7 (by rfl) ⟨74834, by rfl⟩ : syracuseStep 6385877 = 149669) (by norm_num)
theorem B4257251 : Blo 1891435 4257251 := bstep (se 1 (by rfl) ⟨3192938, by rfl⟩ : syracuseStep 4257251 = 6385877) B6385877
theorem B2838167 : Blo 1891435 2838167 := bstep (se 1 (by rfl) ⟨2128625, by rfl⟩ : syracuseStep 2838167 = 4257251) B4257251
theorem B1892111 : Blo 1891435 1892111 := bstep (se 1 (by rfl) ⟨1419083, by rfl⟩ : syracuseStep 1892111 = 2838167) B2838167
theorem B2838173 : Blo 1891435 2838173 := bbase (se 3 (by rfl) ⟨532157, by rfl⟩ : syracuseStep 2838173 = 1064315) (by norm_num)
theorem B1892115 : Blo 1891435 1892115 := bstep (se 1 (by rfl) ⟨1419086, by rfl⟩ : syracuseStep 1892115 = 2838173) B2838173
theorem B4257269 : Blo 1891435 4257269 := bbase (se 5 (by rfl) ⟨199559, by rfl⟩ : syracuseStep 4257269 = 399119) (by norm_num)
theorem B2838179 : Blo 1891435 2838179 := bstep (se 1 (by rfl) ⟨2128634, by rfl⟩ : syracuseStep 2838179 = 4257269) B4257269
theorem B1892119 : Blo 1891435 1892119 := bstep (se 1 (by rfl) ⟨1419089, by rfl⟩ : syracuseStep 1892119 = 2838179) B2838179
theorem B2876909 : Blo 1891435 2876909 := bbase (se 3 (by rfl) ⟨539420, by rfl⟩ : syracuseStep 2876909 = 1078841) (by norm_num)
theorem B7671757 : Blo 1891435 7671757 := bstep (se 3 (by rfl) ⟨1438454, by rfl⟩ : syracuseStep 7671757 = 2876909) B2876909
theorem B10229009 : Blo 1891435 10229009 := bstep (se 2 (by rfl) ⟨3835878, by rfl⟩ : syracuseStep 10229009 = 7671757) B7671757
theorem B27277357 : Blo 1891435 27277357 := bstep (se 3 (by rfl) ⟨5114504, by rfl⟩ : syracuseStep 27277357 = 10229009) B10229009
theorem B36369809 : Blo 1891435 36369809 := bstep (se 2 (by rfl) ⟨13638678, by rfl⟩ : syracuseStep 36369809 = 27277357) B27277357
theorem B24246539 : Blo 1891435 24246539 := bstep (se 1 (by rfl) ⟨18184904, by rfl⟩ : syracuseStep 24246539 = 36369809) B36369809
theorem B16164359 : Blo 1891435 16164359 := bstep (se 1 (by rfl) ⟨12123269, by rfl⟩ : syracuseStep 16164359 = 24246539) B24246539
theorem B10776239 : Blo 1891435 10776239 := bstep (se 1 (by rfl) ⟨8082179, by rfl⟩ : syracuseStep 10776239 = 16164359) B16164359
theorem B7184159 : Blo 1891435 7184159 := bstep (se 1 (by rfl) ⟨5388119, by rfl⟩ : syracuseStep 7184159 = 10776239) B10776239
theorem B4789439 : Blo 1891435 4789439 := bstep (se 1 (by rfl) ⟨3592079, by rfl⟩ : syracuseStep 4789439 = 7184159) B7184159
theorem B3192959 : Blo 1891435 3192959 := bstep (se 1 (by rfl) ⟨2394719, by rfl⟩ : syracuseStep 3192959 = 4789439) B4789439
theorem B2128639 : Blo 1891435 2128639 := bstep (se 1 (by rfl) ⟨1596479, by rfl⟩ : syracuseStep 2128639 = 3192959) B3192959
theorem B2838185 : Blo 1891435 2838185 := bstep (se 2 (by rfl) ⟨1064319, by rfl⟩ : syracuseStep 2838185 = 2128639) B2128639
theorem B1892123 : Blo 1891435 1892123 := bstep (se 1 (by rfl) ⟨1419092, by rfl⟩ : syracuseStep 1892123 = 2838185) B2838185
theorem B2020549 : Blo 1891435 2020549 := bbase (se 4 (by rfl) ⟨189426, by rfl⟩ : syracuseStep 2020549 = 378853) (by norm_num)
theorem B2694065 : Blo 1891435 2694065 := bstep (se 2 (by rfl) ⟨1010274, by rfl⟩ : syracuseStep 2694065 = 2020549) B2020549
theorem B7184173 : Blo 1891435 7184173 := bstep (se 3 (by rfl) ⟨1347032, by rfl⟩ : syracuseStep 7184173 = 2694065) B2694065
theorem B9578897 : Blo 1891435 9578897 := bstep (se 2 (by rfl) ⟨3592086, by rfl⟩ : syracuseStep 9578897 = 7184173) B7184173
theorem B6385931 : Blo 1891435 6385931 := bstep (se 1 (by rfl) ⟨4789448, by rfl⟩ : syracuseStep 6385931 = 9578897) B9578897
theorem B4257287 : Blo 1891435 4257287 := bstep (se 1 (by rfl) ⟨3192965, by rfl⟩ : syracuseStep 4257287 = 6385931) B6385931
theorem B2838191 : Blo 1891435 2838191 := bstep (se 1 (by rfl) ⟨2128643, by rfl⟩ : syracuseStep 2838191 = 4257287) B4257287
theorem B1892127 : Blo 1891435 1892127 := bstep (se 1 (by rfl) ⟨1419095, by rfl⟩ : syracuseStep 1892127 = 2838191) B2838191
theorem B2838197 : Blo 1891435 2838197 := bbase (se 5 (by rfl) ⟨133040, by rfl⟩ : syracuseStep 2838197 = 266081) (by norm_num)
theorem B1892131 : Blo 1891435 1892131 := bstep (se 1 (by rfl) ⟨1419098, by rfl⟩ : syracuseStep 1892131 = 2838197) B2838197
theorem B4789469 : Blo 1891435 4789469 := bbase (se 3 (by rfl) ⟨898025, by rfl⟩ : syracuseStep 4789469 = 1796051) (by norm_num)
theorem B3192979 : Blo 1891435 3192979 := bstep (se 1 (by rfl) ⟨2394734, by rfl⟩ : syracuseStep 3192979 = 4789469) B4789469
theorem B4257305 : Blo 1891435 4257305 := bstep (se 2 (by rfl) ⟨1596489, by rfl⟩ : syracuseStep 4257305 = 3192979) B3192979
theorem B2838203 : Blo 1891435 2838203 := bstep (se 1 (by rfl) ⟨2128652, by rfl⟩ : syracuseStep 2838203 = 4257305) B4257305
theorem B1892135 : Blo 1891435 1892135 := bstep (se 1 (by rfl) ⟨1419101, by rfl⟩ : syracuseStep 1892135 = 2838203) B2838203
theorem B2128657 : Blo 1891435 2128657 := bbase (se 2 (by rfl) ⟨798246, by rfl⟩ : syracuseStep 2128657 = 1596493) (by norm_num)
theorem B2838209 : Blo 1891435 2838209 := bstep (se 2 (by rfl) ⟨1064328, by rfl⟩ : syracuseStep 2838209 = 2128657) B2128657
theorem B1892139 : Blo 1891435 1892139 := bstep (se 1 (by rfl) ⟨1419104, by rfl⟩ : syracuseStep 1892139 = 2838209) B2838209
theorem B3592117 : Blo 1891435 3592117 := bbase (se 5 (by rfl) ⟨168380, by rfl⟩ : syracuseStep 3592117 = 336761) (by norm_num)
theorem B4789489 : Blo 1891435 4789489 := bstep (se 2 (by rfl) ⟨1796058, by rfl⟩ : syracuseStep 4789489 = 3592117) B3592117
theorem B6385985 : Blo 1891435 6385985 := bstep (se 2 (by rfl) ⟨2394744, by rfl⟩ : syracuseStep 6385985 = 4789489) B4789489
theorem B4257323 : Blo 1891435 4257323 := bstep (se 1 (by rfl) ⟨3192992, by rfl⟩ : syracuseStep 4257323 = 6385985) B6385985
theorem B2838215 : Blo 1891435 2838215 := bstep (se 1 (by rfl) ⟨2128661, by rfl⟩ : syracuseStep 2838215 = 4257323) B4257323
theorem B1892143 : Blo 1891435 1892143 := bstep (se 1 (by rfl) ⟨1419107, by rfl⟩ : syracuseStep 1892143 = 2838215) B2838215
theorem B2838221 : Blo 1891435 2838221 := bbase (se 3 (by rfl) ⟨532166, by rfl⟩ : syracuseStep 2838221 = 1064333) (by norm_num)
theorem B1892147 : Blo 1891435 1892147 := bstep (se 1 (by rfl) ⟨1419110, by rfl⟩ : syracuseStep 1892147 = 2838221) B2838221
theorem B4257341 : Blo 1891435 4257341 := bbase (se 3 (by rfl) ⟨798251, by rfl⟩ : syracuseStep 4257341 = 1596503) (by norm_num)
theorem B2838227 : Blo 1891435 2838227 := bstep (se 1 (by rfl) ⟨2128670, by rfl⟩ : syracuseStep 2838227 = 4257341) B4257341
theorem B1892151 : Blo 1891435 1892151 := bstep (se 1 (by rfl) ⟨1419113, by rfl⟩ : syracuseStep 1892151 = 2838227) B2838227
theorem B3193013 : Blo 1891435 3193013 := bbase (se 5 (by rfl) ⟨149672, by rfl⟩ : syracuseStep 3193013 = 299345) (by norm_num)
theorem B2128675 : Blo 1891435 2128675 := bstep (se 1 (by rfl) ⟨1596506, by rfl⟩ : syracuseStep 2128675 = 3193013) B3193013
theorem B2838233 : Blo 1891435 2838233 := bstep (se 2 (by rfl) ⟨1064337, by rfl⟩ : syracuseStep 2838233 = 2128675) B2128675
theorem B1892155 : Blo 1891435 1892155 := bstep (se 1 (by rfl) ⟨1419116, by rfl⟩ : syracuseStep 1892155 = 2838233) B2838233
theorem B1944145 : Blo 1891435 1944145 := bbase (se 2 (by rfl) ⟨729054, by rfl⟩ : syracuseStep 1944145 = 1458109) (by norm_num)
theorem B10368773 : Blo 1891435 10368773 := bstep (se 4 (by rfl) ⟨972072, by rfl⟩ : syracuseStep 10368773 = 1944145) B1944145
theorem B6912515 : Blo 1891435 6912515 := bstep (se 1 (by rfl) ⟨5184386, by rfl⟩ : syracuseStep 6912515 = 10368773) B10368773
theorem B4608343 : Blo 1891435 4608343 := bstep (se 1 (by rfl) ⟨3456257, by rfl⟩ : syracuseStep 4608343 = 6912515) B6912515
theorem B6144457 : Blo 1891435 6144457 := bstep (se 2 (by rfl) ⟨2304171, by rfl⟩ : syracuseStep 6144457 = 4608343) B4608343
theorem B8192609 : Blo 1891435 8192609 := bstep (se 2 (by rfl) ⟨3072228, by rfl⟩ : syracuseStep 8192609 = 6144457) B6144457
theorem B5461739 : Blo 1891435 5461739 := bstep (se 1 (by rfl) ⟨4096304, by rfl⟩ : syracuseStep 5461739 = 8192609) B8192609
theorem B3641159 : Blo 1891435 3641159 := bstep (se 1 (by rfl) ⟨2730869, by rfl⟩ : syracuseStep 3641159 = 5461739) B5461739
theorem B9709757 : Blo 1891435 9709757 := bstep (se 3 (by rfl) ⟨1820579, by rfl⟩ : syracuseStep 9709757 = 3641159) B3641159
theorem B6473171 : Blo 1891435 6473171 := bstep (se 1 (by rfl) ⟨4854878, by rfl⟩ : syracuseStep 6473171 = 9709757) B9709757
theorem B4315447 : Blo 1891435 4315447 := bstep (se 1 (by rfl) ⟨3236585, by rfl⟩ : syracuseStep 4315447 = 6473171) B6473171
theorem B5753929 : Blo 1891435 5753929 := bstep (se 2 (by rfl) ⟨2157723, by rfl⟩ : syracuseStep 5753929 = 4315447) B4315447
theorem B7671905 : Blo 1891435 7671905 := bstep (se 2 (by rfl) ⟨2876964, by rfl⟩ : syracuseStep 7671905 = 5753929) B5753929
theorem B5114603 : Blo 1891435 5114603 := bstep (se 1 (by rfl) ⟨3835952, by rfl⟩ : syracuseStep 5114603 = 7671905) B7671905
theorem B3409735 : Blo 1891435 3409735 := bstep (se 1 (by rfl) ⟨2557301, by rfl⟩ : syracuseStep 3409735 = 5114603) B5114603
theorem B4546313 : Blo 1891435 4546313 := bstep (se 2 (by rfl) ⟨1704867, by rfl⟩ : syracuseStep 4546313 = 3409735) B3409735
theorem B3030875 : Blo 1891435 3030875 := bstep (se 1 (by rfl) ⟨2273156, by rfl⟩ : syracuseStep 3030875 = 4546313) B4546313
theorem B2020583 : Blo 1891435 2020583 := bstep (se 1 (by rfl) ⟨1515437, by rfl⟩ : syracuseStep 2020583 = 3030875) B3030875
theorem B5388221 : Blo 1891435 5388221 := bstep (se 3 (by rfl) ⟨1010291, by rfl⟩ : syracuseStep 5388221 = 2020583) B2020583
theorem B14368589 : Blo 1891435 14368589 := bstep (se 3 (by rfl) ⟨2694110, by rfl⟩ : syracuseStep 14368589 = 5388221) B5388221
theorem B9579059 : Blo 1891435 9579059 := bstep (se 1 (by rfl) ⟨7184294, by rfl⟩ : syracuseStep 9579059 = 14368589) B14368589
theorem B6386039 : Blo 1891435 6386039 := bstep (se 1 (by rfl) ⟨4789529, by rfl⟩ : syracuseStep 6386039 = 9579059) B9579059
theorem B4257359 : Blo 1891435 4257359 := bstep (se 1 (by rfl) ⟨3193019, by rfl⟩ : syracuseStep 4257359 = 6386039) B6386039
theorem B2838239 : Blo 1891435 2838239 := bstep (se 1 (by rfl) ⟨2128679, by rfl⟩ : syracuseStep 2838239 = 4257359) B4257359
theorem B1892159 : Blo 1891435 1892159 := bstep (se 1 (by rfl) ⟨1419119, by rfl⟩ : syracuseStep 1892159 = 2838239) B2838239
theorem B2838245 : Blo 1891435 2838245 := bbase (se 4 (by rfl) ⟨266085, by rfl⟩ : syracuseStep 2838245 = 532171) (by norm_num)
theorem B1892163 : Blo 1891435 1892163 := bstep (se 1 (by rfl) ⟨1419122, by rfl⟩ : syracuseStep 1892163 = 2838245) B2838245
theorem B5388245 : Blo 1891435 5388245 := bbase (se 7 (by rfl) ⟨63143, by rfl⟩ : syracuseStep 5388245 = 126287) (by norm_num)
theorem B3592163 : Blo 1891435 3592163 := bstep (se 1 (by rfl) ⟨2694122, by rfl⟩ : syracuseStep 3592163 = 5388245) B5388245
theorem B2394775 : Blo 1891435 2394775 := bstep (se 1 (by rfl) ⟨1796081, by rfl⟩ : syracuseStep 2394775 = 3592163) B3592163
theorem B3193033 : Blo 1891435 3193033 := bstep (se 2 (by rfl) ⟨1197387, by rfl⟩ : syracuseStep 3193033 = 2394775) B2394775
theorem B4257377 : Blo 1891435 4257377 := bstep (se 2 (by rfl) ⟨1596516, by rfl⟩ : syracuseStep 4257377 = 3193033) B3193033
theorem B2838251 : Blo 1891435 2838251 := bstep (se 1 (by rfl) ⟨2128688, by rfl⟩ : syracuseStep 2838251 = 4257377) B4257377
theorem B1892167 : Blo 1891435 1892167 := bstep (se 1 (by rfl) ⟨1419125, by rfl⟩ : syracuseStep 1892167 = 2838251) B2838251
theorem B2128693 : Blo 1891435 2128693 := bbase (se 5 (by rfl) ⟨99782, by rfl⟩ : syracuseStep 2128693 = 199565) (by norm_num)
theorem B2838257 : Blo 1891435 2838257 := bstep (se 2 (by rfl) ⟨1064346, by rfl⟩ : syracuseStep 2838257 = 2128693) B2128693
theorem B1892171 : Blo 1891435 1892171 := bstep (se 1 (by rfl) ⟨1419128, by rfl⟩ : syracuseStep 1892171 = 2838257) B2838257
theorem B2394785 : Blo 1891435 2394785 := bbase (se 2 (by rfl) ⟨898044, by rfl⟩ : syracuseStep 2394785 = 1796089) (by norm_num)
theorem B6386093 : Blo 1891435 6386093 := bstep (se 3 (by rfl) ⟨1197392, by rfl⟩ : syracuseStep 6386093 = 2394785) B2394785
theorem B4257395 : Blo 1891435 4257395 := bstep (se 1 (by rfl) ⟨3193046, by rfl⟩ : syracuseStep 4257395 = 6386093) B6386093
theorem B2838263 : Blo 1891435 2838263 := bstep (se 1 (by rfl) ⟨2128697, by rfl⟩ : syracuseStep 2838263 = 4257395) B4257395
theorem B1892175 : Blo 1891435 1892175 := bstep (se 1 (by rfl) ⟨1419131, by rfl⟩ : syracuseStep 1892175 = 2838263) B2838263
theorem B2838269 : Blo 1891435 2838269 := bbase (se 3 (by rfl) ⟨532175, by rfl⟩ : syracuseStep 2838269 = 1064351) (by norm_num)
theorem B1892179 : Blo 1891435 1892179 := bstep (se 1 (by rfl) ⟨1419134, by rfl⟩ : syracuseStep 1892179 = 2838269) B2838269
theorem B4257413 : Blo 1891435 4257413 := bbase (se 4 (by rfl) ⟨399132, by rfl⟩ : syracuseStep 4257413 = 798265) (by norm_num)
theorem B2838275 : Blo 1891435 2838275 := bstep (se 1 (by rfl) ⟨2128706, by rfl⟩ : syracuseStep 2838275 = 4257413) B4257413
theorem B1892183 : Blo 1891435 1892183 := bstep (se 1 (by rfl) ⟨1419137, by rfl⟩ : syracuseStep 1892183 = 2838275) B2838275
theorem B4546381 : Blo 1891435 4546381 := bbase (se 3 (by rfl) ⟨852446, by rfl⟩ : syracuseStep 4546381 = 1704893) (by norm_num)
theorem B6061841 : Blo 1891435 6061841 := bstep (se 2 (by rfl) ⟨2273190, by rfl⟩ : syracuseStep 6061841 = 4546381) B4546381
theorem B4041227 : Blo 1891435 4041227 := bstep (se 1 (by rfl) ⟨3030920, by rfl⟩ : syracuseStep 4041227 = 6061841) B6061841
theorem B2694151 : Blo 1891435 2694151 := bstep (se 1 (by rfl) ⟨2020613, by rfl⟩ : syracuseStep 2694151 = 4041227) B4041227
theorem B3592201 : Blo 1891435 3592201 := bstep (se 2 (by rfl) ⟨1347075, by rfl⟩ : syracuseStep 3592201 = 2694151) B2694151
theorem B4789601 : Blo 1891435 4789601 := bstep (se 2 (by rfl) ⟨1796100, by rfl⟩ : syracuseStep 4789601 = 3592201) B3592201
theorem B3193067 : Blo 1891435 3193067 := bstep (se 1 (by rfl) ⟨2394800, by rfl⟩ : syracuseStep 3193067 = 4789601) B4789601
theorem B2128711 : Blo 1891435 2128711 := bstep (se 1 (by rfl) ⟨1596533, by rfl⟩ : syracuseStep 2128711 = 3193067) B3193067
theorem B2838281 : Blo 1891435 2838281 := bstep (se 2 (by rfl) ⟨1064355, by rfl⟩ : syracuseStep 2838281 = 2128711) B2128711
theorem B1892187 : Blo 1891435 1892187 := bstep (se 1 (by rfl) ⟨1419140, by rfl⟩ : syracuseStep 1892187 = 2838281) B2838281
theorem B9579221 : Blo 1891435 9579221 := bbase (se 7 (by rfl) ⟨112256, by rfl⟩ : syracuseStep 9579221 = 224513) (by norm_num)
theorem B6386147 : Blo 1891435 6386147 := bstep (se 1 (by rfl) ⟨4789610, by rfl⟩ : syracuseStep 6386147 = 9579221) B9579221
theorem B4257431 : Blo 1891435 4257431 := bstep (se 1 (by rfl) ⟨3193073, by rfl⟩ : syracuseStep 4257431 = 6386147) B6386147
theorem B2838287 : Blo 1891435 2838287 := bstep (se 1 (by rfl) ⟨2128715, by rfl⟩ : syracuseStep 2838287 = 4257431) B4257431
theorem B1892191 : Blo 1891435 1892191 := bstep (se 1 (by rfl) ⟨1419143, by rfl⟩ : syracuseStep 1892191 = 2838287) B2838287
theorem B2838293 : Blo 1891435 2838293 := bbase (se 6 (by rfl) ⟨66522, by rfl⟩ : syracuseStep 2838293 = 133045) (by norm_num)
theorem B1892195 : Blo 1891435 1892195 := bstep (se 1 (by rfl) ⟨1419146, by rfl⟩ : syracuseStep 1892195 = 2838293) B2838293
theorem B7282469 : Blo 1891435 7282469 := bbase (se 4 (by rfl) ⟨682731, by rfl⟩ : syracuseStep 7282469 = 1365463) (by norm_num)
theorem B4854979 : Blo 1891435 4854979 := bstep (se 1 (by rfl) ⟨3641234, by rfl⟩ : syracuseStep 4854979 = 7282469) B7282469
theorem B6473305 : Blo 1891435 6473305 := bstep (se 2 (by rfl) ⟨2427489, by rfl⟩ : syracuseStep 6473305 = 4854979) B4854979
theorem B8631073 : Blo 1891435 8631073 := bstep (se 2 (by rfl) ⟨3236652, by rfl⟩ : syracuseStep 8631073 = 6473305) B6473305
theorem B11508097 : Blo 1891435 11508097 := bstep (se 2 (by rfl) ⟨4315536, by rfl⟩ : syracuseStep 11508097 = 8631073) B8631073
theorem B15344129 : Blo 1891435 15344129 := bstep (se 2 (by rfl) ⟨5754048, by rfl⟩ : syracuseStep 15344129 = 11508097) B11508097
theorem B10229419 : Blo 1891435 10229419 := bstep (se 1 (by rfl) ⟨7672064, by rfl⟩ : syracuseStep 10229419 = 15344129) B15344129
theorem B54556901 : Blo 1891435 54556901 := bstep (se 4 (by rfl) ⟨5114709, by rfl⟩ : syracuseStep 54556901 = 10229419) B10229419
theorem B36371267 : Blo 1891435 36371267 := bstep (se 1 (by rfl) ⟨27278450, by rfl⟩ : syracuseStep 36371267 = 54556901) B54556901
theorem B24247511 : Blo 1891435 24247511 := bstep (se 1 (by rfl) ⟨18185633, by rfl⟩ : syracuseStep 24247511 = 36371267) B36371267
theorem B16165007 : Blo 1891435 16165007 := bstep (se 1 (by rfl) ⟨12123755, by rfl⟩ : syracuseStep 16165007 = 24247511) B24247511
theorem B10776671 : Blo 1891435 10776671 := bstep (se 1 (by rfl) ⟨8082503, by rfl⟩ : syracuseStep 10776671 = 16165007) B16165007
theorem B7184447 : Blo 1891435 7184447 := bstep (se 1 (by rfl) ⟨5388335, by rfl⟩ : syracuseStep 7184447 = 10776671) B10776671
theorem B4789631 : Blo 1891435 4789631 := bstep (se 1 (by rfl) ⟨3592223, by rfl⟩ : syracuseStep 4789631 = 7184447) B7184447
theorem B3193087 : Blo 1891435 3193087 := bstep (se 1 (by rfl) ⟨2394815, by rfl⟩ : syracuseStep 3193087 = 4789631) B4789631
theorem B4257449 : Blo 1891435 4257449 := bstep (se 2 (by rfl) ⟨1596543, by rfl⟩ : syracuseStep 4257449 = 3193087) B3193087
theorem B2838299 : Blo 1891435 2838299 := bstep (se 1 (by rfl) ⟨2128724, by rfl⟩ : syracuseStep 2838299 = 4257449) B4257449
theorem B1892199 : Blo 1891435 1892199 := bstep (se 1 (by rfl) ⟨1419149, by rfl⟩ : syracuseStep 1892199 = 2838299) B2838299
theorem B2128729 : Blo 1891435 2128729 := bbase (se 2 (by rfl) ⟨798273, by rfl⟩ : syracuseStep 2128729 = 1596547) (by norm_num)
theorem B2838305 : Blo 1891435 2838305 := bstep (se 2 (by rfl) ⟨1064364, by rfl⟩ : syracuseStep 2838305 = 2128729) B2128729
theorem B1892203 : Blo 1891435 1892203 := bstep (se 1 (by rfl) ⟨1419152, by rfl⟩ : syracuseStep 1892203 = 2838305) B2838305
theorem B4041269 : Blo 1891435 4041269 := bbase (se 5 (by rfl) ⟨189434, by rfl⟩ : syracuseStep 4041269 = 378869) (by norm_num)
theorem B2694179 : Blo 1891435 2694179 := bstep (se 1 (by rfl) ⟨2020634, by rfl⟩ : syracuseStep 2694179 = 4041269) B4041269
theorem B7184477 : Blo 1891435 7184477 := bstep (se 3 (by rfl) ⟨1347089, by rfl⟩ : syracuseStep 7184477 = 2694179) B2694179
theorem B4789651 : Blo 1891435 4789651 := bstep (se 1 (by rfl) ⟨3592238, by rfl⟩ : syracuseStep 4789651 = 7184477) B7184477
theorem B6386201 : Blo 1891435 6386201 := bstep (se 2 (by rfl) ⟨2394825, by rfl⟩ : syracuseStep 6386201 = 4789651) B4789651
theorem B4257467 : Blo 1891435 4257467 := bstep (se 1 (by rfl) ⟨3193100, by rfl⟩ : syracuseStep 4257467 = 6386201) B6386201
theorem B2838311 : Blo 1891435 2838311 := bstep (se 1 (by rfl) ⟨2128733, by rfl⟩ : syracuseStep 2838311 = 4257467) B4257467
theorem B1892207 : Blo 1891435 1892207 := bstep (se 1 (by rfl) ⟨1419155, by rfl⟩ : syracuseStep 1892207 = 2838311) B2838311
theorem B2838317 : Blo 1891435 2838317 := bbase (se 3 (by rfl) ⟨532184, by rfl⟩ : syracuseStep 2838317 = 1064369) (by norm_num)
theorem B1892211 : Blo 1891435 1892211 := bstep (se 1 (by rfl) ⟨1419158, by rfl⟩ : syracuseStep 1892211 = 2838317) B2838317
theorem B4257485 : Blo 1891435 4257485 := bbase (se 3 (by rfl) ⟨798278, by rfl⟩ : syracuseStep 4257485 = 1596557) (by norm_num)
theorem B2838323 : Blo 1891435 2838323 := bstep (se 1 (by rfl) ⟨2128742, by rfl⟩ : syracuseStep 2838323 = 4257485) B4257485
theorem B1892215 : Blo 1891435 1892215 := bstep (se 1 (by rfl) ⟨1419161, by rfl⟩ : syracuseStep 1892215 = 2838323) B2838323
theorem B2394841 : Blo 1891435 2394841 := bbase (se 2 (by rfl) ⟨898065, by rfl⟩ : syracuseStep 2394841 = 1796131) (by norm_num)
theorem B3193121 : Blo 1891435 3193121 := bstep (se 2 (by rfl) ⟨1197420, by rfl⟩ : syracuseStep 3193121 = 2394841) B2394841
theorem B2128747 : Blo 1891435 2128747 := bstep (se 1 (by rfl) ⟨1596560, by rfl⟩ : syracuseStep 2128747 = 3193121) B3193121
theorem B2838329 : Blo 1891435 2838329 := bstep (se 2 (by rfl) ⟨1064373, by rfl⟩ : syracuseStep 2838329 = 2128747) B2128747
theorem B1892219 : Blo 1891435 1892219 := bstep (se 1 (by rfl) ⟨1419164, by rfl⟩ : syracuseStep 1892219 = 2838329) B2838329
theorem B2273233 : Blo 1891435 2273233 := bbase (se 2 (by rfl) ⟨852462, by rfl⟩ : syracuseStep 2273233 = 1704925) (by norm_num)
theorem B3030977 : Blo 1891435 3030977 := bstep (se 2 (by rfl) ⟨1136616, by rfl⟩ : syracuseStep 3030977 = 2273233) B2273233
theorem B8082605 : Blo 1891435 8082605 := bstep (se 3 (by rfl) ⟨1515488, by rfl⟩ : syracuseStep 8082605 = 3030977) B3030977
theorem B21553613 : Blo 1891435 21553613 := bstep (se 3 (by rfl) ⟨4041302, by rfl⟩ : syracuseStep 21553613 = 8082605) B8082605
theorem B14369075 : Blo 1891435 14369075 := bstep (se 1 (by rfl) ⟨10776806, by rfl⟩ : syracuseStep 14369075 = 21553613) B21553613
theorem B9579383 : Blo 1891435 9579383 := bstep (se 1 (by rfl) ⟨7184537, by rfl⟩ : syracuseStep 9579383 = 14369075) B14369075
theorem B6386255 : Blo 1891435 6386255 := bstep (se 1 (by rfl) ⟨4789691, by rfl⟩ : syracuseStep 6386255 = 9579383) B9579383
theorem B4257503 : Blo 1891435 4257503 := bstep (se 1 (by rfl) ⟨3193127, by rfl⟩ : syracuseStep 4257503 = 6386255) B6386255
theorem B2838335 : Blo 1891435 2838335 := bstep (se 1 (by rfl) ⟨2128751, by rfl⟩ : syracuseStep 2838335 = 4257503) B4257503
theorem B1892223 : Blo 1891435 1892223 := bstep (se 1 (by rfl) ⟨1419167, by rfl⟩ : syracuseStep 1892223 = 2838335) B2838335
theorem B2838341 : Blo 1891435 2838341 := bbase (se 4 (by rfl) ⟨266094, by rfl⟩ : syracuseStep 2838341 = 532189) (by norm_num)
theorem B1892227 : Blo 1891435 1892227 := bstep (se 1 (by rfl) ⟨1419170, by rfl⟩ : syracuseStep 1892227 = 2838341) B2838341
theorem B3193141 : Blo 1891435 3193141 := bbase (se 5 (by rfl) ⟨149678, by rfl⟩ : syracuseStep 3193141 = 299357) (by norm_num)
theorem B4257521 : Blo 1891435 4257521 := bstep (se 2 (by rfl) ⟨1596570, by rfl⟩ : syracuseStep 4257521 = 3193141) B3193141
theorem B2838347 : Blo 1891435 2838347 := bstep (se 1 (by rfl) ⟨2128760, by rfl⟩ : syracuseStep 2838347 = 4257521) B4257521
theorem B1892231 : Blo 1891435 1892231 := bstep (se 1 (by rfl) ⟨1419173, by rfl⟩ : syracuseStep 1892231 = 2838347) B2838347
theorem B2128765 : Blo 1891435 2128765 := bbase (se 3 (by rfl) ⟨399143, by rfl⟩ : syracuseStep 2128765 = 798287) (by norm_num)
theorem B2838353 : Blo 1891435 2838353 := bstep (se 2 (by rfl) ⟨1064382, by rfl⟩ : syracuseStep 2838353 = 2128765) B2128765
theorem B1892235 : Blo 1891435 1892235 := bstep (se 1 (by rfl) ⟨1419176, by rfl⟩ : syracuseStep 1892235 = 2838353) B2838353
theorem B6386309 : Blo 1891435 6386309 := bbase (se 4 (by rfl) ⟨598716, by rfl⟩ : syracuseStep 6386309 = 1197433) (by norm_num)
theorem B4257539 : Blo 1891435 4257539 := bstep (se 1 (by rfl) ⟨3193154, by rfl⟩ : syracuseStep 4257539 = 6386309) B6386309
theorem B2838359 : Blo 1891435 2838359 := bstep (se 1 (by rfl) ⟨2128769, by rfl⟩ : syracuseStep 2838359 = 4257539) B4257539
theorem B1892239 : Blo 1891435 1892239 := bstep (se 1 (by rfl) ⟨1419179, by rfl⟩ : syracuseStep 1892239 = 2838359) B2838359
theorem B2838365 : Blo 1891435 2838365 := bbase (se 3 (by rfl) ⟨532193, by rfl⟩ : syracuseStep 2838365 = 1064387) (by norm_num)
theorem B1892243 : Blo 1891435 1892243 := bstep (se 1 (by rfl) ⟨1419182, by rfl⟩ : syracuseStep 1892243 = 2838365) B2838365
theorem B4257557 : Blo 1891435 4257557 := bbase (se 6 (by rfl) ⟨99786, by rfl⟩ : syracuseStep 4257557 = 199573) (by norm_num)
theorem B2838371 : Blo 1891435 2838371 := bstep (se 1 (by rfl) ⟨2128778, by rfl⟩ : syracuseStep 2838371 = 4257557) B4257557
theorem B1892247 : Blo 1891435 1892247 := bstep (se 1 (by rfl) ⟨1419185, by rfl⟩ : syracuseStep 1892247 = 2838371) B2838371
theorem B7184645 : Blo 1891435 7184645 := bbase (se 4 (by rfl) ⟨673560, by rfl⟩ : syracuseStep 7184645 = 1347121) (by norm_num)
theorem B4789763 : Blo 1891435 4789763 := bstep (se 1 (by rfl) ⟨3592322, by rfl⟩ : syracuseStep 4789763 = 7184645) B7184645
theorem B3193175 : Blo 1891435 3193175 := bstep (se 1 (by rfl) ⟨2394881, by rfl⟩ : syracuseStep 3193175 = 4789763) B4789763
theorem B2128783 : Blo 1891435 2128783 := bstep (se 1 (by rfl) ⟨1596587, by rfl⟩ : syracuseStep 2128783 = 3193175) B3193175
theorem B2838377 : Blo 1891435 2838377 := bstep (se 2 (by rfl) ⟨1064391, by rfl⟩ : syracuseStep 2838377 = 2128783) B2128783
theorem B1892251 : Blo 1891435 1892251 := bstep (se 1 (by rfl) ⟨1419188, by rfl⟩ : syracuseStep 1892251 = 2838377) B2838377
theorem B4988509 : Blo 1891435 4988509 := bbase (se 3 (by rfl) ⟨935345, by rfl⟩ : syracuseStep 4988509 = 1870691) (by norm_num)
theorem B106421525 : Blo 1891435 106421525 := bstep (se 6 (by rfl) ⟨2494254, by rfl⟩ : syracuseStep 106421525 = 4988509) B4988509
theorem B70947683 : Blo 1891435 70947683 := bstep (se 1 (by rfl) ⟨53210762, by rfl⟩ : syracuseStep 70947683 = 106421525) B106421525
theorem B47298455 : Blo 1891435 47298455 := bstep (se 1 (by rfl) ⟨35473841, by rfl⟩ : syracuseStep 47298455 = 70947683) B70947683
theorem B31532303 : Blo 1891435 31532303 := bstep (se 1 (by rfl) ⟨23649227, by rfl⟩ : syracuseStep 31532303 = 47298455) B47298455
theorem B21021535 : Blo 1891435 21021535 := bstep (se 1 (by rfl) ⟨15766151, by rfl⟩ : syracuseStep 21021535 = 31532303) B31532303
theorem B112114853 : Blo 1891435 112114853 := bstep (se 4 (by rfl) ⟨10510767, by rfl⟩ : syracuseStep 112114853 = 21021535) B21021535
theorem B74743235 : Blo 1891435 74743235 := bstep (se 1 (by rfl) ⟨56057426, by rfl⟩ : syracuseStep 74743235 = 112114853) B112114853
theorem B49828823 : Blo 1891435 49828823 := bstep (se 1 (by rfl) ⟨37371617, by rfl⟩ : syracuseStep 49828823 = 74743235) B74743235
theorem B33219215 : Blo 1891435 33219215 := bstep (se 1 (by rfl) ⟨24914411, by rfl⟩ : syracuseStep 33219215 = 49828823) B49828823
theorem B22146143 : Blo 1891435 22146143 := bstep (se 1 (by rfl) ⟨16609607, by rfl⟩ : syracuseStep 22146143 = 33219215) B33219215
theorem B59056381 : Blo 1891435 59056381 := bstep (se 3 (by rfl) ⟨11073071, by rfl⟩ : syracuseStep 59056381 = 22146143) B22146143
theorem B78741841 : Blo 1891435 78741841 := bstep (se 2 (by rfl) ⟨29528190, by rfl⟩ : syracuseStep 78741841 = 59056381) B59056381
theorem B104989121 : Blo 1891435 104989121 := bstep (se 2 (by rfl) ⟨39370920, by rfl⟩ : syracuseStep 104989121 = 78741841) B78741841
theorem B69992747 : Blo 1891435 69992747 := bstep (se 1 (by rfl) ⟨52494560, by rfl⟩ : syracuseStep 69992747 = 104989121) B104989121
theorem B46661831 : Blo 1891435 46661831 := bstep (se 1 (by rfl) ⟨34996373, by rfl⟩ : syracuseStep 46661831 = 69992747) B69992747
theorem B31107887 : Blo 1891435 31107887 := bstep (se 1 (by rfl) ⟨23330915, by rfl⟩ : syracuseStep 31107887 = 46661831) B46661831
theorem B20738591 : Blo 1891435 20738591 := bstep (se 1 (by rfl) ⟨15553943, by rfl⟩ : syracuseStep 20738591 = 31107887) B31107887
theorem B13825727 : Blo 1891435 13825727 := bstep (se 1 (by rfl) ⟨10369295, by rfl⟩ : syracuseStep 13825727 = 20738591) B20738591
theorem B9217151 : Blo 1891435 9217151 := bstep (se 1 (by rfl) ⟨6912863, by rfl⟩ : syracuseStep 9217151 = 13825727) B13825727
theorem B6144767 : Blo 1891435 6144767 := bstep (se 1 (by rfl) ⟨4608575, by rfl⟩ : syracuseStep 6144767 = 9217151) B9217151
theorem B4096511 : Blo 1891435 4096511 := bstep (se 1 (by rfl) ⟨3072383, by rfl⟩ : syracuseStep 4096511 = 6144767) B6144767
theorem B2731007 : Blo 1891435 2731007 := bstep (se 1 (by rfl) ⟨2048255, by rfl⟩ : syracuseStep 2731007 = 4096511) B4096511
theorem B7282685 : Blo 1891435 7282685 := bstep (se 3 (by rfl) ⟨1365503, by rfl⟩ : syracuseStep 7282685 = 2731007) B2731007
theorem B4855123 : Blo 1891435 4855123 := bstep (se 1 (by rfl) ⟨3641342, by rfl⟩ : syracuseStep 4855123 = 7282685) B7282685
theorem B25893989 : Blo 1891435 25893989 := bstep (se 4 (by rfl) ⟨2427561, by rfl⟩ : syracuseStep 25893989 = 4855123) B4855123
theorem B17262659 : Blo 1891435 17262659 := bstep (se 1 (by rfl) ⟨12946994, by rfl⟩ : syracuseStep 17262659 = 25893989) B25893989
theorem B11508439 : Blo 1891435 11508439 := bstep (se 1 (by rfl) ⟨8631329, by rfl⟩ : syracuseStep 11508439 = 17262659) B17262659
theorem B15344585 : Blo 1891435 15344585 := bstep (se 2 (by rfl) ⟨5754219, by rfl⟩ : syracuseStep 15344585 = 11508439) B11508439
theorem B10229723 : Blo 1891435 10229723 := bstep (se 1 (by rfl) ⟨7672292, by rfl⟩ : syracuseStep 10229723 = 15344585) B15344585
theorem B6819815 : Blo 1891435 6819815 := bstep (se 1 (by rfl) ⟨5114861, by rfl⟩ : syracuseStep 6819815 = 10229723) B10229723
theorem B4546543 : Blo 1891435 4546543 := bstep (se 1 (by rfl) ⟨3409907, by rfl⟩ : syracuseStep 4546543 = 6819815) B6819815
theorem B6062057 : Blo 1891435 6062057 := bstep (se 2 (by rfl) ⟨2273271, by rfl⟩ : syracuseStep 6062057 = 4546543) B4546543
theorem B4041371 : Blo 1891435 4041371 := bstep (se 1 (by rfl) ⟨3031028, by rfl⟩ : syracuseStep 4041371 = 6062057) B6062057
theorem B10776989 : Blo 1891435 10776989 := bstep (se 3 (by rfl) ⟨2020685, by rfl⟩ : syracuseStep 10776989 = 4041371) B4041371
theorem B7184659 : Blo 1891435 7184659 := bstep (se 1 (by rfl) ⟨5388494, by rfl⟩ : syracuseStep 7184659 = 10776989) B10776989
theorem B9579545 : Blo 1891435 9579545 := bstep (se 2 (by rfl) ⟨3592329, by rfl⟩ : syracuseStep 9579545 = 7184659) B7184659
theorem B6386363 : Blo 1891435 6386363 := bstep (se 1 (by rfl) ⟨4789772, by rfl⟩ : syracuseStep 6386363 = 9579545) B9579545
theorem B4257575 : Blo 1891435 4257575 := bstep (se 1 (by rfl) ⟨3193181, by rfl⟩ : syracuseStep 4257575 = 6386363) B6386363
theorem B2838383 : Blo 1891435 2838383 := bstep (se 1 (by rfl) ⟨2128787, by rfl⟩ : syracuseStep 2838383 = 4257575) B4257575
theorem B1892255 : Blo 1891435 1892255 := bstep (se 1 (by rfl) ⟨1419191, by rfl⟩ : syracuseStep 1892255 = 2838383) B2838383
theorem B2838389 : Blo 1891435 2838389 := bbase (se 5 (by rfl) ⟨133049, by rfl⟩ : syracuseStep 2838389 = 266099) (by norm_num)
theorem B1892259 : Blo 1891435 1892259 := bstep (se 1 (by rfl) ⟨1419194, by rfl⟩ : syracuseStep 1892259 = 2838389) B2838389
theorem B4041389 : Blo 1891435 4041389 := bbase (se 3 (by rfl) ⟨757760, by rfl⟩ : syracuseStep 4041389 = 1515521) (by norm_num)
theorem B2694259 : Blo 1891435 2694259 := bstep (se 1 (by rfl) ⟨2020694, by rfl⟩ : syracuseStep 2694259 = 4041389) B4041389
theorem B3592345 : Blo 1891435 3592345 := bstep (se 2 (by rfl) ⟨1347129, by rfl⟩ : syracuseStep 3592345 = 2694259) B2694259
theorem B4789793 : Blo 1891435 4789793 := bstep (se 2 (by rfl) ⟨1796172, by rfl⟩ : syracuseStep 4789793 = 3592345) B3592345
theorem B3193195 : Blo 1891435 3193195 := bstep (se 1 (by rfl) ⟨2394896, by rfl⟩ : syracuseStep 3193195 = 4789793) B4789793
theorem B4257593 : Blo 1891435 4257593 := bstep (se 2 (by rfl) ⟨1596597, by rfl⟩ : syracuseStep 4257593 = 3193195) B3193195
theorem B2838395 : Blo 1891435 2838395 := bstep (se 1 (by rfl) ⟨2128796, by rfl⟩ : syracuseStep 2838395 = 4257593) B4257593
theorem B1892263 : Blo 1891435 1892263 := bstep (se 1 (by rfl) ⟨1419197, by rfl⟩ : syracuseStep 1892263 = 2838395) B2838395
theorem B2128801 : Blo 1891435 2128801 := bbase (se 2 (by rfl) ⟨798300, by rfl⟩ : syracuseStep 2128801 = 1596601) (by norm_num)
theorem B2838401 : Blo 1891435 2838401 := bstep (se 2 (by rfl) ⟨1064400, by rfl⟩ : syracuseStep 2838401 = 2128801) B2128801
theorem B1892267 : Blo 1891435 1892267 := bstep (se 1 (by rfl) ⟨1419200, by rfl⟩ : syracuseStep 1892267 = 2838401) B2838401
theorem B4789813 : Blo 1891435 4789813 := bbase (se 5 (by rfl) ⟨224522, by rfl⟩ : syracuseStep 4789813 = 449045) (by norm_num)
theorem B6386417 : Blo 1891435 6386417 := bstep (se 2 (by rfl) ⟨2394906, by rfl⟩ : syracuseStep 6386417 = 4789813) B4789813
theorem B4257611 : Blo 1891435 4257611 := bstep (se 1 (by rfl) ⟨3193208, by rfl⟩ : syracuseStep 4257611 = 6386417) B6386417
theorem B2838407 : Blo 1891435 2838407 := bstep (se 1 (by rfl) ⟨2128805, by rfl⟩ : syracuseStep 2838407 = 4257611) B4257611
theorem B1892271 : Blo 1891435 1892271 := bstep (se 1 (by rfl) ⟨1419203, by rfl⟩ : syracuseStep 1892271 = 2838407) B2838407
theorem B2838413 : Blo 1891435 2838413 := bbase (se 3 (by rfl) ⟨532202, by rfl⟩ : syracuseStep 2838413 = 1064405) (by norm_num)
theorem B1892275 : Blo 1891435 1892275 := bstep (se 1 (by rfl) ⟨1419206, by rfl⟩ : syracuseStep 1892275 = 2838413) B2838413
theorem B4257629 : Blo 1891435 4257629 := bbase (se 3 (by rfl) ⟨798305, by rfl⟩ : syracuseStep 4257629 = 1596611) (by norm_num)
theorem B2838419 : Blo 1891435 2838419 := bstep (se 1 (by rfl) ⟨2128814, by rfl⟩ : syracuseStep 2838419 = 4257629) B4257629
theorem B1892279 : Blo 1891435 1892279 := bstep (se 1 (by rfl) ⟨1419209, by rfl⟩ : syracuseStep 1892279 = 2838419) B2838419
theorem B3193229 : Blo 1891435 3193229 := bbase (se 3 (by rfl) ⟨598730, by rfl⟩ : syracuseStep 3193229 = 1197461) (by norm_num)
theorem B2128819 : Blo 1891435 2128819 := bstep (se 1 (by rfl) ⟨1596614, by rfl⟩ : syracuseStep 2128819 = 3193229) B3193229
theorem B2838425 : Blo 1891435 2838425 := bstep (se 2 (by rfl) ⟨1064409, by rfl⟩ : syracuseStep 2838425 = 2128819) B2128819
theorem B1892283 : Blo 1891435 1892283 := bstep (se 1 (by rfl) ⟨1419212, by rfl⟩ : syracuseStep 1892283 = 2838425) B2838425
theorem B7672421 : Blo 1891435 7672421 := bbase (se 4 (by rfl) ⟨719289, by rfl⟩ : syracuseStep 7672421 = 1438579) (by norm_num)
theorem B20459789 : Blo 1891435 20459789 := bstep (se 3 (by rfl) ⟨3836210, by rfl⟩ : syracuseStep 20459789 = 7672421) B7672421
theorem B13639859 : Blo 1891435 13639859 := bstep (se 1 (by rfl) ⟨10229894, by rfl⟩ : syracuseStep 13639859 = 20459789) B20459789
theorem B9093239 : Blo 1891435 9093239 := bstep (se 1 (by rfl) ⟨6819929, by rfl⟩ : syracuseStep 9093239 = 13639859) B13639859
theorem B6062159 : Blo 1891435 6062159 := bstep (se 1 (by rfl) ⟨4546619, by rfl⟩ : syracuseStep 6062159 = 9093239) B9093239
theorem B16165757 : Blo 1891435 16165757 := bstep (se 3 (by rfl) ⟨3031079, by rfl⟩ : syracuseStep 16165757 = 6062159) B6062159
theorem B10777171 : Blo 1891435 10777171 := bstep (se 1 (by rfl) ⟨8082878, by rfl⟩ : syracuseStep 10777171 = 16165757) B16165757
theorem B14369561 : Blo 1891435 14369561 := bstep (se 2 (by rfl) ⟨5388585, by rfl⟩ : syracuseStep 14369561 = 10777171) B10777171
theorem B9579707 : Blo 1891435 9579707 := bstep (se 1 (by rfl) ⟨7184780, by rfl⟩ : syracuseStep 9579707 = 14369561) B14369561
theorem B6386471 : Blo 1891435 6386471 := bstep (se 1 (by rfl) ⟨4789853, by rfl⟩ : syracuseStep 6386471 = 9579707) B9579707
theorem B4257647 : Blo 1891435 4257647 := bstep (se 1 (by rfl) ⟨3193235, by rfl⟩ : syracuseStep 4257647 = 6386471) B6386471
theorem B2838431 : Blo 1891435 2838431 := bstep (se 1 (by rfl) ⟨2128823, by rfl⟩ : syracuseStep 2838431 = 4257647) B4257647
theorem B1892287 : Blo 1891435 1892287 := bstep (se 1 (by rfl) ⟨1419215, by rfl⟩ : syracuseStep 1892287 = 2838431) B2838431
theorem B2838437 : Blo 1891435 2838437 := bbase (se 4 (by rfl) ⟨266103, by rfl⟩ : syracuseStep 2838437 = 532207) (by norm_num)
theorem B1892291 : Blo 1891435 1892291 := bstep (se 1 (by rfl) ⟨1419218, by rfl⟩ : syracuseStep 1892291 = 2838437) B2838437
theorem B2394937 : Blo 1891435 2394937 := bbase (se 2 (by rfl) ⟨898101, by rfl⟩ : syracuseStep 2394937 = 1796203) (by norm_num)
theorem B3193249 : Blo 1891435 3193249 := bstep (se 2 (by rfl) ⟨1197468, by rfl⟩ : syracuseStep 3193249 = 2394937) B2394937
theorem B4257665 : Blo 1891435 4257665 := bstep (se 2 (by rfl) ⟨1596624, by rfl⟩ : syracuseStep 4257665 = 3193249) B3193249
theorem B2838443 : Blo 1891435 2838443 := bstep (se 1 (by rfl) ⟨2128832, by rfl⟩ : syracuseStep 2838443 = 4257665) B4257665
theorem B1892295 : Blo 1891435 1892295 := bstep (se 1 (by rfl) ⟨1419221, by rfl⟩ : syracuseStep 1892295 = 2838443) B2838443
theorem B2128837 : Blo 1891435 2128837 := bbase (se 4 (by rfl) ⟨199578, by rfl⟩ : syracuseStep 2128837 = 399157) (by norm_num)
theorem B2838449 : Blo 1891435 2838449 := bstep (se 2 (by rfl) ⟨1064418, by rfl⟩ : syracuseStep 2838449 = 2128837) B2128837
theorem B1892299 : Blo 1891435 1892299 := bstep (se 1 (by rfl) ⟨1419224, by rfl⟩ : syracuseStep 1892299 = 2838449) B2838449
theorem B3592421 : Blo 1891435 3592421 := bbase (se 4 (by rfl) ⟨336789, by rfl⟩ : syracuseStep 3592421 = 673579) (by norm_num)
theorem B2394947 : Blo 1891435 2394947 := bstep (se 1 (by rfl) ⟨1796210, by rfl⟩ : syracuseStep 2394947 = 3592421) B3592421
theorem B6386525 : Blo 1891435 6386525 := bstep (se 3 (by rfl) ⟨1197473, by rfl⟩ : syracuseStep 6386525 = 2394947) B2394947
theorem B4257683 : Blo 1891435 4257683 := bstep (se 1 (by rfl) ⟨3193262, by rfl⟩ : syracuseStep 4257683 = 6386525) B6386525
theorem B2838455 : Blo 1891435 2838455 := bstep (se 1 (by rfl) ⟨2128841, by rfl⟩ : syracuseStep 2838455 = 4257683) B4257683
theorem B1892303 : Blo 1891435 1892303 := bstep (se 1 (by rfl) ⟨1419227, by rfl⟩ : syracuseStep 1892303 = 2838455) B2838455
theorem B2838461 : Blo 1891435 2838461 := bbase (se 3 (by rfl) ⟨532211, by rfl⟩ : syracuseStep 2838461 = 1064423) (by norm_num)
theorem B1892307 : Blo 1891435 1892307 := bstep (se 1 (by rfl) ⟨1419230, by rfl⟩ : syracuseStep 1892307 = 2838461) B2838461
theorem B4257701 : Blo 1891435 4257701 := bbase (se 4 (by rfl) ⟨399159, by rfl⟩ : syracuseStep 4257701 = 798319) (by norm_num)
theorem B2838467 : Blo 1891435 2838467 := bstep (se 1 (by rfl) ⟨2128850, by rfl⟩ : syracuseStep 2838467 = 4257701) B4257701
theorem B1892311 : Blo 1891435 1892311 := bstep (se 1 (by rfl) ⟨1419233, by rfl⟩ : syracuseStep 1892311 = 2838467) B2838467
theorem B4789925 : Blo 1891435 4789925 := bbase (se 4 (by rfl) ⟨449055, by rfl⟩ : syracuseStep 4789925 = 898111) (by norm_num)
theorem B3193283 : Blo 1891435 3193283 := bstep (se 1 (by rfl) ⟨2394962, by rfl⟩ : syracuseStep 3193283 = 4789925) B4789925
theorem B2128855 : Blo 1891435 2128855 := bstep (se 1 (by rfl) ⟨1596641, by rfl⟩ : syracuseStep 2128855 = 3193283) B3193283
theorem B2838473 : Blo 1891435 2838473 := bstep (se 2 (by rfl) ⟨1064427, by rfl⟩ : syracuseStep 2838473 = 2128855) B2128855
theorem B1892315 : Blo 1891435 1892315 := bstep (se 1 (by rfl) ⟨1419236, by rfl⟩ : syracuseStep 1892315 = 2838473) B2838473
theorem B5388677 : Blo 1891435 5388677 := bbase (se 4 (by rfl) ⟨505188, by rfl⟩ : syracuseStep 5388677 = 1010377) (by norm_num)
theorem B3592451 : Blo 1891435 3592451 := bstep (se 1 (by rfl) ⟨2694338, by rfl⟩ : syracuseStep 3592451 = 5388677) B5388677
theorem B9579869 : Blo 1891435 9579869 := bstep (se 3 (by rfl) ⟨1796225, by rfl⟩ : syracuseStep 9579869 = 3592451) B3592451
theorem B6386579 : Blo 1891435 6386579 := bstep (se 1 (by rfl) ⟨4789934, by rfl⟩ : syracuseStep 6386579 = 9579869) B9579869
theorem B4257719 : Blo 1891435 4257719 := bstep (se 1 (by rfl) ⟨3193289, by rfl⟩ : syracuseStep 4257719 = 6386579) B6386579
theorem B2838479 : Blo 1891435 2838479 := bstep (se 1 (by rfl) ⟨2128859, by rfl⟩ : syracuseStep 2838479 = 4257719) B4257719
theorem B1892319 : Blo 1891435 1892319 := bstep (se 1 (by rfl) ⟨1419239, by rfl⟩ : syracuseStep 1892319 = 2838479) B2838479
theorem B2838485 : Blo 1891435 2838485 := bbase (se 7 (by rfl) ⟨33263, by rfl⟩ : syracuseStep 2838485 = 66527) (by norm_num)
theorem B1892323 : Blo 1891435 1892323 := bstep (se 1 (by rfl) ⟨1419242, by rfl⟩ : syracuseStep 1892323 = 2838485) B2838485
theorem B7184933 : Blo 1891435 7184933 := bbase (se 4 (by rfl) ⟨673587, by rfl⟩ : syracuseStep 7184933 = 1347175) (by norm_num)
theorem B4789955 : Blo 1891435 4789955 := bstep (se 1 (by rfl) ⟨3592466, by rfl⟩ : syracuseStep 4789955 = 7184933) B7184933
theorem B3193303 : Blo 1891435 3193303 := bstep (se 1 (by rfl) ⟨2394977, by rfl⟩ : syracuseStep 3193303 = 4789955) B4789955
theorem B4257737 : Blo 1891435 4257737 := bstep (se 2 (by rfl) ⟨1596651, by rfl⟩ : syracuseStep 4257737 = 3193303) B3193303
theorem B2838491 : Blo 1891435 2838491 := bstep (se 1 (by rfl) ⟨2128868, by rfl⟩ : syracuseStep 2838491 = 4257737) B4257737
theorem B1892327 : Blo 1891435 1892327 := bstep (se 1 (by rfl) ⟨1419245, by rfl⟩ : syracuseStep 1892327 = 2838491) B2838491
theorem B2128873 : Blo 1891435 2128873 := bbase (se 2 (by rfl) ⟨798327, by rfl⟩ : syracuseStep 2128873 = 1596655) (by norm_num)
theorem B2838497 : Blo 1891435 2838497 := bstep (se 2 (by rfl) ⟨1064436, by rfl⟩ : syracuseStep 2838497 = 2128873) B2128873
theorem B1892331 : Blo 1891435 1892331 := bstep (se 1 (by rfl) ⟨1419248, by rfl⟩ : syracuseStep 1892331 = 2838497) B2838497
theorem B3031157 : Blo 1891435 3031157 := bbase (se 5 (by rfl) ⟨142085, by rfl⟩ : syracuseStep 3031157 = 284171) (by norm_num)
theorem B2020771 : Blo 1891435 2020771 := bstep (se 1 (by rfl) ⟨1515578, by rfl⟩ : syracuseStep 2020771 = 3031157) B3031157
theorem B10777445 : Blo 1891435 10777445 := bstep (se 4 (by rfl) ⟨1010385, by rfl⟩ : syracuseStep 10777445 = 2020771) B2020771
theorem B7184963 : Blo 1891435 7184963 := bstep (se 1 (by rfl) ⟨5388722, by rfl⟩ : syracuseStep 7184963 = 10777445) B10777445
theorem B4789975 : Blo 1891435 4789975 := bstep (se 1 (by rfl) ⟨3592481, by rfl⟩ : syracuseStep 4789975 = 7184963) B7184963
theorem B6386633 : Blo 1891435 6386633 := bstep (se 2 (by rfl) ⟨2394987, by rfl⟩ : syracuseStep 6386633 = 4789975) B4789975
theorem B4257755 : Blo 1891435 4257755 := bstep (se 1 (by rfl) ⟨3193316, by rfl⟩ : syracuseStep 4257755 = 6386633) B6386633
theorem B2838503 : Blo 1891435 2838503 := bstep (se 1 (by rfl) ⟨2128877, by rfl⟩ : syracuseStep 2838503 = 4257755) B4257755
theorem B1892335 : Blo 1891435 1892335 := bstep (se 1 (by rfl) ⟨1419251, by rfl⟩ : syracuseStep 1892335 = 2838503) B2838503
theorem B2838509 : Blo 1891435 2838509 := bbase (se 3 (by rfl) ⟨532220, by rfl⟩ : syracuseStep 2838509 = 1064441) (by norm_num)
theorem B1892339 : Blo 1891435 1892339 := bstep (se 1 (by rfl) ⟨1419254, by rfl⟩ : syracuseStep 1892339 = 2838509) B2838509
theorem B4257773 : Blo 1891435 4257773 := bbase (se 3 (by rfl) ⟨798332, by rfl⟩ : syracuseStep 4257773 = 1596665) (by norm_num)
theorem B2838515 : Blo 1891435 2838515 := bstep (se 1 (by rfl) ⟨2128886, by rfl⟩ : syracuseStep 2838515 = 4257773) B4257773
theorem B1892343 : Blo 1891435 1892343 := bstep (se 1 (by rfl) ⟨1419257, by rfl⟩ : syracuseStep 1892343 = 2838515) B2838515
theorem B9710725 : Blo 1891435 9710725 := bbase (se 4 (by rfl) ⟨910380, by rfl⟩ : syracuseStep 9710725 = 1820761) (by norm_num)
theorem B12947633 : Blo 1891435 12947633 := bstep (se 2 (by rfl) ⟨4855362, by rfl⟩ : syracuseStep 12947633 = 9710725) B9710725
theorem B8631755 : Blo 1891435 8631755 := bstep (se 1 (by rfl) ⟨6473816, by rfl⟩ : syracuseStep 8631755 = 12947633) B12947633
theorem B5754503 : Blo 1891435 5754503 := bstep (se 1 (by rfl) ⟨4315877, by rfl⟩ : syracuseStep 5754503 = 8631755) B8631755
theorem B3836335 : Blo 1891435 3836335 := bstep (se 1 (by rfl) ⟨2877251, by rfl⟩ : syracuseStep 3836335 = 5754503) B5754503
theorem B5115113 : Blo 1891435 5115113 := bstep (se 2 (by rfl) ⟨1918167, by rfl⟩ : syracuseStep 5115113 = 3836335) B3836335
theorem B3410075 : Blo 1891435 3410075 := bstep (se 1 (by rfl) ⟨2557556, by rfl⟩ : syracuseStep 3410075 = 5115113) B5115113
theorem B2273383 : Blo 1891435 2273383 := bstep (se 1 (by rfl) ⟨1705037, by rfl⟩ : syracuseStep 2273383 = 3410075) B3410075
theorem B3031177 : Blo 1891435 3031177 := bstep (se 2 (by rfl) ⟨1136691, by rfl⟩ : syracuseStep 3031177 = 2273383) B2273383
theorem B4041569 : Blo 1891435 4041569 := bstep (se 2 (by rfl) ⟨1515588, by rfl⟩ : syracuseStep 4041569 = 3031177) B3031177
theorem B2694379 : Blo 1891435 2694379 := bstep (se 1 (by rfl) ⟨2020784, by rfl⟩ : syracuseStep 2694379 = 4041569) B4041569
theorem B3592505 : Blo 1891435 3592505 := bstep (se 2 (by rfl) ⟨1347189, by rfl⟩ : syracuseStep 3592505 = 2694379) B2694379
theorem B2395003 : Blo 1891435 2395003 := bstep (se 1 (by rfl) ⟨1796252, by rfl⟩ : syracuseStep 2395003 = 3592505) B3592505
theorem B3193337 : Blo 1891435 3193337 := bstep (se 2 (by rfl) ⟨1197501, by rfl⟩ : syracuseStep 3193337 = 2395003) B2395003
theorem B2128891 : Blo 1891435 2128891 := bstep (se 1 (by rfl) ⟨1596668, by rfl⟩ : syracuseStep 2128891 = 3193337) B3193337
theorem B2838521 : Blo 1891435 2838521 := bstep (se 2 (by rfl) ⟨1064445, by rfl⟩ : syracuseStep 2838521 = 2128891) B2128891
theorem B1892347 : Blo 1891435 1892347 := bstep (se 1 (by rfl) ⟨1419260, by rfl⟩ : syracuseStep 1892347 = 2838521) B2838521
theorem B3456605 : Blo 1891435 3456605 := bbase (se 3 (by rfl) ⟨648113, by rfl⟩ : syracuseStep 3456605 = 1296227) (by norm_num)
theorem B9217613 : Blo 1891435 9217613 := bstep (se 3 (by rfl) ⟨1728302, by rfl⟩ : syracuseStep 9217613 = 3456605) B3456605
theorem B6145075 : Blo 1891435 6145075 := bstep (se 1 (by rfl) ⟨4608806, by rfl⟩ : syracuseStep 6145075 = 9217613) B9217613
theorem B32773733 : Blo 1891435 32773733 := bstep (se 4 (by rfl) ⟨3072537, by rfl⟩ : syracuseStep 32773733 = 6145075) B6145075
theorem B21849155 : Blo 1891435 21849155 := bstep (se 1 (by rfl) ⟨16386866, by rfl⟩ : syracuseStep 21849155 = 32773733) B32773733
theorem B14566103 : Blo 1891435 14566103 := bstep (se 1 (by rfl) ⟨10924577, by rfl⟩ : syracuseStep 14566103 = 21849155) B21849155
theorem B9710735 : Blo 1891435 9710735 := bstep (se 1 (by rfl) ⟨7283051, by rfl⟩ : syracuseStep 9710735 = 14566103) B14566103
theorem B103581173 : Blo 1891435 103581173 := bstep (se 5 (by rfl) ⟨4855367, by rfl⟩ : syracuseStep 103581173 = 9710735) B9710735
theorem B69054115 : Blo 1891435 69054115 := bstep (se 1 (by rfl) ⟨51790586, by rfl⟩ : syracuseStep 69054115 = 103581173) B103581173
theorem B92072153 : Blo 1891435 92072153 := bstep (se 2 (by rfl) ⟨34527057, by rfl⟩ : syracuseStep 92072153 = 69054115) B69054115
theorem B245525741 : Blo 1891435 245525741 := bstep (se 3 (by rfl) ⟨46036076, by rfl⟩ : syracuseStep 245525741 = 92072153) B92072153
theorem B163683827 : Blo 1891435 163683827 := bstep (se 1 (by rfl) ⟨122762870, by rfl⟩ : syracuseStep 163683827 = 245525741) B245525741
theorem B109122551 : Blo 1891435 109122551 := bstep (se 1 (by rfl) ⟨81841913, by rfl⟩ : syracuseStep 109122551 = 163683827) B163683827
theorem B72748367 : Blo 1891435 72748367 := bstep (se 1 (by rfl) ⟨54561275, by rfl⟩ : syracuseStep 72748367 = 109122551) B109122551
theorem B48498911 : Blo 1891435 48498911 := bstep (se 1 (by rfl) ⟨36374183, by rfl⟩ : syracuseStep 48498911 = 72748367) B72748367
theorem B32332607 : Blo 1891435 32332607 := bstep (se 1 (by rfl) ⟨24249455, by rfl⟩ : syracuseStep 32332607 = 48498911) B48498911
theorem B21555071 : Blo 1891435 21555071 := bstep (se 1 (by rfl) ⟨16166303, by rfl⟩ : syracuseStep 21555071 = 32332607) B32332607
theorem B14370047 : Blo 1891435 14370047 := bstep (se 1 (by rfl) ⟨10777535, by rfl⟩ : syracuseStep 14370047 = 21555071) B21555071
theorem B9580031 : Blo 1891435 9580031 := bstep (se 1 (by rfl) ⟨7185023, by rfl⟩ : syracuseStep 9580031 = 14370047) B14370047
theorem B6386687 : Blo 1891435 6386687 := bstep (se 1 (by rfl) ⟨4790015, by rfl⟩ : syracuseStep 6386687 = 9580031) B9580031
theorem B4257791 : Blo 1891435 4257791 := bstep (se 1 (by rfl) ⟨3193343, by rfl⟩ : syracuseStep 4257791 = 6386687) B6386687
theorem B2838527 : Blo 1891435 2838527 := bstep (se 1 (by rfl) ⟨2128895, by rfl⟩ : syracuseStep 2838527 = 4257791) B4257791
theorem B1892351 : Blo 1891435 1892351 := bstep (se 1 (by rfl) ⟨1419263, by rfl⟩ : syracuseStep 1892351 = 2838527) B2838527
theorem B2838533 : Blo 1891435 2838533 := bbase (se 4 (by rfl) ⟨266112, by rfl⟩ : syracuseStep 2838533 = 532225) (by norm_num)
theorem B1892355 : Blo 1891435 1892355 := bstep (se 1 (by rfl) ⟨1419266, by rfl⟩ : syracuseStep 1892355 = 2838533) B2838533
theorem B3193357 : Blo 1891435 3193357 := bbase (se 3 (by rfl) ⟨598754, by rfl⟩ : syracuseStep 3193357 = 1197509) (by norm_num)
theorem B4257809 : Blo 1891435 4257809 := bstep (se 2 (by rfl) ⟨1596678, by rfl⟩ : syracuseStep 4257809 = 3193357) B3193357
theorem B2838539 : Blo 1891435 2838539 := bstep (se 1 (by rfl) ⟨2128904, by rfl⟩ : syracuseStep 2838539 = 4257809) B4257809
theorem B1892359 : Blo 1891435 1892359 := bstep (se 1 (by rfl) ⟨1419269, by rfl⟩ : syracuseStep 1892359 = 2838539) B2838539
theorem B2128909 : Blo 1891435 2128909 := bbase (se 3 (by rfl) ⟨399170, by rfl⟩ : syracuseStep 2128909 = 798341) (by norm_num)
theorem B2838545 : Blo 1891435 2838545 := bstep (se 2 (by rfl) ⟨1064454, by rfl⟩ : syracuseStep 2838545 = 2128909) B2128909
theorem B1892363 : Blo 1891435 1892363 := bstep (se 1 (by rfl) ⟨1419272, by rfl⟩ : syracuseStep 1892363 = 2838545) B2838545
theorem B6386741 : Blo 1891435 6386741 := bbase (se 5 (by rfl) ⟨299378, by rfl⟩ : syracuseStep 6386741 = 598757) (by norm_num)
theorem B4257827 : Blo 1891435 4257827 := bstep (se 1 (by rfl) ⟨3193370, by rfl⟩ : syracuseStep 4257827 = 6386741) B6386741
theorem B2838551 : Blo 1891435 2838551 := bstep (se 1 (by rfl) ⟨2128913, by rfl⟩ : syracuseStep 2838551 = 4257827) B4257827
theorem B1892367 : Blo 1891435 1892367 := bstep (se 1 (by rfl) ⟨1419275, by rfl⟩ : syracuseStep 1892367 = 2838551) B2838551
theorem B2838557 : Blo 1891435 2838557 := bbase (se 3 (by rfl) ⟨532229, by rfl⟩ : syracuseStep 2838557 = 1064459) (by norm_num)
theorem B1892371 : Blo 1891435 1892371 := bstep (se 1 (by rfl) ⟨1419278, by rfl⟩ : syracuseStep 1892371 = 2838557) B2838557
theorem B4257845 : Blo 1891435 4257845 := bbase (se 5 (by rfl) ⟨199586, by rfl⟩ : syracuseStep 4257845 = 399173) (by norm_num)
theorem B2838563 : Blo 1891435 2838563 := bstep (se 1 (by rfl) ⟨2128922, by rfl⟩ : syracuseStep 2838563 = 4257845) B4257845
theorem B1892375 : Blo 1891435 1892375 := bstep (se 1 (by rfl) ⟨1419281, by rfl⟩ : syracuseStep 1892375 = 2838563) B2838563
theorem B4315949 : Blo 1891435 4315949 := bbase (se 3 (by rfl) ⟨809240, by rfl⟩ : syracuseStep 4315949 = 1618481) (by norm_num)
theorem B2877299 : Blo 1891435 2877299 := bstep (se 1 (by rfl) ⟨2157974, by rfl⟩ : syracuseStep 2877299 = 4315949) B4315949
theorem B1918199 : Blo 1891435 1918199 := bstep (se 1 (by rfl) ⟨1438649, by rfl⟩ : syracuseStep 1918199 = 2877299) B2877299
theorem B5115197 : Blo 1891435 5115197 := bstep (se 3 (by rfl) ⟨959099, by rfl⟩ : syracuseStep 5115197 = 1918199) B1918199
theorem B13640525 : Blo 1891435 13640525 := bstep (se 3 (by rfl) ⟨2557598, by rfl⟩ : syracuseStep 13640525 = 5115197) B5115197
theorem B9093683 : Blo 1891435 9093683 := bstep (se 1 (by rfl) ⟨6820262, by rfl⟩ : syracuseStep 9093683 = 13640525) B13640525
theorem B6062455 : Blo 1891435 6062455 := bstep (se 1 (by rfl) ⟨4546841, by rfl⟩ : syracuseStep 6062455 = 9093683) B9093683
theorem B8083273 : Blo 1891435 8083273 := bstep (se 2 (by rfl) ⟨3031227, by rfl⟩ : syracuseStep 8083273 = 6062455) B6062455
theorem B10777697 : Blo 1891435 10777697 := bstep (se 2 (by rfl) ⟨4041636, by rfl⟩ : syracuseStep 10777697 = 8083273) B8083273
theorem B7185131 : Blo 1891435 7185131 := bstep (se 1 (by rfl) ⟨5388848, by rfl⟩ : syracuseStep 7185131 = 10777697) B10777697
theorem B4790087 : Blo 1891435 4790087 := bstep (se 1 (by rfl) ⟨3592565, by rfl⟩ : syracuseStep 4790087 = 7185131) B7185131
theorem B3193391 : Blo 1891435 3193391 := bstep (se 1 (by rfl) ⟨2395043, by rfl⟩ : syracuseStep 3193391 = 4790087) B4790087
theorem B2128927 : Blo 1891435 2128927 := bstep (se 1 (by rfl) ⟨1596695, by rfl⟩ : syracuseStep 2128927 = 3193391) B3193391
theorem B2838569 : Blo 1891435 2838569 := bstep (se 2 (by rfl) ⟨1064463, by rfl⟩ : syracuseStep 2838569 = 2128927) B2128927
theorem B1892379 : Blo 1891435 1892379 := bstep (se 1 (by rfl) ⟨1419284, by rfl⟩ : syracuseStep 1892379 = 2838569) B2838569
theorem B9093701 : Blo 1891435 9093701 := bbase (se 4 (by rfl) ⟨852534, by rfl⟩ : syracuseStep 9093701 = 1705069) (by norm_num)
theorem B6062467 : Blo 1891435 6062467 := bstep (se 1 (by rfl) ⟨4546850, by rfl⟩ : syracuseStep 6062467 = 9093701) B9093701
theorem B8083289 : Blo 1891435 8083289 := bstep (se 2 (by rfl) ⟨3031233, by rfl⟩ : syracuseStep 8083289 = 6062467) B6062467
theorem B5388859 : Blo 1891435 5388859 := bstep (se 1 (by rfl) ⟨4041644, by rfl⟩ : syracuseStep 5388859 = 8083289) B8083289
theorem B7185145 : Blo 1891435 7185145 := bstep (se 2 (by rfl) ⟨2694429, by rfl⟩ : syracuseStep 7185145 = 5388859) B5388859
theorem B9580193 : Blo 1891435 9580193 := bstep (se 2 (by rfl) ⟨3592572, by rfl⟩ : syracuseStep 9580193 = 7185145) B7185145
theorem B6386795 : Blo 1891435 6386795 := bstep (se 1 (by rfl) ⟨4790096, by rfl⟩ : syracuseStep 6386795 = 9580193) B9580193
theorem B4257863 : Blo 1891435 4257863 := bstep (se 1 (by rfl) ⟨3193397, by rfl⟩ : syracuseStep 4257863 = 6386795) B6386795
theorem B2838575 : Blo 1891435 2838575 := bstep (se 1 (by rfl) ⟨2128931, by rfl⟩ : syracuseStep 2838575 = 4257863) B4257863
theorem B1892383 : Blo 1891435 1892383 := bstep (se 1 (by rfl) ⟨1419287, by rfl⟩ : syracuseStep 1892383 = 2838575) B2838575
theorem B2838581 : Blo 1891435 2838581 := bbase (se 5 (by rfl) ⟨133058, by rfl⟩ : syracuseStep 2838581 = 266117) (by norm_num)
theorem B1892387 : Blo 1891435 1892387 := bstep (se 1 (by rfl) ⟨1419290, by rfl⟩ : syracuseStep 1892387 = 2838581) B2838581
theorem B4790117 : Blo 1891435 4790117 := bbase (se 4 (by rfl) ⟨449073, by rfl⟩ : syracuseStep 4790117 = 898147) (by norm_num)
theorem B3193411 : Blo 1891435 3193411 := bstep (se 1 (by rfl) ⟨2395058, by rfl⟩ : syracuseStep 3193411 = 4790117) B4790117
theorem B4257881 : Blo 1891435 4257881 := bstep (se 2 (by rfl) ⟨1596705, by rfl⟩ : syracuseStep 4257881 = 3193411) B3193411
theorem B2838587 : Blo 1891435 2838587 := bstep (se 1 (by rfl) ⟨2128940, by rfl⟩ : syracuseStep 2838587 = 4257881) B4257881
theorem B1892391 : Blo 1891435 1892391 := bstep (se 1 (by rfl) ⟨1419293, by rfl⟩ : syracuseStep 1892391 = 2838587) B2838587
theorem B2128945 : Blo 1891435 2128945 := bbase (se 2 (by rfl) ⟨798354, by rfl⟩ : syracuseStep 2128945 = 1596709) (by norm_num)
theorem B2838593 : Blo 1891435 2838593 := bstep (se 2 (by rfl) ⟨1064472, by rfl⟩ : syracuseStep 2838593 = 2128945) B2128945
theorem B1892395 : Blo 1891435 1892395 := bstep (se 1 (by rfl) ⟨1419296, by rfl⟩ : syracuseStep 1892395 = 2838593) B2838593
theorem B2157997 : Blo 1891435 2157997 := bbase (se 3 (by rfl) ⟨404624, by rfl⟩ : syracuseStep 2157997 = 809249) (by norm_num)
theorem B2877329 : Blo 1891435 2877329 := bstep (se 2 (by rfl) ⟨1078998, by rfl⟩ : syracuseStep 2877329 = 2157997) B2157997
theorem B7672877 : Blo 1891435 7672877 := bstep (se 3 (by rfl) ⟨1438664, by rfl⟩ : syracuseStep 7672877 = 2877329) B2877329
theorem B5115251 : Blo 1891435 5115251 := bstep (se 1 (by rfl) ⟨3836438, by rfl⟩ : syracuseStep 5115251 = 7672877) B7672877
theorem B13640669 : Blo 1891435 13640669 := bstep (se 3 (by rfl) ⟨2557625, by rfl⟩ : syracuseStep 13640669 = 5115251) B5115251
theorem B9093779 : Blo 1891435 9093779 := bstep (se 1 (by rfl) ⟨6820334, by rfl⟩ : syracuseStep 9093779 = 13640669) B13640669
theorem B6062519 : Blo 1891435 6062519 := bstep (se 1 (by rfl) ⟨4546889, by rfl⟩ : syracuseStep 6062519 = 9093779) B9093779
theorem B4041679 : Blo 1891435 4041679 := bstep (se 1 (by rfl) ⟨3031259, by rfl⟩ : syracuseStep 4041679 = 6062519) B6062519
theorem B5388905 : Blo 1891435 5388905 := bstep (se 2 (by rfl) ⟨2020839, by rfl⟩ : syracuseStep 5388905 = 4041679) B4041679
theorem B3592603 : Blo 1891435 3592603 := bstep (se 1 (by rfl) ⟨2694452, by rfl⟩ : syracuseStep 3592603 = 5388905) B5388905
theorem B4790137 : Blo 1891435 4790137 := bstep (se 2 (by rfl) ⟨1796301, by rfl⟩ : syracuseStep 4790137 = 3592603) B3592603
theorem B6386849 : Blo 1891435 6386849 := bstep (se 2 (by rfl) ⟨2395068, by rfl⟩ : syracuseStep 6386849 = 4790137) B4790137
theorem B4257899 : Blo 1891435 4257899 := bstep (se 1 (by rfl) ⟨3193424, by rfl⟩ : syracuseStep 4257899 = 6386849) B6386849
theorem B2838599 : Blo 1891435 2838599 := bstep (se 1 (by rfl) ⟨2128949, by rfl⟩ : syracuseStep 2838599 = 4257899) B4257899
theorem B1892399 : Blo 1891435 1892399 := bstep (se 1 (by rfl) ⟨1419299, by rfl⟩ : syracuseStep 1892399 = 2838599) B2838599
theorem B2838605 : Blo 1891435 2838605 := bbase (se 3 (by rfl) ⟨532238, by rfl⟩ : syracuseStep 2838605 = 1064477) (by norm_num)
theorem B1892403 : Blo 1891435 1892403 := bstep (se 1 (by rfl) ⟨1419302, by rfl⟩ : syracuseStep 1892403 = 2838605) B2838605
theorem B4257917 : Blo 1891435 4257917 := bbase (se 3 (by rfl) ⟨798359, by rfl⟩ : syracuseStep 4257917 = 1596719) (by norm_num)
theorem B2838611 : Blo 1891435 2838611 := bstep (se 1 (by rfl) ⟨2128958, by rfl⟩ : syracuseStep 2838611 = 4257917) B4257917
theorem B1892407 : Blo 1891435 1892407 := bstep (se 1 (by rfl) ⟨1419305, by rfl⟩ : syracuseStep 1892407 = 2838611) B2838611
theorem B3193445 : Blo 1891435 3193445 := bbase (se 4 (by rfl) ⟨299385, by rfl⟩ : syracuseStep 3193445 = 598771) (by norm_num)
theorem B2128963 : Blo 1891435 2128963 := bstep (se 1 (by rfl) ⟨1596722, by rfl⟩ : syracuseStep 2128963 = 3193445) B3193445
theorem B2838617 : Blo 1891435 2838617 := bstep (se 2 (by rfl) ⟨1064481, by rfl⟩ : syracuseStep 2838617 = 2128963) B2128963
theorem B1892411 : Blo 1891435 1892411 := bstep (se 1 (by rfl) ⟨1419308, by rfl⟩ : syracuseStep 1892411 = 2838617) B2838617
theorem B3031285 : Blo 1891435 3031285 := bbase (se 5 (by rfl) ⟨142091, by rfl⟩ : syracuseStep 3031285 = 284183) (by norm_num)
theorem B4041713 : Blo 1891435 4041713 := bstep (se 2 (by rfl) ⟨1515642, by rfl⟩ : syracuseStep 4041713 = 3031285) B3031285
theorem B2694475 : Blo 1891435 2694475 := bstep (se 1 (by rfl) ⟨2020856, by rfl⟩ : syracuseStep 2694475 = 4041713) B4041713
theorem B14370533 : Blo 1891435 14370533 := bstep (se 4 (by rfl) ⟨1347237, by rfl⟩ : syracuseStep 14370533 = 2694475) B2694475
theorem B9580355 : Blo 1891435 9580355 := bstep (se 1 (by rfl) ⟨7185266, by rfl⟩ : syracuseStep 9580355 = 14370533) B14370533
theorem B6386903 : Blo 1891435 6386903 := bstep (se 1 (by rfl) ⟨4790177, by rfl⟩ : syracuseStep 6386903 = 9580355) B9580355
theorem B4257935 : Blo 1891435 4257935 := bstep (se 1 (by rfl) ⟨3193451, by rfl⟩ : syracuseStep 4257935 = 6386903) B6386903
theorem B2838623 : Blo 1891435 2838623 := bstep (se 1 (by rfl) ⟨2128967, by rfl⟩ : syracuseStep 2838623 = 4257935) B4257935
theorem B1892415 : Blo 1891435 1892415 := bstep (se 1 (by rfl) ⟨1419311, by rfl⟩ : syracuseStep 1892415 = 2838623) B2838623
theorem B2838629 : Blo 1891435 2838629 := bbase (se 4 (by rfl) ⟨266121, by rfl⟩ : syracuseStep 2838629 = 532243) (by norm_num)
theorem B1892419 : Blo 1891435 1892419 := bstep (se 1 (by rfl) ⟨1419314, by rfl⟩ : syracuseStep 1892419 = 2838629) B2838629
theorem B6062597 : Blo 1891435 6062597 := bbase (se 4 (by rfl) ⟨568368, by rfl⟩ : syracuseStep 6062597 = 1136737) (by norm_num)
theorem B4041731 : Blo 1891435 4041731 := bstep (se 1 (by rfl) ⟨3031298, by rfl⟩ : syracuseStep 4041731 = 6062597) B6062597
theorem B2694487 : Blo 1891435 2694487 := bstep (se 1 (by rfl) ⟨2020865, by rfl⟩ : syracuseStep 2694487 = 4041731) B4041731
theorem B3592649 : Blo 1891435 3592649 := bstep (se 2 (by rfl) ⟨1347243, by rfl⟩ : syracuseStep 3592649 = 2694487) B2694487
theorem B2395099 : Blo 1891435 2395099 := bstep (se 1 (by rfl) ⟨1796324, by rfl⟩ : syracuseStep 2395099 = 3592649) B3592649
theorem B3193465 : Blo 1891435 3193465 := bstep (se 2 (by rfl) ⟨1197549, by rfl⟩ : syracuseStep 3193465 = 2395099) B2395099
theorem B4257953 : Blo 1891435 4257953 := bstep (se 2 (by rfl) ⟨1596732, by rfl⟩ : syracuseStep 4257953 = 3193465) B3193465
theorem B2838635 : Blo 1891435 2838635 := bstep (se 1 (by rfl) ⟨2128976, by rfl⟩ : syracuseStep 2838635 = 4257953) B4257953
theorem B1892423 : Blo 1891435 1892423 := bstep (se 1 (by rfl) ⟨1419317, by rfl⟩ : syracuseStep 1892423 = 2838635) B2838635
theorem B2128981 : Blo 1891435 2128981 := bbase (se 8 (by rfl) ⟨12474, by rfl⟩ : syracuseStep 2128981 = 24949) (by norm_num)
theorem B2838641 : Blo 1891435 2838641 := bstep (se 2 (by rfl) ⟨1064490, by rfl⟩ : syracuseStep 2838641 = 2128981) B2128981
theorem B1892427 : Blo 1891435 1892427 := bstep (se 1 (by rfl) ⟨1419320, by rfl⟩ : syracuseStep 1892427 = 2838641) B2838641
theorem B2395109 : Blo 1891435 2395109 := bbase (se 4 (by rfl) ⟨224541, by rfl⟩ : syracuseStep 2395109 = 449083) (by norm_num)
theorem B6386957 : Blo 1891435 6386957 := bstep (se 3 (by rfl) ⟨1197554, by rfl⟩ : syracuseStep 6386957 = 2395109) B2395109
theorem B4257971 : Blo 1891435 4257971 := bstep (se 1 (by rfl) ⟨3193478, by rfl⟩ : syracuseStep 4257971 = 6386957) B6386957
theorem B2838647 : Blo 1891435 2838647 := bstep (se 1 (by rfl) ⟨2128985, by rfl⟩ : syracuseStep 2838647 = 4257971) B4257971
theorem B1892431 : Blo 1891435 1892431 := bstep (se 1 (by rfl) ⟨1419323, by rfl⟩ : syracuseStep 1892431 = 2838647) B2838647
theorem B2838653 : Blo 1891435 2838653 := bbase (se 3 (by rfl) ⟨532247, by rfl⟩ : syracuseStep 2838653 = 1064495) (by norm_num)
theorem B1892435 : Blo 1891435 1892435 := bstep (se 1 (by rfl) ⟨1419326, by rfl⟩ : syracuseStep 1892435 = 2838653) B2838653
theorem B4257989 : Blo 1891435 4257989 := bbase (se 4 (by rfl) ⟨399186, by rfl⟩ : syracuseStep 4257989 = 798373) (by norm_num)
theorem B2838659 : Blo 1891435 2838659 := bstep (se 1 (by rfl) ⟨2128994, by rfl⟩ : syracuseStep 2838659 = 4257989) B4257989
theorem B1892439 : Blo 1891435 1892439 := bstep (se 1 (by rfl) ⟨1419329, by rfl⟩ : syracuseStep 1892439 = 2838659) B2838659
theorem B59062229 : Blo 1891435 59062229 := bbase (se 7 (by rfl) ⟨692135, by rfl⟩ : syracuseStep 59062229 = 1384271) (by norm_num)
theorem B39374819 : Blo 1891435 39374819 := bstep (se 1 (by rfl) ⟨29531114, by rfl⟩ : syracuseStep 39374819 = 59062229) B59062229
theorem B26249879 : Blo 1891435 26249879 := bstep (se 1 (by rfl) ⟨19687409, by rfl⟩ : syracuseStep 26249879 = 39374819) B39374819
theorem B17499919 : Blo 1891435 17499919 := bstep (se 1 (by rfl) ⟨13124939, by rfl⟩ : syracuseStep 17499919 = 26249879) B26249879
theorem B23333225 : Blo 1891435 23333225 := bstep (se 2 (by rfl) ⟨8749959, by rfl⟩ : syracuseStep 23333225 = 17499919) B17499919
theorem B62221933 : Blo 1891435 62221933 := bstep (se 3 (by rfl) ⟨11666612, by rfl⟩ : syracuseStep 62221933 = 23333225) B23333225
theorem B82962577 : Blo 1891435 82962577 := bstep (se 2 (by rfl) ⟨31110966, by rfl⟩ : syracuseStep 82962577 = 62221933) B62221933
theorem B110616769 : Blo 1891435 110616769 := bstep (se 2 (by rfl) ⟨41481288, by rfl⟩ : syracuseStep 110616769 = 82962577) B82962577
theorem B147489025 : Blo 1891435 147489025 := bstep (se 2 (by rfl) ⟨55308384, by rfl⟩ : syracuseStep 147489025 = 110616769) B110616769
theorem B196652033 : Blo 1891435 196652033 := bstep (se 2 (by rfl) ⟨73744512, by rfl⟩ : syracuseStep 196652033 = 147489025) B147489025
theorem B131101355 : Blo 1891435 131101355 := bstep (se 1 (by rfl) ⟨98326016, by rfl⟩ : syracuseStep 131101355 = 196652033) B196652033
theorem B87400903 : Blo 1891435 87400903 := bstep (se 1 (by rfl) ⟨65550677, by rfl⟩ : syracuseStep 87400903 = 131101355) B131101355
theorem B116534537 : Blo 1891435 116534537 := bstep (se 2 (by rfl) ⟨43700451, by rfl⟩ : syracuseStep 116534537 = 87400903) B87400903
theorem B77689691 : Blo 1891435 77689691 := bstep (se 1 (by rfl) ⟨58267268, by rfl⟩ : syracuseStep 77689691 = 116534537) B116534537
theorem B51793127 : Blo 1891435 51793127 := bstep (se 1 (by rfl) ⟨38844845, by rfl⟩ : syracuseStep 51793127 = 77689691) B77689691
theorem B34528751 : Blo 1891435 34528751 := bstep (se 1 (by rfl) ⟨25896563, by rfl⟩ : syracuseStep 34528751 = 51793127) B51793127
theorem B23019167 : Blo 1891435 23019167 := bstep (se 1 (by rfl) ⟨17264375, by rfl⟩ : syracuseStep 23019167 = 34528751) B34528751
theorem B15346111 : Blo 1891435 15346111 := bstep (se 1 (by rfl) ⟨11509583, by rfl⟩ : syracuseStep 15346111 = 23019167) B23019167
theorem B20461481 : Blo 1891435 20461481 := bstep (se 2 (by rfl) ⟨7673055, by rfl⟩ : syracuseStep 20461481 = 15346111) B15346111
theorem B13640987 : Blo 1891435 13640987 := bstep (se 1 (by rfl) ⟨10230740, by rfl⟩ : syracuseStep 13640987 = 20461481) B20461481
theorem B9093991 : Blo 1891435 9093991 := bstep (se 1 (by rfl) ⟨6820493, by rfl⟩ : syracuseStep 9093991 = 13640987) B13640987
theorem B12125321 : Blo 1891435 12125321 := bstep (se 2 (by rfl) ⟨4546995, by rfl⟩ : syracuseStep 12125321 = 9093991) B9093991
theorem B8083547 : Blo 1891435 8083547 := bstep (se 1 (by rfl) ⟨6062660, by rfl⟩ : syracuseStep 8083547 = 12125321) B12125321
theorem B5389031 : Blo 1891435 5389031 := bstep (se 1 (by rfl) ⟨4041773, by rfl⟩ : syracuseStep 5389031 = 8083547) B8083547
theorem B3592687 : Blo 1891435 3592687 := bstep (se 1 (by rfl) ⟨2694515, by rfl⟩ : syracuseStep 3592687 = 5389031) B5389031
theorem B4790249 : Blo 1891435 4790249 := bstep (se 2 (by rfl) ⟨1796343, by rfl⟩ : syracuseStep 4790249 = 3592687) B3592687
theorem B3193499 : Blo 1891435 3193499 := bstep (se 1 (by rfl) ⟨2395124, by rfl⟩ : syracuseStep 3193499 = 4790249) B4790249
theorem B2128999 : Blo 1891435 2128999 := bstep (se 1 (by rfl) ⟨1596749, by rfl⟩ : syracuseStep 2128999 = 3193499) B3193499
theorem B2838665 : Blo 1891435 2838665 := bstep (se 2 (by rfl) ⟨1064499, by rfl⟩ : syracuseStep 2838665 = 2128999) B2128999
theorem B1892443 : Blo 1891435 1892443 := bstep (se 1 (by rfl) ⟨1419332, by rfl⟩ : syracuseStep 1892443 = 2838665) B2838665
theorem B9580517 : Blo 1891435 9580517 := bbase (se 4 (by rfl) ⟨898173, by rfl⟩ : syracuseStep 9580517 = 1796347) (by norm_num)
theorem B6387011 : Blo 1891435 6387011 := bstep (se 1 (by rfl) ⟨4790258, by rfl⟩ : syracuseStep 6387011 = 9580517) B9580517
theorem B4258007 : Blo 1891435 4258007 := bstep (se 1 (by rfl) ⟨3193505, by rfl⟩ : syracuseStep 4258007 = 6387011) B6387011
theorem B2838671 : Blo 1891435 2838671 := bstep (se 1 (by rfl) ⟨2129003, by rfl⟩ : syracuseStep 2838671 = 4258007) B4258007
theorem B1892447 : Blo 1891435 1892447 := bstep (se 1 (by rfl) ⟨1419335, by rfl⟩ : syracuseStep 1892447 = 2838671) B2838671
theorem B2838677 : Blo 1891435 2838677 := bbase (se 6 (by rfl) ⟨66531, by rfl⟩ : syracuseStep 2838677 = 133063) (by norm_num)
theorem B1892451 : Blo 1891435 1892451 := bstep (se 1 (by rfl) ⟨1419338, by rfl⟩ : syracuseStep 1892451 = 2838677) B2838677
theorem B3031349 : Blo 1891435 3031349 := bbase (se 5 (by rfl) ⟨142094, by rfl⟩ : syracuseStep 3031349 = 284189) (by norm_num)
theorem B8083597 : Blo 1891435 8083597 := bstep (se 3 (by rfl) ⟨1515674, by rfl⟩ : syracuseStep 8083597 = 3031349) B3031349
theorem B10778129 : Blo 1891435 10778129 := bstep (se 2 (by rfl) ⟨4041798, by rfl⟩ : syracuseStep 10778129 = 8083597) B8083597
theorem B7185419 : Blo 1891435 7185419 := bstep (se 1 (by rfl) ⟨5389064, by rfl⟩ : syracuseStep 7185419 = 10778129) B10778129
theorem B4790279 : Blo 1891435 4790279 := bstep (se 1 (by rfl) ⟨3592709, by rfl⟩ : syracuseStep 4790279 = 7185419) B7185419
theorem B3193519 : Blo 1891435 3193519 := bstep (se 1 (by rfl) ⟨2395139, by rfl⟩ : syracuseStep 3193519 = 4790279) B4790279
theorem B4258025 : Blo 1891435 4258025 := bstep (se 2 (by rfl) ⟨1596759, by rfl⟩ : syracuseStep 4258025 = 3193519) B3193519
theorem B2838683 : Blo 1891435 2838683 := bstep (se 1 (by rfl) ⟨2129012, by rfl⟩ : syracuseStep 2838683 = 4258025) B4258025
theorem B1892455 : Blo 1891435 1892455 := bstep (se 1 (by rfl) ⟨1419341, by rfl⟩ : syracuseStep 1892455 = 2838683) B2838683
theorem B2129017 : Blo 1891435 2129017 := bbase (se 2 (by rfl) ⟨798381, by rfl⟩ : syracuseStep 2129017 = 1596763) (by norm_num)
theorem B2838689 : Blo 1891435 2838689 := bstep (se 2 (by rfl) ⟨1064508, by rfl⟩ : syracuseStep 2838689 = 2129017) B2129017
theorem B1892459 : Blo 1891435 1892459 := bstep (se 1 (by rfl) ⟨1419344, by rfl⟩ : syracuseStep 1892459 = 2838689) B2838689
theorem B6913621 : Blo 1891435 6913621 := bbase (se 8 (by rfl) ⟨40509, by rfl⟩ : syracuseStep 6913621 = 81019) (by norm_num)
theorem B9218161 : Blo 1891435 9218161 := bstep (se 2 (by rfl) ⟨3456810, by rfl⟩ : syracuseStep 9218161 = 6913621) B6913621
theorem B12290881 : Blo 1891435 12290881 := bstep (se 2 (by rfl) ⟨4609080, by rfl⟩ : syracuseStep 12290881 = 9218161) B9218161
theorem B16387841 : Blo 1891435 16387841 := bstep (se 2 (by rfl) ⟨6145440, by rfl⟩ : syracuseStep 16387841 = 12290881) B12290881
theorem B10925227 : Blo 1891435 10925227 := bstep (se 1 (by rfl) ⟨8193920, by rfl⟩ : syracuseStep 10925227 = 16387841) B16387841
theorem B14566969 : Blo 1891435 14566969 := bstep (se 2 (by rfl) ⟨5462613, by rfl⟩ : syracuseStep 14566969 = 10925227) B10925227
theorem B19422625 : Blo 1891435 19422625 := bstep (se 2 (by rfl) ⟨7283484, by rfl⟩ : syracuseStep 19422625 = 14566969) B14566969
theorem B25896833 : Blo 1891435 25896833 := bstep (se 2 (by rfl) ⟨9711312, by rfl⟩ : syracuseStep 25896833 = 19422625) B19422625
theorem B17264555 : Blo 1891435 17264555 := bstep (se 1 (by rfl) ⟨12948416, by rfl⟩ : syracuseStep 17264555 = 25896833) B25896833
theorem B11509703 : Blo 1891435 11509703 := bstep (se 1 (by rfl) ⟨8632277, by rfl⟩ : syracuseStep 11509703 = 17264555) B17264555
theorem B7673135 : Blo 1891435 7673135 := bstep (se 1 (by rfl) ⟨5754851, by rfl⟩ : syracuseStep 7673135 = 11509703) B11509703
theorem B20461693 : Blo 1891435 20461693 := bstep (se 3 (by rfl) ⟨3836567, by rfl⟩ : syracuseStep 20461693 = 7673135) B7673135
theorem B27282257 : Blo 1891435 27282257 := bstep (se 2 (by rfl) ⟨10230846, by rfl⟩ : syracuseStep 27282257 = 20461693) B20461693
theorem B18188171 : Blo 1891435 18188171 := bstep (se 1 (by rfl) ⟨13641128, by rfl⟩ : syracuseStep 18188171 = 27282257) B27282257
theorem B12125447 : Blo 1891435 12125447 := bstep (se 1 (by rfl) ⟨9094085, by rfl⟩ : syracuseStep 12125447 = 18188171) B18188171
theorem B8083631 : Blo 1891435 8083631 := bstep (se 1 (by rfl) ⟨6062723, by rfl⟩ : syracuseStep 8083631 = 12125447) B12125447
theorem B5389087 : Blo 1891435 5389087 := bstep (se 1 (by rfl) ⟨4041815, by rfl⟩ : syracuseStep 5389087 = 8083631) B8083631
theorem B7185449 : Blo 1891435 7185449 := bstep (se 2 (by rfl) ⟨2694543, by rfl⟩ : syracuseStep 7185449 = 5389087) B5389087
theorem B4790299 : Blo 1891435 4790299 := bstep (se 1 (by rfl) ⟨3592724, by rfl⟩ : syracuseStep 4790299 = 7185449) B7185449
theorem B6387065 : Blo 1891435 6387065 := bstep (se 2 (by rfl) ⟨2395149, by rfl⟩ : syracuseStep 6387065 = 4790299) B4790299
theorem B4258043 : Blo 1891435 4258043 := bstep (se 1 (by rfl) ⟨3193532, by rfl⟩ : syracuseStep 4258043 = 6387065) B6387065
theorem B2838695 : Blo 1891435 2838695 := bstep (se 1 (by rfl) ⟨2129021, by rfl⟩ : syracuseStep 2838695 = 4258043) B4258043
theorem B1892463 : Blo 1891435 1892463 := bstep (se 1 (by rfl) ⟨1419347, by rfl⟩ : syracuseStep 1892463 = 2838695) B2838695
theorem B2838701 : Blo 1891435 2838701 := bbase (se 3 (by rfl) ⟨532256, by rfl⟩ : syracuseStep 2838701 = 1064513) (by norm_num)
theorem B1892467 : Blo 1891435 1892467 := bstep (se 1 (by rfl) ⟨1419350, by rfl⟩ : syracuseStep 1892467 = 2838701) B2838701
theorem B4258061 : Blo 1891435 4258061 := bbase (se 3 (by rfl) ⟨798386, by rfl⟩ : syracuseStep 4258061 = 1596773) (by norm_num)
theorem B2838707 : Blo 1891435 2838707 := bstep (se 1 (by rfl) ⟨2129030, by rfl⟩ : syracuseStep 2838707 = 4258061) B4258061
theorem B1892471 : Blo 1891435 1892471 := bstep (se 1 (by rfl) ⟨1419353, by rfl⟩ : syracuseStep 1892471 = 2838707) B2838707
theorem B2395165 : Blo 1891435 2395165 := bbase (se 3 (by rfl) ⟨449093, by rfl⟩ : syracuseStep 2395165 = 898187) (by norm_num)
theorem B3193553 : Blo 1891435 3193553 := bstep (se 2 (by rfl) ⟨1197582, by rfl⟩ : syracuseStep 3193553 = 2395165) B2395165
theorem B2129035 : Blo 1891435 2129035 := bstep (se 1 (by rfl) ⟨1596776, by rfl⟩ : syracuseStep 2129035 = 3193553) B3193553
theorem B2838713 : Blo 1891435 2838713 := bstep (se 2 (by rfl) ⟨1064517, by rfl⟩ : syracuseStep 2838713 = 2129035) B2129035
theorem B1892475 : Blo 1891435 1892475 := bstep (se 1 (by rfl) ⟨1419356, by rfl⟩ : syracuseStep 1892475 = 2838713) B2838713
theorem B5754901 : Blo 1891435 5754901 := bbase (se 6 (by rfl) ⟨134880, by rfl⟩ : syracuseStep 5754901 = 269761) (by norm_num)
theorem B7673201 : Blo 1891435 7673201 := bstep (se 2 (by rfl) ⟨2877450, by rfl⟩ : syracuseStep 7673201 = 5754901) B5754901
theorem B5115467 : Blo 1891435 5115467 := bstep (se 1 (by rfl) ⟨3836600, by rfl⟩ : syracuseStep 5115467 = 7673201) B7673201
theorem B3410311 : Blo 1891435 3410311 := bstep (se 1 (by rfl) ⟨2557733, by rfl⟩ : syracuseStep 3410311 = 5115467) B5115467
theorem B4547081 : Blo 1891435 4547081 := bstep (se 2 (by rfl) ⟨1705155, by rfl⟩ : syracuseStep 4547081 = 3410311) B3410311
theorem B3031387 : Blo 1891435 3031387 := bstep (se 1 (by rfl) ⟨2273540, by rfl⟩ : syracuseStep 3031387 = 4547081) B4547081
theorem B16167397 : Blo 1891435 16167397 := bstep (se 4 (by rfl) ⟨1515693, by rfl⟩ : syracuseStep 16167397 = 3031387) B3031387
theorem B21556529 : Blo 1891435 21556529 := bstep (se 2 (by rfl) ⟨8083698, by rfl⟩ : syracuseStep 21556529 = 16167397) B16167397
theorem B14371019 : Blo 1891435 14371019 := bstep (se 1 (by rfl) ⟨10778264, by rfl⟩ : syracuseStep 14371019 = 21556529) B21556529
theorem B9580679 : Blo 1891435 9580679 := bstep (se 1 (by rfl) ⟨7185509, by rfl⟩ : syracuseStep 9580679 = 14371019) B14371019
theorem B6387119 : Blo 1891435 6387119 := bstep (se 1 (by rfl) ⟨4790339, by rfl⟩ : syracuseStep 6387119 = 9580679) B9580679
theorem B4258079 : Blo 1891435 4258079 := bstep (se 1 (by rfl) ⟨3193559, by rfl⟩ : syracuseStep 4258079 = 6387119) B6387119
theorem B2838719 : Blo 1891435 2838719 := bstep (se 1 (by rfl) ⟨2129039, by rfl⟩ : syracuseStep 2838719 = 4258079) B4258079
theorem B1892479 : Blo 1891435 1892479 := bstep (se 1 (by rfl) ⟨1419359, by rfl⟩ : syracuseStep 1892479 = 2838719) B2838719
theorem B2838725 : Blo 1891435 2838725 := bbase (se 4 (by rfl) ⟨266130, by rfl⟩ : syracuseStep 2838725 = 532261) (by norm_num)
theorem B1892483 : Blo 1891435 1892483 := bstep (se 1 (by rfl) ⟨1419362, by rfl⟩ : syracuseStep 1892483 = 2838725) B2838725
theorem B3193573 : Blo 1891435 3193573 := bbase (se 4 (by rfl) ⟨299397, by rfl⟩ : syracuseStep 3193573 = 598795) (by norm_num)
theorem B4258097 : Blo 1891435 4258097 := bstep (se 2 (by rfl) ⟨1596786, by rfl⟩ : syracuseStep 4258097 = 3193573) B3193573
theorem B2838731 : Blo 1891435 2838731 := bstep (se 1 (by rfl) ⟨2129048, by rfl⟩ : syracuseStep 2838731 = 4258097) B4258097
theorem B1892487 : Blo 1891435 1892487 := bstep (se 1 (by rfl) ⟨1419365, by rfl⟩ : syracuseStep 1892487 = 2838731) B2838731
theorem B2129053 : Blo 1891435 2129053 := bbase (se 3 (by rfl) ⟨399197, by rfl⟩ : syracuseStep 2129053 = 798395) (by norm_num)
theorem B2838737 : Blo 1891435 2838737 := bstep (se 2 (by rfl) ⟨1064526, by rfl⟩ : syracuseStep 2838737 = 2129053) B2129053
theorem B1892491 : Blo 1891435 1892491 := bstep (se 1 (by rfl) ⟨1419368, by rfl⟩ : syracuseStep 1892491 = 2838737) B2838737
theorem B6387173 : Blo 1891435 6387173 := bbase (se 4 (by rfl) ⟨598797, by rfl⟩ : syracuseStep 6387173 = 1197595) (by norm_num)
theorem B4258115 : Blo 1891435 4258115 := bstep (se 1 (by rfl) ⟨3193586, by rfl⟩ : syracuseStep 4258115 = 6387173) B6387173
theorem B2838743 : Blo 1891435 2838743 := bstep (se 1 (by rfl) ⟨2129057, by rfl⟩ : syracuseStep 2838743 = 4258115) B4258115
theorem B1892495 : Blo 1891435 1892495 := bstep (se 1 (by rfl) ⟨1419371, by rfl⟩ : syracuseStep 1892495 = 2838743) B2838743
theorem B2838749 : Blo 1891435 2838749 := bbase (se 3 (by rfl) ⟨532265, by rfl⟩ : syracuseStep 2838749 = 1064531) (by norm_num)
theorem B1892499 : Blo 1891435 1892499 := bstep (se 1 (by rfl) ⟨1419374, by rfl⟩ : syracuseStep 1892499 = 2838749) B2838749
theorem B4258133 : Blo 1891435 4258133 := bbase (se 10 (by rfl) ⟨6237, by rfl⟩ : syracuseStep 4258133 = 12475) (by norm_num)
theorem B2838755 : Blo 1891435 2838755 := bstep (se 1 (by rfl) ⟨2129066, by rfl⟩ : syracuseStep 2838755 = 4258133) B4258133
theorem B1892503 : Blo 1891435 1892503 := bstep (se 1 (by rfl) ⟨1419377, by rfl⟩ : syracuseStep 1892503 = 2838755) B2838755
theorem B2158121 : Blo 1891435 2158121 := bbase (se 2 (by rfl) ⟨809295, by rfl⟩ : syracuseStep 2158121 = 1618591) (by norm_num)
theorem B5754989 : Blo 1891435 5754989 := bstep (se 3 (by rfl) ⟨1079060, by rfl⟩ : syracuseStep 5754989 = 2158121) B2158121
theorem B3836659 : Blo 1891435 3836659 := bstep (se 1 (by rfl) ⟨2877494, by rfl⟩ : syracuseStep 3836659 = 5754989) B5754989
theorem B5115545 : Blo 1891435 5115545 := bstep (se 2 (by rfl) ⟨1918329, by rfl⟩ : syracuseStep 5115545 = 3836659) B3836659
theorem B3410363 : Blo 1891435 3410363 := bstep (se 1 (by rfl) ⟨2557772, by rfl⟩ : syracuseStep 3410363 = 5115545) B5115545
theorem B2273575 : Blo 1891435 2273575 := bstep (se 1 (by rfl) ⟨1705181, by rfl⟩ : syracuseStep 2273575 = 3410363) B3410363
theorem B3031433 : Blo 1891435 3031433 := bstep (se 2 (by rfl) ⟨1136787, by rfl⟩ : syracuseStep 3031433 = 2273575) B2273575
theorem B2020955 : Blo 1891435 2020955 := bstep (se 1 (by rfl) ⟨1515716, by rfl⟩ : syracuseStep 2020955 = 3031433) B3031433
theorem B5389213 : Blo 1891435 5389213 := bstep (se 3 (by rfl) ⟨1010477, by rfl⟩ : syracuseStep 5389213 = 2020955) B2020955
theorem B7185617 : Blo 1891435 7185617 := bstep (se 2 (by rfl) ⟨2694606, by rfl⟩ : syracuseStep 7185617 = 5389213) B5389213
theorem B4790411 : Blo 1891435 4790411 := bstep (se 1 (by rfl) ⟨3592808, by rfl⟩ : syracuseStep 4790411 = 7185617) B7185617
theorem B3193607 : Blo 1891435 3193607 := bstep (se 1 (by rfl) ⟨2395205, by rfl⟩ : syracuseStep 3193607 = 4790411) B4790411
theorem B2129071 : Blo 1891435 2129071 := bstep (se 1 (by rfl) ⟨1596803, by rfl⟩ : syracuseStep 2129071 = 3193607) B3193607
theorem B2838761 : Blo 1891435 2838761 := bstep (se 2 (by rfl) ⟨1064535, by rfl⟩ : syracuseStep 2838761 = 2129071) B2129071
theorem B1892507 : Blo 1891435 1892507 := bstep (se 1 (by rfl) ⟨1419380, by rfl⟩ : syracuseStep 1892507 = 2838761) B2838761
theorem B5754997 : Blo 1891435 5754997 := bbase (se 5 (by rfl) ⟨269765, by rfl⟩ : syracuseStep 5754997 = 539531) (by norm_num)
theorem B7673329 : Blo 1891435 7673329 := bstep (se 2 (by rfl) ⟨2877498, by rfl⟩ : syracuseStep 7673329 = 5754997) B5754997
theorem B10231105 : Blo 1891435 10231105 := bstep (se 2 (by rfl) ⟨3836664, by rfl⟩ : syracuseStep 10231105 = 7673329) B7673329
theorem B13641473 : Blo 1891435 13641473 := bstep (se 2 (by rfl) ⟨5115552, by rfl⟩ : syracuseStep 13641473 = 10231105) B10231105
theorem B36377261 : Blo 1891435 36377261 := bstep (se 3 (by rfl) ⟨6820736, by rfl⟩ : syracuseStep 36377261 = 13641473) B13641473
theorem B24251507 : Blo 1891435 24251507 := bstep (se 1 (by rfl) ⟨18188630, by rfl⟩ : syracuseStep 24251507 = 36377261) B36377261
theorem B16167671 : Blo 1891435 16167671 := bstep (se 1 (by rfl) ⟨12125753, by rfl⟩ : syracuseStep 16167671 = 24251507) B24251507
theorem B10778447 : Blo 1891435 10778447 := bstep (se 1 (by rfl) ⟨8083835, by rfl⟩ : syracuseStep 10778447 = 16167671) B16167671
theorem B7185631 : Blo 1891435 7185631 := bstep (se 1 (by rfl) ⟨5389223, by rfl⟩ : syracuseStep 7185631 = 10778447) B10778447
theorem B9580841 : Blo 1891435 9580841 := bstep (se 2 (by rfl) ⟨3592815, by rfl⟩ : syracuseStep 9580841 = 7185631) B7185631
theorem B6387227 : Blo 1891435 6387227 := bstep (se 1 (by rfl) ⟨4790420, by rfl⟩ : syracuseStep 6387227 = 9580841) B9580841
theorem B4258151 : Blo 1891435 4258151 := bstep (se 1 (by rfl) ⟨3193613, by rfl⟩ : syracuseStep 4258151 = 6387227) B6387227
theorem B2838767 : Blo 1891435 2838767 := bstep (se 1 (by rfl) ⟨2129075, by rfl⟩ : syracuseStep 2838767 = 4258151) B4258151
theorem B1892511 : Blo 1891435 1892511 := bstep (se 1 (by rfl) ⟨1419383, by rfl⟩ : syracuseStep 1892511 = 2838767) B2838767
theorem B2838773 : Blo 1891435 2838773 := bbase (se 5 (by rfl) ⟨133067, by rfl⟩ : syracuseStep 2838773 = 266135) (by norm_num)
theorem B1892515 : Blo 1891435 1892515 := bstep (se 1 (by rfl) ⟨1419386, by rfl⟩ : syracuseStep 1892515 = 2838773) B2838773
theorem B34530133 : Blo 1891435 34530133 := bbase (se 9 (by rfl) ⟨101162, by rfl⟩ : syracuseStep 34530133 = 202325) (by norm_num)
theorem B46040177 : Blo 1891435 46040177 := bstep (se 2 (by rfl) ⟨17265066, by rfl⟩ : syracuseStep 46040177 = 34530133) B34530133
theorem B30693451 : Blo 1891435 30693451 := bstep (se 1 (by rfl) ⟨23020088, by rfl⟩ : syracuseStep 30693451 = 46040177) B46040177
theorem B40924601 : Blo 1891435 40924601 := bstep (se 2 (by rfl) ⟨15346725, by rfl⟩ : syracuseStep 40924601 = 30693451) B30693451
theorem B27283067 : Blo 1891435 27283067 := bstep (se 1 (by rfl) ⟨20462300, by rfl⟩ : syracuseStep 27283067 = 40924601) B40924601
theorem B18188711 : Blo 1891435 18188711 := bstep (se 1 (by rfl) ⟨13641533, by rfl⟩ : syracuseStep 18188711 = 27283067) B27283067
theorem B12125807 : Blo 1891435 12125807 := bstep (se 1 (by rfl) ⟨9094355, by rfl⟩ : syracuseStep 12125807 = 18188711) B18188711
theorem B8083871 : Blo 1891435 8083871 := bstep (se 1 (by rfl) ⟨6062903, by rfl⟩ : syracuseStep 8083871 = 12125807) B12125807
theorem B5389247 : Blo 1891435 5389247 := bstep (se 1 (by rfl) ⟨4041935, by rfl⟩ : syracuseStep 5389247 = 8083871) B8083871
theorem B3592831 : Blo 1891435 3592831 := bstep (se 1 (by rfl) ⟨2694623, by rfl⟩ : syracuseStep 3592831 = 5389247) B5389247
theorem B4790441 : Blo 1891435 4790441 := bstep (se 2 (by rfl) ⟨1796415, by rfl⟩ : syracuseStep 4790441 = 3592831) B3592831
theorem B3193627 : Blo 1891435 3193627 := bstep (se 1 (by rfl) ⟨2395220, by rfl⟩ : syracuseStep 3193627 = 4790441) B4790441
theorem B4258169 : Blo 1891435 4258169 := bstep (se 2 (by rfl) ⟨1596813, by rfl⟩ : syracuseStep 4258169 = 3193627) B3193627
theorem B2838779 : Blo 1891435 2838779 := bstep (se 1 (by rfl) ⟨2129084, by rfl⟩ : syracuseStep 2838779 = 4258169) B4258169
theorem B1892519 : Blo 1891435 1892519 := bstep (se 1 (by rfl) ⟨1419389, by rfl⟩ : syracuseStep 1892519 = 2838779) B2838779
theorem B2129089 : Blo 1891435 2129089 := bbase (se 2 (by rfl) ⟨798408, by rfl⟩ : syracuseStep 2129089 = 1596817) (by norm_num)
theorem B2838785 : Blo 1891435 2838785 := bstep (se 2 (by rfl) ⟨1064544, by rfl⟩ : syracuseStep 2838785 = 2129089) B2129089
theorem B1892523 : Blo 1891435 1892523 := bstep (se 1 (by rfl) ⟨1419392, by rfl⟩ : syracuseStep 1892523 = 2838785) B2838785
theorem B4790461 : Blo 1891435 4790461 := bbase (se 3 (by rfl) ⟨898211, by rfl⟩ : syracuseStep 4790461 = 1796423) (by norm_num)
theorem B6387281 : Blo 1891435 6387281 := bstep (se 2 (by rfl) ⟨2395230, by rfl⟩ : syracuseStep 6387281 = 4790461) B4790461
theorem B4258187 : Blo 1891435 4258187 := bstep (se 1 (by rfl) ⟨3193640, by rfl⟩ : syracuseStep 4258187 = 6387281) B6387281
theorem B2838791 : Blo 1891435 2838791 := bstep (se 1 (by rfl) ⟨2129093, by rfl⟩ : syracuseStep 2838791 = 4258187) B4258187
theorem B1892527 : Blo 1891435 1892527 := bstep (se 1 (by rfl) ⟨1419395, by rfl⟩ : syracuseStep 1892527 = 2838791) B2838791
theorem B2838797 : Blo 1891435 2838797 := bbase (se 3 (by rfl) ⟨532274, by rfl⟩ : syracuseStep 2838797 = 1064549) (by norm_num)
theorem B1892531 : Blo 1891435 1892531 := bstep (se 1 (by rfl) ⟨1419398, by rfl⟩ : syracuseStep 1892531 = 2838797) B2838797
theorem B4258205 : Blo 1891435 4258205 := bbase (se 3 (by rfl) ⟨798413, by rfl⟩ : syracuseStep 4258205 = 1596827) (by norm_num)
theorem B2838803 : Blo 1891435 2838803 := bstep (se 1 (by rfl) ⟨2129102, by rfl⟩ : syracuseStep 2838803 = 4258205) B4258205
theorem B1892535 : Blo 1891435 1892535 := bstep (se 1 (by rfl) ⟨1419401, by rfl⟩ : syracuseStep 1892535 = 2838803) B2838803
theorem B3193661 : Blo 1891435 3193661 := bbase (se 3 (by rfl) ⟨598811, by rfl⟩ : syracuseStep 3193661 = 1197623) (by norm_num)
theorem B2129107 : Blo 1891435 2129107 := bstep (se 1 (by rfl) ⟨1596830, by rfl⟩ : syracuseStep 2129107 = 3193661) B3193661
theorem B2838809 : Blo 1891435 2838809 := bstep (se 2 (by rfl) ⟨1064553, by rfl⟩ : syracuseStep 2838809 = 2129107) B2129107
theorem B1892539 : Blo 1891435 1892539 := bstep (se 1 (by rfl) ⟨1419404, by rfl⟩ : syracuseStep 1892539 = 2838809) B2838809
theorem B2020993 : Blo 1891435 2020993 := bbase (se 2 (by rfl) ⟨757872, by rfl⟩ : syracuseStep 2020993 = 1515745) (by norm_num)
theorem B10778629 : Blo 1891435 10778629 := bstep (se 4 (by rfl) ⟨1010496, by rfl⟩ : syracuseStep 10778629 = 2020993) B2020993
theorem B14371505 : Blo 1891435 14371505 := bstep (se 2 (by rfl) ⟨5389314, by rfl⟩ : syracuseStep 14371505 = 10778629) B10778629
theorem B9581003 : Blo 1891435 9581003 := bstep (se 1 (by rfl) ⟨7185752, by rfl⟩ : syracuseStep 9581003 = 14371505) B14371505
theorem B6387335 : Blo 1891435 6387335 := bstep (se 1 (by rfl) ⟨4790501, by rfl⟩ : syracuseStep 6387335 = 9581003) B9581003
theorem B4258223 : Blo 1891435 4258223 := bstep (se 1 (by rfl) ⟨3193667, by rfl⟩ : syracuseStep 4258223 = 6387335) B6387335
theorem B2838815 : Blo 1891435 2838815 := bstep (se 1 (by rfl) ⟨2129111, by rfl⟩ : syracuseStep 2838815 = 4258223) B4258223
theorem B1892543 : Blo 1891435 1892543 := bstep (se 1 (by rfl) ⟨1419407, by rfl⟩ : syracuseStep 1892543 = 2838815) B2838815
theorem B2838821 : Blo 1891435 2838821 := bbase (se 4 (by rfl) ⟨266139, by rfl⟩ : syracuseStep 2838821 = 532279) (by norm_num)
theorem B1892547 : Blo 1891435 1892547 := bstep (se 1 (by rfl) ⟨1419410, by rfl⟩ : syracuseStep 1892547 = 2838821) B2838821
theorem B2395261 : Blo 1891435 2395261 := bbase (se 3 (by rfl) ⟨449111, by rfl⟩ : syracuseStep 2395261 = 898223) (by norm_num)
theorem B3193681 : Blo 1891435 3193681 := bstep (se 2 (by rfl) ⟨1197630, by rfl⟩ : syracuseStep 3193681 = 2395261) B2395261
theorem B4258241 : Blo 1891435 4258241 := bstep (se 2 (by rfl) ⟨1596840, by rfl⟩ : syracuseStep 4258241 = 3193681) B3193681
theorem B2838827 : Blo 1891435 2838827 := bstep (se 1 (by rfl) ⟨2129120, by rfl⟩ : syracuseStep 2838827 = 4258241) B4258241
theorem B1892551 : Blo 1891435 1892551 := bstep (se 1 (by rfl) ⟨1419413, by rfl⟩ : syracuseStep 1892551 = 2838827) B2838827
theorem B2129125 : Blo 1891435 2129125 := bbase (se 4 (by rfl) ⟨199605, by rfl⟩ : syracuseStep 2129125 = 399211) (by norm_num)
theorem B2838833 : Blo 1891435 2838833 := bstep (se 2 (by rfl) ⟨1064562, by rfl⟩ : syracuseStep 2838833 = 2129125) B2129125
theorem B1892555 : Blo 1891435 1892555 := bstep (se 1 (by rfl) ⟨1419416, by rfl⟩ : syracuseStep 1892555 = 2838833) B2838833
theorem B4042021 : Blo 1891435 4042021 := bbase (se 4 (by rfl) ⟨378939, by rfl⟩ : syracuseStep 4042021 = 757879) (by norm_num)
theorem B5389361 : Blo 1891435 5389361 := bstep (se 2 (by rfl) ⟨2021010, by rfl⟩ : syracuseStep 5389361 = 4042021) B4042021
theorem B3592907 : Blo 1891435 3592907 := bstep (se 1 (by rfl) ⟨2694680, by rfl⟩ : syracuseStep 3592907 = 5389361) B5389361
theorem B2395271 : Blo 1891435 2395271 := bstep (se 1 (by rfl) ⟨1796453, by rfl⟩ : syracuseStep 2395271 = 3592907) B3592907
theorem B6387389 : Blo 1891435 6387389 := bstep (se 3 (by rfl) ⟨1197635, by rfl⟩ : syracuseStep 6387389 = 2395271) B2395271
theorem B4258259 : Blo 1891435 4258259 := bstep (se 1 (by rfl) ⟨3193694, by rfl⟩ : syracuseStep 4258259 = 6387389) B6387389
theorem B2838839 : Blo 1891435 2838839 := bstep (se 1 (by rfl) ⟨2129129, by rfl⟩ : syracuseStep 2838839 = 4258259) B4258259
theorem B1892559 : Blo 1891435 1892559 := bstep (se 1 (by rfl) ⟨1419419, by rfl⟩ : syracuseStep 1892559 = 2838839) B2838839
theorem B2838845 : Blo 1891435 2838845 := bbase (se 3 (by rfl) ⟨532283, by rfl⟩ : syracuseStep 2838845 = 1064567) (by norm_num)
theorem B1892563 : Blo 1891435 1892563 := bstep (se 1 (by rfl) ⟨1419422, by rfl⟩ : syracuseStep 1892563 = 2838845) B2838845
theorem B4258277 : Blo 1891435 4258277 := bbase (se 4 (by rfl) ⟨399213, by rfl⟩ : syracuseStep 4258277 = 798427) (by norm_num)
theorem B2838851 : Blo 1891435 2838851 := bstep (se 1 (by rfl) ⟨2129138, by rfl⟩ : syracuseStep 2838851 = 4258277) B4258277
theorem B1892567 : Blo 1891435 1892567 := bstep (se 1 (by rfl) ⟨1419425, by rfl⟩ : syracuseStep 1892567 = 2838851) B2838851
theorem B4790573 : Blo 1891435 4790573 := bbase (se 3 (by rfl) ⟨898232, by rfl⟩ : syracuseStep 4790573 = 1796465) (by norm_num)
theorem B3193715 : Blo 1891435 3193715 := bstep (se 1 (by rfl) ⟨2395286, by rfl⟩ : syracuseStep 3193715 = 4790573) B4790573
theorem B2129143 : Blo 1891435 2129143 := bstep (se 1 (by rfl) ⟨1596857, by rfl⟩ : syracuseStep 2129143 = 3193715) B3193715
theorem B2838857 : Blo 1891435 2838857 := bstep (se 2 (by rfl) ⟨1064571, by rfl⟩ : syracuseStep 2838857 = 2129143) B2129143
theorem B1892571 : Blo 1891435 1892571 := bstep (se 1 (by rfl) ⟨1419428, by rfl⟩ : syracuseStep 1892571 = 2838857) B2838857
theorem B20742101 : Blo 1891435 20742101 := bbase (se 7 (by rfl) ⟨243071, by rfl⟩ : syracuseStep 20742101 = 486143) (by norm_num)
theorem B13828067 : Blo 1891435 13828067 := bstep (se 1 (by rfl) ⟨10371050, by rfl⟩ : syracuseStep 13828067 = 20742101) B20742101
theorem B9218711 : Blo 1891435 9218711 := bstep (se 1 (by rfl) ⟨6914033, by rfl⟩ : syracuseStep 9218711 = 13828067) B13828067
theorem B6145807 : Blo 1891435 6145807 := bstep (se 1 (by rfl) ⟨4609355, by rfl⟩ : syracuseStep 6145807 = 9218711) B9218711
theorem B8194409 : Blo 1891435 8194409 := bstep (se 2 (by rfl) ⟨3072903, by rfl⟩ : syracuseStep 8194409 = 6145807) B6145807
theorem B5462939 : Blo 1891435 5462939 := bstep (se 1 (by rfl) ⟨4097204, by rfl⟩ : syracuseStep 5462939 = 8194409) B8194409
theorem B3641959 : Blo 1891435 3641959 := bstep (se 1 (by rfl) ⟨2731469, by rfl⟩ : syracuseStep 3641959 = 5462939) B5462939
theorem B4855945 : Blo 1891435 4855945 := bstep (se 2 (by rfl) ⟨1820979, by rfl⟩ : syracuseStep 4855945 = 3641959) B3641959
theorem B6474593 : Blo 1891435 6474593 := bstep (se 2 (by rfl) ⟨2427972, by rfl⟩ : syracuseStep 6474593 = 4855945) B4855945
theorem B17265581 : Blo 1891435 17265581 := bstep (se 3 (by rfl) ⟨3237296, by rfl⟩ : syracuseStep 17265581 = 6474593) B6474593
theorem B11510387 : Blo 1891435 11510387 := bstep (se 1 (by rfl) ⟨8632790, by rfl⟩ : syracuseStep 11510387 = 17265581) B17265581
theorem B7673591 : Blo 1891435 7673591 := bstep (se 1 (by rfl) ⟨5755193, by rfl⟩ : syracuseStep 7673591 = 11510387) B11510387
theorem B5115727 : Blo 1891435 5115727 := bstep (se 1 (by rfl) ⟨3836795, by rfl⟩ : syracuseStep 5115727 = 7673591) B7673591
theorem B6820969 : Blo 1891435 6820969 := bstep (se 2 (by rfl) ⟨2557863, by rfl⟩ : syracuseStep 6820969 = 5115727) B5115727
theorem B9094625 : Blo 1891435 9094625 := bstep (se 2 (by rfl) ⟨3410484, by rfl⟩ : syracuseStep 9094625 = 6820969) B6820969
theorem B6063083 : Blo 1891435 6063083 := bstep (se 1 (by rfl) ⟨4547312, by rfl⟩ : syracuseStep 6063083 = 9094625) B9094625
theorem B4042055 : Blo 1891435 4042055 := bstep (se 1 (by rfl) ⟨3031541, by rfl⟩ : syracuseStep 4042055 = 6063083) B6063083
theorem B2694703 : Blo 1891435 2694703 := bstep (se 1 (by rfl) ⟨2021027, by rfl⟩ : syracuseStep 2694703 = 4042055) B4042055
theorem B3592937 : Blo 1891435 3592937 := bstep (se 2 (by rfl) ⟨1347351, by rfl⟩ : syracuseStep 3592937 = 2694703) B2694703
theorem B9581165 : Blo 1891435 9581165 := bstep (se 3 (by rfl) ⟨1796468, by rfl⟩ : syracuseStep 9581165 = 3592937) B3592937
theorem B6387443 : Blo 1891435 6387443 := bstep (se 1 (by rfl) ⟨4790582, by rfl⟩ : syracuseStep 6387443 = 9581165) B9581165
theorem B4258295 : Blo 1891435 4258295 := bstep (se 1 (by rfl) ⟨3193721, by rfl⟩ : syracuseStep 4258295 = 6387443) B6387443
theorem B2838863 : Blo 1891435 2838863 := bstep (se 1 (by rfl) ⟨2129147, by rfl⟩ : syracuseStep 2838863 = 4258295) B4258295
theorem B1892575 : Blo 1891435 1892575 := bstep (se 1 (by rfl) ⟨1419431, by rfl⟩ : syracuseStep 1892575 = 2838863) B2838863
theorem B2838869 : Blo 1891435 2838869 := bbase (se 10 (by rfl) ⟨4158, by rfl⟩ : syracuseStep 2838869 = 8317) (by norm_num)
theorem B1892579 : Blo 1891435 1892579 := bstep (se 1 (by rfl) ⟨1419434, by rfl⟩ : syracuseStep 1892579 = 2838869) B2838869
theorem B5389429 : Blo 1891435 5389429 := bbase (se 5 (by rfl) ⟨252629, by rfl⟩ : syracuseStep 5389429 = 505259) (by norm_num)
theorem B7185905 : Blo 1891435 7185905 := bstep (se 2 (by rfl) ⟨2694714, by rfl⟩ : syracuseStep 7185905 = 5389429) B5389429
theorem B4790603 : Blo 1891435 4790603 := bstep (se 1 (by rfl) ⟨3592952, by rfl⟩ : syracuseStep 4790603 = 7185905) B7185905
theorem B3193735 : Blo 1891435 3193735 := bstep (se 1 (by rfl) ⟨2395301, by rfl⟩ : syracuseStep 3193735 = 4790603) B4790603
theorem B4258313 : Blo 1891435 4258313 := bstep (se 2 (by rfl) ⟨1596867, by rfl⟩ : syracuseStep 4258313 = 3193735) B3193735
theorem B2838875 : Blo 1891435 2838875 := bstep (se 1 (by rfl) ⟨2129156, by rfl⟩ : syracuseStep 2838875 = 4258313) B4258313
theorem B1892583 : Blo 1891435 1892583 := bstep (se 1 (by rfl) ⟨1419437, by rfl⟩ : syracuseStep 1892583 = 2838875) B2838875
theorem B2129161 : Blo 1891435 2129161 := bbase (se 2 (by rfl) ⟨798435, by rfl⟩ : syracuseStep 2129161 = 1596871) (by norm_num)
theorem B2838881 : Blo 1891435 2838881 := bstep (se 2 (by rfl) ⟨1064580, by rfl⟩ : syracuseStep 2838881 = 2129161) B2129161
theorem B1892587 : Blo 1891435 1892587 := bstep (se 1 (by rfl) ⟨1419440, by rfl⟩ : syracuseStep 1892587 = 2838881) B2838881
theorem B2557885 : Blo 1891435 2557885 := bbase (se 3 (by rfl) ⟨479603, by rfl⟩ : syracuseStep 2557885 = 959207) (by norm_num)
theorem B3410513 : Blo 1891435 3410513 := bstep (se 2 (by rfl) ⟨1278942, by rfl⟩ : syracuseStep 3410513 = 2557885) B2557885
theorem B2273675 : Blo 1891435 2273675 := bstep (se 1 (by rfl) ⟨1705256, by rfl⟩ : syracuseStep 2273675 = 3410513) B3410513
theorem B24252533 : Blo 1891435 24252533 := bstep (se 5 (by rfl) ⟨1136837, by rfl⟩ : syracuseStep 24252533 = 2273675) B2273675
theorem B16168355 : Blo 1891435 16168355 := bstep (se 1 (by rfl) ⟨12126266, by rfl⟩ : syracuseStep 16168355 = 24252533) B24252533
theorem B10778903 : Blo 1891435 10778903 := bstep (se 1 (by rfl) ⟨8084177, by rfl⟩ : syracuseStep 10778903 = 16168355) B16168355
theorem B7185935 : Blo 1891435 7185935 := bstep (se 1 (by rfl) ⟨5389451, by rfl⟩ : syracuseStep 7185935 = 10778903) B10778903
theorem B4790623 : Blo 1891435 4790623 := bstep (se 1 (by rfl) ⟨3592967, by rfl⟩ : syracuseStep 4790623 = 7185935) B7185935
theorem B6387497 : Blo 1891435 6387497 := bstep (se 2 (by rfl) ⟨2395311, by rfl⟩ : syracuseStep 6387497 = 4790623) B4790623
theorem B4258331 : Blo 1891435 4258331 := bstep (se 1 (by rfl) ⟨3193748, by rfl⟩ : syracuseStep 4258331 = 6387497) B6387497
theorem B2838887 : Blo 1891435 2838887 := bstep (se 1 (by rfl) ⟨2129165, by rfl⟩ : syracuseStep 2838887 = 4258331) B4258331
theorem B1892591 : Blo 1891435 1892591 := bstep (se 1 (by rfl) ⟨1419443, by rfl⟩ : syracuseStep 1892591 = 2838887) B2838887
theorem B2838893 : Blo 1891435 2838893 := bbase (se 3 (by rfl) ⟨532292, by rfl⟩ : syracuseStep 2838893 = 1064585) (by norm_num)
theorem B1892595 : Blo 1891435 1892595 := bstep (se 1 (by rfl) ⟨1419446, by rfl⟩ : syracuseStep 1892595 = 2838893) B2838893
theorem B4258349 : Blo 1891435 4258349 := bbase (se 3 (by rfl) ⟨798440, by rfl⟩ : syracuseStep 4258349 = 1596881) (by norm_num)
theorem B2838899 : Blo 1891435 2838899 := bstep (se 1 (by rfl) ⟨2129174, by rfl⟩ : syracuseStep 2838899 = 4258349) B4258349
theorem B1892599 : Blo 1891435 1892599 := bstep (se 1 (by rfl) ⟨1419449, by rfl⟩ : syracuseStep 1892599 = 2838899) B2838899
theorem B3642013 : Blo 1891435 3642013 := bbase (se 3 (by rfl) ⟨682877, by rfl⟩ : syracuseStep 3642013 = 1365755) (by norm_num)
theorem B19424069 : Blo 1891435 19424069 := bstep (se 4 (by rfl) ⟨1821006, by rfl⟩ : syracuseStep 19424069 = 3642013) B3642013
theorem B12949379 : Blo 1891435 12949379 := bstep (se 1 (by rfl) ⟨9712034, by rfl⟩ : syracuseStep 12949379 = 19424069) B19424069
theorem B8632919 : Blo 1891435 8632919 := bstep (se 1 (by rfl) ⟨6474689, by rfl⟩ : syracuseStep 8632919 = 12949379) B12949379
theorem B5755279 : Blo 1891435 5755279 := bstep (se 1 (by rfl) ⟨4316459, by rfl⟩ : syracuseStep 5755279 = 8632919) B8632919
theorem B7673705 : Blo 1891435 7673705 := bstep (se 2 (by rfl) ⟨2877639, by rfl⟩ : syracuseStep 7673705 = 5755279) B5755279
theorem B5115803 : Blo 1891435 5115803 := bstep (se 1 (by rfl) ⟨3836852, by rfl⟩ : syracuseStep 5115803 = 7673705) B7673705
theorem B13642141 : Blo 1891435 13642141 := bstep (se 3 (by rfl) ⟨2557901, by rfl⟩ : syracuseStep 13642141 = 5115803) B5115803
theorem B18189521 : Blo 1891435 18189521 := bstep (se 2 (by rfl) ⟨6821070, by rfl⟩ : syracuseStep 18189521 = 13642141) B13642141
theorem B12126347 : Blo 1891435 12126347 := bstep (se 1 (by rfl) ⟨9094760, by rfl⟩ : syracuseStep 12126347 = 18189521) B18189521
theorem B8084231 : Blo 1891435 8084231 := bstep (se 1 (by rfl) ⟨6063173, by rfl⟩ : syracuseStep 8084231 = 12126347) B12126347
theorem B5389487 : Blo 1891435 5389487 := bstep (se 1 (by rfl) ⟨4042115, by rfl⟩ : syracuseStep 5389487 = 8084231) B8084231
theorem B3592991 : Blo 1891435 3592991 := bstep (se 1 (by rfl) ⟨2694743, by rfl⟩ : syracuseStep 3592991 = 5389487) B5389487
theorem B2395327 : Blo 1891435 2395327 := bstep (se 1 (by rfl) ⟨1796495, by rfl⟩ : syracuseStep 2395327 = 3592991) B3592991
theorem B3193769 : Blo 1891435 3193769 := bstep (se 2 (by rfl) ⟨1197663, by rfl⟩ : syracuseStep 3193769 = 2395327) B2395327
theorem B2129179 : Blo 1891435 2129179 := bstep (se 1 (by rfl) ⟨1596884, by rfl⟩ : syracuseStep 2129179 = 3193769) B3193769
theorem B2838905 : Blo 1891435 2838905 := bstep (se 2 (by rfl) ⟨1064589, by rfl⟩ : syracuseStep 2838905 = 2129179) B2129179
theorem B1892603 : Blo 1891435 1892603 := bstep (se 1 (by rfl) ⟨1419452, by rfl⟩ : syracuseStep 1892603 = 2838905) B2838905
theorem B32336981 : Blo 1891435 32336981 := bbase (se 8 (by rfl) ⟨189474, by rfl⟩ : syracuseStep 32336981 = 378949) (by norm_num)
theorem B21557987 : Blo 1891435 21557987 := bstep (se 1 (by rfl) ⟨16168490, by rfl⟩ : syracuseStep 21557987 = 32336981) B32336981
theorem B14371991 : Blo 1891435 14371991 := bstep (se 1 (by rfl) ⟨10778993, by rfl⟩ : syracuseStep 14371991 = 21557987) B21557987
theorem B9581327 : Blo 1891435 9581327 := bstep (se 1 (by rfl) ⟨7185995, by rfl⟩ : syracuseStep 9581327 = 14371991) B14371991
theorem B6387551 : Blo 1891435 6387551 := bstep (se 1 (by rfl) ⟨4790663, by rfl⟩ : syracuseStep 6387551 = 9581327) B9581327
theorem B4258367 : Blo 1891435 4258367 := bstep (se 1 (by rfl) ⟨3193775, by rfl⟩ : syracuseStep 4258367 = 6387551) B6387551
theorem B2838911 : Blo 1891435 2838911 := bstep (se 1 (by rfl) ⟨2129183, by rfl⟩ : syracuseStep 2838911 = 4258367) B4258367
theorem B1892607 : Blo 1891435 1892607 := bstep (se 1 (by rfl) ⟨1419455, by rfl⟩ : syracuseStep 1892607 = 2838911) B2838911
theorem B2838917 : Blo 1891435 2838917 := bbase (se 4 (by rfl) ⟨266148, by rfl⟩ : syracuseStep 2838917 = 532297) (by norm_num)
theorem B1892611 : Blo 1891435 1892611 := bstep (se 1 (by rfl) ⟨1419458, by rfl⟩ : syracuseStep 1892611 = 2838917) B2838917
theorem B3193789 : Blo 1891435 3193789 := bbase (se 3 (by rfl) ⟨598835, by rfl⟩ : syracuseStep 3193789 = 1197671) (by norm_num)
theorem B4258385 : Blo 1891435 4258385 := bstep (se 2 (by rfl) ⟨1596894, by rfl⟩ : syracuseStep 4258385 = 3193789) B3193789
theorem B2838923 : Blo 1891435 2838923 := bstep (se 1 (by rfl) ⟨2129192, by rfl⟩ : syracuseStep 2838923 = 4258385) B4258385
theorem B1892615 : Blo 1891435 1892615 := bstep (se 1 (by rfl) ⟨1419461, by rfl⟩ : syracuseStep 1892615 = 2838923) B2838923
theorem B2129197 : Blo 1891435 2129197 := bbase (se 3 (by rfl) ⟨399224, by rfl⟩ : syracuseStep 2129197 = 798449) (by norm_num)
theorem B2838929 : Blo 1891435 2838929 := bstep (se 2 (by rfl) ⟨1064598, by rfl⟩ : syracuseStep 2838929 = 2129197) B2129197
theorem B1892619 : Blo 1891435 1892619 := bstep (se 1 (by rfl) ⟨1419464, by rfl⟩ : syracuseStep 1892619 = 2838929) B2838929
theorem B6387605 : Blo 1891435 6387605 := bbase (se 6 (by rfl) ⟨149709, by rfl⟩ : syracuseStep 6387605 = 299419) (by norm_num)
theorem B4258403 : Blo 1891435 4258403 := bstep (se 1 (by rfl) ⟨3193802, by rfl⟩ : syracuseStep 4258403 = 6387605) B6387605
theorem B2838935 : Blo 1891435 2838935 := bstep (se 1 (by rfl) ⟨2129201, by rfl⟩ : syracuseStep 2838935 = 4258403) B4258403
theorem B1892623 : Blo 1891435 1892623 := bstep (se 1 (by rfl) ⟨1419467, by rfl⟩ : syracuseStep 1892623 = 2838935) B2838935
theorem B2838941 : Blo 1891435 2838941 := bbase (se 3 (by rfl) ⟨532301, by rfl⟩ : syracuseStep 2838941 = 1064603) (by norm_num)
theorem B1892627 : Blo 1891435 1892627 := bstep (se 1 (by rfl) ⟨1419470, by rfl⟩ : syracuseStep 1892627 = 2838941) B2838941
theorem B4258421 : Blo 1891435 4258421 := bbase (se 5 (by rfl) ⟨199613, by rfl⟩ : syracuseStep 4258421 = 399227) (by norm_num)
theorem B2838947 : Blo 1891435 2838947 := bstep (se 1 (by rfl) ⟨2129210, by rfl⟩ : syracuseStep 2838947 = 4258421) B4258421
theorem B1892631 : Blo 1891435 1892631 := bstep (se 1 (by rfl) ⟨1419473, by rfl⟩ : syracuseStep 1892631 = 2838947) B2838947
theorem B3836917 : Blo 1891435 3836917 := bbase (se 5 (by rfl) ⟨179855, by rfl⟩ : syracuseStep 3836917 = 359711) (by norm_num)
theorem B5115889 : Blo 1891435 5115889 := bstep (se 2 (by rfl) ⟨1918458, by rfl⟩ : syracuseStep 5115889 = 3836917) B3836917
theorem B6821185 : Blo 1891435 6821185 := bstep (se 2 (by rfl) ⟨2557944, by rfl⟩ : syracuseStep 6821185 = 5115889) B5115889
theorem B9094913 : Blo 1891435 9094913 := bstep (se 2 (by rfl) ⟨3410592, by rfl⟩ : syracuseStep 9094913 = 6821185) B6821185
theorem B6063275 : Blo 1891435 6063275 := bstep (se 1 (by rfl) ⟨4547456, by rfl⟩ : syracuseStep 6063275 = 9094913) B9094913
theorem B16168733 : Blo 1891435 16168733 := bstep (se 3 (by rfl) ⟨3031637, by rfl⟩ : syracuseStep 16168733 = 6063275) B6063275
theorem B10779155 : Blo 1891435 10779155 := bstep (se 1 (by rfl) ⟨8084366, by rfl⟩ : syracuseStep 10779155 = 16168733) B16168733
theorem B7186103 : Blo 1891435 7186103 := bstep (se 1 (by rfl) ⟨5389577, by rfl⟩ : syracuseStep 7186103 = 10779155) B10779155
theorem B4790735 : Blo 1891435 4790735 := bstep (se 1 (by rfl) ⟨3593051, by rfl⟩ : syracuseStep 4790735 = 7186103) B7186103
theorem B3193823 : Blo 1891435 3193823 := bstep (se 1 (by rfl) ⟨2395367, by rfl⟩ : syracuseStep 3193823 = 4790735) B4790735
theorem B2129215 : Blo 1891435 2129215 := bstep (se 1 (by rfl) ⟨1596911, by rfl⟩ : syracuseStep 2129215 = 3193823) B3193823
theorem B2838953 : Blo 1891435 2838953 := bstep (se 2 (by rfl) ⟨1064607, by rfl⟩ : syracuseStep 2838953 = 2129215) B2129215
theorem B1892635 : Blo 1891435 1892635 := bstep (se 1 (by rfl) ⟨1419476, by rfl⟩ : syracuseStep 1892635 = 2838953) B2838953
theorem B7186117 : Blo 1891435 7186117 := bbase (se 4 (by rfl) ⟨673698, by rfl⟩ : syracuseStep 7186117 = 1347397) (by norm_num)
theorem B9581489 : Blo 1891435 9581489 := bstep (se 2 (by rfl) ⟨3593058, by rfl⟩ : syracuseStep 9581489 = 7186117) B7186117
theorem B6387659 : Blo 1891435 6387659 := bstep (se 1 (by rfl) ⟨4790744, by rfl⟩ : syracuseStep 6387659 = 9581489) B9581489
theorem B4258439 : Blo 1891435 4258439 := bstep (se 1 (by rfl) ⟨3193829, by rfl⟩ : syracuseStep 4258439 = 6387659) B6387659
theorem B2838959 : Blo 1891435 2838959 := bstep (se 1 (by rfl) ⟨2129219, by rfl⟩ : syracuseStep 2838959 = 4258439) B4258439
theorem B1892639 : Blo 1891435 1892639 := bstep (se 1 (by rfl) ⟨1419479, by rfl⟩ : syracuseStep 1892639 = 2838959) B2838959
theorem B2838965 : Blo 1891435 2838965 := bbase (se 5 (by rfl) ⟨133076, by rfl⟩ : syracuseStep 2838965 = 266153) (by norm_num)
theorem B1892643 : Blo 1891435 1892643 := bstep (se 1 (by rfl) ⟨1419482, by rfl⟩ : syracuseStep 1892643 = 2838965) B2838965
theorem B4790765 : Blo 1891435 4790765 := bbase (se 3 (by rfl) ⟨898268, by rfl⟩ : syracuseStep 4790765 = 1796537) (by norm_num)
theorem B3193843 : Blo 1891435 3193843 := bstep (se 1 (by rfl) ⟨2395382, by rfl⟩ : syracuseStep 3193843 = 4790765) B4790765
theorem B4258457 : Blo 1891435 4258457 := bstep (se 2 (by rfl) ⟨1596921, by rfl⟩ : syracuseStep 4258457 = 3193843) B3193843
theorem B2838971 : Blo 1891435 2838971 := bstep (se 1 (by rfl) ⟨2129228, by rfl⟩ : syracuseStep 2838971 = 4258457) B4258457
theorem B1892647 : Blo 1891435 1892647 := bstep (se 1 (by rfl) ⟨1419485, by rfl⟩ : syracuseStep 1892647 = 2838971) B2838971
theorem B2129233 : Blo 1891435 2129233 := bbase (se 2 (by rfl) ⟨798462, by rfl⟩ : syracuseStep 2129233 = 1596925) (by norm_num)
theorem B2838977 : Blo 1891435 2838977 := bstep (se 2 (by rfl) ⟨1064616, by rfl⟩ : syracuseStep 2838977 = 2129233) B2129233
theorem B1892651 : Blo 1891435 1892651 := bstep (se 1 (by rfl) ⟨1419488, by rfl⟩ : syracuseStep 1892651 = 2838977) B2838977
theorem B2021113 : Blo 1891435 2021113 := bbase (se 2 (by rfl) ⟨757917, by rfl⟩ : syracuseStep 2021113 = 1515835) (by norm_num)
theorem B2694817 : Blo 1891435 2694817 := bstep (se 2 (by rfl) ⟨1010556, by rfl⟩ : syracuseStep 2694817 = 2021113) B2021113
theorem B3593089 : Blo 1891435 3593089 := bstep (se 2 (by rfl) ⟨1347408, by rfl⟩ : syracuseStep 3593089 = 2694817) B2694817
theorem B4790785 : Blo 1891435 4790785 := bstep (se 2 (by rfl) ⟨1796544, by rfl⟩ : syracuseStep 4790785 = 3593089) B3593089
theorem B6387713 : Blo 1891435 6387713 := bstep (se 2 (by rfl) ⟨2395392, by rfl⟩ : syracuseStep 6387713 = 4790785) B4790785
theorem B4258475 : Blo 1891435 4258475 := bstep (se 1 (by rfl) ⟨3193856, by rfl⟩ : syracuseStep 4258475 = 6387713) B6387713
theorem B2838983 : Blo 1891435 2838983 := bstep (se 1 (by rfl) ⟨2129237, by rfl⟩ : syracuseStep 2838983 = 4258475) B4258475
theorem B1892655 : Blo 1891435 1892655 := bstep (se 1 (by rfl) ⟨1419491, by rfl⟩ : syracuseStep 1892655 = 2838983) B2838983
theorem B2838989 : Blo 1891435 2838989 := bbase (se 3 (by rfl) ⟨532310, by rfl⟩ : syracuseStep 2838989 = 1064621) (by norm_num)
theorem B1892659 : Blo 1891435 1892659 := bstep (se 1 (by rfl) ⟨1419494, by rfl⟩ : syracuseStep 1892659 = 2838989) B2838989
theorem B4258493 : Blo 1891435 4258493 := bbase (se 3 (by rfl) ⟨798467, by rfl⟩ : syracuseStep 4258493 = 1596935) (by norm_num)
theorem B2838995 : Blo 1891435 2838995 := bstep (se 1 (by rfl) ⟨2129246, by rfl⟩ : syracuseStep 2838995 = 4258493) B4258493
theorem B1892663 : Blo 1891435 1892663 := bstep (se 1 (by rfl) ⟨1419497, by rfl⟩ : syracuseStep 1892663 = 2838995) B2838995
theorem B3193877 : Blo 1891435 3193877 := bbase (se 6 (by rfl) ⟨74856, by rfl⟩ : syracuseStep 3193877 = 149713) (by norm_num)
theorem B2129251 : Blo 1891435 2129251 := bstep (se 1 (by rfl) ⟨1596938, by rfl⟩ : syracuseStep 2129251 = 3193877) B3193877
theorem B2839001 : Blo 1891435 2839001 := bstep (se 2 (by rfl) ⟨1064625, by rfl⟩ : syracuseStep 2839001 = 2129251) B2129251
theorem B1892667 : Blo 1891435 1892667 := bstep (se 1 (by rfl) ⟨1419500, by rfl⟩ : syracuseStep 1892667 = 2839001) B2839001
theorem B3836989 : Blo 1891435 3836989 := bbase (se 3 (by rfl) ⟨719435, by rfl⟩ : syracuseStep 3836989 = 1438871) (by norm_num)
theorem B20463941 : Blo 1891435 20463941 := bstep (se 4 (by rfl) ⟨1918494, by rfl⟩ : syracuseStep 20463941 = 3836989) B3836989
theorem B13642627 : Blo 1891435 13642627 := bstep (se 1 (by rfl) ⟨10231970, by rfl⟩ : syracuseStep 13642627 = 20463941) B20463941
theorem B18190169 : Blo 1891435 18190169 := bstep (se 2 (by rfl) ⟨6821313, by rfl⟩ : syracuseStep 18190169 = 13642627) B13642627
theorem B12126779 : Blo 1891435 12126779 := bstep (se 1 (by rfl) ⟨9095084, by rfl⟩ : syracuseStep 12126779 = 18190169) B18190169
theorem B8084519 : Blo 1891435 8084519 := bstep (se 1 (by rfl) ⟨6063389, by rfl⟩ : syracuseStep 8084519 = 12126779) B12126779
theorem B5389679 : Blo 1891435 5389679 := bstep (se 1 (by rfl) ⟨4042259, by rfl⟩ : syracuseStep 5389679 = 8084519) B8084519
theorem B14372477 : Blo 1891435 14372477 := bstep (se 3 (by rfl) ⟨2694839, by rfl⟩ : syracuseStep 14372477 = 5389679) B5389679
theorem B9581651 : Blo 1891435 9581651 := bstep (se 1 (by rfl) ⟨7186238, by rfl⟩ : syracuseStep 9581651 = 14372477) B14372477
theorem B6387767 : Blo 1891435 6387767 := bstep (se 1 (by rfl) ⟨4790825, by rfl⟩ : syracuseStep 6387767 = 9581651) B9581651
theorem B4258511 : Blo 1891435 4258511 := bstep (se 1 (by rfl) ⟨3193883, by rfl⟩ : syracuseStep 4258511 = 6387767) B6387767
theorem B2839007 : Blo 1891435 2839007 := bstep (se 1 (by rfl) ⟨2129255, by rfl⟩ : syracuseStep 2839007 = 4258511) B4258511
theorem B1892671 : Blo 1891435 1892671 := bstep (se 1 (by rfl) ⟨1419503, by rfl⟩ : syracuseStep 1892671 = 2839007) B2839007
theorem B2839013 : Blo 1891435 2839013 := bbase (se 4 (by rfl) ⟨266157, by rfl⟩ : syracuseStep 2839013 = 532315) (by norm_num)
theorem B1892675 : Blo 1891435 1892675 := bstep (se 1 (by rfl) ⟨1419506, by rfl⟩ : syracuseStep 1892675 = 2839013) B2839013
theorem B9095125 : Blo 1891435 9095125 := bbase (se 7 (by rfl) ⟨106583, by rfl⟩ : syracuseStep 9095125 = 213167) (by norm_num)
theorem B12126833 : Blo 1891435 12126833 := bstep (se 2 (by rfl) ⟨4547562, by rfl⟩ : syracuseStep 12126833 = 9095125) B9095125
theorem B8084555 : Blo 1891435 8084555 := bstep (se 1 (by rfl) ⟨6063416, by rfl⟩ : syracuseStep 8084555 = 12126833) B12126833
theorem B5389703 : Blo 1891435 5389703 := bstep (se 1 (by rfl) ⟨4042277, by rfl⟩ : syracuseStep 5389703 = 8084555) B8084555
theorem B3593135 : Blo 1891435 3593135 := bstep (se 1 (by rfl) ⟨2694851, by rfl⟩ : syracuseStep 3593135 = 5389703) B5389703
theorem B2395423 : Blo 1891435 2395423 := bstep (se 1 (by rfl) ⟨1796567, by rfl⟩ : syracuseStep 2395423 = 3593135) B3593135
theorem B3193897 : Blo 1891435 3193897 := bstep (se 2 (by rfl) ⟨1197711, by rfl⟩ : syracuseStep 3193897 = 2395423) B2395423
theorem B4258529 : Blo 1891435 4258529 := bstep (se 2 (by rfl) ⟨1596948, by rfl⟩ : syracuseStep 4258529 = 3193897) B3193897
theorem B2839019 : Blo 1891435 2839019 := bstep (se 1 (by rfl) ⟨2129264, by rfl⟩ : syracuseStep 2839019 = 4258529) B4258529
theorem B1892679 : Blo 1891435 1892679 := bstep (se 1 (by rfl) ⟨1419509, by rfl⟩ : syracuseStep 1892679 = 2839019) B2839019
theorem B2129269 : Blo 1891435 2129269 := bbase (se 5 (by rfl) ⟨99809, by rfl⟩ : syracuseStep 2129269 = 199619) (by norm_num)
theorem B2839025 : Blo 1891435 2839025 := bstep (se 2 (by rfl) ⟨1064634, by rfl⟩ : syracuseStep 2839025 = 2129269) B2129269
theorem B1892683 : Blo 1891435 1892683 := bstep (se 1 (by rfl) ⟨1419512, by rfl⟩ : syracuseStep 1892683 = 2839025) B2839025
theorem B2395433 : Blo 1891435 2395433 := bbase (se 2 (by rfl) ⟨898287, by rfl⟩ : syracuseStep 2395433 = 1796575) (by norm_num)
theorem B6387821 : Blo 1891435 6387821 := bstep (se 3 (by rfl) ⟨1197716, by rfl⟩ : syracuseStep 6387821 = 2395433) B2395433
theorem B4258547 : Blo 1891435 4258547 := bstep (se 1 (by rfl) ⟨3193910, by rfl⟩ : syracuseStep 4258547 = 6387821) B6387821
theorem B2839031 : Blo 1891435 2839031 := bstep (se 1 (by rfl) ⟨2129273, by rfl⟩ : syracuseStep 2839031 = 4258547) B4258547
theorem B1892687 : Blo 1891435 1892687 := bstep (se 1 (by rfl) ⟨1419515, by rfl⟩ : syracuseStep 1892687 = 2839031) B2839031
theorem B2839037 : Blo 1891435 2839037 := bbase (se 3 (by rfl) ⟨532319, by rfl⟩ : syracuseStep 2839037 = 1064639) (by norm_num)
theorem B1892691 : Blo 1891435 1892691 := bstep (se 1 (by rfl) ⟨1419518, by rfl⟩ : syracuseStep 1892691 = 2839037) B2839037
theorem B4258565 : Blo 1891435 4258565 := bbase (se 4 (by rfl) ⟨399240, by rfl⟩ : syracuseStep 4258565 = 798481) (by norm_num)
theorem B2839043 : Blo 1891435 2839043 := bstep (se 1 (by rfl) ⟨2129282, by rfl⟩ : syracuseStep 2839043 = 4258565) B4258565
theorem B1892695 : Blo 1891435 1892695 := bstep (se 1 (by rfl) ⟨1419521, by rfl⟩ : syracuseStep 1892695 = 2839043) B2839043
theorem B3593173 : Blo 1891435 3593173 := bbase (se 7 (by rfl) ⟨42107, by rfl⟩ : syracuseStep 3593173 = 84215) (by norm_num)
theorem B4790897 : Blo 1891435 4790897 := bstep (se 2 (by rfl) ⟨1796586, by rfl⟩ : syracuseStep 4790897 = 3593173) B3593173
theorem B3193931 : Blo 1891435 3193931 := bstep (se 1 (by rfl) ⟨2395448, by rfl⟩ : syracuseStep 3193931 = 4790897) B4790897
theorem B2129287 : Blo 1891435 2129287 := bstep (se 1 (by rfl) ⟨1596965, by rfl⟩ : syracuseStep 2129287 = 3193931) B3193931
theorem B2839049 : Blo 1891435 2839049 := bstep (se 2 (by rfl) ⟨1064643, by rfl⟩ : syracuseStep 2839049 = 2129287) B2129287
theorem B1892699 : Blo 1891435 1892699 := bstep (se 1 (by rfl) ⟨1419524, by rfl⟩ : syracuseStep 1892699 = 2839049) B2839049
theorem B9581813 : Blo 1891435 9581813 := bbase (se 5 (by rfl) ⟨449147, by rfl⟩ : syracuseStep 9581813 = 898295) (by norm_num)
theorem B6387875 : Blo 1891435 6387875 := bstep (se 1 (by rfl) ⟨4790906, by rfl⟩ : syracuseStep 6387875 = 9581813) B9581813
theorem B4258583 : Blo 1891435 4258583 := bstep (se 1 (by rfl) ⟨3193937, by rfl⟩ : syracuseStep 4258583 = 6387875) B6387875
theorem B2839055 : Blo 1891435 2839055 := bstep (se 1 (by rfl) ⟨2129291, by rfl⟩ : syracuseStep 2839055 = 4258583) B4258583
theorem B1892703 : Blo 1891435 1892703 := bstep (se 1 (by rfl) ⟨1419527, by rfl⟩ : syracuseStep 1892703 = 2839055) B2839055
theorem B2839061 : Blo 1891435 2839061 := bbase (se 6 (by rfl) ⟨66540, by rfl⟩ : syracuseStep 2839061 = 133081) (by norm_num)
theorem B1892707 : Blo 1891435 1892707 := bstep (se 1 (by rfl) ⟨1419530, by rfl⟩ : syracuseStep 1892707 = 2839061) B2839061
theorem B3642221 : Blo 1891435 3642221 := bbase (se 3 (by rfl) ⟨682916, by rfl⟩ : syracuseStep 3642221 = 1365833) (by norm_num)
theorem B2428147 : Blo 1891435 2428147 := bstep (se 1 (by rfl) ⟨1821110, by rfl⟩ : syracuseStep 2428147 = 3642221) B3642221
theorem B12950117 : Blo 1891435 12950117 := bstep (se 4 (by rfl) ⟨1214073, by rfl⟩ : syracuseStep 12950117 = 2428147) B2428147
theorem B8633411 : Blo 1891435 8633411 := bstep (se 1 (by rfl) ⟨6475058, by rfl⟩ : syracuseStep 8633411 = 12950117) B12950117
theorem B5755607 : Blo 1891435 5755607 := bstep (se 1 (by rfl) ⟨4316705, by rfl⟩ : syracuseStep 5755607 = 8633411) B8633411
theorem B3837071 : Blo 1891435 3837071 := bstep (se 1 (by rfl) ⟨2877803, by rfl⟩ : syracuseStep 3837071 = 5755607) B5755607
theorem B10232189 : Blo 1891435 10232189 := bstep (se 3 (by rfl) ⟨1918535, by rfl⟩ : syracuseStep 10232189 = 3837071) B3837071
theorem B6821459 : Blo 1891435 6821459 := bstep (se 1 (by rfl) ⟨5116094, by rfl⟩ : syracuseStep 6821459 = 10232189) B10232189
theorem B4547639 : Blo 1891435 4547639 := bstep (se 1 (by rfl) ⟨3410729, by rfl⟩ : syracuseStep 4547639 = 6821459) B6821459
theorem B3031759 : Blo 1891435 3031759 := bstep (se 1 (by rfl) ⟨2273819, by rfl⟩ : syracuseStep 3031759 = 4547639) B4547639
theorem B16169381 : Blo 1891435 16169381 := bstep (se 4 (by rfl) ⟨1515879, by rfl⟩ : syracuseStep 16169381 = 3031759) B3031759
theorem B10779587 : Blo 1891435 10779587 := bstep (se 1 (by rfl) ⟨8084690, by rfl⟩ : syracuseStep 10779587 = 16169381) B16169381
theorem B7186391 : Blo 1891435 7186391 := bstep (se 1 (by rfl) ⟨5389793, by rfl⟩ : syracuseStep 7186391 = 10779587) B10779587
theorem B4790927 : Blo 1891435 4790927 := bstep (se 1 (by rfl) ⟨3593195, by rfl⟩ : syracuseStep 4790927 = 7186391) B7186391
theorem B3193951 : Blo 1891435 3193951 := bstep (se 1 (by rfl) ⟨2395463, by rfl⟩ : syracuseStep 3193951 = 4790927) B4790927
theorem B4258601 : Blo 1891435 4258601 := bstep (se 2 (by rfl) ⟨1596975, by rfl⟩ : syracuseStep 4258601 = 3193951) B3193951
theorem B2839067 : Blo 1891435 2839067 := bstep (se 1 (by rfl) ⟨2129300, by rfl⟩ : syracuseStep 2839067 = 4258601) B4258601
theorem B1892711 : Blo 1891435 1892711 := bstep (se 1 (by rfl) ⟨1419533, by rfl⟩ : syracuseStep 1892711 = 2839067) B2839067
theorem B2129305 : Blo 1891435 2129305 := bbase (se 2 (by rfl) ⟨798489, by rfl⟩ : syracuseStep 2129305 = 1596979) (by norm_num)
theorem B2839073 : Blo 1891435 2839073 := bstep (se 2 (by rfl) ⟨1064652, by rfl⟩ : syracuseStep 2839073 = 2129305) B2129305
theorem B1892715 : Blo 1891435 1892715 := bstep (se 1 (by rfl) ⟨1419536, by rfl⟩ : syracuseStep 1892715 = 2839073) B2839073
theorem B7186421 : Blo 1891435 7186421 := bbase (se 5 (by rfl) ⟨336863, by rfl⟩ : syracuseStep 7186421 = 673727) (by norm_num)
theorem B4790947 : Blo 1891435 4790947 := bstep (se 1 (by rfl) ⟨3593210, by rfl⟩ : syracuseStep 4790947 = 7186421) B7186421
theorem B6387929 : Blo 1891435 6387929 := bstep (se 2 (by rfl) ⟨2395473, by rfl⟩ : syracuseStep 6387929 = 4790947) B4790947
theorem B4258619 : Blo 1891435 4258619 := bstep (se 1 (by rfl) ⟨3193964, by rfl⟩ : syracuseStep 4258619 = 6387929) B6387929
theorem B2839079 : Blo 1891435 2839079 := bstep (se 1 (by rfl) ⟨2129309, by rfl⟩ : syracuseStep 2839079 = 4258619) B4258619
theorem B1892719 : Blo 1891435 1892719 := bstep (se 1 (by rfl) ⟨1419539, by rfl⟩ : syracuseStep 1892719 = 2839079) B2839079
theorem B2839085 : Blo 1891435 2839085 := bbase (se 3 (by rfl) ⟨532328, by rfl⟩ : syracuseStep 2839085 = 1064657) (by norm_num)
theorem B1892723 : Blo 1891435 1892723 := bstep (se 1 (by rfl) ⟨1419542, by rfl⟩ : syracuseStep 1892723 = 2839085) B2839085
theorem B4258637 : Blo 1891435 4258637 := bbase (se 3 (by rfl) ⟨798494, by rfl⟩ : syracuseStep 4258637 = 1596989) (by norm_num)
theorem B2839091 : Blo 1891435 2839091 := bstep (se 1 (by rfl) ⟨2129318, by rfl⟩ : syracuseStep 2839091 = 4258637) B4258637
theorem B1892727 : Blo 1891435 1892727 := bstep (se 1 (by rfl) ⟨1419545, by rfl⟩ : syracuseStep 1892727 = 2839091) B2839091
theorem B2395489 : Blo 1891435 2395489 := bbase (se 2 (by rfl) ⟨898308, by rfl⟩ : syracuseStep 2395489 = 1796617) (by norm_num)
theorem B3193985 : Blo 1891435 3193985 := bstep (se 2 (by rfl) ⟨1197744, by rfl⟩ : syracuseStep 3193985 = 2395489) B2395489
theorem B2129323 : Blo 1891435 2129323 := bstep (se 1 (by rfl) ⟨1596992, by rfl⟩ : syracuseStep 2129323 = 3193985) B3193985
theorem B2839097 : Blo 1891435 2839097 := bstep (se 2 (by rfl) ⟨1064661, by rfl⟩ : syracuseStep 2839097 = 2129323) B2129323
theorem B1892731 : Blo 1891435 1892731 := bstep (se 1 (by rfl) ⟨1419548, by rfl⟩ : syracuseStep 1892731 = 2839097) B2839097
theorem B21559445 : Blo 1891435 21559445 := bbase (se 6 (by rfl) ⟨505299, by rfl⟩ : syracuseStep 21559445 = 1010599) (by norm_num)
theorem B14372963 : Blo 1891435 14372963 := bstep (se 1 (by rfl) ⟨10779722, by rfl⟩ : syracuseStep 14372963 = 21559445) B21559445
theorem B9581975 : Blo 1891435 9581975 := bstep (se 1 (by rfl) ⟨7186481, by rfl⟩ : syracuseStep 9581975 = 14372963) B14372963
theorem B6387983 : Blo 1891435 6387983 := bstep (se 1 (by rfl) ⟨4790987, by rfl⟩ : syracuseStep 6387983 = 9581975) B9581975
theorem B4258655 : Blo 1891435 4258655 := bstep (se 1 (by rfl) ⟨3193991, by rfl⟩ : syracuseStep 4258655 = 6387983) B6387983
theorem B2839103 : Blo 1891435 2839103 := bstep (se 1 (by rfl) ⟨2129327, by rfl⟩ : syracuseStep 2839103 = 4258655) B4258655
theorem B1892735 : Blo 1891435 1892735 := bstep (se 1 (by rfl) ⟨1419551, by rfl⟩ : syracuseStep 1892735 = 2839103) B2839103
theorem B2839109 : Blo 1891435 2839109 := bbase (se 4 (by rfl) ⟨266166, by rfl⟩ : syracuseStep 2839109 = 532333) (by norm_num)
theorem B1892739 : Blo 1891435 1892739 := bstep (se 1 (by rfl) ⟨1419554, by rfl⟩ : syracuseStep 1892739 = 2839109) B2839109
theorem B3194005 : Blo 1891435 3194005 := bbase (se 6 (by rfl) ⟨74859, by rfl⟩ : syracuseStep 3194005 = 149719) (by norm_num)
theorem B4258673 : Blo 1891435 4258673 := bstep (se 2 (by rfl) ⟨1597002, by rfl⟩ : syracuseStep 4258673 = 3194005) B3194005
theorem B2839115 : Blo 1891435 2839115 := bstep (se 1 (by rfl) ⟨2129336, by rfl⟩ : syracuseStep 2839115 = 4258673) B4258673
theorem B1892743 : Blo 1891435 1892743 := bstep (se 1 (by rfl) ⟨1419557, by rfl⟩ : syracuseStep 1892743 = 2839115) B2839115
theorem B2129341 : Blo 1891435 2129341 := bbase (se 3 (by rfl) ⟨399251, by rfl⟩ : syracuseStep 2129341 = 798503) (by norm_num)
theorem B2839121 : Blo 1891435 2839121 := bstep (se 2 (by rfl) ⟨1064670, by rfl⟩ : syracuseStep 2839121 = 2129341) B2129341
theorem B1892747 : Blo 1891435 1892747 := bstep (se 1 (by rfl) ⟨1419560, by rfl⟩ : syracuseStep 1892747 = 2839121) B2839121
theorem B6388037 : Blo 1891435 6388037 := bbase (se 4 (by rfl) ⟨598878, by rfl⟩ : syracuseStep 6388037 = 1197757) (by norm_num)
theorem B4258691 : Blo 1891435 4258691 := bstep (se 1 (by rfl) ⟨3194018, by rfl⟩ : syracuseStep 4258691 = 6388037) B6388037
theorem B2839127 : Blo 1891435 2839127 := bstep (se 1 (by rfl) ⟨2129345, by rfl⟩ : syracuseStep 2839127 = 4258691) B4258691
theorem B1892751 : Blo 1891435 1892751 := bstep (se 1 (by rfl) ⟨1419563, by rfl⟩ : syracuseStep 1892751 = 2839127) B2839127
theorem B2839133 : Blo 1891435 2839133 := bbase (se 3 (by rfl) ⟨532337, by rfl⟩ : syracuseStep 2839133 = 1064675) (by norm_num)
theorem B1892755 : Blo 1891435 1892755 := bstep (se 1 (by rfl) ⟨1419566, by rfl⟩ : syracuseStep 1892755 = 2839133) B2839133
theorem B4258709 : Blo 1891435 4258709 := bbase (se 6 (by rfl) ⟨99813, by rfl⟩ : syracuseStep 4258709 = 199627) (by norm_num)
theorem B2839139 : Blo 1891435 2839139 := bstep (se 1 (by rfl) ⟨2129354, by rfl⟩ : syracuseStep 2839139 = 4258709) B4258709
theorem B1892759 : Blo 1891435 1892759 := bstep (se 1 (by rfl) ⟨1419569, by rfl⟩ : syracuseStep 1892759 = 2839139) B2839139
theorem B4547765 : Blo 1891435 4547765 := bbase (se 5 (by rfl) ⟨213176, by rfl⟩ : syracuseStep 4547765 = 426353) (by norm_num)
theorem B3031843 : Blo 1891435 3031843 := bstep (se 1 (by rfl) ⟨2273882, by rfl⟩ : syracuseStep 3031843 = 4547765) B4547765
theorem B4042457 : Blo 1891435 4042457 := bstep (se 2 (by rfl) ⟨1515921, by rfl⟩ : syracuseStep 4042457 = 3031843) B3031843
theorem B2694971 : Blo 1891435 2694971 := bstep (se 1 (by rfl) ⟨2021228, by rfl⟩ : syracuseStep 2694971 = 4042457) B4042457
theorem B7186589 : Blo 1891435 7186589 := bstep (se 3 (by rfl) ⟨1347485, by rfl⟩ : syracuseStep 7186589 = 2694971) B2694971
theorem B4791059 : Blo 1891435 4791059 := bstep (se 1 (by rfl) ⟨3593294, by rfl⟩ : syracuseStep 4791059 = 7186589) B7186589
theorem B3194039 : Blo 1891435 3194039 := bstep (se 1 (by rfl) ⟨2395529, by rfl⟩ : syracuseStep 3194039 = 4791059) B4791059
theorem B2129359 : Blo 1891435 2129359 := bstep (se 1 (by rfl) ⟨1597019, by rfl⟩ : syracuseStep 2129359 = 3194039) B3194039
theorem B2839145 : Blo 1891435 2839145 := bstep (se 2 (by rfl) ⟨1064679, by rfl⟩ : syracuseStep 2839145 = 2129359) B2129359
theorem B1892763 : Blo 1891435 1892763 := bstep (se 1 (by rfl) ⟨1419572, by rfl⟩ : syracuseStep 1892763 = 2839145) B2839145
theorem B4547773 : Blo 1891435 4547773 := bbase (se 3 (by rfl) ⟨852707, by rfl⟩ : syracuseStep 4547773 = 1705415) (by norm_num)
theorem B6063697 : Blo 1891435 6063697 := bstep (se 2 (by rfl) ⟨2273886, by rfl⟩ : syracuseStep 6063697 = 4547773) B4547773
theorem B8084929 : Blo 1891435 8084929 := bstep (se 2 (by rfl) ⟨3031848, by rfl⟩ : syracuseStep 8084929 = 6063697) B6063697
theorem B10779905 : Blo 1891435 10779905 := bstep (se 2 (by rfl) ⟨4042464, by rfl⟩ : syracuseStep 10779905 = 8084929) B8084929
theorem B7186603 : Blo 1891435 7186603 := bstep (se 1 (by rfl) ⟨5389952, by rfl⟩ : syracuseStep 7186603 = 10779905) B10779905
theorem B9582137 : Blo 1891435 9582137 := bstep (se 2 (by rfl) ⟨3593301, by rfl⟩ : syracuseStep 9582137 = 7186603) B7186603
theorem B6388091 : Blo 1891435 6388091 := bstep (se 1 (by rfl) ⟨4791068, by rfl⟩ : syracuseStep 6388091 = 9582137) B9582137
theorem B4258727 : Blo 1891435 4258727 := bstep (se 1 (by rfl) ⟨3194045, by rfl⟩ : syracuseStep 4258727 = 6388091) B6388091
theorem B2839151 : Blo 1891435 2839151 := bstep (se 1 (by rfl) ⟨2129363, by rfl⟩ : syracuseStep 2839151 = 4258727) B4258727
theorem B1892767 : Blo 1891435 1892767 := bstep (se 1 (by rfl) ⟨1419575, by rfl⟩ : syracuseStep 1892767 = 2839151) B2839151
theorem B2839157 : Blo 1891435 2839157 := bbase (se 5 (by rfl) ⟨133085, by rfl⟩ : syracuseStep 2839157 = 266171) (by norm_num)
theorem B1892771 : Blo 1891435 1892771 := bstep (se 1 (by rfl) ⟨1419578, by rfl⟩ : syracuseStep 1892771 = 2839157) B2839157
theorem B3593317 : Blo 1891435 3593317 := bbase (se 4 (by rfl) ⟨336873, by rfl⟩ : syracuseStep 3593317 = 673747) (by norm_num)
theorem B4791089 : Blo 1891435 4791089 := bstep (se 2 (by rfl) ⟨1796658, by rfl⟩ : syracuseStep 4791089 = 3593317) B3593317
theorem B3194059 : Blo 1891435 3194059 := bstep (se 1 (by rfl) ⟨2395544, by rfl⟩ : syracuseStep 3194059 = 4791089) B4791089
theorem B4258745 : Blo 1891435 4258745 := bstep (se 2 (by rfl) ⟨1597029, by rfl⟩ : syracuseStep 4258745 = 3194059) B3194059
theorem B2839163 : Blo 1891435 2839163 := bstep (se 1 (by rfl) ⟨2129372, by rfl⟩ : syracuseStep 2839163 = 4258745) B4258745
theorem B1892775 : Blo 1891435 1892775 := bstep (se 1 (by rfl) ⟨1419581, by rfl⟩ : syracuseStep 1892775 = 2839163) B2839163
theorem B2129377 : Blo 1891435 2129377 := bbase (se 2 (by rfl) ⟨798516, by rfl⟩ : syracuseStep 2129377 = 1597033) (by norm_num)
theorem B2839169 : Blo 1891435 2839169 := bstep (se 2 (by rfl) ⟨1064688, by rfl⟩ : syracuseStep 2839169 = 2129377) B2129377
theorem B1892779 : Blo 1891435 1892779 := bstep (se 1 (by rfl) ⟨1419584, by rfl⟩ : syracuseStep 1892779 = 2839169) B2839169
theorem B4791109 : Blo 1891435 4791109 := bbase (se 4 (by rfl) ⟨449166, by rfl⟩ : syracuseStep 4791109 = 898333) (by norm_num)
theorem B6388145 : Blo 1891435 6388145 := bstep (se 2 (by rfl) ⟨2395554, by rfl⟩ : syracuseStep 6388145 = 4791109) B4791109
theorem B4258763 : Blo 1891435 4258763 := bstep (se 1 (by rfl) ⟨3194072, by rfl⟩ : syracuseStep 4258763 = 6388145) B6388145
theorem B2839175 : Blo 1891435 2839175 := bstep (se 1 (by rfl) ⟨2129381, by rfl⟩ : syracuseStep 2839175 = 4258763) B4258763
theorem B1892783 : Blo 1891435 1892783 := bstep (se 1 (by rfl) ⟨1419587, by rfl⟩ : syracuseStep 1892783 = 2839175) B2839175
theorem B2839181 : Blo 1891435 2839181 := bbase (se 3 (by rfl) ⟨532346, by rfl⟩ : syracuseStep 2839181 = 1064693) (by norm_num)
theorem B1892787 : Blo 1891435 1892787 := bstep (se 1 (by rfl) ⟨1419590, by rfl⟩ : syracuseStep 1892787 = 2839181) B2839181
theorem B4258781 : Blo 1891435 4258781 := bbase (se 3 (by rfl) ⟨798521, by rfl⟩ : syracuseStep 4258781 = 1597043) (by norm_num)
theorem B2839187 : Blo 1891435 2839187 := bstep (se 1 (by rfl) ⟨2129390, by rfl⟩ : syracuseStep 2839187 = 4258781) B4258781
theorem B1892791 : Blo 1891435 1892791 := bstep (se 1 (by rfl) ⟨1419593, by rfl⟩ : syracuseStep 1892791 = 2839187) B2839187
theorem B3194093 : Blo 1891435 3194093 := bbase (se 3 (by rfl) ⟨598892, by rfl⟩ : syracuseStep 3194093 = 1197785) (by norm_num)
theorem B2129395 : Blo 1891435 2129395 := bstep (se 1 (by rfl) ⟨1597046, by rfl⟩ : syracuseStep 2129395 = 3194093) B3194093
theorem B2839193 : Blo 1891435 2839193 := bstep (se 2 (by rfl) ⟨1064697, by rfl⟩ : syracuseStep 2839193 = 2129395) B2129395
theorem B1892795 : Blo 1891435 1892795 := bstep (se 1 (by rfl) ⟨1419596, by rfl⟩ : syracuseStep 1892795 = 2839193) B2839193
theorem B6146533 : Blo 1891435 6146533 := bbase (se 4 (by rfl) ⟨576237, by rfl⟩ : syracuseStep 6146533 = 1152475) (by norm_num)
theorem B8195377 : Blo 1891435 8195377 := bstep (se 2 (by rfl) ⟨3073266, by rfl⟩ : syracuseStep 8195377 = 6146533) B6146533
theorem B10927169 : Blo 1891435 10927169 := bstep (se 2 (by rfl) ⟨4097688, by rfl⟩ : syracuseStep 10927169 = 8195377) B8195377
theorem B7284779 : Blo 1891435 7284779 := bstep (se 1 (by rfl) ⟨5463584, by rfl⟩ : syracuseStep 7284779 = 10927169) B10927169
theorem B4856519 : Blo 1891435 4856519 := bstep (se 1 (by rfl) ⟨3642389, by rfl⟩ : syracuseStep 4856519 = 7284779) B7284779
theorem B3237679 : Blo 1891435 3237679 := bstep (se 1 (by rfl) ⟨2428259, by rfl⟩ : syracuseStep 3237679 = 4856519) B4856519
theorem B4316905 : Blo 1891435 4316905 := bstep (se 2 (by rfl) ⟨1618839, by rfl⟩ : syracuseStep 4316905 = 3237679) B3237679
theorem B5755873 : Blo 1891435 5755873 := bstep (se 2 (by rfl) ⟨2158452, by rfl⟩ : syracuseStep 5755873 = 4316905) B4316905
theorem B7674497 : Blo 1891435 7674497 := bstep (se 2 (by rfl) ⟨2877936, by rfl⟩ : syracuseStep 7674497 = 5755873) B5755873
theorem B5116331 : Blo 1891435 5116331 := bstep (se 1 (by rfl) ⟨3837248, by rfl⟩ : syracuseStep 5116331 = 7674497) B7674497
theorem B13643549 : Blo 1891435 13643549 := bstep (se 3 (by rfl) ⟨2558165, by rfl⟩ : syracuseStep 13643549 = 5116331) B5116331
theorem B9095699 : Blo 1891435 9095699 := bstep (se 1 (by rfl) ⟨6821774, by rfl⟩ : syracuseStep 9095699 = 13643549) B13643549
theorem B24255197 : Blo 1891435 24255197 := bstep (se 3 (by rfl) ⟨4547849, by rfl⟩ : syracuseStep 24255197 = 9095699) B9095699
theorem B16170131 : Blo 1891435 16170131 := bstep (se 1 (by rfl) ⟨12127598, by rfl⟩ : syracuseStep 16170131 = 24255197) B24255197
theorem B10780087 : Blo 1891435 10780087 := bstep (se 1 (by rfl) ⟨8085065, by rfl⟩ : syracuseStep 10780087 = 16170131) B16170131
theorem B14373449 : Blo 1891435 14373449 := bstep (se 2 (by rfl) ⟨5390043, by rfl⟩ : syracuseStep 14373449 = 10780087) B10780087
theorem B9582299 : Blo 1891435 9582299 := bstep (se 1 (by rfl) ⟨7186724, by rfl⟩ : syracuseStep 9582299 = 14373449) B14373449
theorem B6388199 : Blo 1891435 6388199 := bstep (se 1 (by rfl) ⟨4791149, by rfl⟩ : syracuseStep 6388199 = 9582299) B9582299
theorem B4258799 : Blo 1891435 4258799 := bstep (se 1 (by rfl) ⟨3194099, by rfl⟩ : syracuseStep 4258799 = 6388199) B6388199
theorem B2839199 : Blo 1891435 2839199 := bstep (se 1 (by rfl) ⟨2129399, by rfl⟩ : syracuseStep 2839199 = 4258799) B4258799
theorem B1892799 : Blo 1891435 1892799 := bstep (se 1 (by rfl) ⟨1419599, by rfl⟩ : syracuseStep 1892799 = 2839199) B2839199
theorem B2839205 : Blo 1891435 2839205 := bbase (se 4 (by rfl) ⟨266175, by rfl⟩ : syracuseStep 2839205 = 532351) (by norm_num)
theorem B1892803 : Blo 1891435 1892803 := bstep (se 1 (by rfl) ⟨1419602, by rfl⟩ : syracuseStep 1892803 = 2839205) B2839205
theorem B2395585 : Blo 1891435 2395585 := bbase (se 2 (by rfl) ⟨898344, by rfl⟩ : syracuseStep 2395585 = 1796689) (by norm_num)
theorem B3194113 : Blo 1891435 3194113 := bstep (se 2 (by rfl) ⟨1197792, by rfl⟩ : syracuseStep 3194113 = 2395585) B2395585
theorem B4258817 : Blo 1891435 4258817 := bstep (se 2 (by rfl) ⟨1597056, by rfl⟩ : syracuseStep 4258817 = 3194113) B3194113
theorem B2839211 : Blo 1891435 2839211 := bstep (se 1 (by rfl) ⟨2129408, by rfl⟩ : syracuseStep 2839211 = 4258817) B4258817
theorem B1892807 : Blo 1891435 1892807 := bstep (se 1 (by rfl) ⟨1419605, by rfl⟩ : syracuseStep 1892807 = 2839211) B2839211
theorem B2129413 : Blo 1891435 2129413 := bbase (se 4 (by rfl) ⟨199632, by rfl⟩ : syracuseStep 2129413 = 399265) (by norm_num)
theorem B2839217 : Blo 1891435 2839217 := bstep (se 2 (by rfl) ⟨1064706, by rfl⟩ : syracuseStep 2839217 = 2129413) B2129413
theorem B1892811 : Blo 1891435 1892811 := bstep (se 1 (by rfl) ⟨1419608, by rfl⟩ : syracuseStep 1892811 = 2839217) B2839217
theorem B2695045 : Blo 1891435 2695045 := bbase (se 4 (by rfl) ⟨252660, by rfl⟩ : syracuseStep 2695045 = 505321) (by norm_num)
theorem B3593393 : Blo 1891435 3593393 := bstep (se 2 (by rfl) ⟨1347522, by rfl⟩ : syracuseStep 3593393 = 2695045) B2695045
theorem B2395595 : Blo 1891435 2395595 := bstep (se 1 (by rfl) ⟨1796696, by rfl⟩ : syracuseStep 2395595 = 3593393) B3593393
theorem B6388253 : Blo 1891435 6388253 := bstep (se 3 (by rfl) ⟨1197797, by rfl⟩ : syracuseStep 6388253 = 2395595) B2395595
theorem B4258835 : Blo 1891435 4258835 := bstep (se 1 (by rfl) ⟨3194126, by rfl⟩ : syracuseStep 4258835 = 6388253) B6388253
theorem B2839223 : Blo 1891435 2839223 := bstep (se 1 (by rfl) ⟨2129417, by rfl⟩ : syracuseStep 2839223 = 4258835) B4258835
theorem B1892815 : Blo 1891435 1892815 := bstep (se 1 (by rfl) ⟨1419611, by rfl⟩ : syracuseStep 1892815 = 2839223) B2839223
theorem B2839229 : Blo 1891435 2839229 := bbase (se 3 (by rfl) ⟨532355, by rfl⟩ : syracuseStep 2839229 = 1064711) (by norm_num)
theorem B1892819 : Blo 1891435 1892819 := bstep (se 1 (by rfl) ⟨1419614, by rfl⟩ : syracuseStep 1892819 = 2839229) B2839229
theorem B4258853 : Blo 1891435 4258853 := bbase (se 4 (by rfl) ⟨399267, by rfl⟩ : syracuseStep 4258853 = 798535) (by norm_num)
theorem B2839235 : Blo 1891435 2839235 := bstep (se 1 (by rfl) ⟨2129426, by rfl⟩ : syracuseStep 2839235 = 4258853) B4258853
theorem B1892823 : Blo 1891435 1892823 := bstep (se 1 (by rfl) ⟨1419617, by rfl⟩ : syracuseStep 1892823 = 2839235) B2839235
theorem B4791221 : Blo 1891435 4791221 := bbase (se 5 (by rfl) ⟨224588, by rfl⟩ : syracuseStep 4791221 = 449177) (by norm_num)
theorem B3194147 : Blo 1891435 3194147 := bstep (se 1 (by rfl) ⟨2395610, by rfl⟩ : syracuseStep 3194147 = 4791221) B4791221
theorem B2129431 : Blo 1891435 2129431 := bstep (se 1 (by rfl) ⟨1597073, by rfl⟩ : syracuseStep 2129431 = 3194147) B3194147
theorem B2839241 : Blo 1891435 2839241 := bstep (se 2 (by rfl) ⟨1064715, by rfl⟩ : syracuseStep 2839241 = 2129431) B2129431
theorem B1892827 : Blo 1891435 1892827 := bstep (se 1 (by rfl) ⟨1419620, by rfl⟩ : syracuseStep 1892827 = 2839241) B2839241
theorem B1918657 : Blo 1891435 1918657 := bbase (se 2 (by rfl) ⟨719496, by rfl⟩ : syracuseStep 1918657 = 1438993) (by norm_num)
theorem B10232837 : Blo 1891435 10232837 := bstep (se 4 (by rfl) ⟨959328, by rfl⟩ : syracuseStep 10232837 = 1918657) B1918657
theorem B6821891 : Blo 1891435 6821891 := bstep (se 1 (by rfl) ⟨5116418, by rfl⟩ : syracuseStep 6821891 = 10232837) B10232837
theorem B4547927 : Blo 1891435 4547927 := bstep (se 1 (by rfl) ⟨3410945, by rfl⟩ : syracuseStep 4547927 = 6821891) B6821891
theorem B12127805 : Blo 1891435 12127805 := bstep (se 3 (by rfl) ⟨2273963, by rfl⟩ : syracuseStep 12127805 = 4547927) B4547927
theorem B8085203 : Blo 1891435 8085203 := bstep (se 1 (by rfl) ⟨6063902, by rfl⟩ : syracuseStep 8085203 = 12127805) B12127805
theorem B5390135 : Blo 1891435 5390135 := bstep (se 1 (by rfl) ⟨4042601, by rfl⟩ : syracuseStep 5390135 = 8085203) B8085203
theorem B3593423 : Blo 1891435 3593423 := bstep (se 1 (by rfl) ⟨2695067, by rfl⟩ : syracuseStep 3593423 = 5390135) B5390135
theorem B9582461 : Blo 1891435 9582461 := bstep (se 3 (by rfl) ⟨1796711, by rfl⟩ : syracuseStep 9582461 = 3593423) B3593423
theorem B6388307 : Blo 1891435 6388307 := bstep (se 1 (by rfl) ⟨4791230, by rfl⟩ : syracuseStep 6388307 = 9582461) B9582461
theorem B4258871 : Blo 1891435 4258871 := bstep (se 1 (by rfl) ⟨3194153, by rfl⟩ : syracuseStep 4258871 = 6388307) B6388307
theorem B2839247 : Blo 1891435 2839247 := bstep (se 1 (by rfl) ⟨2129435, by rfl⟩ : syracuseStep 2839247 = 4258871) B4258871
theorem B1892831 : Blo 1891435 1892831 := bstep (se 1 (by rfl) ⟨1419623, by rfl⟩ : syracuseStep 1892831 = 2839247) B2839247
theorem B2839253 : Blo 1891435 2839253 := bbase (se 7 (by rfl) ⟨33272, by rfl⟩ : syracuseStep 2839253 = 66545) (by norm_num)
theorem B1892835 : Blo 1891435 1892835 := bstep (se 1 (by rfl) ⟨1419626, by rfl⟩ : syracuseStep 1892835 = 2839253) B2839253
theorem B3237749 : Blo 1891435 3237749 := bbase (se 5 (by rfl) ⟨151769, by rfl⟩ : syracuseStep 3237749 = 303539) (by norm_num)
theorem B2158499 : Blo 1891435 2158499 := bstep (se 1 (by rfl) ⟨1618874, by rfl⟩ : syracuseStep 2158499 = 3237749) B3237749
theorem B5755997 : Blo 1891435 5755997 := bstep (se 3 (by rfl) ⟨1079249, by rfl⟩ : syracuseStep 5755997 = 2158499) B2158499
theorem B3837331 : Blo 1891435 3837331 := bstep (se 1 (by rfl) ⟨2877998, by rfl⟩ : syracuseStep 3837331 = 5755997) B5755997
theorem B5116441 : Blo 1891435 5116441 := bstep (se 2 (by rfl) ⟨1918665, by rfl⟩ : syracuseStep 5116441 = 3837331) B3837331
theorem B6821921 : Blo 1891435 6821921 := bstep (se 2 (by rfl) ⟨2558220, by rfl⟩ : syracuseStep 6821921 = 5116441) B5116441
theorem B4547947 : Blo 1891435 4547947 := bstep (se 1 (by rfl) ⟨3410960, by rfl⟩ : syracuseStep 4547947 = 6821921) B6821921
theorem B6063929 : Blo 1891435 6063929 := bstep (se 2 (by rfl) ⟨2273973, by rfl⟩ : syracuseStep 6063929 = 4547947) B4547947
theorem B4042619 : Blo 1891435 4042619 := bstep (se 1 (by rfl) ⟨3031964, by rfl⟩ : syracuseStep 4042619 = 6063929) B6063929
theorem B2695079 : Blo 1891435 2695079 := bstep (se 1 (by rfl) ⟨2021309, by rfl⟩ : syracuseStep 2695079 = 4042619) B4042619
theorem B7186877 : Blo 1891435 7186877 := bstep (se 3 (by rfl) ⟨1347539, by rfl⟩ : syracuseStep 7186877 = 2695079) B2695079
theorem B4791251 : Blo 1891435 4791251 := bstep (se 1 (by rfl) ⟨3593438, by rfl⟩ : syracuseStep 4791251 = 7186877) B7186877
theorem B3194167 : Blo 1891435 3194167 := bstep (se 1 (by rfl) ⟨2395625, by rfl⟩ : syracuseStep 3194167 = 4791251) B4791251
theorem B4258889 : Blo 1891435 4258889 := bstep (se 2 (by rfl) ⟨1597083, by rfl⟩ : syracuseStep 4258889 = 3194167) B3194167
theorem B2839259 : Blo 1891435 2839259 := bstep (se 1 (by rfl) ⟨2129444, by rfl⟩ : syracuseStep 2839259 = 4258889) B4258889
theorem B1892839 : Blo 1891435 1892839 := bstep (se 1 (by rfl) ⟨1419629, by rfl⟩ : syracuseStep 1892839 = 2839259) B2839259
theorem B2129449 : Blo 1891435 2129449 := bbase (se 2 (by rfl) ⟨798543, by rfl⟩ : syracuseStep 2129449 = 1597087) (by norm_num)
theorem B2839265 : Blo 1891435 2839265 := bstep (se 2 (by rfl) ⟨1064724, by rfl⟩ : syracuseStep 2839265 = 2129449) B2129449
theorem B1892843 : Blo 1891435 1892843 := bstep (se 1 (by rfl) ⟨1419632, by rfl⟩ : syracuseStep 1892843 = 2839265) B2839265
theorem B18191861 : Blo 1891435 18191861 := bbase (se 5 (by rfl) ⟨852743, by rfl⟩ : syracuseStep 18191861 = 1705487) (by norm_num)
theorem B12127907 : Blo 1891435 12127907 := bstep (se 1 (by rfl) ⟨9095930, by rfl⟩ : syracuseStep 12127907 = 18191861) B18191861
theorem B8085271 : Blo 1891435 8085271 := bstep (se 1 (by rfl) ⟨6063953, by rfl⟩ : syracuseStep 8085271 = 12127907) B12127907
theorem B10780361 : Blo 1891435 10780361 := bstep (se 2 (by rfl) ⟨4042635, by rfl⟩ : syracuseStep 10780361 = 8085271) B8085271
theorem B7186907 : Blo 1891435 7186907 := bstep (se 1 (by rfl) ⟨5390180, by rfl⟩ : syracuseStep 7186907 = 10780361) B10780361
theorem B4791271 : Blo 1891435 4791271 := bstep (se 1 (by rfl) ⟨3593453, by rfl⟩ : syracuseStep 4791271 = 7186907) B7186907
theorem B6388361 : Blo 1891435 6388361 := bstep (se 2 (by rfl) ⟨2395635, by rfl⟩ : syracuseStep 6388361 = 4791271) B4791271
theorem B4258907 : Blo 1891435 4258907 := bstep (se 1 (by rfl) ⟨3194180, by rfl⟩ : syracuseStep 4258907 = 6388361) B6388361
theorem B2839271 : Blo 1891435 2839271 := bstep (se 1 (by rfl) ⟨2129453, by rfl⟩ : syracuseStep 2839271 = 4258907) B4258907
theorem B1892847 : Blo 1891435 1892847 := bstep (se 1 (by rfl) ⟨1419635, by rfl⟩ : syracuseStep 1892847 = 2839271) B2839271
theorem B2839277 : Blo 1891435 2839277 := bbase (se 3 (by rfl) ⟨532364, by rfl⟩ : syracuseStep 2839277 = 1064729) (by norm_num)
theorem B1892851 : Blo 1891435 1892851 := bstep (se 1 (by rfl) ⟨1419638, by rfl⟩ : syracuseStep 1892851 = 2839277) B2839277
theorem B4258925 : Blo 1891435 4258925 := bbase (se 3 (by rfl) ⟨798548, by rfl⟩ : syracuseStep 4258925 = 1597097) (by norm_num)
theorem B2839283 : Blo 1891435 2839283 := bstep (se 1 (by rfl) ⟨2129462, by rfl⟩ : syracuseStep 2839283 = 4258925) B4258925
theorem B1892855 : Blo 1891435 1892855 := bstep (se 1 (by rfl) ⟨1419641, by rfl⟩ : syracuseStep 1892855 = 2839283) B2839283
theorem B3593477 : Blo 1891435 3593477 := bbase (se 4 (by rfl) ⟨336888, by rfl⟩ : syracuseStep 3593477 = 673777) (by norm_num)
theorem B2395651 : Blo 1891435 2395651 := bstep (se 1 (by rfl) ⟨1796738, by rfl⟩ : syracuseStep 2395651 = 3593477) B3593477
theorem B3194201 : Blo 1891435 3194201 := bstep (se 2 (by rfl) ⟨1197825, by rfl⟩ : syracuseStep 3194201 = 2395651) B2395651
theorem B2129467 : Blo 1891435 2129467 := bstep (se 1 (by rfl) ⟨1597100, by rfl⟩ : syracuseStep 2129467 = 3194201) B3194201
theorem B2839289 : Blo 1891435 2839289 := bstep (se 2 (by rfl) ⟨1064733, by rfl⟩ : syracuseStep 2839289 = 2129467) B2129467
theorem B1892859 : Blo 1891435 1892859 := bstep (se 1 (by rfl) ⟨1419644, by rfl⟩ : syracuseStep 1892859 = 2839289) B2839289
theorem B3457541 : Blo 1891435 3457541 := bbase (se 4 (by rfl) ⟨324144, by rfl⟩ : syracuseStep 3457541 = 648289) (by norm_num)
theorem B2305027 : Blo 1891435 2305027 := bstep (se 1 (by rfl) ⟨1728770, by rfl⟩ : syracuseStep 2305027 = 3457541) B3457541
theorem B12293477 : Blo 1891435 12293477 := bstep (se 4 (by rfl) ⟨1152513, by rfl⟩ : syracuseStep 12293477 = 2305027) B2305027
theorem B8195651 : Blo 1891435 8195651 := bstep (se 1 (by rfl) ⟨6146738, by rfl⟩ : syracuseStep 8195651 = 12293477) B12293477
theorem B5463767 : Blo 1891435 5463767 := bstep (se 1 (by rfl) ⟨4097825, by rfl⟩ : syracuseStep 5463767 = 8195651) B8195651
theorem B14570045 : Blo 1891435 14570045 := bstep (se 3 (by rfl) ⟨2731883, by rfl⟩ : syracuseStep 14570045 = 5463767) B5463767
theorem B9713363 : Blo 1891435 9713363 := bstep (se 1 (by rfl) ⟨7285022, by rfl⟩ : syracuseStep 9713363 = 14570045) B14570045
theorem B25902301 : Blo 1891435 25902301 := bstep (se 3 (by rfl) ⟨4856681, by rfl⟩ : syracuseStep 25902301 = 9713363) B9713363
theorem B34536401 : Blo 1891435 34536401 := bstep (se 2 (by rfl) ⟨12951150, by rfl⟩ : syracuseStep 34536401 = 25902301) B25902301
theorem B23024267 : Blo 1891435 23024267 := bstep (se 1 (by rfl) ⟨17268200, by rfl⟩ : syracuseStep 23024267 = 34536401) B34536401
theorem B15349511 : Blo 1891435 15349511 := bstep (se 1 (by rfl) ⟨11512133, by rfl⟩ : syracuseStep 15349511 = 23024267) B23024267
theorem B40932029 : Blo 1891435 40932029 := bstep (se 3 (by rfl) ⟨7674755, by rfl⟩ : syracuseStep 40932029 = 15349511) B15349511
theorem B27288019 : Blo 1891435 27288019 := bstep (se 1 (by rfl) ⟨20466014, by rfl⟩ : syracuseStep 27288019 = 40932029) B40932029
theorem B36384025 : Blo 1891435 36384025 := bstep (se 2 (by rfl) ⟨13644009, by rfl⟩ : syracuseStep 36384025 = 27288019) B27288019
theorem B48512033 : Blo 1891435 48512033 := bstep (se 2 (by rfl) ⟨18192012, by rfl⟩ : syracuseStep 48512033 = 36384025) B36384025
theorem B32341355 : Blo 1891435 32341355 := bstep (se 1 (by rfl) ⟨24256016, by rfl⟩ : syracuseStep 32341355 = 48512033) B48512033
theorem B21560903 : Blo 1891435 21560903 := bstep (se 1 (by rfl) ⟨16170677, by rfl⟩ : syracuseStep 21560903 = 32341355) B32341355
theorem B14373935 : Blo 1891435 14373935 := bstep (se 1 (by rfl) ⟨10780451, by rfl⟩ : syracuseStep 14373935 = 21560903) B21560903
theorem B9582623 : Blo 1891435 9582623 := bstep (se 1 (by rfl) ⟨7186967, by rfl⟩ : syracuseStep 9582623 = 14373935) B14373935
theorem B6388415 : Blo 1891435 6388415 := bstep (se 1 (by rfl) ⟨4791311, by rfl⟩ : syracuseStep 6388415 = 9582623) B9582623
theorem B4258943 : Blo 1891435 4258943 := bstep (se 1 (by rfl) ⟨3194207, by rfl⟩ : syracuseStep 4258943 = 6388415) B6388415
theorem B2839295 : Blo 1891435 2839295 := bstep (se 1 (by rfl) ⟨2129471, by rfl⟩ : syracuseStep 2839295 = 4258943) B4258943
theorem B1892863 : Blo 1891435 1892863 := bstep (se 1 (by rfl) ⟨1419647, by rfl⟩ : syracuseStep 1892863 = 2839295) B2839295
theorem B2839301 : Blo 1891435 2839301 := bbase (se 4 (by rfl) ⟨266184, by rfl⟩ : syracuseStep 2839301 = 532369) (by norm_num)
theorem B1892867 : Blo 1891435 1892867 := bstep (se 1 (by rfl) ⟨1419650, by rfl⟩ : syracuseStep 1892867 = 2839301) B2839301
theorem B3194221 : Blo 1891435 3194221 := bbase (se 3 (by rfl) ⟨598916, by rfl⟩ : syracuseStep 3194221 = 1197833) (by norm_num)
theorem B4258961 : Blo 1891435 4258961 := bstep (se 2 (by rfl) ⟨1597110, by rfl⟩ : syracuseStep 4258961 = 3194221) B3194221
theorem B2839307 : Blo 1891435 2839307 := bstep (se 1 (by rfl) ⟨2129480, by rfl⟩ : syracuseStep 2839307 = 4258961) B4258961
theorem B1892871 : Blo 1891435 1892871 := bstep (se 1 (by rfl) ⟨1419653, by rfl⟩ : syracuseStep 1892871 = 2839307) B2839307
theorem B2129485 : Blo 1891435 2129485 := bbase (se 3 (by rfl) ⟨399278, by rfl⟩ : syracuseStep 2129485 = 798557) (by norm_num)
theorem B2839313 : Blo 1891435 2839313 := bstep (se 2 (by rfl) ⟨1064742, by rfl⟩ : syracuseStep 2839313 = 2129485) B2129485
theorem B1892875 : Blo 1891435 1892875 := bstep (se 1 (by rfl) ⟨1419656, by rfl⟩ : syracuseStep 1892875 = 2839313) B2839313
theorem B6388469 : Blo 1891435 6388469 := bbase (se 5 (by rfl) ⟨299459, by rfl⟩ : syracuseStep 6388469 = 598919) (by norm_num)
theorem B4258979 : Blo 1891435 4258979 := bstep (se 1 (by rfl) ⟨3194234, by rfl⟩ : syracuseStep 4258979 = 6388469) B6388469
theorem B2839319 : Blo 1891435 2839319 := bstep (se 1 (by rfl) ⟨2129489, by rfl⟩ : syracuseStep 2839319 = 4258979) B4258979
theorem B1892879 : Blo 1891435 1892879 := bstep (se 1 (by rfl) ⟨1419659, by rfl⟩ : syracuseStep 1892879 = 2839319) B2839319
theorem B2839325 : Blo 1891435 2839325 := bbase (se 3 (by rfl) ⟨532373, by rfl⟩ : syracuseStep 2839325 = 1064747) (by norm_num)
theorem B1892883 : Blo 1891435 1892883 := bstep (se 1 (by rfl) ⟨1419662, by rfl⟩ : syracuseStep 1892883 = 2839325) B2839325
theorem B4258997 : Blo 1891435 4258997 := bbase (se 5 (by rfl) ⟨199640, by rfl⟩ : syracuseStep 4258997 = 399281) (by norm_num)
theorem B2839331 : Blo 1891435 2839331 := bstep (se 1 (by rfl) ⟨2129498, by rfl⟩ : syracuseStep 2839331 = 4258997) B4258997
theorem B1892887 : Blo 1891435 1892887 := bstep (se 1 (by rfl) ⟨1419665, by rfl⟩ : syracuseStep 1892887 = 2839331) B2839331
theorem B2021365 : Blo 1891435 2021365 := bbase (se 5 (by rfl) ⟨94751, by rfl⟩ : syracuseStep 2021365 = 189503) (by norm_num)
theorem B10780613 : Blo 1891435 10780613 := bstep (se 4 (by rfl) ⟨1010682, by rfl⟩ : syracuseStep 10780613 = 2021365) B2021365
theorem B7187075 : Blo 1891435 7187075 := bstep (se 1 (by rfl) ⟨5390306, by rfl⟩ : syracuseStep 7187075 = 10780613) B10780613
theorem B4791383 : Blo 1891435 4791383 := bstep (se 1 (by rfl) ⟨3593537, by rfl⟩ : syracuseStep 4791383 = 7187075) B7187075
theorem B3194255 : Blo 1891435 3194255 := bstep (se 1 (by rfl) ⟨2395691, by rfl⟩ : syracuseStep 3194255 = 4791383) B4791383
theorem B2129503 : Blo 1891435 2129503 := bstep (se 1 (by rfl) ⟨1597127, by rfl⟩ : syracuseStep 2129503 = 3194255) B3194255
theorem B2839337 : Blo 1891435 2839337 := bstep (se 2 (by rfl) ⟨1064751, by rfl⟩ : syracuseStep 2839337 = 2129503) B2129503
theorem B1892891 : Blo 1891435 1892891 := bstep (se 1 (by rfl) ⟨1419668, by rfl⟩ : syracuseStep 1892891 = 2839337) B2839337
theorem B2021369 : Blo 1891435 2021369 := bbase (se 2 (by rfl) ⟨758013, by rfl⟩ : syracuseStep 2021369 = 1516027) (by norm_num)
theorem B5390317 : Blo 1891435 5390317 := bstep (se 3 (by rfl) ⟨1010684, by rfl⟩ : syracuseStep 5390317 = 2021369) B2021369
theorem B7187089 : Blo 1891435 7187089 := bstep (se 2 (by rfl) ⟨2695158, by rfl⟩ : syracuseStep 7187089 = 5390317) B5390317
theorem B9582785 : Blo 1891435 9582785 := bstep (se 2 (by rfl) ⟨3593544, by rfl⟩ : syracuseStep 9582785 = 7187089) B7187089
theorem B6388523 : Blo 1891435 6388523 := bstep (se 1 (by rfl) ⟨4791392, by rfl⟩ : syracuseStep 6388523 = 9582785) B9582785
theorem B4259015 : Blo 1891435 4259015 := bstep (se 1 (by rfl) ⟨3194261, by rfl⟩ : syracuseStep 4259015 = 6388523) B6388523
theorem B2839343 : Blo 1891435 2839343 := bstep (se 1 (by rfl) ⟨2129507, by rfl⟩ : syracuseStep 2839343 = 4259015) B4259015
theorem B1892895 : Blo 1891435 1892895 := bstep (se 1 (by rfl) ⟨1419671, by rfl⟩ : syracuseStep 1892895 = 2839343) B2839343
theorem B2839349 : Blo 1891435 2839349 := bbase (se 5 (by rfl) ⟨133094, by rfl⟩ : syracuseStep 2839349 = 266189) (by norm_num)
theorem B1892899 : Blo 1891435 1892899 := bstep (se 1 (by rfl) ⟨1419674, by rfl⟩ : syracuseStep 1892899 = 2839349) B2839349
theorem B4791413 : Blo 1891435 4791413 := bbase (se 5 (by rfl) ⟨224597, by rfl⟩ : syracuseStep 4791413 = 449195) (by norm_num)
theorem B3194275 : Blo 1891435 3194275 := bstep (se 1 (by rfl) ⟨2395706, by rfl⟩ : syracuseStep 3194275 = 4791413) B4791413
theorem B4259033 : Blo 1891435 4259033 := bstep (se 2 (by rfl) ⟨1597137, by rfl⟩ : syracuseStep 4259033 = 3194275) B3194275
theorem B2839355 : Blo 1891435 2839355 := bstep (se 1 (by rfl) ⟨2129516, by rfl⟩ : syracuseStep 2839355 = 4259033) B4259033
theorem B1892903 : Blo 1891435 1892903 := bstep (se 1 (by rfl) ⟨1419677, by rfl⟩ : syracuseStep 1892903 = 2839355) B2839355
theorem B2129521 : Blo 1891435 2129521 := bbase (se 2 (by rfl) ⟨798570, by rfl⟩ : syracuseStep 2129521 = 1597141) (by norm_num)
theorem B2839361 : Blo 1891435 2839361 := bstep (se 2 (by rfl) ⟨1064760, by rfl⟩ : syracuseStep 2839361 = 2129521) B2129521
theorem B1892907 : Blo 1891435 1892907 := bstep (se 1 (by rfl) ⟨1419680, by rfl⟩ : syracuseStep 1892907 = 2839361) B2839361
theorem B3642605 : Blo 1891435 3642605 := bbase (se 3 (by rfl) ⟨682988, by rfl⟩ : syracuseStep 3642605 = 1365977) (by norm_num)
theorem B2428403 : Blo 1891435 2428403 := bstep (se 1 (by rfl) ⟨1821302, by rfl⟩ : syracuseStep 2428403 = 3642605) B3642605
theorem B25902965 : Blo 1891435 25902965 := bstep (se 5 (by rfl) ⟨1214201, by rfl⟩ : syracuseStep 25902965 = 2428403) B2428403
theorem B17268643 : Blo 1891435 17268643 := bstep (se 1 (by rfl) ⟨12951482, by rfl⟩ : syracuseStep 17268643 = 25902965) B25902965
theorem B23024857 : Blo 1891435 23024857 := bstep (se 2 (by rfl) ⟨8634321, by rfl⟩ : syracuseStep 23024857 = 17268643) B17268643
theorem B30699809 : Blo 1891435 30699809 := bstep (se 2 (by rfl) ⟨11512428, by rfl⟩ : syracuseStep 30699809 = 23024857) B23024857
theorem B20466539 : Blo 1891435 20466539 := bstep (se 1 (by rfl) ⟨15349904, by rfl⟩ : syracuseStep 20466539 = 30699809) B30699809
theorem B13644359 : Blo 1891435 13644359 := bstep (se 1 (by rfl) ⟨10233269, by rfl⟩ : syracuseStep 13644359 = 20466539) B20466539
theorem B9096239 : Blo 1891435 9096239 := bstep (se 1 (by rfl) ⟨6822179, by rfl⟩ : syracuseStep 9096239 = 13644359) B13644359
theorem B6064159 : Blo 1891435 6064159 := bstep (se 1 (by rfl) ⟨4548119, by rfl⟩ : syracuseStep 6064159 = 9096239) B9096239
theorem B8085545 : Blo 1891435 8085545 := bstep (se 2 (by rfl) ⟨3032079, by rfl⟩ : syracuseStep 8085545 = 6064159) B6064159
theorem B5390363 : Blo 1891435 5390363 := bstep (se 1 (by rfl) ⟨4042772, by rfl⟩ : syracuseStep 5390363 = 8085545) B8085545
theorem B3593575 : Blo 1891435 3593575 := bstep (se 1 (by rfl) ⟨2695181, by rfl⟩ : syracuseStep 3593575 = 5390363) B5390363
theorem B4791433 : Blo 1891435 4791433 := bstep (se 2 (by rfl) ⟨1796787, by rfl⟩ : syracuseStep 4791433 = 3593575) B3593575
theorem B6388577 : Blo 1891435 6388577 := bstep (se 2 (by rfl) ⟨2395716, by rfl⟩ : syracuseStep 6388577 = 4791433) B4791433
theorem B4259051 : Blo 1891435 4259051 := bstep (se 1 (by rfl) ⟨3194288, by rfl⟩ : syracuseStep 4259051 = 6388577) B6388577
theorem B2839367 : Blo 1891435 2839367 := bstep (se 1 (by rfl) ⟨2129525, by rfl⟩ : syracuseStep 2839367 = 4259051) B4259051
theorem B1892911 : Blo 1891435 1892911 := bstep (se 1 (by rfl) ⟨1419683, by rfl⟩ : syracuseStep 1892911 = 2839367) B2839367
theorem B2839373 : Blo 1891435 2839373 := bbase (se 3 (by rfl) ⟨532382, by rfl⟩ : syracuseStep 2839373 = 1064765) (by norm_num)
theorem B1892915 : Blo 1891435 1892915 := bstep (se 1 (by rfl) ⟨1419686, by rfl⟩ : syracuseStep 1892915 = 2839373) B2839373
theorem B4259069 : Blo 1891435 4259069 := bbase (se 3 (by rfl) ⟨798575, by rfl⟩ : syracuseStep 4259069 = 1597151) (by norm_num)
theorem B2839379 : Blo 1891435 2839379 := bstep (se 1 (by rfl) ⟨2129534, by rfl⟩ : syracuseStep 2839379 = 4259069) B4259069
theorem B1892919 : Blo 1891435 1892919 := bstep (se 1 (by rfl) ⟨1419689, by rfl⟩ : syracuseStep 1892919 = 2839379) B2839379
theorem B3194309 : Blo 1891435 3194309 := bbase (se 4 (by rfl) ⟨299466, by rfl⟩ : syracuseStep 3194309 = 598933) (by norm_num)
theorem B2129539 : Blo 1891435 2129539 := bstep (se 1 (by rfl) ⟨1597154, by rfl⟩ : syracuseStep 2129539 = 3194309) B3194309
theorem B2839385 : Blo 1891435 2839385 := bstep (se 2 (by rfl) ⟨1064769, by rfl⟩ : syracuseStep 2839385 = 2129539) B2129539
theorem B1892923 : Blo 1891435 1892923 := bstep (se 1 (by rfl) ⟨1419692, by rfl⟩ : syracuseStep 1892923 = 2839385) B2839385
theorem B14374421 : Blo 1891435 14374421 := bbase (se 6 (by rfl) ⟨336900, by rfl⟩ : syracuseStep 14374421 = 673801) (by norm_num)
theorem B9582947 : Blo 1891435 9582947 := bstep (se 1 (by rfl) ⟨7187210, by rfl⟩ : syracuseStep 9582947 = 14374421) B14374421
theorem B6388631 : Blo 1891435 6388631 := bstep (se 1 (by rfl) ⟨4791473, by rfl⟩ : syracuseStep 6388631 = 9582947) B9582947
theorem B4259087 : Blo 1891435 4259087 := bstep (se 1 (by rfl) ⟨3194315, by rfl⟩ : syracuseStep 4259087 = 6388631) B6388631
theorem B2839391 : Blo 1891435 2839391 := bstep (se 1 (by rfl) ⟨2129543, by rfl⟩ : syracuseStep 2839391 = 4259087) B4259087
theorem B1892927 : Blo 1891435 1892927 := bstep (se 1 (by rfl) ⟨1419695, by rfl⟩ : syracuseStep 1892927 = 2839391) B2839391
theorem B2839397 : Blo 1891435 2839397 := bbase (se 4 (by rfl) ⟨266193, by rfl⟩ : syracuseStep 2839397 = 532387) (by norm_num)
theorem B1892931 : Blo 1891435 1892931 := bstep (se 1 (by rfl) ⟨1419698, by rfl⟩ : syracuseStep 1892931 = 2839397) B2839397
theorem B3593621 : Blo 1891435 3593621 := bbase (se 6 (by rfl) ⟨84225, by rfl⟩ : syracuseStep 3593621 = 168451) (by norm_num)
theorem B2395747 : Blo 1891435 2395747 := bstep (se 1 (by rfl) ⟨1796810, by rfl⟩ : syracuseStep 2395747 = 3593621) B3593621
theorem B3194329 : Blo 1891435 3194329 := bstep (se 2 (by rfl) ⟨1197873, by rfl⟩ : syracuseStep 3194329 = 2395747) B2395747
theorem B4259105 : Blo 1891435 4259105 := bstep (se 2 (by rfl) ⟨1597164, by rfl⟩ : syracuseStep 4259105 = 3194329) B3194329
theorem B2839403 : Blo 1891435 2839403 := bstep (se 1 (by rfl) ⟨2129552, by rfl⟩ : syracuseStep 2839403 = 4259105) B4259105
theorem B1892935 : Blo 1891435 1892935 := bstep (se 1 (by rfl) ⟨1419701, by rfl⟩ : syracuseStep 1892935 = 2839403) B2839403
theorem B2129557 : Blo 1891435 2129557 := bbase (se 6 (by rfl) ⟨49911, by rfl⟩ : syracuseStep 2129557 = 99823) (by norm_num)
theorem B2839409 : Blo 1891435 2839409 := bstep (se 2 (by rfl) ⟨1064778, by rfl⟩ : syracuseStep 2839409 = 2129557) B2129557
theorem B1892939 : Blo 1891435 1892939 := bstep (se 1 (by rfl) ⟨1419704, by rfl⟩ : syracuseStep 1892939 = 2839409) B2839409
theorem B2395757 : Blo 1891435 2395757 := bbase (se 3 (by rfl) ⟨449204, by rfl⟩ : syracuseStep 2395757 = 898409) (by norm_num)
theorem B6388685 : Blo 1891435 6388685 := bstep (se 3 (by rfl) ⟨1197878, by rfl⟩ : syracuseStep 6388685 = 2395757) B2395757
theorem B4259123 : Blo 1891435 4259123 := bstep (se 1 (by rfl) ⟨3194342, by rfl⟩ : syracuseStep 4259123 = 6388685) B6388685
theorem B2839415 : Blo 1891435 2839415 := bstep (se 1 (by rfl) ⟨2129561, by rfl⟩ : syracuseStep 2839415 = 4259123) B4259123
theorem B1892943 : Blo 1891435 1892943 := bstep (se 1 (by rfl) ⟨1419707, by rfl⟩ : syracuseStep 1892943 = 2839415) B2839415
theorem B2839421 : Blo 1891435 2839421 := bbase (se 3 (by rfl) ⟨532391, by rfl⟩ : syracuseStep 2839421 = 1064783) (by norm_num)
theorem B1892947 : Blo 1891435 1892947 := bstep (se 1 (by rfl) ⟨1419710, by rfl⟩ : syracuseStep 1892947 = 2839421) B2839421
theorem B4259141 : Blo 1891435 4259141 := bbase (se 4 (by rfl) ⟨399294, by rfl⟩ : syracuseStep 4259141 = 798589) (by norm_num)
theorem B2839427 : Blo 1891435 2839427 := bstep (se 1 (by rfl) ⟨2129570, by rfl⟩ : syracuseStep 2839427 = 4259141) B4259141
theorem B1892951 : Blo 1891435 1892951 := bstep (se 1 (by rfl) ⟨1419713, by rfl⟩ : syracuseStep 1892951 = 2839427) B2839427
theorem B2274113 : Blo 1891435 2274113 := bbase (se 2 (by rfl) ⟨852792, by rfl⟩ : syracuseStep 2274113 = 1705585) (by norm_num)
theorem B6064301 : Blo 1891435 6064301 := bstep (se 3 (by rfl) ⟨1137056, by rfl⟩ : syracuseStep 6064301 = 2274113) B2274113
theorem B4042867 : Blo 1891435 4042867 := bstep (se 1 (by rfl) ⟨3032150, by rfl⟩ : syracuseStep 4042867 = 6064301) B6064301
theorem B5390489 : Blo 1891435 5390489 := bstep (se 2 (by rfl) ⟨2021433, by rfl⟩ : syracuseStep 5390489 = 4042867) B4042867
theorem B3593659 : Blo 1891435 3593659 := bstep (se 1 (by rfl) ⟨2695244, by rfl⟩ : syracuseStep 3593659 = 5390489) B5390489
theorem B4791545 : Blo 1891435 4791545 := bstep (se 2 (by rfl) ⟨1796829, by rfl⟩ : syracuseStep 4791545 = 3593659) B3593659
theorem B3194363 : Blo 1891435 3194363 := bstep (se 1 (by rfl) ⟨2395772, by rfl⟩ : syracuseStep 3194363 = 4791545) B4791545
theorem B2129575 : Blo 1891435 2129575 := bstep (se 1 (by rfl) ⟨1597181, by rfl⟩ : syracuseStep 2129575 = 3194363) B3194363
theorem B2839433 : Blo 1891435 2839433 := bstep (se 2 (by rfl) ⟨1064787, by rfl⟩ : syracuseStep 2839433 = 2129575) B2129575
theorem B1892955 : Blo 1891435 1892955 := bstep (se 1 (by rfl) ⟨1419716, by rfl⟩ : syracuseStep 1892955 = 2839433) B2839433
theorem B9583109 : Blo 1891435 9583109 := bbase (se 4 (by rfl) ⟨898416, by rfl⟩ : syracuseStep 9583109 = 1796833) (by norm_num)
theorem B6388739 : Blo 1891435 6388739 := bstep (se 1 (by rfl) ⟨4791554, by rfl⟩ : syracuseStep 6388739 = 9583109) B9583109
theorem B4259159 : Blo 1891435 4259159 := bstep (se 1 (by rfl) ⟨3194369, by rfl⟩ : syracuseStep 4259159 = 6388739) B6388739
theorem B2839439 : Blo 1891435 2839439 := bstep (se 1 (by rfl) ⟨2129579, by rfl⟩ : syracuseStep 2839439 = 4259159) B4259159
theorem B1892959 : Blo 1891435 1892959 := bstep (se 1 (by rfl) ⟨1419719, by rfl⟩ : syracuseStep 1892959 = 2839439) B2839439
theorem B2839445 : Blo 1891435 2839445 := bbase (se 6 (by rfl) ⟨66549, by rfl⟩ : syracuseStep 2839445 = 133099) (by norm_num)
theorem B1892963 : Blo 1891435 1892963 := bstep (se 1 (by rfl) ⟨1419722, by rfl⟩ : syracuseStep 1892963 = 2839445) B2839445
theorem B10781045 : Blo 1891435 10781045 := bbase (se 5 (by rfl) ⟨505361, by rfl⟩ : syracuseStep 10781045 = 1010723) (by norm_num)
theorem B7187363 : Blo 1891435 7187363 := bstep (se 1 (by rfl) ⟨5390522, by rfl⟩ : syracuseStep 7187363 = 10781045) B10781045
theorem B4791575 : Blo 1891435 4791575 := bstep (se 1 (by rfl) ⟨3593681, by rfl⟩ : syracuseStep 4791575 = 7187363) B7187363
theorem B3194383 : Blo 1891435 3194383 := bstep (se 1 (by rfl) ⟨2395787, by rfl⟩ : syracuseStep 3194383 = 4791575) B4791575
theorem B4259177 : Blo 1891435 4259177 := bstep (se 2 (by rfl) ⟨1597191, by rfl⟩ : syracuseStep 4259177 = 3194383) B3194383
theorem B2839451 : Blo 1891435 2839451 := bstep (se 1 (by rfl) ⟨2129588, by rfl⟩ : syracuseStep 2839451 = 4259177) B4259177
theorem B1892967 : Blo 1891435 1892967 := bstep (se 1 (by rfl) ⟨1419725, by rfl⟩ : syracuseStep 1892967 = 2839451) B2839451
theorem B2129593 : Blo 1891435 2129593 := bbase (se 2 (by rfl) ⟨798597, by rfl⟩ : syracuseStep 2129593 = 1597195) (by norm_num)
theorem B2839457 : Blo 1891435 2839457 := bstep (se 2 (by rfl) ⟨1064796, by rfl⟩ : syracuseStep 2839457 = 2129593) B2129593
theorem B1892971 : Blo 1891435 1892971 := bstep (se 1 (by rfl) ⟨1419728, by rfl⟩ : syracuseStep 1892971 = 2839457) B2839457
theorem B4042909 : Blo 1891435 4042909 := bbase (se 3 (by rfl) ⟨758045, by rfl⟩ : syracuseStep 4042909 = 1516091) (by norm_num)
theorem B5390545 : Blo 1891435 5390545 := bstep (se 2 (by rfl) ⟨2021454, by rfl⟩ : syracuseStep 5390545 = 4042909) B4042909
theorem B7187393 : Blo 1891435 7187393 := bstep (se 2 (by rfl) ⟨2695272, by rfl⟩ : syracuseStep 7187393 = 5390545) B5390545
theorem B4791595 : Blo 1891435 4791595 := bstep (se 1 (by rfl) ⟨3593696, by rfl⟩ : syracuseStep 4791595 = 7187393) B7187393
theorem B6388793 : Blo 1891435 6388793 := bstep (se 2 (by rfl) ⟨2395797, by rfl⟩ : syracuseStep 6388793 = 4791595) B4791595
theorem B4259195 : Blo 1891435 4259195 := bstep (se 1 (by rfl) ⟨3194396, by rfl⟩ : syracuseStep 4259195 = 6388793) B6388793
theorem B2839463 : Blo 1891435 2839463 := bstep (se 1 (by rfl) ⟨2129597, by rfl⟩ : syracuseStep 2839463 = 4259195) B4259195
theorem B1892975 : Blo 1891435 1892975 := bstep (se 1 (by rfl) ⟨1419731, by rfl⟩ : syracuseStep 1892975 = 2839463) B2839463
theorem B2839469 : Blo 1891435 2839469 := bbase (se 3 (by rfl) ⟨532400, by rfl⟩ : syracuseStep 2839469 = 1064801) (by norm_num)
theorem B1892979 : Blo 1891435 1892979 := bstep (se 1 (by rfl) ⟨1419734, by rfl⟩ : syracuseStep 1892979 = 2839469) B2839469
theorem B4259213 : Blo 1891435 4259213 := bbase (se 3 (by rfl) ⟨798602, by rfl⟩ : syracuseStep 4259213 = 1597205) (by norm_num)
theorem B2839475 : Blo 1891435 2839475 := bstep (se 1 (by rfl) ⟨2129606, by rfl⟩ : syracuseStep 2839475 = 4259213) B4259213
theorem B1892983 : Blo 1891435 1892983 := bstep (se 1 (by rfl) ⟨1419737, by rfl⟩ : syracuseStep 1892983 = 2839475) B2839475
theorem B2395813 : Blo 1891435 2395813 := bbase (se 4 (by rfl) ⟨224607, by rfl⟩ : syracuseStep 2395813 = 449215) (by norm_num)
theorem B3194417 : Blo 1891435 3194417 := bstep (se 2 (by rfl) ⟨1197906, by rfl⟩ : syracuseStep 3194417 = 2395813) B2395813
theorem B2129611 : Blo 1891435 2129611 := bstep (se 1 (by rfl) ⟨1597208, by rfl⟩ : syracuseStep 2129611 = 3194417) B3194417
theorem B2839481 : Blo 1891435 2839481 := bstep (se 2 (by rfl) ⟨1064805, by rfl⟩ : syracuseStep 2839481 = 2129611) B2129611
theorem B1892987 : Blo 1891435 1892987 := bstep (se 1 (by rfl) ⟨1419740, by rfl⟩ : syracuseStep 1892987 = 2839481) B2839481
theorem B2428505 : Blo 1891435 2428505 := bbase (se 2 (by rfl) ⟨910689, by rfl⟩ : syracuseStep 2428505 = 1821379) (by norm_num)
theorem B25904053 : Blo 1891435 25904053 := bstep (se 5 (by rfl) ⟨1214252, by rfl⟩ : syracuseStep 25904053 = 2428505) B2428505
theorem B34538737 : Blo 1891435 34538737 := bstep (se 2 (by rfl) ⟨12952026, by rfl⟩ : syracuseStep 34538737 = 25904053) B25904053
theorem B46051649 : Blo 1891435 46051649 := bstep (se 2 (by rfl) ⟨17269368, by rfl⟩ : syracuseStep 46051649 = 34538737) B34538737
theorem B30701099 : Blo 1891435 30701099 := bstep (se 1 (by rfl) ⟨23025824, by rfl⟩ : syracuseStep 30701099 = 46051649) B46051649
theorem B20467399 : Blo 1891435 20467399 := bstep (se 1 (by rfl) ⟨15350549, by rfl⟩ : syracuseStep 20467399 = 30701099) B30701099
theorem B27289865 : Blo 1891435 27289865 := bstep (se 2 (by rfl) ⟨10233699, by rfl⟩ : syracuseStep 27289865 = 20467399) B20467399
theorem B18193243 : Blo 1891435 18193243 := bstep (se 1 (by rfl) ⟨13644932, by rfl⟩ : syracuseStep 18193243 = 27289865) B27289865
theorem B24257657 : Blo 1891435 24257657 := bstep (se 2 (by rfl) ⟨9096621, by rfl⟩ : syracuseStep 24257657 = 18193243) B18193243
theorem B16171771 : Blo 1891435 16171771 := bstep (se 1 (by rfl) ⟨12128828, by rfl⟩ : syracuseStep 16171771 = 24257657) B24257657
theorem B21562361 : Blo 1891435 21562361 := bstep (se 2 (by rfl) ⟨8085885, by rfl⟩ : syracuseStep 21562361 = 16171771) B16171771
theorem B14374907 : Blo 1891435 14374907 := bstep (se 1 (by rfl) ⟨10781180, by rfl⟩ : syracuseStep 14374907 = 21562361) B21562361
theorem B9583271 : Blo 1891435 9583271 := bstep (se 1 (by rfl) ⟨7187453, by rfl⟩ : syracuseStep 9583271 = 14374907) B14374907
theorem B6388847 : Blo 1891435 6388847 := bstep (se 1 (by rfl) ⟨4791635, by rfl⟩ : syracuseStep 6388847 = 9583271) B9583271
theorem B4259231 : Blo 1891435 4259231 := bstep (se 1 (by rfl) ⟨3194423, by rfl⟩ : syracuseStep 4259231 = 6388847) B6388847
theorem B2839487 : Blo 1891435 2839487 := bstep (se 1 (by rfl) ⟨2129615, by rfl⟩ : syracuseStep 2839487 = 4259231) B4259231
theorem B1892991 : Blo 1891435 1892991 := bstep (se 1 (by rfl) ⟨1419743, by rfl⟩ : syracuseStep 1892991 = 2839487) B2839487
theorem B2839493 : Blo 1891435 2839493 := bbase (se 4 (by rfl) ⟨266202, by rfl⟩ : syracuseStep 2839493 = 532405) (by norm_num)
theorem B1892995 : Blo 1891435 1892995 := bstep (se 1 (by rfl) ⟨1419746, by rfl⟩ : syracuseStep 1892995 = 2839493) B2839493
theorem B3194437 : Blo 1891435 3194437 := bbase (se 4 (by rfl) ⟨299478, by rfl⟩ : syracuseStep 3194437 = 598957) (by norm_num)
theorem B4259249 : Blo 1891435 4259249 := bstep (se 2 (by rfl) ⟨1597218, by rfl⟩ : syracuseStep 4259249 = 3194437) B3194437
theorem B2839499 : Blo 1891435 2839499 := bstep (se 1 (by rfl) ⟨2129624, by rfl⟩ : syracuseStep 2839499 = 4259249) B4259249
theorem B1892999 : Blo 1891435 1892999 := bstep (se 1 (by rfl) ⟨1419749, by rfl⟩ : syracuseStep 1892999 = 2839499) B2839499
theorem B2129629 : Blo 1891435 2129629 := bbase (se 3 (by rfl) ⟨399305, by rfl⟩ : syracuseStep 2129629 = 798611) (by norm_num)
theorem B2839505 : Blo 1891435 2839505 := bstep (se 2 (by rfl) ⟨1064814, by rfl⟩ : syracuseStep 2839505 = 2129629) B2129629
theorem B1893003 : Blo 1891435 1893003 := bstep (se 1 (by rfl) ⟨1419752, by rfl⟩ : syracuseStep 1893003 = 2839505) B2839505
theorem B6388901 : Blo 1891435 6388901 := bbase (se 4 (by rfl) ⟨598959, by rfl⟩ : syracuseStep 6388901 = 1197919) (by norm_num)
theorem B4259267 : Blo 1891435 4259267 := bstep (se 1 (by rfl) ⟨3194450, by rfl⟩ : syracuseStep 4259267 = 6388901) B6388901
theorem B2839511 : Blo 1891435 2839511 := bstep (se 1 (by rfl) ⟨2129633, by rfl⟩ : syracuseStep 2839511 = 4259267) B4259267
theorem B1893007 : Blo 1891435 1893007 := bstep (se 1 (by rfl) ⟨1419755, by rfl⟩ : syracuseStep 1893007 = 2839511) B2839511
theorem B2839517 : Blo 1891435 2839517 := bbase (se 3 (by rfl) ⟨532409, by rfl⟩ : syracuseStep 2839517 = 1064819) (by norm_num)
theorem B1893011 : Blo 1891435 1893011 := bstep (se 1 (by rfl) ⟨1419758, by rfl⟩ : syracuseStep 1893011 = 2839517) B2839517
theorem B4259285 : Blo 1891435 4259285 := bbase (se 7 (by rfl) ⟨49913, by rfl⟩ : syracuseStep 4259285 = 99827) (by norm_num)
theorem B2839523 : Blo 1891435 2839523 := bstep (se 1 (by rfl) ⟨2129642, by rfl⟩ : syracuseStep 2839523 = 4259285) B4259285
theorem B1893015 : Blo 1891435 1893015 := bstep (se 1 (by rfl) ⟨1419761, by rfl⟩ : syracuseStep 1893015 = 2839523) B2839523
theorem B6077189 : Blo 1891435 6077189 := bbase (se 4 (by rfl) ⟨569736, by rfl⟩ : syracuseStep 6077189 = 1139473) (by norm_num)
theorem B16205837 : Blo 1891435 16205837 := bstep (se 3 (by rfl) ⟨3038594, by rfl⟩ : syracuseStep 16205837 = 6077189) B6077189
theorem B43215565 : Blo 1891435 43215565 := bstep (se 3 (by rfl) ⟨8102918, by rfl⟩ : syracuseStep 43215565 = 16205837) B16205837
theorem B57620753 : Blo 1891435 57620753 := bstep (se 2 (by rfl) ⟨21607782, by rfl⟩ : syracuseStep 57620753 = 43215565) B43215565
theorem B38413835 : Blo 1891435 38413835 := bstep (se 1 (by rfl) ⟨28810376, by rfl⟩ : syracuseStep 38413835 = 57620753) B57620753
theorem B25609223 : Blo 1891435 25609223 := bstep (se 1 (by rfl) ⟨19206917, by rfl⟩ : syracuseStep 25609223 = 38413835) B38413835
theorem B17072815 : Blo 1891435 17072815 := bstep (se 1 (by rfl) ⟨12804611, by rfl⟩ : syracuseStep 17072815 = 25609223) B25609223
theorem B22763753 : Blo 1891435 22763753 := bstep (se 2 (by rfl) ⟨8536407, by rfl⟩ : syracuseStep 22763753 = 17072815) B17072815
theorem B15175835 : Blo 1891435 15175835 := bstep (se 1 (by rfl) ⟨11381876, by rfl⟩ : syracuseStep 15175835 = 22763753) B22763753
theorem B10117223 : Blo 1891435 10117223 := bstep (se 1 (by rfl) ⟨7587917, by rfl⟩ : syracuseStep 10117223 = 15175835) B15175835
theorem B6744815 : Blo 1891435 6744815 := bstep (se 1 (by rfl) ⟨5058611, by rfl⟩ : syracuseStep 6744815 = 10117223) B10117223
theorem B4496543 : Blo 1891435 4496543 := bstep (se 1 (by rfl) ⟨3372407, by rfl⟩ : syracuseStep 4496543 = 6744815) B6744815
theorem B2997695 : Blo 1891435 2997695 := bstep (se 1 (by rfl) ⟨2248271, by rfl⟩ : syracuseStep 2997695 = 4496543) B4496543
theorem B7993853 : Blo 1891435 7993853 := bstep (se 3 (by rfl) ⟨1498847, by rfl⟩ : syracuseStep 7993853 = 2997695) B2997695
theorem B5329235 : Blo 1891435 5329235 := bstep (se 1 (by rfl) ⟨3996926, by rfl⟩ : syracuseStep 5329235 = 7993853) B7993853
theorem B14211293 : Blo 1891435 14211293 := bstep (se 3 (by rfl) ⟨2664617, by rfl⟩ : syracuseStep 14211293 = 5329235) B5329235
theorem B37896781 : Blo 1891435 37896781 := bstep (se 3 (by rfl) ⟨7105646, by rfl⟩ : syracuseStep 37896781 = 14211293) B14211293
theorem B50529041 : Blo 1891435 50529041 := bstep (se 2 (by rfl) ⟨18948390, by rfl⟩ : syracuseStep 50529041 = 37896781) B37896781
theorem B33686027 : Blo 1891435 33686027 := bstep (se 1 (by rfl) ⟨25264520, by rfl⟩ : syracuseStep 33686027 = 50529041) B50529041
theorem B22457351 : Blo 1891435 22457351 := bstep (se 1 (by rfl) ⟨16843013, by rfl⟩ : syracuseStep 22457351 = 33686027) B33686027
theorem B14971567 : Blo 1891435 14971567 := bstep (se 1 (by rfl) ⟨11228675, by rfl⟩ : syracuseStep 14971567 = 22457351) B22457351
theorem B19962089 : Blo 1891435 19962089 := bstep (se 2 (by rfl) ⟨7485783, by rfl⟩ : syracuseStep 19962089 = 14971567) B14971567
theorem B13308059 : Blo 1891435 13308059 := bstep (se 1 (by rfl) ⟨9981044, by rfl⟩ : syracuseStep 13308059 = 19962089) B19962089
theorem B8872039 : Blo 1891435 8872039 := bstep (se 1 (by rfl) ⟨6654029, by rfl⟩ : syracuseStep 8872039 = 13308059) B13308059
theorem B11829385 : Blo 1891435 11829385 := bstep (se 2 (by rfl) ⟨4436019, by rfl⟩ : syracuseStep 11829385 = 8872039) B8872039
theorem B63090053 : Blo 1891435 63090053 := bstep (se 4 (by rfl) ⟨5914692, by rfl⟩ : syracuseStep 63090053 = 11829385) B11829385
theorem B42060035 : Blo 1891435 42060035 := bstep (se 1 (by rfl) ⟨31545026, by rfl⟩ : syracuseStep 42060035 = 63090053) B63090053
theorem B28040023 : Blo 1891435 28040023 := bstep (se 1 (by rfl) ⟨21030017, by rfl⟩ : syracuseStep 28040023 = 42060035) B42060035
theorem B37386697 : Blo 1891435 37386697 := bstep (se 2 (by rfl) ⟨14020011, by rfl⟩ : syracuseStep 37386697 = 28040023) B28040023
theorem B49848929 : Blo 1891435 49848929 := bstep (se 2 (by rfl) ⟨18693348, by rfl⟩ : syracuseStep 49848929 = 37386697) B37386697
theorem B33232619 : Blo 1891435 33232619 := bstep (se 1 (by rfl) ⟨24924464, by rfl⟩ : syracuseStep 33232619 = 49848929) B49848929
theorem B88620317 : Blo 1891435 88620317 := bstep (se 3 (by rfl) ⟨16616309, by rfl⟩ : syracuseStep 88620317 = 33232619) B33232619
theorem B59080211 : Blo 1891435 59080211 := bstep (se 1 (by rfl) ⟨44310158, by rfl⟩ : syracuseStep 59080211 = 88620317) B88620317
theorem B39386807 : Blo 1891435 39386807 := bstep (se 1 (by rfl) ⟨29540105, by rfl⟩ : syracuseStep 39386807 = 59080211) B59080211
theorem B26257871 : Blo 1891435 26257871 := bstep (se 1 (by rfl) ⟨19693403, by rfl⟩ : syracuseStep 26257871 = 39386807) B39386807
theorem B17505247 : Blo 1891435 17505247 := bstep (se 1 (by rfl) ⟨13128935, by rfl⟩ : syracuseStep 17505247 = 26257871) B26257871
theorem B23340329 : Blo 1891435 23340329 := bstep (se 2 (by rfl) ⟨8752623, by rfl⟩ : syracuseStep 23340329 = 17505247) B17505247
theorem B15560219 : Blo 1891435 15560219 := bstep (se 1 (by rfl) ⟨11670164, by rfl⟩ : syracuseStep 15560219 = 23340329) B23340329
theorem B41493917 : Blo 1891435 41493917 := bstep (se 3 (by rfl) ⟨7780109, by rfl⟩ : syracuseStep 41493917 = 15560219) B15560219
theorem B110650445 : Blo 1891435 110650445 := bstep (se 3 (by rfl) ⟨20746958, by rfl⟩ : syracuseStep 110650445 = 41493917) B41493917
theorem B73766963 : Blo 1891435 73766963 := bstep (se 1 (by rfl) ⟨55325222, by rfl⟩ : syracuseStep 73766963 = 110650445) B110650445
theorem B196711901 : Blo 1891435 196711901 := bstep (se 3 (by rfl) ⟨36883481, by rfl⟩ : syracuseStep 196711901 = 73766963) B73766963
theorem B131141267 : Blo 1891435 131141267 := bstep (se 1 (by rfl) ⟨98355950, by rfl⟩ : syracuseStep 131141267 = 196711901) B196711901
theorem B87427511 : Blo 1891435 87427511 := bstep (se 1 (by rfl) ⟨65570633, by rfl⟩ : syracuseStep 87427511 = 131141267) B131141267
theorem B58285007 : Blo 1891435 58285007 := bstep (se 1 (by rfl) ⟨43713755, by rfl⟩ : syracuseStep 58285007 = 87427511) B87427511
theorem B38856671 : Blo 1891435 38856671 := bstep (se 1 (by rfl) ⟨29142503, by rfl⟩ : syracuseStep 38856671 = 58285007) B58285007
theorem B25904447 : Blo 1891435 25904447 := bstep (se 1 (by rfl) ⟨19428335, by rfl⟩ : syracuseStep 25904447 = 38856671) B38856671
theorem B17269631 : Blo 1891435 17269631 := bstep (se 1 (by rfl) ⟨12952223, by rfl⟩ : syracuseStep 17269631 = 25904447) B25904447
theorem B11513087 : Blo 1891435 11513087 := bstep (se 1 (by rfl) ⟨8634815, by rfl⟩ : syracuseStep 11513087 = 17269631) B17269631
theorem B7675391 : Blo 1891435 7675391 := bstep (se 1 (by rfl) ⟨5756543, by rfl⟩ : syracuseStep 7675391 = 11513087) B11513087
theorem B5116927 : Blo 1891435 5116927 := bstep (se 1 (by rfl) ⟨3837695, by rfl⟩ : syracuseStep 5116927 = 7675391) B7675391
theorem B6822569 : Blo 1891435 6822569 := bstep (se 2 (by rfl) ⟨2558463, by rfl⟩ : syracuseStep 6822569 = 5116927) B5116927
theorem B18193517 : Blo 1891435 18193517 := bstep (se 3 (by rfl) ⟨3411284, by rfl⟩ : syracuseStep 18193517 = 6822569) B6822569
theorem B12129011 : Blo 1891435 12129011 := bstep (se 1 (by rfl) ⟨9096758, by rfl⟩ : syracuseStep 12129011 = 18193517) B18193517
theorem B8086007 : Blo 1891435 8086007 := bstep (se 1 (by rfl) ⟨6064505, by rfl⟩ : syracuseStep 8086007 = 12129011) B12129011
theorem B5390671 : Blo 1891435 5390671 := bstep (se 1 (by rfl) ⟨4043003, by rfl⟩ : syracuseStep 5390671 = 8086007) B8086007
theorem B7187561 : Blo 1891435 7187561 := bstep (se 2 (by rfl) ⟨2695335, by rfl⟩ : syracuseStep 7187561 = 5390671) B5390671
theorem B4791707 : Blo 1891435 4791707 := bstep (se 1 (by rfl) ⟨3593780, by rfl⟩ : syracuseStep 4791707 = 7187561) B7187561
theorem B3194471 : Blo 1891435 3194471 := bstep (se 1 (by rfl) ⟨2395853, by rfl⟩ : syracuseStep 3194471 = 4791707) B4791707
theorem B2129647 : Blo 1891435 2129647 := bstep (se 1 (by rfl) ⟨1597235, by rfl⟩ : syracuseStep 2129647 = 3194471) B3194471
theorem B2839529 : Blo 1891435 2839529 := bstep (se 2 (by rfl) ⟨1064823, by rfl⟩ : syracuseStep 2839529 = 2129647) B2129647
theorem B1893019 : Blo 1891435 1893019 := bstep (se 1 (by rfl) ⟨1419764, by rfl⟩ : syracuseStep 1893019 = 2839529) B2839529
theorem B6064517 : Blo 1891435 6064517 := bbase (se 4 (by rfl) ⟨568548, by rfl⟩ : syracuseStep 6064517 = 1137097) (by norm_num)
theorem B16172045 : Blo 1891435 16172045 := bstep (se 3 (by rfl) ⟨3032258, by rfl⟩ : syracuseStep 16172045 = 6064517) B6064517
theorem B10781363 : Blo 1891435 10781363 := bstep (se 1 (by rfl) ⟨8086022, by rfl⟩ : syracuseStep 10781363 = 16172045) B16172045
theorem B7187575 : Blo 1891435 7187575 := bstep (se 1 (by rfl) ⟨5390681, by rfl⟩ : syracuseStep 7187575 = 10781363) B10781363
theorem B9583433 : Blo 1891435 9583433 := bstep (se 2 (by rfl) ⟨3593787, by rfl⟩ : syracuseStep 9583433 = 7187575) B7187575
theorem B6388955 : Blo 1891435 6388955 := bstep (se 1 (by rfl) ⟨4791716, by rfl⟩ : syracuseStep 6388955 = 9583433) B9583433
theorem B4259303 : Blo 1891435 4259303 := bstep (se 1 (by rfl) ⟨3194477, by rfl⟩ : syracuseStep 4259303 = 6388955) B6388955
theorem B2839535 : Blo 1891435 2839535 := bstep (se 1 (by rfl) ⟨2129651, by rfl⟩ : syracuseStep 2839535 = 4259303) B4259303
theorem B1893023 : Blo 1891435 1893023 := bstep (se 1 (by rfl) ⟨1419767, by rfl⟩ : syracuseStep 1893023 = 2839535) B2839535
theorem B2839541 : Blo 1891435 2839541 := bbase (se 5 (by rfl) ⟨133103, by rfl⟩ : syracuseStep 2839541 = 266207) (by norm_num)
theorem B1893027 : Blo 1891435 1893027 := bstep (se 1 (by rfl) ⟨1419770, by rfl⟩ : syracuseStep 1893027 = 2839541) B2839541
theorem B4043029 : Blo 1891435 4043029 := bbase (se 6 (by rfl) ⟨94758, by rfl⟩ : syracuseStep 4043029 = 189517) (by norm_num)
theorem B5390705 : Blo 1891435 5390705 := bstep (se 2 (by rfl) ⟨2021514, by rfl⟩ : syracuseStep 5390705 = 4043029) B4043029
theorem B3593803 : Blo 1891435 3593803 := bstep (se 1 (by rfl) ⟨2695352, by rfl⟩ : syracuseStep 3593803 = 5390705) B5390705
theorem B4791737 : Blo 1891435 4791737 := bstep (se 2 (by rfl) ⟨1796901, by rfl⟩ : syracuseStep 4791737 = 3593803) B3593803
theorem B3194491 : Blo 1891435 3194491 := bstep (se 1 (by rfl) ⟨2395868, by rfl⟩ : syracuseStep 3194491 = 4791737) B4791737
theorem B4259321 : Blo 1891435 4259321 := bstep (se 2 (by rfl) ⟨1597245, by rfl⟩ : syracuseStep 4259321 = 3194491) B3194491
theorem B2839547 : Blo 1891435 2839547 := bstep (se 1 (by rfl) ⟨2129660, by rfl⟩ : syracuseStep 2839547 = 4259321) B4259321
theorem B1893031 : Blo 1891435 1893031 := bstep (se 1 (by rfl) ⟨1419773, by rfl⟩ : syracuseStep 1893031 = 2839547) B2839547
theorem B2129665 : Blo 1891435 2129665 := bbase (se 2 (by rfl) ⟨798624, by rfl⟩ : syracuseStep 2129665 = 1597249) (by norm_num)
theorem B2839553 : Blo 1891435 2839553 := bstep (se 2 (by rfl) ⟨1064832, by rfl⟩ : syracuseStep 2839553 = 2129665) B2129665
theorem B1893035 : Blo 1891435 1893035 := bstep (se 1 (by rfl) ⟨1419776, by rfl⟩ : syracuseStep 1893035 = 2839553) B2839553
theorem B4791757 : Blo 1891435 4791757 := bbase (se 3 (by rfl) ⟨898454, by rfl⟩ : syracuseStep 4791757 = 1796909) (by norm_num)
theorem B6389009 : Blo 1891435 6389009 := bstep (se 2 (by rfl) ⟨2395878, by rfl⟩ : syracuseStep 6389009 = 4791757) B4791757
theorem B4259339 : Blo 1891435 4259339 := bstep (se 1 (by rfl) ⟨3194504, by rfl⟩ : syracuseStep 4259339 = 6389009) B6389009
theorem B2839559 : Blo 1891435 2839559 := bstep (se 1 (by rfl) ⟨2129669, by rfl⟩ : syracuseStep 2839559 = 4259339) B4259339
theorem B1893039 : Blo 1891435 1893039 := bstep (se 1 (by rfl) ⟨1419779, by rfl⟩ : syracuseStep 1893039 = 2839559) B2839559
theorem B2839565 : Blo 1891435 2839565 := bbase (se 3 (by rfl) ⟨532418, by rfl⟩ : syracuseStep 2839565 = 1064837) (by norm_num)
theorem B1893043 : Blo 1891435 1893043 := bstep (se 1 (by rfl) ⟨1419782, by rfl⟩ : syracuseStep 1893043 = 2839565) B2839565
theorem B4259357 : Blo 1891435 4259357 := bbase (se 3 (by rfl) ⟨798629, by rfl⟩ : syracuseStep 4259357 = 1597259) (by norm_num)
theorem B2839571 : Blo 1891435 2839571 := bstep (se 1 (by rfl) ⟨2129678, by rfl⟩ : syracuseStep 2839571 = 4259357) B4259357
theorem B1893047 : Blo 1891435 1893047 := bstep (se 1 (by rfl) ⟨1419785, by rfl⟩ : syracuseStep 1893047 = 2839571) B2839571
theorem B3194525 : Blo 1891435 3194525 := bbase (se 3 (by rfl) ⟨598973, by rfl⟩ : syracuseStep 3194525 = 1197947) (by norm_num)
theorem B2129683 : Blo 1891435 2129683 := bstep (se 1 (by rfl) ⟨1597262, by rfl⟩ : syracuseStep 2129683 = 3194525) B3194525
theorem B2839577 : Blo 1891435 2839577 := bstep (se 2 (by rfl) ⟨1064841, by rfl⟩ : syracuseStep 2839577 = 2129683) B2129683
theorem B1893051 : Blo 1891435 1893051 := bstep (se 1 (by rfl) ⟨1419788, by rfl⟩ : syracuseStep 1893051 = 2839577) B2839577
theorem B2049121 : Blo 1891435 2049121 := bbase (se 2 (by rfl) ⟨768420, by rfl⟩ : syracuseStep 2049121 = 1536841) (by norm_num)
theorem B10928645 : Blo 1891435 10928645 := bstep (se 4 (by rfl) ⟨1024560, by rfl⟩ : syracuseStep 10928645 = 2049121) B2049121
theorem B7285763 : Blo 1891435 7285763 := bstep (se 1 (by rfl) ⟨5464322, by rfl⟩ : syracuseStep 7285763 = 10928645) B10928645
theorem B4857175 : Blo 1891435 4857175 := bstep (se 1 (by rfl) ⟨3642881, by rfl⟩ : syracuseStep 4857175 = 7285763) B7285763
theorem B25904933 : Blo 1891435 25904933 := bstep (se 4 (by rfl) ⟨2428587, by rfl⟩ : syracuseStep 25904933 = 4857175) B4857175
theorem B17269955 : Blo 1891435 17269955 := bstep (se 1 (by rfl) ⟨12952466, by rfl⟩ : syracuseStep 17269955 = 25904933) B25904933
theorem B11513303 : Blo 1891435 11513303 := bstep (se 1 (by rfl) ⟨8634977, by rfl⟩ : syracuseStep 11513303 = 17269955) B17269955
theorem B7675535 : Blo 1891435 7675535 := bstep (se 1 (by rfl) ⟨5756651, by rfl⟩ : syracuseStep 7675535 = 11513303) B11513303
theorem B5117023 : Blo 1891435 5117023 := bstep (se 1 (by rfl) ⟨3837767, by rfl⟩ : syracuseStep 5117023 = 7675535) B7675535
theorem B27290789 : Blo 1891435 27290789 := bstep (se 4 (by rfl) ⟨2558511, by rfl⟩ : syracuseStep 27290789 = 5117023) B5117023
theorem B18193859 : Blo 1891435 18193859 := bstep (se 1 (by rfl) ⟨13645394, by rfl⟩ : syracuseStep 18193859 = 27290789) B27290789
theorem B12129239 : Blo 1891435 12129239 := bstep (se 1 (by rfl) ⟨9096929, by rfl⟩ : syracuseStep 12129239 = 18193859) B18193859
theorem B8086159 : Blo 1891435 8086159 := bstep (se 1 (by rfl) ⟨6064619, by rfl⟩ : syracuseStep 8086159 = 12129239) B12129239
theorem B10781545 : Blo 1891435 10781545 := bstep (se 2 (by rfl) ⟨4043079, by rfl⟩ : syracuseStep 10781545 = 8086159) B8086159
theorem B14375393 : Blo 1891435 14375393 := bstep (se 2 (by rfl) ⟨5390772, by rfl⟩ : syracuseStep 14375393 = 10781545) B10781545
theorem B9583595 : Blo 1891435 9583595 := bstep (se 1 (by rfl) ⟨7187696, by rfl⟩ : syracuseStep 9583595 = 14375393) B14375393
theorem B6389063 : Blo 1891435 6389063 := bstep (se 1 (by rfl) ⟨4791797, by rfl⟩ : syracuseStep 6389063 = 9583595) B9583595
theorem B4259375 : Blo 1891435 4259375 := bstep (se 1 (by rfl) ⟨3194531, by rfl⟩ : syracuseStep 4259375 = 6389063) B6389063
theorem B2839583 : Blo 1891435 2839583 := bstep (se 1 (by rfl) ⟨2129687, by rfl⟩ : syracuseStep 2839583 = 4259375) B4259375
theorem B1893055 : Blo 1891435 1893055 := bstep (se 1 (by rfl) ⟨1419791, by rfl⟩ : syracuseStep 1893055 = 2839583) B2839583
theorem B2839589 : Blo 1891435 2839589 := bbase (se 4 (by rfl) ⟨266211, by rfl⟩ : syracuseStep 2839589 = 532423) (by norm_num)
theorem B1893059 : Blo 1891435 1893059 := bstep (se 1 (by rfl) ⟨1419794, by rfl⟩ : syracuseStep 1893059 = 2839589) B2839589
theorem B2395909 : Blo 1891435 2395909 := bbase (se 4 (by rfl) ⟨224616, by rfl⟩ : syracuseStep 2395909 = 449233) (by norm_num)
theorem B3194545 : Blo 1891435 3194545 := bstep (se 2 (by rfl) ⟨1197954, by rfl⟩ : syracuseStep 3194545 = 2395909) B2395909
theorem B4259393 : Blo 1891435 4259393 := bstep (se 2 (by rfl) ⟨1597272, by rfl⟩ : syracuseStep 4259393 = 3194545) B3194545
theorem B2839595 : Blo 1891435 2839595 := bstep (se 1 (by rfl) ⟨2129696, by rfl⟩ : syracuseStep 2839595 = 4259393) B4259393
theorem B1893063 : Blo 1891435 1893063 := bstep (se 1 (by rfl) ⟨1419797, by rfl⟩ : syracuseStep 1893063 = 2839595) B2839595
theorem B2129701 : Blo 1891435 2129701 := bbase (se 4 (by rfl) ⟨199659, by rfl⟩ : syracuseStep 2129701 = 399319) (by norm_num)
theorem B2839601 : Blo 1891435 2839601 := bstep (se 2 (by rfl) ⟨1064850, by rfl⟩ : syracuseStep 2839601 = 2129701) B2129701
theorem B1893067 : Blo 1891435 1893067 := bstep (se 1 (by rfl) ⟨1419800, by rfl⟩ : syracuseStep 1893067 = 2839601) B2839601
theorem B8086229 : Blo 1891435 8086229 := bbase (se 7 (by rfl) ⟨94760, by rfl⟩ : syracuseStep 8086229 = 189521) (by norm_num)
theorem B5390819 : Blo 1891435 5390819 := bstep (se 1 (by rfl) ⟨4043114, by rfl⟩ : syracuseStep 5390819 = 8086229) B8086229
theorem B3593879 : Blo 1891435 3593879 := bstep (se 1 (by rfl) ⟨2695409, by rfl⟩ : syracuseStep 3593879 = 5390819) B5390819
theorem B2395919 : Blo 1891435 2395919 := bstep (se 1 (by rfl) ⟨1796939, by rfl⟩ : syracuseStep 2395919 = 3593879) B3593879
theorem B6389117 : Blo 1891435 6389117 := bstep (se 3 (by rfl) ⟨1197959, by rfl⟩ : syracuseStep 6389117 = 2395919) B2395919
theorem B4259411 : Blo 1891435 4259411 := bstep (se 1 (by rfl) ⟨3194558, by rfl⟩ : syracuseStep 4259411 = 6389117) B6389117
theorem B2839607 : Blo 1891435 2839607 := bstep (se 1 (by rfl) ⟨2129705, by rfl⟩ : syracuseStep 2839607 = 4259411) B4259411
theorem B1893071 : Blo 1891435 1893071 := bstep (se 1 (by rfl) ⟨1419803, by rfl⟩ : syracuseStep 1893071 = 2839607) B2839607
theorem B2839613 : Blo 1891435 2839613 := bbase (se 3 (by rfl) ⟨532427, by rfl⟩ : syracuseStep 2839613 = 1064855) (by norm_num)
theorem B1893075 : Blo 1891435 1893075 := bstep (se 1 (by rfl) ⟨1419806, by rfl⟩ : syracuseStep 1893075 = 2839613) B2839613
theorem B4259429 : Blo 1891435 4259429 := bbase (se 4 (by rfl) ⟨399321, by rfl⟩ : syracuseStep 4259429 = 798643) (by norm_num)
theorem B2839619 : Blo 1891435 2839619 := bstep (se 1 (by rfl) ⟨2129714, by rfl⟩ : syracuseStep 2839619 = 4259429) B4259429
theorem B1893079 : Blo 1891435 1893079 := bstep (se 1 (by rfl) ⟨1419809, by rfl⟩ : syracuseStep 1893079 = 2839619) B2839619
theorem B4791869 : Blo 1891435 4791869 := bbase (se 3 (by rfl) ⟨898475, by rfl⟩ : syracuseStep 4791869 = 1796951) (by norm_num)
theorem B3194579 : Blo 1891435 3194579 := bstep (se 1 (by rfl) ⟨2395934, by rfl⟩ : syracuseStep 3194579 = 4791869) B4791869
theorem B2129719 : Blo 1891435 2129719 := bstep (se 1 (by rfl) ⟨1597289, by rfl⟩ : syracuseStep 2129719 = 3194579) B3194579
theorem B2839625 : Blo 1891435 2839625 := bstep (se 2 (by rfl) ⟨1064859, by rfl⟩ : syracuseStep 2839625 = 2129719) B2129719
theorem B1893083 : Blo 1891435 1893083 := bstep (se 1 (by rfl) ⟨1419812, by rfl⟩ : syracuseStep 1893083 = 2839625) B2839625
theorem B3593909 : Blo 1891435 3593909 := bbase (se 5 (by rfl) ⟨168464, by rfl⟩ : syracuseStep 3593909 = 336929) (by norm_num)
theorem B9583757 : Blo 1891435 9583757 := bstep (se 3 (by rfl) ⟨1796954, by rfl⟩ : syracuseStep 9583757 = 3593909) B3593909
theorem B6389171 : Blo 1891435 6389171 := bstep (se 1 (by rfl) ⟨4791878, by rfl⟩ : syracuseStep 6389171 = 9583757) B9583757
theorem B4259447 : Blo 1891435 4259447 := bstep (se 1 (by rfl) ⟨3194585, by rfl⟩ : syracuseStep 4259447 = 6389171) B6389171
theorem B2839631 : Blo 1891435 2839631 := bstep (se 1 (by rfl) ⟨2129723, by rfl⟩ : syracuseStep 2839631 = 4259447) B4259447
theorem B1893087 : Blo 1891435 1893087 := bstep (se 1 (by rfl) ⟨1419815, by rfl⟩ : syracuseStep 1893087 = 2839631) B2839631
theorem B2839637 : Blo 1891435 2839637 := bbase (se 8 (by rfl) ⟨16638, by rfl⟩ : syracuseStep 2839637 = 33277) (by norm_num)
theorem B1893091 : Blo 1891435 1893091 := bstep (se 1 (by rfl) ⟨1419818, by rfl⟩ : syracuseStep 1893091 = 2839637) B2839637
theorem B13645685 : Blo 1891435 13645685 := bbase (se 5 (by rfl) ⟨639641, by rfl⟩ : syracuseStep 13645685 = 1279283) (by norm_num)
theorem B9097123 : Blo 1891435 9097123 := bstep (se 1 (by rfl) ⟨6822842, by rfl⟩ : syracuseStep 9097123 = 13645685) B13645685
theorem B12129497 : Blo 1891435 12129497 := bstep (se 2 (by rfl) ⟨4548561, by rfl⟩ : syracuseStep 12129497 = 9097123) B9097123
theorem B8086331 : Blo 1891435 8086331 := bstep (se 1 (by rfl) ⟨6064748, by rfl⟩ : syracuseStep 8086331 = 12129497) B12129497
theorem B5390887 : Blo 1891435 5390887 := bstep (se 1 (by rfl) ⟨4043165, by rfl⟩ : syracuseStep 5390887 = 8086331) B8086331
theorem B7187849 : Blo 1891435 7187849 := bstep (se 2 (by rfl) ⟨2695443, by rfl⟩ : syracuseStep 7187849 = 5390887) B5390887
theorem B4791899 : Blo 1891435 4791899 := bstep (se 1 (by rfl) ⟨3593924, by rfl⟩ : syracuseStep 4791899 = 7187849) B7187849
theorem B3194599 : Blo 1891435 3194599 := bstep (se 1 (by rfl) ⟨2395949, by rfl⟩ : syracuseStep 3194599 = 4791899) B4791899
theorem B4259465 : Blo 1891435 4259465 := bstep (se 2 (by rfl) ⟨1597299, by rfl⟩ : syracuseStep 4259465 = 3194599) B3194599
theorem B2839643 : Blo 1891435 2839643 := bstep (se 1 (by rfl) ⟨2129732, by rfl⟩ : syracuseStep 2839643 = 4259465) B4259465
theorem B1893095 : Blo 1891435 1893095 := bstep (se 1 (by rfl) ⟨1419821, by rfl⟩ : syracuseStep 1893095 = 2839643) B2839643
theorem B2129737 : Blo 1891435 2129737 := bbase (se 2 (by rfl) ⟨798651, by rfl⟩ : syracuseStep 2129737 = 1597303) (by norm_num)
theorem B2839649 : Blo 1891435 2839649 := bstep (se 2 (by rfl) ⟨1064868, by rfl⟩ : syracuseStep 2839649 = 2129737) B2129737
theorem B1893099 : Blo 1891435 1893099 := bstep (se 1 (by rfl) ⟨1419824, by rfl⟩ : syracuseStep 1893099 = 2839649) B2839649
theorem B10373941 : Blo 1891435 10373941 := bbase (se 5 (by rfl) ⟨486278, by rfl⟩ : syracuseStep 10373941 = 972557) (by norm_num)
theorem B13831921 : Blo 1891435 13831921 := bstep (se 2 (by rfl) ⟨5186970, by rfl⟩ : syracuseStep 13831921 = 10373941) B10373941
theorem B18442561 : Blo 1891435 18442561 := bstep (se 2 (by rfl) ⟨6915960, by rfl⟩ : syracuseStep 18442561 = 13831921) B13831921
theorem B24590081 : Blo 1891435 24590081 := bstep (se 2 (by rfl) ⟨9221280, by rfl⟩ : syracuseStep 24590081 = 18442561) B18442561
theorem B16393387 : Blo 1891435 16393387 := bstep (se 1 (by rfl) ⟨12295040, by rfl⟩ : syracuseStep 16393387 = 24590081) B24590081
theorem B21857849 : Blo 1891435 21857849 := bstep (se 2 (by rfl) ⟨8196693, by rfl⟩ : syracuseStep 21857849 = 16393387) B16393387
theorem B14571899 : Blo 1891435 14571899 := bstep (se 1 (by rfl) ⟨10928924, by rfl⟩ : syracuseStep 14571899 = 21857849) B21857849
theorem B9714599 : Blo 1891435 9714599 := bstep (se 1 (by rfl) ⟨7285949, by rfl⟩ : syracuseStep 9714599 = 14571899) B14571899
theorem B6476399 : Blo 1891435 6476399 := bstep (se 1 (by rfl) ⟨4857299, by rfl⟩ : syracuseStep 6476399 = 9714599) B9714599
theorem B4317599 : Blo 1891435 4317599 := bstep (se 1 (by rfl) ⟨3238199, by rfl⟩ : syracuseStep 4317599 = 6476399) B6476399
theorem B2878399 : Blo 1891435 2878399 := bstep (se 1 (by rfl) ⟨2158799, by rfl⟩ : syracuseStep 2878399 = 4317599) B4317599
theorem B3837865 : Blo 1891435 3837865 := bstep (se 2 (by rfl) ⟨1439199, by rfl⟩ : syracuseStep 3837865 = 2878399) B2878399
theorem B5117153 : Blo 1891435 5117153 := bstep (se 2 (by rfl) ⟨1918932, by rfl⟩ : syracuseStep 5117153 = 3837865) B3837865
theorem B13645741 : Blo 1891435 13645741 := bstep (se 3 (by rfl) ⟨2558576, by rfl⟩ : syracuseStep 13645741 = 5117153) B5117153
theorem B18194321 : Blo 1891435 18194321 := bstep (se 2 (by rfl) ⟨6822870, by rfl⟩ : syracuseStep 18194321 = 13645741) B13645741
theorem B12129547 : Blo 1891435 12129547 := bstep (se 1 (by rfl) ⟨9097160, by rfl⟩ : syracuseStep 12129547 = 18194321) B18194321
theorem B16172729 : Blo 1891435 16172729 := bstep (se 2 (by rfl) ⟨6064773, by rfl⟩ : syracuseStep 16172729 = 12129547) B12129547
theorem B10781819 : Blo 1891435 10781819 := bstep (se 1 (by rfl) ⟨8086364, by rfl⟩ : syracuseStep 10781819 = 16172729) B16172729
theorem B7187879 : Blo 1891435 7187879 := bstep (se 1 (by rfl) ⟨5390909, by rfl⟩ : syracuseStep 7187879 = 10781819) B10781819
theorem B4791919 : Blo 1891435 4791919 := bstep (se 1 (by rfl) ⟨3593939, by rfl⟩ : syracuseStep 4791919 = 7187879) B7187879
theorem B6389225 : Blo 1891435 6389225 := bstep (se 2 (by rfl) ⟨2395959, by rfl⟩ : syracuseStep 6389225 = 4791919) B4791919
theorem B4259483 : Blo 1891435 4259483 := bstep (se 1 (by rfl) ⟨3194612, by rfl⟩ : syracuseStep 4259483 = 6389225) B6389225
theorem B2839655 : Blo 1891435 2839655 := bstep (se 1 (by rfl) ⟨2129741, by rfl⟩ : syracuseStep 2839655 = 4259483) B4259483
theorem B1893103 : Blo 1891435 1893103 := bstep (se 1 (by rfl) ⟨1419827, by rfl⟩ : syracuseStep 1893103 = 2839655) B2839655
theorem B2839661 : Blo 1891435 2839661 := bbase (se 3 (by rfl) ⟨532436, by rfl⟩ : syracuseStep 2839661 = 1064873) (by norm_num)
theorem B1893107 : Blo 1891435 1893107 := bstep (se 1 (by rfl) ⟨1419830, by rfl⟩ : syracuseStep 1893107 = 2839661) B2839661
theorem B4259501 : Blo 1891435 4259501 := bbase (se 3 (by rfl) ⟨798656, by rfl⟩ : syracuseStep 4259501 = 1597313) (by norm_num)
theorem B2839667 : Blo 1891435 2839667 := bstep (se 1 (by rfl) ⟨2129750, by rfl⟩ : syracuseStep 2839667 = 4259501) B4259501
theorem B1893111 : Blo 1891435 1893111 := bstep (se 1 (by rfl) ⟨1419833, by rfl⟩ : syracuseStep 1893111 = 2839667) B2839667
theorem B6822917 : Blo 1891435 6822917 := bbase (se 4 (by rfl) ⟨639648, by rfl⟩ : syracuseStep 6822917 = 1279297) (by norm_num)
theorem B4548611 : Blo 1891435 4548611 := bstep (se 1 (by rfl) ⟨3411458, by rfl⟩ : syracuseStep 4548611 = 6822917) B6822917
theorem B3032407 : Blo 1891435 3032407 := bstep (se 1 (by rfl) ⟨2274305, by rfl⟩ : syracuseStep 3032407 = 4548611) B4548611
theorem B4043209 : Blo 1891435 4043209 := bstep (se 2 (by rfl) ⟨1516203, by rfl⟩ : syracuseStep 4043209 = 3032407) B3032407
theorem B5390945 : Blo 1891435 5390945 := bstep (se 2 (by rfl) ⟨2021604, by rfl⟩ : syracuseStep 5390945 = 4043209) B4043209
theorem B3593963 : Blo 1891435 3593963 := bstep (se 1 (by rfl) ⟨2695472, by rfl⟩ : syracuseStep 3593963 = 5390945) B5390945
theorem B2395975 : Blo 1891435 2395975 := bstep (se 1 (by rfl) ⟨1796981, by rfl⟩ : syracuseStep 2395975 = 3593963) B3593963
theorem B3194633 : Blo 1891435 3194633 := bstep (se 2 (by rfl) ⟨1197987, by rfl⟩ : syracuseStep 3194633 = 2395975) B2395975
theorem B2129755 : Blo 1891435 2129755 := bstep (se 1 (by rfl) ⟨1597316, by rfl⟩ : syracuseStep 2129755 = 3194633) B3194633
theorem B2839673 : Blo 1891435 2839673 := bstep (se 2 (by rfl) ⟨1064877, by rfl⟩ : syracuseStep 2839673 = 2129755) B2129755
theorem B1893115 : Blo 1891435 1893115 := bstep (se 1 (by rfl) ⟨1419836, by rfl⟩ : syracuseStep 1893115 = 2839673) B2839673
theorem B29541653 : Blo 1891435 29541653 := bbase (se 6 (by rfl) ⟨692382, by rfl⟩ : syracuseStep 29541653 = 1384765) (by norm_num)
theorem B19694435 : Blo 1891435 19694435 := bstep (se 1 (by rfl) ⟨14770826, by rfl⟩ : syracuseStep 19694435 = 29541653) B29541653
theorem B52518493 : Blo 1891435 52518493 := bstep (se 3 (by rfl) ⟨9847217, by rfl⟩ : syracuseStep 52518493 = 19694435) B19694435
theorem B70024657 : Blo 1891435 70024657 := bstep (se 2 (by rfl) ⟨26259246, by rfl⟩ : syracuseStep 70024657 = 52518493) B52518493
theorem B93366209 : Blo 1891435 93366209 := bstep (se 2 (by rfl) ⟨35012328, by rfl⟩ : syracuseStep 93366209 = 70024657) B70024657
theorem B62244139 : Blo 1891435 62244139 := bstep (se 1 (by rfl) ⟨46683104, by rfl⟩ : syracuseStep 62244139 = 93366209) B93366209
theorem B82992185 : Blo 1891435 82992185 := bstep (se 2 (by rfl) ⟨31122069, by rfl⟩ : syracuseStep 82992185 = 62244139) B62244139
theorem B55328123 : Blo 1891435 55328123 := bstep (se 1 (by rfl) ⟨41496092, by rfl⟩ : syracuseStep 55328123 = 82992185) B82992185
theorem B36885415 : Blo 1891435 36885415 := bstep (se 1 (by rfl) ⟨27664061, by rfl⟩ : syracuseStep 36885415 = 55328123) B55328123
theorem B49180553 : Blo 1891435 49180553 := bstep (se 2 (by rfl) ⟨18442707, by rfl⟩ : syracuseStep 49180553 = 36885415) B36885415
theorem B32787035 : Blo 1891435 32787035 := bstep (se 1 (by rfl) ⟨24590276, by rfl⟩ : syracuseStep 32787035 = 49180553) B49180553
theorem B21858023 : Blo 1891435 21858023 := bstep (se 1 (by rfl) ⟨16393517, by rfl⟩ : syracuseStep 21858023 = 32787035) B32787035
theorem B58288061 : Blo 1891435 58288061 := bstep (se 3 (by rfl) ⟨10929011, by rfl⟩ : syracuseStep 58288061 = 21858023) B21858023
theorem B38858707 : Blo 1891435 38858707 := bstep (se 1 (by rfl) ⟨29144030, by rfl⟩ : syracuseStep 38858707 = 58288061) B58288061
theorem B51811609 : Blo 1891435 51811609 := bstep (se 2 (by rfl) ⟨19429353, by rfl⟩ : syracuseStep 51811609 = 38858707) B38858707
theorem B69082145 : Blo 1891435 69082145 := bstep (se 2 (by rfl) ⟨25905804, by rfl⟩ : syracuseStep 69082145 = 51811609) B51811609
theorem B46054763 : Blo 1891435 46054763 := bstep (se 1 (by rfl) ⟨34541072, by rfl⟩ : syracuseStep 46054763 = 69082145) B69082145
theorem B30703175 : Blo 1891435 30703175 := bstep (se 1 (by rfl) ⟨23027381, by rfl⟩ : syracuseStep 30703175 = 46054763) B46054763
theorem B20468783 : Blo 1891435 20468783 := bstep (se 1 (by rfl) ⟨15351587, by rfl⟩ : syracuseStep 20468783 = 30703175) B30703175
theorem B13645855 : Blo 1891435 13645855 := bstep (se 1 (by rfl) ⟨10234391, by rfl⟩ : syracuseStep 13645855 = 20468783) B20468783
theorem B18194473 : Blo 1891435 18194473 := bstep (se 2 (by rfl) ⟨6822927, by rfl⟩ : syracuseStep 18194473 = 13645855) B13645855
theorem B24259297 : Blo 1891435 24259297 := bstep (se 2 (by rfl) ⟨9097236, by rfl⟩ : syracuseStep 24259297 = 18194473) B18194473
theorem B32345729 : Blo 1891435 32345729 := bstep (se 2 (by rfl) ⟨12129648, by rfl⟩ : syracuseStep 32345729 = 24259297) B24259297
theorem B21563819 : Blo 1891435 21563819 := bstep (se 1 (by rfl) ⟨16172864, by rfl⟩ : syracuseStep 21563819 = 32345729) B32345729
theorem B14375879 : Blo 1891435 14375879 := bstep (se 1 (by rfl) ⟨10781909, by rfl⟩ : syracuseStep 14375879 = 21563819) B21563819
theorem B9583919 : Blo 1891435 9583919 := bstep (se 1 (by rfl) ⟨7187939, by rfl⟩ : syracuseStep 9583919 = 14375879) B14375879
theorem B6389279 : Blo 1891435 6389279 := bstep (se 1 (by rfl) ⟨4791959, by rfl⟩ : syracuseStep 6389279 = 9583919) B9583919
theorem B4259519 : Blo 1891435 4259519 := bstep (se 1 (by rfl) ⟨3194639, by rfl⟩ : syracuseStep 4259519 = 6389279) B6389279
theorem B2839679 : Blo 1891435 2839679 := bstep (se 1 (by rfl) ⟨2129759, by rfl⟩ : syracuseStep 2839679 = 4259519) B4259519
theorem B1893119 : Blo 1891435 1893119 := bstep (se 1 (by rfl) ⟨1419839, by rfl⟩ : syracuseStep 1893119 = 2839679) B2839679
theorem B2839685 : Blo 1891435 2839685 := bbase (se 4 (by rfl) ⟨266220, by rfl⟩ : syracuseStep 2839685 = 532441) (by norm_num)
theorem B1893123 : Blo 1891435 1893123 := bstep (se 1 (by rfl) ⟨1419842, by rfl⟩ : syracuseStep 1893123 = 2839685) B2839685
theorem B3194653 : Blo 1891435 3194653 := bbase (se 3 (by rfl) ⟨598997, by rfl⟩ : syracuseStep 3194653 = 1197995) (by norm_num)
theorem B4259537 : Blo 1891435 4259537 := bstep (se 2 (by rfl) ⟨1597326, by rfl⟩ : syracuseStep 4259537 = 3194653) B3194653
theorem B2839691 : Blo 1891435 2839691 := bstep (se 1 (by rfl) ⟨2129768, by rfl⟩ : syracuseStep 2839691 = 4259537) B4259537
theorem B1893127 : Blo 1891435 1893127 := bstep (se 1 (by rfl) ⟨1419845, by rfl⟩ : syracuseStep 1893127 = 2839691) B2839691
theorem B2129773 : Blo 1891435 2129773 := bbase (se 3 (by rfl) ⟨399332, by rfl⟩ : syracuseStep 2129773 = 798665) (by norm_num)
theorem B2839697 : Blo 1891435 2839697 := bstep (se 2 (by rfl) ⟨1064886, by rfl⟩ : syracuseStep 2839697 = 2129773) B2129773
theorem B1893131 : Blo 1891435 1893131 := bstep (se 1 (by rfl) ⟨1419848, by rfl⟩ : syracuseStep 1893131 = 2839697) B2839697
theorem B6389333 : Blo 1891435 6389333 := bbase (se 8 (by rfl) ⟨37437, by rfl⟩ : syracuseStep 6389333 = 74875) (by norm_num)
theorem B4259555 : Blo 1891435 4259555 := bstep (se 1 (by rfl) ⟨3194666, by rfl⟩ : syracuseStep 4259555 = 6389333) B6389333
theorem B2839703 : Blo 1891435 2839703 := bstep (se 1 (by rfl) ⟨2129777, by rfl⟩ : syracuseStep 2839703 = 4259555) B4259555
theorem B1893135 : Blo 1891435 1893135 := bstep (se 1 (by rfl) ⟨1419851, by rfl⟩ : syracuseStep 1893135 = 2839703) B2839703
theorem B2839709 : Blo 1891435 2839709 := bbase (se 3 (by rfl) ⟨532445, by rfl⟩ : syracuseStep 2839709 = 1064891) (by norm_num)
theorem B1893139 : Blo 1891435 1893139 := bstep (se 1 (by rfl) ⟨1419854, by rfl⟩ : syracuseStep 1893139 = 2839709) B2839709
theorem B4259573 : Blo 1891435 4259573 := bbase (se 5 (by rfl) ⟨199667, by rfl⟩ : syracuseStep 4259573 = 399335) (by norm_num)
theorem B2839715 : Blo 1891435 2839715 := bstep (se 1 (by rfl) ⟨2129786, by rfl⟩ : syracuseStep 2839715 = 4259573) B4259573
theorem B1893143 : Blo 1891435 1893143 := bstep (se 1 (by rfl) ⟨1419857, by rfl⟩ : syracuseStep 1893143 = 2839715) B2839715
theorem B5756933 : Blo 1891435 5756933 := bbase (se 4 (by rfl) ⟨539712, by rfl⟩ : syracuseStep 5756933 = 1079425) (by norm_num)
theorem B3837955 : Blo 1891435 3837955 := bstep (se 1 (by rfl) ⟨2878466, by rfl⟩ : syracuseStep 3837955 = 5756933) B5756933
theorem B5117273 : Blo 1891435 5117273 := bstep (se 2 (by rfl) ⟨1918977, by rfl⟩ : syracuseStep 5117273 = 3837955) B3837955
theorem B3411515 : Blo 1891435 3411515 := bstep (se 1 (by rfl) ⟨2558636, by rfl⟩ : syracuseStep 3411515 = 5117273) B5117273
theorem B9097373 : Blo 1891435 9097373 := bstep (se 3 (by rfl) ⟨1705757, by rfl⟩ : syracuseStep 9097373 = 3411515) B3411515
theorem B24259661 : Blo 1891435 24259661 := bstep (se 3 (by rfl) ⟨4548686, by rfl⟩ : syracuseStep 24259661 = 9097373) B9097373
theorem B16173107 : Blo 1891435 16173107 := bstep (se 1 (by rfl) ⟨12129830, by rfl⟩ : syracuseStep 16173107 = 24259661) B24259661
theorem B10782071 : Blo 1891435 10782071 := bstep (se 1 (by rfl) ⟨8086553, by rfl⟩ : syracuseStep 10782071 = 16173107) B16173107
theorem B7188047 : Blo 1891435 7188047 := bstep (se 1 (by rfl) ⟨5391035, by rfl⟩ : syracuseStep 7188047 = 10782071) B10782071
theorem B4792031 : Blo 1891435 4792031 := bstep (se 1 (by rfl) ⟨3594023, by rfl⟩ : syracuseStep 4792031 = 7188047) B7188047
theorem B3194687 : Blo 1891435 3194687 := bstep (se 1 (by rfl) ⟨2396015, by rfl⟩ : syracuseStep 3194687 = 4792031) B4792031
theorem B2129791 : Blo 1891435 2129791 := bstep (se 1 (by rfl) ⟨1597343, by rfl⟩ : syracuseStep 2129791 = 3194687) B3194687
theorem B2839721 : Blo 1891435 2839721 := bstep (se 2 (by rfl) ⟨1064895, by rfl⟩ : syracuseStep 2839721 = 2129791) B2129791
theorem B1893147 : Blo 1891435 1893147 := bstep (se 1 (by rfl) ⟨1419860, by rfl⟩ : syracuseStep 1893147 = 2839721) B2839721
theorem B4043285 : Blo 1891435 4043285 := bbase (se 6 (by rfl) ⟨94764, by rfl⟩ : syracuseStep 4043285 = 189529) (by norm_num)
theorem B2695523 : Blo 1891435 2695523 := bstep (se 1 (by rfl) ⟨2021642, by rfl⟩ : syracuseStep 2695523 = 4043285) B4043285
theorem B7188061 : Blo 1891435 7188061 := bstep (se 3 (by rfl) ⟨1347761, by rfl⟩ : syracuseStep 7188061 = 2695523) B2695523
theorem B9584081 : Blo 1891435 9584081 := bstep (se 2 (by rfl) ⟨3594030, by rfl⟩ : syracuseStep 9584081 = 7188061) B7188061
theorem B6389387 : Blo 1891435 6389387 := bstep (se 1 (by rfl) ⟨4792040, by rfl⟩ : syracuseStep 6389387 = 9584081) B9584081
theorem B4259591 : Blo 1891435 4259591 := bstep (se 1 (by rfl) ⟨3194693, by rfl⟩ : syracuseStep 4259591 = 6389387) B6389387
theorem B2839727 : Blo 1891435 2839727 := bstep (se 1 (by rfl) ⟨2129795, by rfl⟩ : syracuseStep 2839727 = 4259591) B4259591
theorem B1893151 : Blo 1891435 1893151 := bstep (se 1 (by rfl) ⟨1419863, by rfl⟩ : syracuseStep 1893151 = 2839727) B2839727
theorem B2839733 : Blo 1891435 2839733 := bbase (se 5 (by rfl) ⟨133112, by rfl⟩ : syracuseStep 2839733 = 266225) (by norm_num)
theorem B1893155 : Blo 1891435 1893155 := bstep (se 1 (by rfl) ⟨1419866, by rfl⟩ : syracuseStep 1893155 = 2839733) B2839733
theorem B4792061 : Blo 1891435 4792061 := bbase (se 3 (by rfl) ⟨898511, by rfl⟩ : syracuseStep 4792061 = 1797023) (by norm_num)
theorem B3194707 : Blo 1891435 3194707 := bstep (se 1 (by rfl) ⟨2396030, by rfl⟩ : syracuseStep 3194707 = 4792061) B4792061
theorem B4259609 : Blo 1891435 4259609 := bstep (se 2 (by rfl) ⟨1597353, by rfl⟩ : syracuseStep 4259609 = 3194707) B3194707
theorem B2839739 : Blo 1891435 2839739 := bstep (se 1 (by rfl) ⟨2129804, by rfl⟩ : syracuseStep 2839739 = 4259609) B4259609
theorem B1893159 : Blo 1891435 1893159 := bstep (se 1 (by rfl) ⟨1419869, by rfl⟩ : syracuseStep 1893159 = 2839739) B2839739
theorem B2129809 : Blo 1891435 2129809 := bbase (se 2 (by rfl) ⟨798678, by rfl⟩ : syracuseStep 2129809 = 1597357) (by norm_num)
theorem B2839745 : Blo 1891435 2839745 := bstep (se 2 (by rfl) ⟨1064904, by rfl⟩ : syracuseStep 2839745 = 2129809) B2129809
theorem B1893163 : Blo 1891435 1893163 := bstep (se 1 (by rfl) ⟨1419872, by rfl⟩ : syracuseStep 1893163 = 2839745) B2839745
theorem B3594061 : Blo 1891435 3594061 := bbase (se 3 (by rfl) ⟨673886, by rfl⟩ : syracuseStep 3594061 = 1347773) (by norm_num)
theorem B4792081 : Blo 1891435 4792081 := bstep (se 2 (by rfl) ⟨1797030, by rfl⟩ : syracuseStep 4792081 = 3594061) B3594061
theorem B6389441 : Blo 1891435 6389441 := bstep (se 2 (by rfl) ⟨2396040, by rfl⟩ : syracuseStep 6389441 = 4792081) B4792081
theorem B4259627 : Blo 1891435 4259627 := bstep (se 1 (by rfl) ⟨3194720, by rfl⟩ : syracuseStep 4259627 = 6389441) B6389441
theorem B2839751 : Blo 1891435 2839751 := bstep (se 1 (by rfl) ⟨2129813, by rfl⟩ : syracuseStep 2839751 = 4259627) B4259627
theorem B1893167 : Blo 1891435 1893167 := bstep (se 1 (by rfl) ⟨1419875, by rfl⟩ : syracuseStep 1893167 = 2839751) B2839751
theorem B2839757 : Blo 1891435 2839757 := bbase (se 3 (by rfl) ⟨532454, by rfl⟩ : syracuseStep 2839757 = 1064909) (by norm_num)
theorem B1893171 : Blo 1891435 1893171 := bstep (se 1 (by rfl) ⟨1419878, by rfl⟩ : syracuseStep 1893171 = 2839757) B2839757
theorem B4259645 : Blo 1891435 4259645 := bbase (se 3 (by rfl) ⟨798683, by rfl⟩ : syracuseStep 4259645 = 1597367) (by norm_num)
theorem B2839763 : Blo 1891435 2839763 := bstep (se 1 (by rfl) ⟨2129822, by rfl⟩ : syracuseStep 2839763 = 4259645) B4259645
theorem B1893175 : Blo 1891435 1893175 := bstep (se 1 (by rfl) ⟨1419881, by rfl⟩ : syracuseStep 1893175 = 2839763) B2839763
theorem B3194741 : Blo 1891435 3194741 := bbase (se 5 (by rfl) ⟨149753, by rfl⟩ : syracuseStep 3194741 = 299507) (by norm_num)
theorem B2129827 : Blo 1891435 2129827 := bstep (se 1 (by rfl) ⟨1597370, by rfl⟩ : syracuseStep 2129827 = 3194741) B3194741
theorem B2839769 : Blo 1891435 2839769 := bstep (se 2 (by rfl) ⟨1064913, by rfl⟩ : syracuseStep 2839769 = 2129827) B2129827
theorem B1893179 : Blo 1891435 1893179 := bstep (se 1 (by rfl) ⟨1419884, by rfl⟩ : syracuseStep 1893179 = 2839769) B2839769
theorem B4548773 : Blo 1891435 4548773 := bbase (se 4 (by rfl) ⟨426447, by rfl⟩ : syracuseStep 4548773 = 852895) (by norm_num)
theorem B3032515 : Blo 1891435 3032515 := bstep (se 1 (by rfl) ⟨2274386, by rfl⟩ : syracuseStep 3032515 = 4548773) B4548773
theorem B4043353 : Blo 1891435 4043353 := bstep (se 2 (by rfl) ⟨1516257, by rfl⟩ : syracuseStep 4043353 = 3032515) B3032515
theorem B5391137 : Blo 1891435 5391137 := bstep (se 2 (by rfl) ⟨2021676, by rfl⟩ : syracuseStep 5391137 = 4043353) B4043353
theorem B14376365 : Blo 1891435 14376365 := bstep (se 3 (by rfl) ⟨2695568, by rfl⟩ : syracuseStep 14376365 = 5391137) B5391137
theorem B9584243 : Blo 1891435 9584243 := bstep (se 1 (by rfl) ⟨7188182, by rfl⟩ : syracuseStep 9584243 = 14376365) B14376365
theorem B6389495 : Blo 1891435 6389495 := bstep (se 1 (by rfl) ⟨4792121, by rfl⟩ : syracuseStep 6389495 = 9584243) B9584243
theorem B4259663 : Blo 1891435 4259663 := bstep (se 1 (by rfl) ⟨3194747, by rfl⟩ : syracuseStep 4259663 = 6389495) B6389495
theorem B2839775 : Blo 1891435 2839775 := bstep (se 1 (by rfl) ⟨2129831, by rfl⟩ : syracuseStep 2839775 = 4259663) B4259663
theorem B1893183 : Blo 1891435 1893183 := bstep (se 1 (by rfl) ⟨1419887, by rfl⟩ : syracuseStep 1893183 = 2839775) B2839775
theorem B2839781 : Blo 1891435 2839781 := bbase (se 4 (by rfl) ⟨266229, by rfl⟩ : syracuseStep 2839781 = 532459) (by norm_num)
theorem B1893187 : Blo 1891435 1893187 := bstep (se 1 (by rfl) ⟨1419890, by rfl⟩ : syracuseStep 1893187 = 2839781) B2839781
theorem B3838045 : Blo 1891435 3838045 := bbase (se 3 (by rfl) ⟨719633, by rfl⟩ : syracuseStep 3838045 = 1439267) (by norm_num)
theorem B5117393 : Blo 1891435 5117393 := bstep (se 2 (by rfl) ⟨1919022, by rfl⟩ : syracuseStep 5117393 = 3838045) B3838045
theorem B3411595 : Blo 1891435 3411595 := bstep (se 1 (by rfl) ⟨2558696, by rfl⟩ : syracuseStep 3411595 = 5117393) B5117393
theorem B4548793 : Blo 1891435 4548793 := bstep (se 2 (by rfl) ⟨1705797, by rfl⟩ : syracuseStep 4548793 = 3411595) B3411595
theorem B6065057 : Blo 1891435 6065057 := bstep (se 2 (by rfl) ⟨2274396, by rfl⟩ : syracuseStep 6065057 = 4548793) B4548793
theorem B4043371 : Blo 1891435 4043371 := bstep (se 1 (by rfl) ⟨3032528, by rfl⟩ : syracuseStep 4043371 = 6065057) B6065057
theorem B5391161 : Blo 1891435 5391161 := bstep (se 2 (by rfl) ⟨2021685, by rfl⟩ : syracuseStep 5391161 = 4043371) B4043371
theorem B3594107 : Blo 1891435 3594107 := bstep (se 1 (by rfl) ⟨2695580, by rfl⟩ : syracuseStep 3594107 = 5391161) B5391161
theorem B2396071 : Blo 1891435 2396071 := bstep (se 1 (by rfl) ⟨1797053, by rfl⟩ : syracuseStep 2396071 = 3594107) B3594107
theorem B3194761 : Blo 1891435 3194761 := bstep (se 2 (by rfl) ⟨1198035, by rfl⟩ : syracuseStep 3194761 = 2396071) B2396071
theorem B4259681 : Blo 1891435 4259681 := bstep (se 2 (by rfl) ⟨1597380, by rfl⟩ : syracuseStep 4259681 = 3194761) B3194761
theorem B2839787 : Blo 1891435 2839787 := bstep (se 1 (by rfl) ⟨2129840, by rfl⟩ : syracuseStep 2839787 = 4259681) B4259681
theorem B1893191 : Blo 1891435 1893191 := bstep (se 1 (by rfl) ⟨1419893, by rfl⟩ : syracuseStep 1893191 = 2839787) B2839787
theorem B2129845 : Blo 1891435 2129845 := bbase (se 5 (by rfl) ⟨99836, by rfl⟩ : syracuseStep 2129845 = 199673) (by norm_num)
theorem B2839793 : Blo 1891435 2839793 := bstep (se 2 (by rfl) ⟨1064922, by rfl⟩ : syracuseStep 2839793 = 2129845) B2129845
theorem B1893195 : Blo 1891435 1893195 := bstep (se 1 (by rfl) ⟨1419896, by rfl⟩ : syracuseStep 1893195 = 2839793) B2839793
theorem B2396081 : Blo 1891435 2396081 := bbase (se 2 (by rfl) ⟨898530, by rfl⟩ : syracuseStep 2396081 = 1797061) (by norm_num)
theorem B6389549 : Blo 1891435 6389549 := bstep (se 3 (by rfl) ⟨1198040, by rfl⟩ : syracuseStep 6389549 = 2396081) B2396081
theorem B4259699 : Blo 1891435 4259699 := bstep (se 1 (by rfl) ⟨3194774, by rfl⟩ : syracuseStep 4259699 = 6389549) B6389549
theorem B2839799 : Blo 1891435 2839799 := bstep (se 1 (by rfl) ⟨2129849, by rfl⟩ : syracuseStep 2839799 = 4259699) B4259699
theorem B1893199 : Blo 1891435 1893199 := bstep (se 1 (by rfl) ⟨1419899, by rfl⟩ : syracuseStep 1893199 = 2839799) B2839799
theorem B2839805 : Blo 1891435 2839805 := bbase (se 3 (by rfl) ⟨532463, by rfl⟩ : syracuseStep 2839805 = 1064927) (by norm_num)
theorem B1893203 : Blo 1891435 1893203 := bstep (se 1 (by rfl) ⟨1419902, by rfl⟩ : syracuseStep 1893203 = 2839805) B2839805
theorem B4259717 : Blo 1891435 4259717 := bbase (se 4 (by rfl) ⟨399348, by rfl⟩ : syracuseStep 4259717 = 798697) (by norm_num)
theorem B2839811 : Blo 1891435 2839811 := bstep (se 1 (by rfl) ⟨2129858, by rfl⟩ : syracuseStep 2839811 = 4259717) B4259717
theorem B1893207 : Blo 1891435 1893207 := bstep (se 1 (by rfl) ⟨1419905, by rfl⟩ : syracuseStep 1893207 = 2839811) B2839811
theorem B2274421 : Blo 1891435 2274421 := bbase (se 5 (by rfl) ⟨106613, by rfl⟩ : syracuseStep 2274421 = 213227) (by norm_num)
theorem B3032561 : Blo 1891435 3032561 := bstep (se 2 (by rfl) ⟨1137210, by rfl⟩ : syracuseStep 3032561 = 2274421) B2274421
theorem B2021707 : Blo 1891435 2021707 := bstep (se 1 (by rfl) ⟨1516280, by rfl⟩ : syracuseStep 2021707 = 3032561) B3032561
theorem B2695609 : Blo 1891435 2695609 := bstep (se 2 (by rfl) ⟨1010853, by rfl⟩ : syracuseStep 2695609 = 2021707) B2021707
theorem B3594145 : Blo 1891435 3594145 := bstep (se 2 (by rfl) ⟨1347804, by rfl⟩ : syracuseStep 3594145 = 2695609) B2695609
theorem B4792193 : Blo 1891435 4792193 := bstep (se 2 (by rfl) ⟨1797072, by rfl⟩ : syracuseStep 4792193 = 3594145) B3594145
theorem B3194795 : Blo 1891435 3194795 := bstep (se 1 (by rfl) ⟨2396096, by rfl⟩ : syracuseStep 3194795 = 4792193) B4792193
theorem B2129863 : Blo 1891435 2129863 := bstep (se 1 (by rfl) ⟨1597397, by rfl⟩ : syracuseStep 2129863 = 3194795) B3194795
theorem B2839817 : Blo 1891435 2839817 := bstep (se 2 (by rfl) ⟨1064931, by rfl⟩ : syracuseStep 2839817 = 2129863) B2129863
theorem B1893211 : Blo 1891435 1893211 := bstep (se 1 (by rfl) ⟨1419908, by rfl⟩ : syracuseStep 1893211 = 2839817) B2839817
theorem B9584405 : Blo 1891435 9584405 := bbase (se 6 (by rfl) ⟨224634, by rfl⟩ : syracuseStep 9584405 = 449269) (by norm_num)
theorem B6389603 : Blo 1891435 6389603 := bstep (se 1 (by rfl) ⟨4792202, by rfl⟩ : syracuseStep 6389603 = 9584405) B9584405
theorem B4259735 : Blo 1891435 4259735 := bstep (se 1 (by rfl) ⟨3194801, by rfl⟩ : syracuseStep 4259735 = 6389603) B6389603
theorem B2839823 : Blo 1891435 2839823 := bstep (se 1 (by rfl) ⟨2129867, by rfl⟩ : syracuseStep 2839823 = 4259735) B4259735
theorem B1893215 : Blo 1891435 1893215 := bstep (se 1 (by rfl) ⟨1419911, by rfl⟩ : syracuseStep 1893215 = 2839823) B2839823
theorem B2839829 : Blo 1891435 2839829 := bbase (se 6 (by rfl) ⟨66558, by rfl⟩ : syracuseStep 2839829 = 133117) (by norm_num)
theorem B1893219 : Blo 1891435 1893219 := bstep (se 1 (by rfl) ⟨1419914, by rfl⟩ : syracuseStep 1893219 = 2839829) B2839829
theorem B11514325 : Blo 1891435 11514325 := bbase (se 7 (by rfl) ⟨134933, by rfl⟩ : syracuseStep 11514325 = 269867) (by norm_num)
theorem B15352433 : Blo 1891435 15352433 := bstep (se 2 (by rfl) ⟨5757162, by rfl⟩ : syracuseStep 15352433 = 11514325) B11514325
theorem B10234955 : Blo 1891435 10234955 := bstep (se 1 (by rfl) ⟨7676216, by rfl⟩ : syracuseStep 10234955 = 15352433) B15352433
theorem B27293213 : Blo 1891435 27293213 := bstep (se 3 (by rfl) ⟨5117477, by rfl⟩ : syracuseStep 27293213 = 10234955) B10234955
theorem B18195475 : Blo 1891435 18195475 := bstep (se 1 (by rfl) ⟨13646606, by rfl⟩ : syracuseStep 18195475 = 27293213) B27293213
theorem B24260633 : Blo 1891435 24260633 := bstep (se 2 (by rfl) ⟨9097737, by rfl⟩ : syracuseStep 24260633 = 18195475) B18195475
theorem B16173755 : Blo 1891435 16173755 := bstep (se 1 (by rfl) ⟨12130316, by rfl⟩ : syracuseStep 16173755 = 24260633) B24260633
theorem B10782503 : Blo 1891435 10782503 := bstep (se 1 (by rfl) ⟨8086877, by rfl⟩ : syracuseStep 10782503 = 16173755) B16173755
theorem B7188335 : Blo 1891435 7188335 := bstep (se 1 (by rfl) ⟨5391251, by rfl⟩ : syracuseStep 7188335 = 10782503) B10782503
theorem B4792223 : Blo 1891435 4792223 := bstep (se 1 (by rfl) ⟨3594167, by rfl⟩ : syracuseStep 4792223 = 7188335) B7188335
theorem B3194815 : Blo 1891435 3194815 := bstep (se 1 (by rfl) ⟨2396111, by rfl⟩ : syracuseStep 3194815 = 4792223) B4792223
theorem B4259753 : Blo 1891435 4259753 := bstep (se 2 (by rfl) ⟨1597407, by rfl⟩ : syracuseStep 4259753 = 3194815) B3194815
theorem B2839835 : Blo 1891435 2839835 := bstep (se 1 (by rfl) ⟨2129876, by rfl⟩ : syracuseStep 2839835 = 4259753) B4259753
theorem B1893223 : Blo 1891435 1893223 := bstep (se 1 (by rfl) ⟨1419917, by rfl⟩ : syracuseStep 1893223 = 2839835) B2839835
theorem B2129881 : Blo 1891435 2129881 := bbase (se 2 (by rfl) ⟨798705, by rfl⟩ : syracuseStep 2129881 = 1597411) (by norm_num)
theorem B2839841 : Blo 1891435 2839841 := bstep (se 2 (by rfl) ⟨1064940, by rfl⟩ : syracuseStep 2839841 = 2129881) B2129881
theorem B1893227 : Blo 1891435 1893227 := bstep (se 1 (by rfl) ⟨1419920, by rfl⟩ : syracuseStep 1893227 = 2839841) B2839841
theorem B2695637 : Blo 1891435 2695637 := bbase (se 7 (by rfl) ⟨31589, by rfl⟩ : syracuseStep 2695637 = 63179) (by norm_num)
theorem B7188365 : Blo 1891435 7188365 := bstep (se 3 (by rfl) ⟨1347818, by rfl⟩ : syracuseStep 7188365 = 2695637) B2695637
theorem B4792243 : Blo 1891435 4792243 := bstep (se 1 (by rfl) ⟨3594182, by rfl⟩ : syracuseStep 4792243 = 7188365) B7188365
theorem B6389657 : Blo 1891435 6389657 := bstep (se 2 (by rfl) ⟨2396121, by rfl⟩ : syracuseStep 6389657 = 4792243) B4792243
theorem B4259771 : Blo 1891435 4259771 := bstep (se 1 (by rfl) ⟨3194828, by rfl⟩ : syracuseStep 4259771 = 6389657) B6389657
theorem B2839847 : Blo 1891435 2839847 := bstep (se 1 (by rfl) ⟨2129885, by rfl⟩ : syracuseStep 2839847 = 4259771) B4259771
theorem B1893231 : Blo 1891435 1893231 := bstep (se 1 (by rfl) ⟨1419923, by rfl⟩ : syracuseStep 1893231 = 2839847) B2839847
theorem B2839853 : Blo 1891435 2839853 := bbase (se 3 (by rfl) ⟨532472, by rfl⟩ : syracuseStep 2839853 = 1064945) (by norm_num)
theorem B1893235 : Blo 1891435 1893235 := bstep (se 1 (by rfl) ⟨1419926, by rfl⟩ : syracuseStep 1893235 = 2839853) B2839853
theorem B4259789 : Blo 1891435 4259789 := bbase (se 3 (by rfl) ⟨798710, by rfl⟩ : syracuseStep 4259789 = 1597421) (by norm_num)
theorem B2839859 : Blo 1891435 2839859 := bstep (se 1 (by rfl) ⟨2129894, by rfl⟩ : syracuseStep 2839859 = 4259789) B4259789
theorem B1893239 : Blo 1891435 1893239 := bstep (se 1 (by rfl) ⟨1419929, by rfl⟩ : syracuseStep 1893239 = 2839859) B2839859
theorem B2396137 : Blo 1891435 2396137 := bbase (se 2 (by rfl) ⟨898551, by rfl⟩ : syracuseStep 2396137 = 1797103) (by norm_num)
theorem B3194849 : Blo 1891435 3194849 := bstep (se 2 (by rfl) ⟨1198068, by rfl⟩ : syracuseStep 3194849 = 2396137) B2396137
theorem B2129899 : Blo 1891435 2129899 := bstep (se 1 (by rfl) ⟨1597424, by rfl⟩ : syracuseStep 2129899 = 3194849) B3194849
theorem B2839865 : Blo 1891435 2839865 := bstep (se 2 (by rfl) ⟨1064949, by rfl⟩ : syracuseStep 2839865 = 2129899) B2129899
theorem B1893243 : Blo 1891435 1893243 := bstep (se 1 (by rfl) ⟨1419932, by rfl⟩ : syracuseStep 1893243 = 2839865) B2839865
theorem B2105633 : Blo 1891435 2105633 := bbase (se 2 (by rfl) ⟨789612, by rfl⟩ : syracuseStep 2105633 = 1579225) (by norm_num)
theorem B5615021 : Blo 1891435 5615021 := bstep (se 3 (by rfl) ⟨1052816, by rfl⟩ : syracuseStep 5615021 = 2105633) B2105633
theorem B3743347 : Blo 1891435 3743347 := bstep (se 1 (by rfl) ⟨2807510, by rfl⟩ : syracuseStep 3743347 = 5615021) B5615021
theorem B4991129 : Blo 1891435 4991129 := bstep (se 2 (by rfl) ⟨1871673, by rfl⟩ : syracuseStep 4991129 = 3743347) B3743347
theorem B3327419 : Blo 1891435 3327419 := bstep (se 1 (by rfl) ⟨2495564, by rfl⟩ : syracuseStep 3327419 = 4991129) B4991129
theorem B2218279 : Blo 1891435 2218279 := bstep (se 1 (by rfl) ⟨1663709, by rfl⟩ : syracuseStep 2218279 = 3327419) B3327419
theorem B2957705 : Blo 1891435 2957705 := bstep (se 2 (by rfl) ⟨1109139, by rfl⟩ : syracuseStep 2957705 = 2218279) B2218279
theorem B1971803 : Blo 1891435 1971803 := bstep (se 1 (by rfl) ⟨1478852, by rfl⟩ : syracuseStep 1971803 = 2957705) B2957705
theorem B5258141 : Blo 1891435 5258141 := bstep (se 3 (by rfl) ⟨985901, by rfl⟩ : syracuseStep 5258141 = 1971803) B1971803
theorem B3505427 : Blo 1891435 3505427 := bstep (se 1 (by rfl) ⟨2629070, by rfl⟩ : syracuseStep 3505427 = 5258141) B5258141
theorem B2336951 : Blo 1891435 2336951 := bstep (se 1 (by rfl) ⟨1752713, by rfl⟩ : syracuseStep 2336951 = 3505427) B3505427
theorem B6231869 : Blo 1891435 6231869 := bstep (se 3 (by rfl) ⟨1168475, by rfl⟩ : syracuseStep 6231869 = 2336951) B2336951
theorem B4154579 : Blo 1891435 4154579 := bstep (se 1 (by rfl) ⟨3115934, by rfl⟩ : syracuseStep 4154579 = 6231869) B6231869
theorem B2769719 : Blo 1891435 2769719 := bstep (se 1 (by rfl) ⟨2077289, by rfl⟩ : syracuseStep 2769719 = 4154579) B4154579
theorem B7385917 : Blo 1891435 7385917 := bstep (se 3 (by rfl) ⟨1384859, by rfl⟩ : syracuseStep 7385917 = 2769719) B2769719
theorem B9847889 : Blo 1891435 9847889 := bstep (se 2 (by rfl) ⟨3692958, by rfl⟩ : syracuseStep 9847889 = 7385917) B7385917
theorem B6565259 : Blo 1891435 6565259 := bstep (se 1 (by rfl) ⟨4923944, by rfl⟩ : syracuseStep 6565259 = 9847889) B9847889
theorem B17507357 : Blo 1891435 17507357 := bstep (se 3 (by rfl) ⟨3282629, by rfl⟩ : syracuseStep 17507357 = 6565259) B6565259
theorem B11671571 : Blo 1891435 11671571 := bstep (se 1 (by rfl) ⟨8753678, by rfl⟩ : syracuseStep 11671571 = 17507357) B17507357
theorem B31124189 : Blo 1891435 31124189 := bstep (se 3 (by rfl) ⟨5835785, by rfl⟩ : syracuseStep 31124189 = 11671571) B11671571
theorem B20749459 : Blo 1891435 20749459 := bstep (se 1 (by rfl) ⟨15562094, by rfl⟩ : syracuseStep 20749459 = 31124189) B31124189
theorem B27665945 : Blo 1891435 27665945 := bstep (se 2 (by rfl) ⟨10374729, by rfl⟩ : syracuseStep 27665945 = 20749459) B20749459
theorem B18443963 : Blo 1891435 18443963 := bstep (se 1 (by rfl) ⟨13832972, by rfl⟩ : syracuseStep 18443963 = 27665945) B27665945
theorem B12295975 : Blo 1891435 12295975 := bstep (se 1 (by rfl) ⟨9221981, by rfl⟩ : syracuseStep 12295975 = 18443963) B18443963
theorem B16394633 : Blo 1891435 16394633 := bstep (se 2 (by rfl) ⟨6147987, by rfl⟩ : syracuseStep 16394633 = 12295975) B12295975
theorem B10929755 : Blo 1891435 10929755 := bstep (se 1 (by rfl) ⟨8197316, by rfl⟩ : syracuseStep 10929755 = 16394633) B16394633
theorem B29146013 : Blo 1891435 29146013 := bstep (se 3 (by rfl) ⟨5464877, by rfl⟩ : syracuseStep 29146013 = 10929755) B10929755
theorem B19430675 : Blo 1891435 19430675 := bstep (se 1 (by rfl) ⟨14573006, by rfl⟩ : syracuseStep 19430675 = 29146013) B29146013
theorem B12953783 : Blo 1891435 12953783 := bstep (se 1 (by rfl) ⟨9715337, by rfl⟩ : syracuseStep 12953783 = 19430675) B19430675
theorem B8635855 : Blo 1891435 8635855 := bstep (se 1 (by rfl) ⟨6476891, by rfl⟩ : syracuseStep 8635855 = 12953783) B12953783
theorem B11514473 : Blo 1891435 11514473 := bstep (se 2 (by rfl) ⟨4317927, by rfl⟩ : syracuseStep 11514473 = 8635855) B8635855
theorem B7676315 : Blo 1891435 7676315 := bstep (se 1 (by rfl) ⟨5757236, by rfl⟩ : syracuseStep 7676315 = 11514473) B11514473
theorem B5117543 : Blo 1891435 5117543 := bstep (se 1 (by rfl) ⟨3838157, by rfl⟩ : syracuseStep 5117543 = 7676315) B7676315
theorem B3411695 : Blo 1891435 3411695 := bstep (se 1 (by rfl) ⟨2558771, by rfl⟩ : syracuseStep 3411695 = 5117543) B5117543
theorem B2274463 : Blo 1891435 2274463 := bstep (se 1 (by rfl) ⟨1705847, by rfl⟩ : syracuseStep 2274463 = 3411695) B3411695
theorem B12130469 : Blo 1891435 12130469 := bstep (se 4 (by rfl) ⟨1137231, by rfl⟩ : syracuseStep 12130469 = 2274463) B2274463
theorem B8086979 : Blo 1891435 8086979 := bstep (se 1 (by rfl) ⟨6065234, by rfl⟩ : syracuseStep 8086979 = 12130469) B12130469
theorem B21565277 : Blo 1891435 21565277 := bstep (se 3 (by rfl) ⟨4043489, by rfl⟩ : syracuseStep 21565277 = 8086979) B8086979
theorem B14376851 : Blo 1891435 14376851 := bstep (se 1 (by rfl) ⟨10782638, by rfl⟩ : syracuseStep 14376851 = 21565277) B21565277
theorem B9584567 : Blo 1891435 9584567 := bstep (se 1 (by rfl) ⟨7188425, by rfl⟩ : syracuseStep 9584567 = 14376851) B14376851
theorem B6389711 : Blo 1891435 6389711 := bstep (se 1 (by rfl) ⟨4792283, by rfl⟩ : syracuseStep 6389711 = 9584567) B9584567
theorem B4259807 : Blo 1891435 4259807 := bstep (se 1 (by rfl) ⟨3194855, by rfl⟩ : syracuseStep 4259807 = 6389711) B6389711
theorem B2839871 : Blo 1891435 2839871 := bstep (se 1 (by rfl) ⟨2129903, by rfl⟩ : syracuseStep 2839871 = 4259807) B4259807
theorem B1893247 : Blo 1891435 1893247 := bstep (se 1 (by rfl) ⟨1419935, by rfl⟩ : syracuseStep 1893247 = 2839871) B2839871
theorem B2839877 : Blo 1891435 2839877 := bbase (se 4 (by rfl) ⟨266238, by rfl⟩ : syracuseStep 2839877 = 532477) (by norm_num)
theorem B1893251 : Blo 1891435 1893251 := bstep (se 1 (by rfl) ⟨1419938, by rfl⟩ : syracuseStep 1893251 = 2839877) B2839877
theorem B3194869 : Blo 1891435 3194869 := bbase (se 5 (by rfl) ⟨149759, by rfl⟩ : syracuseStep 3194869 = 299519) (by norm_num)
theorem B4259825 : Blo 1891435 4259825 := bstep (se 2 (by rfl) ⟨1597434, by rfl⟩ : syracuseStep 4259825 = 3194869) B3194869
theorem B2839883 : Blo 1891435 2839883 := bstep (se 1 (by rfl) ⟨2129912, by rfl⟩ : syracuseStep 2839883 = 4259825) B4259825
theorem B1893255 : Blo 1891435 1893255 := bstep (se 1 (by rfl) ⟨1419941, by rfl⟩ : syracuseStep 1893255 = 2839883) B2839883
theorem B2129917 : Blo 1891435 2129917 := bbase (se 3 (by rfl) ⟨399359, by rfl⟩ : syracuseStep 2129917 = 798719) (by norm_num)
theorem B2839889 : Blo 1891435 2839889 := bstep (se 2 (by rfl) ⟨1064958, by rfl⟩ : syracuseStep 2839889 = 2129917) B2129917
theorem B1893259 : Blo 1891435 1893259 := bstep (se 1 (by rfl) ⟨1419944, by rfl⟩ : syracuseStep 1893259 = 2839889) B2839889
theorem B6389765 : Blo 1891435 6389765 := bbase (se 4 (by rfl) ⟨599040, by rfl⟩ : syracuseStep 6389765 = 1198081) (by norm_num)
theorem B4259843 : Blo 1891435 4259843 := bstep (se 1 (by rfl) ⟨3194882, by rfl⟩ : syracuseStep 4259843 = 6389765) B6389765
theorem B2839895 : Blo 1891435 2839895 := bstep (se 1 (by rfl) ⟨2129921, by rfl⟩ : syracuseStep 2839895 = 4259843) B4259843
theorem B1893263 : Blo 1891435 1893263 := bstep (se 1 (by rfl) ⟨1419947, by rfl⟩ : syracuseStep 1893263 = 2839895) B2839895
theorem B2839901 : Blo 1891435 2839901 := bbase (se 3 (by rfl) ⟨532481, by rfl⟩ : syracuseStep 2839901 = 1064963) (by norm_num)
theorem B1893267 : Blo 1891435 1893267 := bstep (se 1 (by rfl) ⟨1419950, by rfl⟩ : syracuseStep 1893267 = 2839901) B2839901
theorem B4259861 : Blo 1891435 4259861 := bbase (se 6 (by rfl) ⟨99840, by rfl⟩ : syracuseStep 4259861 = 199681) (by norm_num)
theorem B2839907 : Blo 1891435 2839907 := bstep (se 1 (by rfl) ⟨2129930, by rfl⟩ : syracuseStep 2839907 = 4259861) B4259861
theorem B1893271 : Blo 1891435 1893271 := bstep (se 1 (by rfl) ⟨1419953, by rfl⟩ : syracuseStep 1893271 = 2839907) B2839907
theorem B7188533 : Blo 1891435 7188533 := bbase (se 5 (by rfl) ⟨336962, by rfl⟩ : syracuseStep 7188533 = 673925) (by norm_num)
theorem B4792355 : Blo 1891435 4792355 := bstep (se 1 (by rfl) ⟨3594266, by rfl⟩ : syracuseStep 4792355 = 7188533) B7188533
theorem B3194903 : Blo 1891435 3194903 := bstep (se 1 (by rfl) ⟨2396177, by rfl⟩ : syracuseStep 3194903 = 4792355) B4792355
theorem B2129935 : Blo 1891435 2129935 := bstep (se 1 (by rfl) ⟨1597451, by rfl⟩ : syracuseStep 2129935 = 3194903) B3194903
theorem B2839913 : Blo 1891435 2839913 := bstep (se 2 (by rfl) ⟨1064967, by rfl⟩ : syracuseStep 2839913 = 2129935) B2129935
theorem B1893275 : Blo 1891435 1893275 := bstep (se 1 (by rfl) ⟨1419956, by rfl⟩ : syracuseStep 1893275 = 2839913) B2839913
theorem B3032669 : Blo 1891435 3032669 := bbase (se 3 (by rfl) ⟨568625, by rfl⟩ : syracuseStep 3032669 = 1137251) (by norm_num)
theorem B2021779 : Blo 1891435 2021779 := bstep (se 1 (by rfl) ⟨1516334, by rfl⟩ : syracuseStep 2021779 = 3032669) B3032669
theorem B10782821 : Blo 1891435 10782821 := bstep (se 4 (by rfl) ⟨1010889, by rfl⟩ : syracuseStep 10782821 = 2021779) B2021779
theorem B7188547 : Blo 1891435 7188547 := bstep (se 1 (by rfl) ⟨5391410, by rfl⟩ : syracuseStep 7188547 = 10782821) B10782821
theorem B9584729 : Blo 1891435 9584729 := bstep (se 2 (by rfl) ⟨3594273, by rfl⟩ : syracuseStep 9584729 = 7188547) B7188547
theorem B6389819 : Blo 1891435 6389819 := bstep (se 1 (by rfl) ⟨4792364, by rfl⟩ : syracuseStep 6389819 = 9584729) B9584729
theorem B4259879 : Blo 1891435 4259879 := bstep (se 1 (by rfl) ⟨3194909, by rfl⟩ : syracuseStep 4259879 = 6389819) B6389819
theorem B2839919 : Blo 1891435 2839919 := bstep (se 1 (by rfl) ⟨2129939, by rfl⟩ : syracuseStep 2839919 = 4259879) B4259879
theorem B1893279 : Blo 1891435 1893279 := bstep (se 1 (by rfl) ⟨1419959, by rfl⟩ : syracuseStep 1893279 = 2839919) B2839919
theorem B2839925 : Blo 1891435 2839925 := bbase (se 5 (by rfl) ⟨133121, by rfl⟩ : syracuseStep 2839925 = 266243) (by norm_num)
theorem B1893283 : Blo 1891435 1893283 := bstep (se 1 (by rfl) ⟨1419962, by rfl⟩ : syracuseStep 1893283 = 2839925) B2839925
theorem B2695717 : Blo 1891435 2695717 := bbase (se 4 (by rfl) ⟨252723, by rfl⟩ : syracuseStep 2695717 = 505447) (by norm_num)
theorem B3594289 : Blo 1891435 3594289 := bstep (se 2 (by rfl) ⟨1347858, by rfl⟩ : syracuseStep 3594289 = 2695717) B2695717
theorem B4792385 : Blo 1891435 4792385 := bstep (se 2 (by rfl) ⟨1797144, by rfl⟩ : syracuseStep 4792385 = 3594289) B3594289
theorem B3194923 : Blo 1891435 3194923 := bstep (se 1 (by rfl) ⟨2396192, by rfl⟩ : syracuseStep 3194923 = 4792385) B4792385
theorem B4259897 : Blo 1891435 4259897 := bstep (se 2 (by rfl) ⟨1597461, by rfl⟩ : syracuseStep 4259897 = 3194923) B3194923
theorem B2839931 : Blo 1891435 2839931 := bstep (se 1 (by rfl) ⟨2129948, by rfl⟩ : syracuseStep 2839931 = 4259897) B4259897
theorem B1893287 : Blo 1891435 1893287 := bstep (se 1 (by rfl) ⟨1419965, by rfl⟩ : syracuseStep 1893287 = 2839931) B2839931
theorem B2129953 : Blo 1891435 2129953 := bbase (se 2 (by rfl) ⟨798732, by rfl⟩ : syracuseStep 2129953 = 1597465) (by norm_num)
theorem B2839937 : Blo 1891435 2839937 := bstep (se 2 (by rfl) ⟨1064976, by rfl⟩ : syracuseStep 2839937 = 2129953) B2129953
theorem B1893291 : Blo 1891435 1893291 := bstep (se 1 (by rfl) ⟨1419968, by rfl⟩ : syracuseStep 1893291 = 2839937) B2839937
theorem B4792405 : Blo 1891435 4792405 := bbase (se 8 (by rfl) ⟨28080, by rfl⟩ : syracuseStep 4792405 = 56161) (by norm_num)
theorem B6389873 : Blo 1891435 6389873 := bstep (se 2 (by rfl) ⟨2396202, by rfl⟩ : syracuseStep 6389873 = 4792405) B4792405
theorem B4259915 : Blo 1891435 4259915 := bstep (se 1 (by rfl) ⟨3194936, by rfl⟩ : syracuseStep 4259915 = 6389873) B6389873
theorem B2839943 : Blo 1891435 2839943 := bstep (se 1 (by rfl) ⟨2129957, by rfl⟩ : syracuseStep 2839943 = 4259915) B4259915
theorem B1893295 : Blo 1891435 1893295 := bstep (se 1 (by rfl) ⟨1419971, by rfl⟩ : syracuseStep 1893295 = 2839943) B2839943
theorem B2839949 : Blo 1891435 2839949 := bbase (se 3 (by rfl) ⟨532490, by rfl⟩ : syracuseStep 2839949 = 1064981) (by norm_num)
theorem B1893299 : Blo 1891435 1893299 := bstep (se 1 (by rfl) ⟨1419974, by rfl⟩ : syracuseStep 1893299 = 2839949) B2839949
theorem B4259933 : Blo 1891435 4259933 := bbase (se 3 (by rfl) ⟨798737, by rfl⟩ : syracuseStep 4259933 = 1597475) (by norm_num)
theorem B2839955 : Blo 1891435 2839955 := bstep (se 1 (by rfl) ⟨2129966, by rfl⟩ : syracuseStep 2839955 = 4259933) B4259933
theorem B1893303 : Blo 1891435 1893303 := bstep (se 1 (by rfl) ⟨1419977, by rfl⟩ : syracuseStep 1893303 = 2839955) B2839955
theorem B3194957 : Blo 1891435 3194957 := bbase (se 3 (by rfl) ⟨599054, by rfl⟩ : syracuseStep 3194957 = 1198109) (by norm_num)
theorem B2129971 : Blo 1891435 2129971 := bstep (se 1 (by rfl) ⟨1597478, by rfl⟩ : syracuseStep 2129971 = 3194957) B3194957
theorem B2839961 : Blo 1891435 2839961 := bstep (se 2 (by rfl) ⟨1064985, by rfl⟩ : syracuseStep 2839961 = 2129971) B2129971
theorem B1893307 : Blo 1891435 1893307 := bstep (se 1 (by rfl) ⟨1419980, by rfl⟩ : syracuseStep 1893307 = 2839961) B2839961
theorem B92118869 : Blo 1891435 92118869 := bbase (se 9 (by rfl) ⟨269879, by rfl⟩ : syracuseStep 92118869 = 539759) (by norm_num)
theorem B61412579 : Blo 1891435 61412579 := bstep (se 1 (by rfl) ⟨46059434, by rfl⟩ : syracuseStep 61412579 = 92118869) B92118869
theorem B40941719 : Blo 1891435 40941719 := bstep (se 1 (by rfl) ⟨30706289, by rfl⟩ : syracuseStep 40941719 = 61412579) B61412579
theorem B27294479 : Blo 1891435 27294479 := bstep (se 1 (by rfl) ⟨20470859, by rfl⟩ : syracuseStep 27294479 = 40941719) B40941719
theorem B18196319 : Blo 1891435 18196319 := bstep (se 1 (by rfl) ⟨13647239, by rfl⟩ : syracuseStep 18196319 = 27294479) B27294479
theorem B12130879 : Blo 1891435 12130879 := bstep (se 1 (by rfl) ⟨9098159, by rfl⟩ : syracuseStep 12130879 = 18196319) B18196319
theorem B16174505 : Blo 1891435 16174505 := bstep (se 2 (by rfl) ⟨6065439, by rfl⟩ : syracuseStep 16174505 = 12130879) B12130879
theorem B10783003 : Blo 1891435 10783003 := bstep (se 1 (by rfl) ⟨8087252, by rfl⟩ : syracuseStep 10783003 = 16174505) B16174505
theorem B14377337 : Blo 1891435 14377337 := bstep (se 2 (by rfl) ⟨5391501, by rfl⟩ : syracuseStep 14377337 = 10783003) B10783003
theorem B9584891 : Blo 1891435 9584891 := bstep (se 1 (by rfl) ⟨7188668, by rfl⟩ : syracuseStep 9584891 = 14377337) B14377337
theorem B6389927 : Blo 1891435 6389927 := bstep (se 1 (by rfl) ⟨4792445, by rfl⟩ : syracuseStep 6389927 = 9584891) B9584891
theorem B4259951 : Blo 1891435 4259951 := bstep (se 1 (by rfl) ⟨3194963, by rfl⟩ : syracuseStep 4259951 = 6389927) B6389927
theorem B2839967 : Blo 1891435 2839967 := bstep (se 1 (by rfl) ⟨2129975, by rfl⟩ : syracuseStep 2839967 = 4259951) B4259951
theorem B1893311 : Blo 1891435 1893311 := bstep (se 1 (by rfl) ⟨1419983, by rfl⟩ : syracuseStep 1893311 = 2839967) B2839967
theorem B2839973 : Blo 1891435 2839973 := bbase (se 4 (by rfl) ⟨266247, by rfl⟩ : syracuseStep 2839973 = 532495) (by norm_num)
theorem B1893315 : Blo 1891435 1893315 := bstep (se 1 (by rfl) ⟨1419986, by rfl⟩ : syracuseStep 1893315 = 2839973) B2839973
theorem B2396233 : Blo 1891435 2396233 := bbase (se 2 (by rfl) ⟨898587, by rfl⟩ : syracuseStep 2396233 = 1797175) (by norm_num)
theorem B3194977 : Blo 1891435 3194977 := bstep (se 2 (by rfl) ⟨1198116, by rfl⟩ : syracuseStep 3194977 = 2396233) B2396233
theorem B4259969 : Blo 1891435 4259969 := bstep (se 2 (by rfl) ⟨1597488, by rfl⟩ : syracuseStep 4259969 = 3194977) B3194977
theorem B2839979 : Blo 1891435 2839979 := bstep (se 1 (by rfl) ⟨2129984, by rfl⟩ : syracuseStep 2839979 = 4259969) B4259969
theorem B1893319 : Blo 1891435 1893319 := bstep (se 1 (by rfl) ⟨1419989, by rfl⟩ : syracuseStep 1893319 = 2839979) B2839979
theorem B2129989 : Blo 1891435 2129989 := bbase (se 4 (by rfl) ⟨199686, by rfl⟩ : syracuseStep 2129989 = 399373) (by norm_num)
theorem B2839985 : Blo 1891435 2839985 := bstep (se 2 (by rfl) ⟨1064994, by rfl⟩ : syracuseStep 2839985 = 2129989) B2129989
theorem B1893323 : Blo 1891435 1893323 := bstep (se 1 (by rfl) ⟨1419992, by rfl⟩ : syracuseStep 1893323 = 2839985) B2839985
theorem B3594365 : Blo 1891435 3594365 := bbase (se 3 (by rfl) ⟨673943, by rfl⟩ : syracuseStep 3594365 = 1347887) (by norm_num)
theorem B2396243 : Blo 1891435 2396243 := bstep (se 1 (by rfl) ⟨1797182, by rfl⟩ : syracuseStep 2396243 = 3594365) B3594365
theorem B6389981 : Blo 1891435 6389981 := bstep (se 3 (by rfl) ⟨1198121, by rfl⟩ : syracuseStep 6389981 = 2396243) B2396243
theorem B4259987 : Blo 1891435 4259987 := bstep (se 1 (by rfl) ⟨3194990, by rfl⟩ : syracuseStep 4259987 = 6389981) B6389981
theorem B2839991 : Blo 1891435 2839991 := bstep (se 1 (by rfl) ⟨2129993, by rfl⟩ : syracuseStep 2839991 = 4259987) B4259987
theorem B1893327 : Blo 1891435 1893327 := bstep (se 1 (by rfl) ⟨1419995, by rfl⟩ : syracuseStep 1893327 = 2839991) B2839991
theorem B2839997 : Blo 1891435 2839997 := bbase (se 3 (by rfl) ⟨532499, by rfl⟩ : syracuseStep 2839997 = 1064999) (by norm_num)
theorem B1893331 : Blo 1891435 1893331 := bstep (se 1 (by rfl) ⟨1419998, by rfl⟩ : syracuseStep 1893331 = 2839997) B2839997
theorem B4260005 : Blo 1891435 4260005 := bbase (se 4 (by rfl) ⟨399375, by rfl⟩ : syracuseStep 4260005 = 798751) (by norm_num)
theorem B2840003 : Blo 1891435 2840003 := bstep (se 1 (by rfl) ⟨2130002, by rfl⟩ : syracuseStep 2840003 = 4260005) B4260005
theorem B1893335 : Blo 1891435 1893335 := bstep (se 1 (by rfl) ⟨1420001, by rfl⟩ : syracuseStep 1893335 = 2840003) B2840003
theorem B4792517 : Blo 1891435 4792517 := bbase (se 4 (by rfl) ⟨449298, by rfl⟩ : syracuseStep 4792517 = 898597) (by norm_num)
theorem B3195011 : Blo 1891435 3195011 := bstep (se 1 (by rfl) ⟨2396258, by rfl⟩ : syracuseStep 3195011 = 4792517) B4792517
theorem B2130007 : Blo 1891435 2130007 := bstep (se 1 (by rfl) ⟨1597505, by rfl⟩ : syracuseStep 2130007 = 3195011) B3195011
theorem B2840009 : Blo 1891435 2840009 := bstep (se 2 (by rfl) ⟨1065003, by rfl⟩ : syracuseStep 2840009 = 2130007) B2130007
theorem B1893339 : Blo 1891435 1893339 := bstep (se 1 (by rfl) ⟨1420004, by rfl⟩ : syracuseStep 1893339 = 2840009) B2840009
theorem B10235605 : Blo 1891435 10235605 := bbase (se 7 (by rfl) ⟨119948, by rfl⟩ : syracuseStep 10235605 = 239897) (by norm_num)
theorem B13647473 : Blo 1891435 13647473 := bstep (se 2 (by rfl) ⟨5117802, by rfl⟩ : syracuseStep 13647473 = 10235605) B10235605
theorem B9098315 : Blo 1891435 9098315 := bstep (se 1 (by rfl) ⟨6823736, by rfl⟩ : syracuseStep 9098315 = 13647473) B13647473
theorem B6065543 : Blo 1891435 6065543 := bstep (se 1 (by rfl) ⟨4549157, by rfl⟩ : syracuseStep 6065543 = 9098315) B9098315
theorem B4043695 : Blo 1891435 4043695 := bstep (se 1 (by rfl) ⟨3032771, by rfl⟩ : syracuseStep 4043695 = 6065543) B6065543
theorem B5391593 : Blo 1891435 5391593 := bstep (se 2 (by rfl) ⟨2021847, by rfl⟩ : syracuseStep 5391593 = 4043695) B4043695
theorem B3594395 : Blo 1891435 3594395 := bstep (se 1 (by rfl) ⟨2695796, by rfl⟩ : syracuseStep 3594395 = 5391593) B5391593
theorem B9585053 : Blo 1891435 9585053 := bstep (se 3 (by rfl) ⟨1797197, by rfl⟩ : syracuseStep 9585053 = 3594395) B3594395
theorem B6390035 : Blo 1891435 6390035 := bstep (se 1 (by rfl) ⟨4792526, by rfl⟩ : syracuseStep 6390035 = 9585053) B9585053
theorem B4260023 : Blo 1891435 4260023 := bstep (se 1 (by rfl) ⟨3195017, by rfl⟩ : syracuseStep 4260023 = 6390035) B6390035
theorem B2840015 : Blo 1891435 2840015 := bstep (se 1 (by rfl) ⟨2130011, by rfl⟩ : syracuseStep 2840015 = 4260023) B4260023
theorem B1893343 : Blo 1891435 1893343 := bstep (se 1 (by rfl) ⟨1420007, by rfl⟩ : syracuseStep 1893343 = 2840015) B2840015
theorem B2840021 : Blo 1891435 2840021 := bbase (se 7 (by rfl) ⟨33281, by rfl⟩ : syracuseStep 2840021 = 66563) (by norm_num)
theorem B1893347 : Blo 1891435 1893347 := bstep (se 1 (by rfl) ⟨1420010, by rfl⟩ : syracuseStep 1893347 = 2840021) B2840021
theorem B7188821 : Blo 1891435 7188821 := bbase (se 10 (by rfl) ⟨10530, by rfl⟩ : syracuseStep 7188821 = 21061) (by norm_num)
theorem B4792547 : Blo 1891435 4792547 := bstep (se 1 (by rfl) ⟨3594410, by rfl⟩ : syracuseStep 4792547 = 7188821) B7188821
theorem B3195031 : Blo 1891435 3195031 := bstep (se 1 (by rfl) ⟨2396273, by rfl⟩ : syracuseStep 3195031 = 4792547) B4792547
theorem B4260041 : Blo 1891435 4260041 := bstep (se 2 (by rfl) ⟨1597515, by rfl⟩ : syracuseStep 4260041 = 3195031) B3195031
theorem B2840027 : Blo 1891435 2840027 := bstep (se 1 (by rfl) ⟨2130020, by rfl⟩ : syracuseStep 2840027 = 4260041) B4260041
theorem B1893351 : Blo 1891435 1893351 := bstep (se 1 (by rfl) ⟨1420013, by rfl⟩ : syracuseStep 1893351 = 2840027) B2840027
theorem B2130025 : Blo 1891435 2130025 := bbase (se 2 (by rfl) ⟨798759, by rfl⟩ : syracuseStep 2130025 = 1597519) (by norm_num)
theorem B2840033 : Blo 1891435 2840033 := bstep (se 2 (by rfl) ⟨1065012, by rfl⟩ : syracuseStep 2840033 = 2130025) B2130025
theorem B1893355 : Blo 1891435 1893355 := bstep (se 1 (by rfl) ⟨1420016, by rfl⟩ : syracuseStep 1893355 = 2840033) B2840033
theorem B3032797 : Blo 1891435 3032797 := bbase (se 3 (by rfl) ⟨568649, by rfl⟩ : syracuseStep 3032797 = 1137299) (by norm_num)
theorem B4043729 : Blo 1891435 4043729 := bstep (se 2 (by rfl) ⟨1516398, by rfl⟩ : syracuseStep 4043729 = 3032797) B3032797
theorem B10783277 : Blo 1891435 10783277 := bstep (se 3 (by rfl) ⟨2021864, by rfl⟩ : syracuseStep 10783277 = 4043729) B4043729
theorem B7188851 : Blo 1891435 7188851 := bstep (se 1 (by rfl) ⟨5391638, by rfl⟩ : syracuseStep 7188851 = 10783277) B10783277
theorem B4792567 : Blo 1891435 4792567 := bstep (se 1 (by rfl) ⟨3594425, by rfl⟩ : syracuseStep 4792567 = 7188851) B7188851
theorem B6390089 : Blo 1891435 6390089 := bstep (se 2 (by rfl) ⟨2396283, by rfl⟩ : syracuseStep 6390089 = 4792567) B4792567
theorem B4260059 : Blo 1891435 4260059 := bstep (se 1 (by rfl) ⟨3195044, by rfl⟩ : syracuseStep 4260059 = 6390089) B6390089
theorem B2840039 : Blo 1891435 2840039 := bstep (se 1 (by rfl) ⟨2130029, by rfl⟩ : syracuseStep 2840039 = 4260059) B4260059
theorem B1893359 : Blo 1891435 1893359 := bstep (se 1 (by rfl) ⟨1420019, by rfl⟩ : syracuseStep 1893359 = 2840039) B2840039
theorem B2840045 : Blo 1891435 2840045 := bbase (se 3 (by rfl) ⟨532508, by rfl⟩ : syracuseStep 2840045 = 1065017) (by norm_num)
theorem B1893363 : Blo 1891435 1893363 := bstep (se 1 (by rfl) ⟨1420022, by rfl⟩ : syracuseStep 1893363 = 2840045) B2840045
theorem B4260077 : Blo 1891435 4260077 := bbase (se 3 (by rfl) ⟨798764, by rfl⟩ : syracuseStep 4260077 = 1597529) (by norm_num)
theorem B2840051 : Blo 1891435 2840051 := bstep (se 1 (by rfl) ⟨2130038, by rfl⟩ : syracuseStep 2840051 = 4260077) B4260077
theorem B1893367 : Blo 1891435 1893367 := bstep (se 1 (by rfl) ⟨1420025, by rfl⟩ : syracuseStep 1893367 = 2840051) B2840051
theorem B2695837 : Blo 1891435 2695837 := bbase (se 3 (by rfl) ⟨505469, by rfl⟩ : syracuseStep 2695837 = 1010939) (by norm_num)
theorem B3594449 : Blo 1891435 3594449 := bstep (se 2 (by rfl) ⟨1347918, by rfl⟩ : syracuseStep 3594449 = 2695837) B2695837
theorem B2396299 : Blo 1891435 2396299 := bstep (se 1 (by rfl) ⟨1797224, by rfl⟩ : syracuseStep 2396299 = 3594449) B3594449
theorem B3195065 : Blo 1891435 3195065 := bstep (se 2 (by rfl) ⟨1198149, by rfl⟩ : syracuseStep 3195065 = 2396299) B2396299
theorem B2130043 : Blo 1891435 2130043 := bstep (se 1 (by rfl) ⟨1597532, by rfl⟩ : syracuseStep 2130043 = 3195065) B3195065
theorem B2840057 : Blo 1891435 2840057 := bstep (se 2 (by rfl) ⟨1065021, by rfl⟩ : syracuseStep 2840057 = 2130043) B2130043
theorem B1893371 : Blo 1891435 1893371 := bstep (se 1 (by rfl) ⟨1420028, by rfl⟩ : syracuseStep 1893371 = 2840057) B2840057
theorem B3411925 : Blo 1891435 3411925 := bbase (se 7 (by rfl) ⟨39983, by rfl⟩ : syracuseStep 3411925 = 79967) (by norm_num)
theorem B72787733 : Blo 1891435 72787733 := bstep (se 6 (by rfl) ⟨1705962, by rfl⟩ : syracuseStep 72787733 = 3411925) B3411925
theorem B48525155 : Blo 1891435 48525155 := bstep (se 1 (by rfl) ⟨36393866, by rfl⟩ : syracuseStep 48525155 = 72787733) B72787733
theorem B32350103 : Blo 1891435 32350103 := bstep (se 1 (by rfl) ⟨24262577, by rfl⟩ : syracuseStep 32350103 = 48525155) B48525155
theorem B21566735 : Blo 1891435 21566735 := bstep (se 1 (by rfl) ⟨16175051, by rfl⟩ : syracuseStep 21566735 = 32350103) B32350103
theorem B14377823 : Blo 1891435 14377823 := bstep (se 1 (by rfl) ⟨10783367, by rfl⟩ : syracuseStep 14377823 = 21566735) B21566735
theorem B9585215 : Blo 1891435 9585215 := bstep (se 1 (by rfl) ⟨7188911, by rfl⟩ : syracuseStep 9585215 = 14377823) B14377823
theorem B6390143 : Blo 1891435 6390143 := bstep (se 1 (by rfl) ⟨4792607, by rfl⟩ : syracuseStep 6390143 = 9585215) B9585215
theorem B4260095 : Blo 1891435 4260095 := bstep (se 1 (by rfl) ⟨3195071, by rfl⟩ : syracuseStep 4260095 = 6390143) B6390143
theorem B2840063 : Blo 1891435 2840063 := bstep (se 1 (by rfl) ⟨2130047, by rfl⟩ : syracuseStep 2840063 = 4260095) B4260095
theorem B1893375 : Blo 1891435 1893375 := bstep (se 1 (by rfl) ⟨1420031, by rfl⟩ : syracuseStep 1893375 = 2840063) B2840063
theorem B2840069 : Blo 1891435 2840069 := bbase (se 4 (by rfl) ⟨266256, by rfl⟩ : syracuseStep 2840069 = 532513) (by norm_num)
theorem B1893379 : Blo 1891435 1893379 := bstep (se 1 (by rfl) ⟨1420034, by rfl⟩ : syracuseStep 1893379 = 2840069) B2840069
theorem B3195085 : Blo 1891435 3195085 := bbase (se 3 (by rfl) ⟨599078, by rfl⟩ : syracuseStep 3195085 = 1198157) (by norm_num)
theorem B4260113 : Blo 1891435 4260113 := bstep (se 2 (by rfl) ⟨1597542, by rfl⟩ : syracuseStep 4260113 = 3195085) B3195085
theorem B2840075 : Blo 1891435 2840075 := bstep (se 1 (by rfl) ⟨2130056, by rfl⟩ : syracuseStep 2840075 = 4260113) B4260113
theorem B1893383 : Blo 1891435 1893383 := bstep (se 1 (by rfl) ⟨1420037, by rfl⟩ : syracuseStep 1893383 = 2840075) B2840075
theorem B2130061 : Blo 1891435 2130061 := bbase (se 3 (by rfl) ⟨399386, by rfl⟩ : syracuseStep 2130061 = 798773) (by norm_num)
theorem B2840081 : Blo 1891435 2840081 := bstep (se 2 (by rfl) ⟨1065030, by rfl⟩ : syracuseStep 2840081 = 2130061) B2130061
theorem B1893387 : Blo 1891435 1893387 := bstep (se 1 (by rfl) ⟨1420040, by rfl⟩ : syracuseStep 1893387 = 2840081) B2840081
theorem B6390197 : Blo 1891435 6390197 := bbase (se 5 (by rfl) ⟨299540, by rfl⟩ : syracuseStep 6390197 = 599081) (by norm_num)
theorem B4260131 : Blo 1891435 4260131 := bstep (se 1 (by rfl) ⟨3195098, by rfl⟩ : syracuseStep 4260131 = 6390197) B6390197
theorem B2840087 : Blo 1891435 2840087 := bstep (se 1 (by rfl) ⟨2130065, by rfl⟩ : syracuseStep 2840087 = 4260131) B4260131
theorem B1893391 : Blo 1891435 1893391 := bstep (se 1 (by rfl) ⟨1420043, by rfl⟩ : syracuseStep 1893391 = 2840087) B2840087
theorem B2840093 : Blo 1891435 2840093 := bbase (se 3 (by rfl) ⟨532517, by rfl⟩ : syracuseStep 2840093 = 1065035) (by norm_num)
theorem B1893395 : Blo 1891435 1893395 := bstep (se 1 (by rfl) ⟨1420046, by rfl⟩ : syracuseStep 1893395 = 2840093) B2840093
theorem B4260149 : Blo 1891435 4260149 := bbase (se 5 (by rfl) ⟨199694, by rfl⟩ : syracuseStep 4260149 = 399389) (by norm_num)
theorem B2840099 : Blo 1891435 2840099 := bstep (se 1 (by rfl) ⟨2130074, by rfl⟩ : syracuseStep 2840099 = 4260149) B4260149
theorem B1893399 : Blo 1891435 1893399 := bstep (se 1 (by rfl) ⟨1420049, by rfl⟩ : syracuseStep 1893399 = 2840099) B2840099
theorem B4858069 : Blo 1891435 4858069 := bbase (se 7 (by rfl) ⟨56930, by rfl⟩ : syracuseStep 4858069 = 113861) (by norm_num)
theorem B6477425 : Blo 1891435 6477425 := bstep (se 2 (by rfl) ⟨2429034, by rfl⟩ : syracuseStep 6477425 = 4858069) B4858069
theorem B4318283 : Blo 1891435 4318283 := bstep (se 1 (by rfl) ⟨3238712, by rfl⟩ : syracuseStep 4318283 = 6477425) B6477425
theorem B11515421 : Blo 1891435 11515421 := bstep (se 3 (by rfl) ⟨2159141, by rfl⟩ : syracuseStep 11515421 = 4318283) B4318283
theorem B7676947 : Blo 1891435 7676947 := bstep (se 1 (by rfl) ⟨5757710, by rfl⟩ : syracuseStep 7676947 = 11515421) B11515421
theorem B40943717 : Blo 1891435 40943717 := bstep (se 4 (by rfl) ⟨3838473, by rfl⟩ : syracuseStep 40943717 = 7676947) B7676947
theorem B27295811 : Blo 1891435 27295811 := bstep (se 1 (by rfl) ⟨20471858, by rfl⟩ : syracuseStep 27295811 = 40943717) B40943717
theorem B18197207 : Blo 1891435 18197207 := bstep (se 1 (by rfl) ⟨13647905, by rfl⟩ : syracuseStep 18197207 = 27295811) B27295811
theorem B12131471 : Blo 1891435 12131471 := bstep (se 1 (by rfl) ⟨9098603, by rfl⟩ : syracuseStep 12131471 = 18197207) B18197207
theorem B8087647 : Blo 1891435 8087647 := bstep (se 1 (by rfl) ⟨6065735, by rfl⟩ : syracuseStep 8087647 = 12131471) B12131471
theorem B10783529 : Blo 1891435 10783529 := bstep (se 2 (by rfl) ⟨4043823, by rfl⟩ : syracuseStep 10783529 = 8087647) B8087647
theorem B7189019 : Blo 1891435 7189019 := bstep (se 1 (by rfl) ⟨5391764, by rfl⟩ : syracuseStep 7189019 = 10783529) B10783529
theorem B4792679 : Blo 1891435 4792679 := bstep (se 1 (by rfl) ⟨3594509, by rfl⟩ : syracuseStep 4792679 = 7189019) B7189019
theorem B3195119 : Blo 1891435 3195119 := bstep (se 1 (by rfl) ⟨2396339, by rfl⟩ : syracuseStep 3195119 = 4792679) B4792679
theorem B2130079 : Blo 1891435 2130079 := bstep (se 1 (by rfl) ⟨1597559, by rfl⟩ : syracuseStep 2130079 = 3195119) B3195119
theorem B2840105 : Blo 1891435 2840105 := bstep (se 2 (by rfl) ⟨1065039, by rfl⟩ : syracuseStep 2840105 = 2130079) B2130079
theorem B1893403 : Blo 1891435 1893403 := bstep (se 1 (by rfl) ⟨1420052, by rfl⟩ : syracuseStep 1893403 = 2840105) B2840105
theorem B3693269 : Blo 1891435 3693269 := bbase (se 7 (by rfl) ⟨43280, by rfl⟩ : syracuseStep 3693269 = 86561) (by norm_num)
theorem B9848717 : Blo 1891435 9848717 := bstep (se 3 (by rfl) ⟨1846634, by rfl⟩ : syracuseStep 9848717 = 3693269) B3693269
theorem B6565811 : Blo 1891435 6565811 := bstep (se 1 (by rfl) ⟨4924358, by rfl⟩ : syracuseStep 6565811 = 9848717) B9848717
theorem B17508829 : Blo 1891435 17508829 := bstep (se 3 (by rfl) ⟨3282905, by rfl⟩ : syracuseStep 17508829 = 6565811) B6565811
theorem B23345105 : Blo 1891435 23345105 := bstep (se 2 (by rfl) ⟨8754414, by rfl⟩ : syracuseStep 23345105 = 17508829) B17508829
theorem B62253613 : Blo 1891435 62253613 := bstep (se 3 (by rfl) ⟨11672552, by rfl⟩ : syracuseStep 62253613 = 23345105) B23345105
theorem B332019269 : Blo 1891435 332019269 := bstep (se 4 (by rfl) ⟨31126806, by rfl⟩ : syracuseStep 332019269 = 62253613) B62253613
theorem B221346179 : Blo 1891435 221346179 := bstep (se 1 (by rfl) ⟨166009634, by rfl⟩ : syracuseStep 221346179 = 332019269) B332019269
theorem B147564119 : Blo 1891435 147564119 := bstep (se 1 (by rfl) ⟨110673089, by rfl⟩ : syracuseStep 147564119 = 221346179) B221346179
theorem B98376079 : Blo 1891435 98376079 := bstep (se 1 (by rfl) ⟨73782059, by rfl⟩ : syracuseStep 98376079 = 147564119) B147564119
theorem B131168105 : Blo 1891435 131168105 := bstep (se 2 (by rfl) ⟨49188039, by rfl⟩ : syracuseStep 131168105 = 98376079) B98376079
theorem B87445403 : Blo 1891435 87445403 := bstep (se 1 (by rfl) ⟨65584052, by rfl⟩ : syracuseStep 87445403 = 131168105) B131168105
theorem B58296935 : Blo 1891435 58296935 := bstep (se 1 (by rfl) ⟨43722701, by rfl⟩ : syracuseStep 58296935 = 87445403) B87445403
theorem B38864623 : Blo 1891435 38864623 := bstep (se 1 (by rfl) ⟨29148467, by rfl⟩ : syracuseStep 38864623 = 58296935) B58296935
theorem B51819497 : Blo 1891435 51819497 := bstep (se 2 (by rfl) ⟨19432311, by rfl⟩ : syracuseStep 51819497 = 38864623) B38864623
theorem B34546331 : Blo 1891435 34546331 := bstep (se 1 (by rfl) ⟨25909748, by rfl⟩ : syracuseStep 34546331 = 51819497) B51819497
theorem B23030887 : Blo 1891435 23030887 := bstep (se 1 (by rfl) ⟨17273165, by rfl⟩ : syracuseStep 23030887 = 34546331) B34546331
theorem B30707849 : Blo 1891435 30707849 := bstep (se 2 (by rfl) ⟨11515443, by rfl⟩ : syracuseStep 30707849 = 23030887) B23030887
theorem B20471899 : Blo 1891435 20471899 := bstep (se 1 (by rfl) ⟨15353924, by rfl⟩ : syracuseStep 20471899 = 30707849) B30707849
theorem B27295865 : Blo 1891435 27295865 := bstep (se 2 (by rfl) ⟨10235949, by rfl⟩ : syracuseStep 27295865 = 20471899) B20471899
theorem B18197243 : Blo 1891435 18197243 := bstep (se 1 (by rfl) ⟨13647932, by rfl⟩ : syracuseStep 18197243 = 27295865) B27295865
theorem B12131495 : Blo 1891435 12131495 := bstep (se 1 (by rfl) ⟨9098621, by rfl⟩ : syracuseStep 12131495 = 18197243) B18197243
theorem B8087663 : Blo 1891435 8087663 := bstep (se 1 (by rfl) ⟨6065747, by rfl⟩ : syracuseStep 8087663 = 12131495) B12131495
theorem B5391775 : Blo 1891435 5391775 := bstep (se 1 (by rfl) ⟨4043831, by rfl⟩ : syracuseStep 5391775 = 8087663) B8087663
theorem B7189033 : Blo 1891435 7189033 := bstep (se 2 (by rfl) ⟨2695887, by rfl⟩ : syracuseStep 7189033 = 5391775) B5391775
theorem B9585377 : Blo 1891435 9585377 := bstep (se 2 (by rfl) ⟨3594516, by rfl⟩ : syracuseStep 9585377 = 7189033) B7189033
theorem B6390251 : Blo 1891435 6390251 := bstep (se 1 (by rfl) ⟨4792688, by rfl⟩ : syracuseStep 6390251 = 9585377) B9585377
theorem B4260167 : Blo 1891435 4260167 := bstep (se 1 (by rfl) ⟨3195125, by rfl⟩ : syracuseStep 4260167 = 6390251) B6390251
theorem B2840111 : Blo 1891435 2840111 := bstep (se 1 (by rfl) ⟨2130083, by rfl⟩ : syracuseStep 2840111 = 4260167) B4260167
theorem B1893407 : Blo 1891435 1893407 := bstep (se 1 (by rfl) ⟨1420055, by rfl⟩ : syracuseStep 1893407 = 2840111) B2840111
theorem B2840117 : Blo 1891435 2840117 := bbase (se 5 (by rfl) ⟨133130, by rfl⟩ : syracuseStep 2840117 = 266261) (by norm_num)
theorem B1893411 : Blo 1891435 1893411 := bstep (se 1 (by rfl) ⟨1420058, by rfl⟩ : syracuseStep 1893411 = 2840117) B2840117
theorem B4792709 : Blo 1891435 4792709 := bbase (se 4 (by rfl) ⟨449316, by rfl⟩ : syracuseStep 4792709 = 898633) (by norm_num)
theorem B3195139 : Blo 1891435 3195139 := bstep (se 1 (by rfl) ⟨2396354, by rfl⟩ : syracuseStep 3195139 = 4792709) B4792709
theorem B4260185 : Blo 1891435 4260185 := bstep (se 2 (by rfl) ⟨1597569, by rfl⟩ : syracuseStep 4260185 = 3195139) B3195139
theorem B2840123 : Blo 1891435 2840123 := bstep (se 1 (by rfl) ⟨2130092, by rfl⟩ : syracuseStep 2840123 = 4260185) B4260185
theorem B1893415 : Blo 1891435 1893415 := bstep (se 1 (by rfl) ⟨1420061, by rfl⟩ : syracuseStep 1893415 = 2840123) B2840123
theorem B2130097 : Blo 1891435 2130097 := bbase (se 2 (by rfl) ⟨798786, by rfl⟩ : syracuseStep 2130097 = 1597573) (by norm_num)
theorem B2840129 : Blo 1891435 2840129 := bstep (se 2 (by rfl) ⟨1065048, by rfl⟩ : syracuseStep 2840129 = 2130097) B2130097
theorem B1893419 : Blo 1891435 1893419 := bstep (se 1 (by rfl) ⟨1420064, by rfl⟩ : syracuseStep 1893419 = 2840129) B2840129
theorem B2021933 : Blo 1891435 2021933 := bbase (se 3 (by rfl) ⟨379112, by rfl⟩ : syracuseStep 2021933 = 758225) (by norm_num)
theorem B5391821 : Blo 1891435 5391821 := bstep (se 3 (by rfl) ⟨1010966, by rfl⟩ : syracuseStep 5391821 = 2021933) B2021933
theorem B3594547 : Blo 1891435 3594547 := bstep (se 1 (by rfl) ⟨2695910, by rfl⟩ : syracuseStep 3594547 = 5391821) B5391821
theorem B4792729 : Blo 1891435 4792729 := bstep (se 2 (by rfl) ⟨1797273, by rfl⟩ : syracuseStep 4792729 = 3594547) B3594547
theorem B6390305 : Blo 1891435 6390305 := bstep (se 2 (by rfl) ⟨2396364, by rfl⟩ : syracuseStep 6390305 = 4792729) B4792729
theorem B4260203 : Blo 1891435 4260203 := bstep (se 1 (by rfl) ⟨3195152, by rfl⟩ : syracuseStep 4260203 = 6390305) B6390305
theorem B2840135 : Blo 1891435 2840135 := bstep (se 1 (by rfl) ⟨2130101, by rfl⟩ : syracuseStep 2840135 = 4260203) B4260203
theorem B1893423 : Blo 1891435 1893423 := bstep (se 1 (by rfl) ⟨1420067, by rfl⟩ : syracuseStep 1893423 = 2840135) B2840135
theorem B2840141 : Blo 1891435 2840141 := bbase (se 3 (by rfl) ⟨532526, by rfl⟩ : syracuseStep 2840141 = 1065053) (by norm_num)
theorem B1893427 : Blo 1891435 1893427 := bstep (se 1 (by rfl) ⟨1420070, by rfl⟩ : syracuseStep 1893427 = 2840141) B2840141
theorem B4260221 : Blo 1891435 4260221 := bbase (se 3 (by rfl) ⟨798791, by rfl⟩ : syracuseStep 4260221 = 1597583) (by norm_num)
theorem B2840147 : Blo 1891435 2840147 := bstep (se 1 (by rfl) ⟨2130110, by rfl⟩ : syracuseStep 2840147 = 4260221) B4260221
theorem B1893431 : Blo 1891435 1893431 := bstep (se 1 (by rfl) ⟨1420073, by rfl⟩ : syracuseStep 1893431 = 2840147) B2840147
theorem B3195173 : Blo 1891435 3195173 := bbase (se 4 (by rfl) ⟨299547, by rfl⟩ : syracuseStep 3195173 = 599095) (by norm_num)
theorem B2130115 : Blo 1891435 2130115 := bstep (se 1 (by rfl) ⟨1597586, by rfl⟩ : syracuseStep 2130115 = 3195173) B3195173
theorem B2840153 : Blo 1891435 2840153 := bstep (se 2 (by rfl) ⟨1065057, by rfl⟩ : syracuseStep 2840153 = 2130115) B2130115
theorem B1893435 : Blo 1891435 1893435 := bstep (se 1 (by rfl) ⟨1420076, by rfl⟩ : syracuseStep 1893435 = 2840153) B2840153
theorem C0 (j : ℕ) (h1 : 472858 ≤ j) (h2 : j ≤ 473358) : Blo 1891435 (4 * j + 3) := by
  interval_cases j
  · exact B1891435
  · exact B1891439
  · exact B1891443
  · exact B1891447
  · exact B1891451
  · exact B1891455
  · exact B1891459
  · exact B1891463
  · exact B1891467
  · exact B1891471
  · exact B1891475
  · exact B1891479
  · exact B1891483
  · exact B1891487
  · exact B1891491
  · exact B1891495
  · exact B1891499
  · exact B1891503
  · exact B1891507
  · exact B1891511
  · exact B1891515
  · exact B1891519
  · exact B1891523
  · exact B1891527
  · exact B1891531
  · exact B1891535
  · exact B1891539
  · exact B1891543
  · exact B1891547
  · exact B1891551
  · exact B1891555
  · exact B1891559
  · exact B1891563
  · exact B1891567
  · exact B1891571
  · exact B1891575
  · exact B1891579
  · exact B1891583
  · exact B1891587
  · exact B1891591
  · exact B1891595
  · exact B1891599
  · exact B1891603
  · exact B1891607
  · exact B1891611
  · exact B1891615
  · exact B1891619
  · exact B1891623
  · exact B1891627
  · exact B1891631
  · exact B1891635
  · exact B1891639
  · exact B1891643
  · exact B1891647
  · exact B1891651
  · exact B1891655
  · exact B1891659
  · exact B1891663
  · exact B1891667
  · exact B1891671
  · exact B1891675
  · exact B1891679
  · exact B1891683
  · exact B1891687
  · exact B1891691
  · exact B1891695
  · exact B1891699
  · exact B1891703
  · exact B1891707
  · exact B1891711
  · exact B1891715
  · exact B1891719
  · exact B1891723
  · exact B1891727
  · exact B1891731
  · exact B1891735
  · exact B1891739
  · exact B1891743
  · exact B1891747
  · exact B1891751
  · exact B1891755
  · exact B1891759
  · exact B1891763
  · exact B1891767
  · exact B1891771
  · exact B1891775
  · exact B1891779
  · exact B1891783
  · exact B1891787
  · exact B1891791
  · exact B1891795
  · exact B1891799
  · exact B1891803
  · exact B1891807
  · exact B1891811
  · exact B1891815
  · exact B1891819
  · exact B1891823
  · exact B1891827
  · exact B1891831
  · exact B1891835
  · exact B1891839
  · exact B1891843
  · exact B1891847
  · exact B1891851
  · exact B1891855
  · exact B1891859
  · exact B1891863
  · exact B1891867
  · exact B1891871
  · exact B1891875
  · exact B1891879
  · exact B1891883
  · exact B1891887
  · exact B1891891
  · exact B1891895
  · exact B1891899
  · exact B1891903
  · exact B1891907
  · exact B1891911
  · exact B1891915
  · exact B1891919
  · exact B1891923
  · exact B1891927
  · exact B1891931
  · exact B1891935
  · exact B1891939
  · exact B1891943
  · exact B1891947
  · exact B1891951
  · exact B1891955
  · exact B1891959
  · exact B1891963
  · exact B1891967
  · exact B1891971
  · exact B1891975
  · exact B1891979
  · exact B1891983
  · exact B1891987
  · exact B1891991
  · exact B1891995
  · exact B1891999
  · exact B1892003
  · exact B1892007
  · exact B1892011
  · exact B1892015
  · exact B1892019
  · exact B1892023
  · exact B1892027
  · exact B1892031
  · exact B1892035
  · exact B1892039
  · exact B1892043
  · exact B1892047
  · exact B1892051
  · exact B1892055
  · exact B1892059
  · exact B1892063
  · exact B1892067
  · exact B1892071
  · exact B1892075
  · exact B1892079
  · exact B1892083
  · exact B1892087
  · exact B1892091
  · exact B1892095
  · exact B1892099
  · exact B1892103
  · exact B1892107
  · exact B1892111
  · exact B1892115
  · exact B1892119
  · exact B1892123
  · exact B1892127
  · exact B1892131
  · exact B1892135
  · exact B1892139
  · exact B1892143
  · exact B1892147
  · exact B1892151
  · exact B1892155
  · exact B1892159
  · exact B1892163
  · exact B1892167
  · exact B1892171
  · exact B1892175
  · exact B1892179
  · exact B1892183
  · exact B1892187
  · exact B1892191
  · exact B1892195
  · exact B1892199
  · exact B1892203
  · exact B1892207
  · exact B1892211
  · exact B1892215
  · exact B1892219
  · exact B1892223
  · exact B1892227
  · exact B1892231
  · exact B1892235
  · exact B1892239
  · exact B1892243
  · exact B1892247
  · exact B1892251
  · exact B1892255
  · exact B1892259
  · exact B1892263
  · exact B1892267
  · exact B1892271
  · exact B1892275
  · exact B1892279
  · exact B1892283
  · exact B1892287
  · exact B1892291
  · exact B1892295
  · exact B1892299
  · exact B1892303
  · exact B1892307
  · exact B1892311
  · exact B1892315
  · exact B1892319
  · exact B1892323
  · exact B1892327
  · exact B1892331
  · exact B1892335
  · exact B1892339
  · exact B1892343
  · exact B1892347
  · exact B1892351
  · exact B1892355
  · exact B1892359
  · exact B1892363
  · exact B1892367
  · exact B1892371
  · exact B1892375
  · exact B1892379
  · exact B1892383
  · exact B1892387
  · exact B1892391
  · exact B1892395
  · exact B1892399
  · exact B1892403
  · exact B1892407
  · exact B1892411
  · exact B1892415
  · exact B1892419
  · exact B1892423
  · exact B1892427
  · exact B1892431
  · exact B1892435
  · exact B1892439
  · exact B1892443
  · exact B1892447
  · exact B1892451
  · exact B1892455
  · exact B1892459
  · exact B1892463
  · exact B1892467
  · exact B1892471
  · exact B1892475
  · exact B1892479
  · exact B1892483
  · exact B1892487
  · exact B1892491
  · exact B1892495
  · exact B1892499
  · exact B1892503
  · exact B1892507
  · exact B1892511
  · exact B1892515
  · exact B1892519
  · exact B1892523
  · exact B1892527
  · exact B1892531
  · exact B1892535
  · exact B1892539
  · exact B1892543
  · exact B1892547
  · exact B1892551
  · exact B1892555
  · exact B1892559
  · exact B1892563
  · exact B1892567
  · exact B1892571
  · exact B1892575
  · exact B1892579
  · exact B1892583
  · exact B1892587
  · exact B1892591
  · exact B1892595
  · exact B1892599
  · exact B1892603
  · exact B1892607
  · exact B1892611
  · exact B1892615
  · exact B1892619
  · exact B1892623
  · exact B1892627
  · exact B1892631
  · exact B1892635
  · exact B1892639
  · exact B1892643
  · exact B1892647
  · exact B1892651
  · exact B1892655
  · exact B1892659
  · exact B1892663
  · exact B1892667
  · exact B1892671
  · exact B1892675
  · exact B1892679
  · exact B1892683
  · exact B1892687
  · exact B1892691
  · exact B1892695
  · exact B1892699
  · exact B1892703
  · exact B1892707
  · exact B1892711
  · exact B1892715
  · exact B1892719
  · exact B1892723
  · exact B1892727
  · exact B1892731
  · exact B1892735
  · exact B1892739
  · exact B1892743
  · exact B1892747
  · exact B1892751
  · exact B1892755
  · exact B1892759
  · exact B1892763
  · exact B1892767
  · exact B1892771
  · exact B1892775
  · exact B1892779
  · exact B1892783
  · exact B1892787
  · exact B1892791
  · exact B1892795
  · exact B1892799
  · exact B1892803
  · exact B1892807
  · exact B1892811
  · exact B1892815
  · exact B1892819
  · exact B1892823
  · exact B1892827
  · exact B1892831
  · exact B1892835
  · exact B1892839
  · exact B1892843
  · exact B1892847
  · exact B1892851
  · exact B1892855
  · exact B1892859
  · exact B1892863
  · exact B1892867
  · exact B1892871
  · exact B1892875
  · exact B1892879
  · exact B1892883
  · exact B1892887
  · exact B1892891
  · exact B1892895
  · exact B1892899
  · exact B1892903
  · exact B1892907
  · exact B1892911
  · exact B1892915
  · exact B1892919
  · exact B1892923
  · exact B1892927
  · exact B1892931
  · exact B1892935
  · exact B1892939
  · exact B1892943
  · exact B1892947
  · exact B1892951
  · exact B1892955
  · exact B1892959
  · exact B1892963
  · exact B1892967
  · exact B1892971
  · exact B1892975
  · exact B1892979
  · exact B1892983
  · exact B1892987
  · exact B1892991
  · exact B1892995
  · exact B1892999
  · exact B1893003
  · exact B1893007
  · exact B1893011
  · exact B1893015
  · exact B1893019
  · exact B1893023
  · exact B1893027
  · exact B1893031
  · exact B1893035
  · exact B1893039
  · exact B1893043
  · exact B1893047
  · exact B1893051
  · exact B1893055
  · exact B1893059
  · exact B1893063
  · exact B1893067
  · exact B1893071
  · exact B1893075
  · exact B1893079
  · exact B1893083
  · exact B1893087
  · exact B1893091
  · exact B1893095
  · exact B1893099
  · exact B1893103
  · exact B1893107
  · exact B1893111
  · exact B1893115
  · exact B1893119
  · exact B1893123
  · exact B1893127
  · exact B1893131
  · exact B1893135
  · exact B1893139
  · exact B1893143
  · exact B1893147
  · exact B1893151
  · exact B1893155
  · exact B1893159
  · exact B1893163
  · exact B1893167
  · exact B1893171
  · exact B1893175
  · exact B1893179
  · exact B1893183
  · exact B1893187
  · exact B1893191
  · exact B1893195
  · exact B1893199
  · exact B1893203
  · exact B1893207
  · exact B1893211
  · exact B1893215
  · exact B1893219
  · exact B1893223
  · exact B1893227
  · exact B1893231
  · exact B1893235
  · exact B1893239
  · exact B1893243
  · exact B1893247
  · exact B1893251
  · exact B1893255
  · exact B1893259
  · exact B1893263
  · exact B1893267
  · exact B1893271
  · exact B1893275
  · exact B1893279
  · exact B1893283
  · exact B1893287
  · exact B1893291
  · exact B1893295
  · exact B1893299
  · exact B1893303
  · exact B1893307
  · exact B1893311
  · exact B1893315
  · exact B1893319
  · exact B1893323
  · exact B1893327
  · exact B1893331
  · exact B1893335
  · exact B1893339
  · exact B1893343
  · exact B1893347
  · exact B1893351
  · exact B1893355
  · exact B1893359
  · exact B1893363
  · exact B1893367
  · exact B1893371
  · exact B1893375
  · exact B1893379
  · exact B1893383
  · exact B1893387
  · exact B1893391
  · exact B1893395
  · exact B1893399
  · exact B1893403
  · exact B1893407
  · exact B1893411
  · exact B1893415
  · exact B1893419
  · exact B1893423
  · exact B1893427
  · exact B1893431
  · exact B1893435
theorem solution (m : ℕ) (hlo : 1891435 ≤ m) (hhi : m ≤ 1893435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 472858 ≤ j := by omega
    have hj2 : j ≤ 473358 := by omega
    have hb : Blo 1891435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
