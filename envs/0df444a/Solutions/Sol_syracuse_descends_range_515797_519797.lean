-- Prove2me | solution 1 for syracuse_descends_range_515797_519797
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:24.947238+00:00
-- url     : https://prove2.me/submissions/d6319d22-9588-4795-8cf9-cb215ae8fab9

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


theorem B655381 : Blo 515797 655381 := bbase (se 6 (by rfl) ⟨15360, by rfl⟩ : syracuseStep 655381 = 30721) (by norm_num)
theorem B983117 : Blo 515797 983117 := bbase (se 3 (by rfl) ⟨184334, by rfl⟩ : syracuseStep 983117 = 368669) (by norm_num)
theorem B1310813 : Blo 515797 1310813 := bbase (se 3 (by rfl) ⟨245777, by rfl⟩ : syracuseStep 1310813 = 491555) (by norm_num)
theorem B4259957 : Blo 515797 4259957 := bbase (se 5 (by rfl) ⟨199685, by rfl⟩ : syracuseStep 4259957 = 399371) (by norm_num)
theorem B655553 : Blo 515797 655553 := bbase (se 2 (by rfl) ⟨245832, by rfl⟩ : syracuseStep 655553 = 491665) (by norm_num)
theorem B1474757 : Blo 515797 1474757 := bbase (se 4 (by rfl) ⟨138258, by rfl⟩ : syracuseStep 1474757 = 276517) (by norm_num)
theorem B786653 : Blo 515797 786653 := bbase (se 3 (by rfl) ⟨147497, by rfl⟩ : syracuseStep 786653 = 294995) (by norm_num)
theorem B983269 : Blo 515797 983269 := bbase (se 4 (by rfl) ⟨92181, by rfl⟩ : syracuseStep 983269 = 184363) (by norm_num)
theorem B655609 : Blo 515797 655609 := bbase (se 2 (by rfl) ⟨245853, by rfl⟩ : syracuseStep 655609 = 491707) (by norm_num)
theorem B1311005 : Blo 515797 1311005 := bbase (se 3 (by rfl) ⟨245813, by rfl⟩ : syracuseStep 1311005 = 491627) (by norm_num)
theorem B1245509 : Blo 515797 1245509 := bbase (se 4 (by rfl) ⟨116766, by rfl⟩ : syracuseStep 1245509 = 233533) (by norm_num)
theorem B2490709 : Blo 515797 2490709 := bbase (se 10 (by rfl) ⟨3648, by rfl⟩ : syracuseStep 2490709 = 7297) (by norm_num)
theorem B655705 : Blo 515797 655705 := bbase (se 2 (by rfl) ⟨245889, by rfl⟩ : syracuseStep 655705 = 491779) (by norm_num)
theorem B885109 : Blo 515797 885109 := bbase (se 5 (by rfl) ⟨41489, by rfl⟩ : syracuseStep 885109 = 82979) (by norm_num)
theorem B1245557 : Blo 515797 1245557 := bbase (se 5 (by rfl) ⟨58385, by rfl⟩ : syracuseStep 1245557 = 116771) (by norm_num)
theorem B1245565 : Blo 515797 1245565 := bbase (se 3 (by rfl) ⟨233543, by rfl⟩ : syracuseStep 1245565 = 467087) (by norm_num)
theorem B1474949 : Blo 515797 1474949 := bbase (se 4 (by rfl) ⟨138276, by rfl⟩ : syracuseStep 1474949 = 276553) (by norm_num)
theorem B655877 : Blo 515797 655877 := bbase (se 4 (by rfl) ⟨61488, by rfl⟩ : syracuseStep 655877 = 122977) (by norm_num)
theorem B983573 : Blo 515797 983573 := bbase (se 6 (by rfl) ⟨23052, by rfl⟩ : syracuseStep 983573 = 46105) (by norm_num)
theorem B655933 : Blo 515797 655933 := bbase (se 3 (by rfl) ⟨122987, by rfl⟩ : syracuseStep 655933 = 245975) (by norm_num)
theorem B1311349 : Blo 515797 1311349 := bbase (se 5 (by rfl) ⟨61469, by rfl⟩ : syracuseStep 1311349 = 122939) (by norm_num)
theorem B623225 : Blo 515797 623225 := bbase (se 2 (by rfl) ⟨233709, by rfl⟩ : syracuseStep 623225 = 467419) (by norm_num)
theorem B656029 : Blo 515797 656029 := bbase (se 3 (by rfl) ⟨123005, by rfl⟩ : syracuseStep 656029 = 246011) (by norm_num)
theorem B1311461 : Blo 515797 1311461 := bbase (se 4 (by rfl) ⟨122949, by rfl⟩ : syracuseStep 1311461 = 245899) (by norm_num)
theorem B590657 : Blo 515797 590657 := bbase (se 2 (by rfl) ⟨221496, by rfl⟩ : syracuseStep 590657 = 442993) (by norm_num)
theorem B656201 : Blo 515797 656201 := bbase (se 2 (by rfl) ⟨246075, by rfl⟩ : syracuseStep 656201 = 492151) (by norm_num)
theorem B787285 : Blo 515797 787285 := bbase (se 9 (by rfl) ⟨2306, by rfl⟩ : syracuseStep 787285 = 4613) (by norm_num)
theorem B2622293 : Blo 515797 2622293 := bbase (se 9 (by rfl) ⟨7682, by rfl⟩ : syracuseStep 2622293 = 15365) (by norm_num)
theorem B1966949 : Blo 515797 1966949 := bbase (se 4 (by rfl) ⟨184401, by rfl⟩ : syracuseStep 1966949 = 368803) (by norm_num)
theorem B623485 : Blo 515797 623485 := bbase (se 3 (by rfl) ⟨116903, by rfl⟩ : syracuseStep 623485 = 233807) (by norm_num)
theorem B656257 : Blo 515797 656257 := bbase (se 2 (by rfl) ⟨246096, by rfl⟩ : syracuseStep 656257 = 492193) (by norm_num)
theorem B1311653 : Blo 515797 1311653 := bbase (se 4 (by rfl) ⟨122967, by rfl⟩ : syracuseStep 1311653 = 245935) (by norm_num)
theorem B623533 : Blo 515797 623533 := bbase (se 3 (by rfl) ⟨116912, by rfl⟩ : syracuseStep 623533 = 233825) (by norm_num)
theorem B656353 : Blo 515797 656353 := bbase (se 2 (by rfl) ⟨246132, by rfl⟩ : syracuseStep 656353 = 492265) (by norm_num)
theorem B525425 : Blo 515797 525425 := bbase (se 2 (by rfl) ⟨197034, by rfl⟩ : syracuseStep 525425 = 394069) (by norm_num)
theorem B787573 : Blo 515797 787573 := bbase (se 5 (by rfl) ⟨36917, by rfl⟩ : syracuseStep 787573 = 73835) (by norm_num)
theorem B1967237 : Blo 515797 1967237 := bbase (se 4 (by rfl) ⟨184428, by rfl⟩ : syracuseStep 1967237 = 368857) (by norm_num)
theorem B656525 : Blo 515797 656525 := bbase (se 3 (by rfl) ⟨123098, by rfl⟩ : syracuseStep 656525 = 246197) (by norm_num)
theorem B656581 : Blo 515797 656581 := bbase (se 4 (by rfl) ⟨61554, by rfl⟩ : syracuseStep 656581 = 123109) (by norm_num)
theorem B1311997 : Blo 515797 1311997 := bbase (se 3 (by rfl) ⟨245999, by rfl⟩ : syracuseStep 1311997 = 491999) (by norm_num)
theorem B1049861 : Blo 515797 1049861 := bbase (se 4 (by rfl) ⟨98424, by rfl⟩ : syracuseStep 1049861 = 196849) (by norm_num)
theorem B984325 : Blo 515797 984325 := bbase (se 4 (by rfl) ⟨92280, by rfl⟩ : syracuseStep 984325 = 184561) (by norm_num)
theorem B656677 : Blo 515797 656677 := bbase (se 4 (by rfl) ⟨61563, by rfl⟩ : syracuseStep 656677 = 123127) (by norm_num)
theorem B1475941 : Blo 515797 1475941 := bbase (se 4 (by rfl) ⟨138369, by rfl⟩ : syracuseStep 1475941 = 276739) (by norm_num)
theorem B1246565 : Blo 515797 1246565 := bbase (se 4 (by rfl) ⟨116865, by rfl⟩ : syracuseStep 1246565 = 233731) (by norm_num)
theorem B1049965 : Blo 515797 1049965 := bbase (se 3 (by rfl) ⟨196868, by rfl⟩ : syracuseStep 1049965 = 393737) (by norm_num)
theorem B1312109 : Blo 515797 1312109 := bbase (se 3 (by rfl) ⟨246020, by rfl⟩ : syracuseStep 1312109 = 492041) (by norm_num)
theorem B525685 : Blo 515797 525685 := bbase (se 5 (by rfl) ⟨24641, by rfl⟩ : syracuseStep 525685 = 49283) (by norm_num)
theorem B984469 : Blo 515797 984469 := bbase (se 6 (by rfl) ⟨23073, by rfl⟩ : syracuseStep 984469 = 46147) (by norm_num)
theorem B656849 : Blo 515797 656849 := bbase (se 2 (by rfl) ⟨246318, by rfl⟩ : syracuseStep 656849 = 492637) (by norm_num)
theorem B656905 : Blo 515797 656905 := bbase (se 2 (by rfl) ⟨246339, by rfl⟩ : syracuseStep 656905 = 492679) (by norm_num)
theorem B1246757 : Blo 515797 1246757 := bbase (se 4 (by rfl) ⟨116883, by rfl⟩ : syracuseStep 1246757 = 233767) (by norm_num)
theorem B1312301 : Blo 515797 1312301 := bbase (se 3 (by rfl) ⟨246056, by rfl⟩ : syracuseStep 1312301 = 492113) (by norm_num)
theorem B984629 : Blo 515797 984629 := bbase (se 5 (by rfl) ⟨46154, by rfl⟩ : syracuseStep 984629 = 92309) (by norm_num)
theorem B624205 : Blo 515797 624205 := bbase (se 3 (by rfl) ⟨117038, by rfl⟩ : syracuseStep 624205 = 234077) (by norm_num)
theorem B657001 : Blo 515797 657001 := bbase (se 2 (by rfl) ⟨246375, by rfl⟩ : syracuseStep 657001 = 492751) (by norm_num)
theorem B2360981 : Blo 515797 2360981 := bbase (se 6 (by rfl) ⟨55335, by rfl⟩ : syracuseStep 2360981 = 110671) (by norm_num)
theorem B984773 : Blo 515797 984773 := bbase (se 4 (by rfl) ⟨92322, by rfl⟩ : syracuseStep 984773 = 184645) (by norm_num)
theorem B526025 : Blo 515797 526025 := bbase (se 2 (by rfl) ⟨197259, by rfl⟩ : syracuseStep 526025 = 394519) (by norm_num)
theorem B886477 : Blo 515797 886477 := bbase (se 3 (by rfl) ⟨166214, by rfl⟩ : syracuseStep 886477 = 332429) (by norm_num)
theorem B526057 : Blo 515797 526057 := bbase (se 2 (by rfl) ⟨197271, by rfl⟩ : syracuseStep 526057 = 394543) (by norm_num)
theorem B5310197 : Blo 515797 5310197 := bbase (se 5 (by rfl) ⟨248915, by rfl⟩ : syracuseStep 5310197 = 497831) (by norm_num)
theorem B2950901 : Blo 515797 2950901 := bbase (se 5 (by rfl) ⟨138323, by rfl⟩ : syracuseStep 2950901 = 276647) (by norm_num)
theorem B657173 : Blo 515797 657173 := bbase (se 6 (by rfl) ⟨15402, by rfl⟩ : syracuseStep 657173 = 30805) (by norm_num)
theorem B2361125 : Blo 515797 2361125 := bbase (se 4 (by rfl) ⟨221355, by rfl⟩ : syracuseStep 2361125 = 442711) (by norm_num)
theorem B1869605 : Blo 515797 1869605 := bbase (se 4 (by rfl) ⟨175275, by rfl⟩ : syracuseStep 1869605 = 350551) (by norm_num)
theorem B1050421 : Blo 515797 1050421 := bbase (se 5 (by rfl) ⟨49238, by rfl⟩ : syracuseStep 1050421 = 98477) (by norm_num)
theorem B657229 : Blo 515797 657229 := bbase (se 3 (by rfl) ⟨123230, by rfl⟩ : syracuseStep 657229 = 246461) (by norm_num)
theorem B1312645 : Blo 515797 1312645 := bbase (se 4 (by rfl) ⟨123060, by rfl⟩ : syracuseStep 1312645 = 246121) (by norm_num)
theorem B657325 : Blo 515797 657325 := bbase (se 3 (by rfl) ⟨123248, by rfl⟩ : syracuseStep 657325 = 246497) (by norm_num)
theorem B985061 : Blo 515797 985061 := bbase (se 4 (by rfl) ⟨92349, by rfl⟩ : syracuseStep 985061 = 184699) (by norm_num)
theorem B1312757 : Blo 515797 1312757 := bbase (se 5 (by rfl) ⟨61535, by rfl⟩ : syracuseStep 1312757 = 123071) (by norm_num)
theorem B526357 : Blo 515797 526357 := bbase (se 6 (by rfl) ⟨12336, by rfl⟩ : syracuseStep 526357 = 24673) (by norm_num)
theorem B526381 : Blo 515797 526381 := bbase (se 3 (by rfl) ⟨98696, by rfl⟩ : syracuseStep 526381 = 197393) (by norm_num)
theorem B657497 : Blo 515797 657497 := bbase (se 2 (by rfl) ⟨246561, by rfl⟩ : syracuseStep 657497 = 493123) (by norm_num)
theorem B2623589 : Blo 515797 2623589 := bbase (se 4 (by rfl) ⟨245961, by rfl⟩ : syracuseStep 2623589 = 491923) (by norm_num)
theorem B985213 : Blo 515797 985213 := bbase (se 3 (by rfl) ⟨184727, by rfl⟩ : syracuseStep 985213 = 369455) (by norm_num)
theorem B657553 : Blo 515797 657553 := bbase (se 2 (by rfl) ⟨246582, by rfl⟩ : syracuseStep 657553 = 493165) (by norm_num)
theorem B1312949 : Blo 515797 1312949 := bbase (se 5 (by rfl) ⟨61544, by rfl⟩ : syracuseStep 1312949 = 123089) (by norm_num)
theorem B4425941 : Blo 515797 4425941 := bbase (se 7 (by rfl) ⟨51866, by rfl⟩ : syracuseStep 4425941 = 103733) (by norm_num)
theorem B657649 : Blo 515797 657649 := bbase (se 2 (by rfl) ⟨246618, by rfl⟩ : syracuseStep 657649 = 493237) (by norm_num)
theorem B1968421 : Blo 515797 1968421 := bbase (se 4 (by rfl) ⟨184539, by rfl⟩ : syracuseStep 1968421 = 369079) (by norm_num)
theorem B657821 : Blo 515797 657821 := bbase (se 3 (by rfl) ⟨123341, by rfl⟩ : syracuseStep 657821 = 246683) (by norm_num)
theorem B985517 : Blo 515797 985517 := bbase (se 3 (by rfl) ⟨184784, by rfl⟩ : syracuseStep 985517 = 369569) (by norm_num)
theorem B1477045 : Blo 515797 1477045 := bbase (se 5 (by rfl) ⟨69236, by rfl⟩ : syracuseStep 1477045 = 138473) (by norm_num)
theorem B1051093 : Blo 515797 1051093 := bbase (se 7 (by rfl) ⟨12317, by rfl⟩ : syracuseStep 1051093 = 24635) (by norm_num)
theorem B592381 : Blo 515797 592381 := bbase (se 3 (by rfl) ⟨111071, by rfl⟩ : syracuseStep 592381 = 222143) (by norm_num)
theorem B1313293 : Blo 515797 1313293 := bbase (se 3 (by rfl) ⟨246242, by rfl⟩ : syracuseStep 1313293 = 492485) (by norm_num)
theorem B1968725 : Blo 515797 1968725 := bbase (se 8 (by rfl) ⟨11535, by rfl⟩ : syracuseStep 1968725 = 23071) (by norm_num)
theorem B1313405 : Blo 515797 1313405 := bbase (se 3 (by rfl) ⟨246263, by rfl⟩ : syracuseStep 1313405 = 492527) (by norm_num)
theorem B1313597 : Blo 515797 1313597 := bbase (se 3 (by rfl) ⟨246299, by rfl⟩ : syracuseStep 1313597 = 492599) (by norm_num)
theorem B2952085 : Blo 515797 2952085 := bbase (se 6 (by rfl) ⟨69189, by rfl⟩ : syracuseStep 2952085 = 138379) (by norm_num)
theorem B789421 : Blo 515797 789421 := bbase (se 3 (by rfl) ⟨148016, by rfl⟩ : syracuseStep 789421 = 296033) (by norm_num)
theorem B1870885 : Blo 515797 1870885 := bbase (se 4 (by rfl) ⟨175395, by rfl⟩ : syracuseStep 1870885 = 350791) (by norm_num)
theorem B1313941 : Blo 515797 1313941 := bbase (se 6 (by rfl) ⟨30795, by rfl⟩ : syracuseStep 1313941 = 61591) (by norm_num)
theorem B986269 : Blo 515797 986269 := bbase (se 3 (by rfl) ⟨184925, by rfl⟩ : syracuseStep 986269 = 369851) (by norm_num)
theorem B1314053 : Blo 515797 1314053 := bbase (se 4 (by rfl) ⟨123192, by rfl⟩ : syracuseStep 1314053 = 246385) (by norm_num)
theorem B986413 : Blo 515797 986413 := bbase (se 3 (by rfl) ⟨184952, by rfl⟩ : syracuseStep 986413 = 369905) (by norm_num)
theorem B2624885 : Blo 515797 2624885 := bbase (se 5 (by rfl) ⟨123041, by rfl⟩ : syracuseStep 2624885 = 246083) (by norm_num)
theorem B1314245 : Blo 515797 1314245 := bbase (se 4 (by rfl) ⟨123210, by rfl⟩ : syracuseStep 1314245 = 246421) (by norm_num)
theorem B1248709 : Blo 515797 1248709 := bbase (se 4 (by rfl) ⟨117066, by rfl⟩ : syracuseStep 1248709 = 234133) (by norm_num)
theorem B986573 : Blo 515797 986573 := bbase (se 3 (by rfl) ⟨184982, by rfl⟩ : syracuseStep 986573 = 369965) (by norm_num)
theorem B986717 : Blo 515797 986717 := bbase (se 3 (by rfl) ⟨185009, by rfl⟩ : syracuseStep 986717 = 370019) (by norm_num)
theorem B757405 : Blo 515797 757405 := bbase (se 3 (by rfl) ⟨142013, by rfl⟩ : syracuseStep 757405 = 284027) (by norm_num)
theorem B1314589 : Blo 515797 1314589 := bbase (se 3 (by rfl) ⟨246485, by rfl⟩ : syracuseStep 1314589 = 492971) (by norm_num)
theorem B757621 : Blo 515797 757621 := bbase (se 5 (by rfl) ⟨35513, by rfl⟩ : syracuseStep 757621 = 71027) (by norm_num)
theorem B1314701 : Blo 515797 1314701 := bbase (se 3 (by rfl) ⟨246506, by rfl⟩ : syracuseStep 1314701 = 493013) (by norm_num)
theorem B1478549 : Blo 515797 1478549 := bbase (se 6 (by rfl) ⟨34653, by rfl⟩ : syracuseStep 1478549 = 69307) (by norm_num)
theorem B1314893 : Blo 515797 1314893 := bbase (se 3 (by rfl) ⟨246542, by rfl⟩ : syracuseStep 1314893 = 493085) (by norm_num)
theorem B1741013 : Blo 515797 1741013 := bbase (se 7 (by rfl) ⟨20402, by rfl⟩ : syracuseStep 1741013 = 40805) (by norm_num)
theorem B8523989 : Blo 515797 8523989 := bbase (se 7 (by rfl) ⟨99890, by rfl⟩ : syracuseStep 8523989 = 199781) (by norm_num)
theorem B3739925 : Blo 515797 3739925 := bbase (se 6 (by rfl) ⟨87654, by rfl⟩ : syracuseStep 3739925 = 175309) (by norm_num)
theorem B3313973 : Blo 515797 3313973 := bbase (se 5 (by rfl) ⟨155342, by rfl⟩ : syracuseStep 3313973 = 310685) (by norm_num)
theorem B1315237 : Blo 515797 1315237 := bbase (se 4 (by rfl) ⟨123303, by rfl⟩ : syracuseStep 1315237 = 246607) (by norm_num)
theorem B1315349 : Blo 515797 1315349 := bbase (se 6 (by rfl) ⟨30828, by rfl⟩ : syracuseStep 1315349 = 61657) (by norm_num)
theorem B1741445 : Blo 515797 1741445 := bbase (se 4 (by rfl) ⟨163260, by rfl⟩ : syracuseStep 1741445 = 326521) (by norm_num)
theorem B2626181 : Blo 515797 2626181 := bbase (se 4 (by rfl) ⟨246204, by rfl⟩ : syracuseStep 2626181 = 492409) (by norm_num)
theorem B1970837 : Blo 515797 1970837 := bbase (se 6 (by rfl) ⟨46191, by rfl⟩ : syracuseStep 1970837 = 92383) (by norm_num)
theorem B1315541 : Blo 515797 1315541 := bbase (se 7 (by rfl) ⟨15416, by rfl⟩ : syracuseStep 1315541 = 30833) (by norm_num)
theorem B2954069 : Blo 515797 2954069 := bbase (se 9 (by rfl) ⟨8654, by rfl⟩ : syracuseStep 2954069 = 17309) (by norm_num)
theorem B1971125 : Blo 515797 1971125 := bbase (se 5 (by rfl) ⟨92396, by rfl⟩ : syracuseStep 1971125 = 184793) (by norm_num)
theorem B1741877 : Blo 515797 1741877 := bbase (se 5 (by rfl) ⟨81650, by rfl⟩ : syracuseStep 1741877 = 163301) (by norm_num)
theorem B2495573 : Blo 515797 2495573 := bbase (se 8 (by rfl) ⟨14622, by rfl⟩ : syracuseStep 2495573 = 29245) (by norm_num)
theorem B4428917 : Blo 515797 4428917 := bbase (se 5 (by rfl) ⟨207605, by rfl⟩ : syracuseStep 4428917 = 415211) (by norm_num)
theorem B1578293 : Blo 515797 1578293 := bbase (se 5 (by rfl) ⟨73982, by rfl⟩ : syracuseStep 1578293 = 147965) (by norm_num)
theorem B5051765 : Blo 515797 5051765 := bbase (se 5 (by rfl) ⟨236801, by rfl⟩ : syracuseStep 5051765 = 473603) (by norm_num)
theorem B1480133 : Blo 515797 1480133 := bbase (se 4 (by rfl) ⟨138762, by rfl⟩ : syracuseStep 1480133 = 277525) (by norm_num)
theorem B1742309 : Blo 515797 1742309 := bbase (se 4 (by rfl) ⟨163341, by rfl⟩ : syracuseStep 1742309 = 326683) (by norm_num)
theorem B1349357 : Blo 515797 1349357 := bbase (se 3 (by rfl) ⟨253004, by rfl⟩ : syracuseStep 1349357 = 506009) (by norm_num)
theorem B1742741 : Blo 515797 1742741 := bbase (se 6 (by rfl) ⟨40845, by rfl⟩ : syracuseStep 1742741 = 81691) (by norm_num)
theorem B2627477 : Blo 515797 2627477 := bbase (se 6 (by rfl) ⟨61581, by rfl⟩ : syracuseStep 2627477 = 123163) (by norm_num)
theorem B1972309 : Blo 515797 1972309 := bbase (se 8 (by rfl) ⟨11556, by rfl⟩ : syracuseStep 1972309 = 23113) (by norm_num)
theorem B1743173 : Blo 515797 1743173 := bbase (se 4 (by rfl) ⟨163422, by rfl⟩ : syracuseStep 1743173 = 326845) (by norm_num)
theorem B1972613 : Blo 515797 1972613 := bbase (se 4 (by rfl) ⟨184932, by rfl⟩ : syracuseStep 1972613 = 369865) (by norm_num)
theorem B2497205 : Blo 515797 2497205 := bbase (se 5 (by rfl) ⟨117056, by rfl⟩ : syracuseStep 2497205 = 234113) (by norm_num)
theorem B3939029 : Blo 515797 3939029 := bbase (se 7 (by rfl) ⟨46160, by rfl⟩ : syracuseStep 3939029 = 92321) (by norm_num)
theorem B1743605 : Blo 515797 1743605 := bbase (se 5 (by rfl) ⟨81731, by rfl⟩ : syracuseStep 1743605 = 163463) (by norm_num)
theorem B629537 : Blo 515797 629537 := bbase (se 2 (by rfl) ⟨236076, by rfl⟩ : syracuseStep 629537 = 472153) (by norm_num)
theorem B2235269 : Blo 515797 2235269 := bbase (se 4 (by rfl) ⟨209556, by rfl⟩ : syracuseStep 2235269 = 419113) (by norm_num)
theorem B2956277 : Blo 515797 2956277 := bbase (se 5 (by rfl) ⟨138575, by rfl⟩ : syracuseStep 2956277 = 277151) (by norm_num)
theorem B1744037 : Blo 515797 1744037 := bbase (se 4 (by rfl) ⟨163503, by rfl⟩ : syracuseStep 1744037 = 327007) (by norm_num)
theorem B2628773 : Blo 515797 2628773 := bbase (se 4 (by rfl) ⟨246447, by rfl⟩ : syracuseStep 2628773 = 492895) (by norm_num)
theorem B662753 : Blo 515797 662753 := bbase (se 2 (by rfl) ⟨248532, by rfl⟩ : syracuseStep 662753 = 497065) (by norm_num)
theorem B826661 : Blo 515797 826661 := bbase (se 4 (by rfl) ⟨77499, by rfl⟩ : syracuseStep 826661 = 154999) (by norm_num)
theorem B826789 : Blo 515797 826789 := bbase (se 4 (by rfl) ⟨77511, by rfl⟩ : syracuseStep 826789 = 155023) (by norm_num)
theorem B826853 : Blo 515797 826853 := bbase (se 4 (by rfl) ⟨77517, by rfl⟩ : syracuseStep 826853 = 155035) (by norm_num)
theorem B630289 : Blo 515797 630289 := bbase (se 2 (by rfl) ⟨236358, by rfl⟩ : syracuseStep 630289 = 472717) (by norm_num)
theorem B1121861 : Blo 515797 1121861 := bbase (se 4 (by rfl) ⟨105174, by rfl⟩ : syracuseStep 1121861 = 210349) (by norm_num)
theorem B8822357 : Blo 515797 8822357 := bbase (se 8 (by rfl) ⟨51693, by rfl⟩ : syracuseStep 8822357 = 103387) (by norm_num)
theorem B1744469 : Blo 515797 1744469 := bbase (se 8 (by rfl) ⟨10221, by rfl⟩ : syracuseStep 1744469 = 20443) (by norm_num)
theorem B2203301 : Blo 515797 2203301 := bbase (se 4 (by rfl) ⟨206559, by rfl⟩ : syracuseStep 2203301 = 413119) (by norm_num)
theorem B1351669 : Blo 515797 1351669 := bbase (se 5 (by rfl) ⟨63359, by rfl⟩ : syracuseStep 1351669 = 126719) (by norm_num)
theorem B1744901 : Blo 515797 1744901 := bbase (se 4 (by rfl) ⟨163584, by rfl⟩ : syracuseStep 1744901 = 327169) (by norm_num)
theorem B3744053 : Blo 515797 3744053 := bbase (se 5 (by rfl) ⟨175502, by rfl⟩ : syracuseStep 3744053 = 351005) (by norm_num)
theorem B1745333 : Blo 515797 1745333 := bbase (se 5 (by rfl) ⟨81812, by rfl⟩ : syracuseStep 1745333 = 163625) (by norm_num)
theorem B2630069 : Blo 515797 2630069 := bbase (se 5 (by rfl) ⟨123284, by rfl⟩ : syracuseStep 2630069 = 246569) (by norm_num)
theorem B631261 : Blo 515797 631261 := bbase (se 3 (by rfl) ⟨118361, by rfl⟩ : syracuseStep 631261 = 236723) (by norm_num)
theorem B1122797 : Blo 515797 1122797 := bbase (se 3 (by rfl) ⟨210524, by rfl⟩ : syracuseStep 1122797 = 421049) (by norm_num)
theorem B828173 : Blo 515797 828173 := bbase (se 3 (by rfl) ⟨155282, by rfl⟩ : syracuseStep 828173 = 310565) (by norm_num)
theorem B795413 : Blo 515797 795413 := bbase (se 6 (by rfl) ⟨18642, by rfl⟩ : syracuseStep 795413 = 37285) (by norm_num)
theorem B1745765 : Blo 515797 1745765 := bbase (se 4 (by rfl) ⟨163665, by rfl⟩ : syracuseStep 1745765 = 327331) (by norm_num)
theorem B828301 : Blo 515797 828301 := bbase (se 3 (by rfl) ⟨155306, by rfl⟩ : syracuseStep 828301 = 310613) (by norm_num)
theorem B1746197 : Blo 515797 1746197 := bbase (se 6 (by rfl) ⟨40926, by rfl⟩ : syracuseStep 1746197 = 81853) (by norm_num)
theorem B1123661 : Blo 515797 1123661 := bbase (se 3 (by rfl) ⟨210686, by rfl⟩ : syracuseStep 1123661 = 421373) (by norm_num)
theorem B2368901 : Blo 515797 2368901 := bbase (se 4 (by rfl) ⟨222084, by rfl⟩ : syracuseStep 2368901 = 444169) (by norm_num)
theorem B697901 : Blo 515797 697901 := bbase (se 3 (by rfl) ⟨130856, by rfl⟩ : syracuseStep 697901 = 261713) (by norm_num)
theorem B829109 : Blo 515797 829109 := bbase (se 5 (by rfl) ⟨38864, by rfl⟩ : syracuseStep 829109 = 77729) (by norm_num)
theorem B1746629 : Blo 515797 1746629 := bbase (se 4 (by rfl) ⟨163746, by rfl⟩ : syracuseStep 1746629 = 327493) (by norm_num)
theorem B2631365 : Blo 515797 2631365 := bbase (se 4 (by rfl) ⟨246690, by rfl⟩ : syracuseStep 2631365 = 493381) (by norm_num)
theorem B2369429 : Blo 515797 2369429 := bbase (se 6 (by rfl) ⟨55533, by rfl⟩ : syracuseStep 2369429 = 111067) (by norm_num)
theorem B1124285 : Blo 515797 1124285 := bbase (se 3 (by rfl) ⟨210803, by rfl⟩ : syracuseStep 1124285 = 421607) (by norm_num)
theorem B829397 : Blo 515797 829397 := bbase (se 7 (by rfl) ⟨9719, by rfl⟩ : syracuseStep 829397 = 19439) (by norm_num)
theorem B665705 : Blo 515797 665705 := bbase (se 2 (by rfl) ⟨249639, by rfl⟩ : syracuseStep 665705 = 499279) (by norm_num)
theorem B1747061 : Blo 515797 1747061 := bbase (se 5 (by rfl) ⟨81893, by rfl⟩ : syracuseStep 1747061 = 163787) (by norm_num)
theorem B698533 : Blo 515797 698533 := bbase (se 4 (by rfl) ⟨65487, by rfl⟩ : syracuseStep 698533 = 130975) (by norm_num)
theorem B4466933 : Blo 515797 4466933 := bbase (se 5 (by rfl) ⟨209387, by rfl⟩ : syracuseStep 4466933 = 418775) (by norm_num)
theorem B698653 : Blo 515797 698653 := bbase (se 3 (by rfl) ⟨130997, by rfl⟩ : syracuseStep 698653 = 261995) (by norm_num)
theorem B1091917 : Blo 515797 1091917 := bbase (se 3 (by rfl) ⟨204734, by rfl⟩ : syracuseStep 1091917 = 409469) (by norm_num)
theorem B829813 : Blo 515797 829813 := bbase (se 5 (by rfl) ⟨38897, by rfl⟩ : syracuseStep 829813 = 77795) (by norm_num)
theorem B666037 : Blo 515797 666037 := bbase (se 5 (by rfl) ⟨31220, by rfl⟩ : syracuseStep 666037 = 62441) (by norm_num)
theorem B1747493 : Blo 515797 1747493 := bbase (se 4 (by rfl) ⟨163827, by rfl⟩ : syracuseStep 1747493 = 327655) (by norm_num)
theorem B994069 : Blo 515797 994069 := bbase (se 6 (by rfl) ⟨23298, by rfl⟩ : syracuseStep 994069 = 46597) (by norm_num)
theorem B1747925 : Blo 515797 1747925 := bbase (se 7 (by rfl) ⟨20483, by rfl⟩ : syracuseStep 1747925 = 40967) (by norm_num)
theorem B830749 : Blo 515797 830749 := bbase (se 3 (by rfl) ⟨155765, by rfl⟩ : syracuseStep 830749 = 311531) (by norm_num)
theorem B5680469 : Blo 515797 5680469 := bbase (se 11 (by rfl) ⟨4160, by rfl⟩ : syracuseStep 5680469 = 8321) (by norm_num)
theorem B1748357 : Blo 515797 1748357 := bbase (se 4 (by rfl) ⟨163908, by rfl⟩ : syracuseStep 1748357 = 327817) (by norm_num)
theorem B7450325 : Blo 515797 7450325 := bbase (se 7 (by rfl) ⟨87308, by rfl⟩ : syracuseStep 7450325 = 174617) (by norm_num)
theorem B1748789 : Blo 515797 1748789 := bbase (se 5 (by rfl) ⟨81974, by rfl⟩ : syracuseStep 1748789 = 163949) (by norm_num)
theorem B2207573 : Blo 515797 2207573 := bbase (se 9 (by rfl) ⟨6467, by rfl⟩ : syracuseStep 2207573 = 12935) (by norm_num)
theorem B929677 : Blo 515797 929677 := bbase (se 3 (by rfl) ⟨174314, by rfl⟩ : syracuseStep 929677 = 348629) (by norm_num)
theorem B897173 : Blo 515797 897173 := bbase (se 6 (by rfl) ⟨21027, by rfl⟩ : syracuseStep 897173 = 42055) (by norm_num)
theorem B1749221 : Blo 515797 1749221 := bbase (se 4 (by rfl) ⟨163989, by rfl⟩ : syracuseStep 1749221 = 327979) (by norm_num)
theorem B831941 : Blo 515797 831941 := bbase (se 4 (by rfl) ⟨77994, by rfl⟩ : syracuseStep 831941 = 155989) (by norm_num)
theorem B930253 : Blo 515797 930253 := bbase (se 3 (by rfl) ⟨174422, by rfl⟩ : syracuseStep 930253 = 348845) (by norm_num)
theorem B995917 : Blo 515797 995917 := bbase (se 3 (by rfl) ⟨186734, by rfl⟩ : syracuseStep 995917 = 373469) (by norm_num)
theorem B832133 : Blo 515797 832133 := bbase (se 4 (by rfl) ⟨78012, by rfl⟩ : syracuseStep 832133 = 156025) (by norm_num)
theorem B1749653 : Blo 515797 1749653 := bbase (se 6 (by rfl) ⟨41007, by rfl⟩ : syracuseStep 1749653 = 82015) (by norm_num)
theorem B2700053 : Blo 515797 2700053 := bbase (se 6 (by rfl) ⟨63282, by rfl⟩ : syracuseStep 2700053 = 126565) (by norm_num)
theorem B1750085 : Blo 515797 1750085 := bbase (se 4 (by rfl) ⟨164070, by rfl⟩ : syracuseStep 1750085 = 328141) (by norm_num)
theorem B1160549 : Blo 515797 1160549 := bbase (se 4 (by rfl) ⟨108801, by rfl⟩ : syracuseStep 1160549 = 217603) (by norm_num)
theorem B1160621 : Blo 515797 1160621 := bbase (se 3 (by rfl) ⟨217616, by rfl⟩ : syracuseStep 1160621 = 435233) (by norm_num)
theorem B1160693 : Blo 515797 1160693 := bbase (se 5 (by rfl) ⟨54407, by rfl⟩ : syracuseStep 1160693 = 108815) (by norm_num)
theorem B1750517 : Blo 515797 1750517 := bbase (se 5 (by rfl) ⟨82055, by rfl⟩ : syracuseStep 1750517 = 164111) (by norm_num)
theorem B1160765 : Blo 515797 1160765 := bbase (se 3 (by rfl) ⟨217643, by rfl⟩ : syracuseStep 1160765 = 435287) (by norm_num)
theorem B2209349 : Blo 515797 2209349 := bbase (se 4 (by rfl) ⟨207126, by rfl⟩ : syracuseStep 2209349 = 414253) (by norm_num)
theorem B40416853 : Blo 515797 40416853 := bbase (se 8 (by rfl) ⟨236817, by rfl⟩ : syracuseStep 40416853 = 473635) (by norm_num)
theorem B1160837 : Blo 515797 1160837 := bbase (se 4 (by rfl) ⟨108828, by rfl⟩ : syracuseStep 1160837 = 217657) (by norm_num)
theorem B1160909 : Blo 515797 1160909 := bbase (se 3 (by rfl) ⟨217670, by rfl⟩ : syracuseStep 1160909 = 435341) (by norm_num)
theorem B997085 : Blo 515797 997085 := bbase (se 3 (by rfl) ⟨186953, by rfl⟩ : syracuseStep 997085 = 373907) (by norm_num)
theorem B1652501 : Blo 515797 1652501 := bbase (se 6 (by rfl) ⟨38730, by rfl⟩ : syracuseStep 1652501 = 77461) (by norm_num)
theorem B1160981 : Blo 515797 1160981 := bbase (se 6 (by rfl) ⟨27210, by rfl⟩ : syracuseStep 1160981 = 54421) (by norm_num)
theorem B931637 : Blo 515797 931637 := bbase (se 5 (by rfl) ⟨43670, by rfl⟩ : syracuseStep 931637 = 87341) (by norm_num)
theorem B2209589 : Blo 515797 2209589 := bbase (se 5 (by rfl) ⟨103574, by rfl⟩ : syracuseStep 2209589 = 207149) (by norm_num)
theorem B1161053 : Blo 515797 1161053 := bbase (se 3 (by rfl) ⟨217697, by rfl⟩ : syracuseStep 1161053 = 435395) (by norm_num)
theorem B1161125 : Blo 515797 1161125 := bbase (se 4 (by rfl) ⟨108855, by rfl⟩ : syracuseStep 1161125 = 217711) (by norm_num)
theorem B1750949 : Blo 515797 1750949 := bbase (se 4 (by rfl) ⟨164151, by rfl⟩ : syracuseStep 1750949 = 328303) (by norm_num)
theorem B1161197 : Blo 515797 1161197 := bbase (se 3 (by rfl) ⟨217724, by rfl⟩ : syracuseStep 1161197 = 435449) (by norm_num)
theorem B1161269 : Blo 515797 1161269 := bbase (se 5 (by rfl) ⟨54434, by rfl⟩ : syracuseStep 1161269 = 108869) (by norm_num)
theorem B1325117 : Blo 515797 1325117 := bbase (se 3 (by rfl) ⟨248459, by rfl⟩ : syracuseStep 1325117 = 496919) (by norm_num)
theorem B1161341 : Blo 515797 1161341 := bbase (se 3 (by rfl) ⟨217751, by rfl⟩ : syracuseStep 1161341 = 435503) (by norm_num)
theorem B1161413 : Blo 515797 1161413 := bbase (se 4 (by rfl) ⟨108882, by rfl⟩ : syracuseStep 1161413 = 217765) (by norm_num)
theorem B3324149 : Blo 515797 3324149 := bbase (se 5 (by rfl) ⟨155819, by rfl⟩ : syracuseStep 3324149 = 311639) (by norm_num)
theorem B735493 : Blo 515797 735493 := bbase (se 4 (by rfl) ⟨68952, by rfl⟩ : syracuseStep 735493 = 137905) (by norm_num)
theorem B1161485 : Blo 515797 1161485 := bbase (se 3 (by rfl) ⟨217778, by rfl⟩ : syracuseStep 1161485 = 435557) (by norm_num)
theorem B3946805 : Blo 515797 3946805 := bbase (se 5 (by rfl) ⟨185006, by rfl⟩ : syracuseStep 3946805 = 370013) (by norm_num)
theorem B1161557 : Blo 515797 1161557 := bbase (se 10 (by rfl) ⟨1701, by rfl⟩ : syracuseStep 1161557 = 3403) (by norm_num)
theorem B1751381 : Blo 515797 1751381 := bbase (se 10 (by rfl) ⟨2565, by rfl⟩ : syracuseStep 1751381 = 5131) (by norm_num)
theorem B1161629 : Blo 515797 1161629 := bbase (se 3 (by rfl) ⟨217805, by rfl⟩ : syracuseStep 1161629 = 435611) (by norm_num)
theorem B1161701 : Blo 515797 1161701 := bbase (se 4 (by rfl) ⟨108909, by rfl⟩ : syracuseStep 1161701 = 217819) (by norm_num)
theorem B1161773 : Blo 515797 1161773 := bbase (se 3 (by rfl) ⟨217832, by rfl⟩ : syracuseStep 1161773 = 435665) (by norm_num)
theorem B1620533 : Blo 515797 1620533 := bbase (se 5 (by rfl) ⟨75962, by rfl⟩ : syracuseStep 1620533 = 151925) (by norm_num)
theorem B1161845 : Blo 515797 1161845 := bbase (se 5 (by rfl) ⟨54461, by rfl⟩ : syracuseStep 1161845 = 108923) (by norm_num)
theorem B1161917 : Blo 515797 1161917 := bbase (se 3 (by rfl) ⟨217859, by rfl⟩ : syracuseStep 1161917 = 435719) (by norm_num)
theorem B1161989 : Blo 515797 1161989 := bbase (se 4 (by rfl) ⟨108936, by rfl⟩ : syracuseStep 1161989 = 217873) (by norm_num)
theorem B1751813 : Blo 515797 1751813 := bbase (se 4 (by rfl) ⟨164232, by rfl⟩ : syracuseStep 1751813 = 328465) (by norm_num)
theorem B1162061 : Blo 515797 1162061 := bbase (se 3 (by rfl) ⟨217886, by rfl⟩ : syracuseStep 1162061 = 435773) (by norm_num)
theorem B736085 : Blo 515797 736085 := bbase (se 9 (by rfl) ⟨2156, by rfl⟩ : syracuseStep 736085 = 4313) (by norm_num)
theorem B1653605 : Blo 515797 1653605 := bbase (se 4 (by rfl) ⟨155025, by rfl⟩ : syracuseStep 1653605 = 310051) (by norm_num)
theorem B1162133 : Blo 515797 1162133 := bbase (se 6 (by rfl) ⟨27237, by rfl⟩ : syracuseStep 1162133 = 54475) (by norm_num)
theorem B736165 : Blo 515797 736165 := bbase (se 4 (by rfl) ⟨69015, by rfl⟩ : syracuseStep 736165 = 138031) (by norm_num)
theorem B1162205 : Blo 515797 1162205 := bbase (se 3 (by rfl) ⟨217913, by rfl⟩ : syracuseStep 1162205 = 435827) (by norm_num)
theorem B1260533 : Blo 515797 1260533 := bbase (se 5 (by rfl) ⟨59087, by rfl⟩ : syracuseStep 1260533 = 118175) (by norm_num)
theorem B736285 : Blo 515797 736285 := bbase (se 3 (by rfl) ⟨138053, by rfl⟩ : syracuseStep 736285 = 276107) (by norm_num)
theorem B1162277 : Blo 515797 1162277 := bbase (se 4 (by rfl) ⟨108963, by rfl⟩ : syracuseStep 1162277 = 217927) (by norm_num)
theorem B1162349 : Blo 515797 1162349 := bbase (se 3 (by rfl) ⟨217940, by rfl⟩ : syracuseStep 1162349 = 435881) (by norm_num)
theorem B736381 : Blo 515797 736381 := bbase (se 3 (by rfl) ⟨138071, by rfl⟩ : syracuseStep 736381 = 276143) (by norm_num)
theorem B1162421 : Blo 515797 1162421 := bbase (se 5 (by rfl) ⟨54488, by rfl⟩ : syracuseStep 1162421 = 108977) (by norm_num)
theorem B1752245 : Blo 515797 1752245 := bbase (se 5 (by rfl) ⟨82136, by rfl⟩ : syracuseStep 1752245 = 164273) (by norm_num)
theorem B670933 : Blo 515797 670933 := bbase (se 7 (by rfl) ⟨7862, by rfl⟩ : syracuseStep 670933 = 15725) (by norm_num)
theorem B1162493 : Blo 515797 1162493 := bbase (se 3 (by rfl) ⟨217967, by rfl⟩ : syracuseStep 1162493 = 435935) (by norm_num)
theorem B1162565 : Blo 515797 1162565 := bbase (se 4 (by rfl) ⟨108990, by rfl⟩ : syracuseStep 1162565 = 217981) (by norm_num)
theorem B27344213 : Blo 515797 27344213 := bbase (se 11 (by rfl) ⟨20027, by rfl⟩ : syracuseStep 27344213 = 40055) (by norm_num)
theorem B1162637 : Blo 515797 1162637 := bbase (se 3 (by rfl) ⟨217994, by rfl⟩ : syracuseStep 1162637 = 435989) (by norm_num)
theorem B1162709 : Blo 515797 1162709 := bbase (se 7 (by rfl) ⟨13625, by rfl⟩ : syracuseStep 1162709 = 27251) (by norm_num)
theorem B1162781 : Blo 515797 1162781 := bbase (se 3 (by rfl) ⟨218021, by rfl⟩ : syracuseStep 1162781 = 436043) (by norm_num)
theorem B1162853 : Blo 515797 1162853 := bbase (se 4 (by rfl) ⟨109017, by rfl⟩ : syracuseStep 1162853 = 218035) (by norm_num)
theorem B1752677 : Blo 515797 1752677 := bbase (se 4 (by rfl) ⟨164313, by rfl⟩ : syracuseStep 1752677 = 328627) (by norm_num)
theorem B736877 : Blo 515797 736877 := bbase (se 3 (by rfl) ⟨138164, by rfl⟩ : syracuseStep 736877 = 276329) (by norm_num)
theorem B1162925 : Blo 515797 1162925 := bbase (se 3 (by rfl) ⟨218048, by rfl⟩ : syracuseStep 1162925 = 436097) (by norm_num)
theorem B1162997 : Blo 515797 1162997 := bbase (se 5 (by rfl) ⟨54515, by rfl⟩ : syracuseStep 1162997 = 109031) (by norm_num)
theorem B1163069 : Blo 515797 1163069 := bbase (se 3 (by rfl) ⟨218075, by rfl⟩ : syracuseStep 1163069 = 436151) (by norm_num)
theorem B1163141 : Blo 515797 1163141 := bbase (se 4 (by rfl) ⟨109044, by rfl⟩ : syracuseStep 1163141 = 218089) (by norm_num)
theorem B1163213 : Blo 515797 1163213 := bbase (se 3 (by rfl) ⟨218102, by rfl⟩ : syracuseStep 1163213 = 436205) (by norm_num)
theorem B1163285 : Blo 515797 1163285 := bbase (se 6 (by rfl) ⟨27264, by rfl⟩ : syracuseStep 1163285 = 54529) (by norm_num)
theorem B1753109 : Blo 515797 1753109 := bbase (se 6 (by rfl) ⟨41088, by rfl⟩ : syracuseStep 1753109 = 82177) (by norm_num)
theorem B2211877 : Blo 515797 2211877 := bbase (se 4 (by rfl) ⟨207363, by rfl⟩ : syracuseStep 2211877 = 414727) (by norm_num)
theorem B1163357 : Blo 515797 1163357 := bbase (se 3 (by rfl) ⟨218129, by rfl⟩ : syracuseStep 1163357 = 436259) (by norm_num)
theorem B737429 : Blo 515797 737429 := bbase (se 6 (by rfl) ⟨17283, by rfl⟩ : syracuseStep 737429 = 34567) (by norm_num)
theorem B1163429 : Blo 515797 1163429 := bbase (se 4 (by rfl) ⟨109071, by rfl⟩ : syracuseStep 1163429 = 218143) (by norm_num)
theorem B4538549 : Blo 515797 4538549 := bbase (se 5 (by rfl) ⟨212744, by rfl⟩ : syracuseStep 4538549 = 425489) (by norm_num)
theorem B1163501 : Blo 515797 1163501 := bbase (se 3 (by rfl) ⟨218156, by rfl⟩ : syracuseStep 1163501 = 436313) (by norm_num)
theorem B1163573 : Blo 515797 1163573 := bbase (se 5 (by rfl) ⟨54542, by rfl⟩ : syracuseStep 1163573 = 109085) (by norm_num)
theorem B999749 : Blo 515797 999749 := bbase (se 4 (by rfl) ⟨93726, by rfl⟩ : syracuseStep 999749 = 187453) (by norm_num)
theorem B3555701 : Blo 515797 3555701 := bbase (se 5 (by rfl) ⟨166673, by rfl⟩ : syracuseStep 3555701 = 333347) (by norm_num)
theorem B1163645 : Blo 515797 1163645 := bbase (se 3 (by rfl) ⟨218183, by rfl⟩ : syracuseStep 1163645 = 436367) (by norm_num)
theorem B639389 : Blo 515797 639389 := bbase (se 3 (by rfl) ⟨119885, by rfl⟩ : syracuseStep 639389 = 239771) (by norm_num)
theorem B1163717 : Blo 515797 1163717 := bbase (se 4 (by rfl) ⟨109098, by rfl⟩ : syracuseStep 1163717 = 218197) (by norm_num)
theorem B1753541 : Blo 515797 1753541 := bbase (se 4 (by rfl) ⟨164394, by rfl⟩ : syracuseStep 1753541 = 328789) (by norm_num)
theorem B1163789 : Blo 515797 1163789 := bbase (se 3 (by rfl) ⟨218210, by rfl⟩ : syracuseStep 1163789 = 436421) (by norm_num)
theorem B4964885 : Blo 515797 4964885 := bbase (se 6 (by rfl) ⟨116364, by rfl⟩ : syracuseStep 4964885 = 232729) (by norm_num)
theorem B1163861 : Blo 515797 1163861 := bbase (se 8 (by rfl) ⟨6819, by rfl⟩ : syracuseStep 1163861 = 13639) (by norm_num)
theorem B1163933 : Blo 515797 1163933 := bbase (se 3 (by rfl) ⟨218237, by rfl⟩ : syracuseStep 1163933 = 436475) (by norm_num)
theorem B1655525 : Blo 515797 1655525 := bbase (se 4 (by rfl) ⟨155205, by rfl⟩ : syracuseStep 1655525 = 310411) (by norm_num)
theorem B1164005 : Blo 515797 1164005 := bbase (se 4 (by rfl) ⟨109125, by rfl⟩ : syracuseStep 1164005 = 218251) (by norm_num)
theorem B1164077 : Blo 515797 1164077 := bbase (se 3 (by rfl) ⟨218264, by rfl⟩ : syracuseStep 1164077 = 436529) (by norm_num)
theorem B1164149 : Blo 515797 1164149 := bbase (se 5 (by rfl) ⟨54569, by rfl⟩ : syracuseStep 1164149 = 109139) (by norm_num)
theorem B1753973 : Blo 515797 1753973 := bbase (se 5 (by rfl) ⟨82217, by rfl⟩ : syracuseStep 1753973 = 164435) (by norm_num)
theorem B738181 : Blo 515797 738181 := bbase (se 4 (by rfl) ⟨69204, by rfl⟩ : syracuseStep 738181 = 138409) (by norm_num)
theorem B1164221 : Blo 515797 1164221 := bbase (se 3 (by rfl) ⟨218291, by rfl⟩ : syracuseStep 1164221 = 436583) (by norm_num)
theorem B1164293 : Blo 515797 1164293 := bbase (se 4 (by rfl) ⟨109152, by rfl⟩ : syracuseStep 1164293 = 218305) (by norm_num)
theorem B1164365 : Blo 515797 1164365 := bbase (se 3 (by rfl) ⟨218318, by rfl⟩ : syracuseStep 1164365 = 436637) (by norm_num)
theorem B5883029 : Blo 515797 5883029 := bbase (se 6 (by rfl) ⟨137883, by rfl⟩ : syracuseStep 5883029 = 275767) (by norm_num)
theorem B1164437 : Blo 515797 1164437 := bbase (se 6 (by rfl) ⟨27291, by rfl⟩ : syracuseStep 1164437 = 54583) (by norm_num)
theorem B2802869 : Blo 515797 2802869 := bbase (se 5 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 2802869 = 262769) (by norm_num)
theorem B1164509 : Blo 515797 1164509 := bbase (se 3 (by rfl) ⟨218345, by rfl⟩ : syracuseStep 1164509 = 436691) (by norm_num)
theorem B3720437 : Blo 515797 3720437 := bbase (se 5 (by rfl) ⟨174395, by rfl⟩ : syracuseStep 3720437 = 348791) (by norm_num)
theorem B4211957 : Blo 515797 4211957 := bbase (se 5 (by rfl) ⟨197435, by rfl⟩ : syracuseStep 4211957 = 394871) (by norm_num)
theorem B1164581 : Blo 515797 1164581 := bbase (se 4 (by rfl) ⟨109179, by rfl⟩ : syracuseStep 1164581 = 218359) (by norm_num)
theorem B1164653 : Blo 515797 1164653 := bbase (se 3 (by rfl) ⟨218372, by rfl⟩ : syracuseStep 1164653 = 436745) (by norm_num)
theorem B1164725 : Blo 515797 1164725 := bbase (se 5 (by rfl) ⟨54596, by rfl⟩ : syracuseStep 1164725 = 109193) (by norm_num)
theorem B2213365 : Blo 515797 2213365 := bbase (se 5 (by rfl) ⟨103751, by rfl⟩ : syracuseStep 2213365 = 207503) (by norm_num)
theorem B1164797 : Blo 515797 1164797 := bbase (se 3 (by rfl) ⟨218399, by rfl⟩ : syracuseStep 1164797 = 436799) (by norm_num)
theorem B2213381 : Blo 515797 2213381 := bbase (se 4 (by rfl) ⟨207504, by rfl⟩ : syracuseStep 2213381 = 415009) (by norm_num)
theorem B1590821 : Blo 515797 1590821 := bbase (se 4 (by rfl) ⟨149139, by rfl⟩ : syracuseStep 1590821 = 298279) (by norm_num)
theorem B1164869 : Blo 515797 1164869 := bbase (se 4 (by rfl) ⟨109206, by rfl⟩ : syracuseStep 1164869 = 218413) (by norm_num)
theorem B2246213 : Blo 515797 2246213 := bbase (se 4 (by rfl) ⟨210582, by rfl⟩ : syracuseStep 2246213 = 421165) (by norm_num)
theorem B1164941 : Blo 515797 1164941 := bbase (se 3 (by rfl) ⟨218426, by rfl⟩ : syracuseStep 1164941 = 436853) (by norm_num)
theorem B738973 : Blo 515797 738973 := bbase (se 3 (by rfl) ⟨138557, by rfl⟩ : syracuseStep 738973 = 277115) (by norm_num)
theorem B1165013 : Blo 515797 1165013 := bbase (se 7 (by rfl) ⟨13652, by rfl⟩ : syracuseStep 1165013 = 27305) (by norm_num)
theorem B3032821 : Blo 515797 3032821 := bbase (se 5 (by rfl) ⟨142163, by rfl⟩ : syracuseStep 3032821 = 284327) (by norm_num)
theorem B7096085 : Blo 515797 7096085 := bbase (se 6 (by rfl) ⟨166314, by rfl⟩ : syracuseStep 7096085 = 332629) (by norm_num)
theorem B1165085 : Blo 515797 1165085 := bbase (se 3 (by rfl) ⟨218453, by rfl⟩ : syracuseStep 1165085 = 436907) (by norm_num)
theorem B935725 : Blo 515797 935725 := bbase (se 3 (by rfl) ⟨175448, by rfl⟩ : syracuseStep 935725 = 350897) (by norm_num)
theorem B15976277 : Blo 515797 15976277 := bbase (se 9 (by rfl) ⟨46805, by rfl⟩ : syracuseStep 15976277 = 93611) (by norm_num)
theorem B1165157 : Blo 515797 1165157 := bbase (se 4 (by rfl) ⟨109233, by rfl⟩ : syracuseStep 1165157 = 218467) (by norm_num)
theorem B1165229 : Blo 515797 1165229 := bbase (se 3 (by rfl) ⟨218480, by rfl⟩ : syracuseStep 1165229 = 436961) (by norm_num)
theorem B739309 : Blo 515797 739309 := bbase (se 3 (by rfl) ⟨138620, by rfl⟩ : syracuseStep 739309 = 277241) (by norm_num)
theorem B1165301 : Blo 515797 1165301 := bbase (se 5 (by rfl) ⟨54623, by rfl⟩ : syracuseStep 1165301 = 109247) (by norm_num)
theorem B1165373 : Blo 515797 1165373 := bbase (se 3 (by rfl) ⟨218507, by rfl⟩ : syracuseStep 1165373 = 437015) (by norm_num)
theorem B870493 : Blo 515797 870493 := bbase (se 3 (by rfl) ⟨163217, by rfl⟩ : syracuseStep 870493 = 326435) (by norm_num)
theorem B1656949 : Blo 515797 1656949 := bbase (se 5 (by rfl) ⟨77669, by rfl⟩ : syracuseStep 1656949 = 155339) (by norm_num)
theorem B1165445 : Blo 515797 1165445 := bbase (se 4 (by rfl) ⟨109260, by rfl⟩ : syracuseStep 1165445 = 218521) (by norm_num)
theorem B870581 : Blo 515797 870581 := bbase (se 5 (by rfl) ⟨40808, by rfl⟩ : syracuseStep 870581 = 81617) (by norm_num)
theorem B739525 : Blo 515797 739525 := bbase (se 4 (by rfl) ⟨69330, by rfl⟩ : syracuseStep 739525 = 138661) (by norm_num)
theorem B1165517 : Blo 515797 1165517 := bbase (se 3 (by rfl) ⟨218534, by rfl⟩ : syracuseStep 1165517 = 437069) (by norm_num)
theorem B1165589 : Blo 515797 1165589 := bbase (se 6 (by rfl) ⟨27318, by rfl⟩ : syracuseStep 1165589 = 54637) (by norm_num)
theorem B870709 : Blo 515797 870709 := bbase (se 5 (by rfl) ⟨40814, by rfl⟩ : syracuseStep 870709 = 81629) (by norm_num)
theorem B1165661 : Blo 515797 1165661 := bbase (se 3 (by rfl) ⟨218561, by rfl⟩ : syracuseStep 1165661 = 437123) (by norm_num)
theorem B1493365 : Blo 515797 1493365 := bbase (se 5 (by rfl) ⟨70001, by rfl⟩ : syracuseStep 1493365 = 140003) (by norm_num)
theorem B870797 : Blo 515797 870797 := bbase (se 3 (by rfl) ⟨163274, by rfl⟩ : syracuseStep 870797 = 326549) (by norm_num)
theorem B1165733 : Blo 515797 1165733 := bbase (se 4 (by rfl) ⟨109287, by rfl⟩ : syracuseStep 1165733 = 218575) (by norm_num)
theorem B936365 : Blo 515797 936365 := bbase (se 3 (by rfl) ⟨175568, by rfl⟩ : syracuseStep 936365 = 351137) (by norm_num)
theorem B838117 : Blo 515797 838117 := bbase (se 4 (by rfl) ⟨78573, by rfl⟩ : syracuseStep 838117 = 157147) (by norm_num)
theorem B1165805 : Blo 515797 1165805 := bbase (se 3 (by rfl) ⟨218588, by rfl⟩ : syracuseStep 1165805 = 437177) (by norm_num)
theorem B870925 : Blo 515797 870925 := bbase (se 3 (by rfl) ⟨163298, by rfl⟩ : syracuseStep 870925 = 326597) (by norm_num)
theorem B1657397 : Blo 515797 1657397 := bbase (se 5 (by rfl) ⟨77690, by rfl⟩ : syracuseStep 1657397 = 155381) (by norm_num)
theorem B1165877 : Blo 515797 1165877 := bbase (se 5 (by rfl) ⟨54650, by rfl⟩ : syracuseStep 1165877 = 109301) (by norm_num)
theorem B739901 : Blo 515797 739901 := bbase (se 3 (by rfl) ⟨138731, by rfl⟩ : syracuseStep 739901 = 277463) (by norm_num)
theorem B871013 : Blo 515797 871013 := bbase (se 4 (by rfl) ⟨81657, by rfl⟩ : syracuseStep 871013 = 163315) (by norm_num)
theorem B1165949 : Blo 515797 1165949 := bbase (se 3 (by rfl) ⟨218615, by rfl⟩ : syracuseStep 1165949 = 437231) (by norm_num)
theorem B3721909 : Blo 515797 3721909 := bbase (se 5 (by rfl) ⟨174464, by rfl⟩ : syracuseStep 3721909 = 348929) (by norm_num)
theorem B1166021 : Blo 515797 1166021 := bbase (se 4 (by rfl) ⟨109314, by rfl⟩ : syracuseStep 1166021 = 218629) (by norm_num)
theorem B871141 : Blo 515797 871141 := bbase (se 4 (by rfl) ⟨81669, by rfl⟩ : syracuseStep 871141 = 163339) (by norm_num)
theorem B1166093 : Blo 515797 1166093 := bbase (se 3 (by rfl) ⟨218642, by rfl⟩ : syracuseStep 1166093 = 437285) (by norm_num)
theorem B871229 : Blo 515797 871229 := bbase (se 3 (by rfl) ⟨163355, by rfl⟩ : syracuseStep 871229 = 326711) (by norm_num)
theorem B1166165 : Blo 515797 1166165 := bbase (se 9 (by rfl) ⟨3416, by rfl⟩ : syracuseStep 1166165 = 6833) (by norm_num)
theorem B1166237 : Blo 515797 1166237 := bbase (se 3 (by rfl) ⟨218669, by rfl⟩ : syracuseStep 1166237 = 437339) (by norm_num)
theorem B871357 : Blo 515797 871357 := bbase (se 3 (by rfl) ⟨163379, by rfl⟩ : syracuseStep 871357 = 326759) (by norm_num)
theorem B1166309 : Blo 515797 1166309 := bbase (se 4 (by rfl) ⟨109341, by rfl⟩ : syracuseStep 1166309 = 218683) (by norm_num)
theorem B871445 : Blo 515797 871445 := bbase (se 6 (by rfl) ⟨20424, by rfl⟩ : syracuseStep 871445 = 40849) (by norm_num)
theorem B4213781 : Blo 515797 4213781 := bbase (se 6 (by rfl) ⟨98760, by rfl⟩ : syracuseStep 4213781 = 197521) (by norm_num)
theorem B1166381 : Blo 515797 1166381 := bbase (se 3 (by rfl) ⟨218696, by rfl⟩ : syracuseStep 1166381 = 437393) (by norm_num)
theorem B1166453 : Blo 515797 1166453 := bbase (se 5 (by rfl) ⟨54677, by rfl⟩ : syracuseStep 1166453 = 109355) (by norm_num)
theorem B871573 : Blo 515797 871573 := bbase (se 6 (by rfl) ⟨20427, by rfl⟩ : syracuseStep 871573 = 40855) (by norm_num)
theorem B1166525 : Blo 515797 1166525 := bbase (se 3 (by rfl) ⟨218723, by rfl⟩ : syracuseStep 1166525 = 437447) (by norm_num)
theorem B871661 : Blo 515797 871661 := bbase (se 3 (by rfl) ⟨163436, by rfl⟩ : syracuseStep 871661 = 326873) (by norm_num)
theorem B1166597 : Blo 515797 1166597 := bbase (se 4 (by rfl) ⟨109368, by rfl⟩ : syracuseStep 1166597 = 218737) (by norm_num)
theorem B1166669 : Blo 515797 1166669 := bbase (se 3 (by rfl) ⟨218750, by rfl⟩ : syracuseStep 1166669 = 437501) (by norm_num)
theorem B871789 : Blo 515797 871789 := bbase (se 3 (by rfl) ⟨163460, by rfl⟩ : syracuseStep 871789 = 326921) (by norm_num)
theorem B1166741 : Blo 515797 1166741 := bbase (se 6 (by rfl) ⟨27345, by rfl⟩ : syracuseStep 1166741 = 54691) (by norm_num)
theorem B871877 : Blo 515797 871877 := bbase (se 4 (by rfl) ⟨81738, by rfl⟩ : syracuseStep 871877 = 163477) (by norm_num)
theorem B1166813 : Blo 515797 1166813 := bbase (se 3 (by rfl) ⟨218777, by rfl⟩ : syracuseStep 1166813 = 437555) (by norm_num)
theorem B1166885 : Blo 515797 1166885 := bbase (se 4 (by rfl) ⟨109395, by rfl⟩ : syracuseStep 1166885 = 218791) (by norm_num)
theorem B872005 : Blo 515797 872005 := bbase (se 4 (by rfl) ⟨81750, by rfl⟩ : syracuseStep 872005 = 163501) (by norm_num)
theorem B773717 : Blo 515797 773717 := bbase (se 8 (by rfl) ⟨4533, by rfl⟩ : syracuseStep 773717 = 9067) (by norm_num)
theorem B4705877 : Blo 515797 4705877 := bbase (se 8 (by rfl) ⟨27573, by rfl⟩ : syracuseStep 4705877 = 55147) (by norm_num)
theorem B773741 : Blo 515797 773741 := bbase (se 3 (by rfl) ⟨145076, by rfl⟩ : syracuseStep 773741 = 290153) (by norm_num)
theorem B1166957 : Blo 515797 1166957 := bbase (se 3 (by rfl) ⟨218804, by rfl⟩ : syracuseStep 1166957 = 437609) (by norm_num)
theorem B773765 : Blo 515797 773765 := bbase (se 4 (by rfl) ⟨72540, by rfl⟩ : syracuseStep 773765 = 145081) (by norm_num)
theorem B773789 : Blo 515797 773789 := bbase (se 3 (by rfl) ⟨145085, by rfl⟩ : syracuseStep 773789 = 290171) (by norm_num)
theorem B872093 : Blo 515797 872093 := bbase (se 3 (by rfl) ⟨163517, by rfl⟩ : syracuseStep 872093 = 327035) (by norm_num)
theorem B773813 : Blo 515797 773813 := bbase (se 5 (by rfl) ⟨36272, by rfl⟩ : syracuseStep 773813 = 72545) (by norm_num)
theorem B1167029 : Blo 515797 1167029 := bbase (se 5 (by rfl) ⟨54704, by rfl⟩ : syracuseStep 1167029 = 109409) (by norm_num)
theorem B773837 : Blo 515797 773837 := bbase (se 3 (by rfl) ⟨145094, by rfl⟩ : syracuseStep 773837 = 290189) (by norm_num)
theorem B2215637 : Blo 515797 2215637 := bbase (se 7 (by rfl) ⟨25964, by rfl⟩ : syracuseStep 2215637 = 51929) (by norm_num)
theorem B675541 : Blo 515797 675541 := bbase (se 7 (by rfl) ⟨7916, by rfl⟩ : syracuseStep 675541 = 15833) (by norm_num)
theorem B773861 : Blo 515797 773861 := bbase (se 4 (by rfl) ⟨72549, by rfl⟩ : syracuseStep 773861 = 145099) (by norm_num)
theorem B773885 : Blo 515797 773885 := bbase (se 3 (by rfl) ⟨145103, by rfl⟩ : syracuseStep 773885 = 290207) (by norm_num)
theorem B1167101 : Blo 515797 1167101 := bbase (se 3 (by rfl) ⟨218831, by rfl⟩ : syracuseStep 1167101 = 437663) (by norm_num)
theorem B773909 : Blo 515797 773909 := bbase (se 6 (by rfl) ⟨18138, by rfl⟩ : syracuseStep 773909 = 36277) (by norm_num)
theorem B872221 : Blo 515797 872221 := bbase (se 3 (by rfl) ⟨163541, by rfl⟩ : syracuseStep 872221 = 327083) (by norm_num)
theorem B773933 : Blo 515797 773933 := bbase (se 3 (by rfl) ⟨145112, by rfl⟩ : syracuseStep 773933 = 290225) (by norm_num)
theorem B773957 : Blo 515797 773957 := bbase (se 4 (by rfl) ⟨72558, by rfl⟩ : syracuseStep 773957 = 145117) (by norm_num)
theorem B1167173 : Blo 515797 1167173 := bbase (se 4 (by rfl) ⟨109422, by rfl⟩ : syracuseStep 1167173 = 218845) (by norm_num)
theorem B773981 : Blo 515797 773981 := bbase (se 3 (by rfl) ⟨145121, by rfl⟩ : syracuseStep 773981 = 290243) (by norm_num)
theorem B774005 : Blo 515797 774005 := bbase (se 5 (by rfl) ⟨36281, by rfl⟩ : syracuseStep 774005 = 72563) (by norm_num)
theorem B872309 : Blo 515797 872309 := bbase (se 5 (by rfl) ⟨40889, by rfl⟩ : syracuseStep 872309 = 81779) (by norm_num)
theorem B774029 : Blo 515797 774029 := bbase (se 3 (by rfl) ⟨145130, by rfl⟩ : syracuseStep 774029 = 290261) (by norm_num)
theorem B1167245 : Blo 515797 1167245 := bbase (se 3 (by rfl) ⟨218858, by rfl⟩ : syracuseStep 1167245 = 437717) (by norm_num)
theorem B774053 : Blo 515797 774053 := bbase (se 4 (by rfl) ⟨72567, by rfl⟩ : syracuseStep 774053 = 145135) (by norm_num)
theorem B774077 : Blo 515797 774077 := bbase (se 3 (by rfl) ⟨145139, by rfl⟩ : syracuseStep 774077 = 290279) (by norm_num)
theorem B839629 : Blo 515797 839629 := bbase (se 3 (by rfl) ⟨157430, by rfl⟩ : syracuseStep 839629 = 314861) (by norm_num)
theorem B774101 : Blo 515797 774101 := bbase (se 7 (by rfl) ⟨9071, by rfl⟩ : syracuseStep 774101 = 18143) (by norm_num)
theorem B1167317 : Blo 515797 1167317 := bbase (se 7 (by rfl) ⟨13679, by rfl⟩ : syracuseStep 1167317 = 27359) (by norm_num)
theorem B774125 : Blo 515797 774125 := bbase (se 3 (by rfl) ⟨145148, by rfl⟩ : syracuseStep 774125 = 290297) (by norm_num)
theorem B872437 : Blo 515797 872437 := bbase (se 5 (by rfl) ⟨40895, by rfl⟩ : syracuseStep 872437 = 81791) (by norm_num)
theorem B774149 : Blo 515797 774149 := bbase (se 4 (by rfl) ⟨72576, by rfl⟩ : syracuseStep 774149 = 145153) (by norm_num)
theorem B774173 : Blo 515797 774173 := bbase (se 3 (by rfl) ⟨145157, by rfl⟩ : syracuseStep 774173 = 290315) (by norm_num)
theorem B1167389 : Blo 515797 1167389 := bbase (se 3 (by rfl) ⟨218885, by rfl⟩ : syracuseStep 1167389 = 437771) (by norm_num)
theorem B774197 : Blo 515797 774197 := bbase (se 5 (by rfl) ⟨36290, by rfl⟩ : syracuseStep 774197 = 72581) (by norm_num)
theorem B3723317 : Blo 515797 3723317 := bbase (se 5 (by rfl) ⟨174530, by rfl⟩ : syracuseStep 3723317 = 349061) (by norm_num)
theorem B774221 : Blo 515797 774221 := bbase (se 3 (by rfl) ⟨145166, by rfl⟩ : syracuseStep 774221 = 290333) (by norm_num)
theorem B872525 : Blo 515797 872525 := bbase (se 3 (by rfl) ⟨163598, by rfl⟩ : syracuseStep 872525 = 327197) (by norm_num)
theorem B774245 : Blo 515797 774245 := bbase (se 4 (by rfl) ⟨72585, by rfl⟩ : syracuseStep 774245 = 145171) (by norm_num)
theorem B1167461 : Blo 515797 1167461 := bbase (se 4 (by rfl) ⟨109449, by rfl⟩ : syracuseStep 1167461 = 218899) (by norm_num)
theorem B1101941 : Blo 515797 1101941 := bbase (se 5 (by rfl) ⟨51653, by rfl⟩ : syracuseStep 1101941 = 103307) (by norm_num)
theorem B774269 : Blo 515797 774269 := bbase (se 3 (by rfl) ⟨145175, by rfl⟩ : syracuseStep 774269 = 290351) (by norm_num)
theorem B774293 : Blo 515797 774293 := bbase (se 6 (by rfl) ⟨18147, by rfl⟩ : syracuseStep 774293 = 36295) (by norm_num)
theorem B774317 : Blo 515797 774317 := bbase (se 3 (by rfl) ⟨145184, by rfl⟩ : syracuseStep 774317 = 290369) (by norm_num)
theorem B1167533 : Blo 515797 1167533 := bbase (se 3 (by rfl) ⟨218912, by rfl⟩ : syracuseStep 1167533 = 437825) (by norm_num)
theorem B774341 : Blo 515797 774341 := bbase (se 4 (by rfl) ⟨72594, by rfl⟩ : syracuseStep 774341 = 145189) (by norm_num)
theorem B872653 : Blo 515797 872653 := bbase (se 3 (by rfl) ⟨163622, by rfl⟩ : syracuseStep 872653 = 327245) (by norm_num)
theorem B774365 : Blo 515797 774365 := bbase (se 3 (by rfl) ⟨145193, by rfl⟩ : syracuseStep 774365 = 290387) (by norm_num)
theorem B1102061 : Blo 515797 1102061 := bbase (se 3 (by rfl) ⟨206636, by rfl⟩ : syracuseStep 1102061 = 413273) (by norm_num)
theorem B774389 : Blo 515797 774389 := bbase (se 5 (by rfl) ⟨36299, by rfl⟩ : syracuseStep 774389 = 72599) (by norm_num)
theorem B1167605 : Blo 515797 1167605 := bbase (se 5 (by rfl) ⟨54731, by rfl⟩ : syracuseStep 1167605 = 109463) (by norm_num)
theorem B774413 : Blo 515797 774413 := bbase (se 3 (by rfl) ⟨145202, by rfl⟩ : syracuseStep 774413 = 290405) (by norm_num)
theorem B774437 : Blo 515797 774437 := bbase (se 4 (by rfl) ⟨72603, by rfl⟩ : syracuseStep 774437 = 145207) (by norm_num)
theorem B872741 : Blo 515797 872741 := bbase (se 4 (by rfl) ⟨81819, by rfl⟩ : syracuseStep 872741 = 163639) (by norm_num)
theorem B1397045 : Blo 515797 1397045 := bbase (se 5 (by rfl) ⟨65486, by rfl⟩ : syracuseStep 1397045 = 130973) (by norm_num)
theorem B774461 : Blo 515797 774461 := bbase (se 3 (by rfl) ⟨145211, by rfl⟩ : syracuseStep 774461 = 290423) (by norm_num)
theorem B1167677 : Blo 515797 1167677 := bbase (se 3 (by rfl) ⟨218939, by rfl⟩ : syracuseStep 1167677 = 437879) (by norm_num)
theorem B774485 : Blo 515797 774485 := bbase (se 10 (by rfl) ⟨1134, by rfl⟩ : syracuseStep 774485 = 2269) (by norm_num)
theorem B774509 : Blo 515797 774509 := bbase (se 3 (by rfl) ⟨145220, by rfl⟩ : syracuseStep 774509 = 290441) (by norm_num)
theorem B774533 : Blo 515797 774533 := bbase (se 4 (by rfl) ⟨72612, by rfl⟩ : syracuseStep 774533 = 145225) (by norm_num)
theorem B1167749 : Blo 515797 1167749 := bbase (se 4 (by rfl) ⟨109476, by rfl⟩ : syracuseStep 1167749 = 218953) (by norm_num)
theorem B774557 : Blo 515797 774557 := bbase (se 3 (by rfl) ⟨145229, by rfl⟩ : syracuseStep 774557 = 290459) (by norm_num)
theorem B872869 : Blo 515797 872869 := bbase (se 4 (by rfl) ⟨81831, by rfl⟩ : syracuseStep 872869 = 163663) (by norm_num)
theorem B774581 : Blo 515797 774581 := bbase (se 5 (by rfl) ⟨36308, by rfl⟩ : syracuseStep 774581 = 72617) (by norm_num)
theorem B774605 : Blo 515797 774605 := bbase (se 3 (by rfl) ⟨145238, by rfl⟩ : syracuseStep 774605 = 290477) (by norm_num)
theorem B1167821 : Blo 515797 1167821 := bbase (se 3 (by rfl) ⟨218966, by rfl⟩ : syracuseStep 1167821 = 437933) (by norm_num)
theorem B774629 : Blo 515797 774629 := bbase (se 4 (by rfl) ⟨72621, by rfl⟩ : syracuseStep 774629 = 145243) (by norm_num)
theorem B774653 : Blo 515797 774653 := bbase (se 3 (by rfl) ⟨145247, by rfl⟩ : syracuseStep 774653 = 290495) (by norm_num)
theorem B872957 : Blo 515797 872957 := bbase (se 3 (by rfl) ⟨163679, by rfl⟩ : syracuseStep 872957 = 327359) (by norm_num)
theorem B774677 : Blo 515797 774677 := bbase (se 6 (by rfl) ⟨18156, by rfl⟩ : syracuseStep 774677 = 36313) (by norm_num)
theorem B1167893 : Blo 515797 1167893 := bbase (se 6 (by rfl) ⟨27372, by rfl⟩ : syracuseStep 1167893 = 54745) (by norm_num)
theorem B774701 : Blo 515797 774701 := bbase (se 3 (by rfl) ⟨145256, by rfl⟩ : syracuseStep 774701 = 290513) (by norm_num)
theorem B774725 : Blo 515797 774725 := bbase (se 4 (by rfl) ⟨72630, by rfl⟩ : syracuseStep 774725 = 145261) (by norm_num)
theorem B3986005 : Blo 515797 3986005 := bbase (se 8 (by rfl) ⟨23355, by rfl⟩ : syracuseStep 3986005 = 46711) (by norm_num)
theorem B774749 : Blo 515797 774749 := bbase (se 3 (by rfl) ⟨145265, by rfl⟩ : syracuseStep 774749 = 290531) (by norm_num)
theorem B1167965 : Blo 515797 1167965 := bbase (se 3 (by rfl) ⟨218993, by rfl⟩ : syracuseStep 1167965 = 437987) (by norm_num)
theorem B774773 : Blo 515797 774773 := bbase (se 5 (by rfl) ⟨36317, by rfl⟩ : syracuseStep 774773 = 72635) (by norm_num)
theorem B873085 : Blo 515797 873085 := bbase (se 3 (by rfl) ⟨163703, by rfl⟩ : syracuseStep 873085 = 327407) (by norm_num)
theorem B774797 : Blo 515797 774797 := bbase (se 3 (by rfl) ⟨145274, by rfl⟩ : syracuseStep 774797 = 290549) (by norm_num)
theorem B774821 : Blo 515797 774821 := bbase (se 4 (by rfl) ⟨72639, by rfl⟩ : syracuseStep 774821 = 145279) (by norm_num)
theorem B1168037 : Blo 515797 1168037 := bbase (se 4 (by rfl) ⟨109503, by rfl⟩ : syracuseStep 1168037 = 219007) (by norm_num)
theorem B774845 : Blo 515797 774845 := bbase (se 3 (by rfl) ⟨145283, by rfl⟩ : syracuseStep 774845 = 290567) (by norm_num)
theorem B774869 : Blo 515797 774869 := bbase (se 7 (by rfl) ⟨9080, by rfl⟩ : syracuseStep 774869 = 18161) (by norm_num)
theorem B873173 : Blo 515797 873173 := bbase (se 7 (by rfl) ⟨10232, by rfl⟩ : syracuseStep 873173 = 20465) (by norm_num)
theorem B774893 : Blo 515797 774893 := bbase (se 3 (by rfl) ⟨145292, by rfl⟩ : syracuseStep 774893 = 290585) (by norm_num)
theorem B1168109 : Blo 515797 1168109 := bbase (se 3 (by rfl) ⟨219020, by rfl⟩ : syracuseStep 1168109 = 438041) (by norm_num)
theorem B774917 : Blo 515797 774917 := bbase (se 4 (by rfl) ⟨72648, by rfl⟩ : syracuseStep 774917 = 145297) (by norm_num)
theorem B1659653 : Blo 515797 1659653 := bbase (se 4 (by rfl) ⟨155592, by rfl⟩ : syracuseStep 1659653 = 311185) (by norm_num)
theorem B774941 : Blo 515797 774941 := bbase (se 3 (by rfl) ⟨145301, by rfl⟩ : syracuseStep 774941 = 290603) (by norm_num)
theorem B774965 : Blo 515797 774965 := bbase (se 5 (by rfl) ⟨36326, by rfl⟩ : syracuseStep 774965 = 72653) (by norm_num)
theorem B1168181 : Blo 515797 1168181 := bbase (se 5 (by rfl) ⟨54758, by rfl⟩ : syracuseStep 1168181 = 109517) (by norm_num)
theorem B774989 : Blo 515797 774989 := bbase (se 3 (by rfl) ⟨145310, by rfl⟩ : syracuseStep 774989 = 290621) (by norm_num)
theorem B873301 : Blo 515797 873301 := bbase (se 9 (by rfl) ⟨2558, by rfl⟩ : syracuseStep 873301 = 5117) (by norm_num)
theorem B1102693 : Blo 515797 1102693 := bbase (se 4 (by rfl) ⟨103377, by rfl⟩ : syracuseStep 1102693 = 206755) (by norm_num)
theorem B775013 : Blo 515797 775013 := bbase (se 4 (by rfl) ⟨72657, by rfl⟩ : syracuseStep 775013 = 145315) (by norm_num)
theorem B775037 : Blo 515797 775037 := bbase (se 3 (by rfl) ⟨145319, by rfl⟩ : syracuseStep 775037 = 290639) (by norm_num)
theorem B1168253 : Blo 515797 1168253 := bbase (se 3 (by rfl) ⟨219047, by rfl⟩ : syracuseStep 1168253 = 438095) (by norm_num)
theorem B775061 : Blo 515797 775061 := bbase (se 6 (by rfl) ⟨18165, by rfl⟩ : syracuseStep 775061 = 36331) (by norm_num)
theorem B775085 : Blo 515797 775085 := bbase (se 3 (by rfl) ⟨145328, by rfl⟩ : syracuseStep 775085 = 290657) (by norm_num)
theorem B873389 : Blo 515797 873389 := bbase (se 3 (by rfl) ⟨163760, by rfl⟩ : syracuseStep 873389 = 327521) (by norm_num)
theorem B775109 : Blo 515797 775109 := bbase (se 4 (by rfl) ⟨72666, by rfl⟩ : syracuseStep 775109 = 145333) (by norm_num)
theorem B1168325 : Blo 515797 1168325 := bbase (se 4 (by rfl) ⟨109530, by rfl⟩ : syracuseStep 1168325 = 219061) (by norm_num)
theorem B775133 : Blo 515797 775133 := bbase (se 3 (by rfl) ⟨145337, by rfl⟩ : syracuseStep 775133 = 290675) (by norm_num)
theorem B775157 : Blo 515797 775157 := bbase (se 5 (by rfl) ⟨36335, by rfl⟩ : syracuseStep 775157 = 72671) (by norm_num)
theorem B775181 : Blo 515797 775181 := bbase (se 3 (by rfl) ⟨145346, by rfl⟩ : syracuseStep 775181 = 290693) (by norm_num)
theorem B1168397 : Blo 515797 1168397 := bbase (se 3 (by rfl) ⟨219074, by rfl⟩ : syracuseStep 1168397 = 438149) (by norm_num)
theorem B775205 : Blo 515797 775205 := bbase (se 4 (by rfl) ⟨72675, by rfl⟩ : syracuseStep 775205 = 145351) (by norm_num)
theorem B873517 : Blo 515797 873517 := bbase (se 3 (by rfl) ⟨163784, by rfl⟩ : syracuseStep 873517 = 327569) (by norm_num)
theorem B775229 : Blo 515797 775229 := bbase (se 3 (by rfl) ⟨145355, by rfl⟩ : syracuseStep 775229 = 290711) (by norm_num)
theorem B775253 : Blo 515797 775253 := bbase (se 8 (by rfl) ⟨4542, by rfl⟩ : syracuseStep 775253 = 9085) (by norm_num)
theorem B1168469 : Blo 515797 1168469 := bbase (se 8 (by rfl) ⟨6846, by rfl⟩ : syracuseStep 1168469 = 13693) (by norm_num)
theorem B775277 : Blo 515797 775277 := bbase (se 3 (by rfl) ⟨145364, by rfl⟩ : syracuseStep 775277 = 290729) (by norm_num)
theorem B775301 : Blo 515797 775301 := bbase (se 4 (by rfl) ⟨72684, by rfl⟩ : syracuseStep 775301 = 145369) (by norm_num)
theorem B873605 : Blo 515797 873605 := bbase (se 4 (by rfl) ⟨81900, by rfl⟩ : syracuseStep 873605 = 163801) (by norm_num)
theorem B775325 : Blo 515797 775325 := bbase (se 3 (by rfl) ⟨145373, by rfl⟩ : syracuseStep 775325 = 290747) (by norm_num)
theorem B1168541 : Blo 515797 1168541 := bbase (se 3 (by rfl) ⟨219101, by rfl⟩ : syracuseStep 1168541 = 438203) (by norm_num)
theorem B775349 : Blo 515797 775349 := bbase (se 5 (by rfl) ⟨36344, by rfl⟩ : syracuseStep 775349 = 72689) (by norm_num)
theorem B775373 : Blo 515797 775373 := bbase (se 3 (by rfl) ⟨145382, by rfl⟩ : syracuseStep 775373 = 290765) (by norm_num)
theorem B4183253 : Blo 515797 4183253 := bbase (se 7 (by rfl) ⟨49022, by rfl⟩ : syracuseStep 4183253 = 98045) (by norm_num)
theorem B775397 : Blo 515797 775397 := bbase (se 4 (by rfl) ⟨72693, by rfl⟩ : syracuseStep 775397 = 145387) (by norm_num)
theorem B1168613 : Blo 515797 1168613 := bbase (se 4 (by rfl) ⟨109557, by rfl⟩ : syracuseStep 1168613 = 219115) (by norm_num)
theorem B775421 : Blo 515797 775421 := bbase (se 3 (by rfl) ⟨145391, by rfl⟩ : syracuseStep 775421 = 290783) (by norm_num)
theorem B873733 : Blo 515797 873733 := bbase (se 4 (by rfl) ⟨81912, by rfl⟩ : syracuseStep 873733 = 163825) (by norm_num)
theorem B775445 : Blo 515797 775445 := bbase (se 6 (by rfl) ⟨18174, by rfl⟩ : syracuseStep 775445 = 36349) (by norm_num)
theorem B775469 : Blo 515797 775469 := bbase (se 3 (by rfl) ⟨145400, by rfl⟩ : syracuseStep 775469 = 290801) (by norm_num)
theorem B1168685 : Blo 515797 1168685 := bbase (se 3 (by rfl) ⟨219128, by rfl⟩ : syracuseStep 1168685 = 438257) (by norm_num)
theorem B775493 : Blo 515797 775493 := bbase (se 4 (by rfl) ⟨72702, by rfl⟩ : syracuseStep 775493 = 145405) (by norm_num)
theorem B775517 : Blo 515797 775517 := bbase (se 3 (by rfl) ⟨145409, by rfl⟩ : syracuseStep 775517 = 290819) (by norm_num)
theorem B873821 : Blo 515797 873821 := bbase (se 3 (by rfl) ⟨163841, by rfl⟩ : syracuseStep 873821 = 327683) (by norm_num)
theorem B775541 : Blo 515797 775541 := bbase (se 5 (by rfl) ⟨36353, by rfl⟩ : syracuseStep 775541 = 72707) (by norm_num)
theorem B1168757 : Blo 515797 1168757 := bbase (se 5 (by rfl) ⟨54785, by rfl⟩ : syracuseStep 1168757 = 109571) (by norm_num)
theorem B775565 : Blo 515797 775565 := bbase (se 3 (by rfl) ⟨145418, by rfl⟩ : syracuseStep 775565 = 290837) (by norm_num)
theorem B775589 : Blo 515797 775589 := bbase (se 4 (by rfl) ⟨72711, by rfl⟩ : syracuseStep 775589 = 145423) (by norm_num)
theorem B775613 : Blo 515797 775613 := bbase (se 3 (by rfl) ⟨145427, by rfl⟩ : syracuseStep 775613 = 290855) (by norm_num)
theorem B1168829 : Blo 515797 1168829 := bbase (se 3 (by rfl) ⟨219155, by rfl⟩ : syracuseStep 1168829 = 438311) (by norm_num)
theorem B775637 : Blo 515797 775637 := bbase (se 7 (by rfl) ⟨9089, by rfl⟩ : syracuseStep 775637 = 18179) (by norm_num)
theorem B873949 : Blo 515797 873949 := bbase (se 3 (by rfl) ⟨163865, by rfl⟩ : syracuseStep 873949 = 327731) (by norm_num)
theorem B775661 : Blo 515797 775661 := bbase (se 3 (by rfl) ⟨145436, by rfl⟩ : syracuseStep 775661 = 290873) (by norm_num)
theorem B1332733 : Blo 515797 1332733 := bbase (se 3 (by rfl) ⟨249887, by rfl⟩ : syracuseStep 1332733 = 499775) (by norm_num)
theorem B775685 : Blo 515797 775685 := bbase (se 4 (by rfl) ⟨72720, by rfl⟩ : syracuseStep 775685 = 145441) (by norm_num)
theorem B1168901 : Blo 515797 1168901 := bbase (se 4 (by rfl) ⟨109584, by rfl⟩ : syracuseStep 1168901 = 219169) (by norm_num)
theorem B775709 : Blo 515797 775709 := bbase (se 3 (by rfl) ⟨145445, by rfl⟩ : syracuseStep 775709 = 290891) (by norm_num)
theorem B775733 : Blo 515797 775733 := bbase (se 5 (by rfl) ⟨36362, by rfl⟩ : syracuseStep 775733 = 72725) (by norm_num)
theorem B874037 : Blo 515797 874037 := bbase (se 5 (by rfl) ⟨40970, by rfl⟩ : syracuseStep 874037 = 81941) (by norm_num)
theorem B775757 : Blo 515797 775757 := bbase (se 3 (by rfl) ⟨145454, by rfl⟩ : syracuseStep 775757 = 290909) (by norm_num)
theorem B1168973 : Blo 515797 1168973 := bbase (se 3 (by rfl) ⟨219182, by rfl⟩ : syracuseStep 1168973 = 438365) (by norm_num)
theorem B775781 : Blo 515797 775781 := bbase (se 4 (by rfl) ⟨72729, by rfl⟩ : syracuseStep 775781 = 145459) (by norm_num)
theorem B775805 : Blo 515797 775805 := bbase (se 3 (by rfl) ⟨145463, by rfl⟩ : syracuseStep 775805 = 290927) (by norm_num)
theorem B775829 : Blo 515797 775829 := bbase (se 6 (by rfl) ⟨18183, by rfl⟩ : syracuseStep 775829 = 36367) (by norm_num)
theorem B1169045 : Blo 515797 1169045 := bbase (se 6 (by rfl) ⟨27399, by rfl⟩ : syracuseStep 1169045 = 54799) (by norm_num)
theorem B775853 : Blo 515797 775853 := bbase (se 3 (by rfl) ⟨145472, by rfl⟩ : syracuseStep 775853 = 290945) (by norm_num)
theorem B874165 : Blo 515797 874165 := bbase (se 5 (by rfl) ⟨40976, by rfl⟩ : syracuseStep 874165 = 81953) (by norm_num)
theorem B775877 : Blo 515797 775877 := bbase (se 4 (by rfl) ⟨72738, by rfl⟩ : syracuseStep 775877 = 145477) (by norm_num)
theorem B1398485 : Blo 515797 1398485 := bbase (se 7 (by rfl) ⟨16388, by rfl⟩ : syracuseStep 1398485 = 32777) (by norm_num)
theorem B1103581 : Blo 515797 1103581 := bbase (se 3 (by rfl) ⟨206921, by rfl⟩ : syracuseStep 1103581 = 413843) (by norm_num)
theorem B775901 : Blo 515797 775901 := bbase (se 3 (by rfl) ⟨145481, by rfl⟩ : syracuseStep 775901 = 290963) (by norm_num)
theorem B1169117 : Blo 515797 1169117 := bbase (se 3 (by rfl) ⟨219209, by rfl⟩ : syracuseStep 1169117 = 438419) (by norm_num)
theorem B775925 : Blo 515797 775925 := bbase (se 5 (by rfl) ⟨36371, by rfl⟩ : syracuseStep 775925 = 72743) (by norm_num)
theorem B775949 : Blo 515797 775949 := bbase (se 3 (by rfl) ⟨145490, by rfl⟩ : syracuseStep 775949 = 290981) (by norm_num)
theorem B874253 : Blo 515797 874253 := bbase (se 3 (by rfl) ⟨163922, by rfl⟩ : syracuseStep 874253 = 327845) (by norm_num)
theorem B775973 : Blo 515797 775973 := bbase (se 4 (by rfl) ⟨72747, by rfl⟩ : syracuseStep 775973 = 145495) (by norm_num)
theorem B1169189 : Blo 515797 1169189 := bbase (se 4 (by rfl) ⟨109611, by rfl⟩ : syracuseStep 1169189 = 219223) (by norm_num)
theorem B775997 : Blo 515797 775997 := bbase (se 3 (by rfl) ⟨145499, by rfl⟩ : syracuseStep 775997 = 290999) (by norm_num)
theorem B1103701 : Blo 515797 1103701 := bbase (se 9 (by rfl) ⟨3233, by rfl⟩ : syracuseStep 1103701 = 6467) (by norm_num)
theorem B776021 : Blo 515797 776021 := bbase (se 9 (by rfl) ⟨2273, by rfl⟩ : syracuseStep 776021 = 4547) (by norm_num)
theorem B11196245 : Blo 515797 11196245 := bbase (se 9 (by rfl) ⟨32801, by rfl⟩ : syracuseStep 11196245 = 65603) (by norm_num)
theorem B776045 : Blo 515797 776045 := bbase (se 3 (by rfl) ⟨145508, by rfl⟩ : syracuseStep 776045 = 291017) (by norm_num)
theorem B1169261 : Blo 515797 1169261 := bbase (se 3 (by rfl) ⟨219236, by rfl⟩ : syracuseStep 1169261 = 438473) (by norm_num)
theorem B776069 : Blo 515797 776069 := bbase (se 4 (by rfl) ⟨72756, by rfl⟩ : syracuseStep 776069 = 145513) (by norm_num)
theorem B874381 : Blo 515797 874381 := bbase (se 3 (by rfl) ⟨163946, by rfl⟩ : syracuseStep 874381 = 327893) (by norm_num)
theorem B776093 : Blo 515797 776093 := bbase (se 3 (by rfl) ⟨145517, by rfl⟩ : syracuseStep 776093 = 291035) (by norm_num)
theorem B776117 : Blo 515797 776117 := bbase (se 5 (by rfl) ⟨36380, by rfl⟩ : syracuseStep 776117 = 72761) (by norm_num)
theorem B1169333 : Blo 515797 1169333 := bbase (se 5 (by rfl) ⟨54812, by rfl⟩ : syracuseStep 1169333 = 109625) (by norm_num)
theorem B776141 : Blo 515797 776141 := bbase (se 3 (by rfl) ⟨145526, by rfl⟩ : syracuseStep 776141 = 291053) (by norm_num)
theorem B776165 : Blo 515797 776165 := bbase (se 4 (by rfl) ⟨72765, by rfl⟩ : syracuseStep 776165 = 145531) (by norm_num)
theorem B874469 : Blo 515797 874469 := bbase (se 4 (by rfl) ⟨81981, by rfl⟩ : syracuseStep 874469 = 163963) (by norm_num)
theorem B776189 : Blo 515797 776189 := bbase (se 3 (by rfl) ⟨145535, by rfl⟩ : syracuseStep 776189 = 291071) (by norm_num)
theorem B1169405 : Blo 515797 1169405 := bbase (se 3 (by rfl) ⟨219263, by rfl⟩ : syracuseStep 1169405 = 438527) (by norm_num)
theorem B776213 : Blo 515797 776213 := bbase (se 6 (by rfl) ⟨18192, by rfl⟩ : syracuseStep 776213 = 36385) (by norm_num)
theorem B776237 : Blo 515797 776237 := bbase (se 3 (by rfl) ⟨145544, by rfl⟩ : syracuseStep 776237 = 291089) (by norm_num)
theorem B776261 : Blo 515797 776261 := bbase (se 4 (by rfl) ⟨72774, by rfl⟩ : syracuseStep 776261 = 145549) (by norm_num)
theorem B1169477 : Blo 515797 1169477 := bbase (se 4 (by rfl) ⟨109638, by rfl⟩ : syracuseStep 1169477 = 219277) (by norm_num)
theorem B2480213 : Blo 515797 2480213 := bbase (se 8 (by rfl) ⟨14532, by rfl⟩ : syracuseStep 2480213 = 29065) (by norm_num)
theorem B1103957 : Blo 515797 1103957 := bbase (se 8 (by rfl) ⟨6468, by rfl⟩ : syracuseStep 1103957 = 12937) (by norm_num)
theorem B776285 : Blo 515797 776285 := bbase (se 3 (by rfl) ⟨145553, by rfl⟩ : syracuseStep 776285 = 291107) (by norm_num)
theorem B874597 : Blo 515797 874597 := bbase (se 4 (by rfl) ⟨81993, by rfl⟩ : syracuseStep 874597 = 163987) (by norm_num)
theorem B776309 : Blo 515797 776309 := bbase (se 5 (by rfl) ⟨36389, by rfl⟩ : syracuseStep 776309 = 72779) (by norm_num)
theorem B776333 : Blo 515797 776333 := bbase (se 3 (by rfl) ⟨145562, by rfl⟩ : syracuseStep 776333 = 291125) (by norm_num)
theorem B776357 : Blo 515797 776357 := bbase (se 4 (by rfl) ⟨72783, by rfl⟩ : syracuseStep 776357 = 145567) (by norm_num)
theorem B1890485 : Blo 515797 1890485 := bbase (se 5 (by rfl) ⟨88616, by rfl⟩ : syracuseStep 1890485 = 177233) (by norm_num)
theorem B776381 : Blo 515797 776381 := bbase (se 3 (by rfl) ⟨145571, by rfl⟩ : syracuseStep 776381 = 291143) (by norm_num)
theorem B874685 : Blo 515797 874685 := bbase (se 3 (by rfl) ⟨164003, by rfl⟩ : syracuseStep 874685 = 328007) (by norm_num)
theorem B776405 : Blo 515797 776405 := bbase (se 7 (by rfl) ⟨9098, by rfl⟩ : syracuseStep 776405 = 18197) (by norm_num)
theorem B776429 : Blo 515797 776429 := bbase (se 3 (by rfl) ⟨145580, by rfl⟩ : syracuseStep 776429 = 291161) (by norm_num)
theorem B776453 : Blo 515797 776453 := bbase (se 4 (by rfl) ⟨72792, by rfl⟩ : syracuseStep 776453 = 145585) (by norm_num)
theorem B776477 : Blo 515797 776477 := bbase (se 3 (by rfl) ⟨145589, by rfl⟩ : syracuseStep 776477 = 291179) (by norm_num)
theorem B776501 : Blo 515797 776501 := bbase (se 5 (by rfl) ⟨36398, by rfl⟩ : syracuseStep 776501 = 72797) (by norm_num)
theorem B874813 : Blo 515797 874813 := bbase (se 3 (by rfl) ⟨164027, by rfl⟩ : syracuseStep 874813 = 328055) (by norm_num)
theorem B776525 : Blo 515797 776525 := bbase (se 3 (by rfl) ⟨145598, by rfl⟩ : syracuseStep 776525 = 291197) (by norm_num)
theorem B776549 : Blo 515797 776549 := bbase (se 4 (by rfl) ⟨72801, by rfl⟩ : syracuseStep 776549 = 145603) (by norm_num)
theorem B776573 : Blo 515797 776573 := bbase (se 3 (by rfl) ⟨145607, by rfl⟩ : syracuseStep 776573 = 291215) (by norm_num)
theorem B776597 : Blo 515797 776597 := bbase (se 6 (by rfl) ⟨18201, by rfl⟩ : syracuseStep 776597 = 36403) (by norm_num)
theorem B874901 : Blo 515797 874901 := bbase (se 6 (by rfl) ⟨20505, by rfl⟩ : syracuseStep 874901 = 41011) (by norm_num)
theorem B776621 : Blo 515797 776621 := bbase (se 3 (by rfl) ⟨145616, by rfl⟩ : syracuseStep 776621 = 291233) (by norm_num)
theorem B776645 : Blo 515797 776645 := bbase (se 4 (by rfl) ⟨72810, by rfl⟩ : syracuseStep 776645 = 145621) (by norm_num)
theorem B776669 : Blo 515797 776669 := bbase (se 3 (by rfl) ⟨145625, by rfl⟩ : syracuseStep 776669 = 291251) (by norm_num)
theorem B776693 : Blo 515797 776693 := bbase (se 5 (by rfl) ⟨36407, by rfl⟩ : syracuseStep 776693 = 72815) (by norm_num)
theorem B776717 : Blo 515797 776717 := bbase (se 3 (by rfl) ⟨145634, by rfl⟩ : syracuseStep 776717 = 291269) (by norm_num)
theorem B875029 : Blo 515797 875029 := bbase (se 6 (by rfl) ⟨20508, by rfl⟩ : syracuseStep 875029 = 41017) (by norm_num)
theorem B776741 : Blo 515797 776741 := bbase (se 4 (by rfl) ⟨72819, by rfl⟩ : syracuseStep 776741 = 145639) (by norm_num)
theorem B776765 : Blo 515797 776765 := bbase (se 3 (by rfl) ⟨145643, by rfl⟩ : syracuseStep 776765 = 291287) (by norm_num)
theorem B776789 : Blo 515797 776789 := bbase (se 8 (by rfl) ⟨4551, by rfl⟩ : syracuseStep 776789 = 9103) (by norm_num)
theorem B776813 : Blo 515797 776813 := bbase (se 3 (by rfl) ⟨145652, by rfl⟩ : syracuseStep 776813 = 291305) (by norm_num)
theorem B875117 : Blo 515797 875117 := bbase (se 3 (by rfl) ⟨164084, by rfl⟩ : syracuseStep 875117 = 328169) (by norm_num)
theorem B776837 : Blo 515797 776837 := bbase (se 4 (by rfl) ⟨72828, by rfl⟩ : syracuseStep 776837 = 145657) (by norm_num)
theorem B776861 : Blo 515797 776861 := bbase (se 3 (by rfl) ⟨145661, by rfl⟩ : syracuseStep 776861 = 291323) (by norm_num)
theorem B776885 : Blo 515797 776885 := bbase (se 5 (by rfl) ⟨36416, by rfl⟩ : syracuseStep 776885 = 72833) (by norm_num)
theorem B580297 : Blo 515797 580297 := bbase (se 2 (by rfl) ⟨217611, by rfl⟩ : syracuseStep 580297 = 435223) (by norm_num)
theorem B776909 : Blo 515797 776909 := bbase (se 3 (by rfl) ⟨145670, by rfl⟩ : syracuseStep 776909 = 291341) (by norm_num)
theorem B2611925 : Blo 515797 2611925 := bbase (se 7 (by rfl) ⟨30608, by rfl⟩ : syracuseStep 2611925 = 61217) (by norm_num)
theorem B776933 : Blo 515797 776933 := bbase (se 4 (by rfl) ⟨72837, by rfl⟩ : syracuseStep 776933 = 145675) (by norm_num)
theorem B580333 : Blo 515797 580333 := bbase (se 3 (by rfl) ⟨108812, by rfl⟩ : syracuseStep 580333 = 217625) (by norm_num)
theorem B875245 : Blo 515797 875245 := bbase (se 3 (by rfl) ⟨164108, by rfl⟩ : syracuseStep 875245 = 328217) (by norm_num)
theorem B776957 : Blo 515797 776957 := bbase (se 3 (by rfl) ⟨145679, by rfl⟩ : syracuseStep 776957 = 291359) (by norm_num)
theorem B580369 : Blo 515797 580369 := bbase (se 2 (by rfl) ⟨217638, by rfl⟩ : syracuseStep 580369 = 435277) (by norm_num)
theorem B776981 : Blo 515797 776981 := bbase (se 6 (by rfl) ⟨18210, by rfl⟩ : syracuseStep 776981 = 36421) (by norm_num)
theorem B777005 : Blo 515797 777005 := bbase (se 3 (by rfl) ⟨145688, by rfl⟩ : syracuseStep 777005 = 291377) (by norm_num)
theorem B580405 : Blo 515797 580405 := bbase (se 5 (by rfl) ⟨27206, by rfl⟩ : syracuseStep 580405 = 54413) (by norm_num)
theorem B777029 : Blo 515797 777029 := bbase (se 4 (by rfl) ⟨72846, by rfl⟩ : syracuseStep 777029 = 145693) (by norm_num)
theorem B875333 : Blo 515797 875333 := bbase (se 4 (by rfl) ⟨82062, by rfl⟩ : syracuseStep 875333 = 164125) (by norm_num)
theorem B580441 : Blo 515797 580441 := bbase (se 2 (by rfl) ⟨217665, by rfl⟩ : syracuseStep 580441 = 435331) (by norm_num)
theorem B777053 : Blo 515797 777053 := bbase (se 3 (by rfl) ⟨145697, by rfl⟩ : syracuseStep 777053 = 291395) (by norm_num)
theorem B777077 : Blo 515797 777077 := bbase (se 5 (by rfl) ⟨36425, by rfl⟩ : syracuseStep 777077 = 72851) (by norm_num)
theorem B580477 : Blo 515797 580477 := bbase (se 3 (by rfl) ⟨108839, by rfl⟩ : syracuseStep 580477 = 217679) (by norm_num)
theorem B777101 : Blo 515797 777101 := bbase (se 3 (by rfl) ⟨145706, by rfl⟩ : syracuseStep 777101 = 291413) (by norm_num)
theorem B580513 : Blo 515797 580513 := bbase (se 2 (by rfl) ⟨217692, by rfl⟩ : syracuseStep 580513 = 435385) (by norm_num)
theorem B777125 : Blo 515797 777125 := bbase (se 4 (by rfl) ⟨72855, by rfl⟩ : syracuseStep 777125 = 145711) (by norm_num)
theorem B777149 : Blo 515797 777149 := bbase (se 3 (by rfl) ⟨145715, by rfl⟩ : syracuseStep 777149 = 291431) (by norm_num)
theorem B580549 : Blo 515797 580549 := bbase (se 4 (by rfl) ⟨54426, by rfl⟩ : syracuseStep 580549 = 108853) (by norm_num)
theorem B875461 : Blo 515797 875461 := bbase (se 4 (by rfl) ⟨82074, by rfl⟩ : syracuseStep 875461 = 164149) (by norm_num)
theorem B1104845 : Blo 515797 1104845 := bbase (se 3 (by rfl) ⟨207158, by rfl⟩ : syracuseStep 1104845 = 414317) (by norm_num)
theorem B777173 : Blo 515797 777173 := bbase (se 7 (by rfl) ⟨9107, by rfl⟩ : syracuseStep 777173 = 18215) (by norm_num)
theorem B580585 : Blo 515797 580585 := bbase (se 2 (by rfl) ⟨217719, by rfl⟩ : syracuseStep 580585 = 435439) (by norm_num)
theorem B777197 : Blo 515797 777197 := bbase (se 3 (by rfl) ⟨145724, by rfl⟩ : syracuseStep 777197 = 291449) (by norm_num)
theorem B777221 : Blo 515797 777221 := bbase (se 4 (by rfl) ⟨72864, by rfl⟩ : syracuseStep 777221 = 145729) (by norm_num)
theorem B580621 : Blo 515797 580621 := bbase (se 3 (by rfl) ⟨108866, by rfl⟩ : syracuseStep 580621 = 217733) (by norm_num)
theorem B777245 : Blo 515797 777245 := bbase (se 3 (by rfl) ⟨145733, by rfl⟩ : syracuseStep 777245 = 291467) (by norm_num)
theorem B875549 : Blo 515797 875549 := bbase (se 3 (by rfl) ⟨164165, by rfl⟩ : syracuseStep 875549 = 328331) (by norm_num)
theorem B580657 : Blo 515797 580657 := bbase (se 2 (by rfl) ⟨217746, by rfl⟩ : syracuseStep 580657 = 435493) (by norm_num)
theorem B777269 : Blo 515797 777269 := bbase (se 5 (by rfl) ⟨36434, by rfl⟩ : syracuseStep 777269 = 72869) (by norm_num)
theorem B1399877 : Blo 515797 1399877 := bbase (se 4 (by rfl) ⟨131238, by rfl⟩ : syracuseStep 1399877 = 262477) (by norm_num)
theorem B777293 : Blo 515797 777293 := bbase (se 3 (by rfl) ⟨145742, by rfl⟩ : syracuseStep 777293 = 291485) (by norm_num)
theorem B580693 : Blo 515797 580693 := bbase (se 8 (by rfl) ⟨3402, by rfl⟩ : syracuseStep 580693 = 6805) (by norm_num)
theorem B777317 : Blo 515797 777317 := bbase (se 4 (by rfl) ⟨72873, by rfl⟩ : syracuseStep 777317 = 145747) (by norm_num)
theorem B580729 : Blo 515797 580729 := bbase (se 2 (by rfl) ⟨217773, by rfl⟩ : syracuseStep 580729 = 435547) (by norm_num)
theorem B777341 : Blo 515797 777341 := bbase (se 3 (by rfl) ⟨145751, by rfl⟩ : syracuseStep 777341 = 291503) (by norm_num)
theorem B777365 : Blo 515797 777365 := bbase (se 6 (by rfl) ⟨18219, by rfl⟩ : syracuseStep 777365 = 36439) (by norm_num)
theorem B580765 : Blo 515797 580765 := bbase (se 3 (by rfl) ⟨108893, by rfl⟩ : syracuseStep 580765 = 217787) (by norm_num)
theorem B875677 : Blo 515797 875677 := bbase (se 3 (by rfl) ⟨164189, by rfl⟩ : syracuseStep 875677 = 328379) (by norm_num)
theorem B777389 : Blo 515797 777389 := bbase (se 3 (by rfl) ⟨145760, by rfl⟩ : syracuseStep 777389 = 291521) (by norm_num)
theorem B1105085 : Blo 515797 1105085 := bbase (se 3 (by rfl) ⟨207203, by rfl⟩ : syracuseStep 1105085 = 414407) (by norm_num)
theorem B580801 : Blo 515797 580801 := bbase (se 2 (by rfl) ⟨217800, by rfl⟩ : syracuseStep 580801 = 435601) (by norm_num)
theorem B777413 : Blo 515797 777413 := bbase (se 4 (by rfl) ⟨72882, by rfl⟩ : syracuseStep 777413 = 145765) (by norm_num)
theorem B777437 : Blo 515797 777437 := bbase (se 3 (by rfl) ⟨145769, by rfl⟩ : syracuseStep 777437 = 291539) (by norm_num)
theorem B580837 : Blo 515797 580837 := bbase (se 4 (by rfl) ⟨54453, by rfl⟩ : syracuseStep 580837 = 108907) (by norm_num)
theorem B777461 : Blo 515797 777461 := bbase (se 5 (by rfl) ⟨36443, by rfl⟩ : syracuseStep 777461 = 72887) (by norm_num)
theorem B875765 : Blo 515797 875765 := bbase (se 5 (by rfl) ⟨41051, by rfl⟩ : syracuseStep 875765 = 82103) (by norm_num)
theorem B580873 : Blo 515797 580873 := bbase (se 2 (by rfl) ⟨217827, by rfl⟩ : syracuseStep 580873 = 435655) (by norm_num)
theorem B777485 : Blo 515797 777485 := bbase (se 3 (by rfl) ⟨145778, by rfl⟩ : syracuseStep 777485 = 291557) (by norm_num)
theorem B777509 : Blo 515797 777509 := bbase (se 4 (by rfl) ⟨72891, by rfl⟩ : syracuseStep 777509 = 145783) (by norm_num)
theorem B580909 : Blo 515797 580909 := bbase (se 3 (by rfl) ⟨108920, by rfl⟩ : syracuseStep 580909 = 217841) (by norm_num)
theorem B1793333 : Blo 515797 1793333 := bbase (se 5 (by rfl) ⟨84062, by rfl⟩ : syracuseStep 1793333 = 168125) (by norm_num)
theorem B777533 : Blo 515797 777533 := bbase (se 3 (by rfl) ⟨145787, by rfl⟩ : syracuseStep 777533 = 291575) (by norm_num)
theorem B580945 : Blo 515797 580945 := bbase (se 2 (by rfl) ⟨217854, by rfl⟩ : syracuseStep 580945 = 435709) (by norm_num)
theorem B777557 : Blo 515797 777557 := bbase (se 11 (by rfl) ⟨569, by rfl⟩ : syracuseStep 777557 = 1139) (by norm_num)
theorem B777581 : Blo 515797 777581 := bbase (se 3 (by rfl) ⟨145796, by rfl⟩ : syracuseStep 777581 = 291593) (by norm_num)
theorem B580981 : Blo 515797 580981 := bbase (se 5 (by rfl) ⟨27233, by rfl⟩ : syracuseStep 580981 = 54467) (by norm_num)
theorem B875893 : Blo 515797 875893 := bbase (se 5 (by rfl) ⟨41057, by rfl⟩ : syracuseStep 875893 = 82115) (by norm_num)
theorem B777605 : Blo 515797 777605 := bbase (se 4 (by rfl) ⟨72900, by rfl⟩ : syracuseStep 777605 = 145801) (by norm_num)
theorem B5037461 : Blo 515797 5037461 := bbase (se 6 (by rfl) ⟨118065, by rfl⟩ : syracuseStep 5037461 = 236131) (by norm_num)
theorem B581017 : Blo 515797 581017 := bbase (se 2 (by rfl) ⟨217881, by rfl⟩ : syracuseStep 581017 = 435763) (by norm_num)
theorem B777629 : Blo 515797 777629 := bbase (se 3 (by rfl) ⟨145805, by rfl⟩ : syracuseStep 777629 = 291611) (by norm_num)
theorem B777653 : Blo 515797 777653 := bbase (se 5 (by rfl) ⟨36452, by rfl⟩ : syracuseStep 777653 = 72905) (by norm_num)
theorem B581053 : Blo 515797 581053 := bbase (se 3 (by rfl) ⟨108947, by rfl⟩ : syracuseStep 581053 = 217895) (by norm_num)
theorem B777677 : Blo 515797 777677 := bbase (se 3 (by rfl) ⟨145814, by rfl⟩ : syracuseStep 777677 = 291629) (by norm_num)
theorem B875981 : Blo 515797 875981 := bbase (se 3 (by rfl) ⟨164246, by rfl⟩ : syracuseStep 875981 = 328493) (by norm_num)
theorem B581089 : Blo 515797 581089 := bbase (se 2 (by rfl) ⟨217908, by rfl⟩ : syracuseStep 581089 = 435817) (by norm_num)
theorem B2481637 : Blo 515797 2481637 := bbase (se 4 (by rfl) ⟨232653, by rfl⟩ : syracuseStep 2481637 = 465307) (by norm_num)
theorem B777701 : Blo 515797 777701 := bbase (se 4 (by rfl) ⟨72909, by rfl⟩ : syracuseStep 777701 = 145819) (by norm_num)
theorem B1924597 : Blo 515797 1924597 := bbase (se 5 (by rfl) ⟨90215, by rfl⟩ : syracuseStep 1924597 = 180431) (by norm_num)
theorem B777725 : Blo 515797 777725 := bbase (se 3 (by rfl) ⟨145823, by rfl⟩ : syracuseStep 777725 = 291647) (by norm_num)
theorem B581125 : Blo 515797 581125 := bbase (se 4 (by rfl) ⟨54480, by rfl⟩ : syracuseStep 581125 = 108961) (by norm_num)
theorem B3923477 : Blo 515797 3923477 := bbase (se 6 (by rfl) ⟨91956, by rfl⟩ : syracuseStep 3923477 = 183913) (by norm_num)
theorem B777749 : Blo 515797 777749 := bbase (se 6 (by rfl) ⟨18228, by rfl⟩ : syracuseStep 777749 = 36457) (by norm_num)
theorem B581161 : Blo 515797 581161 := bbase (se 2 (by rfl) ⟨217935, by rfl⟩ : syracuseStep 581161 = 435871) (by norm_num)
theorem B777773 : Blo 515797 777773 := bbase (se 3 (by rfl) ⟨145832, by rfl⟩ : syracuseStep 777773 = 291665) (by norm_num)
theorem B777797 : Blo 515797 777797 := bbase (se 4 (by rfl) ⟨72918, by rfl⟩ : syracuseStep 777797 = 145837) (by norm_num)
theorem B581197 : Blo 515797 581197 := bbase (se 3 (by rfl) ⟨108974, by rfl⟩ : syracuseStep 581197 = 217949) (by norm_num)
theorem B876109 : Blo 515797 876109 := bbase (se 3 (by rfl) ⟨164270, by rfl⟩ : syracuseStep 876109 = 328541) (by norm_num)
theorem B777821 : Blo 515797 777821 := bbase (se 3 (by rfl) ⟨145841, by rfl⟩ : syracuseStep 777821 = 291683) (by norm_num)
theorem B581233 : Blo 515797 581233 := bbase (se 2 (by rfl) ⟨217962, by rfl⟩ : syracuseStep 581233 = 435925) (by norm_num)
theorem B777845 : Blo 515797 777845 := bbase (se 5 (by rfl) ⟨36461, by rfl⟩ : syracuseStep 777845 = 72923) (by norm_num)
theorem B777869 : Blo 515797 777869 := bbase (se 3 (by rfl) ⟨145850, by rfl⟩ : syracuseStep 777869 = 291701) (by norm_num)
theorem B581269 : Blo 515797 581269 := bbase (se 6 (by rfl) ⟨13623, by rfl⟩ : syracuseStep 581269 = 27247) (by norm_num)
theorem B2219669 : Blo 515797 2219669 := bbase (se 6 (by rfl) ⟨52023, by rfl⟩ : syracuseStep 2219669 = 104047) (by norm_num)
theorem B777893 : Blo 515797 777893 := bbase (se 4 (by rfl) ⟨72927, by rfl⟩ : syracuseStep 777893 = 145855) (by norm_num)
theorem B876197 : Blo 515797 876197 := bbase (se 4 (by rfl) ⟨82143, by rfl⟩ : syracuseStep 876197 = 164287) (by norm_num)
theorem B1105589 : Blo 515797 1105589 := bbase (se 5 (by rfl) ⟨51824, by rfl⟩ : syracuseStep 1105589 = 103649) (by norm_num)
theorem B581305 : Blo 515797 581305 := bbase (se 2 (by rfl) ⟨217989, by rfl⟩ : syracuseStep 581305 = 435979) (by norm_num)
theorem B1105597 : Blo 515797 1105597 := bbase (se 3 (by rfl) ⟨207299, by rfl⟩ : syracuseStep 1105597 = 414599) (by norm_num)
theorem B777917 : Blo 515797 777917 := bbase (se 3 (by rfl) ⟨145859, by rfl⟩ : syracuseStep 777917 = 291719) (by norm_num)
theorem B777941 : Blo 515797 777941 := bbase (se 7 (by rfl) ⟨9116, by rfl⟩ : syracuseStep 777941 = 18233) (by norm_num)
theorem B581341 : Blo 515797 581341 := bbase (se 3 (by rfl) ⟨109001, by rfl⟩ : syracuseStep 581341 = 218003) (by norm_num)
theorem B777965 : Blo 515797 777965 := bbase (se 3 (by rfl) ⟨145868, by rfl⟩ : syracuseStep 777965 = 291737) (by norm_num)
theorem B581377 : Blo 515797 581377 := bbase (se 2 (by rfl) ⟨218016, by rfl⟩ : syracuseStep 581377 = 436033) (by norm_num)
theorem B777989 : Blo 515797 777989 := bbase (se 4 (by rfl) ⟨72936, by rfl⟩ : syracuseStep 777989 = 145873) (by norm_num)
theorem B778013 : Blo 515797 778013 := bbase (se 3 (by rfl) ⟨145877, by rfl⟩ : syracuseStep 778013 = 291755) (by norm_num)
theorem B581413 : Blo 515797 581413 := bbase (se 4 (by rfl) ⟨54507, by rfl⟩ : syracuseStep 581413 = 109015) (by norm_num)
theorem B876325 : Blo 515797 876325 := bbase (se 4 (by rfl) ⟨82155, by rfl⟩ : syracuseStep 876325 = 164311) (by norm_num)
theorem B778037 : Blo 515797 778037 := bbase (se 5 (by rfl) ⟨36470, by rfl⟩ : syracuseStep 778037 = 72941) (by norm_num)
theorem B581449 : Blo 515797 581449 := bbase (se 2 (by rfl) ⟨218043, by rfl⟩ : syracuseStep 581449 = 436087) (by norm_num)
theorem B778061 : Blo 515797 778061 := bbase (se 3 (by rfl) ⟨145886, by rfl⟩ : syracuseStep 778061 = 291773) (by norm_num)
theorem B778085 : Blo 515797 778085 := bbase (se 4 (by rfl) ⟨72945, by rfl⟩ : syracuseStep 778085 = 145891) (by norm_num)
theorem B581485 : Blo 515797 581485 := bbase (se 3 (by rfl) ⟨109028, by rfl⟩ : syracuseStep 581485 = 218057) (by norm_num)
theorem B778109 : Blo 515797 778109 := bbase (se 3 (by rfl) ⟨145895, by rfl⟩ : syracuseStep 778109 = 291791) (by norm_num)
theorem B876413 : Blo 515797 876413 := bbase (se 3 (by rfl) ⟨164327, by rfl⟩ : syracuseStep 876413 = 328655) (by norm_num)
theorem B581521 : Blo 515797 581521 := bbase (se 2 (by rfl) ⟨218070, by rfl⟩ : syracuseStep 581521 = 436141) (by norm_num)
theorem B778133 : Blo 515797 778133 := bbase (se 6 (by rfl) ⟨18237, by rfl⟩ : syracuseStep 778133 = 36475) (by norm_num)
theorem B778157 : Blo 515797 778157 := bbase (se 3 (by rfl) ⟨145904, by rfl⟩ : syracuseStep 778157 = 291809) (by norm_num)
theorem B581557 : Blo 515797 581557 := bbase (se 5 (by rfl) ⟨27260, by rfl⟩ : syracuseStep 581557 = 54521) (by norm_num)
theorem B778181 : Blo 515797 778181 := bbase (se 4 (by rfl) ⟨72954, by rfl⟩ : syracuseStep 778181 = 145909) (by norm_num)
theorem B581593 : Blo 515797 581593 := bbase (se 2 (by rfl) ⟨218097, by rfl⟩ : syracuseStep 581593 = 436195) (by norm_num)
theorem B778205 : Blo 515797 778205 := bbase (se 3 (by rfl) ⟨145913, by rfl⟩ : syracuseStep 778205 = 291827) (by norm_num)
theorem B2613221 : Blo 515797 2613221 := bbase (se 4 (by rfl) ⟨244989, by rfl⟩ : syracuseStep 2613221 = 489979) (by norm_num)
theorem B778229 : Blo 515797 778229 := bbase (se 5 (by rfl) ⟨36479, by rfl⟩ : syracuseStep 778229 = 72959) (by norm_num)
theorem B581629 : Blo 515797 581629 := bbase (se 3 (by rfl) ⟨109055, by rfl⟩ : syracuseStep 581629 = 218111) (by norm_num)
theorem B876541 : Blo 515797 876541 := bbase (se 3 (by rfl) ⟨164351, by rfl⟩ : syracuseStep 876541 = 328703) (by norm_num)
theorem B778253 : Blo 515797 778253 := bbase (se 3 (by rfl) ⟨145922, by rfl⟩ : syracuseStep 778253 = 291845) (by norm_num)
theorem B581665 : Blo 515797 581665 := bbase (se 2 (by rfl) ⟨218124, by rfl⟩ : syracuseStep 581665 = 436249) (by norm_num)
theorem B778277 : Blo 515797 778277 := bbase (se 4 (by rfl) ⟨72963, by rfl⟩ : syracuseStep 778277 = 145927) (by norm_num)
theorem B778301 : Blo 515797 778301 := bbase (se 3 (by rfl) ⟨145931, by rfl⟩ : syracuseStep 778301 = 291863) (by norm_num)
theorem B581701 : Blo 515797 581701 := bbase (se 4 (by rfl) ⟨54534, by rfl⟩ : syracuseStep 581701 = 109069) (by norm_num)
theorem B778325 : Blo 515797 778325 := bbase (se 8 (by rfl) ⟨4560, by rfl⟩ : syracuseStep 778325 = 9121) (by norm_num)
theorem B876629 : Blo 515797 876629 := bbase (se 8 (by rfl) ⟨5136, by rfl⟩ : syracuseStep 876629 = 10273) (by norm_num)
theorem B581737 : Blo 515797 581737 := bbase (se 2 (by rfl) ⟨218151, by rfl⟩ : syracuseStep 581737 = 436303) (by norm_num)
theorem B778349 : Blo 515797 778349 := bbase (se 3 (by rfl) ⟨145940, by rfl⟩ : syracuseStep 778349 = 291881) (by norm_num)
theorem B778373 : Blo 515797 778373 := bbase (se 4 (by rfl) ⟨72972, by rfl⟩ : syracuseStep 778373 = 145945) (by norm_num)
theorem B581773 : Blo 515797 581773 := bbase (se 3 (by rfl) ⟨109082, by rfl⟩ : syracuseStep 581773 = 218165) (by norm_num)
theorem B778397 : Blo 515797 778397 := bbase (se 3 (by rfl) ⟨145949, by rfl⟩ : syracuseStep 778397 = 291899) (by norm_num)
theorem B581809 : Blo 515797 581809 := bbase (se 2 (by rfl) ⟨218178, by rfl⟩ : syracuseStep 581809 = 436357) (by norm_num)
theorem B778421 : Blo 515797 778421 := bbase (se 5 (by rfl) ⟨36488, by rfl⟩ : syracuseStep 778421 = 72977) (by norm_num)
theorem B778445 : Blo 515797 778445 := bbase (se 3 (by rfl) ⟨145958, by rfl⟩ : syracuseStep 778445 = 291917) (by norm_num)
theorem B581845 : Blo 515797 581845 := bbase (se 7 (by rfl) ⟨6818, by rfl⟩ : syracuseStep 581845 = 13637) (by norm_num)
theorem B876757 : Blo 515797 876757 := bbase (se 7 (by rfl) ⟨10274, by rfl⟩ : syracuseStep 876757 = 20549) (by norm_num)
theorem B778469 : Blo 515797 778469 := bbase (se 4 (by rfl) ⟨72981, by rfl⟩ : syracuseStep 778469 = 145963) (by norm_num)
theorem B581881 : Blo 515797 581881 := bbase (se 2 (by rfl) ⟨218205, by rfl⟩ : syracuseStep 581881 = 436411) (by norm_num)
theorem B778493 : Blo 515797 778493 := bbase (se 3 (by rfl) ⟨145967, by rfl⟩ : syracuseStep 778493 = 291935) (by norm_num)
theorem B778517 : Blo 515797 778517 := bbase (se 6 (by rfl) ⟨18246, by rfl⟩ : syracuseStep 778517 = 36493) (by norm_num)
theorem B581917 : Blo 515797 581917 := bbase (se 3 (by rfl) ⟨109109, by rfl⟩ : syracuseStep 581917 = 218219) (by norm_num)
theorem B778541 : Blo 515797 778541 := bbase (se 3 (by rfl) ⟨145976, by rfl⟩ : syracuseStep 778541 = 291953) (by norm_num)
theorem B876845 : Blo 515797 876845 := bbase (se 3 (by rfl) ⟨164408, by rfl⟩ : syracuseStep 876845 = 328817) (by norm_num)
theorem B581953 : Blo 515797 581953 := bbase (se 2 (by rfl) ⟨218232, by rfl⟩ : syracuseStep 581953 = 436465) (by norm_num)
theorem B778565 : Blo 515797 778565 := bbase (se 4 (by rfl) ⟨72990, by rfl⟩ : syracuseStep 778565 = 145981) (by norm_num)
theorem B778589 : Blo 515797 778589 := bbase (se 3 (by rfl) ⟨145985, by rfl⟩ : syracuseStep 778589 = 291971) (by norm_num)
theorem B581989 : Blo 515797 581989 := bbase (se 4 (by rfl) ⟨54561, by rfl⟩ : syracuseStep 581989 = 109123) (by norm_num)
theorem B778613 : Blo 515797 778613 := bbase (se 5 (by rfl) ⟨36497, by rfl⟩ : syracuseStep 778613 = 72995) (by norm_num)
theorem B582025 : Blo 515797 582025 := bbase (se 2 (by rfl) ⟨218259, by rfl⟩ : syracuseStep 582025 = 436519) (by norm_num)
theorem B778637 : Blo 515797 778637 := bbase (se 3 (by rfl) ⟨145994, by rfl⟩ : syracuseStep 778637 = 291989) (by norm_num)
theorem B778661 : Blo 515797 778661 := bbase (se 4 (by rfl) ⟨72999, by rfl⟩ : syracuseStep 778661 = 145999) (by norm_num)
theorem B582061 : Blo 515797 582061 := bbase (se 3 (by rfl) ⟨109136, by rfl⟩ : syracuseStep 582061 = 218273) (by norm_num)
theorem B876973 : Blo 515797 876973 := bbase (se 3 (by rfl) ⟨164432, by rfl⟩ : syracuseStep 876973 = 328865) (by norm_num)
theorem B778685 : Blo 515797 778685 := bbase (se 3 (by rfl) ⟨146003, by rfl⟩ : syracuseStep 778685 = 292007) (by norm_num)
theorem B582097 : Blo 515797 582097 := bbase (se 2 (by rfl) ⟨218286, by rfl⟩ : syracuseStep 582097 = 436573) (by norm_num)
theorem B778709 : Blo 515797 778709 := bbase (se 7 (by rfl) ⟨9125, by rfl⟩ : syracuseStep 778709 = 18251) (by norm_num)
theorem B778733 : Blo 515797 778733 := bbase (se 3 (by rfl) ⟨146012, by rfl⟩ : syracuseStep 778733 = 292025) (by norm_num)
theorem B582133 : Blo 515797 582133 := bbase (se 5 (by rfl) ⟨27287, by rfl⟩ : syracuseStep 582133 = 54575) (by norm_num)
theorem B778757 : Blo 515797 778757 := bbase (se 4 (by rfl) ⟨73008, by rfl⟩ : syracuseStep 778757 = 146017) (by norm_num)
theorem B877061 : Blo 515797 877061 := bbase (se 4 (by rfl) ⟨82224, by rfl⟩ : syracuseStep 877061 = 164449) (by norm_num)
theorem B582169 : Blo 515797 582169 := bbase (se 2 (by rfl) ⟨218313, by rfl⟩ : syracuseStep 582169 = 436627) (by norm_num)
theorem B778781 : Blo 515797 778781 := bbase (se 3 (by rfl) ⟨146021, by rfl⟩ : syracuseStep 778781 = 292043) (by norm_num)
theorem B778805 : Blo 515797 778805 := bbase (se 5 (by rfl) ⟨36506, by rfl⟩ : syracuseStep 778805 = 73013) (by norm_num)
theorem B582205 : Blo 515797 582205 := bbase (se 3 (by rfl) ⟨109163, by rfl⟩ : syracuseStep 582205 = 218327) (by norm_num)
theorem B778829 : Blo 515797 778829 := bbase (se 3 (by rfl) ⟨146030, by rfl⟩ : syracuseStep 778829 = 292061) (by norm_num)
theorem B1663573 : Blo 515797 1663573 := bbase (se 8 (by rfl) ⟨9747, by rfl⟩ : syracuseStep 1663573 = 19495) (by norm_num)
theorem B582241 : Blo 515797 582241 := bbase (se 2 (by rfl) ⟨218340, by rfl⟩ : syracuseStep 582241 = 436681) (by norm_num)
theorem B778853 : Blo 515797 778853 := bbase (se 4 (by rfl) ⟨73017, by rfl⟩ : syracuseStep 778853 = 146035) (by norm_num)
theorem B778877 : Blo 515797 778877 := bbase (se 3 (by rfl) ⟨146039, by rfl⟩ : syracuseStep 778877 = 292079) (by norm_num)
theorem B582277 : Blo 515797 582277 := bbase (se 4 (by rfl) ⟨54588, by rfl⟩ : syracuseStep 582277 = 109177) (by norm_num)
theorem B778901 : Blo 515797 778901 := bbase (se 6 (by rfl) ⟨18255, by rfl⟩ : syracuseStep 778901 = 36511) (by norm_num)
theorem B582313 : Blo 515797 582313 := bbase (se 2 (by rfl) ⟨218367, by rfl⟩ : syracuseStep 582313 = 436735) (by norm_num)
theorem B778925 : Blo 515797 778925 := bbase (se 3 (by rfl) ⟨146048, by rfl⟩ : syracuseStep 778925 = 292097) (by norm_num)
theorem B778949 : Blo 515797 778949 := bbase (se 4 (by rfl) ⟨73026, by rfl⟩ : syracuseStep 778949 = 146053) (by norm_num)
theorem B582349 : Blo 515797 582349 := bbase (se 3 (by rfl) ⟨109190, by rfl⟩ : syracuseStep 582349 = 218381) (by norm_num)
theorem B778973 : Blo 515797 778973 := bbase (se 3 (by rfl) ⟨146057, by rfl⟩ : syracuseStep 778973 = 292115) (by norm_num)
theorem B582385 : Blo 515797 582385 := bbase (se 2 (by rfl) ⟨218394, by rfl⟩ : syracuseStep 582385 = 436789) (by norm_num)
theorem B778997 : Blo 515797 778997 := bbase (se 5 (by rfl) ⟨36515, by rfl⟩ : syracuseStep 778997 = 73031) (by norm_num)
theorem B779021 : Blo 515797 779021 := bbase (se 3 (by rfl) ⟨146066, by rfl⟩ : syracuseStep 779021 = 292133) (by norm_num)
theorem B582421 : Blo 515797 582421 := bbase (se 6 (by rfl) ⟨13650, by rfl⟩ : syracuseStep 582421 = 27301) (by norm_num)
theorem B1106725 : Blo 515797 1106725 := bbase (se 4 (by rfl) ⟨103755, by rfl⟩ : syracuseStep 1106725 = 207511) (by norm_num)
theorem B779045 : Blo 515797 779045 := bbase (se 4 (by rfl) ⟨73035, by rfl⟩ : syracuseStep 779045 = 146071) (by norm_num)
theorem B582457 : Blo 515797 582457 := bbase (se 2 (by rfl) ⟨218421, by rfl⟩ : syracuseStep 582457 = 436843) (by norm_num)
theorem B779069 : Blo 515797 779069 := bbase (se 3 (by rfl) ⟨146075, by rfl⟩ : syracuseStep 779069 = 292151) (by norm_num)
theorem B1663829 : Blo 515797 1663829 := bbase (se 9 (by rfl) ⟨4874, by rfl⟩ : syracuseStep 1663829 = 9749) (by norm_num)
theorem B779093 : Blo 515797 779093 := bbase (se 9 (by rfl) ⟨2282, by rfl⟩ : syracuseStep 779093 = 4565) (by norm_num)
theorem B582493 : Blo 515797 582493 := bbase (se 3 (by rfl) ⟨109217, by rfl⟩ : syracuseStep 582493 = 218435) (by norm_num)
theorem B779117 : Blo 515797 779117 := bbase (se 3 (by rfl) ⟨146084, by rfl⟩ : syracuseStep 779117 = 292169) (by norm_num)
theorem B582529 : Blo 515797 582529 := bbase (se 2 (by rfl) ⟨218448, by rfl⟩ : syracuseStep 582529 = 436897) (by norm_num)
theorem B779141 : Blo 515797 779141 := bbase (se 4 (by rfl) ⟨73044, by rfl⟩ : syracuseStep 779141 = 146089) (by norm_num)
theorem B779165 : Blo 515797 779165 := bbase (se 3 (by rfl) ⟨146093, by rfl⟩ : syracuseStep 779165 = 292187) (by norm_num)
theorem B582565 : Blo 515797 582565 := bbase (se 4 (by rfl) ⟨54615, by rfl⟩ : syracuseStep 582565 = 109231) (by norm_num)
theorem B779189 : Blo 515797 779189 := bbase (se 5 (by rfl) ⟨36524, by rfl⟩ : syracuseStep 779189 = 73049) (by norm_num)
theorem B582601 : Blo 515797 582601 := bbase (se 2 (by rfl) ⟨218475, by rfl⟩ : syracuseStep 582601 = 436951) (by norm_num)
theorem B779213 : Blo 515797 779213 := bbase (se 3 (by rfl) ⟨146102, by rfl⟩ : syracuseStep 779213 = 292205) (by norm_num)
theorem B779237 : Blo 515797 779237 := bbase (se 4 (by rfl) ⟨73053, by rfl⟩ : syracuseStep 779237 = 146107) (by norm_num)
theorem B582637 : Blo 515797 582637 := bbase (se 3 (by rfl) ⟨109244, by rfl⟩ : syracuseStep 582637 = 218489) (by norm_num)
theorem B779261 : Blo 515797 779261 := bbase (se 3 (by rfl) ⟨146111, by rfl⟩ : syracuseStep 779261 = 292223) (by norm_num)
theorem B582673 : Blo 515797 582673 := bbase (se 2 (by rfl) ⟨218502, by rfl⟩ : syracuseStep 582673 = 437005) (by norm_num)
theorem B779285 : Blo 515797 779285 := bbase (se 6 (by rfl) ⟨18264, by rfl⟩ : syracuseStep 779285 = 36529) (by norm_num)
theorem B779309 : Blo 515797 779309 := bbase (se 3 (by rfl) ⟨146120, by rfl⟩ : syracuseStep 779309 = 292241) (by norm_num)
theorem B582709 : Blo 515797 582709 := bbase (se 5 (by rfl) ⟨27314, by rfl⟩ : syracuseStep 582709 = 54629) (by norm_num)
theorem B779333 : Blo 515797 779333 := bbase (se 4 (by rfl) ⟨73062, by rfl⟩ : syracuseStep 779333 = 146125) (by norm_num)
theorem B582745 : Blo 515797 582745 := bbase (se 2 (by rfl) ⟨218529, by rfl⟩ : syracuseStep 582745 = 437059) (by norm_num)
theorem B779357 : Blo 515797 779357 := bbase (se 3 (by rfl) ⟨146129, by rfl⟩ : syracuseStep 779357 = 292259) (by norm_num)
theorem B779381 : Blo 515797 779381 := bbase (se 5 (by rfl) ⟨36533, by rfl⟩ : syracuseStep 779381 = 73067) (by norm_num)
theorem B582781 : Blo 515797 582781 := bbase (se 3 (by rfl) ⟨109271, by rfl⟩ : syracuseStep 582781 = 218543) (by norm_num)
theorem B779405 : Blo 515797 779405 := bbase (se 3 (by rfl) ⟨146138, by rfl⟩ : syracuseStep 779405 = 292277) (by norm_num)
theorem B1107101 : Blo 515797 1107101 := bbase (se 3 (by rfl) ⟨207581, by rfl⟩ : syracuseStep 1107101 = 415163) (by norm_num)
theorem B582817 : Blo 515797 582817 := bbase (se 2 (by rfl) ⟨218556, by rfl⟩ : syracuseStep 582817 = 437113) (by norm_num)
theorem B779429 : Blo 515797 779429 := bbase (se 4 (by rfl) ⟨73071, by rfl⟩ : syracuseStep 779429 = 146143) (by norm_num)
theorem B779453 : Blo 515797 779453 := bbase (se 3 (by rfl) ⟨146147, by rfl⟩ : syracuseStep 779453 = 292295) (by norm_num)
theorem B582853 : Blo 515797 582853 := bbase (se 4 (by rfl) ⟨54642, by rfl⟩ : syracuseStep 582853 = 109285) (by norm_num)
theorem B779477 : Blo 515797 779477 := bbase (se 7 (by rfl) ⟨9134, by rfl⟩ : syracuseStep 779477 = 18269) (by norm_num)
theorem B1500389 : Blo 515797 1500389 := bbase (se 4 (by rfl) ⟨140661, by rfl⟩ : syracuseStep 1500389 = 281323) (by norm_num)
theorem B582889 : Blo 515797 582889 := bbase (se 2 (by rfl) ⟨218583, by rfl⟩ : syracuseStep 582889 = 437167) (by norm_num)
theorem B779501 : Blo 515797 779501 := bbase (se 3 (by rfl) ⟨146156, by rfl⟩ : syracuseStep 779501 = 292313) (by norm_num)
theorem B1860853 : Blo 515797 1860853 := bbase (se 5 (by rfl) ⟨87227, by rfl⟩ : syracuseStep 1860853 = 174455) (by norm_num)
theorem B2614517 : Blo 515797 2614517 := bbase (se 5 (by rfl) ⟨122555, by rfl⟩ : syracuseStep 2614517 = 245111) (by norm_num)
theorem B1959173 : Blo 515797 1959173 := bbase (se 4 (by rfl) ⟨183672, by rfl⟩ : syracuseStep 1959173 = 367345) (by norm_num)
theorem B779525 : Blo 515797 779525 := bbase (se 4 (by rfl) ⟨73080, by rfl⟩ : syracuseStep 779525 = 146161) (by norm_num)
theorem B582925 : Blo 515797 582925 := bbase (se 3 (by rfl) ⟨109298, by rfl⟩ : syracuseStep 582925 = 218597) (by norm_num)
theorem B779549 : Blo 515797 779549 := bbase (se 3 (by rfl) ⟨146165, by rfl⟩ : syracuseStep 779549 = 292331) (by norm_num)
theorem B582961 : Blo 515797 582961 := bbase (se 2 (by rfl) ⟨218610, by rfl⟩ : syracuseStep 582961 = 437221) (by norm_num)
theorem B779573 : Blo 515797 779573 := bbase (se 5 (by rfl) ⟨36542, by rfl⟩ : syracuseStep 779573 = 73085) (by norm_num)
theorem B779597 : Blo 515797 779597 := bbase (se 3 (by rfl) ⟨146174, by rfl⟩ : syracuseStep 779597 = 292349) (by norm_num)
theorem B582997 : Blo 515797 582997 := bbase (se 12 (by rfl) ⟨213, by rfl⟩ : syracuseStep 582997 = 427) (by norm_num)
theorem B779621 : Blo 515797 779621 := bbase (se 4 (by rfl) ⟨73089, by rfl⟩ : syracuseStep 779621 = 146179) (by norm_num)
theorem B583033 : Blo 515797 583033 := bbase (se 2 (by rfl) ⟨218637, by rfl⟩ : syracuseStep 583033 = 437275) (by norm_num)
theorem B779645 : Blo 515797 779645 := bbase (se 3 (by rfl) ⟨146183, by rfl⟩ : syracuseStep 779645 = 292367) (by norm_num)
theorem B779669 : Blo 515797 779669 := bbase (se 6 (by rfl) ⟨18273, by rfl⟩ : syracuseStep 779669 = 36547) (by norm_num)
theorem B583069 : Blo 515797 583069 := bbase (se 3 (by rfl) ⟨109325, by rfl⟩ : syracuseStep 583069 = 218651) (by norm_num)
theorem B779693 : Blo 515797 779693 := bbase (se 3 (by rfl) ⟨146192, by rfl⟩ : syracuseStep 779693 = 292385) (by norm_num)
theorem B583105 : Blo 515797 583105 := bbase (se 2 (by rfl) ⟨218664, by rfl⟩ : syracuseStep 583105 = 437329) (by norm_num)
theorem B583141 : Blo 515797 583141 := bbase (se 4 (by rfl) ⟨54669, by rfl⟩ : syracuseStep 583141 = 109339) (by norm_num)
theorem B583177 : Blo 515797 583177 := bbase (se 2 (by rfl) ⟨218691, by rfl⟩ : syracuseStep 583177 = 437383) (by norm_num)
theorem B1959461 : Blo 515797 1959461 := bbase (se 4 (by rfl) ⟨183699, by rfl⟩ : syracuseStep 1959461 = 367399) (by norm_num)
theorem B583213 : Blo 515797 583213 := bbase (se 3 (by rfl) ⟨109352, by rfl⟩ : syracuseStep 583213 = 218705) (by norm_num)
theorem B583249 : Blo 515797 583249 := bbase (se 2 (by rfl) ⟨218718, by rfl⟩ : syracuseStep 583249 = 437437) (by norm_num)
theorem B583285 : Blo 515797 583285 := bbase (se 5 (by rfl) ⟨27341, by rfl⟩ : syracuseStep 583285 = 54683) (by norm_num)
theorem B2516629 : Blo 515797 2516629 := bbase (se 6 (by rfl) ⟨58983, by rfl⟩ : syracuseStep 2516629 = 117967) (by norm_num)
theorem B1402517 : Blo 515797 1402517 := bbase (se 6 (by rfl) ⟨32871, by rfl⟩ : syracuseStep 1402517 = 65743) (by norm_num)
theorem B583321 : Blo 515797 583321 := bbase (se 2 (by rfl) ⟨218745, by rfl⟩ : syracuseStep 583321 = 437491) (by norm_num)
theorem B583357 : Blo 515797 583357 := bbase (se 3 (by rfl) ⟨109379, by rfl⟩ : syracuseStep 583357 = 218759) (by norm_num)
theorem B583393 : Blo 515797 583393 := bbase (se 2 (by rfl) ⟨218772, by rfl⟩ : syracuseStep 583393 = 437545) (by norm_num)
theorem B583429 : Blo 515797 583429 := bbase (se 4 (by rfl) ⟨54696, by rfl⟩ : syracuseStep 583429 = 109393) (by norm_num)
theorem B1402645 : Blo 515797 1402645 := bbase (se 6 (by rfl) ⟨32874, by rfl⟩ : syracuseStep 1402645 = 65749) (by norm_num)
theorem B583465 : Blo 515797 583465 := bbase (se 2 (by rfl) ⟨218799, by rfl⟩ : syracuseStep 583465 = 437599) (by norm_num)
theorem B583501 : Blo 515797 583501 := bbase (se 3 (by rfl) ⟨109406, by rfl⟩ : syracuseStep 583501 = 218813) (by norm_num)
theorem B583537 : Blo 515797 583537 := bbase (se 2 (by rfl) ⟨218826, by rfl⟩ : syracuseStep 583537 = 437653) (by norm_num)
theorem B2942837 : Blo 515797 2942837 := bbase (se 5 (by rfl) ⟨137945, by rfl⟩ : syracuseStep 2942837 = 275891) (by norm_num)
theorem B583573 : Blo 515797 583573 := bbase (se 6 (by rfl) ⟨13677, by rfl⟩ : syracuseStep 583573 = 27355) (by norm_num)
theorem B583609 : Blo 515797 583609 := bbase (se 2 (by rfl) ⟨218853, by rfl⟩ : syracuseStep 583609 = 437707) (by norm_num)
theorem B583645 : Blo 515797 583645 := bbase (se 3 (by rfl) ⟨109433, by rfl⟩ : syracuseStep 583645 = 218867) (by norm_num)
theorem B550885 : Blo 515797 550885 := bbase (se 4 (by rfl) ⟨51645, by rfl⟩ : syracuseStep 550885 = 103291) (by norm_num)
theorem B583681 : Blo 515797 583681 := bbase (se 2 (by rfl) ⟨218880, by rfl⟩ : syracuseStep 583681 = 437761) (by norm_num)
theorem B2517013 : Blo 515797 2517013 := bbase (se 6 (by rfl) ⟨58992, by rfl⟩ : syracuseStep 2517013 = 117985) (by norm_num)
theorem B583717 : Blo 515797 583717 := bbase (se 4 (by rfl) ⟨54723, by rfl⟩ : syracuseStep 583717 = 109447) (by norm_num)
theorem B583753 : Blo 515797 583753 := bbase (se 2 (by rfl) ⟨218907, by rfl⟩ : syracuseStep 583753 = 437815) (by norm_num)
theorem B583789 : Blo 515797 583789 := bbase (se 3 (by rfl) ⟨109460, by rfl⟩ : syracuseStep 583789 = 218921) (by norm_num)
theorem B583825 : Blo 515797 583825 := bbase (se 2 (by rfl) ⟨218934, by rfl⟩ : syracuseStep 583825 = 437869) (by norm_num)
theorem B583861 : Blo 515797 583861 := bbase (se 5 (by rfl) ⟨27368, by rfl⟩ : syracuseStep 583861 = 54737) (by norm_num)
theorem B583897 : Blo 515797 583897 := bbase (se 2 (by rfl) ⟨218961, by rfl⟩ : syracuseStep 583897 = 437923) (by norm_num)
theorem B583933 : Blo 515797 583933 := bbase (se 3 (by rfl) ⟨109487, by rfl⟩ : syracuseStep 583933 = 218975) (by norm_num)
theorem B1894661 : Blo 515797 1894661 := bbase (se 4 (by rfl) ⟨177624, by rfl⟩ : syracuseStep 1894661 = 355249) (by norm_num)
theorem B583969 : Blo 515797 583969 := bbase (se 2 (by rfl) ⟨218988, by rfl⟩ : syracuseStep 583969 = 437977) (by norm_num)
theorem B584005 : Blo 515797 584005 := bbase (se 4 (by rfl) ⟨54750, by rfl⟩ : syracuseStep 584005 = 109501) (by norm_num)
theorem B584041 : Blo 515797 584041 := bbase (se 2 (by rfl) ⟨219015, by rfl⟩ : syracuseStep 584041 = 438031) (by norm_num)
theorem B584077 : Blo 515797 584077 := bbase (se 3 (by rfl) ⟨109514, by rfl⟩ : syracuseStep 584077 = 219029) (by norm_num)
theorem B551329 : Blo 515797 551329 := bbase (se 2 (by rfl) ⟨206748, by rfl⟩ : syracuseStep 551329 = 413497) (by norm_num)
theorem B747949 : Blo 515797 747949 := bbase (se 3 (by rfl) ⟨140240, by rfl⟩ : syracuseStep 747949 = 280481) (by norm_num)
theorem B584113 : Blo 515797 584113 := bbase (se 2 (by rfl) ⟨219042, by rfl⟩ : syracuseStep 584113 = 438085) (by norm_num)
theorem B584149 : Blo 515797 584149 := bbase (se 7 (by rfl) ⟨6845, by rfl⟩ : syracuseStep 584149 = 13691) (by norm_num)
theorem B584185 : Blo 515797 584185 := bbase (se 2 (by rfl) ⟨219069, by rfl⟩ : syracuseStep 584185 = 438139) (by norm_num)
theorem B2615813 : Blo 515797 2615813 := bbase (se 4 (by rfl) ⟨245232, by rfl⟩ : syracuseStep 2615813 = 490465) (by norm_num)
theorem B551449 : Blo 515797 551449 := bbase (se 2 (by rfl) ⟨206793, by rfl⟩ : syracuseStep 551449 = 413587) (by norm_num)
theorem B584221 : Blo 515797 584221 := bbase (se 3 (by rfl) ⟨109541, by rfl⟩ : syracuseStep 584221 = 219083) (by norm_num)
theorem B584257 : Blo 515797 584257 := bbase (se 2 (by rfl) ⟨219096, by rfl⟩ : syracuseStep 584257 = 438193) (by norm_num)
theorem B1239637 : Blo 515797 1239637 := bbase (se 8 (by rfl) ⟨7263, by rfl⟩ : syracuseStep 1239637 = 14527) (by norm_num)
theorem B584293 : Blo 515797 584293 := bbase (se 4 (by rfl) ⟨54777, by rfl⟩ : syracuseStep 584293 = 109555) (by norm_num)
theorem B2517637 : Blo 515797 2517637 := bbase (se 4 (by rfl) ⟨236028, by rfl⟩ : syracuseStep 2517637 = 472057) (by norm_num)
theorem B584329 : Blo 515797 584329 := bbase (se 2 (by rfl) ⟨219123, by rfl⟩ : syracuseStep 584329 = 438247) (by norm_num)
theorem B584365 : Blo 515797 584365 := bbase (se 3 (by rfl) ⟨109568, by rfl⟩ : syracuseStep 584365 = 219137) (by norm_num)
theorem B1960645 : Blo 515797 1960645 := bbase (se 4 (by rfl) ⟨183810, by rfl⟩ : syracuseStep 1960645 = 367621) (by norm_num)
theorem B584401 : Blo 515797 584401 := bbase (se 2 (by rfl) ⟨219150, by rfl⟩ : syracuseStep 584401 = 438301) (by norm_num)
theorem B1469141 : Blo 515797 1469141 := bbase (se 7 (by rfl) ⟨17216, by rfl⟩ : syracuseStep 1469141 = 34433) (by norm_num)
theorem B584437 : Blo 515797 584437 := bbase (se 5 (by rfl) ⟨27395, by rfl⟩ : syracuseStep 584437 = 54791) (by norm_num)
theorem B1108741 : Blo 515797 1108741 := bbase (se 4 (by rfl) ⟨103944, by rfl⟩ : syracuseStep 1108741 = 207889) (by norm_num)
theorem B551701 : Blo 515797 551701 := bbase (se 6 (by rfl) ⟨12930, by rfl⟩ : syracuseStep 551701 = 25861) (by norm_num)
theorem B551705 : Blo 515797 551705 := bbase (se 2 (by rfl) ⟨206889, by rfl⟩ : syracuseStep 551705 = 413779) (by norm_num)
theorem B584473 : Blo 515797 584473 := bbase (se 2 (by rfl) ⟨219177, by rfl⟩ : syracuseStep 584473 = 438355) (by norm_num)
theorem B1862453 : Blo 515797 1862453 := bbase (se 5 (by rfl) ⟨87302, by rfl⟩ : syracuseStep 1862453 = 174605) (by norm_num)
theorem B584509 : Blo 515797 584509 := bbase (se 3 (by rfl) ⟨109595, by rfl⟩ : syracuseStep 584509 = 219191) (by norm_num)
theorem B584545 : Blo 515797 584545 := bbase (se 2 (by rfl) ⟨219204, by rfl⟩ : syracuseStep 584545 = 438409) (by norm_num)
theorem B584581 : Blo 515797 584581 := bbase (se 4 (by rfl) ⟨54804, by rfl⟩ : syracuseStep 584581 = 109609) (by norm_num)
theorem B584617 : Blo 515797 584617 := bbase (se 2 (by rfl) ⟨219231, by rfl⟩ : syracuseStep 584617 = 438463) (by norm_num)
theorem B584653 : Blo 515797 584653 := bbase (se 3 (by rfl) ⟨109622, by rfl⟩ : syracuseStep 584653 = 219245) (by norm_num)
theorem B584689 : Blo 515797 584689 := bbase (se 2 (by rfl) ⟨219258, by rfl⟩ : syracuseStep 584689 = 438517) (by norm_num)
theorem B1960949 : Blo 515797 1960949 := bbase (se 5 (by rfl) ⟨91919, by rfl⟩ : syracuseStep 1960949 = 183839) (by norm_num)
theorem B584725 : Blo 515797 584725 := bbase (se 6 (by rfl) ⟨13704, by rfl⟩ : syracuseStep 584725 = 27409) (by norm_num)
theorem B1305629 : Blo 515797 1305629 := bbase (se 3 (by rfl) ⟨244805, by rfl⟩ : syracuseStep 1305629 = 489611) (by norm_num)
theorem B584761 : Blo 515797 584761 := bbase (se 2 (by rfl) ⟨219285, by rfl⟩ : syracuseStep 584761 = 438571) (by norm_num)
theorem B1469573 : Blo 515797 1469573 := bbase (se 4 (by rfl) ⟨137772, by rfl⟩ : syracuseStep 1469573 = 275545) (by norm_num)
theorem B1305821 : Blo 515797 1305821 := bbase (se 3 (by rfl) ⟨244841, by rfl⟩ : syracuseStep 1305821 = 489683) (by norm_num)
theorem B552269 : Blo 515797 552269 := bbase (se 3 (by rfl) ⟨103550, by rfl⟩ : syracuseStep 552269 = 207101) (by norm_num)
theorem B945605 : Blo 515797 945605 := bbase (se 4 (by rfl) ⟨88650, by rfl⟩ : syracuseStep 945605 = 177301) (by norm_num)
theorem B552457 : Blo 515797 552457 := bbase (se 2 (by rfl) ⟨207171, by rfl⟩ : syracuseStep 552457 = 414343) (by norm_num)
theorem B1306165 : Blo 515797 1306165 := bbase (se 5 (by rfl) ⟨61226, by rfl⟩ : syracuseStep 1306165 = 122453) (by norm_num)
theorem B1109629 : Blo 515797 1109629 := bbase (se 3 (by rfl) ⟨208055, by rfl⟩ : syracuseStep 1109629 = 416111) (by norm_num)
theorem B1306277 : Blo 515797 1306277 := bbase (se 4 (by rfl) ⟨122463, by rfl⟩ : syracuseStep 1306277 = 244927) (by norm_num)
theorem B7302869 : Blo 515797 7302869 := bbase (se 7 (by rfl) ⟨85580, by rfl⟩ : syracuseStep 7302869 = 171161) (by norm_num)
theorem B2617109 : Blo 515797 2617109 := bbase (se 6 (by rfl) ⟨61338, by rfl⟩ : syracuseStep 2617109 = 122677) (by norm_num)
theorem B1306469 : Blo 515797 1306469 := bbase (se 4 (by rfl) ⟨122481, by rfl⟩ : syracuseStep 1306469 = 244963) (by norm_num)
theorem B1470325 : Blo 515797 1470325 := bbase (se 5 (by rfl) ⟨68921, by rfl⟩ : syracuseStep 1470325 = 137843) (by norm_num)
theorem B1241021 : Blo 515797 1241021 := bbase (se 3 (by rfl) ⟨232691, by rfl⟩ : syracuseStep 1241021 = 465383) (by norm_num)
theorem B1241029 : Blo 515797 1241029 := bbase (se 4 (by rfl) ⟨116346, by rfl⟩ : syracuseStep 1241029 = 232693) (by norm_num)
theorem B1110125 : Blo 515797 1110125 := bbase (se 3 (by rfl) ⟨208148, by rfl⟩ : syracuseStep 1110125 = 416297) (by norm_num)
theorem B1306813 : Blo 515797 1306813 := bbase (se 3 (by rfl) ⟨245027, by rfl⟩ : syracuseStep 1306813 = 490055) (by norm_num)
theorem B979229 : Blo 515797 979229 := bbase (se 3 (by rfl) ⟨183605, by rfl⟩ : syracuseStep 979229 = 367211) (by norm_num)
theorem B1306925 : Blo 515797 1306925 := bbase (se 3 (by rfl) ⟨245048, by rfl⟩ : syracuseStep 1306925 = 490097) (by norm_num)
theorem B553277 : Blo 515797 553277 := bbase (se 3 (by rfl) ⟨103739, by rfl⟩ : syracuseStep 553277 = 207479) (by norm_num)
theorem B979381 : Blo 515797 979381 := bbase (se 5 (by rfl) ⟨45908, by rfl⟩ : syracuseStep 979381 = 91817) (by norm_num)
theorem B2093525 : Blo 515797 2093525 := bbase (se 7 (by rfl) ⟨24533, by rfl⟩ : syracuseStep 2093525 = 49067) (by norm_num)
theorem B1307117 : Blo 515797 1307117 := bbase (se 3 (by rfl) ⟨245084, by rfl⟩ : syracuseStep 1307117 = 490169) (by norm_num)
theorem B1765973 : Blo 515797 1765973 := bbase (se 8 (by rfl) ⟨10347, by rfl⟩ : syracuseStep 1765973 = 20695) (by norm_num)
theorem B979685 : Blo 515797 979685 := bbase (se 4 (by rfl) ⟨91845, by rfl⟩ : syracuseStep 979685 = 183691) (by norm_num)
theorem B553721 : Blo 515797 553721 := bbase (se 2 (by rfl) ⟨207645, by rfl⟩ : syracuseStep 553721 = 415291) (by norm_num)
theorem B1766165 : Blo 515797 1766165 := bbase (se 6 (by rfl) ⟨41394, by rfl⟩ : syracuseStep 1766165 = 82789) (by norm_num)
theorem B1307461 : Blo 515797 1307461 := bbase (se 4 (by rfl) ⟨122574, by rfl⟩ : syracuseStep 1307461 = 245149) (by norm_num)
theorem B1242029 : Blo 515797 1242029 := bbase (se 3 (by rfl) ⟨232880, by rfl⟩ : syracuseStep 1242029 = 465761) (by norm_num)
theorem B1307573 : Blo 515797 1307573 := bbase (se 5 (by rfl) ⟨61292, by rfl⟩ : syracuseStep 1307573 = 122585) (by norm_num)
theorem B553969 : Blo 515797 553969 := bbase (se 2 (by rfl) ⟨207738, by rfl⟩ : syracuseStep 553969 = 415477) (by norm_num)
theorem B2618405 : Blo 515797 2618405 := bbase (se 4 (by rfl) ⟨245475, by rfl⟩ : syracuseStep 2618405 = 490951) (by norm_num)
theorem B1963061 : Blo 515797 1963061 := bbase (se 5 (by rfl) ⟨92018, by rfl⟩ : syracuseStep 1963061 = 184037) (by norm_num)
theorem B1307765 : Blo 515797 1307765 := bbase (se 5 (by rfl) ⟨61301, by rfl⟩ : syracuseStep 1307765 = 122603) (by norm_num)
theorem B619861 : Blo 515797 619861 := bbase (se 13 (by rfl) ⟨113, by rfl⟩ : syracuseStep 619861 = 227) (by norm_num)
theorem B1963349 : Blo 515797 1963349 := bbase (se 13 (by rfl) ⟨359, by rfl⟩ : syracuseStep 1963349 = 719) (by norm_num)
theorem B554401 : Blo 515797 554401 := bbase (se 2 (by rfl) ⟨207900, by rfl⟩ : syracuseStep 554401 = 415801) (by norm_num)
theorem B1308109 : Blo 515797 1308109 := bbase (se 3 (by rfl) ⟨245270, by rfl⟩ : syracuseStep 1308109 = 490541) (by norm_num)
theorem B980437 : Blo 515797 980437 := bbase (se 7 (by rfl) ⟨11489, by rfl⟩ : syracuseStep 980437 = 22979) (by norm_num)
theorem B554473 : Blo 515797 554473 := bbase (se 2 (by rfl) ⟨207927, by rfl⟩ : syracuseStep 554473 = 415855) (by norm_num)
theorem B1308221 : Blo 515797 1308221 := bbase (se 3 (by rfl) ⟨245291, by rfl⟩ : syracuseStep 1308221 = 490583) (by norm_num)
theorem B980581 : Blo 515797 980581 := bbase (se 4 (by rfl) ⟨91929, by rfl⟩ : syracuseStep 980581 = 183859) (by norm_num)
theorem B2487941 : Blo 515797 2487941 := bbase (se 4 (by rfl) ⟨233244, by rfl⟩ : syracuseStep 2487941 = 466489) (by norm_num)
theorem B652961 : Blo 515797 652961 := bbase (se 2 (by rfl) ⟨244860, by rfl⟩ : syracuseStep 652961 = 489721) (by norm_num)
theorem B1242797 : Blo 515797 1242797 := bbase (se 3 (by rfl) ⟨233024, by rfl⟩ : syracuseStep 1242797 = 466049) (by norm_num)
theorem B653017 : Blo 515797 653017 := bbase (se 2 (by rfl) ⟨244881, by rfl⟩ : syracuseStep 653017 = 489763) (by norm_num)
theorem B1308413 : Blo 515797 1308413 := bbase (se 3 (by rfl) ⟨245327, by rfl⟩ : syracuseStep 1308413 = 490655) (by norm_num)
theorem B980741 : Blo 515797 980741 := bbase (se 4 (by rfl) ⟨91944, by rfl⟩ : syracuseStep 980741 = 183889) (by norm_num)
theorem B653113 : Blo 515797 653113 := bbase (se 2 (by rfl) ⟨244917, by rfl⟩ : syracuseStep 653113 = 489835) (by norm_num)
theorem B1046333 : Blo 515797 1046333 := bbase (se 3 (by rfl) ⟨196187, by rfl⟩ : syracuseStep 1046333 = 392375) (by norm_num)
theorem B554845 : Blo 515797 554845 := bbase (se 3 (by rfl) ⟨104033, by rfl⟩ : syracuseStep 554845 = 208067) (by norm_num)
theorem B980885 : Blo 515797 980885 := bbase (se 6 (by rfl) ⟨22989, by rfl⟩ : syracuseStep 980885 = 45979) (by norm_num)
theorem B653285 : Blo 515797 653285 := bbase (se 4 (by rfl) ⟨61245, by rfl⟩ : syracuseStep 653285 = 122491) (by norm_num)
theorem B653341 : Blo 515797 653341 := bbase (se 3 (by rfl) ⟨122501, by rfl⟩ : syracuseStep 653341 = 245003) (by norm_num)
theorem B1308757 : Blo 515797 1308757 := bbase (se 8 (by rfl) ⟨7668, by rfl⟩ : syracuseStep 1308757 = 15337) (by norm_num)
theorem B653437 : Blo 515797 653437 := bbase (se 3 (by rfl) ⟨122519, by rfl⟩ : syracuseStep 653437 = 245039) (by norm_num)
theorem B981173 : Blo 515797 981173 := bbase (se 5 (by rfl) ⟨45992, by rfl⟩ : syracuseStep 981173 = 91985) (by norm_num)
theorem B620741 : Blo 515797 620741 := bbase (se 4 (by rfl) ⟨58194, by rfl⟩ : syracuseStep 620741 = 116389) (by norm_num)
theorem B1308869 : Blo 515797 1308869 := bbase (se 4 (by rfl) ⟨122706, by rfl⟩ : syracuseStep 1308869 = 245413) (by norm_num)
theorem B653609 : Blo 515797 653609 := bbase (se 2 (by rfl) ⟨245103, by rfl⟩ : syracuseStep 653609 = 490207) (by norm_num)
theorem B2619701 : Blo 515797 2619701 := bbase (se 5 (by rfl) ⟨122798, by rfl⟩ : syracuseStep 2619701 = 245597) (by norm_num)
theorem B981325 : Blo 515797 981325 := bbase (se 3 (by rfl) ⟨183998, by rfl⟩ : syracuseStep 981325 = 367997) (by norm_num)
theorem B653665 : Blo 515797 653665 := bbase (se 2 (by rfl) ⟨245124, by rfl⟩ : syracuseStep 653665 = 490249) (by norm_num)
theorem B1309061 : Blo 515797 1309061 := bbase (se 4 (by rfl) ⟨122724, by rfl⟩ : syracuseStep 1309061 = 245449) (by norm_num)
theorem B1997237 : Blo 515797 1997237 := bbase (se 5 (by rfl) ⟨93620, by rfl⟩ : syracuseStep 1997237 = 187241) (by norm_num)
theorem B653761 : Blo 515797 653761 := bbase (se 2 (by rfl) ⟨245160, by rfl⟩ : syracuseStep 653761 = 490321) (by norm_num)
theorem B1964533 : Blo 515797 1964533 := bbase (se 5 (by rfl) ⟨92087, by rfl⟩ : syracuseStep 1964533 = 184175) (by norm_num)
theorem B621049 : Blo 515797 621049 := bbase (se 2 (by rfl) ⟨232893, by rfl⟩ : syracuseStep 621049 = 465787) (by norm_num)
theorem B653933 : Blo 515797 653933 := bbase (se 3 (by rfl) ⟨122612, by rfl⟩ : syracuseStep 653933 = 245225) (by norm_num)
theorem B981629 : Blo 515797 981629 := bbase (se 3 (by rfl) ⟨184055, by rfl⟩ : syracuseStep 981629 = 368111) (by norm_num)
theorem B588421 : Blo 515797 588421 := bbase (se 4 (by rfl) ⟨55164, by rfl⟩ : syracuseStep 588421 = 110329) (by norm_num)
theorem B1473173 : Blo 515797 1473173 := bbase (se 6 (by rfl) ⟨34527, by rfl⟩ : syracuseStep 1473173 = 69055) (by norm_num)
theorem B653989 : Blo 515797 653989 := bbase (se 4 (by rfl) ⟨61311, by rfl⟩ : syracuseStep 653989 = 122623) (by norm_num)
theorem B588457 : Blo 515797 588457 := bbase (se 2 (by rfl) ⟨220671, by rfl⟩ : syracuseStep 588457 = 441343) (by norm_num)
theorem B1309405 : Blo 515797 1309405 := bbase (se 3 (by rfl) ⟨245513, by rfl⟩ : syracuseStep 1309405 = 491027) (by norm_num)
theorem B654085 : Blo 515797 654085 := bbase (se 4 (by rfl) ⟨61320, by rfl⟩ : syracuseStep 654085 = 122641) (by norm_num)
theorem B1964837 : Blo 515797 1964837 := bbase (se 4 (by rfl) ⟨184203, by rfl⟩ : syracuseStep 1964837 = 368407) (by norm_num)
theorem B1309517 : Blo 515797 1309517 := bbase (se 3 (by rfl) ⟨245534, by rfl⟩ : syracuseStep 1309517 = 491069) (by norm_num)
theorem B621433 : Blo 515797 621433 := bbase (se 2 (by rfl) ⟨233037, by rfl⟩ : syracuseStep 621433 = 466075) (by norm_num)
theorem B621437 : Blo 515797 621437 := bbase (se 3 (by rfl) ⟨116519, by rfl⟩ : syracuseStep 621437 = 233039) (by norm_num)
theorem B654257 : Blo 515797 654257 := bbase (se 2 (by rfl) ⟨245346, by rfl⟩ : syracuseStep 654257 = 490693) (by norm_num)
theorem B2489285 : Blo 515797 2489285 := bbase (se 4 (by rfl) ⟨233370, by rfl⟩ : syracuseStep 2489285 = 466741) (by norm_num)
theorem B654313 : Blo 515797 654313 := bbase (se 2 (by rfl) ⟨245367, by rfl⟩ : syracuseStep 654313 = 490735) (by norm_num)
theorem B1309709 : Blo 515797 1309709 := bbase (se 3 (by rfl) ⟨245570, by rfl⟩ : syracuseStep 1309709 = 491141) (by norm_num)
theorem B523297 : Blo 515797 523297 := bbase (se 2 (by rfl) ⟨196236, by rfl⟩ : syracuseStep 523297 = 392473) (by norm_num)
theorem B654409 : Blo 515797 654409 := bbase (se 2 (by rfl) ⟨245403, by rfl⟩ : syracuseStep 654409 = 490807) (by norm_num)
theorem B3931253 : Blo 515797 3931253 := bbase (se 5 (by rfl) ⟨184277, by rfl⟩ : syracuseStep 3931253 = 368555) (by norm_num)
theorem B621697 : Blo 515797 621697 := bbase (se 2 (by rfl) ⟨233136, by rfl⟩ : syracuseStep 621697 = 466273) (by norm_num)
theorem B1998053 : Blo 515797 1998053 := bbase (se 4 (by rfl) ⟨187317, by rfl⟩ : syracuseStep 1998053 = 374635) (by norm_num)
theorem B654581 : Blo 515797 654581 := bbase (se 5 (by rfl) ⟨30683, by rfl⟩ : syracuseStep 654581 = 61367) (by norm_num)
theorem B621841 : Blo 515797 621841 := bbase (se 2 (by rfl) ⟨233190, by rfl⟩ : syracuseStep 621841 = 466381) (by norm_num)
theorem B654637 : Blo 515797 654637 := bbase (se 3 (by rfl) ⟨122744, by rfl⟩ : syracuseStep 654637 = 245489) (by norm_num)
theorem B1310053 : Blo 515797 1310053 := bbase (se 4 (by rfl) ⟨122817, by rfl⟩ : syracuseStep 1310053 = 245635) (by norm_num)
theorem B982381 : Blo 515797 982381 := bbase (se 3 (by rfl) ⟨184196, by rfl⟩ : syracuseStep 982381 = 368393) (by norm_num)
theorem B523633 : Blo 515797 523633 := bbase (se 2 (by rfl) ⟨196362, by rfl⟩ : syracuseStep 523633 = 392725) (by norm_num)
theorem B654733 : Blo 515797 654733 := bbase (se 3 (by rfl) ⟨122762, by rfl⟩ : syracuseStep 654733 = 245525) (by norm_num)
theorem B1244605 : Blo 515797 1244605 := bbase (se 3 (by rfl) ⟨233363, by rfl⟩ : syracuseStep 1244605 = 466727) (by norm_num)
theorem B1310165 : Blo 515797 1310165 := bbase (se 7 (by rfl) ⟨15353, by rfl⟩ : syracuseStep 1310165 = 30707) (by norm_num)
theorem B982525 : Blo 515797 982525 := bbase (se 3 (by rfl) ⟨184223, by rfl⟩ : syracuseStep 982525 = 368447) (by norm_num)
theorem B654905 : Blo 515797 654905 := bbase (se 2 (by rfl) ⟨245589, by rfl⟩ : syracuseStep 654905 = 491179) (by norm_num)
theorem B2620997 : Blo 515797 2620997 := bbase (se 4 (by rfl) ⟨245718, by rfl⟩ : syracuseStep 2620997 = 491437) (by norm_num)
theorem B654961 : Blo 515797 654961 := bbase (se 2 (by rfl) ⟨245610, by rfl⟩ : syracuseStep 654961 = 491221) (by norm_num)
theorem B1638005 : Blo 515797 1638005 := bbase (se 5 (by rfl) ⟨76781, by rfl⟩ : syracuseStep 1638005 = 153563) (by norm_num)
theorem B523913 : Blo 515797 523913 := bbase (se 2 (by rfl) ⟨196467, by rfl⟩ : syracuseStep 523913 = 392935) (by norm_num)
theorem B1310357 : Blo 515797 1310357 := bbase (se 6 (by rfl) ⟨30711, by rfl⟩ : syracuseStep 1310357 = 61423) (by norm_num)
theorem B982685 : Blo 515797 982685 := bbase (se 3 (by rfl) ⟨184253, by rfl⟩ : syracuseStep 982685 = 368507) (by norm_num)
theorem B523945 : Blo 515797 523945 := bbase (se 2 (by rfl) ⟨196479, by rfl⟩ : syracuseStep 523945 = 392959) (by norm_num)
theorem B655057 : Blo 515797 655057 := bbase (se 2 (by rfl) ⟨245646, by rfl⟩ : syracuseStep 655057 = 491293) (by norm_num)
theorem B851717 : Blo 515797 851717 := bbase (se 4 (by rfl) ⟨79848, by rfl⟩ : syracuseStep 851717 = 159697) (by norm_num)
theorem B982829 : Blo 515797 982829 := bbase (se 3 (by rfl) ⟨184280, by rfl⟩ : syracuseStep 982829 = 368561) (by norm_num)
theorem B1474357 : Blo 515797 1474357 := bbase (se 5 (by rfl) ⟨69110, by rfl⟩ : syracuseStep 1474357 = 138221) (by norm_num)
theorem B655229 : Blo 515797 655229 := bbase (se 3 (by rfl) ⟨122855, by rfl⟩ : syracuseStep 655229 = 245711) (by norm_num)
theorem B655285 : Blo 515797 655285 := bbase (se 5 (by rfl) ⟨30716, by rfl⟩ : syracuseStep 655285 = 61433) (by norm_num)
theorem B1245125 : Blo 515797 1245125 := bbase (se 4 (by rfl) ⟨116730, by rfl⟩ : syracuseStep 1245125 = 233461) (by norm_num)
theorem B1474517 : Blo 515797 1474517 := bbase (se 7 (by rfl) ⟨17279, by rfl⟩ : syracuseStep 1474517 = 34559) (by norm_num)
theorem B1310701 : Blo 515797 1310701 := bbase (se 3 (by rfl) ⟨245756, by rfl⟩ : syracuseStep 1310701 = 491513) (by norm_num)
theorem B2949169 : Blo 515797 2949169 := bstep (se 2 (by rfl) ⟨1105938, by rfl⟩ : syracuseStep 2949169 = 2211877) B2211877
theorem B983171 : Blo 515797 983171 := bstep (se 1 (by rfl) ⟨737378, by rfl⟩ : syracuseStep 983171 = 1474757) B1474757
theorem B524435 : Blo 515797 524435 := bstep (se 1 (by rfl) ⟨393326, by rfl⟩ : syracuseStep 524435 = 786653) B786653
theorem B2621645 : Blo 515797 2621645 := bstep (se 3 (by rfl) ⟨491558, by rfl⟩ : syracuseStep 2621645 = 983117) B983117
theorem B1311025 : Blo 515797 1311025 := bstep (se 2 (by rfl) ⟨491634, by rfl⟩ : syracuseStep 1311025 = 983269) B983269
theorem B3309923 : Blo 515797 3309923 := bstep (se 1 (by rfl) ⟨2482442, by rfl⟩ : syracuseStep 3309923 = 4964885) B4964885
theorem B655715 : Blo 515797 655715 := bstep (se 1 (by rfl) ⟨491786, by rfl⟩ : syracuseStep 655715 = 983573) B983573
theorem B1966477 : Blo 515797 1966477 := bstep (se 3 (by rfl) ⟨368714, by rfl⟩ : syracuseStep 1966477 = 737429) B737429
theorem B1180145 : Blo 515797 1180145 := bstep (se 2 (by rfl) ⟨442554, by rfl⟩ : syracuseStep 1180145 = 885109) B885109
theorem B1311299 : Blo 515797 1311299 := bstep (se 1 (by rfl) ⟨983474, by rfl⟩ : syracuseStep 1311299 = 1966949) B1966949
theorem B1311491 : Blo 515797 1311491 := bstep (se 1 (by rfl) ⟨983618, by rfl⟩ : syracuseStep 1311491 = 1967237) B1967237
theorem B1868579 : Blo 515797 1868579 := bstep (se 1 (by rfl) ⟨1401434, by rfl⟩ : syracuseStep 1868579 = 2802869) B2802869
theorem B1475405 : Blo 515797 1475405 := bstep (se 3 (by rfl) ⟨276638, by rfl⟩ : syracuseStep 1475405 = 553277) B553277
theorem B1475587 : Blo 515797 1475587 := bstep (se 1 (by rfl) ⟨1106690, by rfl⟩ : syracuseStep 1475587 = 2213381) B2213381
theorem B3933197 : Blo 515797 3933197 := bstep (se 3 (by rfl) ⟨737474, by rfl⟩ : syracuseStep 3933197 = 1474949) B1474949
theorem B656419 : Blo 515797 656419 := bstep (se 1 (by rfl) ⟨492314, by rfl⟩ : syracuseStep 656419 = 984629) B984629
theorem B1475633 : Blo 515797 1475633 := bstep (se 2 (by rfl) ⟨553362, by rfl⟩ : syracuseStep 1475633 = 1106725) B1106725
theorem B1573987 : Blo 515797 1573987 := bstep (se 1 (by rfl) ⟨1180490, by rfl⟩ : syracuseStep 1573987 = 2360981) B2360981
theorem B656515 : Blo 515797 656515 := bstep (se 1 (by rfl) ⟨492386, by rfl⟩ : syracuseStep 656515 = 984773) B984773
theorem B3540131 : Blo 515797 3540131 := bstep (se 1 (by rfl) ⟨2655098, by rfl⟩ : syracuseStep 3540131 = 5310197) B5310197
theorem B1967267 : Blo 515797 1967267 := bstep (se 1 (by rfl) ⟨1475450, by rfl⟩ : syracuseStep 1967267 = 2950901) B2950901
theorem B984241 : Blo 515797 984241 := bstep (se 2 (by rfl) ⟨369090, by rfl⟩ : syracuseStep 984241 = 738181) B738181
theorem B1574083 : Blo 515797 1574083 := bstep (se 1 (by rfl) ⟨1180562, by rfl⟩ : syracuseStep 1574083 = 2361125) B2361125
theorem B1246403 : Blo 515797 1246403 := bstep (se 1 (by rfl) ⟨934802, by rfl⟩ : syracuseStep 1246403 = 1869605) B1869605
theorem B10650851 : Blo 515797 10650851 := bstep (se 1 (by rfl) ⟨7988138, by rfl⟩ : syracuseStep 10650851 = 15976277) B15976277
theorem B2950627 : Blo 515797 2950627 := bstep (se 1 (by rfl) ⟨2212970, by rfl⟩ : syracuseStep 2950627 = 4425941) B4425941
theorem B1050097 : Blo 515797 1050097 := bstep (se 2 (by rfl) ⟨393786, by rfl⟩ : syracuseStep 1050097 = 787573) B787573
theorem B657011 : Blo 515797 657011 := bstep (se 1 (by rfl) ⟨492758, by rfl⟩ : syracuseStep 657011 = 985517) B985517
theorem B1312433 : Blo 515797 1312433 := bstep (se 2 (by rfl) ⟨492162, by rfl⟩ : syracuseStep 1312433 = 984325) B984325
theorem B1312483 : Blo 515797 1312483 := bstep (se 1 (by rfl) ⟨984362, by rfl⟩ : syracuseStep 1312483 = 1968725) B1968725
theorem B1967921 : Blo 515797 1967921 := bstep (se 2 (by rfl) ⟨737970, by rfl⟩ : syracuseStep 1967921 = 1475941) B1475941
theorem B1312625 : Blo 515797 1312625 := bstep (se 2 (by rfl) ⟨492234, by rfl⟩ : syracuseStep 1312625 = 984469) B984469
theorem B2951153 : Blo 515797 2951153 := bstep (se 2 (by rfl) ⟨1106682, by rfl⟩ : syracuseStep 2951153 = 2213365) B2213365
theorem B1575085 : Blo 515797 1575085 := bstep (se 3 (by rfl) ⟨295328, by rfl⟩ : syracuseStep 1575085 = 590657) B590657
theorem B985297 : Blo 515797 985297 := bstep (se 2 (by rfl) ⟨369486, by rfl⟩ : syracuseStep 985297 = 738973) B738973
theorem B1181969 : Blo 515797 1181969 := bstep (se 2 (by rfl) ⟨443238, by rfl⟩ : syracuseStep 1181969 = 886477) B886477
theorem B657715 : Blo 515797 657715 := bstep (se 1 (by rfl) ⟨493286, by rfl⟩ : syracuseStep 657715 = 986573) B986573
theorem B1870193 : Blo 515797 1870193 := bstep (se 2 (by rfl) ⟨701322, by rfl⟩ : syracuseStep 1870193 = 1402645) B1402645
theorem B1247633 : Blo 515797 1247633 := bstep (se 2 (by rfl) ⟨467862, by rfl⟩ : syracuseStep 1247633 = 935725) B935725
theorem B657811 : Blo 515797 657811 := bstep (se 1 (by rfl) ⟨493358, by rfl⟩ : syracuseStep 657811 = 986717) B986717
theorem B1477091 : Blo 515797 1477091 := bstep (se 1 (by rfl) ⟨1107818, by rfl⟩ : syracuseStep 1477091 = 2215637) B2215637
theorem B985699 : Blo 515797 985699 := bstep (se 1 (by rfl) ⟨739274, by rfl⟩ : syracuseStep 985699 = 1478549) B1478549
theorem B985745 : Blo 515797 985745 := bstep (se 2 (by rfl) ⟨369654, by rfl⟩ : syracuseStep 985745 = 739309) B739309
theorem B1313617 : Blo 515797 1313617 := bstep (se 2 (by rfl) ⟨492606, by rfl⟩ : syracuseStep 1313617 = 985213) B985213
theorem B2493283 : Blo 515797 2493283 := bstep (se 1 (by rfl) ⟨1869962, by rfl⟩ : syracuseStep 2493283 = 3739925) B3739925
theorem B986033 : Blo 515797 986033 := bstep (se 2 (by rfl) ⟨369762, by rfl⟩ : syracuseStep 986033 = 739525) B739525
theorem B2624561 : Blo 515797 2624561 := bstep (se 2 (by rfl) ⟨984210, by rfl⟩ : syracuseStep 2624561 = 1968421) B1968421
theorem B1313891 : Blo 515797 1313891 := bstep (se 1 (by rfl) ⟨985418, by rfl⟩ : syracuseStep 1313891 = 1970837) B1970837
theorem B1969379 : Blo 515797 1969379 := bstep (se 1 (by rfl) ⟨1477034, by rfl⟩ : syracuseStep 1969379 = 2954069) B2954069
theorem B1969393 : Blo 515797 1969393 := bstep (se 2 (by rfl) ⟨738522, by rfl⟩ : syracuseStep 1969393 = 1477045) B1477045
theorem B888049 : Blo 515797 888049 := bstep (se 2 (by rfl) ⟨333018, by rfl⟩ : syracuseStep 888049 = 666037) B666037
theorem B1314083 : Blo 515797 1314083 := bstep (se 1 (by rfl) ⟨985562, by rfl⟩ : syracuseStep 1314083 = 1971125) B1971125
theorem B1117489 : Blo 515797 1117489 := bstep (se 2 (by rfl) ⟨419058, by rfl⟩ : syracuseStep 1117489 = 838117) B838117
theorem B789841 : Blo 515797 789841 := bstep (se 2 (by rfl) ⟨296190, by rfl⟩ : syracuseStep 789841 = 592381) B592381
theorem B2952611 : Blo 515797 2952611 := bstep (se 1 (by rfl) ⟨2214458, by rfl⟩ : syracuseStep 2952611 = 4428917) B4428917
theorem B2788835 : Blo 515797 2788835 := bstep (se 1 (by rfl) ⟨2091626, by rfl⟩ : syracuseStep 2788835 = 4183253) B4183253
theorem B1052195 : Blo 515797 1052195 := bstep (se 1 (by rfl) ⟨789146, by rfl⟩ : syracuseStep 1052195 = 1578293) B1578293
theorem B986755 : Blo 515797 986755 := bstep (se 1 (by rfl) ⟨740066, by rfl⟩ : syracuseStep 986755 = 1480133) B1480133
theorem B13471373 : Blo 515797 13471373 := bstep (se 3 (by rfl) ⟨2525882, by rfl⟩ : syracuseStep 13471373 = 5051765) B5051765
theorem B1478321 : Blo 515797 1478321 := bstep (se 2 (by rfl) ⟨554370, by rfl⟩ : syracuseStep 1478321 = 1108741) B1108741
theorem B3936113 : Blo 515797 3936113 := bstep (se 2 (by rfl) ⟨1476042, by rfl⟩ : syracuseStep 3936113 = 2952085) B2952085
theorem B1052561 : Blo 515797 1052561 := bstep (se 2 (by rfl) ⟨394710, by rfl⟩ : syracuseStep 1052561 = 789421) B789421
theorem B2494513 : Blo 515797 2494513 := bstep (se 2 (by rfl) ⟨935442, by rfl⟩ : syracuseStep 2494513 = 1870885) B1870885
theorem B1315025 : Blo 515797 1315025 := bstep (se 2 (by rfl) ⟨493134, by rfl⟩ : syracuseStep 1315025 = 986269) B986269
theorem B1315075 : Blo 515797 1315075 := bstep (se 1 (by rfl) ⟨986306, by rfl⟩ : syracuseStep 1315075 = 1972613) B1972613
theorem B1315217 : Blo 515797 1315217 := bstep (se 2 (by rfl) ⟨493206, by rfl⟩ : syracuseStep 1315217 = 986413) B986413
theorem B1741229 : Blo 515797 1741229 := bstep (se 3 (by rfl) ⟨326480, by rfl⟩ : syracuseStep 1741229 = 652961) B652961
theorem B4198853 : Blo 515797 4198853 := bstep (se 4 (by rfl) ⟨393642, by rfl⟩ : syracuseStep 4198853 = 787285) B787285
theorem B3314125 : Blo 515797 3314125 := bstep (se 3 (by rfl) ⟨621398, by rfl⟩ : syracuseStep 3314125 = 1242797) B1242797
theorem B1741283 : Blo 515797 1741283 := bstep (se 1 (by rfl) ⟨1305962, by rfl⟩ : syracuseStep 1741283 = 2611925) B2611925
theorem B2626019 : Blo 515797 2626019 := bstep (se 1 (by rfl) ⟨1969514, by rfl⟩ : syracuseStep 2626019 = 3939029) B3939029
theorem B1970851 : Blo 515797 1970851 := bstep (se 1 (by rfl) ⟨1478138, by rfl⟩ : syracuseStep 1970851 = 2956277) B2956277
theorem B1741553 : Blo 515797 1741553 := bstep (se 2 (by rfl) ⟨653082, by rfl⟩ : syracuseStep 1741553 = 1306165) B1306165
theorem B1479779 : Blo 515797 1479779 := bstep (se 1 (by rfl) ⟨1109834, by rfl⟩ : syracuseStep 1479779 = 2219669) B2219669
theorem B2954501 : Blo 515797 2954501 := bstep (se 4 (by rfl) ⟨276984, by rfl⟩ : syracuseStep 2954501 = 553969) B553969
theorem B1742093 : Blo 515797 1742093 := bstep (se 3 (by rfl) ⟨326642, by rfl⟩ : syracuseStep 1742093 = 653285) B653285
theorem B2626829 : Blo 515797 2626829 := bstep (se 3 (by rfl) ⟨492530, by rfl⟩ : syracuseStep 2626829 = 985061) B985061
theorem B1119505 : Blo 515797 1119505 := bstep (se 2 (by rfl) ⟨419814, by rfl⟩ : syracuseStep 1119505 = 839629) B839629
theorem B1742147 : Blo 515797 1742147 := bstep (se 1 (by rfl) ⟨1306610, by rfl⟩ : syracuseStep 1742147 = 2613221) B2613221
theorem B2496035 : Blo 515797 2496035 := bstep (se 1 (by rfl) ⟨1872026, by rfl⟩ : syracuseStep 2496035 = 3744053) B3744053
theorem B1742417 : Blo 515797 1742417 := bstep (se 2 (by rfl) ⟨653406, by rfl⟩ : syracuseStep 1742417 = 1306813) B1306813
theorem B1775213 : Blo 515797 1775213 := bstep (se 3 (by rfl) ⟨332852, by rfl⟩ : syracuseStep 1775213 = 665705) B665705
theorem B530275 : Blo 515797 530275 := bstep (se 1 (by rfl) ⟨397706, by rfl⟩ : syracuseStep 530275 = 795413) B795413
theorem B1742957 : Blo 515797 1742957 := bstep (se 3 (by rfl) ⟨326804, by rfl⟩ : syracuseStep 1742957 = 653609) B653609
theorem B5314673 : Blo 515797 5314673 := bstep (se 2 (by rfl) ⟨1993002, by rfl⟩ : syracuseStep 5314673 = 3986005) B3986005
theorem B1743011 : Blo 515797 1743011 := bstep (se 1 (by rfl) ⟨1307258, by rfl⟩ : syracuseStep 1743011 = 2614517) B2614517
theorem B1579267 : Blo 515797 1579267 := bstep (se 1 (by rfl) ⟨1184450, by rfl⟩ : syracuseStep 1579267 = 2368901) B2368901
theorem B1743281 : Blo 515797 1743281 := bstep (se 2 (by rfl) ⟨653730, by rfl⟩ : syracuseStep 1743281 = 1307461) B1307461
theorem B3578309 : Blo 515797 3578309 := bstep (se 4 (by rfl) ⟨335466, by rfl⟩ : syracuseStep 3578309 = 670933) B670933
theorem B1579619 : Blo 515797 1579619 := bstep (se 1 (by rfl) ⟨1184714, by rfl⟩ : syracuseStep 1579619 = 2369429) B2369429
theorem B1973069 : Blo 515797 1973069 := bstep (se 3 (by rfl) ⟨369950, by rfl⟩ : syracuseStep 1973069 = 739901) B739901
theorem B1743821 : Blo 515797 1743821 := bstep (se 3 (by rfl) ⟨326966, by rfl⟩ : syracuseStep 1743821 = 653933) B653933
theorem B1743875 : Blo 515797 1743875 := bstep (se 1 (by rfl) ⟨1307906, by rfl⟩ : syracuseStep 1743875 = 2615813) B2615813
theorem B826481 : Blo 515797 826481 := bstep (se 2 (by rfl) ⟨309930, by rfl⟩ : syracuseStep 826481 = 619861) B619861
theorem B1744145 : Blo 515797 1744145 := bstep (se 2 (by rfl) ⟨654054, by rfl⟩ : syracuseStep 1744145 = 1308109) B1308109
theorem B1776977 : Blo 515797 1776977 := bstep (se 2 (by rfl) ⟨666366, by rfl⟩ : syracuseStep 1776977 = 1332733) B1332733
theorem B1744685 : Blo 515797 1744685 := bstep (se 3 (by rfl) ⟨327128, by rfl⟩ : syracuseStep 1744685 = 654257) B654257
theorem B1744739 : Blo 515797 1744739 := bstep (se 1 (by rfl) ⟨1308554, by rfl⟩ : syracuseStep 1744739 = 2617109) B2617109
theorem B5906357 : Blo 515797 5906357 := bstep (se 5 (by rfl) ⟨276860, by rfl⟩ : syracuseStep 5906357 = 553721) B553721
theorem B827347 : Blo 515797 827347 := bstep (se 1 (by rfl) ⟨620510, by rfl⟩ : syracuseStep 827347 = 1241021) B1241021
theorem B598115 : Blo 515797 598115 := bstep (se 1 (by rfl) ⟨448586, by rfl⟩ : syracuseStep 598115 = 897173) B897173
theorem B1745009 : Blo 515797 1745009 := bstep (se 2 (by rfl) ⟨654378, by rfl⟩ : syracuseStep 1745009 = 1308757) B1308757
theorem B2629745 : Blo 515797 2629745 := bstep (se 2 (by rfl) ⟨986154, by rfl⟩ : syracuseStep 2629745 = 1972309) B1972309
theorem B828019 : Blo 515797 828019 := bstep (se 1 (by rfl) ⟨621014, by rfl⟩ : syracuseStep 828019 = 1242029) B1242029
theorem B1745549 : Blo 515797 1745549 := bstep (se 3 (by rfl) ⟨327290, by rfl⟩ : syracuseStep 1745549 = 654581) B654581
theorem B828065 : Blo 515797 828065 := bstep (se 2 (by rfl) ⟨310524, by rfl⟩ : syracuseStep 828065 = 621049) B621049
theorem B1745603 : Blo 515797 1745603 := bstep (se 1 (by rfl) ⟨1309202, by rfl⟩ : syracuseStep 1745603 = 2618405) B2618405
theorem B1745873 : Blo 515797 1745873 := bstep (se 2 (by rfl) ⟨654702, by rfl⟩ : syracuseStep 1745873 = 1309405) B1309405
theorem B664723 : Blo 515797 664723 := bstep (se 1 (by rfl) ⟨498542, by rfl⟩ : syracuseStep 664723 = 997085) B997085
theorem B828577 : Blo 515797 828577 := bstep (se 2 (by rfl) ⟨310716, by rfl⟩ : syracuseStep 828577 = 621433) B621433
theorem B697555 : Blo 515797 697555 := bstep (se 1 (by rfl) ⟨523166, by rfl⟩ : syracuseStep 697555 = 1046333) B1046333
theorem B2204941 : Blo 515797 2204941 := bstep (se 3 (by rfl) ⟨413426, by rfl⟩ : syracuseStep 2204941 = 826853) B826853
theorem B6628661 : Blo 515797 6628661 := bstep (se 5 (by rfl) ⟨310718, by rfl⟩ : syracuseStep 6628661 = 621437) B621437
theorem B697729 : Blo 515797 697729 := bstep (se 2 (by rfl) ⟨261648, by rfl⟩ : syracuseStep 697729 = 523297) B523297
theorem B1746413 : Blo 515797 1746413 := bstep (se 3 (by rfl) ⟨327452, by rfl⟩ : syracuseStep 1746413 = 654905) B654905
theorem B828929 : Blo 515797 828929 := bstep (se 2 (by rfl) ⟨310848, by rfl⟩ : syracuseStep 828929 = 621697) B621697
theorem B2991629 : Blo 515797 2991629 := bstep (se 3 (by rfl) ⟨560930, by rfl⟩ : syracuseStep 2991629 = 1121861) B1121861
theorem B1746467 : Blo 515797 1746467 := bstep (se 1 (by rfl) ⟨1309850, by rfl⟩ : syracuseStep 1746467 = 2619701) B2619701
theorem B2631203 : Blo 515797 2631203 := bstep (se 1 (by rfl) ⟨1973402, by rfl⟩ : syracuseStep 2631203 = 3946805) B3946805
theorem B4368013 : Blo 515797 4368013 := bstep (se 3 (by rfl) ⟨819002, by rfl⟩ : syracuseStep 4368013 = 1638005) B1638005
theorem B829121 : Blo 515797 829121 := bstep (se 2 (by rfl) ⟨310920, by rfl⟩ : syracuseStep 829121 = 621841) B621841
theorem B1746737 : Blo 515797 1746737 := bstep (se 2 (by rfl) ⟨655026, by rfl⟩ : syracuseStep 1746737 = 1310053) B1310053
theorem B698177 : Blo 515797 698177 := bstep (se 2 (by rfl) ⟨261816, by rfl⟩ : syracuseStep 698177 = 523633) B523633
theorem B2566129 : Blo 515797 2566129 := bstep (se 2 (by rfl) ⟨962298, by rfl⟩ : syracuseStep 2566129 = 1924597) B1924597
theorem B698593 : Blo 515797 698593 := bstep (se 2 (by rfl) ⟨261972, by rfl⟩ : syracuseStep 698593 = 523945) B523945
theorem B18229475 : Blo 515797 18229475 := bstep (se 1 (by rfl) ⟨13672106, by rfl⟩ : syracuseStep 18229475 = 27344213) B27344213
theorem B1747277 : Blo 515797 1747277 := bstep (se 3 (by rfl) ⟨327614, by rfl⟩ : syracuseStep 1747277 = 655229) B655229
theorem B1747331 : Blo 515797 1747331 := bstep (se 1 (by rfl) ⟨1310498, by rfl⟩ : syracuseStep 1747331 = 2620997) B2620997
theorem B567811 : Blo 515797 567811 := bstep (se 1 (by rfl) ⟨425858, by rfl⟩ : syracuseStep 567811 = 851717) B851717
theorem B830083 : Blo 515797 830083 := bstep (se 1 (by rfl) ⟨622562, by rfl⟩ : syracuseStep 830083 = 1245125) B1245125
theorem B1747601 : Blo 515797 1747601 := bstep (se 2 (by rfl) ⟨655350, by rfl⟩ : syracuseStep 1747601 = 1310701) B1310701
theorem B830339 : Blo 515797 830339 := bstep (se 1 (by rfl) ⟨622754, by rfl⟩ : syracuseStep 830339 = 1245509) B1245509
theorem B2370467 : Blo 515797 2370467 := bstep (se 1 (by rfl) ⟨1777850, by rfl⟩ : syracuseStep 2370467 = 3555701) B3555701
theorem B2960333 : Blo 515797 2960333 := bstep (se 3 (by rfl) ⟨555062, by rfl⟩ : syracuseStep 2960333 = 1110125) B1110125
theorem B3320945 : Blo 515797 3320945 := bstep (se 2 (by rfl) ⟨1245354, by rfl⟩ : syracuseStep 3320945 = 2490709) B2490709
theorem B12102797 : Blo 515797 12102797 := bstep (se 3 (by rfl) ⟨2269274, by rfl⟩ : syracuseStep 12102797 = 4538549) B4538549
theorem B1748141 : Blo 515797 1748141 := bstep (se 3 (by rfl) ⟨327776, by rfl⟩ : syracuseStep 1748141 = 655553) B655553
theorem B1748195 : Blo 515797 1748195 := bstep (se 1 (by rfl) ⟨1311146, by rfl⟩ : syracuseStep 1748195 = 2622293) B2622293
theorem B1748465 : Blo 515797 1748465 := bstep (se 2 (by rfl) ⟨655674, by rfl⟩ : syracuseStep 1748465 = 1311349) B1311349
theorem B699907 : Blo 515797 699907 := bstep (se 1 (by rfl) ⟨524930, by rfl⟩ : syracuseStep 699907 = 1049861) B1049861
theorem B2665997 : Blo 515797 2665997 := bstep (se 3 (by rfl) ⟨499874, by rfl⟩ : syracuseStep 2665997 = 999749) B999749
theorem B831043 : Blo 515797 831043 := bstep (se 1 (by rfl) ⟨623282, by rfl⟩ : syracuseStep 831043 = 1246565) B1246565
theorem B3321485 : Blo 515797 3321485 := bstep (se 3 (by rfl) ⟨622778, by rfl⟩ : syracuseStep 3321485 = 1245557) B1245557
theorem B1060547 : Blo 515797 1060547 := bstep (se 1 (by rfl) ⟨795410, by rfl⟩ : syracuseStep 1060547 = 1590821) B1590821
theorem B831313 : Blo 515797 831313 := bstep (se 2 (by rfl) ⟨311742, by rfl⟩ : syracuseStep 831313 = 623485) B623485
theorem B4730723 : Blo 515797 4730723 := bstep (se 1 (by rfl) ⟨3548042, by rfl⟩ : syracuseStep 4730723 = 7096085) B7096085
theorem B831377 : Blo 515797 831377 := bstep (se 2 (by rfl) ⟨311766, by rfl⟩ : syracuseStep 831377 = 623533) B623533
theorem B1749005 : Blo 515797 1749005 := bstep (se 3 (by rfl) ⟨327938, by rfl⟩ : syracuseStep 1749005 = 655877) B655877
theorem B1749059 : Blo 515797 1749059 := bstep (se 1 (by rfl) ⟨1311794, by rfl⟩ : syracuseStep 1749059 = 2623589) B2623589
theorem B1749329 : Blo 515797 1749329 := bstep (se 2 (by rfl) ⟨655998, by rfl⟩ : syracuseStep 1749329 = 1311997) B1311997
theorem B700913 : Blo 515797 700913 := bstep (se 2 (by rfl) ⟨262842, by rfl⟩ : syracuseStep 700913 = 525685) B525685
theorem B1749869 : Blo 515797 1749869 := bstep (se 3 (by rfl) ⟨328100, by rfl⟩ : syracuseStep 1749869 = 656201) B656201
theorem B3355505 : Blo 515797 3355505 := bstep (se 2 (by rfl) ⟨1258314, by rfl⟩ : syracuseStep 3355505 = 2516629) B2516629
theorem B1749923 : Blo 515797 1749923 := bstep (se 1 (by rfl) ⟨1312442, by rfl⟩ : syracuseStep 1749923 = 2624885) B2624885
theorem B1750193 : Blo 515797 1750193 := bstep (se 2 (by rfl) ⟨656322, by rfl⟩ : syracuseStep 1750193 = 1312645) B1312645
theorem B734513 : Blo 515797 734513 := bstep (se 2 (by rfl) ⟨275442, by rfl⟩ : syracuseStep 734513 = 550885) B550885
theorem B734627 : Blo 515797 734627 := bstep (se 1 (by rfl) ⟨550970, by rfl⟩ : syracuseStep 734627 = 1101941) B1101941
theorem B1160657 : Blo 515797 1160657 := bstep (se 2 (by rfl) ⟨435246, by rfl⟩ : syracuseStep 1160657 = 870493) B870493
theorem B1160675 : Blo 515797 1160675 := bstep (se 1 (by rfl) ⟨870506, by rfl⟩ : syracuseStep 1160675 = 1741013) B1741013
theorem B5682659 : Blo 515797 5682659 := bstep (se 1 (by rfl) ⟨4261994, by rfl⟩ : syracuseStep 5682659 = 8523989) B8523989
theorem B2209265 : Blo 515797 2209265 := bstep (se 2 (by rfl) ⟨828474, by rfl⟩ : syracuseStep 2209265 = 1656949) B1656949
theorem B734707 : Blo 515797 734707 := bstep (se 1 (by rfl) ⟨551030, by rfl⟩ : syracuseStep 734707 = 1102061) B1102061
theorem B2209315 : Blo 515797 2209315 := bstep (se 1 (by rfl) ⟨1656986, by rfl⟩ : syracuseStep 2209315 = 3313973) B3313973
theorem B1750733 : Blo 515797 1750733 := bstep (se 3 (by rfl) ⟨328262, by rfl⟩ : syracuseStep 1750733 = 656525) B656525
theorem B931537 : Blo 515797 931537 := bstep (se 2 (by rfl) ⟨349326, by rfl⟩ : syracuseStep 931537 = 698653) B698653
theorem B1160945 : Blo 515797 1160945 := bstep (se 2 (by rfl) ⟨435354, by rfl⟩ : syracuseStep 1160945 = 870709) B870709
theorem B1160963 : Blo 515797 1160963 := bstep (se 1 (by rfl) ⟨870722, by rfl⟩ : syracuseStep 1160963 = 1741445) B1741445
theorem B1750787 : Blo 515797 1750787 := bstep (se 1 (by rfl) ⟨1313090, by rfl⟩ : syracuseStep 1750787 = 2626181) B2626181
theorem B1455889 : Blo 515797 1455889 := bstep (se 2 (by rfl) ⟨545958, by rfl⟩ : syracuseStep 1455889 = 1091917) B1091917
theorem B997265 : Blo 515797 997265 := bstep (se 2 (by rfl) ⟨373974, by rfl⟩ : syracuseStep 997265 = 747949) B747949
theorem B1161233 : Blo 515797 1161233 := bstep (se 2 (by rfl) ⟨435462, by rfl⟩ : syracuseStep 1161233 = 870925) B870925
theorem B1751057 : Blo 515797 1751057 := bstep (se 2 (by rfl) ⟨656646, by rfl⟩ : syracuseStep 1751057 = 1313293) B1313293
theorem B735265 : Blo 515797 735265 := bstep (se 2 (by rfl) ⟨275724, by rfl⟩ : syracuseStep 735265 = 551449) B551449
theorem B1161251 : Blo 515797 1161251 := bstep (se 1 (by rfl) ⟨870938, by rfl⟩ : syracuseStep 1161251 = 1741877) B1741877
theorem B1652849 : Blo 515797 1652849 := bstep (se 2 (by rfl) ⟨619818, by rfl⟩ : syracuseStep 1652849 = 1239637) B1239637
theorem B3356849 : Blo 515797 3356849 := bstep (se 2 (by rfl) ⟨1258818, by rfl⟩ : syracuseStep 3356849 = 2517637) B2517637
theorem B4962545 : Blo 515797 4962545 := bstep (se 2 (by rfl) ⟨1860954, by rfl⟩ : syracuseStep 4962545 = 3721909) B3721909
theorem B1161521 : Blo 515797 1161521 := bstep (se 2 (by rfl) ⟨435570, by rfl⟩ : syracuseStep 1161521 = 871141) B871141
theorem B1161539 : Blo 515797 1161539 := bstep (se 1 (by rfl) ⟨871154, by rfl⟩ : syracuseStep 1161539 = 1742309) B1742309
theorem B1325425 : Blo 515797 1325425 := bstep (se 2 (by rfl) ⟨497034, by rfl⟩ : syracuseStep 1325425 = 994069) B994069
theorem B932323 : Blo 515797 932323 := bstep (se 1 (by rfl) ⟨699242, by rfl⟩ : syracuseStep 932323 = 1398485) B1398485
theorem B1751597 : Blo 515797 1751597 := bstep (se 3 (by rfl) ⟨328424, by rfl⟩ : syracuseStep 1751597 = 656849) B656849
theorem B1161809 : Blo 515797 1161809 := bstep (se 2 (by rfl) ⟨435678, by rfl⟩ : syracuseStep 1161809 = 871357) B871357
theorem B1161827 : Blo 515797 1161827 := bstep (se 1 (by rfl) ⟨871370, by rfl⟩ : syracuseStep 1161827 = 1742741) B1742741
theorem B1751651 : Blo 515797 1751651 := bstep (se 1 (by rfl) ⟨1313738, by rfl⟩ : syracuseStep 1751651 = 2627477) B2627477
theorem B1653475 : Blo 515797 1653475 := bstep (se 1 (by rfl) ⟨1240106, by rfl⟩ : syracuseStep 1653475 = 2480213) B2480213
theorem B735971 : Blo 515797 735971 := bstep (se 1 (by rfl) ⟨551978, by rfl⟩ : syracuseStep 735971 = 1103957) B1103957
theorem B3324685 : Blo 515797 3324685 := bstep (se 3 (by rfl) ⟨623378, by rfl⟩ : syracuseStep 3324685 = 1246757) B1246757
theorem B1260323 : Blo 515797 1260323 := bstep (se 1 (by rfl) ⟨945242, by rfl⟩ : syracuseStep 1260323 = 1890485) B1890485
theorem B1162097 : Blo 515797 1162097 := bstep (se 2 (by rfl) ⟨435786, by rfl⟩ : syracuseStep 1162097 = 871573) B871573
theorem B1751921 : Blo 515797 1751921 := bstep (se 2 (by rfl) ⟨656970, by rfl⟩ : syracuseStep 1751921 = 1313941) B1313941
theorem B1162115 : Blo 515797 1162115 := bstep (se 1 (by rfl) ⟨871586, by rfl⟩ : syracuseStep 1162115 = 1743173) B1743173
theorem B1162385 : Blo 515797 1162385 := bstep (se 2 (by rfl) ⟨435894, by rfl⟩ : syracuseStep 1162385 = 871789) B871789
theorem B1162403 : Blo 515797 1162403 := bstep (se 1 (by rfl) ⟨871802, by rfl⟩ : syracuseStep 1162403 = 1743605) B1743605
theorem B1490179 : Blo 515797 1490179 := bstep (se 1 (by rfl) ⟨1117634, by rfl⟩ : syracuseStep 1490179 = 2235269) B2235269
theorem B736609 : Blo 515797 736609 := bstep (se 2 (by rfl) ⟨276228, by rfl⟩ : syracuseStep 736609 = 552457) B552457
theorem B933251 : Blo 515797 933251 := bstep (se 1 (by rfl) ⟨699938, by rfl⟩ : syracuseStep 933251 = 1399877) B1399877
theorem B4406669 : Blo 515797 4406669 := bstep (se 3 (by rfl) ⟨826250, by rfl⟩ : syracuseStep 4406669 = 1652501) B1652501
theorem B1752461 : Blo 515797 1752461 := bstep (se 3 (by rfl) ⟨328586, by rfl⟩ : syracuseStep 1752461 = 657173) B657173
theorem B1162673 : Blo 515797 1162673 := bstep (se 2 (by rfl) ⟨436002, by rfl⟩ : syracuseStep 1162673 = 872005) B872005
theorem B1162691 : Blo 515797 1162691 := bstep (se 1 (by rfl) ⟨872018, by rfl⟩ : syracuseStep 1162691 = 1744037) B1744037
theorem B1752515 : Blo 515797 1752515 := bstep (se 1 (by rfl) ⟨1314386, by rfl⟩ : syracuseStep 1752515 = 2628773) B2628773
theorem B736723 : Blo 515797 736723 := bstep (se 1 (by rfl) ⟨552542, by rfl⟩ : syracuseStep 736723 = 1105085) B1105085
theorem B1195555 : Blo 515797 1195555 := bstep (se 1 (by rfl) ⟨896666, by rfl⟩ : syracuseStep 1195555 = 1793333) B1793333
theorem B3358307 : Blo 515797 3358307 := bstep (se 1 (by rfl) ⟨2518730, by rfl⟩ : syracuseStep 3358307 = 5037461) B5037461
theorem B900721 : Blo 515797 900721 := bstep (se 2 (by rfl) ⟨337770, by rfl⟩ : syracuseStep 900721 = 675541) B675541
theorem B1162961 : Blo 515797 1162961 := bstep (se 2 (by rfl) ⟨436110, by rfl⟩ : syracuseStep 1162961 = 872221) B872221
theorem B1752785 : Blo 515797 1752785 := bstep (se 2 (by rfl) ⟨657294, by rfl⟩ : syracuseStep 1752785 = 1314589) B1314589
theorem B5881571 : Blo 515797 5881571 := bstep (se 1 (by rfl) ⟨4411178, by rfl⟩ : syracuseStep 5881571 = 8822357) B8822357
theorem B1162979 : Blo 515797 1162979 := bstep (se 1 (by rfl) ⟨872234, by rfl⟩ : syracuseStep 1162979 = 1744469) B1744469
theorem B2998093 : Blo 515797 2998093 := bstep (se 3 (by rfl) ⟨562142, by rfl⟩ : syracuseStep 2998093 = 1124285) B1124285
theorem B2211725 : Blo 515797 2211725 := bstep (se 3 (by rfl) ⟨414698, by rfl⟩ : syracuseStep 2211725 = 829397) B829397
theorem B1654705 : Blo 515797 1654705 := bstep (se 2 (by rfl) ⟨620514, by rfl⟩ : syracuseStep 1654705 = 1241029) B1241029
theorem B1163249 : Blo 515797 1163249 := bstep (se 2 (by rfl) ⟨436218, by rfl⟩ : syracuseStep 1163249 = 872437) B872437
theorem B1163267 : Blo 515797 1163267 := bstep (se 1 (by rfl) ⟨872450, by rfl⟩ : syracuseStep 1163267 = 1744901) B1744901
theorem B1753325 : Blo 515797 1753325 := bstep (se 3 (by rfl) ⟨328748, by rfl⟩ : syracuseStep 1753325 = 657497) B657497
theorem B1163537 : Blo 515797 1163537 := bstep (se 2 (by rfl) ⟨436326, by rfl⟩ : syracuseStep 1163537 = 872653) B872653
theorem B1163555 : Blo 515797 1163555 := bstep (se 1 (by rfl) ⟨872666, by rfl⟩ : syracuseStep 1163555 = 1745333) B1745333
theorem B1753379 : Blo 515797 1753379 := bstep (se 1 (by rfl) ⟨1315034, by rfl⟩ : syracuseStep 1753379 = 2630069) B2630069
theorem B1655309 : Blo 515797 1655309 := bstep (se 3 (by rfl) ⟨310370, by rfl⟩ : syracuseStep 1655309 = 620741) B620741
theorem B1163825 : Blo 515797 1163825 := bstep (se 2 (by rfl) ⟨436434, by rfl⟩ : syracuseStep 1163825 = 872869) B872869
theorem B1753649 : Blo 515797 1753649 := bstep (se 2 (by rfl) ⟨657618, by rfl⟩ : syracuseStep 1753649 = 1315237) B1315237
theorem B1163843 : Blo 515797 1163843 := bstep (se 1 (by rfl) ⟨872882, by rfl⟩ : syracuseStep 1163843 = 1745765) B1745765
theorem B1327889 : Blo 515797 1327889 := bstep (se 2 (by rfl) ⟨497958, by rfl⟩ : syracuseStep 1327889 = 995917) B995917
theorem B738067 : Blo 515797 738067 := bstep (se 1 (by rfl) ⟨553550, by rfl⟩ : syracuseStep 738067 = 1107101) B1107101
theorem B1000259 : Blo 515797 1000259 := bstep (se 1 (by rfl) ⟨750194, by rfl⟩ : syracuseStep 1000259 = 1500389) B1500389
theorem B1164113 : Blo 515797 1164113 := bstep (se 2 (by rfl) ⟨436542, by rfl⟩ : syracuseStep 1164113 = 873085) B873085
theorem B1164131 : Blo 515797 1164131 := bstep (se 1 (by rfl) ⟨873098, by rfl⟩ : syracuseStep 1164131 = 1746197) B1746197
theorem B1754189 : Blo 515797 1754189 := bstep (se 3 (by rfl) ⟨328910, by rfl⟩ : syracuseStep 1754189 = 657821) B657821
theorem B935011 : Blo 515797 935011 := bstep (se 1 (by rfl) ⟨701258, by rfl⟩ : syracuseStep 935011 = 1402517) B1402517
theorem B1164401 : Blo 515797 1164401 := bstep (se 2 (by rfl) ⟨436650, by rfl⟩ : syracuseStep 1164401 = 873301) B873301
theorem B1164419 : Blo 515797 1164419 := bstep (se 1 (by rfl) ⟨873314, by rfl⟩ : syracuseStep 1164419 = 1746629) B1746629
theorem B1754243 : Blo 515797 1754243 := bstep (se 1 (by rfl) ⟨1315682, by rfl⟩ : syracuseStep 1754243 = 2631365) B2631365
theorem B27280597 : Blo 515797 27280597 := bstep (se 7 (by rfl) ⟨319694, by rfl⟩ : syracuseStep 27280597 = 639389) B639389
theorem B1164689 : Blo 515797 1164689 := bstep (se 2 (by rfl) ⟨436758, by rfl⟩ : syracuseStep 1164689 = 873517) B873517
theorem B1164707 : Blo 515797 1164707 := bstep (se 1 (by rfl) ⟨873530, by rfl⟩ : syracuseStep 1164707 = 1747061) B1747061
theorem B1263107 : Blo 515797 1263107 := bstep (se 1 (by rfl) ⟨947330, by rfl⟩ : syracuseStep 1263107 = 1894661) B1894661
theorem B1164977 : Blo 515797 1164977 := bstep (se 2 (by rfl) ⟨436866, by rfl⟩ : syracuseStep 1164977 = 873733) B873733
theorem B1164995 : Blo 515797 1164995 := bstep (se 1 (by rfl) ⟨873746, by rfl⟩ : syracuseStep 1164995 = 1747493) B1747493
theorem B739201 : Blo 515797 739201 := bstep (se 2 (by rfl) ⟨277200, by rfl⟩ : syracuseStep 739201 = 554401) B554401
theorem B1165265 : Blo 515797 1165265 := bstep (se 2 (by rfl) ⟨436974, by rfl⟩ : syracuseStep 1165265 = 873949) B873949
theorem B739297 : Blo 515797 739297 := bstep (se 2 (by rfl) ⟨277236, by rfl⟩ : syracuseStep 739297 = 554473) B554473
theorem B1165283 : Blo 515797 1165283 := bstep (se 1 (by rfl) ⟨873962, by rfl⟩ : syracuseStep 1165283 = 1747925) B1747925
theorem B870419 : Blo 515797 870419 := bstep (se 1 (by rfl) ⟨652814, by rfl⟩ : syracuseStep 870419 = 1305629) B1305629
theorem B53889137 : Blo 515797 53889137 := bstep (se 2 (by rfl) ⟨20208426, by rfl⟩ : syracuseStep 53889137 = 40416853) B40416853
theorem B4966541 : Blo 515797 4966541 := bstep (se 3 (by rfl) ⟨931226, by rfl⟩ : syracuseStep 4966541 = 1862453) B1862453
theorem B870547 : Blo 515797 870547 := bstep (se 1 (by rfl) ⟨652910, by rfl⟩ : syracuseStep 870547 = 1305821) B1305821
theorem B3786979 : Blo 515797 3786979 := bstep (se 1 (by rfl) ⟨2840234, by rfl⟩ : syracuseStep 3786979 = 5680469) B5680469
theorem B1165553 : Blo 515797 1165553 := bstep (se 2 (by rfl) ⟨437082, by rfl⟩ : syracuseStep 1165553 = 874165) B874165
theorem B1165571 : Blo 515797 1165571 := bstep (se 1 (by rfl) ⟨874178, by rfl⟩ : syracuseStep 1165571 = 1748357) B1748357
theorem B22399253 : Blo 515797 22399253 := bstep (se 6 (by rfl) ⟨524982, by rfl⟩ : syracuseStep 22399253 = 1049965) B1049965
theorem B870689 : Blo 515797 870689 := bstep (se 2 (by rfl) ⟨326508, by rfl⟩ : syracuseStep 870689 = 653017) B653017
theorem B870817 : Blo 515797 870817 := bstep (se 2 (by rfl) ⟨326556, by rfl⟩ : syracuseStep 870817 = 653113) B653113
theorem B870851 : Blo 515797 870851 := bstep (se 1 (by rfl) ⟨653138, by rfl⟩ : syracuseStep 870851 = 1306277) B1306277
theorem B739793 : Blo 515797 739793 := bstep (se 2 (by rfl) ⟨277422, by rfl⟩ : syracuseStep 739793 = 554845) B554845
theorem B4966883 : Blo 515797 4966883 := bstep (se 1 (by rfl) ⟨3725162, by rfl⟩ : syracuseStep 4966883 = 7450325) B7450325
theorem B4868579 : Blo 515797 4868579 := bstep (se 1 (by rfl) ⟨3651434, by rfl⟩ : syracuseStep 4868579 = 7302869) B7302869
theorem B1165841 : Blo 515797 1165841 := bstep (se 2 (by rfl) ⟨437190, by rfl⟩ : syracuseStep 1165841 = 874381) B874381
theorem B1165859 : Blo 515797 1165859 := bstep (se 1 (by rfl) ⟨874394, by rfl⟩ : syracuseStep 1165859 = 1748789) B1748789
theorem B870979 : Blo 515797 870979 := bstep (se 1 (by rfl) ⟨653234, by rfl⟩ : syracuseStep 870979 = 1306469) B1306469
theorem B3361421 : Blo 515797 3361421 := bstep (se 3 (by rfl) ⟨630266, by rfl⟩ : syracuseStep 3361421 = 1260533) B1260533
theorem B871121 : Blo 515797 871121 := bstep (se 2 (by rfl) ⟨326670, by rfl⟩ : syracuseStep 871121 = 653341) B653341
theorem B1166129 : Blo 515797 1166129 := bstep (se 2 (by rfl) ⟨437298, by rfl⟩ : syracuseStep 1166129 = 874597) B874597
theorem B1166147 : Blo 515797 1166147 := bstep (se 1 (by rfl) ⟨874610, by rfl⟩ : syracuseStep 1166147 = 1749221) B1749221
theorem B871249 : Blo 515797 871249 := bstep (se 2 (by rfl) ⟨326718, by rfl⟩ : syracuseStep 871249 = 653437) B653437
theorem B871283 : Blo 515797 871283 := bstep (se 1 (by rfl) ⟨653462, by rfl⟩ : syracuseStep 871283 = 1306925) B1306925
theorem B1395683 : Blo 515797 1395683 := bstep (se 1 (by rfl) ⟨1046762, by rfl⟩ : syracuseStep 1395683 = 2093525) B2093525
theorem B871411 : Blo 515797 871411 := bstep (se 1 (by rfl) ⟨653558, by rfl⟩ : syracuseStep 871411 = 1307117) B1307117
theorem B3329093 : Blo 515797 3329093 := bstep (se 4 (by rfl) ⟨312102, by rfl⟩ : syracuseStep 3329093 = 624205) B624205
theorem B1166417 : Blo 515797 1166417 := bstep (se 2 (by rfl) ⟨437406, by rfl⟩ : syracuseStep 1166417 = 874813) B874813
theorem B1166435 : Blo 515797 1166435 := bstep (se 1 (by rfl) ⟨874826, by rfl⟩ : syracuseStep 1166435 = 1749653) B1749653
theorem B871553 : Blo 515797 871553 := bstep (se 2 (by rfl) ⟨326832, by rfl⟩ : syracuseStep 871553 = 653665) B653665
theorem B871681 : Blo 515797 871681 := bstep (se 2 (by rfl) ⟨326880, by rfl⟩ : syracuseStep 871681 = 653761) B653761
theorem B871715 : Blo 515797 871715 := bstep (se 1 (by rfl) ⟨653786, by rfl⟩ : syracuseStep 871715 = 1307573) B1307573
theorem B5918021 : Blo 515797 5918021 := bstep (se 4 (by rfl) ⟨554814, by rfl⟩ : syracuseStep 5918021 = 1109629) B1109629
theorem B1166705 : Blo 515797 1166705 := bstep (se 2 (by rfl) ⟨437514, by rfl⟩ : syracuseStep 1166705 = 875029) B875029
theorem B1166723 : Blo 515797 1166723 := bstep (se 1 (by rfl) ⟨875042, by rfl⟩ : syracuseStep 1166723 = 1750085) B1750085
theorem B871843 : Blo 515797 871843 := bstep (se 1 (by rfl) ⟨653882, by rfl⟩ : syracuseStep 871843 = 1307765) B1307765
theorem B871985 : Blo 515797 871985 := bstep (se 2 (by rfl) ⟨326994, by rfl⟩ : syracuseStep 871985 = 653989) B653989
theorem B773699 : Blo 515797 773699 := bstep (se 1 (by rfl) ⟨580274, by rfl⟩ : syracuseStep 773699 = 1160549) B1160549
theorem B773729 : Blo 515797 773729 := bstep (se 2 (by rfl) ⟨290148, by rfl⟩ : syracuseStep 773729 = 580297) B580297
theorem B773747 : Blo 515797 773747 := bstep (se 1 (by rfl) ⟨580310, by rfl⟩ : syracuseStep 773747 = 1160621) B1160621
theorem B773777 : Blo 515797 773777 := bstep (se 2 (by rfl) ⟨290166, by rfl⟩ : syracuseStep 773777 = 580333) B580333
theorem B1166993 : Blo 515797 1166993 := bstep (se 2 (by rfl) ⟨437622, by rfl⟩ : syracuseStep 1166993 = 875245) B875245
theorem B773795 : Blo 515797 773795 := bstep (se 1 (by rfl) ⟨580346, by rfl⟩ : syracuseStep 773795 = 1160693) B1160693
theorem B1167011 : Blo 515797 1167011 := bstep (se 1 (by rfl) ⟨875258, by rfl⟩ : syracuseStep 1167011 = 1750517) B1750517
theorem B872113 : Blo 515797 872113 := bstep (se 2 (by rfl) ⟨327042, by rfl⟩ : syracuseStep 872113 = 654085) B654085
theorem B773825 : Blo 515797 773825 := bstep (se 2 (by rfl) ⟨290184, by rfl⟩ : syracuseStep 773825 = 580369) B580369
theorem B773843 : Blo 515797 773843 := bstep (se 1 (by rfl) ⟨580382, by rfl⟩ : syracuseStep 773843 = 1160765) B1160765
theorem B872147 : Blo 515797 872147 := bstep (se 1 (by rfl) ⟨654110, by rfl⟩ : syracuseStep 872147 = 1308221) B1308221
theorem B773873 : Blo 515797 773873 := bstep (se 2 (by rfl) ⟨290202, by rfl⟩ : syracuseStep 773873 = 580405) B580405
theorem B773891 : Blo 515797 773891 := bstep (se 1 (by rfl) ⟨580418, by rfl⟩ : syracuseStep 773891 = 1160837) B1160837
theorem B1658627 : Blo 515797 1658627 := bstep (se 1 (by rfl) ⟨1243970, by rfl⟩ : syracuseStep 1658627 = 2487941) B2487941
theorem B773921 : Blo 515797 773921 := bstep (se 2 (by rfl) ⟨290220, by rfl⟩ : syracuseStep 773921 = 580441) B580441
theorem B773939 : Blo 515797 773939 := bstep (se 1 (by rfl) ⟨580454, by rfl⟩ : syracuseStep 773939 = 1160909) B1160909
theorem B773969 : Blo 515797 773969 := bstep (se 2 (by rfl) ⟨290238, by rfl⟩ : syracuseStep 773969 = 580477) B580477
theorem B872275 : Blo 515797 872275 := bstep (se 1 (by rfl) ⟨654206, by rfl⟩ : syracuseStep 872275 = 1308413) B1308413
theorem B773987 : Blo 515797 773987 := bstep (se 1 (by rfl) ⟨580490, by rfl⟩ : syracuseStep 773987 = 1160981) B1160981
theorem B774017 : Blo 515797 774017 := bstep (se 2 (by rfl) ⟨290256, by rfl⟩ : syracuseStep 774017 = 580513) B580513
theorem B2805637 : Blo 515797 2805637 := bstep (se 4 (by rfl) ⟨263028, by rfl⟩ : syracuseStep 2805637 = 526057) B526057
theorem B774035 : Blo 515797 774035 := bstep (se 1 (by rfl) ⟨580526, by rfl⟩ : syracuseStep 774035 = 1161053) B1161053
theorem B774065 : Blo 515797 774065 := bstep (se 2 (by rfl) ⟨290274, by rfl⟩ : syracuseStep 774065 = 580549) B580549
theorem B1167281 : Blo 515797 1167281 := bstep (se 2 (by rfl) ⟨437730, by rfl⟩ : syracuseStep 1167281 = 875461) B875461
theorem B774083 : Blo 515797 774083 := bstep (se 1 (by rfl) ⟨580562, by rfl⟩ : syracuseStep 774083 = 1161125) B1161125
theorem B1167299 : Blo 515797 1167299 := bstep (se 1 (by rfl) ⟨875474, by rfl⟩ : syracuseStep 1167299 = 1750949) B1750949
theorem B16175045 : Blo 515797 16175045 := bstep (se 4 (by rfl) ⟨1516410, by rfl⟩ : syracuseStep 16175045 = 3032821) B3032821
theorem B774113 : Blo 515797 774113 := bstep (se 2 (by rfl) ⟨290292, by rfl⟩ : syracuseStep 774113 = 580585) B580585
theorem B872417 : Blo 515797 872417 := bstep (se 2 (by rfl) ⟨327156, by rfl⟩ : syracuseStep 872417 = 654313) B654313
theorem B774131 : Blo 515797 774131 := bstep (se 1 (by rfl) ⟨580598, by rfl⟩ : syracuseStep 774131 = 1161197) B1161197
theorem B774161 : Blo 515797 774161 := bstep (se 2 (by rfl) ⟨290310, by rfl⟩ : syracuseStep 774161 = 580621) B580621
theorem B774179 : Blo 515797 774179 := bstep (se 1 (by rfl) ⟨580634, by rfl⟩ : syracuseStep 774179 = 1161269) B1161269
theorem B774209 : Blo 515797 774209 := bstep (se 2 (by rfl) ⟨290328, by rfl⟩ : syracuseStep 774209 = 580657) B580657
theorem B774227 : Blo 515797 774227 := bstep (se 1 (by rfl) ⟨580670, by rfl⟩ : syracuseStep 774227 = 1161341) B1161341
theorem B872545 : Blo 515797 872545 := bstep (se 2 (by rfl) ⟨327204, by rfl⟩ : syracuseStep 872545 = 654409) B654409
theorem B774257 : Blo 515797 774257 := bstep (se 2 (by rfl) ⟨290346, by rfl⟩ : syracuseStep 774257 = 580693) B580693
theorem B774275 : Blo 515797 774275 := bstep (se 1 (by rfl) ⟨580706, by rfl⟩ : syracuseStep 774275 = 1161413) B1161413
theorem B872579 : Blo 515797 872579 := bstep (se 1 (by rfl) ⟨654434, by rfl⟩ : syracuseStep 872579 = 1308869) B1308869
theorem B774305 : Blo 515797 774305 := bstep (se 2 (by rfl) ⟨290364, by rfl⟩ : syracuseStep 774305 = 580729) B580729
theorem B2216099 : Blo 515797 2216099 := bstep (se 1 (by rfl) ⟨1662074, by rfl⟩ : syracuseStep 2216099 = 3324149) B3324149
theorem B774323 : Blo 515797 774323 := bstep (se 1 (by rfl) ⟨580742, by rfl⟩ : syracuseStep 774323 = 1161485) B1161485
theorem B774353 : Blo 515797 774353 := bstep (se 2 (by rfl) ⟨290382, by rfl⟩ : syracuseStep 774353 = 580765) B580765
theorem B1167569 : Blo 515797 1167569 := bstep (se 2 (by rfl) ⟨437838, by rfl⟩ : syracuseStep 1167569 = 875677) B875677
theorem B774371 : Blo 515797 774371 := bstep (se 1 (by rfl) ⟨580778, by rfl⟩ : syracuseStep 774371 = 1161557) B1161557
theorem B1167587 : Blo 515797 1167587 := bstep (se 1 (by rfl) ⟨875690, by rfl⟩ : syracuseStep 1167587 = 1751381) B1751381
theorem B774401 : Blo 515797 774401 := bstep (se 2 (by rfl) ⟨290400, by rfl⟩ : syracuseStep 774401 = 580801) B580801
theorem B872707 : Blo 515797 872707 := bstep (se 1 (by rfl) ⟨654530, by rfl⟩ : syracuseStep 872707 = 1309061) B1309061
theorem B774419 : Blo 515797 774419 := bstep (se 1 (by rfl) ⟨580814, by rfl⟩ : syracuseStep 774419 = 1161629) B1161629
theorem B1331491 : Blo 515797 1331491 := bstep (se 1 (by rfl) ⟨998618, by rfl⟩ : syracuseStep 1331491 = 1997237) B1997237
theorem B774449 : Blo 515797 774449 := bstep (se 2 (by rfl) ⟨290418, by rfl⟩ : syracuseStep 774449 = 580837) B580837
theorem B774467 : Blo 515797 774467 := bstep (se 1 (by rfl) ⟨580850, by rfl⟩ : syracuseStep 774467 = 1161701) B1161701
theorem B774497 : Blo 515797 774497 := bstep (se 2 (by rfl) ⟨290436, by rfl⟩ : syracuseStep 774497 = 580873) B580873
theorem B1397101 : Blo 515797 1397101 := bstep (se 3 (by rfl) ⟨261956, by rfl⟩ : syracuseStep 1397101 = 523913) B523913
theorem B774515 : Blo 515797 774515 := bstep (se 1 (by rfl) ⟨580886, by rfl⟩ : syracuseStep 774515 = 1161773) B1161773
theorem B774545 : Blo 515797 774545 := bstep (se 2 (by rfl) ⟨290454, by rfl⟩ : syracuseStep 774545 = 580909) B580909
theorem B872849 : Blo 515797 872849 := bstep (se 2 (by rfl) ⟨327318, by rfl⟩ : syracuseStep 872849 = 654637) B654637
theorem B774563 : Blo 515797 774563 := bstep (se 1 (by rfl) ⟨580922, by rfl⟩ : syracuseStep 774563 = 1161845) B1161845
theorem B774593 : Blo 515797 774593 := bstep (se 2 (by rfl) ⟨290472, by rfl⟩ : syracuseStep 774593 = 580945) B580945
theorem B774611 : Blo 515797 774611 := bstep (se 1 (by rfl) ⟨580958, by rfl⟩ : syracuseStep 774611 = 1161917) B1161917
theorem B774641 : Blo 515797 774641 := bstep (se 2 (by rfl) ⟨290490, by rfl⟩ : syracuseStep 774641 = 580981) B580981
theorem B1167857 : Blo 515797 1167857 := bstep (se 2 (by rfl) ⟨437946, by rfl⟩ : syracuseStep 1167857 = 875893) B875893
theorem B774659 : Blo 515797 774659 := bstep (se 1 (by rfl) ⟨580994, by rfl⟩ : syracuseStep 774659 = 1161989) B1161989
theorem B1167875 : Blo 515797 1167875 := bstep (se 1 (by rfl) ⟨875906, by rfl⟩ : syracuseStep 1167875 = 1751813) B1751813
theorem B872977 : Blo 515797 872977 := bstep (se 2 (by rfl) ⟨327366, by rfl⟩ : syracuseStep 872977 = 654733) B654733
theorem B774689 : Blo 515797 774689 := bstep (se 2 (by rfl) ⟨290508, by rfl⟩ : syracuseStep 774689 = 581017) B581017
theorem B1102385 : Blo 515797 1102385 := bstep (se 2 (by rfl) ⟨413394, by rfl⟩ : syracuseStep 1102385 = 826789) B826789
theorem B774707 : Blo 515797 774707 := bstep (se 1 (by rfl) ⟨581030, by rfl⟩ : syracuseStep 774707 = 1162061) B1162061
theorem B873011 : Blo 515797 873011 := bstep (se 1 (by rfl) ⟨654758, by rfl⟩ : syracuseStep 873011 = 1309517) B1309517
theorem B1102403 : Blo 515797 1102403 := bstep (se 1 (by rfl) ⟨826802, by rfl⟩ : syracuseStep 1102403 = 1653605) B1653605
theorem B774737 : Blo 515797 774737 := bstep (se 2 (by rfl) ⟨290526, by rfl⟩ : syracuseStep 774737 = 581053) B581053
theorem B1659473 : Blo 515797 1659473 := bstep (se 2 (by rfl) ⟨622302, by rfl⟩ : syracuseStep 1659473 = 1244605) B1244605
theorem B774755 : Blo 515797 774755 := bstep (se 1 (by rfl) ⟨581066, by rfl⟩ : syracuseStep 774755 = 1162133) B1162133
theorem B774785 : Blo 515797 774785 := bstep (se 2 (by rfl) ⟨290544, by rfl⟩ : syracuseStep 774785 = 581089) B581089
theorem B1659523 : Blo 515797 1659523 := bstep (se 1 (by rfl) ⟨1244642, by rfl⟩ : syracuseStep 1659523 = 2489285) B2489285
theorem B774803 : Blo 515797 774803 := bstep (se 1 (by rfl) ⟨581102, by rfl⟩ : syracuseStep 774803 = 1162205) B1162205
theorem B774833 : Blo 515797 774833 := bstep (se 2 (by rfl) ⟨290562, by rfl⟩ : syracuseStep 774833 = 581125) B581125
theorem B873139 : Blo 515797 873139 := bstep (se 1 (by rfl) ⟨654854, by rfl⟩ : syracuseStep 873139 = 1309709) B1309709
theorem B840385 : Blo 515797 840385 := bstep (se 2 (by rfl) ⟨315144, by rfl⟩ : syracuseStep 840385 = 630289) B630289
theorem B774851 : Blo 515797 774851 := bstep (se 1 (by rfl) ⟨581138, by rfl⟩ : syracuseStep 774851 = 1162277) B1162277
theorem B774881 : Blo 515797 774881 := bstep (se 2 (by rfl) ⟨290580, by rfl⟩ : syracuseStep 774881 = 581161) B581161
theorem B774899 : Blo 515797 774899 := bstep (se 1 (by rfl) ⟨581174, by rfl⟩ : syracuseStep 774899 = 1162349) B1162349
theorem B774929 : Blo 515797 774929 := bstep (se 2 (by rfl) ⟨290598, by rfl⟩ : syracuseStep 774929 = 581197) B581197
theorem B1168145 : Blo 515797 1168145 := bstep (se 2 (by rfl) ⟨438054, by rfl⟩ : syracuseStep 1168145 = 876109) B876109
theorem B774947 : Blo 515797 774947 := bstep (se 1 (by rfl) ⟨581210, by rfl⟩ : syracuseStep 774947 = 1162421) B1162421
theorem B1168163 : Blo 515797 1168163 := bstep (se 1 (by rfl) ⟨876122, by rfl⟩ : syracuseStep 1168163 = 1752245) B1752245
theorem B774977 : Blo 515797 774977 := bstep (se 2 (by rfl) ⟨290616, by rfl⟩ : syracuseStep 774977 = 581233) B581233
theorem B873281 : Blo 515797 873281 := bstep (se 2 (by rfl) ⟨327480, by rfl⟩ : syracuseStep 873281 = 654961) B654961
theorem B1332035 : Blo 515797 1332035 := bstep (se 1 (by rfl) ⟨999026, by rfl⟩ : syracuseStep 1332035 = 1998053) B1998053
theorem B774995 : Blo 515797 774995 := bstep (se 1 (by rfl) ⟨581246, by rfl⟩ : syracuseStep 774995 = 1162493) B1162493
theorem B775025 : Blo 515797 775025 := bstep (se 2 (by rfl) ⟨290634, by rfl⟩ : syracuseStep 775025 = 581269) B581269
theorem B775043 : Blo 515797 775043 := bstep (se 1 (by rfl) ⟨581282, by rfl⟩ : syracuseStep 775043 = 1162565) B1162565
theorem B775073 : Blo 515797 775073 := bstep (se 2 (by rfl) ⟨290652, by rfl⟩ : syracuseStep 775073 = 581305) B581305
theorem B775091 : Blo 515797 775091 := bstep (se 1 (by rfl) ⟨581318, by rfl⟩ : syracuseStep 775091 = 1162637) B1162637
theorem B873409 : Blo 515797 873409 := bstep (se 2 (by rfl) ⟨327528, by rfl⟩ : syracuseStep 873409 = 655057) B655057
theorem B775121 : Blo 515797 775121 := bstep (se 2 (by rfl) ⟨290670, by rfl⟩ : syracuseStep 775121 = 581341) B581341
theorem B775139 : Blo 515797 775139 := bstep (se 1 (by rfl) ⟨581354, by rfl⟩ : syracuseStep 775139 = 1162709) B1162709
theorem B873443 : Blo 515797 873443 := bstep (se 1 (by rfl) ⟨655082, by rfl⟩ : syracuseStep 873443 = 1310165) B1310165
theorem B775169 : Blo 515797 775169 := bstep (se 2 (by rfl) ⟨290688, by rfl⟩ : syracuseStep 775169 = 581377) B581377
theorem B775187 : Blo 515797 775187 := bstep (se 1 (by rfl) ⟨581390, by rfl⟩ : syracuseStep 775187 = 1162781) B1162781
theorem B775217 : Blo 515797 775217 := bstep (se 2 (by rfl) ⟨290706, by rfl⟩ : syracuseStep 775217 = 581413) B581413
theorem B1168433 : Blo 515797 1168433 := bstep (se 2 (by rfl) ⟨438162, by rfl⟩ : syracuseStep 1168433 = 876325) B876325
theorem B775235 : Blo 515797 775235 := bstep (se 1 (by rfl) ⟨581426, by rfl⟩ : syracuseStep 775235 = 1162853) B1162853
theorem B1168451 : Blo 515797 1168451 := bstep (se 1 (by rfl) ⟨876338, by rfl⟩ : syracuseStep 1168451 = 1752677) B1752677
theorem B775265 : Blo 515797 775265 := bstep (se 2 (by rfl) ⟨290724, by rfl⟩ : syracuseStep 775265 = 581449) B581449
theorem B873571 : Blo 515797 873571 := bstep (se 1 (by rfl) ⟨655178, by rfl⟩ : syracuseStep 873571 = 1310357) B1310357
theorem B775283 : Blo 515797 775283 := bstep (se 1 (by rfl) ⟨581462, by rfl⟩ : syracuseStep 775283 = 1162925) B1162925
theorem B775313 : Blo 515797 775313 := bstep (se 2 (by rfl) ⟨290742, by rfl⟩ : syracuseStep 775313 = 581485) B581485
theorem B775331 : Blo 515797 775331 := bstep (se 1 (by rfl) ⟨581498, by rfl⟩ : syracuseStep 775331 = 1162997) B1162997
theorem B775361 : Blo 515797 775361 := bstep (se 2 (by rfl) ⟨290760, by rfl⟩ : syracuseStep 775361 = 581521) B581521
theorem B775379 : Blo 515797 775379 := bstep (se 1 (by rfl) ⟨581534, by rfl⟩ : syracuseStep 775379 = 1163069) B1163069
theorem B775409 : Blo 515797 775409 := bstep (se 2 (by rfl) ⟨290778, by rfl⟩ : syracuseStep 775409 = 581557) B581557
theorem B873713 : Blo 515797 873713 := bstep (se 2 (by rfl) ⟨327642, by rfl⟩ : syracuseStep 873713 = 655285) B655285
theorem B775427 : Blo 515797 775427 := bstep (se 1 (by rfl) ⟨581570, by rfl⟩ : syracuseStep 775427 = 1163141) B1163141
theorem B775457 : Blo 515797 775457 := bstep (se 2 (by rfl) ⟨290796, by rfl⟩ : syracuseStep 775457 = 581593) B581593
theorem B775475 : Blo 515797 775475 := bstep (se 1 (by rfl) ⟨581606, by rfl⟩ : syracuseStep 775475 = 1163213) B1163213
theorem B775505 : Blo 515797 775505 := bstep (se 2 (by rfl) ⟨290814, by rfl⟩ : syracuseStep 775505 = 581629) B581629
theorem B1168721 : Blo 515797 1168721 := bstep (se 2 (by rfl) ⟨438270, by rfl⟩ : syracuseStep 1168721 = 876541) B876541
theorem B775523 : Blo 515797 775523 := bstep (se 1 (by rfl) ⟨581642, by rfl⟩ : syracuseStep 775523 = 1163285) B1163285
theorem B1168739 : Blo 515797 1168739 := bstep (se 1 (by rfl) ⟨876554, by rfl⟩ : syracuseStep 1168739 = 1753109) B1753109
theorem B873841 : Blo 515797 873841 := bstep (se 2 (by rfl) ⟨327690, by rfl⟩ : syracuseStep 873841 = 655381) B655381
theorem B775553 : Blo 515797 775553 := bstep (se 2 (by rfl) ⟨290832, by rfl⟩ : syracuseStep 775553 = 581665) B581665
theorem B775571 : Blo 515797 775571 := bstep (se 1 (by rfl) ⟨581678, by rfl⟩ : syracuseStep 775571 = 1163357) B1163357
theorem B873875 : Blo 515797 873875 := bstep (se 1 (by rfl) ⟨655406, by rfl⟩ : syracuseStep 873875 = 1310813) B1310813
theorem B775601 : Blo 515797 775601 := bstep (se 2 (by rfl) ⟨290850, by rfl⟩ : syracuseStep 775601 = 581701) B581701
theorem B775619 : Blo 515797 775619 := bstep (se 1 (by rfl) ⟨581714, by rfl⟩ : syracuseStep 775619 = 1163429) B1163429
theorem B13424069 : Blo 515797 13424069 := bstep (se 4 (by rfl) ⟨1258506, by rfl⟩ : syracuseStep 13424069 = 2517013) B2517013
theorem B2807237 : Blo 515797 2807237 := bstep (se 4 (by rfl) ⟨263178, by rfl⟩ : syracuseStep 2807237 = 526357) B526357
theorem B775649 : Blo 515797 775649 := bstep (se 2 (by rfl) ⟨290868, by rfl⟩ : syracuseStep 775649 = 581737) B581737
theorem B775667 : Blo 515797 775667 := bstep (se 1 (by rfl) ⟨581750, by rfl⟩ : syracuseStep 775667 = 1163501) B1163501
theorem B775697 : Blo 515797 775697 := bstep (se 2 (by rfl) ⟨290886, by rfl⟩ : syracuseStep 775697 = 581773) B581773
theorem B874003 : Blo 515797 874003 := bstep (se 1 (by rfl) ⟨655502, by rfl⟩ : syracuseStep 874003 = 1311005) B1311005
theorem B775715 : Blo 515797 775715 := bstep (se 1 (by rfl) ⟨581786, by rfl⟩ : syracuseStep 775715 = 1163573) B1163573
theorem B775745 : Blo 515797 775745 := bstep (se 2 (by rfl) ⟨290904, by rfl⟩ : syracuseStep 775745 = 581809) B581809
theorem B775763 : Blo 515797 775763 := bstep (se 1 (by rfl) ⟨581822, by rfl⟩ : syracuseStep 775763 = 1163645) B1163645
theorem B775793 : Blo 515797 775793 := bstep (se 2 (by rfl) ⟨290922, by rfl⟩ : syracuseStep 775793 = 581845) B581845
theorem B1169009 : Blo 515797 1169009 := bstep (se 2 (by rfl) ⟨438378, by rfl⟩ : syracuseStep 1169009 = 876757) B876757
theorem B775811 : Blo 515797 775811 := bstep (se 1 (by rfl) ⟨581858, by rfl⟩ : syracuseStep 775811 = 1163717) B1163717
theorem B1169027 : Blo 515797 1169027 := bstep (se 1 (by rfl) ⟨876770, by rfl⟩ : syracuseStep 1169027 = 1753541) B1753541
theorem B775841 : Blo 515797 775841 := bstep (se 2 (by rfl) ⟨290940, by rfl⟩ : syracuseStep 775841 = 581881) B581881
theorem B874145 : Blo 515797 874145 := bstep (se 2 (by rfl) ⟨327804, by rfl⟩ : syracuseStep 874145 = 655609) B655609
theorem B775859 : Blo 515797 775859 := bstep (se 1 (by rfl) ⟨581894, by rfl⟩ : syracuseStep 775859 = 1163789) B1163789
theorem B775889 : Blo 515797 775889 := bstep (se 2 (by rfl) ⟨290958, by rfl⟩ : syracuseStep 775889 = 581917) B581917
theorem B775907 : Blo 515797 775907 := bstep (se 1 (by rfl) ⟨581930, by rfl⟩ : syracuseStep 775907 = 1163861) B1163861
theorem B775937 : Blo 515797 775937 := bstep (se 2 (by rfl) ⟨290976, by rfl⟩ : syracuseStep 775937 = 581953) B581953
theorem B775955 : Blo 515797 775955 := bstep (se 1 (by rfl) ⟨581966, by rfl⟩ : syracuseStep 775955 = 1163933) B1163933
theorem B874273 : Blo 515797 874273 := bstep (se 2 (by rfl) ⟨327852, by rfl⟩ : syracuseStep 874273 = 655705) B655705
theorem B775985 : Blo 515797 775985 := bstep (se 2 (by rfl) ⟨290994, by rfl⟩ : syracuseStep 775985 = 581989) B581989
theorem B776003 : Blo 515797 776003 := bstep (se 1 (by rfl) ⟨582002, by rfl⟩ : syracuseStep 776003 = 1164005) B1164005
theorem B874307 : Blo 515797 874307 := bstep (se 1 (by rfl) ⟨655730, by rfl⟩ : syracuseStep 874307 = 1311461) B1311461
theorem B1660753 : Blo 515797 1660753 := bstep (se 2 (by rfl) ⟨622782, by rfl⟩ : syracuseStep 1660753 = 1245565) B1245565
theorem B776033 : Blo 515797 776033 := bstep (se 2 (by rfl) ⟨291012, by rfl⟩ : syracuseStep 776033 = 582025) B582025
theorem B776051 : Blo 515797 776051 := bstep (se 1 (by rfl) ⟨582038, by rfl⟩ : syracuseStep 776051 = 1164077) B1164077
theorem B776081 : Blo 515797 776081 := bstep (se 2 (by rfl) ⟨291030, by rfl⟩ : syracuseStep 776081 = 582061) B582061
theorem B1169297 : Blo 515797 1169297 := bstep (se 2 (by rfl) ⟨438486, by rfl⟩ : syracuseStep 1169297 = 876973) B876973
theorem B776099 : Blo 515797 776099 := bstep (se 1 (by rfl) ⟨582074, by rfl⟩ : syracuseStep 776099 = 1164149) B1164149
theorem B1169315 : Blo 515797 1169315 := bstep (se 1 (by rfl) ⟨876986, by rfl⟩ : syracuseStep 1169315 = 1753973) B1753973
theorem B776129 : Blo 515797 776129 := bstep (se 2 (by rfl) ⟨291048, by rfl⟩ : syracuseStep 776129 = 582097) B582097
theorem B874435 : Blo 515797 874435 := bstep (se 1 (by rfl) ⟨655826, by rfl⟩ : syracuseStep 874435 = 1311653) B1311653
theorem B841681 : Blo 515797 841681 := bstep (se 2 (by rfl) ⟨315630, by rfl⟩ : syracuseStep 841681 = 631261) B631261
theorem B776147 : Blo 515797 776147 := bstep (se 1 (by rfl) ⟨582110, by rfl⟩ : syracuseStep 776147 = 1164221) B1164221
theorem B776177 : Blo 515797 776177 := bstep (se 2 (by rfl) ⟨291066, by rfl⟩ : syracuseStep 776177 = 582133) B582133
theorem B776195 : Blo 515797 776195 := bstep (se 1 (by rfl) ⟨582146, by rfl⟩ : syracuseStep 776195 = 1164293) B1164293
theorem B776225 : Blo 515797 776225 := bstep (se 2 (by rfl) ⟨291084, by rfl⟩ : syracuseStep 776225 = 582169) B582169
theorem B776243 : Blo 515797 776243 := bstep (se 1 (by rfl) ⟨582182, by rfl⟩ : syracuseStep 776243 = 1164365) B1164365
theorem B2611277 : Blo 515797 2611277 := bstep (se 3 (by rfl) ⟨489614, by rfl⟩ : syracuseStep 2611277 = 979229) B979229
theorem B776273 : Blo 515797 776273 := bstep (se 2 (by rfl) ⟨291102, by rfl⟩ : syracuseStep 776273 = 582205) B582205
theorem B874577 : Blo 515797 874577 := bstep (se 2 (by rfl) ⟨327966, by rfl⟩ : syracuseStep 874577 = 655933) B655933
theorem B3922019 : Blo 515797 3922019 := bstep (se 1 (by rfl) ⟨2941514, by rfl⟩ : syracuseStep 3922019 = 5883029) B5883029
theorem B776291 : Blo 515797 776291 := bstep (se 1 (by rfl) ⟨582218, by rfl⟩ : syracuseStep 776291 = 1164437) B1164437
theorem B2218097 : Blo 515797 2218097 := bstep (se 2 (by rfl) ⟨831786, by rfl⟩ : syracuseStep 2218097 = 1663573) B1663573
theorem B776321 : Blo 515797 776321 := bstep (se 2 (by rfl) ⟨291120, by rfl⟩ : syracuseStep 776321 = 582241) B582241
theorem B3725453 : Blo 515797 3725453 := bstep (se 3 (by rfl) ⟨698522, by rfl⟩ : syracuseStep 3725453 = 1397045) B1397045
theorem B776339 : Blo 515797 776339 := bstep (se 1 (by rfl) ⟨582254, by rfl⟩ : syracuseStep 776339 = 1164509) B1164509
theorem B2480291 : Blo 515797 2480291 := bstep (se 1 (by rfl) ⟨1860218, by rfl⟩ : syracuseStep 2480291 = 3720437) B3720437
theorem B776369 : Blo 515797 776369 := bstep (se 2 (by rfl) ⟨291138, by rfl⟩ : syracuseStep 776369 = 582277) B582277
theorem B776387 : Blo 515797 776387 := bstep (se 1 (by rfl) ⟨582290, by rfl⟩ : syracuseStep 776387 = 1164581) B1164581
theorem B3725509 : Blo 515797 3725509 := bstep (se 4 (by rfl) ⟨349266, by rfl⟩ : syracuseStep 3725509 = 698533) B698533
theorem B874705 : Blo 515797 874705 := bstep (se 2 (by rfl) ⟨328014, by rfl⟩ : syracuseStep 874705 = 656029) B656029
theorem B776417 : Blo 515797 776417 := bstep (se 2 (by rfl) ⟨291156, by rfl⟩ : syracuseStep 776417 = 582313) B582313
theorem B776435 : Blo 515797 776435 := bstep (se 1 (by rfl) ⟨582326, by rfl⟩ : syracuseStep 776435 = 1164653) B1164653
theorem B874739 : Blo 515797 874739 := bstep (se 1 (by rfl) ⟨656054, by rfl⟩ : syracuseStep 874739 = 1312109) B1312109
theorem B776465 : Blo 515797 776465 := bstep (se 2 (by rfl) ⟨291174, by rfl⟩ : syracuseStep 776465 = 582349) B582349
theorem B11229461 : Blo 515797 11229461 := bstep (se 6 (by rfl) ⟨263190, by rfl⟩ : syracuseStep 11229461 = 526381) B526381
theorem B776483 : Blo 515797 776483 := bstep (se 1 (by rfl) ⟨582362, by rfl⟩ : syracuseStep 776483 = 1164725) B1164725
theorem B776513 : Blo 515797 776513 := bstep (se 2 (by rfl) ⟨291192, by rfl⟩ : syracuseStep 776513 = 582385) B582385
theorem B776531 : Blo 515797 776531 := bstep (se 1 (by rfl) ⟨582398, by rfl⟩ : syracuseStep 776531 = 1164797) B1164797
theorem B776561 : Blo 515797 776561 := bstep (se 2 (by rfl) ⟨291210, by rfl⟩ : syracuseStep 776561 = 582421) B582421
theorem B874867 : Blo 515797 874867 := bstep (se 1 (by rfl) ⟨656150, by rfl⟩ : syracuseStep 874867 = 1312301) B1312301
theorem B776579 : Blo 515797 776579 := bstep (se 1 (by rfl) ⟨582434, by rfl⟩ : syracuseStep 776579 = 1164869) B1164869
theorem B1497475 : Blo 515797 1497475 := bstep (se 1 (by rfl) ⟨1123106, by rfl⟩ : syracuseStep 1497475 = 2246213) B2246213
theorem B776609 : Blo 515797 776609 := bstep (se 2 (by rfl) ⟨291228, by rfl⟩ : syracuseStep 776609 = 582457) B582457
theorem B776627 : Blo 515797 776627 := bstep (se 1 (by rfl) ⟨582470, by rfl⟩ : syracuseStep 776627 = 1164941) B1164941
theorem B776657 : Blo 515797 776657 := bstep (se 2 (by rfl) ⟨291246, by rfl⟩ : syracuseStep 776657 = 582493) B582493
theorem B776675 : Blo 515797 776675 := bstep (se 1 (by rfl) ⟨582506, by rfl⟩ : syracuseStep 776675 = 1165013) B1165013
theorem B776705 : Blo 515797 776705 := bstep (se 2 (by rfl) ⟨291264, by rfl⟩ : syracuseStep 776705 = 582529) B582529
theorem B875009 : Blo 515797 875009 := bstep (se 2 (by rfl) ⟨328128, by rfl⟩ : syracuseStep 875009 = 656257) B656257
theorem B1104401 : Blo 515797 1104401 := bstep (se 2 (by rfl) ⟨414150, by rfl⟩ : syracuseStep 1104401 = 828301) B828301
theorem B776723 : Blo 515797 776723 := bstep (se 1 (by rfl) ⟨582542, by rfl⟩ : syracuseStep 776723 = 1165085) B1165085
theorem B776753 : Blo 515797 776753 := bstep (se 2 (by rfl) ⟨291282, by rfl⟩ : syracuseStep 776753 = 582565) B582565
theorem B45439541 : Blo 515797 45439541 := bstep (se 5 (by rfl) ⟨2129978, by rfl⟩ : syracuseStep 45439541 = 4259957) B4259957
theorem B776771 : Blo 515797 776771 := bstep (se 1 (by rfl) ⟨582578, by rfl⟩ : syracuseStep 776771 = 1165157) B1165157
theorem B776801 : Blo 515797 776801 := bstep (se 2 (by rfl) ⟨291300, by rfl⟩ : syracuseStep 776801 = 582601) B582601
theorem B776819 : Blo 515797 776819 := bstep (se 1 (by rfl) ⟨582614, by rfl⟩ : syracuseStep 776819 = 1165229) B1165229
theorem B875137 : Blo 515797 875137 := bstep (se 2 (by rfl) ⟨328176, by rfl⟩ : syracuseStep 875137 = 656353) B656353
theorem B776849 : Blo 515797 776849 := bstep (se 2 (by rfl) ⟨291318, by rfl⟩ : syracuseStep 776849 = 582637) B582637
theorem B776867 : Blo 515797 776867 := bstep (se 1 (by rfl) ⟨582650, by rfl⟩ : syracuseStep 776867 = 1165301) B1165301
theorem B875171 : Blo 515797 875171 := bstep (se 1 (by rfl) ⟨656378, by rfl⟩ : syracuseStep 875171 = 1312757) B1312757
theorem B776897 : Blo 515797 776897 := bstep (se 2 (by rfl) ⟨291336, by rfl⟩ : syracuseStep 776897 = 582673) B582673
theorem B776915 : Blo 515797 776915 := bstep (se 1 (by rfl) ⟨582686, by rfl⟩ : syracuseStep 776915 = 1165373) B1165373
theorem B776945 : Blo 515797 776945 := bstep (se 2 (by rfl) ⟨291354, by rfl⟩ : syracuseStep 776945 = 582709) B582709
theorem B776963 : Blo 515797 776963 := bstep (se 1 (by rfl) ⟨582722, by rfl⟩ : syracuseStep 776963 = 1165445) B1165445
theorem B776993 : Blo 515797 776993 := bstep (se 2 (by rfl) ⟨291372, by rfl⟩ : syracuseStep 776993 = 582745) B582745
theorem B580387 : Blo 515797 580387 := bstep (se 1 (by rfl) ⟨435290, by rfl⟩ : syracuseStep 580387 = 870581) B870581
theorem B875299 : Blo 515797 875299 := bstep (se 1 (by rfl) ⟨656474, by rfl⟩ : syracuseStep 875299 = 1312949) B1312949
theorem B777011 : Blo 515797 777011 := bstep (se 1 (by rfl) ⟨582758, by rfl⟩ : syracuseStep 777011 = 1165517) B1165517
theorem B777041 : Blo 515797 777041 := bstep (se 2 (by rfl) ⟨291390, by rfl⟩ : syracuseStep 777041 = 582781) B582781
theorem B777059 : Blo 515797 777059 := bstep (se 1 (by rfl) ⟨582794, by rfl⟩ : syracuseStep 777059 = 1165589) B1165589
theorem B777089 : Blo 515797 777089 := bstep (se 2 (by rfl) ⟨291408, by rfl⟩ : syracuseStep 777089 = 582817) B582817
theorem B4709261 : Blo 515797 4709261 := bstep (se 3 (by rfl) ⟨882986, by rfl⟩ : syracuseStep 4709261 = 1765973) B1765973
theorem B777107 : Blo 515797 777107 := bstep (se 1 (by rfl) ⟨582830, by rfl⟩ : syracuseStep 777107 = 1165661) B1165661
theorem B777137 : Blo 515797 777137 := bstep (se 2 (by rfl) ⟨291426, by rfl⟩ : syracuseStep 777137 = 582853) B582853
theorem B875441 : Blo 515797 875441 := bstep (se 2 (by rfl) ⟨328290, by rfl⟩ : syracuseStep 875441 = 656581) B656581
theorem B580531 : Blo 515797 580531 := bstep (se 1 (by rfl) ⟨435398, by rfl⟩ : syracuseStep 580531 = 870797) B870797
theorem B777155 : Blo 515797 777155 := bstep (se 1 (by rfl) ⟨582866, by rfl⟩ : syracuseStep 777155 = 1165733) B1165733
theorem B777185 : Blo 515797 777185 := bstep (se 2 (by rfl) ⟨291444, by rfl⟩ : syracuseStep 777185 = 582889) B582889
theorem B1661933 : Blo 515797 1661933 := bstep (se 3 (by rfl) ⟨311612, by rfl⟩ : syracuseStep 1661933 = 623225) B623225
theorem B2481137 : Blo 515797 2481137 := bstep (se 2 (by rfl) ⟨930426, by rfl⟩ : syracuseStep 2481137 = 1860853) B1860853
theorem B777203 : Blo 515797 777203 := bstep (se 1 (by rfl) ⟨582902, by rfl⟩ : syracuseStep 777203 = 1165805) B1165805
theorem B2219021 : Blo 515797 2219021 := bstep (se 3 (by rfl) ⟨416066, by rfl⟩ : syracuseStep 2219021 = 832133) B832133
theorem B777233 : Blo 515797 777233 := bstep (se 2 (by rfl) ⟨291462, by rfl⟩ : syracuseStep 777233 = 582925) B582925
theorem B1104931 : Blo 515797 1104931 := bstep (se 1 (by rfl) ⟨828698, by rfl⟩ : syracuseStep 1104931 = 1657397) B1657397
theorem B777251 : Blo 515797 777251 := bstep (se 1 (by rfl) ⟨582938, by rfl⟩ : syracuseStep 777251 = 1165877) B1165877
theorem B875569 : Blo 515797 875569 := bstep (se 2 (by rfl) ⟨328338, by rfl⟩ : syracuseStep 875569 = 656677) B656677
theorem B777281 : Blo 515797 777281 := bstep (se 2 (by rfl) ⟨291480, by rfl⟩ : syracuseStep 777281 = 582961) B582961
theorem B580675 : Blo 515797 580675 := bstep (se 1 (by rfl) ⟨435506, by rfl⟩ : syracuseStep 580675 = 871013) B871013
theorem B777299 : Blo 515797 777299 := bstep (se 1 (by rfl) ⟨582974, by rfl⟩ : syracuseStep 777299 = 1165949) B1165949
theorem B875603 : Blo 515797 875603 := bstep (se 1 (by rfl) ⟨656702, by rfl⟩ : syracuseStep 875603 = 1313405) B1313405
theorem B777329 : Blo 515797 777329 := bstep (se 2 (by rfl) ⟨291498, by rfl⟩ : syracuseStep 777329 = 582997) B582997
theorem B777347 : Blo 515797 777347 := bstep (se 1 (by rfl) ⟨583010, by rfl⟩ : syracuseStep 777347 = 1166021) B1166021
theorem B777377 : Blo 515797 777377 := bstep (se 2 (by rfl) ⟨291516, by rfl⟩ : syracuseStep 777377 = 583033) B583033
theorem B777395 : Blo 515797 777395 := bstep (se 1 (by rfl) ⟨583046, by rfl⟩ : syracuseStep 777395 = 1166093) B1166093
theorem B777425 : Blo 515797 777425 := bstep (se 2 (by rfl) ⟨291534, by rfl⟩ : syracuseStep 777425 = 583069) B583069
theorem B580819 : Blo 515797 580819 := bstep (se 1 (by rfl) ⟨435614, by rfl⟩ : syracuseStep 580819 = 871229) B871229
theorem B875731 : Blo 515797 875731 := bstep (se 1 (by rfl) ⟨656798, by rfl⟩ : syracuseStep 875731 = 1313597) B1313597
theorem B777443 : Blo 515797 777443 := bstep (se 1 (by rfl) ⟨583082, by rfl⟩ : syracuseStep 777443 = 1166165) B1166165
theorem B777473 : Blo 515797 777473 := bstep (se 2 (by rfl) ⟨291552, by rfl⟩ : syracuseStep 777473 = 583105) B583105
theorem B4414733 : Blo 515797 4414733 := bstep (se 3 (by rfl) ⟨827762, by rfl⟩ : syracuseStep 4414733 = 1655525) B1655525
theorem B777491 : Blo 515797 777491 := bstep (se 1 (by rfl) ⟨583118, by rfl⟩ : syracuseStep 777491 = 1166237) B1166237
theorem B777521 : Blo 515797 777521 := bstep (se 2 (by rfl) ⟨291570, by rfl⟩ : syracuseStep 777521 = 583141) B583141
theorem B777539 : Blo 515797 777539 := bstep (se 1 (by rfl) ⟨583154, by rfl⟩ : syracuseStep 777539 = 1166309) B1166309
theorem B777569 : Blo 515797 777569 := bstep (se 2 (by rfl) ⟨291588, by rfl⟩ : syracuseStep 777569 = 583177) B583177
theorem B875873 : Blo 515797 875873 := bstep (se 2 (by rfl) ⟨328452, by rfl⟩ : syracuseStep 875873 = 656905) B656905
theorem B580963 : Blo 515797 580963 := bstep (se 1 (by rfl) ⟨435722, by rfl⟩ : syracuseStep 580963 = 871445) B871445
theorem B2809187 : Blo 515797 2809187 := bstep (se 1 (by rfl) ⟨2106890, by rfl⟩ : syracuseStep 2809187 = 4213781) B4213781
theorem B777587 : Blo 515797 777587 := bstep (se 1 (by rfl) ⟨583190, by rfl⟩ : syracuseStep 777587 = 1166381) B1166381
theorem B4709773 : Blo 515797 4709773 := bstep (se 3 (by rfl) ⟨883082, by rfl⟩ : syracuseStep 4709773 = 1766165) B1766165
theorem B777617 : Blo 515797 777617 := bstep (se 2 (by rfl) ⟨291606, by rfl⟩ : syracuseStep 777617 = 583213) B583213
theorem B777635 : Blo 515797 777635 := bstep (se 1 (by rfl) ⟨583226, by rfl⟩ : syracuseStep 777635 = 1166453) B1166453
theorem B777665 : Blo 515797 777665 := bstep (se 2 (by rfl) ⟨291624, by rfl⟩ : syracuseStep 777665 = 583249) B583249
theorem B777683 : Blo 515797 777683 := bstep (se 1 (by rfl) ⟨583262, by rfl⟩ : syracuseStep 777683 = 1166525) B1166525
theorem B876001 : Blo 515797 876001 := bstep (se 2 (by rfl) ⟨328500, by rfl⟩ : syracuseStep 876001 = 657001) B657001
theorem B777713 : Blo 515797 777713 := bstep (se 2 (by rfl) ⟨291642, by rfl⟩ : syracuseStep 777713 = 583285) B583285
theorem B581107 : Blo 515797 581107 := bstep (se 1 (by rfl) ⟨435830, by rfl⟩ : syracuseStep 581107 = 871661) B871661
theorem B777731 : Blo 515797 777731 := bstep (se 1 (by rfl) ⟨583298, by rfl⟩ : syracuseStep 777731 = 1166597) B1166597
theorem B876035 : Blo 515797 876035 := bstep (se 1 (by rfl) ⟨657026, by rfl⟩ : syracuseStep 876035 = 1314053) B1314053
theorem B2940421 : Blo 515797 2940421 := bstep (se 4 (by rfl) ⟨275664, by rfl⟩ : syracuseStep 2940421 = 551329) B551329
theorem B777761 : Blo 515797 777761 := bstep (se 2 (by rfl) ⟨291660, by rfl⟩ : syracuseStep 777761 = 583321) B583321
theorem B777779 : Blo 515797 777779 := bstep (se 1 (by rfl) ⟨583334, by rfl⟩ : syracuseStep 777779 = 1166669) B1166669
theorem B777809 : Blo 515797 777809 := bstep (se 2 (by rfl) ⟨291678, by rfl⟩ : syracuseStep 777809 = 583357) B583357
theorem B777827 : Blo 515797 777827 := bstep (se 1 (by rfl) ⟨583370, by rfl⟩ : syracuseStep 777827 = 1166741) B1166741
theorem B777857 : Blo 515797 777857 := bstep (se 2 (by rfl) ⟨291696, by rfl⟩ : syracuseStep 777857 = 583393) B583393
theorem B581251 : Blo 515797 581251 := bstep (se 1 (by rfl) ⟨435938, by rfl⟩ : syracuseStep 581251 = 871877) B871877
theorem B876163 : Blo 515797 876163 := bstep (se 1 (by rfl) ⟨657122, by rfl⟩ : syracuseStep 876163 = 1314245) B1314245
theorem B777875 : Blo 515797 777875 := bstep (se 1 (by rfl) ⟨583406, by rfl⟩ : syracuseStep 777875 = 1166813) B1166813
theorem B777905 : Blo 515797 777905 := bstep (se 2 (by rfl) ⟨291714, by rfl⟩ : syracuseStep 777905 = 583429) B583429
theorem B777923 : Blo 515797 777923 := bstep (se 1 (by rfl) ⟨583442, by rfl⟩ : syracuseStep 777923 = 1166885) B1166885
theorem B777953 : Blo 515797 777953 := bstep (se 2 (by rfl) ⟨291732, by rfl⟩ : syracuseStep 777953 = 583465) B583465
theorem B515811 : Blo 515797 515811 := bstep (se 1 (by rfl) ⟨386858, by rfl⟩ : syracuseStep 515811 = 773717) B773717
theorem B3137251 : Blo 515797 3137251 := bstep (se 1 (by rfl) ⟨2352938, by rfl⟩ : syracuseStep 3137251 = 4705877) B4705877
theorem B1400561 : Blo 515797 1400561 := bstep (se 2 (by rfl) ⟨525210, by rfl⟩ : syracuseStep 1400561 = 1050421) B1050421
theorem B515827 : Blo 515797 515827 := bstep (se 1 (by rfl) ⟨386870, by rfl⟩ : syracuseStep 515827 = 773741) B773741
theorem B777971 : Blo 515797 777971 := bstep (se 1 (by rfl) ⟨583478, by rfl⟩ : syracuseStep 777971 = 1166957) B1166957
theorem B515843 : Blo 515797 515843 := bstep (se 1 (by rfl) ⟨386882, by rfl⟩ : syracuseStep 515843 = 773765) B773765
theorem B778001 : Blo 515797 778001 := bstep (se 2 (by rfl) ⟨291750, by rfl⟩ : syracuseStep 778001 = 583501) B583501
theorem B876305 : Blo 515797 876305 := bstep (se 2 (by rfl) ⟨328614, by rfl⟩ : syracuseStep 876305 = 657229) B657229
theorem B515859 : Blo 515797 515859 := bstep (se 1 (by rfl) ⟨386894, by rfl⟩ : syracuseStep 515859 = 773789) B773789
theorem B581395 : Blo 515797 581395 := bstep (se 1 (by rfl) ⟨436046, by rfl⟩ : syracuseStep 581395 = 872093) B872093
theorem B515875 : Blo 515797 515875 := bstep (se 1 (by rfl) ⟨386906, by rfl⟩ : syracuseStep 515875 = 773813) B773813
theorem B778019 : Blo 515797 778019 := bstep (se 1 (by rfl) ⟨583514, by rfl⟩ : syracuseStep 778019 = 1167029) B1167029
theorem B515891 : Blo 515797 515891 := bstep (se 1 (by rfl) ⟨386918, by rfl⟩ : syracuseStep 515891 = 773837) B773837
theorem B778049 : Blo 515797 778049 := bstep (se 2 (by rfl) ⟨291768, by rfl⟩ : syracuseStep 778049 = 583537) B583537
theorem B515907 : Blo 515797 515907 := bstep (se 1 (by rfl) ⟨386930, by rfl⟩ : syracuseStep 515907 = 773861) B773861
theorem B515923 : Blo 515797 515923 := bstep (se 1 (by rfl) ⟨386942, by rfl⟩ : syracuseStep 515923 = 773885) B773885
theorem B778067 : Blo 515797 778067 := bstep (se 1 (by rfl) ⟨583550, by rfl⟩ : syracuseStep 778067 = 1167101) B1167101
theorem B515939 : Blo 515797 515939 := bstep (se 1 (by rfl) ⟨386954, by rfl⟩ : syracuseStep 515939 = 773909) B773909
theorem B778097 : Blo 515797 778097 := bstep (se 2 (by rfl) ⟨291786, by rfl⟩ : syracuseStep 778097 = 583573) B583573
theorem B515955 : Blo 515797 515955 := bstep (se 1 (by rfl) ⟨386966, by rfl⟩ : syracuseStep 515955 = 773933) B773933
theorem B515971 : Blo 515797 515971 := bstep (se 1 (by rfl) ⟨386978, by rfl⟩ : syracuseStep 515971 = 773957) B773957
theorem B778115 : Blo 515797 778115 := bstep (se 1 (by rfl) ⟨583586, by rfl⟩ : syracuseStep 778115 = 1167173) B1167173
theorem B876433 : Blo 515797 876433 := bstep (se 2 (by rfl) ⟨328662, by rfl⟩ : syracuseStep 876433 = 657325) B657325
theorem B515987 : Blo 515797 515987 := bstep (se 1 (by rfl) ⟨386990, by rfl⟩ : syracuseStep 515987 = 773981) B773981
theorem B778145 : Blo 515797 778145 := bstep (se 2 (by rfl) ⟨291804, by rfl⟩ : syracuseStep 778145 = 583609) B583609
theorem B516003 : Blo 515797 516003 := bstep (se 1 (by rfl) ⟨387002, by rfl⟩ : syracuseStep 516003 = 774005) B774005
theorem B581539 : Blo 515797 581539 := bstep (se 1 (by rfl) ⟨436154, by rfl⟩ : syracuseStep 581539 = 872309) B872309
theorem B516019 : Blo 515797 516019 := bstep (se 1 (by rfl) ⟨387014, by rfl⟩ : syracuseStep 516019 = 774029) B774029
theorem B778163 : Blo 515797 778163 := bstep (se 1 (by rfl) ⟨583622, by rfl⟩ : syracuseStep 778163 = 1167245) B1167245
theorem B876467 : Blo 515797 876467 := bstep (se 1 (by rfl) ⟨657350, by rfl⟩ : syracuseStep 876467 = 1314701) B1314701
theorem B516035 : Blo 515797 516035 := bstep (se 1 (by rfl) ⟨387026, by rfl⟩ : syracuseStep 516035 = 774053) B774053
theorem B778193 : Blo 515797 778193 := bstep (se 2 (by rfl) ⟨291822, by rfl⟩ : syracuseStep 778193 = 583645) B583645
theorem B516051 : Blo 515797 516051 := bstep (se 1 (by rfl) ⟨387038, by rfl⟩ : syracuseStep 516051 = 774077) B774077
theorem B516067 : Blo 515797 516067 := bstep (se 1 (by rfl) ⟨387050, by rfl⟩ : syracuseStep 516067 = 774101) B774101
theorem B778211 : Blo 515797 778211 := bstep (se 1 (by rfl) ⟨583658, by rfl⟩ : syracuseStep 778211 = 1167317) B1167317
theorem B516083 : Blo 515797 516083 := bstep (se 1 (by rfl) ⟨387062, by rfl⟩ : syracuseStep 516083 = 774125) B774125
theorem B778241 : Blo 515797 778241 := bstep (se 2 (by rfl) ⟨291840, by rfl⟩ : syracuseStep 778241 = 583681) B583681
theorem B516099 : Blo 515797 516099 := bstep (se 1 (by rfl) ⟨387074, by rfl⟩ : syracuseStep 516099 = 774149) B774149
theorem B516115 : Blo 515797 516115 := bstep (se 1 (by rfl) ⟨387086, by rfl⟩ : syracuseStep 516115 = 774173) B774173
theorem B778259 : Blo 515797 778259 := bstep (se 1 (by rfl) ⟨583694, by rfl⟩ : syracuseStep 778259 = 1167389) B1167389
theorem B516131 : Blo 515797 516131 := bstep (se 1 (by rfl) ⟨387098, by rfl⟩ : syracuseStep 516131 = 774197) B774197
theorem B2482211 : Blo 515797 2482211 := bstep (se 1 (by rfl) ⟨1861658, by rfl⟩ : syracuseStep 2482211 = 3723317) B3723317
theorem B778289 : Blo 515797 778289 := bstep (se 2 (by rfl) ⟨291858, by rfl⟩ : syracuseStep 778289 = 583717) B583717
theorem B516147 : Blo 515797 516147 := bstep (se 1 (by rfl) ⟨387110, by rfl⟩ : syracuseStep 516147 = 774221) B774221
theorem B581683 : Blo 515797 581683 := bstep (se 1 (by rfl) ⟨436262, by rfl⟩ : syracuseStep 581683 = 872525) B872525
theorem B876595 : Blo 515797 876595 := bstep (se 1 (by rfl) ⟨657446, by rfl⟩ : syracuseStep 876595 = 1314893) B1314893
theorem B516163 : Blo 515797 516163 := bstep (se 1 (by rfl) ⟨387122, by rfl⟩ : syracuseStep 516163 = 774245) B774245
theorem B778307 : Blo 515797 778307 := bstep (se 1 (by rfl) ⟨583730, by rfl⟩ : syracuseStep 778307 = 1167461) B1167461
theorem B516179 : Blo 515797 516179 := bstep (se 1 (by rfl) ⟨387134, by rfl⟩ : syracuseStep 516179 = 774269) B774269
theorem B778337 : Blo 515797 778337 := bstep (se 2 (by rfl) ⟨291876, by rfl⟩ : syracuseStep 778337 = 583753) B583753
theorem B516195 : Blo 515797 516195 := bstep (se 1 (by rfl) ⟨387146, by rfl⟩ : syracuseStep 516195 = 774293) B774293
theorem B516211 : Blo 515797 516211 := bstep (se 1 (by rfl) ⟨387158, by rfl⟩ : syracuseStep 516211 = 774317) B774317
theorem B778355 : Blo 515797 778355 := bstep (se 1 (by rfl) ⟨583766, by rfl⟩ : syracuseStep 778355 = 1167533) B1167533
theorem B516227 : Blo 515797 516227 := bstep (se 1 (by rfl) ⟨387170, by rfl⟩ : syracuseStep 516227 = 774341) B774341
theorem B778385 : Blo 515797 778385 := bstep (se 2 (by rfl) ⟨291894, by rfl⟩ : syracuseStep 778385 = 583789) B583789
theorem B516243 : Blo 515797 516243 := bstep (se 1 (by rfl) ⟨387182, by rfl⟩ : syracuseStep 516243 = 774365) B774365
theorem B516259 : Blo 515797 516259 := bstep (se 1 (by rfl) ⟨387194, by rfl⟩ : syracuseStep 516259 = 774389) B774389
theorem B778403 : Blo 515797 778403 := bstep (se 1 (by rfl) ⟨583802, by rfl⟩ : syracuseStep 778403 = 1167605) B1167605
theorem B516275 : Blo 515797 516275 := bstep (se 1 (by rfl) ⟨387206, by rfl⟩ : syracuseStep 516275 = 774413) B774413
theorem B778433 : Blo 515797 778433 := bstep (se 2 (by rfl) ⟨291912, by rfl⟩ : syracuseStep 778433 = 583825) B583825
theorem B876737 : Blo 515797 876737 := bstep (se 2 (by rfl) ⟨328776, by rfl⟩ : syracuseStep 876737 = 657553) B657553
theorem B516291 : Blo 515797 516291 := bstep (se 1 (by rfl) ⟨387218, by rfl⟩ : syracuseStep 516291 = 774437) B774437
theorem B581827 : Blo 515797 581827 := bstep (se 1 (by rfl) ⟨436370, by rfl⟩ : syracuseStep 581827 = 872741) B872741
theorem B516307 : Blo 515797 516307 := bstep (se 1 (by rfl) ⟨387230, by rfl⟩ : syracuseStep 516307 = 774461) B774461
theorem B778451 : Blo 515797 778451 := bstep (se 1 (by rfl) ⟨583838, by rfl⟩ : syracuseStep 778451 = 1167677) B1167677
theorem B516323 : Blo 515797 516323 := bstep (se 1 (by rfl) ⟨387242, by rfl⟩ : syracuseStep 516323 = 774485) B774485
theorem B778481 : Blo 515797 778481 := bstep (se 2 (by rfl) ⟨291930, by rfl⟩ : syracuseStep 778481 = 583861) B583861
theorem B516339 : Blo 515797 516339 := bstep (se 1 (by rfl) ⟨387254, by rfl⟩ : syracuseStep 516339 = 774509) B774509
theorem B516355 : Blo 515797 516355 := bstep (se 1 (by rfl) ⟨387266, by rfl⟩ : syracuseStep 516355 = 774533) B774533
theorem B778499 : Blo 515797 778499 := bstep (se 1 (by rfl) ⟨583874, by rfl⟩ : syracuseStep 778499 = 1167749) B1167749
theorem B516371 : Blo 515797 516371 := bstep (se 1 (by rfl) ⟨387278, by rfl⟩ : syracuseStep 516371 = 774557) B774557
theorem B778529 : Blo 515797 778529 := bstep (se 2 (by rfl) ⟨291948, by rfl⟩ : syracuseStep 778529 = 583897) B583897
theorem B516387 : Blo 515797 516387 := bstep (se 1 (by rfl) ⟨387290, by rfl⟩ : syracuseStep 516387 = 774581) B774581
theorem B1401133 : Blo 515797 1401133 := bstep (se 3 (by rfl) ⟨262712, by rfl⟩ : syracuseStep 1401133 = 525425) B525425
theorem B516403 : Blo 515797 516403 := bstep (se 1 (by rfl) ⟨387302, by rfl⟩ : syracuseStep 516403 = 774605) B774605
theorem B778547 : Blo 515797 778547 := bstep (se 1 (by rfl) ⟨583910, by rfl⟩ : syracuseStep 778547 = 1167821) B1167821
theorem B876865 : Blo 515797 876865 := bstep (se 2 (by rfl) ⟨328824, by rfl⟩ : syracuseStep 876865 = 657649) B657649
theorem B516419 : Blo 515797 516419 := bstep (se 1 (by rfl) ⟨387314, by rfl⟩ : syracuseStep 516419 = 774629) B774629
theorem B778577 : Blo 515797 778577 := bstep (se 2 (by rfl) ⟨291966, by rfl⟩ : syracuseStep 778577 = 583933) B583933
theorem B516435 : Blo 515797 516435 := bstep (se 1 (by rfl) ⟨387326, by rfl⟩ : syracuseStep 516435 = 774653) B774653
theorem B581971 : Blo 515797 581971 := bstep (se 1 (by rfl) ⟨436478, by rfl⟩ : syracuseStep 581971 = 872957) B872957
theorem B516451 : Blo 515797 516451 := bstep (se 1 (by rfl) ⟨387338, by rfl⟩ : syracuseStep 516451 = 774677) B774677
theorem B778595 : Blo 515797 778595 := bstep (se 1 (by rfl) ⟨583946, by rfl⟩ : syracuseStep 778595 = 1167893) B1167893
theorem B876899 : Blo 515797 876899 := bstep (se 1 (by rfl) ⟨657674, by rfl⟩ : syracuseStep 876899 = 1315349) B1315349
theorem B516467 : Blo 515797 516467 := bstep (se 1 (by rfl) ⟨387350, by rfl⟩ : syracuseStep 516467 = 774701) B774701
theorem B778625 : Blo 515797 778625 := bstep (se 2 (by rfl) ⟨291984, by rfl⟩ : syracuseStep 778625 = 583969) B583969
theorem B516483 : Blo 515797 516483 := bstep (se 1 (by rfl) ⟨387362, by rfl⟩ : syracuseStep 516483 = 774725) B774725
theorem B516499 : Blo 515797 516499 := bstep (se 1 (by rfl) ⟨387374, by rfl⟩ : syracuseStep 516499 = 774749) B774749
theorem B778643 : Blo 515797 778643 := bstep (se 1 (by rfl) ⟨583982, by rfl⟩ : syracuseStep 778643 = 1167965) B1167965
theorem B516515 : Blo 515797 516515 := bstep (se 1 (by rfl) ⟨387386, by rfl⟩ : syracuseStep 516515 = 774773) B774773
theorem B778673 : Blo 515797 778673 := bstep (se 2 (by rfl) ⟨292002, by rfl⟩ : syracuseStep 778673 = 584005) B584005
theorem B516531 : Blo 515797 516531 := bstep (se 1 (by rfl) ⟨387398, by rfl⟩ : syracuseStep 516531 = 774797) B774797
theorem B516547 : Blo 515797 516547 := bstep (se 1 (by rfl) ⟨387410, by rfl⟩ : syracuseStep 516547 = 774821) B774821
theorem B778691 : Blo 515797 778691 := bstep (se 1 (by rfl) ⟨584018, by rfl⟩ : syracuseStep 778691 = 1168037) B1168037
theorem B516563 : Blo 515797 516563 := bstep (se 1 (by rfl) ⟨387422, by rfl⟩ : syracuseStep 516563 = 774845) B774845
theorem B778721 : Blo 515797 778721 := bstep (se 2 (by rfl) ⟨292020, by rfl⟩ : syracuseStep 778721 = 584041) B584041
theorem B516579 : Blo 515797 516579 := bstep (se 1 (by rfl) ⟨387434, by rfl⟩ : syracuseStep 516579 = 774869) B774869
theorem B582115 : Blo 515797 582115 := bstep (se 1 (by rfl) ⟨436586, by rfl⟩ : syracuseStep 582115 = 873173) B873173
theorem B877027 : Blo 515797 877027 := bstep (se 1 (by rfl) ⟨657770, by rfl⟩ : syracuseStep 877027 = 1315541) B1315541
theorem B1991153 : Blo 515797 1991153 := bstep (se 2 (by rfl) ⟨746682, by rfl⟩ : syracuseStep 1991153 = 1493365) B1493365
theorem B1106417 : Blo 515797 1106417 := bstep (se 2 (by rfl) ⟨414906, by rfl⟩ : syracuseStep 1106417 = 829813) B829813
theorem B516595 : Blo 515797 516595 := bstep (se 1 (by rfl) ⟨387446, by rfl⟩ : syracuseStep 516595 = 774893) B774893
theorem B778739 : Blo 515797 778739 := bstep (se 1 (by rfl) ⟨584054, by rfl⟩ : syracuseStep 778739 = 1168109) B1168109
theorem B516611 : Blo 515797 516611 := bstep (se 1 (by rfl) ⟨387458, by rfl⟩ : syracuseStep 516611 = 774917) B774917
theorem B1106435 : Blo 515797 1106435 := bstep (se 1 (by rfl) ⟨829826, by rfl⟩ : syracuseStep 1106435 = 1659653) B1659653
theorem B778769 : Blo 515797 778769 := bstep (se 2 (by rfl) ⟨292038, by rfl⟩ : syracuseStep 778769 = 584077) B584077
theorem B516627 : Blo 515797 516627 := bstep (se 1 (by rfl) ⟨387470, by rfl⟩ : syracuseStep 516627 = 774941) B774941
theorem B516643 : Blo 515797 516643 := bstep (se 1 (by rfl) ⟨387482, by rfl⟩ : syracuseStep 516643 = 774965) B774965
theorem B778787 : Blo 515797 778787 := bstep (se 1 (by rfl) ⟨584090, by rfl⟩ : syracuseStep 778787 = 1168181) B1168181
theorem B516659 : Blo 515797 516659 := bstep (se 1 (by rfl) ⟨387494, by rfl⟩ : syracuseStep 516659 = 774989) B774989
theorem B778817 : Blo 515797 778817 := bstep (se 2 (by rfl) ⟨292056, by rfl⟩ : syracuseStep 778817 = 584113) B584113
theorem B516675 : Blo 515797 516675 := bstep (se 1 (by rfl) ⟨387506, by rfl⟩ : syracuseStep 516675 = 775013) B775013
theorem B516691 : Blo 515797 516691 := bstep (se 1 (by rfl) ⟨387518, by rfl⟩ : syracuseStep 516691 = 775037) B775037
theorem B778835 : Blo 515797 778835 := bstep (se 1 (by rfl) ⟨584126, by rfl⟩ : syracuseStep 778835 = 1168253) B1168253
theorem B516707 : Blo 515797 516707 := bstep (se 1 (by rfl) ⟨387530, by rfl⟩ : syracuseStep 516707 = 775061) B775061
theorem B1401457 : Blo 515797 1401457 := bstep (se 2 (by rfl) ⟨525546, by rfl⟩ : syracuseStep 1401457 = 1051093) B1051093
theorem B778865 : Blo 515797 778865 := bstep (se 2 (by rfl) ⟨292074, by rfl⟩ : syracuseStep 778865 = 584149) B584149
theorem B516723 : Blo 515797 516723 := bstep (se 1 (by rfl) ⟨387542, by rfl⟩ : syracuseStep 516723 = 775085) B775085
theorem B582259 : Blo 515797 582259 := bstep (se 1 (by rfl) ⟨436694, by rfl⟩ : syracuseStep 582259 = 873389) B873389
theorem B516739 : Blo 515797 516739 := bstep (se 1 (by rfl) ⟨387554, by rfl⟩ : syracuseStep 516739 = 775109) B775109
theorem B778883 : Blo 515797 778883 := bstep (se 1 (by rfl) ⟨584162, by rfl⟩ : syracuseStep 778883 = 1168325) B1168325
theorem B11231885 : Blo 515797 11231885 := bstep (se 3 (by rfl) ⟨2105978, by rfl⟩ : syracuseStep 11231885 = 4211957) B4211957
theorem B516755 : Blo 515797 516755 := bstep (se 1 (by rfl) ⟨387566, by rfl⟩ : syracuseStep 516755 = 775133) B775133
theorem B778913 : Blo 515797 778913 := bstep (se 2 (by rfl) ⟨292092, by rfl⟩ : syracuseStep 778913 = 584185) B584185
theorem B516771 : Blo 515797 516771 := bstep (se 1 (by rfl) ⟨387578, by rfl⟩ : syracuseStep 516771 = 775157) B775157
theorem B516787 : Blo 515797 516787 := bstep (se 1 (by rfl) ⟨387590, by rfl⟩ : syracuseStep 516787 = 775181) B775181
theorem B778931 : Blo 515797 778931 := bstep (se 1 (by rfl) ⟨584198, by rfl⟩ : syracuseStep 778931 = 1168397) B1168397
theorem B516803 : Blo 515797 516803 := bstep (se 1 (by rfl) ⟨387602, by rfl⟩ : syracuseStep 516803 = 775205) B775205
theorem B778961 : Blo 515797 778961 := bstep (se 2 (by rfl) ⟨292110, by rfl⟩ : syracuseStep 778961 = 584221) B584221
theorem B516819 : Blo 515797 516819 := bstep (se 1 (by rfl) ⟨387614, by rfl⟩ : syracuseStep 516819 = 775229) B775229
theorem B516835 : Blo 515797 516835 := bstep (se 1 (by rfl) ⟨387626, by rfl⟩ : syracuseStep 516835 = 775253) B775253
theorem B778979 : Blo 515797 778979 := bstep (se 1 (by rfl) ⟨584234, by rfl⟩ : syracuseStep 778979 = 1168469) B1168469
theorem B1663715 : Blo 515797 1663715 := bstep (se 1 (by rfl) ⟨1247786, by rfl⟩ : syracuseStep 1663715 = 2495573) B2495573
theorem B516851 : Blo 515797 516851 := bstep (se 1 (by rfl) ⟨387638, by rfl⟩ : syracuseStep 516851 = 775277) B775277
theorem B779009 : Blo 515797 779009 := bstep (se 2 (by rfl) ⟨292128, by rfl⟩ : syracuseStep 779009 = 584257) B584257
theorem B516867 : Blo 515797 516867 := bstep (se 1 (by rfl) ⟨387650, by rfl⟩ : syracuseStep 516867 = 775301) B775301
theorem B582403 : Blo 515797 582403 := bstep (se 1 (by rfl) ⟨436802, by rfl⟩ : syracuseStep 582403 = 873605) B873605
theorem B516883 : Blo 515797 516883 := bstep (se 1 (by rfl) ⟨387662, by rfl⟩ : syracuseStep 516883 = 775325) B775325
theorem B779027 : Blo 515797 779027 := bstep (se 1 (by rfl) ⟨584270, by rfl⟩ : syracuseStep 779027 = 1168541) B1168541
theorem B516899 : Blo 515797 516899 := bstep (se 1 (by rfl) ⟨387674, by rfl⟩ : syracuseStep 516899 = 775349) B775349
theorem B779057 : Blo 515797 779057 := bstep (se 2 (by rfl) ⟨292146, by rfl⟩ : syracuseStep 779057 = 584293) B584293
theorem B516915 : Blo 515797 516915 := bstep (se 1 (by rfl) ⟨387686, by rfl⟩ : syracuseStep 516915 = 775373) B775373
theorem B516931 : Blo 515797 516931 := bstep (se 1 (by rfl) ⟨387698, by rfl⟩ : syracuseStep 516931 = 775397) B775397
theorem B779075 : Blo 515797 779075 := bstep (se 1 (by rfl) ⟨584306, by rfl⟩ : syracuseStep 779075 = 1168613) B1168613
theorem B516947 : Blo 515797 516947 := bstep (se 1 (by rfl) ⟨387710, by rfl⟩ : syracuseStep 516947 = 775421) B775421
theorem B779105 : Blo 515797 779105 := bstep (se 2 (by rfl) ⟨292164, by rfl⟩ : syracuseStep 779105 = 584329) B584329
theorem B516963 : Blo 515797 516963 := bstep (se 1 (by rfl) ⟨387722, by rfl⟩ : syracuseStep 516963 = 775445) B775445
theorem B516979 : Blo 515797 516979 := bstep (se 1 (by rfl) ⟨387734, by rfl⟩ : syracuseStep 516979 = 775469) B775469
theorem B779123 : Blo 515797 779123 := bstep (se 1 (by rfl) ⟨584342, by rfl⟩ : syracuseStep 779123 = 1168685) B1168685
theorem B516995 : Blo 515797 516995 := bstep (se 1 (by rfl) ⟨387746, by rfl⟩ : syracuseStep 516995 = 775493) B775493
theorem B779153 : Blo 515797 779153 := bstep (se 2 (by rfl) ⟨292182, by rfl⟩ : syracuseStep 779153 = 584365) B584365
theorem B517011 : Blo 515797 517011 := bstep (se 1 (by rfl) ⟨387758, by rfl⟩ : syracuseStep 517011 = 775517) B775517
theorem B582547 : Blo 515797 582547 := bstep (se 1 (by rfl) ⟨436910, by rfl⟩ : syracuseStep 582547 = 873821) B873821
theorem B517027 : Blo 515797 517027 := bstep (se 1 (by rfl) ⟨387770, by rfl⟩ : syracuseStep 517027 = 775541) B775541
theorem B779171 : Blo 515797 779171 := bstep (se 1 (by rfl) ⟨584378, by rfl⟩ : syracuseStep 779171 = 1168757) B1168757
theorem B2614193 : Blo 515797 2614193 := bstep (se 2 (by rfl) ⟨980322, by rfl⟩ : syracuseStep 2614193 = 1960645) B1960645
theorem B517043 : Blo 515797 517043 := bstep (se 1 (by rfl) ⟨387782, by rfl⟩ : syracuseStep 517043 = 775565) B775565
theorem B779201 : Blo 515797 779201 := bstep (se 2 (by rfl) ⟨292200, by rfl⟩ : syracuseStep 779201 = 584401) B584401
theorem B517059 : Blo 515797 517059 := bstep (se 1 (by rfl) ⟨387794, by rfl⟩ : syracuseStep 517059 = 775589) B775589
theorem B517075 : Blo 515797 517075 := bstep (se 1 (by rfl) ⟨387806, by rfl⟩ : syracuseStep 517075 = 775613) B775613
theorem B779219 : Blo 515797 779219 := bstep (se 1 (by rfl) ⟨584414, by rfl⟩ : syracuseStep 779219 = 1168829) B1168829
theorem B517091 : Blo 515797 517091 := bstep (se 1 (by rfl) ⟨387818, by rfl⟩ : syracuseStep 517091 = 775637) B775637
theorem B779249 : Blo 515797 779249 := bstep (se 2 (by rfl) ⟨292218, by rfl⟩ : syracuseStep 779249 = 584437) B584437
theorem B517107 : Blo 515797 517107 := bstep (se 1 (by rfl) ⟨387830, by rfl⟩ : syracuseStep 517107 = 775661) B775661
theorem B517123 : Blo 515797 517123 := bstep (se 1 (by rfl) ⟨387842, by rfl⟩ : syracuseStep 517123 = 775685) B775685
theorem B779267 : Blo 515797 779267 := bstep (se 1 (by rfl) ⟨584450, by rfl⟩ : syracuseStep 779267 = 1168901) B1168901
theorem B517139 : Blo 515797 517139 := bstep (se 1 (by rfl) ⟨387854, by rfl⟩ : syracuseStep 517139 = 775709) B775709
theorem B779297 : Blo 515797 779297 := bstep (se 2 (by rfl) ⟨292236, by rfl⟩ : syracuseStep 779297 = 584473) B584473
theorem B517155 : Blo 515797 517155 := bstep (se 1 (by rfl) ⟨387866, by rfl⟩ : syracuseStep 517155 = 775733) B775733
theorem B582691 : Blo 515797 582691 := bstep (se 1 (by rfl) ⟨437018, by rfl⟩ : syracuseStep 582691 = 874037) B874037
theorem B517171 : Blo 515797 517171 := bstep (se 1 (by rfl) ⟨387878, by rfl⟩ : syracuseStep 517171 = 775757) B775757
theorem B779315 : Blo 515797 779315 := bstep (se 1 (by rfl) ⟨584486, by rfl⟩ : syracuseStep 779315 = 1168973) B1168973
theorem B517187 : Blo 515797 517187 := bstep (se 1 (by rfl) ⟨387890, by rfl⟩ : syracuseStep 517187 = 775781) B775781
theorem B779345 : Blo 515797 779345 := bstep (se 2 (by rfl) ⟨292254, by rfl⟩ : syracuseStep 779345 = 584509) B584509
theorem B517203 : Blo 515797 517203 := bstep (se 1 (by rfl) ⟨387902, by rfl⟩ : syracuseStep 517203 = 775805) B775805
theorem B517219 : Blo 515797 517219 := bstep (se 1 (by rfl) ⟨387914, by rfl⟩ : syracuseStep 517219 = 775829) B775829
theorem B779363 : Blo 515797 779363 := bstep (se 1 (by rfl) ⟨584522, by rfl⟩ : syracuseStep 779363 = 1169045) B1169045
theorem B517235 : Blo 515797 517235 := bstep (se 1 (by rfl) ⟨387926, by rfl⟩ : syracuseStep 517235 = 775853) B775853
theorem B779393 : Blo 515797 779393 := bstep (se 2 (by rfl) ⟨292272, by rfl⟩ : syracuseStep 779393 = 584545) B584545
theorem B517251 : Blo 515797 517251 := bstep (se 1 (by rfl) ⟨387938, by rfl⟩ : syracuseStep 517251 = 775877) B775877
theorem B517267 : Blo 515797 517267 := bstep (se 1 (by rfl) ⟨387950, by rfl⟩ : syracuseStep 517267 = 775901) B775901
theorem B779411 : Blo 515797 779411 := bstep (se 1 (by rfl) ⟨584558, by rfl⟩ : syracuseStep 779411 = 1169117) B1169117
theorem B517283 : Blo 515797 517283 := bstep (se 1 (by rfl) ⟨387962, by rfl⟩ : syracuseStep 517283 = 775925) B775925
theorem B779441 : Blo 515797 779441 := bstep (se 2 (by rfl) ⟨292290, by rfl⟩ : syracuseStep 779441 = 584581) B584581
theorem B517299 : Blo 515797 517299 := bstep (se 1 (by rfl) ⟨387974, by rfl⟩ : syracuseStep 517299 = 775949) B775949
theorem B582835 : Blo 515797 582835 := bstep (se 1 (by rfl) ⟨437126, by rfl⟩ : syracuseStep 582835 = 874253) B874253
theorem B517315 : Blo 515797 517315 := bstep (se 1 (by rfl) ⟨387986, by rfl⟩ : syracuseStep 517315 = 775973) B775973
theorem B779459 : Blo 515797 779459 := bstep (se 1 (by rfl) ⟨584594, by rfl⟩ : syracuseStep 779459 = 1169189) B1169189
theorem B517331 : Blo 515797 517331 := bstep (se 1 (by rfl) ⟨387998, by rfl⟩ : syracuseStep 517331 = 775997) B775997
theorem B779489 : Blo 515797 779489 := bstep (se 2 (by rfl) ⟨292308, by rfl⟩ : syracuseStep 779489 = 584617) B584617
theorem B517347 : Blo 515797 517347 := bstep (se 1 (by rfl) ⟨388010, by rfl⟩ : syracuseStep 517347 = 776021) B776021
theorem B7464163 : Blo 515797 7464163 := bstep (se 1 (by rfl) ⟨5598122, by rfl⟩ : syracuseStep 7464163 = 11196245) B11196245
theorem B517363 : Blo 515797 517363 := bstep (se 1 (by rfl) ⟨388022, by rfl⟩ : syracuseStep 517363 = 776045) B776045
theorem B779507 : Blo 515797 779507 := bstep (se 1 (by rfl) ⟨584630, by rfl⟩ : syracuseStep 779507 = 1169261) B1169261
theorem B517379 : Blo 515797 517379 := bstep (se 1 (by rfl) ⟨388034, by rfl⟩ : syracuseStep 517379 = 776069) B776069
theorem B779537 : Blo 515797 779537 := bstep (se 2 (by rfl) ⟨292326, by rfl⟩ : syracuseStep 779537 = 584653) B584653
theorem B517395 : Blo 515797 517395 := bstep (se 1 (by rfl) ⟨388046, by rfl⟩ : syracuseStep 517395 = 776093) B776093
theorem B517411 : Blo 515797 517411 := bstep (se 1 (by rfl) ⟨388058, by rfl⟩ : syracuseStep 517411 = 776117) B776117
theorem B779555 : Blo 515797 779555 := bstep (se 1 (by rfl) ⟨584666, by rfl⟩ : syracuseStep 779555 = 1169333) B1169333
theorem B517427 : Blo 515797 517427 := bstep (se 1 (by rfl) ⟨388070, by rfl⟩ : syracuseStep 517427 = 776141) B776141
theorem B779585 : Blo 515797 779585 := bstep (se 2 (by rfl) ⟨292344, by rfl⟩ : syracuseStep 779585 = 584689) B584689
theorem B517443 : Blo 515797 517443 := bstep (se 1 (by rfl) ⟨388082, by rfl⟩ : syracuseStep 517443 = 776165) B776165
theorem B582979 : Blo 515797 582979 := bstep (se 1 (by rfl) ⟨437234, by rfl⟩ : syracuseStep 582979 = 874469) B874469
theorem B517459 : Blo 515797 517459 := bstep (se 1 (by rfl) ⟨388094, by rfl⟩ : syracuseStep 517459 = 776189) B776189
theorem B779603 : Blo 515797 779603 := bstep (se 1 (by rfl) ⟨584702, by rfl⟩ : syracuseStep 779603 = 1169405) B1169405
theorem B517475 : Blo 515797 517475 := bstep (se 1 (by rfl) ⟨388106, by rfl⟩ : syracuseStep 517475 = 776213) B776213
theorem B779633 : Blo 515797 779633 := bstep (se 2 (by rfl) ⟨292362, by rfl⟩ : syracuseStep 779633 = 584725) B584725
theorem B517491 : Blo 515797 517491 := bstep (se 1 (by rfl) ⟨388118, by rfl⟩ : syracuseStep 517491 = 776237) B776237
theorem B517507 : Blo 515797 517507 := bstep (se 1 (by rfl) ⟨388130, by rfl⟩ : syracuseStep 517507 = 776261) B776261
theorem B779651 : Blo 515797 779651 := bstep (se 1 (by rfl) ⟨584738, by rfl⟩ : syracuseStep 779651 = 1169477) B1169477
theorem B517523 : Blo 515797 517523 := bstep (se 1 (by rfl) ⟨388142, by rfl⟩ : syracuseStep 517523 = 776285) B776285
theorem B779681 : Blo 515797 779681 := bstep (se 2 (by rfl) ⟨292380, by rfl⟩ : syracuseStep 779681 = 584761) B584761
theorem B517539 : Blo 515797 517539 := bstep (se 1 (by rfl) ⟨388154, by rfl⟩ : syracuseStep 517539 = 776309) B776309
theorem B517555 : Blo 515797 517555 := bstep (se 1 (by rfl) ⟨388166, by rfl⟩ : syracuseStep 517555 = 776333) B776333
theorem B517571 : Blo 515797 517571 := bstep (se 1 (by rfl) ⟨388178, by rfl⟩ : syracuseStep 517571 = 776357) B776357
theorem B2942405 : Blo 515797 2942405 := bstep (se 4 (by rfl) ⟨275850, by rfl⟩ : syracuseStep 2942405 = 551701) B551701
theorem B1861069 : Blo 515797 1861069 := bstep (se 3 (by rfl) ⟨348950, by rfl⟩ : syracuseStep 1861069 = 697901) B697901
theorem B517587 : Blo 515797 517587 := bstep (se 1 (by rfl) ⟨388190, by rfl⟩ : syracuseStep 517587 = 776381) B776381
theorem B583123 : Blo 515797 583123 := bstep (se 1 (by rfl) ⟨437342, by rfl⟩ : syracuseStep 583123 = 874685) B874685
theorem B517603 : Blo 515797 517603 := bstep (se 1 (by rfl) ⟨388202, by rfl⟩ : syracuseStep 517603 = 776405) B776405
theorem B517619 : Blo 515797 517619 := bstep (se 1 (by rfl) ⟨388214, by rfl⟩ : syracuseStep 517619 = 776429) B776429
theorem B517635 : Blo 515797 517635 := bstep (se 1 (by rfl) ⟨388226, by rfl⟩ : syracuseStep 517635 = 776453) B776453
theorem B517651 : Blo 515797 517651 := bstep (se 1 (by rfl) ⟨388238, by rfl⟩ : syracuseStep 517651 = 776477) B776477
theorem B517667 : Blo 515797 517667 := bstep (se 1 (by rfl) ⟨388250, by rfl⟩ : syracuseStep 517667 = 776501) B776501
theorem B517683 : Blo 515797 517683 := bstep (se 1 (by rfl) ⟨388262, by rfl⟩ : syracuseStep 517683 = 776525) B776525
theorem B517699 : Blo 515797 517699 := bstep (se 1 (by rfl) ⟨388274, by rfl⟩ : syracuseStep 517699 = 776549) B776549
theorem B517715 : Blo 515797 517715 := bstep (se 1 (by rfl) ⟨388286, by rfl⟩ : syracuseStep 517715 = 776573) B776573
theorem B517731 : Blo 515797 517731 := bstep (se 1 (by rfl) ⟨388298, by rfl⟩ : syracuseStep 517731 = 776597) B776597
theorem B583267 : Blo 515797 583267 := bstep (se 1 (by rfl) ⟨437450, by rfl⟩ : syracuseStep 583267 = 874901) B874901
theorem B517747 : Blo 515797 517747 := bstep (se 1 (by rfl) ⟨388310, by rfl⟩ : syracuseStep 517747 = 776621) B776621
theorem B517763 : Blo 515797 517763 := bstep (se 1 (by rfl) ⟨388322, by rfl⟩ : syracuseStep 517763 = 776645) B776645
theorem B517779 : Blo 515797 517779 := bstep (se 1 (by rfl) ⟨388334, by rfl⟩ : syracuseStep 517779 = 776669) B776669
theorem B517795 : Blo 515797 517795 := bstep (se 1 (by rfl) ⟨388346, by rfl⟩ : syracuseStep 517795 = 776693) B776693
theorem B517811 : Blo 515797 517811 := bstep (se 1 (by rfl) ⟨388358, by rfl⟩ : syracuseStep 517811 = 776717) B776717
theorem B517827 : Blo 515797 517827 := bstep (se 1 (by rfl) ⟨388370, by rfl⟩ : syracuseStep 517827 = 776741) B776741
theorem B1107665 : Blo 515797 1107665 := bstep (se 2 (by rfl) ⟨415374, by rfl⟩ : syracuseStep 1107665 = 830749) B830749
theorem B517843 : Blo 515797 517843 := bstep (se 1 (by rfl) ⟨388382, by rfl⟩ : syracuseStep 517843 = 776765) B776765
theorem B517859 : Blo 515797 517859 := bstep (se 1 (by rfl) ⟨388394, by rfl⟩ : syracuseStep 517859 = 776789) B776789
theorem B517875 : Blo 515797 517875 := bstep (se 1 (by rfl) ⟨388406, by rfl⟩ : syracuseStep 517875 = 776813) B776813
theorem B583411 : Blo 515797 583411 := bstep (se 1 (by rfl) ⟨437558, by rfl⟩ : syracuseStep 583411 = 875117) B875117
theorem B517891 : Blo 515797 517891 := bstep (se 1 (by rfl) ⟨388418, by rfl⟩ : syracuseStep 517891 = 776837) B776837
theorem B517907 : Blo 515797 517907 := bstep (se 1 (by rfl) ⟨388430, by rfl⟩ : syracuseStep 517907 = 776861) B776861
theorem B517923 : Blo 515797 517923 := bstep (se 1 (by rfl) ⟨388442, by rfl⟩ : syracuseStep 517923 = 776885) B776885
theorem B1664803 : Blo 515797 1664803 := bstep (se 1 (by rfl) ⟨1248602, by rfl⟩ : syracuseStep 1664803 = 2497205) B2497205
theorem B517939 : Blo 515797 517939 := bstep (se 1 (by rfl) ⟨388454, by rfl⟩ : syracuseStep 517939 = 776909) B776909
theorem B9987893 : Blo 515797 9987893 := bstep (se 5 (by rfl) ⟨468182, by rfl⟩ : syracuseStep 9987893 = 936365) B936365
theorem B517955 : Blo 515797 517955 := bstep (se 1 (by rfl) ⟨388466, by rfl⟩ : syracuseStep 517955 = 776933) B776933
theorem B517971 : Blo 515797 517971 := bstep (se 1 (by rfl) ⟨388478, by rfl⟩ : syracuseStep 517971 = 776957) B776957
theorem B517987 : Blo 515797 517987 := bstep (se 1 (by rfl) ⟨388490, by rfl⟩ : syracuseStep 517987 = 776981) B776981
theorem B1402733 : Blo 515797 1402733 := bstep (se 3 (by rfl) ⟨263012, by rfl⟩ : syracuseStep 1402733 = 526025) B526025
theorem B518003 : Blo 515797 518003 := bstep (se 1 (by rfl) ⟨388502, by rfl⟩ : syracuseStep 518003 = 777005) B777005
theorem B518019 : Blo 515797 518019 := bstep (se 1 (by rfl) ⟨388514, by rfl⟩ : syracuseStep 518019 = 777029) B777029
theorem B583555 : Blo 515797 583555 := bstep (se 1 (by rfl) ⟨437666, by rfl⟩ : syracuseStep 583555 = 875333) B875333
theorem B518035 : Blo 515797 518035 := bstep (se 1 (by rfl) ⟨388526, by rfl⟩ : syracuseStep 518035 = 777053) B777053
theorem B518051 : Blo 515797 518051 := bstep (se 1 (by rfl) ⟨388538, by rfl⟩ : syracuseStep 518051 = 777077) B777077
theorem B1664945 : Blo 515797 1664945 := bstep (se 2 (by rfl) ⟨624354, by rfl⟩ : syracuseStep 1664945 = 1248709) B1248709
theorem B518067 : Blo 515797 518067 := bstep (se 1 (by rfl) ⟨388550, by rfl⟩ : syracuseStep 518067 = 777101) B777101
theorem B518083 : Blo 515797 518083 := bstep (se 1 (by rfl) ⟨388562, by rfl⟩ : syracuseStep 518083 = 777125) B777125
theorem B3598285 : Blo 515797 3598285 := bstep (se 3 (by rfl) ⟨674678, by rfl⟩ : syracuseStep 3598285 = 1349357) B1349357
theorem B518099 : Blo 515797 518099 := bstep (se 1 (by rfl) ⟨388574, by rfl⟩ : syracuseStep 518099 = 777149) B777149
theorem B518115 : Blo 515797 518115 := bstep (se 1 (by rfl) ⟨388586, by rfl⟩ : syracuseStep 518115 = 777173) B777173
theorem B518131 : Blo 515797 518131 := bstep (se 1 (by rfl) ⟨388598, by rfl⟩ : syracuseStep 518131 = 777197) B777197
theorem B518147 : Blo 515797 518147 := bstep (se 1 (by rfl) ⟨388610, by rfl⟩ : syracuseStep 518147 = 777221) B777221
theorem B518163 : Blo 515797 518163 := bstep (se 1 (by rfl) ⟨388622, by rfl⟩ : syracuseStep 518163 = 777245) B777245
theorem B583699 : Blo 515797 583699 := bstep (se 1 (by rfl) ⟨437774, by rfl⟩ : syracuseStep 583699 = 875549) B875549
theorem B518179 : Blo 515797 518179 := bstep (se 1 (by rfl) ⟨388634, by rfl⟩ : syracuseStep 518179 = 777269) B777269
theorem B518195 : Blo 515797 518195 := bstep (se 1 (by rfl) ⟨388646, by rfl⟩ : syracuseStep 518195 = 777293) B777293
theorem B518211 : Blo 515797 518211 := bstep (se 1 (by rfl) ⟨388658, by rfl⟩ : syracuseStep 518211 = 777317) B777317
theorem B518227 : Blo 515797 518227 := bstep (se 1 (by rfl) ⟨388670, by rfl⟩ : syracuseStep 518227 = 777341) B777341
theorem B518243 : Blo 515797 518243 := bstep (se 1 (by rfl) ⟨388682, by rfl⟩ : syracuseStep 518243 = 777365) B777365
theorem B518259 : Blo 515797 518259 := bstep (se 1 (by rfl) ⟨388694, by rfl⟩ : syracuseStep 518259 = 777389) B777389
theorem B518275 : Blo 515797 518275 := bstep (se 1 (by rfl) ⟨388706, by rfl⟩ : syracuseStep 518275 = 777413) B777413
theorem B518291 : Blo 515797 518291 := bstep (se 1 (by rfl) ⟨388718, by rfl⟩ : syracuseStep 518291 = 777437) B777437
theorem B518307 : Blo 515797 518307 := bstep (se 1 (by rfl) ⟨388730, by rfl⟩ : syracuseStep 518307 = 777461) B777461
theorem B583843 : Blo 515797 583843 := bstep (se 1 (by rfl) ⟨437882, by rfl⟩ : syracuseStep 583843 = 875765) B875765
theorem B518323 : Blo 515797 518323 := bstep (se 1 (by rfl) ⟨388742, by rfl⟩ : syracuseStep 518323 = 777485) B777485
theorem B551107 : Blo 515797 551107 := bstep (se 1 (by rfl) ⟨413330, by rfl⟩ : syracuseStep 551107 = 826661) B826661
theorem B518339 : Blo 515797 518339 := bstep (se 1 (by rfl) ⟨388754, by rfl⟩ : syracuseStep 518339 = 777509) B777509
theorem B1009873 : Blo 515797 1009873 := bstep (se 2 (by rfl) ⟨378702, by rfl⟩ : syracuseStep 1009873 = 757405) B757405
theorem B518355 : Blo 515797 518355 := bstep (se 1 (by rfl) ⟨388766, by rfl⟩ : syracuseStep 518355 = 777533) B777533
theorem B518371 : Blo 515797 518371 := bstep (se 1 (by rfl) ⟨388778, by rfl⟩ : syracuseStep 518371 = 777557) B777557
theorem B518387 : Blo 515797 518387 := bstep (se 1 (by rfl) ⟨388790, by rfl⟩ : syracuseStep 518387 = 777581) B777581
theorem B518403 : Blo 515797 518403 := bstep (se 1 (by rfl) ⟨388802, by rfl⟩ : syracuseStep 518403 = 777605) B777605
theorem B518419 : Blo 515797 518419 := bstep (se 1 (by rfl) ⟨388814, by rfl⟩ : syracuseStep 518419 = 777629) B777629
theorem B518435 : Blo 515797 518435 := bstep (se 1 (by rfl) ⟨388826, by rfl⟩ : syracuseStep 518435 = 777653) B777653
theorem B518451 : Blo 515797 518451 := bstep (se 1 (by rfl) ⟨388838, by rfl⟩ : syracuseStep 518451 = 777677) B777677
theorem B583987 : Blo 515797 583987 := bstep (se 1 (by rfl) ⟨437990, by rfl⟩ : syracuseStep 583987 = 875981) B875981
theorem B518467 : Blo 515797 518467 := bstep (se 1 (by rfl) ⟨388850, by rfl⟩ : syracuseStep 518467 = 777701) B777701
theorem B518483 : Blo 515797 518483 := bstep (se 1 (by rfl) ⟨388862, by rfl⟩ : syracuseStep 518483 = 777725) B777725
theorem B2615651 : Blo 515797 2615651 := bstep (se 1 (by rfl) ⟨1961738, by rfl⟩ : syracuseStep 2615651 = 3923477) B3923477
theorem B518499 : Blo 515797 518499 := bstep (se 1 (by rfl) ⟨388874, by rfl⟩ : syracuseStep 518499 = 777749) B777749
theorem B518515 : Blo 515797 518515 := bstep (se 1 (by rfl) ⟨388886, by rfl⟩ : syracuseStep 518515 = 777773) B777773
theorem B518531 : Blo 515797 518531 := bstep (se 1 (by rfl) ⟨388898, by rfl⟩ : syracuseStep 518531 = 777797) B777797
theorem B518547 : Blo 515797 518547 := bstep (se 1 (by rfl) ⟨388910, by rfl⟩ : syracuseStep 518547 = 777821) B777821
theorem B518563 : Blo 515797 518563 := bstep (se 1 (by rfl) ⟨388922, by rfl⟩ : syracuseStep 518563 = 777845) B777845
theorem B518579 : Blo 515797 518579 := bstep (se 1 (by rfl) ⟨388934, by rfl⟩ : syracuseStep 518579 = 777869) B777869
theorem B1468867 : Blo 515797 1468867 := bstep (se 1 (by rfl) ⟨1101650, by rfl⟩ : syracuseStep 1468867 = 2203301) B2203301
theorem B518595 : Blo 515797 518595 := bstep (se 1 (by rfl) ⟨388946, by rfl⟩ : syracuseStep 518595 = 777893) B777893
theorem B584131 : Blo 515797 584131 := bstep (se 1 (by rfl) ⟨438098, by rfl⟩ : syracuseStep 584131 = 876197) B876197
theorem B518611 : Blo 515797 518611 := bstep (se 1 (by rfl) ⟨388958, by rfl⟩ : syracuseStep 518611 = 777917) B777917
theorem B518627 : Blo 515797 518627 := bstep (se 1 (by rfl) ⟨388970, by rfl⟩ : syracuseStep 518627 = 777941) B777941
theorem B1960433 : Blo 515797 1960433 := bstep (se 2 (by rfl) ⟨735162, by rfl⟩ : syracuseStep 1960433 = 1470325) B1470325
theorem B1010161 : Blo 515797 1010161 := bstep (se 2 (by rfl) ⟨378810, by rfl⟩ : syracuseStep 1010161 = 757621) B757621
theorem B518643 : Blo 515797 518643 := bstep (se 1 (by rfl) ⟨388982, by rfl⟩ : syracuseStep 518643 = 777965) B777965
theorem B518659 : Blo 515797 518659 := bstep (se 1 (by rfl) ⟨388994, by rfl⟩ : syracuseStep 518659 = 777989) B777989
theorem B1239569 : Blo 515797 1239569 := bstep (se 2 (by rfl) ⟨464838, by rfl⟩ : syracuseStep 1239569 = 929677) B929677
theorem B518675 : Blo 515797 518675 := bstep (se 1 (by rfl) ⟨389006, by rfl⟩ : syracuseStep 518675 = 778013) B778013
theorem B518691 : Blo 515797 518691 := bstep (se 1 (by rfl) ⟨389018, by rfl⟩ : syracuseStep 518691 = 778037) B778037
theorem B518707 : Blo 515797 518707 := bstep (se 1 (by rfl) ⟨389030, by rfl⟩ : syracuseStep 518707 = 778061) B778061
theorem B518723 : Blo 515797 518723 := bstep (se 1 (by rfl) ⟨389042, by rfl⟩ : syracuseStep 518723 = 778085) B778085
theorem B518739 : Blo 515797 518739 := bstep (se 1 (by rfl) ⟨389054, by rfl⟩ : syracuseStep 518739 = 778109) B778109
theorem B584275 : Blo 515797 584275 := bstep (se 1 (by rfl) ⟨438206, by rfl⟩ : syracuseStep 584275 = 876413) B876413
theorem B518755 : Blo 515797 518755 := bstep (se 1 (by rfl) ⟨389066, by rfl⟩ : syracuseStep 518755 = 778133) B778133
theorem B518771 : Blo 515797 518771 := bstep (se 1 (by rfl) ⟨389078, by rfl⟩ : syracuseStep 518771 = 778157) B778157
theorem B518787 : Blo 515797 518787 := bstep (se 1 (by rfl) ⟨389090, by rfl⟩ : syracuseStep 518787 = 778181) B778181
theorem B518803 : Blo 515797 518803 := bstep (se 1 (by rfl) ⟨389102, by rfl⟩ : syracuseStep 518803 = 778205) B778205
theorem B518819 : Blo 515797 518819 := bstep (se 1 (by rfl) ⟨389114, by rfl⟩ : syracuseStep 518819 = 778229) B778229
theorem B518835 : Blo 515797 518835 := bstep (se 1 (by rfl) ⟨389126, by rfl⟩ : syracuseStep 518835 = 778253) B778253
theorem B518851 : Blo 515797 518851 := bstep (se 1 (by rfl) ⟨389138, by rfl⟩ : syracuseStep 518851 = 778277) B778277
theorem B518867 : Blo 515797 518867 := bstep (se 1 (by rfl) ⟨389150, by rfl⟩ : syracuseStep 518867 = 778301) B778301
theorem B518883 : Blo 515797 518883 := bstep (se 1 (by rfl) ⟨389162, by rfl⟩ : syracuseStep 518883 = 778325) B778325
theorem B584419 : Blo 515797 584419 := bstep (se 1 (by rfl) ⟨438314, by rfl⟩ : syracuseStep 584419 = 876629) B876629
theorem B518899 : Blo 515797 518899 := bstep (se 1 (by rfl) ⟨389174, by rfl⟩ : syracuseStep 518899 = 778349) B778349
theorem B518915 : Blo 515797 518915 := bstep (se 1 (by rfl) ⟨389186, by rfl⟩ : syracuseStep 518915 = 778373) B778373
theorem B518931 : Blo 515797 518931 := bstep (se 1 (by rfl) ⟨389198, by rfl⟩ : syracuseStep 518931 = 778397) B778397
theorem B518947 : Blo 515797 518947 := bstep (se 1 (by rfl) ⟨389210, by rfl⟩ : syracuseStep 518947 = 778421) B778421
theorem B518963 : Blo 515797 518963 := bstep (se 1 (by rfl) ⟨389222, by rfl⟩ : syracuseStep 518963 = 778445) B778445
theorem B518979 : Blo 515797 518979 := bstep (se 1 (by rfl) ⟨389234, by rfl⟩ : syracuseStep 518979 = 778469) B778469
theorem B3533645 : Blo 515797 3533645 := bstep (se 3 (by rfl) ⟨662558, by rfl⟩ : syracuseStep 3533645 = 1325117) B1325117
theorem B518995 : Blo 515797 518995 := bstep (se 1 (by rfl) ⟨389246, by rfl⟩ : syracuseStep 518995 = 778493) B778493
theorem B519011 : Blo 515797 519011 := bstep (se 1 (by rfl) ⟨389258, by rfl⟩ : syracuseStep 519011 = 778517) B778517
theorem B519027 : Blo 515797 519027 := bstep (se 1 (by rfl) ⟨389270, by rfl⟩ : syracuseStep 519027 = 778541) B778541
theorem B584563 : Blo 515797 584563 := bstep (se 1 (by rfl) ⟨438422, by rfl⟩ : syracuseStep 584563 = 876845) B876845
theorem B519043 : Blo 515797 519043 := bstep (se 1 (by rfl) ⟨389282, by rfl⟩ : syracuseStep 519043 = 778565) B778565
theorem B519059 : Blo 515797 519059 := bstep (se 1 (by rfl) ⟨389294, by rfl⟩ : syracuseStep 519059 = 778589) B778589
theorem B519075 : Blo 515797 519075 := bstep (se 1 (by rfl) ⟨389306, by rfl⟩ : syracuseStep 519075 = 778613) B778613
theorem B519091 : Blo 515797 519091 := bstep (se 1 (by rfl) ⟨389318, by rfl⟩ : syracuseStep 519091 = 778637) B778637
theorem B519107 : Blo 515797 519107 := bstep (se 1 (by rfl) ⟨389330, by rfl⟩ : syracuseStep 519107 = 778661) B778661
theorem B519123 : Blo 515797 519123 := bstep (se 1 (by rfl) ⟨389342, by rfl⟩ : syracuseStep 519123 = 778685) B778685
theorem B519139 : Blo 515797 519139 := bstep (se 1 (by rfl) ⟨389354, by rfl⟩ : syracuseStep 519139 = 778709) B778709
theorem B748531 : Blo 515797 748531 := bstep (se 1 (by rfl) ⟨561398, by rfl⟩ : syracuseStep 748531 = 1122797) B1122797
theorem B519155 : Blo 515797 519155 := bstep (se 1 (by rfl) ⟨389366, by rfl⟩ : syracuseStep 519155 = 778733) B778733
theorem B519171 : Blo 515797 519171 := bstep (se 1 (by rfl) ⟨389378, by rfl⟩ : syracuseStep 519171 = 778757) B778757
theorem B584707 : Blo 515797 584707 := bstep (se 1 (by rfl) ⟨438530, by rfl⟩ : syracuseStep 584707 = 877061) B877061
theorem B519187 : Blo 515797 519187 := bstep (se 1 (by rfl) ⟨389390, by rfl⟩ : syracuseStep 519187 = 778781) B778781
theorem B519203 : Blo 515797 519203 := bstep (se 1 (by rfl) ⟨389402, by rfl⟩ : syracuseStep 519203 = 778805) B778805
theorem B519219 : Blo 515797 519219 := bstep (se 1 (by rfl) ⟨389414, by rfl⟩ : syracuseStep 519219 = 778829) B778829
theorem B519235 : Blo 515797 519235 := bstep (se 1 (by rfl) ⟨389426, by rfl⟩ : syracuseStep 519235 = 778853) B778853
theorem B519251 : Blo 515797 519251 := bstep (se 1 (by rfl) ⟨389438, by rfl⟩ : syracuseStep 519251 = 778877) B778877
theorem B519267 : Blo 515797 519267 := bstep (se 1 (by rfl) ⟨389450, by rfl⟩ : syracuseStep 519267 = 778901) B778901
theorem B519283 : Blo 515797 519283 := bstep (se 1 (by rfl) ⟨389462, by rfl⟩ : syracuseStep 519283 = 778925) B778925
theorem B519299 : Blo 515797 519299 := bstep (se 1 (by rfl) ⟨389474, by rfl⟩ : syracuseStep 519299 = 778949) B778949
theorem B2616461 : Blo 515797 2616461 := bstep (se 3 (by rfl) ⟨490586, by rfl⟩ : syracuseStep 2616461 = 981173) B981173
theorem B519315 : Blo 515797 519315 := bstep (se 1 (by rfl) ⟨389486, by rfl⟩ : syracuseStep 519315 = 778973) B778973
theorem B519331 : Blo 515797 519331 := bstep (se 1 (by rfl) ⟨389498, by rfl⟩ : syracuseStep 519331 = 778997) B778997
theorem B552115 : Blo 515797 552115 := bstep (se 1 (by rfl) ⟨414086, by rfl⟩ : syracuseStep 552115 = 828173) B828173
theorem B519347 : Blo 515797 519347 := bstep (se 1 (by rfl) ⟨389510, by rfl⟩ : syracuseStep 519347 = 779021) B779021
theorem B519363 : Blo 515797 519363 := bstep (se 1 (by rfl) ⟨389522, by rfl⟩ : syracuseStep 519363 = 779045) B779045
theorem B519379 : Blo 515797 519379 := bstep (se 1 (by rfl) ⟨389534, by rfl⟩ : syracuseStep 519379 = 779069) B779069
theorem B1109219 : Blo 515797 1109219 := bstep (se 1 (by rfl) ⟨831914, by rfl⟩ : syracuseStep 1109219 = 1663829) B1663829
theorem B519395 : Blo 515797 519395 := bstep (se 1 (by rfl) ⟨389546, by rfl⟩ : syracuseStep 519395 = 779093) B779093
theorem B1305841 : Blo 515797 1305841 := bstep (se 2 (by rfl) ⟨489690, by rfl⟩ : syracuseStep 1305841 = 979381) B979381
theorem B519411 : Blo 515797 519411 := bstep (se 1 (by rfl) ⟨389558, by rfl⟩ : syracuseStep 519411 = 779117) B779117
theorem B519427 : Blo 515797 519427 := bstep (se 1 (by rfl) ⟨389570, by rfl⟩ : syracuseStep 519427 = 779141) B779141
theorem B1240337 : Blo 515797 1240337 := bstep (se 2 (by rfl) ⟨465126, by rfl⟩ : syracuseStep 1240337 = 930253) B930253
theorem B519443 : Blo 515797 519443 := bstep (se 1 (by rfl) ⟨389582, by rfl⟩ : syracuseStep 519443 = 779165) B779165
theorem B519459 : Blo 515797 519459 := bstep (se 1 (by rfl) ⟨389594, by rfl⟩ : syracuseStep 519459 = 779189) B779189
theorem B519475 : Blo 515797 519475 := bstep (se 1 (by rfl) ⟨389606, by rfl⟩ : syracuseStep 519475 = 779213) B779213
theorem B519491 : Blo 515797 519491 := bstep (se 1 (by rfl) ⟨389618, by rfl⟩ : syracuseStep 519491 = 779237) B779237
theorem B3927365 : Blo 515797 3927365 := bstep (se 4 (by rfl) ⟨368190, by rfl⟩ : syracuseStep 3927365 = 736381) B736381
theorem B519507 : Blo 515797 519507 := bstep (se 1 (by rfl) ⟨389630, by rfl⟩ : syracuseStep 519507 = 779261) B779261
theorem B519523 : Blo 515797 519523 := bstep (se 1 (by rfl) ⟨389642, by rfl⟩ : syracuseStep 519523 = 779285) B779285
theorem B519539 : Blo 515797 519539 := bstep (se 1 (by rfl) ⟨389654, by rfl⟩ : syracuseStep 519539 = 779309) B779309
theorem B519555 : Blo 515797 519555 := bstep (se 1 (by rfl) ⟨389666, by rfl⟩ : syracuseStep 519555 = 779333) B779333
theorem B519571 : Blo 515797 519571 := bstep (se 1 (by rfl) ⟨389678, by rfl⟩ : syracuseStep 519571 = 779357) B779357
theorem B519587 : Blo 515797 519587 := bstep (se 1 (by rfl) ⟨389690, by rfl⟩ : syracuseStep 519587 = 779381) B779381
theorem B519603 : Blo 515797 519603 := bstep (se 1 (by rfl) ⟨389702, by rfl⟩ : syracuseStep 519603 = 779405) B779405
theorem B519619 : Blo 515797 519619 := bstep (se 1 (by rfl) ⟨389714, by rfl⟩ : syracuseStep 519619 = 779429) B779429
theorem B519635 : Blo 515797 519635 := bstep (se 1 (by rfl) ⟨389726, by rfl⟩ : syracuseStep 519635 = 779453) B779453
theorem B519651 : Blo 515797 519651 := bstep (se 1 (by rfl) ⟨389738, by rfl⟩ : syracuseStep 519651 = 779477) B779477
theorem B519667 : Blo 515797 519667 := bstep (se 1 (by rfl) ⟨389750, by rfl⟩ : syracuseStep 519667 = 779501) B779501
theorem B1306115 : Blo 515797 1306115 := bstep (se 1 (by rfl) ⟨979586, by rfl⟩ : syracuseStep 1306115 = 1959173) B1959173
theorem B519683 : Blo 515797 519683 := bstep (se 1 (by rfl) ⟨389762, by rfl⟩ : syracuseStep 519683 = 779525) B779525
theorem B519699 : Blo 515797 519699 := bstep (se 1 (by rfl) ⟨389774, by rfl⟩ : syracuseStep 519699 = 779549) B779549
theorem B519715 : Blo 515797 519715 := bstep (se 1 (by rfl) ⟨389786, by rfl⟩ : syracuseStep 519715 = 779573) B779573
theorem B749107 : Blo 515797 749107 := bstep (se 1 (by rfl) ⟨561830, by rfl⟩ : syracuseStep 749107 = 1123661) B1123661
theorem B519731 : Blo 515797 519731 := bstep (se 1 (by rfl) ⟨389798, by rfl⟩ : syracuseStep 519731 = 779597) B779597
theorem B519747 : Blo 515797 519747 := bstep (se 1 (by rfl) ⟨389810, by rfl⟩ : syracuseStep 519747 = 779621) B779621
theorem B519763 : Blo 515797 519763 := bstep (se 1 (by rfl) ⟨389822, by rfl⟩ : syracuseStep 519763 = 779645) B779645
theorem B519779 : Blo 515797 519779 := bstep (se 1 (by rfl) ⟨389834, by rfl⟩ : syracuseStep 519779 = 779669) B779669
theorem B519795 : Blo 515797 519795 := bstep (se 1 (by rfl) ⟨389846, by rfl⟩ : syracuseStep 519795 = 779693) B779693
theorem B1306307 : Blo 515797 1306307 := bstep (se 1 (by rfl) ⟨979730, by rfl⟩ : syracuseStep 1306307 = 1959461) B1959461
theorem B552739 : Blo 515797 552739 := bstep (se 1 (by rfl) ⟨414554, by rfl⟩ : syracuseStep 552739 = 829109) B829109
theorem B1470257 : Blo 515797 1470257 := bstep (se 2 (by rfl) ⟨551346, by rfl⟩ : syracuseStep 1470257 = 1102693) B1102693
theorem B1961891 : Blo 515797 1961891 := bstep (se 1 (by rfl) ⟨1471418, by rfl⟩ : syracuseStep 1961891 = 2942837) B2942837
theorem B4321421 : Blo 515797 4321421 := bstep (se 3 (by rfl) ⟨810266, by rfl⟩ : syracuseStep 4321421 = 1620533) B1620533
theorem B2977955 : Blo 515797 2977955 := bstep (se 1 (by rfl) ⟨2233466, by rfl⟩ : syracuseStep 2977955 = 4466933) B4466933
theorem B979427 : Blo 515797 979427 := bstep (se 1 (by rfl) ⟨734570, by rfl⟩ : syracuseStep 979427 = 1469141) B1469141
theorem B1307249 : Blo 515797 1307249 := bstep (se 2 (by rfl) ⟨490218, by rfl⟩ : syracuseStep 1307249 = 980437) B980437
theorem B1307299 : Blo 515797 1307299 := bstep (se 1 (by rfl) ⟨980474, by rfl⟩ : syracuseStep 1307299 = 1960949) B1960949
theorem B1471213 : Blo 515797 1471213 := bstep (se 3 (by rfl) ⟨275852, by rfl⟩ : syracuseStep 1471213 = 551705) B551705
theorem B979715 : Blo 515797 979715 := bstep (se 1 (by rfl) ⟨734786, by rfl⟩ : syracuseStep 979715 = 1469573) B1469573
theorem B1307441 : Blo 515797 1307441 := bstep (se 2 (by rfl) ⟨490290, by rfl⟩ : syracuseStep 1307441 = 980581) B980581
theorem B1962893 : Blo 515797 1962893 := bstep (se 3 (by rfl) ⟨368042, by rfl⟩ : syracuseStep 1962893 = 736085) B736085
theorem B1471441 : Blo 515797 1471441 := bstep (se 2 (by rfl) ⟨551790, by rfl⟩ : syracuseStep 1471441 = 1103581) B1103581
theorem B1471601 : Blo 515797 1471601 := bstep (se 2 (by rfl) ⟨551850, by rfl⟩ : syracuseStep 1471601 = 1103701) B1103701
theorem B2946253 : Blo 515797 2946253 := bstep (se 3 (by rfl) ⟨552422, by rfl⟩ : syracuseStep 2946253 = 1104845) B1104845
theorem B1471715 : Blo 515797 1471715 := bstep (se 1 (by rfl) ⟨1103786, by rfl⟩ : syracuseStep 1471715 = 2207573) B2207573
theorem B554627 : Blo 515797 554627 := bstep (se 1 (by rfl) ⟨415970, by rfl⟩ : syracuseStep 554627 = 831941) B831941
theorem B980657 : Blo 515797 980657 := bstep (se 2 (by rfl) ⟨367746, by rfl⟩ : syracuseStep 980657 = 735493) B735493
theorem B6715061 : Blo 515797 6715061 := bstep (se 5 (by rfl) ⟨314768, by rfl⟩ : syracuseStep 6715061 = 629537) B629537
theorem B1308433 : Blo 515797 1308433 := bstep (se 2 (by rfl) ⟨490662, by rfl⟩ : syracuseStep 1308433 = 981325) B981325
theorem B653123 : Blo 515797 653123 := bstep (se 1 (by rfl) ⟨489842, by rfl⟩ : syracuseStep 653123 = 979685) B979685
theorem B1800035 : Blo 515797 1800035 := bstep (se 1 (by rfl) ⟨1350026, by rfl⟩ : syracuseStep 1800035 = 2700053) B2700053
theorem B1767341 : Blo 515797 1767341 := bstep (se 3 (by rfl) ⟨331376, by rfl⟩ : syracuseStep 1767341 = 662753) B662753
theorem B2619377 : Blo 515797 2619377 := bstep (se 2 (by rfl) ⟨982266, by rfl⟩ : syracuseStep 2619377 = 1964533) B1964533
theorem B1308707 : Blo 515797 1308707 := bstep (se 1 (by rfl) ⟨981530, by rfl⟩ : syracuseStep 1308707 = 1963061) B1963061
theorem B784561 : Blo 515797 784561 := bstep (se 2 (by rfl) ⟨294210, by rfl⟩ : syracuseStep 784561 = 588421) B588421
theorem B1472717 : Blo 515797 1472717 := bstep (se 3 (by rfl) ⟨276134, by rfl⟩ : syracuseStep 1472717 = 552269) B552269
theorem B784609 : Blo 515797 784609 := bstep (se 2 (by rfl) ⟨294228, by rfl⟩ : syracuseStep 784609 = 588457) B588457
theorem B1308899 : Blo 515797 1308899 := bstep (se 1 (by rfl) ⟨981674, by rfl⟩ : syracuseStep 1308899 = 1963349) B1963349
theorem B1472899 : Blo 515797 1472899 := bstep (se 1 (by rfl) ⟨1104674, by rfl⟩ : syracuseStep 1472899 = 2209349) B2209349
theorem B653827 : Blo 515797 653827 := bstep (se 1 (by rfl) ⟨490370, by rfl⟩ : syracuseStep 653827 = 980741) B980741
theorem B2521613 : Blo 515797 2521613 := bstep (se 3 (by rfl) ⟨472802, by rfl⟩ : syracuseStep 2521613 = 945605) B945605
theorem B621091 : Blo 515797 621091 := bstep (se 1 (by rfl) ⟨465818, by rfl⟩ : syracuseStep 621091 = 931637) B931637
theorem B1473059 : Blo 515797 1473059 := bstep (se 1 (by rfl) ⟨1104794, by rfl⟩ : syracuseStep 1473059 = 2209589) B2209589
theorem B981553 : Blo 515797 981553 := bstep (se 2 (by rfl) ⟨368082, by rfl⟩ : syracuseStep 981553 = 736165) B736165
theorem B653923 : Blo 515797 653923 := bstep (se 1 (by rfl) ⟨490442, by rfl⟩ : syracuseStep 653923 = 980885) B980885
theorem B981713 : Blo 515797 981713 := bstep (se 2 (by rfl) ⟨368142, by rfl⟩ : syracuseStep 981713 = 736285) B736285
theorem B1965005 : Blo 515797 1965005 := bstep (se 3 (by rfl) ⟨368438, by rfl⟩ : syracuseStep 1965005 = 736877) B736877
theorem B654419 : Blo 515797 654419 := bstep (se 1 (by rfl) ⟨490814, by rfl⟩ : syracuseStep 654419 = 981629) B981629
theorem B982115 : Blo 515797 982115 := bstep (se 1 (by rfl) ⟨736586, by rfl⟩ : syracuseStep 982115 = 1473173) B1473173
theorem B2948237 : Blo 515797 2948237 := bstep (se 3 (by rfl) ⟨552794, by rfl⟩ : syracuseStep 2948237 = 1105589) B1105589
theorem B1309841 : Blo 515797 1309841 := bstep (se 2 (by rfl) ⟨491190, by rfl⟩ : syracuseStep 1309841 = 982381) B982381
theorem B1309891 : Blo 515797 1309891 := bstep (se 1 (by rfl) ⟨982418, by rfl⟩ : syracuseStep 1309891 = 1964837) B1964837
theorem B3308849 : Blo 515797 3308849 := bstep (se 2 (by rfl) ⟨1240818, by rfl⟩ : syracuseStep 3308849 = 2481637) B2481637
theorem B1310033 : Blo 515797 1310033 := bstep (se 2 (by rfl) ⟨491262, by rfl⟩ : syracuseStep 1310033 = 982525) B982525
theorem B2620835 : Blo 515797 2620835 := bstep (se 1 (by rfl) ⟨1965626, by rfl⟩ : syracuseStep 2620835 = 3931253) B3931253
theorem B1474129 : Blo 515797 1474129 := bstep (se 2 (by rfl) ⟨552798, by rfl⟩ : syracuseStep 1474129 = 1105597) B1105597
theorem B1965809 : Blo 515797 1965809 := bstep (se 2 (by rfl) ⟨737178, by rfl⟩ : syracuseStep 1965809 = 1474357) B1474357
theorem B655123 : Blo 515797 655123 := bstep (se 1 (by rfl) ⟨491342, by rfl⟩ : syracuseStep 655123 = 982685) B982685
theorem B655219 : Blo 515797 655219 := bstep (se 1 (by rfl) ⟨491414, by rfl⟩ : syracuseStep 655219 = 982829) B982829
theorem B983011 : Blo 515797 983011 := bstep (se 1 (by rfl) ⟨737258, by rfl⟩ : syracuseStep 983011 = 1474517) B1474517
theorem B1802225 : Blo 515797 1802225 := bstep (se 2 (by rfl) ⟨675834, by rfl⟩ : syracuseStep 1802225 = 1351669) B1351669
theorem B3932225 : Blo 515797 3932225 := bstep (se 2 (by rfl) ⟨1474584, by rfl⟩ : syracuseStep 3932225 = 2949169) B2949169
theorem B655447 : Blo 515797 655447 := bstep (se 1 (by rfl) ⟨491585, by rfl⟩ : syracuseStep 655447 = 983171) B983171
theorem B6619229 : Blo 515797 6619229 := bstep (se 3 (by rfl) ⟨1241105, by rfl⟩ : syracuseStep 6619229 = 2482211) B2482211
theorem B786763 : Blo 515797 786763 := bstep (se 1 (by rfl) ⟨590072, by rfl⟩ : syracuseStep 786763 = 1180145) B1180145
theorem B1868177 : Blo 515797 1868177 := bstep (se 2 (by rfl) ⟨700566, by rfl⟩ : syracuseStep 1868177 = 1401133) B1401133
theorem B885259 : Blo 515797 885259 := bstep (se 1 (by rfl) ⟨663944, by rfl⟩ : syracuseStep 885259 = 1327889) B1327889
theorem B2621969 : Blo 515797 2621969 := bstep (se 2 (by rfl) ⟨983238, by rfl⟩ : syracuseStep 2621969 = 1966477) B1966477
theorem B1245719 : Blo 515797 1245719 := bstep (se 1 (by rfl) ⟨934289, by rfl⟩ : syracuseStep 1245719 = 1868579) B1868579
theorem B983603 : Blo 515797 983603 := bstep (se 1 (by rfl) ⟨737702, by rfl⟩ : syracuseStep 983603 = 1475405) B1475405
theorem B2622131 : Blo 515797 2622131 := bstep (se 1 (by rfl) ⟨1966598, by rfl⟩ : syracuseStep 2622131 = 3933197) B3933197
theorem B983755 : Blo 515797 983755 := bstep (se 1 (by rfl) ⟨737816, by rfl⟩ : syracuseStep 983755 = 1475633) B1475633
theorem B2360087 : Blo 515797 2360087 := bstep (se 1 (by rfl) ⟨1770065, by rfl⟩ : syracuseStep 2360087 = 3540131) B3540131
theorem B1311511 : Blo 515797 1311511 := bstep (se 1 (by rfl) ⟨983633, by rfl⟩ : syracuseStep 1311511 = 1967267) B1967267
theorem B1868609 : Blo 515797 1868609 := bstep (se 2 (by rfl) ⟨700728, by rfl⟩ : syracuseStep 1868609 = 1401457) B1401457
theorem B984089 : Blo 515797 984089 := bstep (se 2 (by rfl) ⟨369033, by rfl⟩ : syracuseStep 984089 = 738067) B738067
theorem B1311947 : Blo 515797 1311947 := bstep (se 1 (by rfl) ⟨983960, by rfl⟩ : syracuseStep 1311947 = 1967921) B1967921
theorem B2950445 : Blo 515797 2950445 := bstep (se 3 (by rfl) ⟨553208, by rfl⟩ : syracuseStep 2950445 = 1106417) B1106417
theorem B1869101 : Blo 515797 1869101 := bstep (se 3 (by rfl) ⟨350456, by rfl⟩ : syracuseStep 1869101 = 700913) B700913
theorem B1967435 : Blo 515797 1967435 := bstep (se 1 (by rfl) ⟨1475576, by rfl⟩ : syracuseStep 1967435 = 2951153) B2951153
theorem B1967449 : Blo 515797 1967449 := bstep (se 2 (by rfl) ⟨737793, by rfl⟩ : syracuseStep 1967449 = 1475587) B1475587
theorem B3311027 : Blo 515797 3311027 := bstep (se 1 (by rfl) ⟨2483270, by rfl⟩ : syracuseStep 3311027 = 4966541) B4966541
theorem B2098649 : Blo 515797 2098649 := bstep (se 2 (by rfl) ⟨786993, by rfl⟩ : syracuseStep 2098649 = 1573987) B1573987
theorem B1246681 : Blo 515797 1246681 := bstep (se 2 (by rfl) ⟨467505, by rfl⟩ : syracuseStep 1246681 = 935011) B935011
theorem B787979 : Blo 515797 787979 := bstep (se 1 (by rfl) ⟨590984, by rfl⟩ : syracuseStep 787979 = 1181969) B1181969
theorem B1312321 : Blo 515797 1312321 := bstep (se 2 (by rfl) ⟨492120, by rfl⟩ : syracuseStep 1312321 = 984241) B984241
theorem B1246795 : Blo 515797 1246795 := bstep (se 1 (by rfl) ⟨935096, by rfl⟩ : syracuseStep 1246795 = 1870193) B1870193
theorem B36374129 : Blo 515797 36374129 := bstep (se 2 (by rfl) ⟨13640298, by rfl⟩ : syracuseStep 36374129 = 27280597) B27280597
theorem B3311255 : Blo 515797 3311255 := bstep (se 1 (by rfl) ⟨2483441, by rfl⟩ : syracuseStep 3311255 = 4966883) B4966883
theorem B984727 : Blo 515797 984727 := bstep (se 1 (by rfl) ⟨738545, by rfl⟩ : syracuseStep 984727 = 1477091) B1477091
theorem B3245719 : Blo 515797 3245719 := bstep (se 1 (by rfl) ⟨2434289, by rfl⟩ : syracuseStep 3245719 = 4868579) B4868579
theorem B657163 : Blo 515797 657163 := bstep (se 1 (by rfl) ⟨492872, by rfl⟩ : syracuseStep 657163 = 985745) B985745
theorem B3934169 : Blo 515797 3934169 := bstep (se 2 (by rfl) ⟨1475313, by rfl⟩ : syracuseStep 3934169 = 2950627) B2950627
theorem B1312919 : Blo 515797 1312919 := bstep (se 1 (by rfl) ⟨984689, by rfl⟩ : syracuseStep 1312919 = 1969379) B1969379
theorem B1968407 : Blo 515797 1968407 := bstep (se 1 (by rfl) ⟨1476305, by rfl⟩ : syracuseStep 1968407 = 2952611) B2952611
theorem B985547 : Blo 515797 985547 := bstep (se 1 (by rfl) ⟨739160, by rfl⟩ : syracuseStep 985547 = 1478321) B1478321
theorem B985601 : Blo 515797 985601 := bstep (se 2 (by rfl) ⟨369600, by rfl⟩ : syracuseStep 985601 = 739201) B739201
theorem B2624075 : Blo 515797 2624075 := bstep (se 1 (by rfl) ⟨1968056, by rfl⟩ : syracuseStep 2624075 = 3936113) B3936113
theorem B10783363 : Blo 515797 10783363 := bstep (se 1 (by rfl) ⟨8087522, by rfl⟩ : syracuseStep 10783363 = 16175045) B16175045
theorem B1477399 : Blo 515797 1477399 := bstep (se 1 (by rfl) ⟨1108049, by rfl⟩ : syracuseStep 1477399 = 2216099) B2216099
theorem B3312485 : Blo 515797 3312485 := bstep (se 4 (by rfl) ⟨310545, by rfl⟩ : syracuseStep 3312485 = 621091) B621091
theorem B2100113 : Blo 515797 2100113 := bstep (se 2 (by rfl) ⟨787542, by rfl⟩ : syracuseStep 2100113 = 1575085) B1575085
theorem B1313729 : Blo 515797 1313729 := bstep (se 2 (by rfl) ⟨492648, by rfl⟩ : syracuseStep 1313729 = 985297) B985297
theorem B5049305 : Blo 515797 5049305 := bstep (se 2 (by rfl) ⟨1893489, by rfl⟩ : syracuseStep 5049305 = 3786979) B3786979
theorem B888023 : Blo 515797 888023 := bstep (se 1 (by rfl) ⟨666017, by rfl⟩ : syracuseStep 888023 = 1332035) B1332035
theorem B1346881 : Blo 515797 1346881 := bstep (se 2 (by rfl) ⟨505080, by rfl⟩ : syracuseStep 1346881 = 1010161) B1010161
theorem B757081 : Blo 515797 757081 := bstep (se 2 (by rfl) ⟨283905, by rfl⟩ : syracuseStep 757081 = 567811) B567811
theorem B986519 : Blo 515797 986519 := bstep (se 1 (by rfl) ⟨739889, by rfl⟩ : syracuseStep 986519 = 1479779) B1479779
theorem B1314265 : Blo 515797 1314265 := bstep (se 2 (by rfl) ⟨492849, by rfl⟩ : syracuseStep 1314265 = 985699) B985699
theorem B1969667 : Blo 515797 1969667 := bstep (se 1 (by rfl) ⟨1477250, by rfl⟩ : syracuseStep 1969667 = 2954501) B2954501
theorem B8949379 : Blo 515797 8949379 := bstep (se 1 (by rfl) ⟨6712034, by rfl⟩ : syracuseStep 8949379 = 13424069) B13424069
theorem B1183475 : Blo 515797 1183475 := bstep (se 1 (by rfl) ⟨887606, by rfl⟩ : syracuseStep 1183475 = 1775213) B1775213
theorem B1740851 : Blo 515797 1740851 := bstep (se 1 (by rfl) ⟨1305638, by rfl⟩ : syracuseStep 1740851 = 2611277) B2611277
theorem B3543115 : Blo 515797 3543115 := bstep (se 1 (by rfl) ⟨2657336, by rfl⟩ : syracuseStep 3543115 = 5314673) B5314673
theorem B1478731 : Blo 515797 1478731 := bstep (se 1 (by rfl) ⟨1109048, by rfl⟩ : syracuseStep 1478731 = 2218097) B2218097
theorem B1741121 : Blo 515797 1741121 := bstep (se 2 (by rfl) ⟨652920, by rfl⟩ : syracuseStep 1741121 = 1305841) B1305841
theorem B2625857 : Blo 515797 2625857 := bstep (se 2 (by rfl) ⟨984696, by rfl⟩ : syracuseStep 2625857 = 1969393) B1969393
theorem B1479005 : Blo 515797 1479005 := bstep (se 3 (by rfl) ⟨277313, by rfl⟩ : syracuseStep 1479005 = 554627) B554627
theorem B1053121 : Blo 515797 1053121 := bstep (se 2 (by rfl) ⟨394920, by rfl⟩ : syracuseStep 1053121 = 789841) B789841
theorem B1315379 : Blo 515797 1315379 := bstep (se 1 (by rfl) ⟨986534, by rfl⟩ : syracuseStep 1315379 = 1973069) B1973069
theorem B1479347 : Blo 515797 1479347 := bstep (se 1 (by rfl) ⟨1109510, by rfl⟩ : syracuseStep 1479347 = 2219021) B2219021
theorem B1315673 : Blo 515797 1315673 := bstep (se 2 (by rfl) ⟨493377, by rfl⟩ : syracuseStep 1315673 = 986755) B986755
theorem B1741661 : Blo 515797 1741661 := bstep (se 3 (by rfl) ⟨326561, by rfl⟩ : syracuseStep 1741661 = 653123) B653123
theorem B1184651 : Blo 515797 1184651 := bstep (se 1 (by rfl) ⟨888488, by rfl⟩ : syracuseStep 1184651 = 1776977) B1776977
theorem B1872791 : Blo 515797 1872791 := bstep (se 1 (by rfl) ⟨1404593, by rfl⟩ : syracuseStep 1872791 = 2809187) B2809187
theorem B3740849 : Blo 515797 3740849 := bstep (se 2 (by rfl) ⟨1402818, by rfl⟩ : syracuseStep 3740849 = 2805637) B2805637
theorem B3937571 : Blo 515797 3937571 := bstep (se 1 (by rfl) ⟨2953178, by rfl⟩ : syracuseStep 3937571 = 5906357) B5906357
theorem B1775321 : Blo 515797 1775321 := bstep (se 2 (by rfl) ⟨665745, by rfl⟩ : syracuseStep 1775321 = 1331491) B1331491
theorem B8951597 : Blo 515797 8951597 := bstep (se 3 (by rfl) ⟨1678424, by rfl⟩ : syracuseStep 8951597 = 3356849) B3356849
theorem B1742795 : Blo 515797 1742795 := bstep (se 1 (by rfl) ⟨1307096, by rfl⟩ : syracuseStep 1742795 = 2614193) B2614193
theorem B3545189 : Blo 515797 3545189 := bstep (se 4 (by rfl) ⟨332361, by rfl⟩ : syracuseStep 3545189 = 664723) B664723
theorem B1743065 : Blo 515797 1743065 := bstep (se 2 (by rfl) ⟨653649, by rfl⟩ : syracuseStep 1743065 = 1307299) B1307299
theorem B2627801 : Blo 515797 2627801 := bstep (se 2 (by rfl) ⟨985425, by rfl⟩ : syracuseStep 2627801 = 1970851) B1970851
theorem B8395109 : Blo 515797 8395109 := bstep (se 4 (by rfl) ⟨787041, by rfl⟩ : syracuseStep 8395109 = 1574083) B1574083
theorem B6658595 : Blo 515797 6658595 := bstep (se 1 (by rfl) ⟨4993946, by rfl⟩ : syracuseStep 6658595 = 9987893) B9987893
theorem B1972781 : Blo 515797 1972781 := bstep (se 3 (by rfl) ⟨369896, by rfl⟩ : syracuseStep 1972781 = 739793) B739793
theorem B1743767 : Blo 515797 1743767 := bstep (se 1 (by rfl) ⟨1307825, by rfl⟩ : syracuseStep 1743767 = 2615651) B2615651
theorem B826379 : Blo 515797 826379 := bstep (se 1 (by rfl) ⟨619784, by rfl⟩ : syracuseStep 826379 = 1239569) B1239569
theorem B1580311 : Blo 515797 1580311 := bstep (se 1 (by rfl) ⟨1185233, by rfl⟩ : syracuseStep 1580311 = 2370467) B2370467
theorem B1973555 : Blo 515797 1973555 := bstep (se 1 (by rfl) ⟨1480166, by rfl⟩ : syracuseStep 1973555 = 2960333) B2960333
theorem B1744307 : Blo 515797 1744307 := bstep (se 1 (by rfl) ⟨1308230, by rfl⟩ : syracuseStep 1744307 = 2616461) B2616461
theorem B8068531 : Blo 515797 8068531 := bstep (se 1 (by rfl) ⟨6051398, by rfl⟩ : syracuseStep 8068531 = 12102797) B12102797
theorem B826891 : Blo 515797 826891 := bstep (se 1 (by rfl) ⟨620168, by rfl⟩ : syracuseStep 826891 = 1240337) B1240337
theorem B1777331 : Blo 515797 1777331 := bstep (se 1 (by rfl) ⟨1332998, by rfl⟩ : syracuseStep 1777331 = 2665997) B2665997
theorem B1744577 : Blo 515797 1744577 := bstep (se 2 (by rfl) ⟨654216, by rfl⟩ : syracuseStep 1744577 = 1308433) B1308433
theorem B1941185 : Blo 515797 1941185 := bstep (se 2 (by rfl) ⟨727944, by rfl⟩ : syracuseStep 1941185 = 1455889) B1455889
theorem B2629421 : Blo 515797 2629421 := bstep (se 3 (by rfl) ⟨493016, by rfl⟩ : syracuseStep 2629421 = 986033) B986033
theorem B3153815 : Blo 515797 3153815 := bstep (se 1 (by rfl) ⟨2365361, by rfl⟩ : syracuseStep 3153815 = 4730723) B4730723
theorem B1122241 : Blo 515797 1122241 := bstep (se 2 (by rfl) ⟨420840, by rfl⟩ : syracuseStep 1122241 = 841681) B841681
theorem B1745117 : Blo 515797 1745117 := bstep (se 3 (by rfl) ⟨327209, by rfl⟩ : syracuseStep 1745117 = 654419) B654419
theorem B2203949 : Blo 515797 2203949 := bstep (se 3 (by rfl) ⟨413240, by rfl⟩ : syracuseStep 2203949 = 826481) B826481
theorem B2105689 : Blo 515797 2105689 := bstep (se 2 (by rfl) ⟨789633, by rfl⟩ : syracuseStep 2105689 = 1579267) B1579267
theorem B4432229 : Blo 515797 4432229 := bstep (se 4 (by rfl) ⟨415521, by rfl⟩ : syracuseStep 4432229 = 831043) B831043
theorem B2237003 : Blo 515797 2237003 := bstep (se 1 (by rfl) ⟨1677752, by rfl⟩ : syracuseStep 2237003 = 3355505) B3355505
theorem B2957917 : Blo 515797 2957917 := bstep (se 3 (by rfl) ⟨554609, by rfl⟩ : syracuseStep 2957917 = 1109219) B1109219
theorem B2204633 : Blo 515797 2204633 := bstep (se 2 (by rfl) ⟨826737, by rfl⟩ : syracuseStep 2204633 = 1653475) B1653475
theorem B4432913 : Blo 515797 4432913 := bstep (se 2 (by rfl) ⟨1662342, by rfl⟩ : syracuseStep 4432913 = 3324685) B3324685
theorem B664843 : Blo 515797 664843 := bstep (se 1 (by rfl) ⟨498632, by rfl⟩ : syracuseStep 664843 = 997265) B997265
theorem B1746251 : Blo 515797 1746251 := bstep (se 1 (by rfl) ⟨1309688, by rfl⟩ : syracuseStep 1746251 = 2619377) B2619377
theorem B1746521 : Blo 515797 1746521 := bstep (se 2 (by rfl) ⟨654945, by rfl⟩ : syracuseStep 1746521 = 1309891) B1309891
theorem B8955485 : Blo 515797 8955485 := bstep (se 3 (by rfl) ⟨1679153, by rfl⟩ : syracuseStep 8955485 = 3358307) B3358307
theorem B1681075 : Blo 515797 1681075 := bstep (se 1 (by rfl) ⟨1260806, by rfl⟩ : syracuseStep 1681075 = 2521613) B2521613
theorem B35923661 : Blo 515797 35923661 := bstep (se 3 (by rfl) ⟨6735686, by rfl⟩ : syracuseStep 35923661 = 13471373) B13471373
theorem B8857349 : Blo 515797 8857349 := bstep (se 4 (by rfl) ⟨830376, by rfl⟩ : syracuseStep 8857349 = 1660753) B1660753
theorem B2828125 : Blo 515797 2828125 := bstep (se 3 (by rfl) ⟨530273, by rfl⟩ : syracuseStep 2828125 = 1060547) B1060547
theorem B2205899 : Blo 515797 2205899 := bstep (se 1 (by rfl) ⟨1654424, by rfl⟩ : syracuseStep 2205899 = 3308849) B3308849
theorem B1747223 : Blo 515797 1747223 := bstep (se 1 (by rfl) ⟨1310417, by rfl⟩ : syracuseStep 1747223 = 2620835) B2620835
theorem B3942917 : Blo 515797 3942917 := bstep (se 4 (by rfl) ⟨369648, by rfl⟩ : syracuseStep 3942917 = 739297) B739297
theorem B2206273 : Blo 515797 2206273 := bstep (se 2 (by rfl) ⟨827352, by rfl⟩ : syracuseStep 2206273 = 1654705) B1654705
theorem B1747763 : Blo 515797 1747763 := bstep (se 1 (by rfl) ⟨1310822, by rfl⟩ : syracuseStep 1747763 = 2621645) B2621645
theorem B2206615 : Blo 515797 2206615 := bstep (se 1 (by rfl) ⟨1654961, by rfl⟩ : syracuseStep 2206615 = 3309923) B3309923
theorem B1748033 : Blo 515797 1748033 := bstep (se 2 (by rfl) ⟨655512, by rfl⟩ : syracuseStep 1748033 = 1311025) B1311025
theorem B666839 : Blo 515797 666839 := bstep (se 1 (by rfl) ⟨500129, by rfl⟩ : syracuseStep 666839 = 1000259) B1000259
theorem B830935 : Blo 515797 830935 := bstep (se 1 (by rfl) ⟨623201, by rfl⟩ : syracuseStep 830935 = 1246403) B1246403
theorem B1748573 : Blo 515797 1748573 := bstep (se 3 (by rfl) ⟨327857, by rfl⟩ : syracuseStep 1748573 = 655715) B655715
theorem B5385989 : Blo 515797 5385989 := bstep (se 4 (by rfl) ⟨504936, by rfl⟩ : syracuseStep 5385989 = 1009873) B1009873
theorem B35926091 : Blo 515797 35926091 := bstep (se 1 (by rfl) ⟨26944568, by rfl⟩ : syracuseStep 35926091 = 53889137) B53889137
theorem B831755 : Blo 515797 831755 := bstep (se 1 (by rfl) ⟨623816, by rfl⟩ : syracuseStep 831755 = 1247633) B1247633
theorem B2240947 : Blo 515797 2240947 := bstep (se 1 (by rfl) ⟨1680710, by rfl⟩ : syracuseStep 2240947 = 3361421) B3361421
theorem B930305 : Blo 515797 930305 := bstep (se 2 (by rfl) ⟨348864, by rfl⟩ : syracuseStep 930305 = 697729) B697729
theorem B930455 : Blo 515797 930455 := bstep (se 1 (by rfl) ⟨697841, by rfl⟩ : syracuseStep 930455 = 1395683) B1395683
theorem B1749707 : Blo 515797 1749707 := bstep (se 1 (by rfl) ⟨1312280, by rfl⟩ : syracuseStep 1749707 = 2624561) B2624561
theorem B3945347 : Blo 515797 3945347 := bstep (se 1 (by rfl) ⟨2959010, by rfl⟩ : syracuseStep 3945347 = 5918021) B5918021
theorem B1749977 : Blo 515797 1749977 := bstep (se 2 (by rfl) ⟨656241, by rfl⟩ : syracuseStep 1749977 = 1312483) B1312483
theorem B701707 : Blo 515797 701707 := bstep (se 1 (by rfl) ⟨526280, by rfl⟩ : syracuseStep 701707 = 1052561) B1052561
theorem B4797713 : Blo 515797 4797713 := bstep (se 2 (by rfl) ⟨1799142, by rfl⟩ : syracuseStep 4797713 = 3598285) B3598285
theorem B3421505 : Blo 515797 3421505 := bstep (se 2 (by rfl) ⟨1283064, by rfl⟩ : syracuseStep 3421505 = 2566129) B2566129
theorem B1160729 : Blo 515797 1160729 := bstep (se 2 (by rfl) ⟨435273, by rfl⟩ : syracuseStep 1160729 = 870547) B870547
theorem B1160819 : Blo 515797 1160819 := bstep (se 1 (by rfl) ⟨870614, by rfl⟩ : syracuseStep 1160819 = 1741229) B1741229
theorem B931457 : Blo 515797 931457 := bstep (se 2 (by rfl) ⟨349296, by rfl⟩ : syracuseStep 931457 = 698593) B698593
theorem B2799235 : Blo 515797 2799235 := bstep (se 1 (by rfl) ⟨2099426, by rfl⟩ : syracuseStep 2799235 = 4198853) B4198853
theorem B1160855 : Blo 515797 1160855 := bstep (se 1 (by rfl) ⟨870641, by rfl⟩ : syracuseStep 1160855 = 1741283) B1741283
theorem B1750679 : Blo 515797 1750679 := bstep (se 1 (by rfl) ⟨1313009, by rfl⟩ : syracuseStep 1750679 = 2626019) B2626019
theorem B734923 : Blo 515797 734923 := bstep (se 1 (by rfl) ⟨551192, by rfl⟩ : syracuseStep 734923 = 1102385) B1102385
theorem B734935 : Blo 515797 734935 := bstep (se 1 (by rfl) ⟨551201, by rfl⟩ : syracuseStep 734935 = 1102403) B1102403
theorem B1161035 : Blo 515797 1161035 := bstep (se 1 (by rfl) ⟨870776, by rfl⟩ : syracuseStep 1161035 = 1741553) B1741553
theorem B1161089 : Blo 515797 1161089 := bstep (se 2 (by rfl) ⟨435408, by rfl⟩ : syracuseStep 1161089 = 870817) B870817
theorem B1161305 : Blo 515797 1161305 := bstep (se 2 (by rfl) ⟨435489, by rfl⟩ : syracuseStep 1161305 = 870979) B870979
theorem B1161395 : Blo 515797 1161395 := bstep (se 1 (by rfl) ⟨871046, by rfl⟩ : syracuseStep 1161395 = 1742093) B1742093
theorem B1751219 : Blo 515797 1751219 := bstep (se 1 (by rfl) ⟨1313414, by rfl⟩ : syracuseStep 1751219 = 2626829) B2626829
theorem B1161431 : Blo 515797 1161431 := bstep (se 1 (by rfl) ⟨871073, by rfl⟩ : syracuseStep 1161431 = 1742147) B1742147
theorem B1161611 : Blo 515797 1161611 := bstep (se 1 (by rfl) ⟨871208, by rfl⟩ : syracuseStep 1161611 = 1742417) B1742417
theorem B1161665 : Blo 515797 1161665 := bstep (se 2 (by rfl) ⟨435624, by rfl⟩ : syracuseStep 1161665 = 871249) B871249
theorem B1751489 : Blo 515797 1751489 := bstep (se 2 (by rfl) ⟨656808, by rfl⟩ : syracuseStep 1751489 = 1313617) B1313617
theorem B3324377 : Blo 515797 3324377 := bstep (se 2 (by rfl) ⟨1246641, by rfl⟩ : syracuseStep 3324377 = 2493283) B2493283
theorem B7485965 : Blo 515797 7485965 := bstep (se 3 (by rfl) ⟨1403618, by rfl⟩ : syracuseStep 7485965 = 2807237) B2807237
theorem B1161881 : Blo 515797 1161881 := bstep (se 2 (by rfl) ⟨435705, by rfl⟩ : syracuseStep 1161881 = 871411) B871411
theorem B1161971 : Blo 515797 1161971 := bstep (se 1 (by rfl) ⟨871478, by rfl⟩ : syracuseStep 1161971 = 1742957) B1742957
theorem B1653527 : Blo 515797 1653527 := bstep (se 1 (by rfl) ⟨1240145, by rfl⟩ : syracuseStep 1653527 = 2480291) B2480291
theorem B1162007 : Blo 515797 1162007 := bstep (se 1 (by rfl) ⟨871505, by rfl⟩ : syracuseStep 1162007 = 1743011) B1743011
theorem B7486307 : Blo 515797 7486307 := bstep (se 1 (by rfl) ⟨5614730, by rfl⟩ : syracuseStep 7486307 = 11229461) B11229461
theorem B1162187 : Blo 515797 1162187 := bstep (se 1 (by rfl) ⟨871640, by rfl⟩ : syracuseStep 1162187 = 1743281) B1743281
theorem B1752029 : Blo 515797 1752029 := bstep (se 3 (by rfl) ⟨328505, by rfl⟩ : syracuseStep 1752029 = 657011) B657011
theorem B1162241 : Blo 515797 1162241 := bstep (se 2 (by rfl) ⟨435840, by rfl⟩ : syracuseStep 1162241 = 871681) B871681
theorem B30293027 : Blo 515797 30293027 := bstep (se 1 (by rfl) ⟨22719770, by rfl⟩ : syracuseStep 30293027 = 45439541) B45439541
theorem B1489985 : Blo 515797 1489985 := bstep (se 2 (by rfl) ⟨558744, by rfl⟩ : syracuseStep 1489985 = 1117489) B1117489
theorem B2210989 : Blo 515797 2210989 := bstep (se 3 (by rfl) ⟨414560, by rfl⟩ : syracuseStep 2210989 = 829121) B829121
theorem B1162457 : Blo 515797 1162457 := bstep (se 2 (by rfl) ⟨435921, by rfl⟩ : syracuseStep 1162457 = 871843) B871843
theorem B1162547 : Blo 515797 1162547 := bstep (se 1 (by rfl) ⟨871910, by rfl⟩ : syracuseStep 1162547 = 1743821) B1743821
theorem B1654091 : Blo 515797 1654091 := bstep (se 1 (by rfl) ⟨1240568, by rfl⟩ : syracuseStep 1654091 = 2481137) B2481137
theorem B1162583 : Blo 515797 1162583 := bstep (se 1 (by rfl) ⟨871937, by rfl⟩ : syracuseStep 1162583 = 1743875) B1743875
theorem B933209 : Blo 515797 933209 := bstep (se 2 (by rfl) ⟨349953, by rfl⟩ : syracuseStep 933209 = 699907) B699907
theorem B1162763 : Blo 515797 1162763 := bstep (se 1 (by rfl) ⟨872072, by rfl⟩ : syracuseStep 1162763 = 1744145) B1744145
theorem B1162817 : Blo 515797 1162817 := bstep (se 2 (by rfl) ⟨436056, by rfl⟩ : syracuseStep 1162817 = 872113) B872113
theorem B736985 : Blo 515797 736985 := bstep (se 2 (by rfl) ⟨276369, by rfl⟩ : syracuseStep 736985 = 552739) B552739
theorem B1163033 : Blo 515797 1163033 := bstep (se 2 (by rfl) ⟨436137, by rfl⟩ : syracuseStep 1163033 = 872275) B872275
theorem B933707 : Blo 515797 933707 := bstep (se 1 (by rfl) ⟨700280, by rfl⟩ : syracuseStep 933707 = 1400561) B1400561
theorem B1163123 : Blo 515797 1163123 := bstep (se 1 (by rfl) ⟨872342, by rfl⟩ : syracuseStep 1163123 = 1744685) B1744685
theorem B1163159 : Blo 515797 1163159 := bstep (se 1 (by rfl) ⟨872369, by rfl⟩ : syracuseStep 1163159 = 1744739) B1744739
theorem B3326017 : Blo 515797 3326017 := bstep (se 2 (by rfl) ⟨1247256, by rfl⟩ : syracuseStep 3326017 = 2494513) B2494513
theorem B1163339 : Blo 515797 1163339 := bstep (se 1 (by rfl) ⟨872504, by rfl⟩ : syracuseStep 1163339 = 1745009) B1745009
theorem B1753163 : Blo 515797 1753163 := bstep (se 1 (by rfl) ⟨1314872, by rfl⟩ : syracuseStep 1753163 = 2629745) B2629745
theorem B1163393 : Blo 515797 1163393 := bstep (se 2 (by rfl) ⟨436272, by rfl⟩ : syracuseStep 1163393 = 872545) B872545
theorem B1327435 : Blo 515797 1327435 := bstep (se 1 (by rfl) ⟨995576, by rfl⟩ : syracuseStep 1327435 = 1991153) B1991153
theorem B737623 : Blo 515797 737623 := bstep (se 1 (by rfl) ⟨553217, by rfl⟩ : syracuseStep 737623 = 1106435) B1106435
theorem B1163609 : Blo 515797 1163609 := bstep (se 2 (by rfl) ⟨436353, by rfl⟩ : syracuseStep 1163609 = 872707) B872707
theorem B1753433 : Blo 515797 1753433 := bstep (se 2 (by rfl) ⟨657537, by rfl⟩ : syracuseStep 1753433 = 1315075) B1315075
theorem B1163699 : Blo 515797 1163699 := bstep (se 1 (by rfl) ⟨872774, by rfl⟩ : syracuseStep 1163699 = 1745549) B1745549
theorem B7487923 : Blo 515797 7487923 := bstep (se 1 (by rfl) ⟨5615942, by rfl⟩ : syracuseStep 7487923 = 11231885) B11231885
theorem B1163735 : Blo 515797 1163735 := bstep (se 1 (by rfl) ⟨872801, by rfl⟩ : syracuseStep 1163735 = 1745603) B1745603
theorem B48611933 : Blo 515797 48611933 := bstep (se 3 (by rfl) ⟨9114737, by rfl⟩ : syracuseStep 48611933 = 18229475) B18229475
theorem B1163915 : Blo 515797 1163915 := bstep (se 1 (by rfl) ⟨872936, by rfl⟩ : syracuseStep 1163915 = 1745873) B1745873
theorem B1163969 : Blo 515797 1163969 := bstep (se 2 (by rfl) ⟨436488, by rfl⟩ : syracuseStep 1163969 = 872977) B872977
theorem B2212697 : Blo 515797 2212697 := bstep (se 2 (by rfl) ⟨829761, by rfl⟩ : syracuseStep 2212697 = 1659523) B1659523
theorem B1164185 : Blo 515797 1164185 := bstep (se 2 (by rfl) ⟨436569, by rfl⟩ : syracuseStep 1164185 = 873139) B873139
theorem B1164275 : Blo 515797 1164275 := bstep (se 1 (by rfl) ⟨873206, by rfl⟩ : syracuseStep 1164275 = 1746413) B1746413
theorem B1164311 : Blo 515797 1164311 := bstep (se 1 (by rfl) ⟨873233, by rfl⟩ : syracuseStep 1164311 = 1746467) B1746467
theorem B1754135 : Blo 515797 1754135 := bstep (se 1 (by rfl) ⟨1315601, by rfl⟩ : syracuseStep 1754135 = 2631203) B2631203
theorem B3720293 : Blo 515797 3720293 := bstep (se 4 (by rfl) ⟨348777, by rfl⟩ : syracuseStep 3720293 = 697555) B697555
theorem B738443 : Blo 515797 738443 := bstep (se 1 (by rfl) ⟨553832, by rfl⟩ : syracuseStep 738443 = 1107665) B1107665
theorem B1164491 : Blo 515797 1164491 := bstep (se 1 (by rfl) ⟨873368, by rfl⟩ : syracuseStep 1164491 = 1746737) B1746737
theorem B935155 : Blo 515797 935155 := bstep (se 1 (by rfl) ⟨701366, by rfl⟩ : syracuseStep 935155 = 1402733) B1402733
theorem B1164545 : Blo 515797 1164545 := bstep (se 2 (by rfl) ⟨436704, by rfl⟩ : syracuseStep 1164545 = 873409) B873409
theorem B4736261 : Blo 515797 4736261 := bstep (se 4 (by rfl) ⟨444024, by rfl⟩ : syracuseStep 4736261 = 888049) B888049
theorem B1164761 : Blo 515797 1164761 := bstep (se 2 (by rfl) ⟨436785, by rfl⟩ : syracuseStep 1164761 = 873571) B873571
theorem B1164851 : Blo 515797 1164851 := bstep (se 1 (by rfl) ⟨873638, by rfl⟩ : syracuseStep 1164851 = 1747277) B1747277
theorem B1164887 : Blo 515797 1164887 := bstep (se 1 (by rfl) ⟨873665, by rfl⟩ : syracuseStep 1164887 = 1747331) B1747331
theorem B4212317 : Blo 515797 4212317 := bstep (se 3 (by rfl) ⟨789809, by rfl⟩ : syracuseStep 4212317 = 1579619) B1579619
theorem B1492673 : Blo 515797 1492673 := bstep (se 2 (by rfl) ⟨559752, by rfl⟩ : syracuseStep 1492673 = 1119505) B1119505
theorem B1165067 : Blo 515797 1165067 := bstep (se 1 (by rfl) ⟨873800, by rfl⟩ : syracuseStep 1165067 = 1747601) B1747601
theorem B1165121 : Blo 515797 1165121 := bstep (se 2 (by rfl) ⟨436920, by rfl⟩ : syracuseStep 1165121 = 873841) B873841
theorem B1165337 : Blo 515797 1165337 := bstep (se 2 (by rfl) ⟨437001, by rfl⟩ : syracuseStep 1165337 = 874003) B874003
theorem B2213963 : Blo 515797 2213963 := bstep (se 1 (by rfl) ⟨1660472, by rfl⟩ : syracuseStep 2213963 = 3320945) B3320945
theorem B1165427 : Blo 515797 1165427 := bstep (se 1 (by rfl) ⟨874070, by rfl⟩ : syracuseStep 1165427 = 1748141) B1748141
theorem B1165463 : Blo 515797 1165463 := bstep (se 1 (by rfl) ⟨874097, by rfl⟩ : syracuseStep 1165463 = 1748195) B1748195
theorem B9423053 : Blo 515797 9423053 := bstep (se 3 (by rfl) ⟨1766822, by rfl⟩ : syracuseStep 9423053 = 3533645) B3533645
theorem B1165643 : Blo 515797 1165643 := bstep (se 1 (by rfl) ⟨874232, by rfl⟩ : syracuseStep 1165643 = 1748465) B1748465
theorem B870743 : Blo 515797 870743 := bstep (se 1 (by rfl) ⟨653057, by rfl⟩ : syracuseStep 870743 = 1306115) B1306115
theorem B1165697 : Blo 515797 1165697 := bstep (se 2 (by rfl) ⟨437136, by rfl⟩ : syracuseStep 1165697 = 874273) B874273
theorem B2214323 : Blo 515797 2214323 := bstep (se 1 (by rfl) ⟨1660742, by rfl⟩ : syracuseStep 2214323 = 3321485) B3321485
theorem B870871 : Blo 515797 870871 := bstep (se 1 (by rfl) ⟨653153, by rfl⟩ : syracuseStep 870871 = 1306307) B1306307
theorem B707033 : Blo 515797 707033 := bstep (se 2 (by rfl) ⟨265137, by rfl⟩ : syracuseStep 707033 = 530275) B530275
theorem B1165913 : Blo 515797 1165913 := bstep (se 2 (by rfl) ⟨437217, by rfl⟩ : syracuseStep 1165913 = 874435) B874435
theorem B1166003 : Blo 515797 1166003 := bstep (se 1 (by rfl) ⟨874502, by rfl⟩ : syracuseStep 1166003 = 1749005) B1749005
theorem B1166039 : Blo 515797 1166039 := bstep (se 1 (by rfl) ⟨874529, by rfl⟩ : syracuseStep 1166039 = 1749059) B1749059
theorem B1985303 : Blo 515797 1985303 := bstep (se 1 (by rfl) ⟨1488977, by rfl⟩ : syracuseStep 1985303 = 2977955) B2977955
theorem B1166219 : Blo 515797 1166219 := bstep (se 1 (by rfl) ⟨874664, by rfl⟩ : syracuseStep 1166219 = 1749329) B1749329
theorem B4967345 : Blo 515797 4967345 := bstep (se 2 (by rfl) ⟨1862754, by rfl⟩ : syracuseStep 4967345 = 3725509) B3725509
theorem B1166273 : Blo 515797 1166273 := bstep (se 2 (by rfl) ⟨437352, by rfl⟩ : syracuseStep 1166273 = 874705) B874705
theorem B871499 : Blo 515797 871499 := bstep (se 1 (by rfl) ⟨653624, by rfl⟩ : syracuseStep 871499 = 1307249) B1307249
theorem B1166489 : Blo 515797 1166489 := bstep (se 2 (by rfl) ⟨437433, by rfl⟩ : syracuseStep 1166489 = 874867) B874867
theorem B871627 : Blo 515797 871627 := bstep (se 1 (by rfl) ⟨653720, by rfl⟩ : syracuseStep 871627 = 1307441) B1307441
theorem B1166579 : Blo 515797 1166579 := bstep (se 1 (by rfl) ⟨874934, by rfl⟩ : syracuseStep 1166579 = 1749869) B1749869
theorem B1166615 : Blo 515797 1166615 := bstep (se 1 (by rfl) ⟨874961, by rfl⟩ : syracuseStep 1166615 = 1749923) B1749923
theorem B871769 : Blo 515797 871769 := bstep (se 2 (by rfl) ⟨326913, by rfl⟩ : syracuseStep 871769 = 653827) B653827
theorem B1166795 : Blo 515797 1166795 := bstep (se 1 (by rfl) ⟨875096, by rfl⟩ : syracuseStep 1166795 = 1750193) B1750193
theorem B871897 : Blo 515797 871897 := bstep (se 2 (by rfl) ⟨326961, by rfl⟩ : syracuseStep 871897 = 653923) B653923
theorem B1166849 : Blo 515797 1166849 := bstep (se 2 (by rfl) ⟨437568, by rfl⟩ : syracuseStep 1166849 = 875137) B875137
theorem B773771 : Blo 515797 773771 := bstep (se 1 (by rfl) ⟨580328, by rfl⟩ : syracuseStep 773771 = 1160657) B1160657
theorem B773783 : Blo 515797 773783 := bstep (se 1 (by rfl) ⟨580337, by rfl⟩ : syracuseStep 773783 = 1160675) B1160675
theorem B773849 : Blo 515797 773849 := bstep (se 2 (by rfl) ⟨290193, by rfl⟩ : syracuseStep 773849 = 580387) B580387
theorem B1167065 : Blo 515797 1167065 := bstep (se 2 (by rfl) ⟨437649, by rfl⟩ : syracuseStep 1167065 = 875299) B875299
theorem B4476707 : Blo 515797 4476707 := bstep (se 1 (by rfl) ⟨3357530, by rfl⟩ : syracuseStep 4476707 = 6715061) B6715061
theorem B1167155 : Blo 515797 1167155 := bstep (se 1 (by rfl) ⟨875366, by rfl⟩ : syracuseStep 1167155 = 1750733) B1750733
theorem B773963 : Blo 515797 773963 := bstep (se 1 (by rfl) ⟨580472, by rfl⟩ : syracuseStep 773963 = 1160945) B1160945
theorem B773975 : Blo 515797 773975 := bstep (se 1 (by rfl) ⟨580481, by rfl⟩ : syracuseStep 773975 = 1160963) B1160963
theorem B1167191 : Blo 515797 1167191 := bstep (se 1 (by rfl) ⟨875393, by rfl⟩ : syracuseStep 1167191 = 1750787) B1750787
theorem B1200023 : Blo 515797 1200023 := bstep (se 1 (by rfl) ⟨900017, by rfl⟩ : syracuseStep 1200023 = 1800035) B1800035
theorem B774041 : Blo 515797 774041 := bstep (se 2 (by rfl) ⟨290265, by rfl⟩ : syracuseStep 774041 = 580531) B580531
theorem B774155 : Blo 515797 774155 := bstep (se 1 (by rfl) ⟨580616, by rfl⟩ : syracuseStep 774155 = 1161233) B1161233
theorem B1167371 : Blo 515797 1167371 := bstep (se 1 (by rfl) ⟨875528, by rfl⟩ : syracuseStep 1167371 = 1751057) B1751057
theorem B774167 : Blo 515797 774167 := bstep (se 1 (by rfl) ⟨580625, by rfl⟩ : syracuseStep 774167 = 1161251) B1161251
theorem B872471 : Blo 515797 872471 := bstep (se 1 (by rfl) ⟨654353, by rfl⟩ : syracuseStep 872471 = 1308707) B1308707
theorem B1167425 : Blo 515797 1167425 := bstep (se 2 (by rfl) ⟨437784, by rfl⟩ : syracuseStep 1167425 = 875569) B875569
theorem B1101899 : Blo 515797 1101899 := bstep (se 1 (by rfl) ⟨826424, by rfl⟩ : syracuseStep 1101899 = 1652849) B1652849
theorem B774233 : Blo 515797 774233 := bstep (se 2 (by rfl) ⟨290337, by rfl⟩ : syracuseStep 774233 = 580675) B580675
theorem B2805853 : Blo 515797 2805853 := bstep (se 3 (by rfl) ⟨526097, by rfl⟩ : syracuseStep 2805853 = 1052195) B1052195
theorem B872599 : Blo 515797 872599 := bstep (se 1 (by rfl) ⟨654449, by rfl⟩ : syracuseStep 872599 = 1308899) B1308899
theorem B774347 : Blo 515797 774347 := bstep (se 1 (by rfl) ⟨580760, by rfl⟩ : syracuseStep 774347 = 1161521) B1161521
theorem B774359 : Blo 515797 774359 := bstep (se 1 (by rfl) ⟨580769, by rfl⟩ : syracuseStep 774359 = 1161539) B1161539
theorem B774425 : Blo 515797 774425 := bstep (se 2 (by rfl) ⟨290409, by rfl⟩ : syracuseStep 774425 = 580819) B580819
theorem B1167641 : Blo 515797 1167641 := bstep (se 2 (by rfl) ⟨437865, by rfl⟩ : syracuseStep 1167641 = 875731) B875731
theorem B1986905 : Blo 515797 1986905 := bstep (se 2 (by rfl) ⟨745089, by rfl⟩ : syracuseStep 1986905 = 1490179) B1490179
theorem B1167731 : Blo 515797 1167731 := bstep (se 1 (by rfl) ⟨875798, by rfl⟩ : syracuseStep 1167731 = 1751597) B1751597
theorem B774539 : Blo 515797 774539 := bstep (se 1 (by rfl) ⟨580904, by rfl⟩ : syracuseStep 774539 = 1161809) B1161809
theorem B774551 : Blo 515797 774551 := bstep (se 1 (by rfl) ⟨580913, by rfl⟩ : syracuseStep 774551 = 1161827) B1161827
theorem B1167767 : Blo 515797 1167767 := bstep (se 1 (by rfl) ⟨875825, by rfl⟩ : syracuseStep 1167767 = 1751651) B1751651
theorem B774617 : Blo 515797 774617 := bstep (se 2 (by rfl) ⟨290481, by rfl⟩ : syracuseStep 774617 = 580963) B580963
theorem B6279697 : Blo 515797 6279697 := bstep (se 2 (by rfl) ⟨2354886, by rfl⟩ : syracuseStep 6279697 = 4709773) B4709773
theorem B840215 : Blo 515797 840215 := bstep (se 1 (by rfl) ⟨630161, by rfl⟩ : syracuseStep 840215 = 1260323) B1260323
theorem B774731 : Blo 515797 774731 := bstep (se 1 (by rfl) ⟨581048, by rfl⟩ : syracuseStep 774731 = 1162097) B1162097
theorem B1167947 : Blo 515797 1167947 := bstep (se 1 (by rfl) ⟨875960, by rfl⟩ : syracuseStep 1167947 = 1751921) B1751921
theorem B774743 : Blo 515797 774743 := bstep (se 1 (by rfl) ⟨581057, by rfl⟩ : syracuseStep 774743 = 1162115) B1162115
theorem B1168001 : Blo 515797 1168001 := bstep (se 2 (by rfl) ⟨438000, by rfl⟩ : syracuseStep 1168001 = 876001) B876001
theorem B774809 : Blo 515797 774809 := bstep (se 2 (by rfl) ⟨290553, by rfl⟩ : syracuseStep 774809 = 581107) B581107
theorem B3920561 : Blo 515797 3920561 := bstep (se 2 (by rfl) ⟨1470210, by rfl⟩ : syracuseStep 3920561 = 2940421) B2940421
theorem B1594073 : Blo 515797 1594073 := bstep (se 2 (by rfl) ⟨597777, by rfl⟩ : syracuseStep 1594073 = 1195555) B1195555
theorem B774923 : Blo 515797 774923 := bstep (se 1 (by rfl) ⟨581192, by rfl⟩ : syracuseStep 774923 = 1162385) B1162385
theorem B873227 : Blo 515797 873227 := bstep (se 1 (by rfl) ⟨654920, by rfl⟩ : syracuseStep 873227 = 1309841) B1309841
theorem B774935 : Blo 515797 774935 := bstep (se 1 (by rfl) ⟨581201, by rfl⟩ : syracuseStep 774935 = 1162403) B1162403
theorem B1200961 : Blo 515797 1200961 := bstep (se 2 (by rfl) ⟨450360, by rfl⟩ : syracuseStep 1200961 = 900721) B900721
theorem B775001 : Blo 515797 775001 := bstep (se 2 (by rfl) ⟨290625, by rfl⟩ : syracuseStep 775001 = 581251) B581251
theorem B1168217 : Blo 515797 1168217 := bstep (se 2 (by rfl) ⟨438081, by rfl⟩ : syracuseStep 1168217 = 876163) B876163
theorem B873355 : Blo 515797 873355 := bstep (se 1 (by rfl) ⟨655016, by rfl⟩ : syracuseStep 873355 = 1310033) B1310033
theorem B2937779 : Blo 515797 2937779 := bstep (se 1 (by rfl) ⟨2203334, by rfl⟩ : syracuseStep 2937779 = 4406669) B4406669
theorem B1168307 : Blo 515797 1168307 := bstep (se 1 (by rfl) ⟨876230, by rfl⟩ : syracuseStep 1168307 = 1752461) B1752461
theorem B775115 : Blo 515797 775115 := bstep (se 1 (by rfl) ⟨581336, by rfl⟩ : syracuseStep 775115 = 1162673) B1162673
theorem B775127 : Blo 515797 775127 := bstep (se 1 (by rfl) ⟨581345, by rfl⟩ : syracuseStep 775127 = 1162691) B1162691
theorem B1168343 : Blo 515797 1168343 := bstep (se 1 (by rfl) ⟨876257, by rfl⟩ : syracuseStep 1168343 = 1752515) B1752515
theorem B4183001 : Blo 515797 4183001 := bstep (se 2 (by rfl) ⟨1568625, by rfl⟩ : syracuseStep 4183001 = 3137251) B3137251
theorem B775193 : Blo 515797 775193 := bstep (se 2 (by rfl) ⟨290697, by rfl⟩ : syracuseStep 775193 = 581395) B581395
theorem B873497 : Blo 515797 873497 := bstep (se 2 (by rfl) ⟨327561, by rfl⟩ : syracuseStep 873497 = 655123) B655123
theorem B775307 : Blo 515797 775307 := bstep (se 1 (by rfl) ⟨581480, by rfl⟩ : syracuseStep 775307 = 1162961) B1162961
theorem B1168523 : Blo 515797 1168523 := bstep (se 1 (by rfl) ⟨876392, by rfl⟩ : syracuseStep 1168523 = 1752785) B1752785
theorem B3921047 : Blo 515797 3921047 := bstep (se 1 (by rfl) ⟨2940785, by rfl⟩ : syracuseStep 3921047 = 5881571) B5881571
theorem B775319 : Blo 515797 775319 := bstep (se 1 (by rfl) ⟨581489, by rfl⟩ : syracuseStep 775319 = 1162979) B1162979
theorem B873625 : Blo 515797 873625 := bstep (se 2 (by rfl) ⟨327609, by rfl⟩ : syracuseStep 873625 = 655219) B655219
theorem B1168577 : Blo 515797 1168577 := bstep (se 2 (by rfl) ⟨438216, by rfl⟩ : syracuseStep 1168577 = 876433) B876433
theorem B775385 : Blo 515797 775385 := bstep (se 2 (by rfl) ⟨290769, by rfl⟩ : syracuseStep 775385 = 581539) B581539
theorem B1103129 : Blo 515797 1103129 := bstep (se 2 (by rfl) ⟨413673, by rfl⟩ : syracuseStep 1103129 = 827347) B827347
theorem B775499 : Blo 515797 775499 := bstep (se 1 (by rfl) ⟨581624, by rfl⟩ : syracuseStep 775499 = 1163249) B1163249
theorem B1201483 : Blo 515797 1201483 := bstep (se 1 (by rfl) ⟨901112, by rfl⟩ : syracuseStep 1201483 = 1802225) B1802225
theorem B775511 : Blo 515797 775511 := bstep (se 1 (by rfl) ⟨581633, by rfl⟩ : syracuseStep 775511 = 1163267) B1163267
theorem B775577 : Blo 515797 775577 := bstep (se 2 (by rfl) ⟨290841, by rfl⟩ : syracuseStep 775577 = 581683) B581683
theorem B1168793 : Blo 515797 1168793 := bstep (se 2 (by rfl) ⟨438297, by rfl⟩ : syracuseStep 1168793 = 876595) B876595
theorem B1168883 : Blo 515797 1168883 := bstep (se 1 (by rfl) ⟨876662, by rfl⟩ : syracuseStep 1168883 = 1753325) B1753325
theorem B775691 : Blo 515797 775691 := bstep (se 1 (by rfl) ⟨581768, by rfl⟩ : syracuseStep 775691 = 1163537) B1163537
theorem B775703 : Blo 515797 775703 := bstep (se 1 (by rfl) ⟨581777, by rfl⟩ : syracuseStep 775703 = 1163555) B1163555
theorem B1168919 : Blo 515797 1168919 := bstep (se 1 (by rfl) ⟨876689, by rfl⟩ : syracuseStep 1168919 = 1753379) B1753379
theorem B775769 : Blo 515797 775769 := bstep (se 2 (by rfl) ⟨290913, by rfl⟩ : syracuseStep 775769 = 581827) B581827
theorem B1594973 : Blo 515797 1594973 := bstep (se 3 (by rfl) ⟨299057, by rfl⟩ : syracuseStep 1594973 = 598115) B598115
theorem B1103539 : Blo 515797 1103539 := bstep (se 1 (by rfl) ⟨827654, by rfl⟩ : syracuseStep 1103539 = 1655309) B1655309
theorem B775883 : Blo 515797 775883 := bstep (se 1 (by rfl) ⟨581912, by rfl⟩ : syracuseStep 775883 = 1163825) B1163825
theorem B1169099 : Blo 515797 1169099 := bstep (se 1 (by rfl) ⟨876824, by rfl⟩ : syracuseStep 1169099 = 1753649) B1753649
theorem B775895 : Blo 515797 775895 := bstep (se 1 (by rfl) ⟨581921, by rfl⟩ : syracuseStep 775895 = 1163843) B1163843
theorem B874199 : Blo 515797 874199 := bstep (se 1 (by rfl) ⟨655649, by rfl⟩ : syracuseStep 874199 = 1311299) B1311299
theorem B1398493 : Blo 515797 1398493 := bstep (se 3 (by rfl) ⟨262217, by rfl⟩ : syracuseStep 1398493 = 524435) B524435
theorem B1169153 : Blo 515797 1169153 := bstep (se 2 (by rfl) ⟨438432, by rfl⟩ : syracuseStep 1169153 = 876865) B876865
theorem B775961 : Blo 515797 775961 := bstep (se 2 (by rfl) ⟨290985, by rfl⟩ : syracuseStep 775961 = 581971) B581971
theorem B874327 : Blo 515797 874327 := bstep (se 1 (by rfl) ⟨655745, by rfl⟩ : syracuseStep 874327 = 1311491) B1311491
theorem B776075 : Blo 515797 776075 := bstep (se 1 (by rfl) ⟨582056, by rfl⟩ : syracuseStep 776075 = 1164113) B1164113
theorem B776087 : Blo 515797 776087 := bstep (se 1 (by rfl) ⟨582065, by rfl⟩ : syracuseStep 776087 = 1164131) B1164131
theorem B776153 : Blo 515797 776153 := bstep (se 2 (by rfl) ⟨291057, by rfl⟩ : syracuseStep 776153 = 582115) B582115
theorem B1169369 : Blo 515797 1169369 := bstep (se 2 (by rfl) ⟨438513, by rfl⟩ : syracuseStep 1169369 = 877027) B877027
theorem B1169459 : Blo 515797 1169459 := bstep (se 1 (by rfl) ⟨877094, by rfl⟩ : syracuseStep 1169459 = 1754189) B1754189
theorem B776267 : Blo 515797 776267 := bstep (se 1 (by rfl) ⟨582200, by rfl⟩ : syracuseStep 776267 = 1164401) B1164401
theorem B776279 : Blo 515797 776279 := bstep (se 1 (by rfl) ⟨582209, by rfl⟩ : syracuseStep 776279 = 1164419) B1164419
theorem B1169495 : Blo 515797 1169495 := bstep (se 1 (by rfl) ⟨877121, by rfl⟩ : syracuseStep 1169495 = 1754243) B1754243
theorem B7100567 : Blo 515797 7100567 := bstep (se 1 (by rfl) ⟨5325425, by rfl⟩ : syracuseStep 7100567 = 10650851) B10650851
theorem B1104025 : Blo 515797 1104025 := bstep (se 2 (by rfl) ⟨414009, by rfl⟩ : syracuseStep 1104025 = 828019) B828019
theorem B776345 : Blo 515797 776345 := bstep (se 2 (by rfl) ⟨291129, by rfl⟩ : syracuseStep 776345 = 582259) B582259
theorem B776459 : Blo 515797 776459 := bstep (se 1 (by rfl) ⟨582344, by rfl⟩ : syracuseStep 776459 = 1164689) B1164689
theorem B776471 : Blo 515797 776471 := bstep (se 1 (by rfl) ⟨582353, by rfl⟩ : syracuseStep 776471 = 1164707) B1164707
theorem B842071 : Blo 515797 842071 := bstep (se 1 (by rfl) ⟨631553, by rfl⟩ : syracuseStep 842071 = 1263107) B1263107
theorem B776537 : Blo 515797 776537 := bstep (se 2 (by rfl) ⟨291201, by rfl⟩ : syracuseStep 776537 = 582403) B582403
theorem B2939237 : Blo 515797 2939237 := bstep (se 4 (by rfl) ⟨275553, by rfl⟩ : syracuseStep 2939237 = 551107) B551107
theorem B776651 : Blo 515797 776651 := bstep (se 1 (by rfl) ⟨582488, by rfl⟩ : syracuseStep 776651 = 1164977) B1164977
theorem B874955 : Blo 515797 874955 := bstep (se 1 (by rfl) ⟨656216, by rfl⟩ : syracuseStep 874955 = 1312433) B1312433
theorem B776663 : Blo 515797 776663 := bstep (se 1 (by rfl) ⟨582497, by rfl⟩ : syracuseStep 776663 = 1164995) B1164995
theorem B4184581 : Blo 515797 4184581 := bstep (se 4 (by rfl) ⟨392304, by rfl⟩ : syracuseStep 4184581 = 784609) B784609
theorem B776729 : Blo 515797 776729 := bstep (se 2 (by rfl) ⟨291273, by rfl⟩ : syracuseStep 776729 = 582547) B582547
theorem B875083 : Blo 515797 875083 := bstep (se 1 (by rfl) ⟨656312, by rfl⟩ : syracuseStep 875083 = 1312625) B1312625
theorem B776843 : Blo 515797 776843 := bstep (se 1 (by rfl) ⟨582632, by rfl⟩ : syracuseStep 776843 = 1165265) B1165265
theorem B776855 : Blo 515797 776855 := bstep (se 1 (by rfl) ⟨582641, by rfl⟩ : syracuseStep 776855 = 1165283) B1165283
theorem B580279 : Blo 515797 580279 := bstep (se 1 (by rfl) ⟨435209, by rfl⟩ : syracuseStep 580279 = 870419) B870419
theorem B776921 : Blo 515797 776921 := bstep (se 2 (by rfl) ⟨291345, by rfl⟩ : syracuseStep 776921 = 582691) B582691
theorem B875225 : Blo 515797 875225 := bstep (se 2 (by rfl) ⟨328209, by rfl⟩ : syracuseStep 875225 = 656419) B656419
theorem B777035 : Blo 515797 777035 := bstep (se 1 (by rfl) ⟨582776, by rfl⟩ : syracuseStep 777035 = 1165553) B1165553
theorem B777047 : Blo 515797 777047 := bstep (se 1 (by rfl) ⟨582785, by rfl⟩ : syracuseStep 777047 = 1165571) B1165571
theorem B875353 : Blo 515797 875353 := bstep (se 2 (by rfl) ⟨328257, by rfl⟩ : syracuseStep 875353 = 656515) B656515
theorem B14932835 : Blo 515797 14932835 := bstep (se 1 (by rfl) ⟨11199626, by rfl⟩ : syracuseStep 14932835 = 22399253) B22399253
theorem B580459 : Blo 515797 580459 := bstep (se 1 (by rfl) ⟨435344, by rfl⟩ : syracuseStep 580459 = 870689) B870689
theorem B1104769 : Blo 515797 1104769 := bstep (se 2 (by rfl) ⟨414288, by rfl⟩ : syracuseStep 1104769 = 828577) B828577
theorem B777113 : Blo 515797 777113 := bstep (se 2 (by rfl) ⟨291417, by rfl⟩ : syracuseStep 777113 = 582835) B582835
theorem B580567 : Blo 515797 580567 := bstep (se 1 (by rfl) ⟨435425, by rfl⟩ : syracuseStep 580567 = 870851) B870851
theorem B9952217 : Blo 515797 9952217 := bstep (se 2 (by rfl) ⟨3732081, by rfl⟩ : syracuseStep 9952217 = 7464163) B7464163
theorem B777227 : Blo 515797 777227 := bstep (se 1 (by rfl) ⟨582920, by rfl⟩ : syracuseStep 777227 = 1165841) B1165841
theorem B2939921 : Blo 515797 2939921 := bstep (se 2 (by rfl) ⟨1102470, by rfl⟩ : syracuseStep 2939921 = 2204941) B2204941
theorem B777239 : Blo 515797 777239 := bstep (se 1 (by rfl) ⟨582929, by rfl⟩ : syracuseStep 777239 = 1165859) B1165859
theorem B777305 : Blo 515797 777305 := bstep (se 2 (by rfl) ⟨291489, by rfl⟩ : syracuseStep 777305 = 582979) B582979
theorem B580747 : Blo 515797 580747 := bstep (se 1 (by rfl) ⟨435560, by rfl⟩ : syracuseStep 580747 = 871121) B871121
theorem B777419 : Blo 515797 777419 := bstep (se 1 (by rfl) ⟨583064, by rfl⟩ : syracuseStep 777419 = 1166129) B1166129
theorem B777431 : Blo 515797 777431 := bstep (se 1 (by rfl) ⟨583073, by rfl⟩ : syracuseStep 777431 = 1166147) B1166147
theorem B580855 : Blo 515797 580855 := bstep (se 1 (by rfl) ⟨435641, by rfl⟩ : syracuseStep 580855 = 871283) B871283
theorem B2481425 : Blo 515797 2481425 := bstep (se 2 (by rfl) ⟨930534, by rfl⟩ : syracuseStep 2481425 = 1861069) B1861069
theorem B777497 : Blo 515797 777497 := bstep (se 2 (by rfl) ⟨291561, by rfl⟩ : syracuseStep 777497 = 583123) B583123
theorem B1400129 : Blo 515797 1400129 := bstep (se 2 (by rfl) ⟨525048, by rfl⟩ : syracuseStep 1400129 = 1050097) B1050097
theorem B2612573 : Blo 515797 2612573 := bstep (se 3 (by rfl) ⟨489857, by rfl⟩ : syracuseStep 2612573 = 979715) B979715
theorem B2219395 : Blo 515797 2219395 := bstep (se 1 (by rfl) ⟨1664546, by rfl⟩ : syracuseStep 2219395 = 3329093) B3329093
theorem B777611 : Blo 515797 777611 := bstep (se 1 (by rfl) ⟨583208, by rfl⟩ : syracuseStep 777611 = 1166417) B1166417
theorem B777623 : Blo 515797 777623 := bstep (se 1 (by rfl) ⟨583217, by rfl⟩ : syracuseStep 777623 = 1166435) B1166435
theorem B875927 : Blo 515797 875927 := bstep (se 1 (by rfl) ⟨656945, by rfl⟩ : syracuseStep 875927 = 1313891) B1313891
theorem B581035 : Blo 515797 581035 := bstep (se 1 (by rfl) ⟨435776, by rfl⟩ : syracuseStep 581035 = 871553) B871553
theorem B777689 : Blo 515797 777689 := bstep (se 2 (by rfl) ⟨291633, by rfl⟩ : syracuseStep 777689 = 583267) B583267
theorem B581143 : Blo 515797 581143 := bstep (se 1 (by rfl) ⟨435857, by rfl⟩ : syracuseStep 581143 = 871715) B871715
theorem B876055 : Blo 515797 876055 := bstep (se 1 (by rfl) ⟨657041, by rfl⟩ : syracuseStep 876055 = 1314083) B1314083
theorem B777803 : Blo 515797 777803 := bstep (se 1 (by rfl) ⟨583352, by rfl⟩ : syracuseStep 777803 = 1166705) B1166705
theorem B777815 : Blo 515797 777815 := bstep (se 1 (by rfl) ⟨583361, by rfl⟩ : syracuseStep 777815 = 1166723) B1166723
theorem B777881 : Blo 515797 777881 := bstep (se 2 (by rfl) ⟨291705, by rfl⟩ : syracuseStep 777881 = 583411) B583411
theorem B581323 : Blo 515797 581323 := bstep (se 1 (by rfl) ⟨435992, by rfl⟩ : syracuseStep 581323 = 871985) B871985
theorem B515799 : Blo 515797 515799 := bstep (se 1 (by rfl) ⟨386849, by rfl⟩ : syracuseStep 515799 = 773699) B773699
theorem B2219737 : Blo 515797 2219737 := bstep (se 2 (by rfl) ⟨832401, by rfl⟩ : syracuseStep 2219737 = 1664803) B1664803
theorem B515819 : Blo 515797 515819 := bstep (se 1 (by rfl) ⟨386864, by rfl⟩ : syracuseStep 515819 = 773729) B773729
theorem B515831 : Blo 515797 515831 := bstep (se 1 (by rfl) ⟨386873, by rfl⟩ : syracuseStep 515831 = 773747) B773747
theorem B515851 : Blo 515797 515851 := bstep (se 1 (by rfl) ⟨386888, by rfl⟩ : syracuseStep 515851 = 773777) B773777
theorem B777995 : Blo 515797 777995 := bstep (se 1 (by rfl) ⟨583496, by rfl⟩ : syracuseStep 777995 = 1166993) B1166993
theorem B515863 : Blo 515797 515863 := bstep (se 1 (by rfl) ⟨386897, by rfl⟩ : syracuseStep 515863 = 773795) B773795
theorem B778007 : Blo 515797 778007 := bstep (se 1 (by rfl) ⟨583505, by rfl⟩ : syracuseStep 778007 = 1167011) B1167011
theorem B515883 : Blo 515797 515883 := bstep (se 1 (by rfl) ⟨386912, by rfl⟩ : syracuseStep 515883 = 773825) B773825
theorem B515895 : Blo 515797 515895 := bstep (se 1 (by rfl) ⟨386921, by rfl⟩ : syracuseStep 515895 = 773843) B773843
theorem B581431 : Blo 515797 581431 := bstep (se 1 (by rfl) ⟨436073, by rfl⟩ : syracuseStep 581431 = 872147) B872147
theorem B515915 : Blo 515797 515915 := bstep (se 1 (by rfl) ⟨386936, by rfl⟩ : syracuseStep 515915 = 773873) B773873
theorem B515927 : Blo 515797 515927 := bstep (se 1 (by rfl) ⟨386945, by rfl⟩ : syracuseStep 515927 = 773891) B773891
theorem B1105751 : Blo 515797 1105751 := bstep (se 1 (by rfl) ⟨829313, by rfl⟩ : syracuseStep 1105751 = 1658627) B1658627
theorem B778073 : Blo 515797 778073 := bstep (se 2 (by rfl) ⟨291777, by rfl⟩ : syracuseStep 778073 = 583555) B583555
theorem B515947 : Blo 515797 515947 := bstep (se 1 (by rfl) ⟨386960, by rfl⟩ : syracuseStep 515947 = 773921) B773921
theorem B515959 : Blo 515797 515959 := bstep (se 1 (by rfl) ⟨386969, by rfl⟩ : syracuseStep 515959 = 773939) B773939
theorem B515979 : Blo 515797 515979 := bstep (se 1 (by rfl) ⟨386984, by rfl⟩ : syracuseStep 515979 = 773969) B773969
theorem B515991 : Blo 515797 515991 := bstep (se 1 (by rfl) ⟨386993, by rfl⟩ : syracuseStep 515991 = 773987) B773987
theorem B516011 : Blo 515797 516011 := bstep (se 1 (by rfl) ⟨387008, by rfl⟩ : syracuseStep 516011 = 774017) B774017
theorem B516023 : Blo 515797 516023 := bstep (se 1 (by rfl) ⟨387017, by rfl⟩ : syracuseStep 516023 = 774035) B774035
theorem B516043 : Blo 515797 516043 := bstep (se 1 (by rfl) ⟨387032, by rfl⟩ : syracuseStep 516043 = 774065) B774065
theorem B778187 : Blo 515797 778187 := bstep (se 1 (by rfl) ⟨583640, by rfl⟩ : syracuseStep 778187 = 1167281) B1167281
theorem B516055 : Blo 515797 516055 := bstep (se 1 (by rfl) ⟨387041, by rfl⟩ : syracuseStep 516055 = 774083) B774083
theorem B778199 : Blo 515797 778199 := bstep (se 1 (by rfl) ⟨583649, by rfl⟩ : syracuseStep 778199 = 1167299) B1167299
theorem B516075 : Blo 515797 516075 := bstep (se 1 (by rfl) ⟨387056, by rfl⟩ : syracuseStep 516075 = 774113) B774113
theorem B581611 : Blo 515797 581611 := bstep (se 1 (by rfl) ⟨436208, by rfl⟩ : syracuseStep 581611 = 872417) B872417
theorem B516087 : Blo 515797 516087 := bstep (se 1 (by rfl) ⟨387065, by rfl⟩ : syracuseStep 516087 = 774131) B774131
theorem B516107 : Blo 515797 516107 := bstep (se 1 (by rfl) ⟨387080, by rfl⟩ : syracuseStep 516107 = 774161) B774161
theorem B516119 : Blo 515797 516119 := bstep (se 1 (by rfl) ⟨387089, by rfl⟩ : syracuseStep 516119 = 774179) B774179
theorem B778265 : Blo 515797 778265 := bstep (se 2 (by rfl) ⟨291849, by rfl⟩ : syracuseStep 778265 = 583699) B583699
theorem B516139 : Blo 515797 516139 := bstep (se 1 (by rfl) ⟨387104, by rfl⟩ : syracuseStep 516139 = 774209) B774209
theorem B516151 : Blo 515797 516151 := bstep (se 1 (by rfl) ⟨387113, by rfl⟩ : syracuseStep 516151 = 774227) B774227
theorem B516171 : Blo 515797 516171 := bstep (se 1 (by rfl) ⟨387128, by rfl⟩ : syracuseStep 516171 = 774257) B774257
theorem B516183 : Blo 515797 516183 := bstep (se 1 (by rfl) ⟨387137, by rfl⟩ : syracuseStep 516183 = 774275) B774275
theorem B581719 : Blo 515797 581719 := bstep (se 1 (by rfl) ⟨436289, by rfl⟩ : syracuseStep 581719 = 872579) B872579
theorem B516203 : Blo 515797 516203 := bstep (se 1 (by rfl) ⟨387152, by rfl⟩ : syracuseStep 516203 = 774305) B774305
theorem B516215 : Blo 515797 516215 := bstep (se 1 (by rfl) ⟨387161, by rfl⟩ : syracuseStep 516215 = 774323) B774323
theorem B516235 : Blo 515797 516235 := bstep (se 1 (by rfl) ⟨387176, by rfl⟩ : syracuseStep 516235 = 774353) B774353
theorem B778379 : Blo 515797 778379 := bstep (se 1 (by rfl) ⟨583784, by rfl⟩ : syracuseStep 778379 = 1167569) B1167569
theorem B876683 : Blo 515797 876683 := bstep (se 1 (by rfl) ⟨657512, by rfl⟩ : syracuseStep 876683 = 1315025) B1315025
theorem B516247 : Blo 515797 516247 := bstep (se 1 (by rfl) ⟨387185, by rfl⟩ : syracuseStep 516247 = 774371) B774371
theorem B778391 : Blo 515797 778391 := bstep (se 1 (by rfl) ⟨583793, by rfl⟩ : syracuseStep 778391 = 1167587) B1167587
theorem B516267 : Blo 515797 516267 := bstep (se 1 (by rfl) ⟨387200, by rfl⟩ : syracuseStep 516267 = 774401) B774401
theorem B516279 : Blo 515797 516279 := bstep (se 1 (by rfl) ⟨387209, by rfl⟩ : syracuseStep 516279 = 774419) B774419
theorem B516299 : Blo 515797 516299 := bstep (se 1 (by rfl) ⟨387224, by rfl⟩ : syracuseStep 516299 = 774449) B774449
theorem B516311 : Blo 515797 516311 := bstep (se 1 (by rfl) ⟨387233, by rfl⟩ : syracuseStep 516311 = 774467) B774467
theorem B778457 : Blo 515797 778457 := bstep (se 2 (by rfl) ⟨291921, by rfl⟩ : syracuseStep 778457 = 583843) B583843
theorem B516331 : Blo 515797 516331 := bstep (se 1 (by rfl) ⟨387248, by rfl⟩ : syracuseStep 516331 = 774497) B774497
theorem B516343 : Blo 515797 516343 := bstep (se 1 (by rfl) ⟨387257, by rfl⟩ : syracuseStep 516343 = 774515) B774515
theorem B516363 : Blo 515797 516363 := bstep (se 1 (by rfl) ⟨387272, by rfl⟩ : syracuseStep 516363 = 774545) B774545
theorem B581899 : Blo 515797 581899 := bstep (se 1 (by rfl) ⟨436424, by rfl⟩ : syracuseStep 581899 = 872849) B872849
theorem B876811 : Blo 515797 876811 := bstep (se 1 (by rfl) ⟨657608, by rfl⟩ : syracuseStep 876811 = 1315217) B1315217
theorem B93184277 : Blo 515797 93184277 := bstep (se 6 (by rfl) ⟨2184006, by rfl⟩ : syracuseStep 93184277 = 4368013) B4368013
theorem B516375 : Blo 515797 516375 := bstep (se 1 (by rfl) ⟨387281, by rfl⟩ : syracuseStep 516375 = 774563) B774563
theorem B516395 : Blo 515797 516395 := bstep (se 1 (by rfl) ⟨387296, by rfl⟩ : syracuseStep 516395 = 774593) B774593
theorem B516407 : Blo 515797 516407 := bstep (se 1 (by rfl) ⟨387305, by rfl⟩ : syracuseStep 516407 = 774611) B774611
theorem B516427 : Blo 515797 516427 := bstep (se 1 (by rfl) ⟨387320, by rfl⟩ : syracuseStep 516427 = 774641) B774641
theorem B778571 : Blo 515797 778571 := bstep (se 1 (by rfl) ⟨583928, by rfl⟩ : syracuseStep 778571 = 1167857) B1167857
theorem B516439 : Blo 515797 516439 := bstep (se 1 (by rfl) ⟨387329, by rfl⟩ : syracuseStep 516439 = 774659) B774659
theorem B778583 : Blo 515797 778583 := bstep (se 1 (by rfl) ⟨583937, by rfl⟩ : syracuseStep 778583 = 1167875) B1167875
theorem B516459 : Blo 515797 516459 := bstep (se 1 (by rfl) ⟨387344, by rfl⟩ : syracuseStep 516459 = 774689) B774689
theorem B516471 : Blo 515797 516471 := bstep (se 1 (by rfl) ⟨387353, by rfl⟩ : syracuseStep 516471 = 774707) B774707
theorem B582007 : Blo 515797 582007 := bstep (se 1 (by rfl) ⟨436505, by rfl⟩ : syracuseStep 582007 = 873011) B873011
theorem B516491 : Blo 515797 516491 := bstep (se 1 (by rfl) ⟨387368, by rfl⟩ : syracuseStep 516491 = 774737) B774737
theorem B1106315 : Blo 515797 1106315 := bstep (se 1 (by rfl) ⟨829736, by rfl⟩ : syracuseStep 1106315 = 1659473) B1659473
theorem B516503 : Blo 515797 516503 := bstep (se 1 (by rfl) ⟨387377, by rfl⟩ : syracuseStep 516503 = 774755) B774755
theorem B778649 : Blo 515797 778649 := bstep (se 2 (by rfl) ⟨291993, by rfl⟩ : syracuseStep 778649 = 583987) B583987
theorem B876953 : Blo 515797 876953 := bstep (se 2 (by rfl) ⟨328857, by rfl⟩ : syracuseStep 876953 = 657715) B657715
theorem B516523 : Blo 515797 516523 := bstep (se 1 (by rfl) ⟨387392, by rfl⟩ : syracuseStep 516523 = 774785) B774785
theorem B516535 : Blo 515797 516535 := bstep (se 1 (by rfl) ⟨387401, by rfl⟩ : syracuseStep 516535 = 774803) B774803
theorem B516555 : Blo 515797 516555 := bstep (se 1 (by rfl) ⟨387416, by rfl⟩ : syracuseStep 516555 = 774833) B774833
theorem B516567 : Blo 515797 516567 := bstep (se 1 (by rfl) ⟨387425, by rfl⟩ : syracuseStep 516567 = 774851) B774851
theorem B516587 : Blo 515797 516587 := bstep (se 1 (by rfl) ⟨387440, by rfl⟩ : syracuseStep 516587 = 774881) B774881
theorem B516599 : Blo 515797 516599 := bstep (se 1 (by rfl) ⟨387449, by rfl⟩ : syracuseStep 516599 = 774899) B774899
theorem B516619 : Blo 515797 516619 := bstep (se 1 (by rfl) ⟨387464, by rfl⟩ : syracuseStep 516619 = 774929) B774929
theorem B778763 : Blo 515797 778763 := bstep (se 1 (by rfl) ⟨584072, by rfl⟩ : syracuseStep 778763 = 1168145) B1168145
theorem B516631 : Blo 515797 516631 := bstep (se 1 (by rfl) ⟨387473, by rfl⟩ : syracuseStep 516631 = 774947) B774947
theorem B778775 : Blo 515797 778775 := bstep (se 1 (by rfl) ⟨584081, by rfl⟩ : syracuseStep 778775 = 1168163) B1168163
theorem B877081 : Blo 515797 877081 := bstep (se 2 (by rfl) ⟨328905, by rfl⟩ : syracuseStep 877081 = 657811) B657811
theorem B516651 : Blo 515797 516651 := bstep (se 1 (by rfl) ⟨387488, by rfl⟩ : syracuseStep 516651 = 774977) B774977
theorem B582187 : Blo 515797 582187 := bstep (se 1 (by rfl) ⟨436640, by rfl⟩ : syracuseStep 582187 = 873281) B873281
theorem B516663 : Blo 515797 516663 := bstep (se 1 (by rfl) ⟨387497, by rfl⟩ : syracuseStep 516663 = 774995) B774995
theorem B516683 : Blo 515797 516683 := bstep (se 1 (by rfl) ⟨387512, by rfl⟩ : syracuseStep 516683 = 775025) B775025
theorem B516695 : Blo 515797 516695 := bstep (se 1 (by rfl) ⟨387521, by rfl⟩ : syracuseStep 516695 = 775043) B775043
theorem B1958489 : Blo 515797 1958489 := bstep (se 2 (by rfl) ⟨734433, by rfl⟩ : syracuseStep 1958489 = 1468867) B1468867
theorem B778841 : Blo 515797 778841 := bstep (se 2 (by rfl) ⟨292065, by rfl⟩ : syracuseStep 778841 = 584131) B584131
theorem B516715 : Blo 515797 516715 := bstep (se 1 (by rfl) ⟨387536, by rfl⟩ : syracuseStep 516715 = 775073) B775073
theorem B516727 : Blo 515797 516727 := bstep (se 1 (by rfl) ⟨387545, by rfl⟩ : syracuseStep 516727 = 775091) B775091
theorem B516747 : Blo 515797 516747 := bstep (se 1 (by rfl) ⟨387560, by rfl⟩ : syracuseStep 516747 = 775121) B775121
theorem B516759 : Blo 515797 516759 := bstep (se 1 (by rfl) ⟨387569, by rfl⟩ : syracuseStep 516759 = 775139) B775139
theorem B582295 : Blo 515797 582295 := bstep (se 1 (by rfl) ⟨436721, by rfl⟩ : syracuseStep 582295 = 873443) B873443
theorem B516779 : Blo 515797 516779 := bstep (se 1 (by rfl) ⟨387584, by rfl⟩ : syracuseStep 516779 = 775169) B775169
theorem B516791 : Blo 515797 516791 := bstep (se 1 (by rfl) ⟨387593, by rfl⟩ : syracuseStep 516791 = 775187) B775187
theorem B516811 : Blo 515797 516811 := bstep (se 1 (by rfl) ⟨387608, by rfl⟩ : syracuseStep 516811 = 775217) B775217
theorem B778955 : Blo 515797 778955 := bstep (se 1 (by rfl) ⟨584216, by rfl⟩ : syracuseStep 778955 = 1168433) B1168433
theorem B516823 : Blo 515797 516823 := bstep (se 1 (by rfl) ⟨387617, by rfl⟩ : syracuseStep 516823 = 775235) B775235
theorem B778967 : Blo 515797 778967 := bstep (se 1 (by rfl) ⟨584225, by rfl⟩ : syracuseStep 778967 = 1168451) B1168451
theorem B516843 : Blo 515797 516843 := bstep (se 1 (by rfl) ⟨387632, by rfl⟩ : syracuseStep 516843 = 775265) B775265
theorem B516855 : Blo 515797 516855 := bstep (se 1 (by rfl) ⟨387641, by rfl⟩ : syracuseStep 516855 = 775283) B775283
theorem B516875 : Blo 515797 516875 := bstep (se 1 (by rfl) ⟨387656, by rfl⟩ : syracuseStep 516875 = 775313) B775313
theorem B516887 : Blo 515797 516887 := bstep (se 1 (by rfl) ⟨387665, by rfl⟩ : syracuseStep 516887 = 775331) B775331
theorem B779033 : Blo 515797 779033 := bstep (se 2 (by rfl) ⟨292137, by rfl⟩ : syracuseStep 779033 = 584275) B584275
theorem B516907 : Blo 515797 516907 := bstep (se 1 (by rfl) ⟨387680, by rfl⟩ : syracuseStep 516907 = 775361) B775361
theorem B1958701 : Blo 515797 1958701 := bstep (se 3 (by rfl) ⟨367256, by rfl⟩ : syracuseStep 1958701 = 734513) B734513
theorem B516919 : Blo 515797 516919 := bstep (se 1 (by rfl) ⟨387689, by rfl⟩ : syracuseStep 516919 = 775379) B775379
theorem B516939 : Blo 515797 516939 := bstep (se 1 (by rfl) ⟨387704, by rfl⟩ : syracuseStep 516939 = 775409) B775409
theorem B582475 : Blo 515797 582475 := bstep (se 1 (by rfl) ⟨436856, by rfl⟩ : syracuseStep 582475 = 873713) B873713
theorem B516951 : Blo 515797 516951 := bstep (se 1 (by rfl) ⟨387713, by rfl⟩ : syracuseStep 516951 = 775427) B775427
theorem B1106777 : Blo 515797 1106777 := bstep (se 2 (by rfl) ⟨415041, by rfl⟩ : syracuseStep 1106777 = 830083) B830083
theorem B516971 : Blo 515797 516971 := bstep (se 1 (by rfl) ⟨387728, by rfl⟩ : syracuseStep 516971 = 775457) B775457
theorem B516983 : Blo 515797 516983 := bstep (se 1 (by rfl) ⟨387737, by rfl⟩ : syracuseStep 516983 = 775475) B775475
theorem B517003 : Blo 515797 517003 := bstep (se 1 (by rfl) ⟨387752, by rfl⟩ : syracuseStep 517003 = 775505) B775505
theorem B779147 : Blo 515797 779147 := bstep (se 1 (by rfl) ⟨584360, by rfl⟩ : syracuseStep 779147 = 1168721) B1168721
theorem B517015 : Blo 515797 517015 := bstep (se 1 (by rfl) ⟨387761, by rfl⟩ : syracuseStep 517015 = 775523) B775523
theorem B779159 : Blo 515797 779159 := bstep (se 1 (by rfl) ⟨584369, by rfl⟩ : syracuseStep 779159 = 1168739) B1168739
theorem B517035 : Blo 515797 517035 := bstep (se 1 (by rfl) ⟨387776, by rfl⟩ : syracuseStep 517035 = 775553) B775553
theorem B517047 : Blo 515797 517047 := bstep (se 1 (by rfl) ⟨387785, by rfl⟩ : syracuseStep 517047 = 775571) B775571
theorem B582583 : Blo 515797 582583 := bstep (se 1 (by rfl) ⟨436937, by rfl⟩ : syracuseStep 582583 = 873875) B873875
theorem B517067 : Blo 515797 517067 := bstep (se 1 (by rfl) ⟨387800, by rfl⟩ : syracuseStep 517067 = 775601) B775601
theorem B517079 : Blo 515797 517079 := bstep (se 1 (by rfl) ⟨387809, by rfl⟩ : syracuseStep 517079 = 775619) B775619
theorem B779225 : Blo 515797 779225 := bstep (se 2 (by rfl) ⟨292209, by rfl⟩ : syracuseStep 779225 = 584419) B584419
theorem B517099 : Blo 515797 517099 := bstep (se 1 (by rfl) ⟨387824, by rfl⟩ : syracuseStep 517099 = 775649) B775649
theorem B517111 : Blo 515797 517111 := bstep (se 1 (by rfl) ⟨387833, by rfl⟩ : syracuseStep 517111 = 775667) B775667
theorem B4482053 : Blo 515797 4482053 := bstep (se 4 (by rfl) ⟨420192, by rfl⟩ : syracuseStep 4482053 = 840385) B840385
theorem B517131 : Blo 515797 517131 := bstep (se 1 (by rfl) ⟨387848, by rfl⟩ : syracuseStep 517131 = 775697) B775697
theorem B517143 : Blo 515797 517143 := bstep (se 1 (by rfl) ⟨387857, by rfl⟩ : syracuseStep 517143 = 775715) B775715
theorem B1664023 : Blo 515797 1664023 := bstep (se 1 (by rfl) ⟨1248017, by rfl⟩ : syracuseStep 1664023 = 2496035) B2496035
theorem B517163 : Blo 515797 517163 := bstep (se 1 (by rfl) ⟨387872, by rfl⟩ : syracuseStep 517163 = 775745) B775745
theorem B517175 : Blo 515797 517175 := bstep (se 1 (by rfl) ⟨387881, by rfl⟩ : syracuseStep 517175 = 775763) B775763
theorem B517195 : Blo 515797 517195 := bstep (se 1 (by rfl) ⟨387896, by rfl⟩ : syracuseStep 517195 = 775793) B775793
theorem B779339 : Blo 515797 779339 := bstep (se 1 (by rfl) ⟨584504, by rfl⟩ : syracuseStep 779339 = 1169009) B1169009
theorem B517207 : Blo 515797 517207 := bstep (se 1 (by rfl) ⟨387905, by rfl⟩ : syracuseStep 517207 = 775811) B775811
theorem B779351 : Blo 515797 779351 := bstep (se 1 (by rfl) ⟨584513, by rfl⟩ : syracuseStep 779351 = 1169027) B1169027
theorem B1959005 : Blo 515797 1959005 := bstep (se 3 (by rfl) ⟨367313, by rfl⟩ : syracuseStep 1959005 = 734627) B734627
theorem B517227 : Blo 515797 517227 := bstep (se 1 (by rfl) ⟨387920, by rfl⟩ : syracuseStep 517227 = 775841) B775841
theorem B582763 : Blo 515797 582763 := bstep (se 1 (by rfl) ⟨437072, by rfl⟩ : syracuseStep 582763 = 874145) B874145
theorem B517239 : Blo 515797 517239 := bstep (se 1 (by rfl) ⟨387929, by rfl⟩ : syracuseStep 517239 = 775859) B775859
theorem B517259 : Blo 515797 517259 := bstep (se 1 (by rfl) ⟨387944, by rfl⟩ : syracuseStep 517259 = 775889) B775889
theorem B517271 : Blo 515797 517271 := bstep (se 1 (by rfl) ⟨387953, by rfl⟩ : syracuseStep 517271 = 775907) B775907
theorem B779417 : Blo 515797 779417 := bstep (se 2 (by rfl) ⟨292281, by rfl⟩ : syracuseStep 779417 = 584563) B584563
theorem B517291 : Blo 515797 517291 := bstep (se 1 (by rfl) ⟨387968, by rfl⟩ : syracuseStep 517291 = 775937) B775937
theorem B517303 : Blo 515797 517303 := bstep (se 1 (by rfl) ⟨387977, by rfl⟩ : syracuseStep 517303 = 775955) B775955
theorem B517323 : Blo 515797 517323 := bstep (se 1 (by rfl) ⟨387992, by rfl⟩ : syracuseStep 517323 = 775985) B775985
theorem B517335 : Blo 515797 517335 := bstep (se 1 (by rfl) ⟨388001, by rfl⟩ : syracuseStep 517335 = 776003) B776003
theorem B582871 : Blo 515797 582871 := bstep (se 1 (by rfl) ⟨437153, by rfl⟩ : syracuseStep 582871 = 874307) B874307
theorem B517355 : Blo 515797 517355 := bstep (se 1 (by rfl) ⟨388016, by rfl⟩ : syracuseStep 517355 = 776033) B776033
theorem B517367 : Blo 515797 517367 := bstep (se 1 (by rfl) ⟨388025, by rfl⟩ : syracuseStep 517367 = 776051) B776051
theorem B517387 : Blo 515797 517387 := bstep (se 1 (by rfl) ⟨388040, by rfl⟩ : syracuseStep 517387 = 776081) B776081
theorem B779531 : Blo 515797 779531 := bstep (se 1 (by rfl) ⟨584648, by rfl⟩ : syracuseStep 779531 = 1169297) B1169297
theorem B517399 : Blo 515797 517399 := bstep (se 1 (by rfl) ⟨388049, by rfl⟩ : syracuseStep 517399 = 776099) B776099
theorem B779543 : Blo 515797 779543 := bstep (se 1 (by rfl) ⟨584657, by rfl⟩ : syracuseStep 779543 = 1169315) B1169315
theorem B517419 : Blo 515797 517419 := bstep (se 1 (by rfl) ⟨388064, by rfl⟩ : syracuseStep 517419 = 776129) B776129
theorem B517431 : Blo 515797 517431 := bstep (se 1 (by rfl) ⟨388073, by rfl⟩ : syracuseStep 517431 = 776147) B776147
theorem B517451 : Blo 515797 517451 := bstep (se 1 (by rfl) ⟨388088, by rfl⟩ : syracuseStep 517451 = 776177) B776177
theorem B517463 : Blo 515797 517463 := bstep (se 1 (by rfl) ⟨388097, by rfl⟩ : syracuseStep 517463 = 776195) B776195
theorem B779609 : Blo 515797 779609 := bstep (se 2 (by rfl) ⟨292353, by rfl⟩ : syracuseStep 779609 = 584707) B584707
theorem B517483 : Blo 515797 517483 := bstep (se 1 (by rfl) ⟨388112, by rfl⟩ : syracuseStep 517483 = 776225) B776225
theorem B9954677 : Blo 515797 9954677 := bstep (se 5 (by rfl) ⟨466625, by rfl⟩ : syracuseStep 9954677 = 933251) B933251
theorem B517495 : Blo 515797 517495 := bstep (se 1 (by rfl) ⟨388121, by rfl⟩ : syracuseStep 517495 = 776243) B776243
theorem B517515 : Blo 515797 517515 := bstep (se 1 (by rfl) ⟨388136, by rfl⟩ : syracuseStep 517515 = 776273) B776273
theorem B583051 : Blo 515797 583051 := bstep (se 1 (by rfl) ⟨437288, by rfl⟩ : syracuseStep 583051 = 874577) B874577
theorem B2614679 : Blo 515797 2614679 := bstep (se 1 (by rfl) ⟨1961009, by rfl⟩ : syracuseStep 2614679 = 3922019) B3922019
theorem B517527 : Blo 515797 517527 := bstep (se 1 (by rfl) ⟨388145, by rfl⟩ : syracuseStep 517527 = 776291) B776291
theorem B517547 : Blo 515797 517547 := bstep (se 1 (by rfl) ⟨388160, by rfl⟩ : syracuseStep 517547 = 776321) B776321
theorem B2483635 : Blo 515797 2483635 := bstep (se 1 (by rfl) ⟨1862726, by rfl⟩ : syracuseStep 2483635 = 3725453) B3725453
theorem B517559 : Blo 515797 517559 := bstep (se 1 (by rfl) ⟨388169, by rfl⟩ : syracuseStep 517559 = 776339) B776339
theorem B517579 : Blo 515797 517579 := bstep (se 1 (by rfl) ⟨388184, by rfl⟩ : syracuseStep 517579 = 776369) B776369
theorem B517591 : Blo 515797 517591 := bstep (se 1 (by rfl) ⟨388193, by rfl⟩ : syracuseStep 517591 = 776387) B776387
theorem B517611 : Blo 515797 517611 := bstep (se 1 (by rfl) ⟨388208, by rfl⟩ : syracuseStep 517611 = 776417) B776417
theorem B517623 : Blo 515797 517623 := bstep (se 1 (by rfl) ⟨388217, by rfl⟩ : syracuseStep 517623 = 776435) B776435
theorem B583159 : Blo 515797 583159 := bstep (se 1 (by rfl) ⟨437369, by rfl⟩ : syracuseStep 583159 = 874739) B874739
theorem B517643 : Blo 515797 517643 := bstep (se 1 (by rfl) ⟨388232, by rfl⟩ : syracuseStep 517643 = 776465) B776465
theorem B517655 : Blo 515797 517655 := bstep (se 1 (by rfl) ⟨388241, by rfl⟩ : syracuseStep 517655 = 776483) B776483
theorem B517675 : Blo 515797 517675 := bstep (se 1 (by rfl) ⟨388256, by rfl⟩ : syracuseStep 517675 = 776513) B776513
theorem B517687 : Blo 515797 517687 := bstep (se 1 (by rfl) ⟨388265, by rfl⟩ : syracuseStep 517687 = 776531) B776531
theorem B517707 : Blo 515797 517707 := bstep (se 1 (by rfl) ⟨388280, by rfl⟩ : syracuseStep 517707 = 776561) B776561
theorem B517719 : Blo 515797 517719 := bstep (se 1 (by rfl) ⟨388289, by rfl⟩ : syracuseStep 517719 = 776579) B776579
theorem B517739 : Blo 515797 517739 := bstep (se 1 (by rfl) ⟨388304, by rfl⟩ : syracuseStep 517739 = 776609) B776609
theorem B517751 : Blo 515797 517751 := bstep (se 1 (by rfl) ⟨388313, by rfl⟩ : syracuseStep 517751 = 776627) B776627
theorem B2385539 : Blo 515797 2385539 := bstep (se 1 (by rfl) ⟨1789154, by rfl⟩ : syracuseStep 2385539 = 3578309) B3578309
theorem B517771 : Blo 515797 517771 := bstep (se 1 (by rfl) ⟨388328, by rfl⟩ : syracuseStep 517771 = 776657) B776657
theorem B517783 : Blo 515797 517783 := bstep (se 1 (by rfl) ⟨388337, by rfl⟩ : syracuseStep 517783 = 776675) B776675
theorem B517803 : Blo 515797 517803 := bstep (se 1 (by rfl) ⟨388352, by rfl⟩ : syracuseStep 517803 = 776705) B776705
theorem B583339 : Blo 515797 583339 := bstep (se 1 (by rfl) ⟨437504, by rfl⟩ : syracuseStep 583339 = 875009) B875009
theorem B517815 : Blo 515797 517815 := bstep (se 1 (by rfl) ⟨388361, by rfl⟩ : syracuseStep 517815 = 776723) B776723
theorem B517835 : Blo 515797 517835 := bstep (se 1 (by rfl) ⟨388376, by rfl⟩ : syracuseStep 517835 = 776753) B776753
theorem B517847 : Blo 515797 517847 := bstep (se 1 (by rfl) ⟨388385, by rfl⟩ : syracuseStep 517847 = 776771) B776771
theorem B517867 : Blo 515797 517867 := bstep (se 1 (by rfl) ⟨388400, by rfl⟩ : syracuseStep 517867 = 776801) B776801
theorem B517879 : Blo 515797 517879 := bstep (se 1 (by rfl) ⟨388409, by rfl⟩ : syracuseStep 517879 = 776819) B776819
theorem B517899 : Blo 515797 517899 := bstep (se 1 (by rfl) ⟨388424, by rfl⟩ : syracuseStep 517899 = 776849) B776849
theorem B517911 : Blo 515797 517911 := bstep (se 1 (by rfl) ⟨388433, by rfl⟩ : syracuseStep 517911 = 776867) B776867
theorem B583447 : Blo 515797 583447 := bstep (se 1 (by rfl) ⟨437585, by rfl⟩ : syracuseStep 583447 = 875171) B875171
theorem B517931 : Blo 515797 517931 := bstep (se 1 (by rfl) ⟨388448, by rfl⟩ : syracuseStep 517931 = 776897) B776897
theorem B517943 : Blo 515797 517943 := bstep (se 1 (by rfl) ⟨388457, by rfl⟩ : syracuseStep 517943 = 776915) B776915
theorem B517963 : Blo 515797 517963 := bstep (se 1 (by rfl) ⟨388472, by rfl⟩ : syracuseStep 517963 = 776945) B776945
theorem B517975 : Blo 515797 517975 := bstep (se 1 (by rfl) ⟨388481, by rfl⟩ : syracuseStep 517975 = 776963) B776963
theorem B517995 : Blo 515797 517995 := bstep (se 1 (by rfl) ⟨388496, by rfl⟩ : syracuseStep 517995 = 776993) B776993
theorem B518007 : Blo 515797 518007 := bstep (se 1 (by rfl) ⟨388505, by rfl⟩ : syracuseStep 518007 = 777011) B777011
theorem B518027 : Blo 515797 518027 := bstep (se 1 (by rfl) ⟨388520, by rfl⟩ : syracuseStep 518027 = 777041) B777041
theorem B518039 : Blo 515797 518039 := bstep (se 1 (by rfl) ⟨388529, by rfl⟩ : syracuseStep 518039 = 777059) B777059
theorem B518059 : Blo 515797 518059 := bstep (se 1 (by rfl) ⟨388544, by rfl⟩ : syracuseStep 518059 = 777089) B777089
theorem B3139507 : Blo 515797 3139507 := bstep (se 1 (by rfl) ⟨2354630, by rfl⟩ : syracuseStep 3139507 = 4709261) B4709261
theorem B518071 : Blo 515797 518071 := bstep (se 1 (by rfl) ⟨388553, by rfl⟩ : syracuseStep 518071 = 777107) B777107
theorem B518091 : Blo 515797 518091 := bstep (se 1 (by rfl) ⟨388568, by rfl⟩ : syracuseStep 518091 = 777137) B777137
theorem B583627 : Blo 515797 583627 := bstep (se 1 (by rfl) ⟨437720, by rfl⟩ : syracuseStep 583627 = 875441) B875441
theorem B518103 : Blo 515797 518103 := bstep (se 1 (by rfl) ⟨388577, by rfl⟩ : syracuseStep 518103 = 777155) B777155
theorem B518123 : Blo 515797 518123 := bstep (se 1 (by rfl) ⟨388592, by rfl⟩ : syracuseStep 518123 = 777185) B777185
theorem B1107955 : Blo 515797 1107955 := bstep (se 1 (by rfl) ⟨830966, by rfl⟩ : syracuseStep 1107955 = 1661933) B1661933
theorem B518135 : Blo 515797 518135 := bstep (se 1 (by rfl) ⟨388601, by rfl⟩ : syracuseStep 518135 = 777203) B777203
theorem B518155 : Blo 515797 518155 := bstep (se 1 (by rfl) ⟨388616, by rfl⟩ : syracuseStep 518155 = 777233) B777233
theorem B518167 : Blo 515797 518167 := bstep (se 1 (by rfl) ⟨388625, by rfl⟩ : syracuseStep 518167 = 777251) B777251
theorem B518187 : Blo 515797 518187 := bstep (se 1 (by rfl) ⟨388640, by rfl⟩ : syracuseStep 518187 = 777281) B777281
theorem B518199 : Blo 515797 518199 := bstep (se 1 (by rfl) ⟨388649, by rfl⟩ : syracuseStep 518199 = 777299) B777299
theorem B583735 : Blo 515797 583735 := bstep (se 1 (by rfl) ⟨437801, by rfl⟩ : syracuseStep 583735 = 875603) B875603
theorem B518219 : Blo 515797 518219 := bstep (se 1 (by rfl) ⟨388664, by rfl⟩ : syracuseStep 518219 = 777329) B777329
theorem B518231 : Blo 515797 518231 := bstep (se 1 (by rfl) ⟨388673, by rfl⟩ : syracuseStep 518231 = 777347) B777347
theorem B518251 : Blo 515797 518251 := bstep (se 1 (by rfl) ⟨388688, by rfl⟩ : syracuseStep 518251 = 777377) B777377
theorem B518263 : Blo 515797 518263 := bstep (se 1 (by rfl) ⟨388697, by rfl⟩ : syracuseStep 518263 = 777395) B777395
theorem B518283 : Blo 515797 518283 := bstep (se 1 (by rfl) ⟨388712, by rfl⟩ : syracuseStep 518283 = 777425) B777425
theorem B518295 : Blo 515797 518295 := bstep (se 1 (by rfl) ⟨388721, by rfl⟩ : syracuseStep 518295 = 777443) B777443
theorem B518315 : Blo 515797 518315 := bstep (se 1 (by rfl) ⟨388736, by rfl⟩ : syracuseStep 518315 = 777473) B777473
theorem B1861805 : Blo 515797 1861805 := bstep (se 3 (by rfl) ⟨349088, by rfl⟩ : syracuseStep 1861805 = 698177) B698177
theorem B2943155 : Blo 515797 2943155 := bstep (se 1 (by rfl) ⟨2207366, by rfl⟩ : syracuseStep 2943155 = 4414733) B4414733
theorem B518327 : Blo 515797 518327 := bstep (se 1 (by rfl) ⟨388745, by rfl⟩ : syracuseStep 518327 = 777491) B777491
theorem B518347 : Blo 515797 518347 := bstep (se 1 (by rfl) ⟨388760, by rfl⟩ : syracuseStep 518347 = 777521) B777521
theorem B518359 : Blo 515797 518359 := bstep (se 1 (by rfl) ⟨388769, by rfl⟩ : syracuseStep 518359 = 777539) B777539
theorem B518379 : Blo 515797 518379 := bstep (se 1 (by rfl) ⟨388784, by rfl⟩ : syracuseStep 518379 = 777569) B777569
theorem B583915 : Blo 515797 583915 := bstep (se 1 (by rfl) ⟨437936, by rfl⟩ : syracuseStep 583915 = 875873) B875873
theorem B518391 : Blo 515797 518391 := bstep (se 1 (by rfl) ⟨388793, by rfl⟩ : syracuseStep 518391 = 777587) B777587
theorem B518411 : Blo 515797 518411 := bstep (se 1 (by rfl) ⟨388808, by rfl⟩ : syracuseStep 518411 = 777617) B777617
theorem B518423 : Blo 515797 518423 := bstep (se 1 (by rfl) ⟨388817, by rfl⟩ : syracuseStep 518423 = 777635) B777635
theorem B518443 : Blo 515797 518443 := bstep (se 1 (by rfl) ⟨388832, by rfl⟩ : syracuseStep 518443 = 777665) B777665
theorem B518455 : Blo 515797 518455 := bstep (se 1 (by rfl) ⟨388841, by rfl⟩ : syracuseStep 518455 = 777683) B777683
theorem B518475 : Blo 515797 518475 := bstep (se 1 (by rfl) ⟨388856, by rfl⟩ : syracuseStep 518475 = 777713) B777713
theorem B518487 : Blo 515797 518487 := bstep (se 1 (by rfl) ⟨388865, by rfl⟩ : syracuseStep 518487 = 777731) B777731
theorem B584023 : Blo 515797 584023 := bstep (se 1 (by rfl) ⟨438017, by rfl⟩ : syracuseStep 584023 = 876035) B876035
theorem B518507 : Blo 515797 518507 := bstep (se 1 (by rfl) ⟨388880, by rfl⟩ : syracuseStep 518507 = 777761) B777761
theorem B60615029 : Blo 515797 60615029 := bstep (se 5 (by rfl) ⟨2841329, by rfl⟩ : syracuseStep 60615029 = 5682659) B5682659
theorem B518519 : Blo 515797 518519 := bstep (se 1 (by rfl) ⟨388889, by rfl⟩ : syracuseStep 518519 = 777779) B777779
theorem B518539 : Blo 515797 518539 := bstep (se 1 (by rfl) ⟨388904, by rfl⟩ : syracuseStep 518539 = 777809) B777809
theorem B518551 : Blo 515797 518551 := bstep (se 1 (by rfl) ⟨388913, by rfl⟩ : syracuseStep 518551 = 777827) B777827
theorem B518571 : Blo 515797 518571 := bstep (se 1 (by rfl) ⟨388928, by rfl⟩ : syracuseStep 518571 = 777857) B777857
theorem B518583 : Blo 515797 518583 := bstep (se 1 (by rfl) ⟨388937, by rfl⟩ : syracuseStep 518583 = 777875) B777875
theorem B1108417 : Blo 515797 1108417 := bstep (se 2 (by rfl) ⟨415656, by rfl⟩ : syracuseStep 1108417 = 831313) B831313
theorem B518603 : Blo 515797 518603 := bstep (se 1 (by rfl) ⟨388952, by rfl⟩ : syracuseStep 518603 = 777905) B777905
theorem B518615 : Blo 515797 518615 := bstep (se 1 (by rfl) ⟨388961, by rfl⟩ : syracuseStep 518615 = 777923) B777923
theorem B518635 : Blo 515797 518635 := bstep (se 1 (by rfl) ⟨388976, by rfl⟩ : syracuseStep 518635 = 777953) B777953
theorem B518647 : Blo 515797 518647 := bstep (se 1 (by rfl) ⟨388985, by rfl⟩ : syracuseStep 518647 = 777971) B777971
theorem B518667 : Blo 515797 518667 := bstep (se 1 (by rfl) ⟨389000, by rfl⟩ : syracuseStep 518667 = 778001) B778001
theorem B584203 : Blo 515797 584203 := bstep (se 1 (by rfl) ⟨438152, by rfl⟩ : syracuseStep 584203 = 876305) B876305
theorem B518679 : Blo 515797 518679 := bstep (se 1 (by rfl) ⟨389009, by rfl⟩ : syracuseStep 518679 = 778019) B778019
theorem B518699 : Blo 515797 518699 := bstep (se 1 (by rfl) ⟨389024, by rfl⟩ : syracuseStep 518699 = 778049) B778049
theorem B518711 : Blo 515797 518711 := bstep (se 1 (by rfl) ⟨389033, by rfl⟩ : syracuseStep 518711 = 778067) B778067
theorem B518731 : Blo 515797 518731 := bstep (se 1 (by rfl) ⟨389048, by rfl⟩ : syracuseStep 518731 = 778097) B778097
theorem B518743 : Blo 515797 518743 := bstep (se 1 (by rfl) ⟨389057, by rfl⟩ : syracuseStep 518743 = 778115) B778115
theorem B3992165 : Blo 515797 3992165 := bstep (se 4 (by rfl) ⟨374265, by rfl⟩ : syracuseStep 3992165 = 748531) B748531
theorem B518763 : Blo 515797 518763 := bstep (se 1 (by rfl) ⟨389072, by rfl⟩ : syracuseStep 518763 = 778145) B778145
theorem B518775 : Blo 515797 518775 := bstep (se 1 (by rfl) ⟨389081, by rfl⟩ : syracuseStep 518775 = 778163) B778163
theorem B584311 : Blo 515797 584311 := bstep (se 1 (by rfl) ⟨438233, by rfl⟩ : syracuseStep 584311 = 876467) B876467
theorem B518795 : Blo 515797 518795 := bstep (se 1 (by rfl) ⟨389096, by rfl⟩ : syracuseStep 518795 = 778193) B778193
theorem B518807 : Blo 515797 518807 := bstep (se 1 (by rfl) ⟨389105, by rfl⟩ : syracuseStep 518807 = 778211) B778211
theorem B518827 : Blo 515797 518827 := bstep (se 1 (by rfl) ⟨389120, by rfl⟩ : syracuseStep 518827 = 778241) B778241
theorem B518839 : Blo 515797 518839 := bstep (se 1 (by rfl) ⟨389129, by rfl⟩ : syracuseStep 518839 = 778259) B778259
theorem B518859 : Blo 515797 518859 := bstep (se 1 (by rfl) ⟨389144, by rfl⟩ : syracuseStep 518859 = 778289) B778289
theorem B518871 : Blo 515797 518871 := bstep (se 1 (by rfl) ⟨389153, by rfl⟩ : syracuseStep 518871 = 778307) B778307
theorem B518891 : Blo 515797 518891 := bstep (se 1 (by rfl) ⟨389168, by rfl⟩ : syracuseStep 518891 = 778337) B778337
theorem B518903 : Blo 515797 518903 := bstep (se 1 (by rfl) ⟨389177, by rfl⟩ : syracuseStep 518903 = 778355) B778355
theorem B518923 : Blo 515797 518923 := bstep (se 1 (by rfl) ⟨389192, by rfl⟩ : syracuseStep 518923 = 778385) B778385
theorem B518935 : Blo 515797 518935 := bstep (se 1 (by rfl) ⟨389201, by rfl⟩ : syracuseStep 518935 = 778403) B778403
theorem B518955 : Blo 515797 518955 := bstep (se 1 (by rfl) ⟨389216, by rfl⟩ : syracuseStep 518955 = 778433) B778433
theorem B584491 : Blo 515797 584491 := bstep (se 1 (by rfl) ⟨438368, by rfl⟩ : syracuseStep 584491 = 876737) B876737
theorem B518967 : Blo 515797 518967 := bstep (se 1 (by rfl) ⟨389225, by rfl⟩ : syracuseStep 518967 = 778451) B778451
theorem B518987 : Blo 515797 518987 := bstep (se 1 (by rfl) ⟨389240, by rfl⟩ : syracuseStep 518987 = 778481) B778481
theorem B518999 : Blo 515797 518999 := bstep (se 1 (by rfl) ⟨389249, by rfl⟩ : syracuseStep 518999 = 778499) B778499
theorem B519019 : Blo 515797 519019 := bstep (se 1 (by rfl) ⟨389264, by rfl⟩ : syracuseStep 519019 = 778529) B778529
theorem B519031 : Blo 515797 519031 := bstep (se 1 (by rfl) ⟨389273, by rfl⟩ : syracuseStep 519031 = 778547) B778547
theorem B519051 : Blo 515797 519051 := bstep (se 1 (by rfl) ⟨389288, by rfl⟩ : syracuseStep 519051 = 778577) B778577
theorem B519063 : Blo 515797 519063 := bstep (se 1 (by rfl) ⟨389297, by rfl⟩ : syracuseStep 519063 = 778595) B778595
theorem B584599 : Blo 515797 584599 := bstep (se 1 (by rfl) ⟨438449, by rfl⟩ : syracuseStep 584599 = 876899) B876899
theorem B519083 : Blo 515797 519083 := bstep (se 1 (by rfl) ⟨389312, by rfl⟩ : syracuseStep 519083 = 778625) B778625
theorem B519095 : Blo 515797 519095 := bstep (se 1 (by rfl) ⟨389321, by rfl⟩ : syracuseStep 519095 = 778643) B778643
theorem B519115 : Blo 515797 519115 := bstep (se 1 (by rfl) ⟨389336, by rfl⟩ : syracuseStep 519115 = 778673) B778673
theorem B519127 : Blo 515797 519127 := bstep (se 1 (by rfl) ⟨389345, by rfl⟩ : syracuseStep 519127 = 778691) B778691
theorem B519147 : Blo 515797 519147 := bstep (se 1 (by rfl) ⟨389360, by rfl⟩ : syracuseStep 519147 = 778721) B778721
theorem B519159 : Blo 515797 519159 := bstep (se 1 (by rfl) ⟨389369, by rfl⟩ : syracuseStep 519159 = 778739) B778739
theorem B519179 : Blo 515797 519179 := bstep (se 1 (by rfl) ⟨389384, by rfl⟩ : syracuseStep 519179 = 778769) B778769
theorem B519191 : Blo 515797 519191 := bstep (se 1 (by rfl) ⟨389393, by rfl⟩ : syracuseStep 519191 = 778787) B778787
theorem B519211 : Blo 515797 519211 := bstep (se 1 (by rfl) ⟨389408, by rfl⟩ : syracuseStep 519211 = 778817) B778817
theorem B519223 : Blo 515797 519223 := bstep (se 1 (by rfl) ⟨389417, by rfl⟩ : syracuseStep 519223 = 778835) B778835
theorem B519243 : Blo 515797 519243 := bstep (se 1 (by rfl) ⟨389432, by rfl⟩ : syracuseStep 519243 = 778865) B778865
theorem B519255 : Blo 515797 519255 := bstep (se 1 (by rfl) ⟨389441, by rfl⟩ : syracuseStep 519255 = 778883) B778883
theorem B552043 : Blo 515797 552043 := bstep (se 1 (by rfl) ⟨414032, by rfl⟩ : syracuseStep 552043 = 828065) B828065
theorem B519275 : Blo 515797 519275 := bstep (se 1 (by rfl) ⟨389456, by rfl⟩ : syracuseStep 519275 = 778913) B778913
theorem B519287 : Blo 515797 519287 := bstep (se 1 (by rfl) ⟨389465, by rfl⟩ : syracuseStep 519287 = 778931) B778931
theorem B519307 : Blo 515797 519307 := bstep (se 1 (by rfl) ⟨389480, by rfl⟩ : syracuseStep 519307 = 778961) B778961
theorem B1862801 : Blo 515797 1862801 := bstep (se 2 (by rfl) ⟨698550, by rfl⟩ : syracuseStep 1862801 = 1397101) B1397101
theorem B519319 : Blo 515797 519319 := bstep (se 1 (by rfl) ⟨389489, by rfl⟩ : syracuseStep 519319 = 778979) B778979
theorem B1109143 : Blo 515797 1109143 := bstep (se 1 (by rfl) ⟨831857, by rfl⟩ : syracuseStep 1109143 = 1663715) B1663715
theorem B519339 : Blo 515797 519339 := bstep (se 1 (by rfl) ⟨389504, by rfl⟩ : syracuseStep 519339 = 779009) B779009
theorem B519351 : Blo 515797 519351 := bstep (se 1 (by rfl) ⟨389513, by rfl⟩ : syracuseStep 519351 = 779027) B779027
theorem B519371 : Blo 515797 519371 := bstep (se 1 (by rfl) ⟨389528, by rfl⟩ : syracuseStep 519371 = 779057) B779057
theorem B519383 : Blo 515797 519383 := bstep (se 1 (by rfl) ⟨389537, by rfl⟩ : syracuseStep 519383 = 779075) B779075
theorem B519403 : Blo 515797 519403 := bstep (se 1 (by rfl) ⟨389552, by rfl⟩ : syracuseStep 519403 = 779105) B779105
theorem B519415 : Blo 515797 519415 := bstep (se 1 (by rfl) ⟨389561, by rfl⟩ : syracuseStep 519415 = 779123) B779123
theorem B519435 : Blo 515797 519435 := bstep (se 1 (by rfl) ⟨389576, by rfl⟩ : syracuseStep 519435 = 779153) B779153
theorem B4418833 : Blo 515797 4418833 := bstep (se 2 (by rfl) ⟨1657062, by rfl⟩ : syracuseStep 4418833 = 3314125) B3314125
theorem B519447 : Blo 515797 519447 := bstep (se 1 (by rfl) ⟨389585, by rfl⟩ : syracuseStep 519447 = 779171) B779171
theorem B519467 : Blo 515797 519467 := bstep (se 1 (by rfl) ⟨389600, by rfl⟩ : syracuseStep 519467 = 779201) B779201
theorem B519479 : Blo 515797 519479 := bstep (se 1 (by rfl) ⟨389609, by rfl⟩ : syracuseStep 519479 = 779219) B779219
theorem B519499 : Blo 515797 519499 := bstep (se 1 (by rfl) ⟨389624, by rfl⟩ : syracuseStep 519499 = 779249) B779249
theorem B519511 : Blo 515797 519511 := bstep (se 1 (by rfl) ⟨389633, by rfl⟩ : syracuseStep 519511 = 779267) B779267
theorem B519531 : Blo 515797 519531 := bstep (se 1 (by rfl) ⟨389648, by rfl⟩ : syracuseStep 519531 = 779297) B779297
theorem B519543 : Blo 515797 519543 := bstep (se 1 (by rfl) ⟨389657, by rfl⟩ : syracuseStep 519543 = 779315) B779315
theorem B519563 : Blo 515797 519563 := bstep (se 1 (by rfl) ⟨389672, by rfl⟩ : syracuseStep 519563 = 779345) B779345
theorem B519575 : Blo 515797 519575 := bstep (se 1 (by rfl) ⟨389681, by rfl⟩ : syracuseStep 519575 = 779363) B779363
theorem B519595 : Blo 515797 519595 := bstep (se 1 (by rfl) ⟨389696, by rfl⟩ : syracuseStep 519595 = 779393) B779393
theorem B519607 : Blo 515797 519607 := bstep (se 1 (by rfl) ⟨389705, by rfl⟩ : syracuseStep 519607 = 779411) B779411
theorem B519627 : Blo 515797 519627 := bstep (se 1 (by rfl) ⟨389720, by rfl⟩ : syracuseStep 519627 = 779441) B779441
theorem B519639 : Blo 515797 519639 := bstep (se 1 (by rfl) ⟨389729, by rfl⟩ : syracuseStep 519639 = 779459) B779459
theorem B519659 : Blo 515797 519659 := bstep (se 1 (by rfl) ⟨389744, by rfl⟩ : syracuseStep 519659 = 779489) B779489
theorem B519671 : Blo 515797 519671 := bstep (se 1 (by rfl) ⟨389753, by rfl⟩ : syracuseStep 519671 = 779507) B779507
theorem B519691 : Blo 515797 519691 := bstep (se 1 (by rfl) ⟨389768, by rfl⟩ : syracuseStep 519691 = 779537) B779537
theorem B519703 : Blo 515797 519703 := bstep (se 1 (by rfl) ⟨389777, by rfl⟩ : syracuseStep 519703 = 779555) B779555
theorem B4419107 : Blo 515797 4419107 := bstep (se 1 (by rfl) ⟨3314330, by rfl⟩ : syracuseStep 4419107 = 6628661) B6628661
theorem B519723 : Blo 515797 519723 := bstep (se 1 (by rfl) ⟨389792, by rfl⟩ : syracuseStep 519723 = 779585) B779585
theorem B519735 : Blo 515797 519735 := bstep (se 1 (by rfl) ⟨389801, by rfl⟩ : syracuseStep 519735 = 779603) B779603
theorem B519755 : Blo 515797 519755 := bstep (se 1 (by rfl) ⟨389816, by rfl⟩ : syracuseStep 519755 = 779633) B779633
theorem B519767 : Blo 515797 519767 := bstep (se 1 (by rfl) ⟨389825, by rfl⟩ : syracuseStep 519767 = 779651) B779651
theorem B2944613 : Blo 515797 2944613 := bstep (se 4 (by rfl) ⟨276057, by rfl⟩ : syracuseStep 2944613 = 552115) B552115
theorem B519787 : Blo 515797 519787 := bstep (se 1 (by rfl) ⟨389840, by rfl⟩ : syracuseStep 519787 = 779681) B779681
theorem B1961603 : Blo 515797 1961603 := bstep (se 1 (by rfl) ⟨1471202, by rfl⟩ : syracuseStep 1961603 = 2942405) B2942405
theorem B1961617 : Blo 515797 1961617 := bstep (se 2 (by rfl) ⟨735606, by rfl⟩ : syracuseStep 1961617 = 1471213) B1471213
theorem B552619 : Blo 515797 552619 := bstep (se 1 (by rfl) ⟨414464, by rfl⟩ : syracuseStep 552619 = 828929) B828929
theorem B1994419 : Blo 515797 1994419 := bstep (se 1 (by rfl) ⟨1495814, by rfl⟩ : syracuseStep 1994419 = 2991629) B2991629
theorem B1961921 : Blo 515797 1961921 := bstep (se 2 (by rfl) ⟨735720, by rfl⟩ : syracuseStep 1961921 = 1471441) B1471441
theorem B1109963 : Blo 515797 1109963 := bstep (se 1 (by rfl) ⟨832472, by rfl⟩ : syracuseStep 1109963 = 1664945) B1664945
theorem B2945069 : Blo 515797 2945069 := bstep (se 3 (by rfl) ⟨552200, by rfl⟩ : syracuseStep 2945069 = 1104401) B1104401
theorem B3928337 : Blo 515797 3928337 := bstep (se 2 (by rfl) ⟨1473126, by rfl⟩ : syracuseStep 3928337 = 2946253) B2946253
theorem B1306955 : Blo 515797 1306955 := bstep (se 1 (by rfl) ⟨980216, by rfl⟩ : syracuseStep 1306955 = 1960433) B1960433
theorem B553559 : Blo 515797 553559 := bstep (se 1 (by rfl) ⟨415169, by rfl⟩ : syracuseStep 553559 = 830339) B830339
theorem B1962589 : Blo 515797 1962589 := bstep (se 3 (by rfl) ⟨367985, by rfl⟩ : syracuseStep 1962589 = 735971) B735971
theorem B979609 : Blo 515797 979609 := bstep (se 2 (by rfl) ⟨367353, by rfl⟩ : syracuseStep 979609 = 734707) B734707
theorem B2945753 : Blo 515797 2945753 := bstep (se 2 (by rfl) ⟨1104657, by rfl⟩ : syracuseStep 2945753 = 2209315) B2209315
theorem B2618243 : Blo 515797 2618243 := bstep (se 1 (by rfl) ⟨1963682, by rfl⟩ : syracuseStep 2618243 = 3927365) B3927365
theorem B1242049 : Blo 515797 1242049 := bstep (se 2 (by rfl) ⟨465768, by rfl⟩ : syracuseStep 1242049 = 931537) B931537
theorem B980171 : Blo 515797 980171 := bstep (se 1 (by rfl) ⟨735128, by rfl⟩ : syracuseStep 980171 = 1470257) B1470257
theorem B554251 : Blo 515797 554251 := bstep (se 1 (by rfl) ⟨415688, by rfl⟩ : syracuseStep 554251 = 831377) B831377
theorem B1307927 : Blo 515797 1307927 := bstep (se 1 (by rfl) ⟨980945, by rfl⟩ : syracuseStep 1307927 = 1961891) B1961891
theorem B980353 : Blo 515797 980353 := bstep (se 2 (by rfl) ⟨367632, by rfl⟩ : syracuseStep 980353 = 735265) B735265
theorem B2880947 : Blo 515797 2880947 := bstep (se 1 (by rfl) ⟨2160710, by rfl⟩ : syracuseStep 2880947 = 4321421) B4321421
theorem B1046081 : Blo 515797 1046081 := bstep (se 2 (by rfl) ⟨392280, by rfl⟩ : syracuseStep 1046081 = 784561) B784561
theorem B3995237 : Blo 515797 3995237 := bstep (se 4 (by rfl) ⟨374553, by rfl⟩ : syracuseStep 3995237 = 749107) B749107
theorem B652951 : Blo 515797 652951 := bstep (se 1 (by rfl) ⟨489713, by rfl⟩ : syracuseStep 652951 = 979427) B979427
theorem B1767233 : Blo 515797 1767233 := bstep (se 2 (by rfl) ⟨662712, by rfl⟩ : syracuseStep 1767233 = 1325425) B1325425
theorem B1963865 : Blo 515797 1963865 := bstep (se 2 (by rfl) ⟨736449, by rfl⟩ : syracuseStep 1963865 = 1472899) B1472899
theorem B1996633 : Blo 515797 1996633 := bstep (se 2 (by rfl) ⟨748737, by rfl⟩ : syracuseStep 1996633 = 1497475) B1497475
theorem B1308595 : Blo 515797 1308595 := bstep (se 1 (by rfl) ⟨981446, by rfl⟩ : syracuseStep 1308595 = 1962893) B1962893
theorem B1243097 : Blo 515797 1243097 := bstep (se 2 (by rfl) ⟨466161, by rfl⟩ : syracuseStep 1243097 = 932323) B932323
theorem B1308737 : Blo 515797 1308737 := bstep (se 2 (by rfl) ⟨490776, by rfl⟩ : syracuseStep 1308737 = 981553) B981553
theorem B981067 : Blo 515797 981067 := bstep (se 1 (by rfl) ⟨735800, by rfl⟩ : syracuseStep 981067 = 1471601) B1471601
theorem B981143 : Blo 515797 981143 := bstep (se 1 (by rfl) ⟨735857, by rfl⟩ : syracuseStep 981143 = 1471715) B1471715
theorem B1472843 : Blo 515797 1472843 := bstep (se 1 (by rfl) ⟨1104632, by rfl⟩ : syracuseStep 1472843 = 2209265) B2209265
theorem B653771 : Blo 515797 653771 := bstep (se 1 (by rfl) ⟨490328, by rfl⟩ : syracuseStep 653771 = 980657) B980657
theorem B7436893 : Blo 515797 7436893 := bstep (se 3 (by rfl) ⟨1394417, by rfl⟩ : syracuseStep 7436893 = 2788835) B2788835
theorem B1178227 : Blo 515797 1178227 := bstep (se 1 (by rfl) ⟨883670, by rfl⟩ : syracuseStep 1178227 = 1767341) B1767341
theorem B1473241 : Blo 515797 1473241 := bstep (se 2 (by rfl) ⟨552465, by rfl⟩ : syracuseStep 1473241 = 1104931) B1104931
theorem B981811 : Blo 515797 981811 := bstep (se 1 (by rfl) ⟨736358, by rfl⟩ : syracuseStep 981811 = 1472717) B1472717
theorem B3308363 : Blo 515797 3308363 := bstep (se 1 (by rfl) ⟨2481272, by rfl⟩ : syracuseStep 3308363 = 4962545) B4962545
theorem B982039 : Blo 515797 982039 := bstep (se 1 (by rfl) ⟨736529, by rfl⟩ : syracuseStep 982039 = 1473059) B1473059
theorem B982145 : Blo 515797 982145 := bstep (se 2 (by rfl) ⟨368304, by rfl⟩ : syracuseStep 982145 = 736609) B736609
theorem B654475 : Blo 515797 654475 := bstep (se 1 (by rfl) ⟨490856, by rfl⟩ : syracuseStep 654475 = 981713) B981713
theorem B982297 : Blo 515797 982297 := bstep (se 2 (by rfl) ⟨368361, by rfl⟩ : syracuseStep 982297 = 736723) B736723
theorem B1310003 : Blo 515797 1310003 := bstep (se 1 (by rfl) ⟨982502, by rfl⟩ : syracuseStep 1310003 = 1965005) B1965005
theorem B654743 : Blo 515797 654743 := bstep (se 1 (by rfl) ⟨491057, by rfl⟩ : syracuseStep 654743 = 982115) B982115
theorem B1965491 : Blo 515797 1965491 := bstep (se 1 (by rfl) ⟨1474118, by rfl⟩ : syracuseStep 1965491 = 2948237) B2948237
theorem B1965505 : Blo 515797 1965505 := bstep (se 2 (by rfl) ⟨737064, by rfl⟩ : syracuseStep 1965505 = 1474129) B1474129
theorem B3997457 : Blo 515797 3997457 := bstep (se 2 (by rfl) ⟨1499046, by rfl⟩ : syracuseStep 3997457 = 2998093) B2998093
theorem B1310539 : Blo 515797 1310539 := bstep (se 1 (by rfl) ⟨982904, by rfl⟩ : syracuseStep 1310539 = 1965809) B1965809
theorem B1474483 : Blo 515797 1474483 := bstep (se 1 (by rfl) ⟨1105862, by rfl⟩ : syracuseStep 1474483 = 2211725) B2211725
theorem B1310681 : Blo 515797 1310681 := bstep (se 2 (by rfl) ⟨491505, by rfl⟩ : syracuseStep 1310681 = 983011) B983011
theorem B2621483 : Blo 515797 2621483 := bstep (se 1 (by rfl) ⟨1966112, by rfl⟩ : syracuseStep 2621483 = 3932225) B3932225
theorem B1245451 : Blo 515797 1245451 := bstep (se 1 (by rfl) ⟨934088, by rfl⟩ : syracuseStep 1245451 = 1868177) B1868177
theorem B32407955 : Blo 515797 32407955 := bstep (se 1 (by rfl) ⟨24305966, by rfl⟩ : syracuseStep 32407955 = 48611933) B48611933
theorem B983497 : Blo 515797 983497 := bstep (se 2 (by rfl) ⟨368811, by rfl⟩ : syracuseStep 983497 = 737623) B737623
theorem B1573391 : Blo 515797 1573391 := bstep (se 1 (by rfl) ⟨1180043, by rfl⟩ : syracuseStep 1573391 = 2360087) B2360087
theorem B1180345 : Blo 515797 1180345 := bstep (se 2 (by rfl) ⟨442629, by rfl⟩ : syracuseStep 1180345 = 885259) B885259
theorem B1966963 : Blo 515797 1966963 := bstep (se 1 (by rfl) ⟨1475222, by rfl⟩ : syracuseStep 1966963 = 2950445) B2950445
theorem B1246067 : Blo 515797 1246067 := bstep (se 1 (by rfl) ⟨934550, by rfl⟩ : syracuseStep 1246067 = 1869101) B1869101
theorem B1311623 : Blo 515797 1311623 := bstep (se 1 (by rfl) ⟨983717, by rfl⟩ : syracuseStep 1311623 = 1967435) B1967435
theorem B1311673 : Blo 515797 1311673 := bstep (se 2 (by rfl) ⟨491877, by rfl⟩ : syracuseStep 1311673 = 983755) B983755
theorem B37815349 : Blo 515797 37815349 := bstep (se 5 (by rfl) ⟨1772594, by rfl⟩ : syracuseStep 37815349 = 3545189) B3545189
theorem B24249419 : Blo 515797 24249419 := bstep (se 1 (by rfl) ⟨18187064, by rfl⟩ : syracuseStep 24249419 = 36374129) B36374129
theorem B2622779 : Blo 515797 2622779 := bstep (se 1 (by rfl) ⟨1967084, by rfl⟩ : syracuseStep 2622779 = 3934169) B3934169
theorem B1475975 : Blo 515797 1475975 := bstep (se 1 (by rfl) ⟨1106981, by rfl⟩ : syracuseStep 1475975 = 2213963) B2213963
theorem B2622941 : Blo 515797 2622941 := bstep (se 3 (by rfl) ⟨491801, by rfl⟩ : syracuseStep 2622941 = 983603) B983603
theorem B1312271 : Blo 515797 1312271 := bstep (se 1 (by rfl) ⟨984203, by rfl⟩ : syracuseStep 1312271 = 1968407) B1968407
theorem B1476157 : Blo 515797 1476157 := bstep (se 3 (by rfl) ⟨276779, by rfl⟩ : syracuseStep 1476157 = 553559) B553559
theorem B1476215 : Blo 515797 1476215 := bstep (se 1 (by rfl) ⟨1107161, by rfl⟩ : syracuseStep 1476215 = 2214323) B2214323
theorem B1246873 : Blo 515797 1246873 := bstep (se 2 (by rfl) ⟨467577, by rfl⟩ : syracuseStep 1246873 = 935155) B935155
theorem B657067 : Blo 515797 657067 := bstep (se 1 (by rfl) ⟨492800, by rfl⟩ : syracuseStep 657067 = 985601) B985601
theorem B886457 : Blo 515797 886457 := bstep (se 2 (by rfl) ⟨332421, by rfl⟩ : syracuseStep 886457 = 664843) B664843
theorem B7079653 : Blo 515797 7079653 := bstep (se 4 (by rfl) ⟨663717, by rfl⟩ : syracuseStep 7079653 = 1327435) B1327435
theorem B4196069 : Blo 515797 4196069 := bstep (se 4 (by rfl) ⟨393381, by rfl⟩ : syracuseStep 4196069 = 786763) B786763
theorem B2623265 : Blo 515797 2623265 := bstep (se 2 (by rfl) ⟨983724, by rfl⟩ : syracuseStep 2623265 = 1967449) B1967449
theorem B3311513 : Blo 515797 3311513 := bstep (se 2 (by rfl) ⟨1241817, by rfl⟩ : syracuseStep 3311513 = 2483635) B2483635
theorem B3311563 : Blo 515797 3311563 := bstep (se 1 (by rfl) ⟨2483672, by rfl⟩ : syracuseStep 3311563 = 4967345) B4967345
theorem B4982957 : Blo 515797 4982957 := bstep (se 3 (by rfl) ⟨934304, by rfl⟩ : syracuseStep 4982957 = 1868609) B1868609
theorem B1312969 : Blo 515797 1312969 := bstep (se 2 (by rfl) ⟨492363, by rfl⟩ : syracuseStep 1312969 = 984727) B984727
theorem B4327625 : Blo 515797 4327625 := bstep (se 2 (by rfl) ⟨1622859, by rfl⟩ : syracuseStep 4327625 = 3245719) B3245719
theorem B5900525 : Blo 515797 5900525 := bstep (se 3 (by rfl) ⟨1106348, by rfl⟩ : syracuseStep 5900525 = 2212697) B2212697
theorem B1313111 : Blo 515797 1313111 := bstep (se 1 (by rfl) ⟨984833, by rfl⟩ : syracuseStep 1313111 = 1969667) B1969667
theorem B3770833 : Blo 515797 3770833 := bstep (se 2 (by rfl) ⟨1414062, by rfl⟩ : syracuseStep 3770833 = 2828125) B2828125
theorem B788983 : Blo 515797 788983 := bstep (se 1 (by rfl) ⟨591737, by rfl⟩ : syracuseStep 788983 = 1183475) B1183475
theorem B2984471 : Blo 515797 2984471 := bstep (se 1 (by rfl) ⟨2238353, by rfl⟩ : syracuseStep 2984471 = 4476707) B4476707
theorem B1477273 : Blo 515797 1477273 := bstep (se 2 (by rfl) ⟨553977, by rfl⟩ : syracuseStep 1477273 = 1107955) B1107955
theorem B2624237 : Blo 515797 2624237 := bstep (se 3 (by rfl) ⟨492044, by rfl⟩ : syracuseStep 2624237 = 984089) B984089
theorem B986003 : Blo 515797 986003 := bstep (se 1 (by rfl) ⟨739502, by rfl⟩ : syracuseStep 986003 = 1479005) B1479005
theorem B560143 : Blo 515797 560143 := bstep (se 1 (by rfl) ⟨420107, by rfl⟩ : syracuseStep 560143 = 840215) B840215
theorem B1969181 : Blo 515797 1969181 := bstep (se 3 (by rfl) ⟨369221, by rfl⟩ : syracuseStep 1969181 = 738443) B738443
theorem B986231 : Blo 515797 986231 := bstep (se 1 (by rfl) ⟨739673, by rfl⟩ : syracuseStep 986231 = 1479347) B1479347
theorem B1477889 : Blo 515797 1477889 := bstep (se 2 (by rfl) ⟨554208, by rfl⟩ : syracuseStep 1477889 = 1108417) B1108417
theorem B789767 : Blo 515797 789767 := bstep (se 1 (by rfl) ⟨592325, by rfl⟩ : syracuseStep 789767 = 1184651) B1184651
theorem B1248527 : Blo 515797 1248527 := bstep (se 1 (by rfl) ⟨936395, by rfl⟩ : syracuseStep 1248527 = 1872791) B1872791
theorem B2788667 : Blo 515797 2788667 := bstep (se 1 (by rfl) ⟨2091500, by rfl⟩ : syracuseStep 2788667 = 4183001) B4183001
theorem B2493899 : Blo 515797 2493899 := bstep (se 1 (by rfl) ⟨1870424, by rfl⟩ : syracuseStep 2493899 = 3740849) B3740849
theorem B2625047 : Blo 515797 2625047 := bstep (se 1 (by rfl) ⟨1968785, by rfl⟩ : syracuseStep 2625047 = 3937571) B3937571
theorem B1969865 : Blo 515797 1969865 := bstep (se 2 (by rfl) ⟨738699, by rfl⟩ : syracuseStep 1969865 = 1477399) B1477399
theorem B1183547 : Blo 515797 1183547 := bstep (se 1 (by rfl) ⟨887660, by rfl⟩ : syracuseStep 1183547 = 1775321) B1775321
theorem B5967731 : Blo 515797 5967731 := bstep (se 1 (by rfl) ⟨4475798, by rfl⟩ : syracuseStep 5967731 = 8951597) B8951597
theorem B2101277 : Blo 515797 2101277 := bstep (se 3 (by rfl) ⟨393989, by rfl⟩ : syracuseStep 2101277 = 787979) B787979
theorem B2789549 : Blo 515797 2789549 := bstep (se 3 (by rfl) ⟨523040, by rfl⟩ : syracuseStep 2789549 = 1046081) B1046081
theorem B1478857 : Blo 515797 1478857 := bstep (se 2 (by rfl) ⟨554571, by rfl⟩ : syracuseStep 1478857 = 1109143) B1109143
theorem B1315187 : Blo 515797 1315187 := bstep (se 1 (by rfl) ⟨986390, by rfl⟩ : syracuseStep 1315187 = 1972781) B1972781
theorem B11932505 : Blo 515797 11932505 := bstep (se 2 (by rfl) ⟨4474689, by rfl⟩ : syracuseStep 11932505 = 8949379) B8949379
theorem B1315703 : Blo 515797 1315703 := bstep (se 1 (by rfl) ⟨986777, by rfl⟩ : syracuseStep 1315703 = 1973555) B1973555
theorem B1741715 : Blo 515797 1741715 := bstep (se 1 (by rfl) ⟨1306286, by rfl⟩ : syracuseStep 1741715 = 2612573) B2612573
theorem B2659225 : Blo 515797 2659225 := bstep (se 2 (by rfl) ⟨997209, by rfl⟩ : syracuseStep 2659225 = 1994419) B1994419
theorem B1184887 : Blo 515797 1184887 := bstep (se 1 (by rfl) ⟨888665, by rfl⟩ : syracuseStep 1184887 = 1777331) B1777331
theorem B2102543 : Blo 515797 2102543 := bstep (se 1 (by rfl) ⟨1576907, by rfl⟩ : syracuseStep 2102543 = 3153815) B3153815
theorem B4724153 : Blo 515797 4724153 := bstep (se 2 (by rfl) ⟨1771557, by rfl⟩ : syracuseStep 4724153 = 3543115) B3543115
theorem B1971641 : Blo 515797 1971641 := bstep (se 2 (by rfl) ⟨739365, by rfl⟩ : syracuseStep 1971641 = 1478731) B1478731
theorem B3741137 : Blo 515797 3741137 := bstep (se 2 (by rfl) ⟨1402926, by rfl⟩ : syracuseStep 3741137 = 2805853) B2805853
theorem B2954819 : Blo 515797 2954819 := bstep (se 1 (by rfl) ⟨2216114, by rfl⟩ : syracuseStep 2954819 = 4432229) B4432229
theorem B2987929 : Blo 515797 2987929 := bstep (se 2 (by rfl) ⟨1120473, by rfl⟩ : syracuseStep 2987929 = 2240947) B2240947
theorem B2988035 : Blo 515797 2988035 := bstep (se 1 (by rfl) ⟨2241026, by rfl⟩ : syracuseStep 2988035 = 4482053) B4482053
theorem B2955275 : Blo 515797 2955275 := bstep (se 1 (by rfl) ⟨2216456, by rfl⟩ : syracuseStep 2955275 = 4432913) B4432913
theorem B1743119 : Blo 515797 1743119 := bstep (se 1 (by rfl) ⟨1307339, by rfl⟩ : syracuseStep 1743119 = 2614679) B2614679
theorem B5970323 : Blo 515797 5970323 := bstep (se 1 (by rfl) ⟨4477742, by rfl⟩ : syracuseStep 5970323 = 8955485) B8955485
theorem B5904899 : Blo 515797 5904899 := bstep (se 1 (by rfl) ⟨4428674, by rfl⟩ : syracuseStep 5904899 = 8857349) B8857349
theorem B1743389 : Blo 515797 1743389 := bstep (se 3 (by rfl) ⟨326885, by rfl⟩ : syracuseStep 1743389 = 653771) B653771
theorem B2628125 : Blo 515797 2628125 := bstep (se 3 (by rfl) ⟨492773, by rfl⟩ : syracuseStep 2628125 = 985547) B985547
theorem B40410019 : Blo 515797 40410019 := bstep (se 1 (by rfl) ⟨30307514, by rfl⟩ : syracuseStep 40410019 = 60615029) B60615029
theorem B2628611 : Blo 515797 2628611 := bstep (se 1 (by rfl) ⟨1971458, by rfl⟩ : syracuseStep 2628611 = 3942917) B3942917
theorem B2661443 : Blo 515797 2661443 := bstep (se 1 (by rfl) ⟨1996082, by rfl⟩ : syracuseStep 2661443 = 3992165) B3992165
theorem B1744793 : Blo 515797 1744793 := bstep (se 2 (by rfl) ⟨654297, by rfl⟩ : syracuseStep 1744793 = 1308595) B1308595
theorem B1122761 : Blo 515797 1122761 := bstep (se 2 (by rfl) ⟨421035, by rfl⟩ : syracuseStep 1122761 = 842071) B842071
theorem B2368061 : Blo 515797 2368061 := bstep (se 3 (by rfl) ⟨444011, by rfl⟩ : syracuseStep 2368061 = 888023) B888023
theorem B1778237 : Blo 515797 1778237 := bstep (se 3 (by rfl) ⟨333419, by rfl⟩ : syracuseStep 1778237 = 666839) B666839
theorem B1745495 : Blo 515797 1745495 := bstep (se 1 (by rfl) ⟨1309121, by rfl⟩ : syracuseStep 1745495 = 2618243) B2618243
theorem B2630231 : Blo 515797 2630231 := bstep (se 1 (by rfl) ⟨1972673, by rfl⟩ : syracuseStep 2630231 = 3945347) B3945347
theorem B5579441 : Blo 515797 5579441 := bstep (se 2 (by rfl) ⟨2092290, by rfl⟩ : syracuseStep 5579441 = 4184581) B4184581
theorem B1745981 : Blo 515797 1745981 := bstep (se 3 (by rfl) ⟨327371, by rfl⟩ : syracuseStep 1745981 = 654743) B654743
theorem B2630717 : Blo 515797 2630717 := bstep (se 3 (by rfl) ⟨493259, by rfl⟩ : syracuseStep 2630717 = 986519) B986519
theorem B2663491 : Blo 515797 2663491 := bstep (se 1 (by rfl) ⟨1997618, by rfl⟩ : syracuseStep 2663491 = 3995237) B3995237
theorem B828731 : Blo 515797 828731 := bstep (se 1 (by rfl) ⟨621548, by rfl⟩ : syracuseStep 828731 = 1243097) B1243097
theorem B4990643 : Blo 515797 4990643 := bstep (se 1 (by rfl) ⟨3742982, by rfl⟩ : syracuseStep 4990643 = 7485965) B7485965
theorem B2107081 : Blo 515797 2107081 := bstep (se 2 (by rfl) ⟨790155, by rfl⟩ : syracuseStep 2107081 = 1580311) B1580311
theorem B2959193 : Blo 515797 2959193 := bstep (se 2 (by rfl) ⟨1109697, by rfl⟩ : syracuseStep 2959193 = 2219395) B2219395
theorem B2205575 : Blo 515797 2205575 := bstep (se 1 (by rfl) ⟨1654181, by rfl⟩ : syracuseStep 2205575 = 3308363) B3308363
theorem B4990871 : Blo 515797 4990871 := bstep (se 1 (by rfl) ⟨3743153, by rfl⟩ : syracuseStep 4990871 = 7486307) B7486307
theorem B10758041 : Blo 515797 10758041 := bstep (se 2 (by rfl) ⟨4034265, by rfl⟩ : syracuseStep 10758041 = 8068531) B8068531
theorem B20195351 : Blo 515797 20195351 := bstep (se 1 (by rfl) ⟨15146513, by rfl⟩ : syracuseStep 20195351 = 30293027) B30293027
theorem B993323 : Blo 515797 993323 := bstep (se 1 (by rfl) ⟨744992, by rfl⟩ : syracuseStep 993323 = 1489985) B1489985
theorem B2959649 : Blo 515797 2959649 := bstep (se 2 (by rfl) ⟨1109868, by rfl⟩ : syracuseStep 2959649 = 2219737) B2219737
theorem B1747385 : Blo 515797 1747385 := bstep (se 2 (by rfl) ⟨655269, by rfl⟩ : syracuseStep 1747385 = 1310539) B1310539
theorem B2664971 : Blo 515797 2664971 := bstep (se 1 (by rfl) ⟨1998728, by rfl⟩ : syracuseStep 2664971 = 3997457) B3997457
theorem B2959901 : Blo 515797 2959901 := bstep (se 3 (by rfl) ⟨554981, by rfl⟩ : syracuseStep 2959901 = 1109963) B1109963
theorem B4434689 : Blo 515797 4434689 := bstep (se 2 (by rfl) ⟨1663008, by rfl⟩ : syracuseStep 4434689 = 3326017) B3326017
theorem B1747979 : Blo 515797 1747979 := bstep (se 1 (by rfl) ⟨1310984, by rfl⟩ : syracuseStep 1747979 = 2621969) B2621969
theorem B1748087 : Blo 515797 1748087 := bstep (se 1 (by rfl) ⟨1311065, by rfl⟩ : syracuseStep 1748087 = 2622131) B2622131
theorem B248491405 : Blo 515797 248491405 := bstep (se 3 (by rfl) ⟨46592138, by rfl⟩ : syracuseStep 248491405 = 93184277) B93184277
theorem B5877197 : Blo 515797 5877197 := bstep (se 3 (by rfl) ⟨1101974, by rfl⟩ : syracuseStep 5877197 = 2203949) B2203949
theorem B3943889 : Blo 515797 3943889 := bstep (se 2 (by rfl) ⟨1478958, by rfl⟩ : syracuseStep 3943889 = 2957917) B2957917
theorem B3157507 : Blo 515797 3157507 := bstep (se 1 (by rfl) ⟨2368130, by rfl⟩ : syracuseStep 3157507 = 4736261) B4736261
theorem B2207351 : Blo 515797 2207351 := bstep (se 1 (by rfl) ⟨1655513, by rfl⟩ : syracuseStep 2207351 = 3311027) B3311027
theorem B1748681 : Blo 515797 1748681 := bstep (se 2 (by rfl) ⟨655755, by rfl⟩ : syracuseStep 1748681 = 1311511) B1311511
theorem B2207503 : Blo 515797 2207503 := bstep (se 1 (by rfl) ⟨1655627, by rfl⟩ : syracuseStep 2207503 = 3311255) B3311255
theorem B3321917 : Blo 515797 3321917 := bstep (se 3 (by rfl) ⟨622859, by rfl⟩ : syracuseStep 3321917 = 1245719) B1245719
theorem B1749383 : Blo 515797 1749383 := bstep (se 1 (by rfl) ⟨1312037, by rfl⟩ : syracuseStep 1749383 = 2624075) B2624075
theorem B1323535 : Blo 515797 1323535 := bstep (se 1 (by rfl) ⟨992651, by rfl⟩ : syracuseStep 1323535 = 1985303) B1985303
theorem B2208323 : Blo 515797 2208323 := bstep (se 1 (by rfl) ⟨1656242, by rfl⟩ : syracuseStep 2208323 = 3312485) B3312485
theorem B1749761 : Blo 515797 1749761 := bstep (se 2 (by rfl) ⟨656160, by rfl⟩ : syracuseStep 1749761 = 1312321) B1312321
theorem B2241433 : Blo 515797 2241433 := bstep (se 2 (by rfl) ⟨840537, by rfl⟩ : syracuseStep 2241433 = 1681075) B1681075
theorem B800015 : Blo 515797 800015 := bstep (se 1 (by rfl) ⟨600011, by rfl⟩ : syracuseStep 800015 = 1200023) B1200023
theorem B1160567 : Blo 515797 1160567 := bstep (se 1 (by rfl) ⟨870425, by rfl⟩ : syracuseStep 1160567 = 1740851) B1740851
theorem B734599 : Blo 515797 734599 := bstep (se 1 (by rfl) ⟨550949, by rfl⟩ : syracuseStep 734599 = 1101899) B1101899
theorem B1160747 : Blo 515797 1160747 := bstep (se 1 (by rfl) ⟨870560, by rfl⟩ : syracuseStep 1160747 = 1741121) B1741121
theorem B1750571 : Blo 515797 1750571 := bstep (se 1 (by rfl) ⟨1312928, by rfl⟩ : syracuseStep 1750571 = 2625857) B2625857
theorem B1324603 : Blo 515797 1324603 := bstep (se 1 (by rfl) ⟨993452, by rfl⟩ : syracuseStep 1324603 = 1986905) B1986905
theorem B1062715 : Blo 515797 1062715 := bstep (se 1 (by rfl) ⟨797036, by rfl⟩ : syracuseStep 1062715 = 1594073) B1594073
theorem B1161107 : Blo 515797 1161107 := bstep (se 1 (by rfl) ⟨870830, by rfl⟩ : syracuseStep 1161107 = 1741661) B1741661
theorem B1161161 : Blo 515797 1161161 := bstep (se 2 (by rfl) ⟨435435, by rfl⟩ : syracuseStep 1161161 = 870871) B870871
theorem B9124013 : Blo 515797 9124013 := bstep (se 3 (by rfl) ⟨1710752, by rfl⟩ : syracuseStep 9124013 = 3421505) B3421505
theorem B735419 : Blo 515797 735419 := bstep (se 1 (by rfl) ⟨551564, by rfl⟩ : syracuseStep 735419 = 1103129) B1103129
theorem B188627285 : Blo 515797 188627285 := bstep (se 10 (by rfl) ⟨276309, by rfl⟩ : syracuseStep 188627285 = 552619) B552619
theorem B1063315 : Blo 515797 1063315 := bstep (se 1 (by rfl) ⟨797486, by rfl⟩ : syracuseStep 1063315 = 1594973) B1594973
theorem B1161863 : Blo 515797 1161863 := bstep (se 1 (by rfl) ⟨871397, by rfl⟩ : syracuseStep 1161863 = 1742795) B1742795
theorem B4733711 : Blo 515797 4733711 := bstep (se 1 (by rfl) ⟨3550283, by rfl⟩ : syracuseStep 4733711 = 7100567) B7100567
theorem B736057 : Blo 515797 736057 := bstep (se 2 (by rfl) ⟨276021, by rfl⟩ : syracuseStep 736057 = 552043) B552043
theorem B1162043 : Blo 515797 1162043 := bstep (se 1 (by rfl) ⟨871532, by rfl⟩ : syracuseStep 1162043 = 1743065) B1743065
theorem B1751867 : Blo 515797 1751867 := bstep (se 1 (by rfl) ⟨1313900, by rfl⟩ : syracuseStep 1751867 = 2627801) B2627801
theorem B1162169 : Blo 515797 1162169 := bstep (se 2 (by rfl) ⟨435813, by rfl⟩ : syracuseStep 1162169 = 871627) B871627
theorem B4439063 : Blo 515797 4439063 := bstep (se 1 (by rfl) ⟨3329297, by rfl⟩ : syracuseStep 4439063 = 6658595) B6658595
theorem B3980461 : Blo 515797 3980461 := bstep (se 3 (by rfl) ⟨746336, by rfl⟩ : syracuseStep 3980461 = 1492673) B1492673
theorem B1162511 : Blo 515797 1162511 := bstep (se 1 (by rfl) ⟨871883, by rfl⟩ : syracuseStep 1162511 = 1743767) B1743767
theorem B1162529 : Blo 515797 1162529 := bstep (se 2 (by rfl) ⟨435948, by rfl⟩ : syracuseStep 1162529 = 871897) B871897
theorem B1752353 : Blo 515797 1752353 := bstep (se 2 (by rfl) ⟨657132, by rfl⟩ : syracuseStep 1752353 = 1314265) B1314265
theorem B6634811 : Blo 515797 6634811 := bstep (se 1 (by rfl) ⟨4976108, by rfl⟩ : syracuseStep 6634811 = 9952217) B9952217
theorem B1654283 : Blo 515797 1654283 := bstep (se 1 (by rfl) ⟨1240712, by rfl⟩ : syracuseStep 1654283 = 2481425) B2481425
theorem B933419 : Blo 515797 933419 := bstep (se 1 (by rfl) ⟨700064, by rfl⟩ : syracuseStep 933419 = 1400129) B1400129
theorem B1162871 : Blo 515797 1162871 := bstep (se 1 (by rfl) ⟨872153, by rfl⟩ : syracuseStep 1162871 = 1744307) B1744307
theorem B1163051 : Blo 515797 1163051 := bstep (se 1 (by rfl) ⟨872288, by rfl⟩ : syracuseStep 1163051 = 1744577) B1744577
theorem B1294123 : Blo 515797 1294123 := bstep (se 1 (by rfl) ⟨970592, by rfl⟩ : syracuseStep 1294123 = 1941185) B1941185
theorem B1752947 : Blo 515797 1752947 := bstep (se 1 (by rfl) ⟨1314710, by rfl⟩ : syracuseStep 1752947 = 2629421) B2629421
theorem B1163411 : Blo 515797 1163411 := bstep (se 1 (by rfl) ⟨872558, by rfl⟩ : syracuseStep 1163411 = 1745117) B1745117
theorem B1163465 : Blo 515797 1163465 := bstep (se 2 (by rfl) ⟨436299, by rfl⟩ : syracuseStep 1163465 = 872599) B872599
theorem B737543 : Blo 515797 737543 := bstep (se 1 (by rfl) ⟨553157, by rfl⟩ : syracuseStep 737543 = 1106315) B1106315
theorem B1491335 : Blo 515797 1491335 := bstep (se 1 (by rfl) ⟨1118501, by rfl⟩ : syracuseStep 1491335 = 2237003) B2237003
theorem B737851 : Blo 515797 737851 := bstep (se 1 (by rfl) ⟨553388, by rfl⟩ : syracuseStep 737851 = 1106777) B1106777
theorem B8372929 : Blo 515797 8372929 := bstep (se 2 (by rfl) ⟨3139848, by rfl⟩ : syracuseStep 8372929 = 6279697) B6279697
theorem B1164167 : Blo 515797 1164167 := bstep (se 1 (by rfl) ⟨873125, by rfl⟩ : syracuseStep 1164167 = 1746251) B1746251
theorem B6636451 : Blo 515797 6636451 := bstep (se 1 (by rfl) ⟨4977338, by rfl⟩ : syracuseStep 6636451 = 9954677) B9954677
theorem B1164347 : Blo 515797 1164347 := bstep (se 1 (by rfl) ⟨873260, by rfl⟩ : syracuseStep 1164347 = 1746521) B1746521
theorem B1590359 : Blo 515797 1590359 := bstep (se 1 (by rfl) ⟨1192769, by rfl⟩ : syracuseStep 1590359 = 2385539) B2385539
theorem B1164473 : Blo 515797 1164473 := bstep (se 2 (by rfl) ⟨436677, by rfl⟩ : syracuseStep 1164473 = 873355) B873355
theorem B1885421 : Blo 515797 1885421 := bstep (se 3 (by rfl) ⟨353516, by rfl⟩ : syracuseStep 1885421 = 707033) B707033
theorem B1656065 : Blo 515797 1656065 := bstep (se 2 (by rfl) ⟨621024, by rfl⟩ : syracuseStep 1656065 = 1242049) B1242049
theorem B1164815 : Blo 515797 1164815 := bstep (se 1 (by rfl) ⟨873611, by rfl⟩ : syracuseStep 1164815 = 1747223) B1747223
theorem B1164833 : Blo 515797 1164833 := bstep (se 2 (by rfl) ⟨436812, by rfl⟩ : syracuseStep 1164833 = 873625) B873625
theorem B739001 : Blo 515797 739001 := bstep (se 2 (by rfl) ⟨277125, by rfl⟩ : syracuseStep 739001 = 554251) B554251
theorem B935609 : Blo 515797 935609 := bstep (se 2 (by rfl) ⟨350853, by rfl⟩ : syracuseStep 935609 = 701707) B701707
theorem B6407909 : Blo 515797 6407909 := bstep (se 4 (by rfl) ⟨600741, by rfl⟩ : syracuseStep 6407909 = 1201483) B1201483
theorem B1165175 : Blo 515797 1165175 := bstep (se 1 (by rfl) ⟨873881, by rfl⟩ : syracuseStep 1165175 = 1747763) B1747763
theorem B1165355 : Blo 515797 1165355 := bstep (se 1 (by rfl) ⟨874016, by rfl⟩ : syracuseStep 1165355 = 1748033) B1748033
theorem B870601 : Blo 515797 870601 := bstep (se 2 (by rfl) ⟨326475, by rfl⟩ : syracuseStep 870601 = 652951) B652951
theorem B1165715 : Blo 515797 1165715 := bstep (se 1 (by rfl) ⟨874286, by rfl⟩ : syracuseStep 1165715 = 1748573) B1748573
theorem B1165769 : Blo 515797 1165769 := bstep (se 2 (by rfl) ⟨437163, by rfl⟩ : syracuseStep 1165769 = 874327) B874327
theorem B3590659 : Blo 515797 3590659 := bstep (se 1 (by rfl) ⟨2692994, by rfl⟩ : syracuseStep 3590659 = 5385989) B5385989
theorem B4410085 : Blo 515797 4410085 := bstep (se 4 (by rfl) ⟨413445, by rfl⟩ : syracuseStep 4410085 = 826891) B826891
theorem B871303 : Blo 515797 871303 := bstep (se 1 (by rfl) ⟨653477, by rfl⟩ : syracuseStep 871303 = 1306955) B1306955
theorem B1166471 : Blo 515797 1166471 := bstep (se 1 (by rfl) ⟨874853, by rfl⟩ : syracuseStep 1166471 = 1749707) B1749707
theorem B1166651 : Blo 515797 1166651 := bstep (se 1 (by rfl) ⟨874988, by rfl⟩ : syracuseStep 1166651 = 1749977) B1749977
theorem B1166777 : Blo 515797 1166777 := bstep (se 2 (by rfl) ⟨437541, by rfl⟩ : syracuseStep 1166777 = 875083) B875083
theorem B9915857 : Blo 515797 9915857 := bstep (se 2 (by rfl) ⟨3718446, by rfl⟩ : syracuseStep 9915857 = 7436893) B7436893
theorem B3198475 : Blo 515797 3198475 := bstep (se 1 (by rfl) ⟨2398856, by rfl⟩ : syracuseStep 3198475 = 4797713) B4797713
theorem B871951 : Blo 515797 871951 := bstep (se 1 (by rfl) ⟨653963, by rfl⟩ : syracuseStep 871951 = 1307927) B1307927
theorem B773705 : Blo 515797 773705 := bstep (se 2 (by rfl) ⟨290139, by rfl⟩ : syracuseStep 773705 = 580279) B580279
theorem B1920631 : Blo 515797 1920631 := bstep (se 1 (by rfl) ⟨1440473, by rfl⟩ : syracuseStep 1920631 = 2880947) B2880947
theorem B773819 : Blo 515797 773819 := bstep (se 1 (by rfl) ⟨580364, by rfl⟩ : syracuseStep 773819 = 1160729) B1160729
theorem B3919589 : Blo 515797 3919589 := bstep (se 4 (by rfl) ⟨367461, by rfl⟩ : syracuseStep 3919589 = 734923) B734923
theorem B773879 : Blo 515797 773879 := bstep (se 1 (by rfl) ⟨580409, by rfl⟩ : syracuseStep 773879 = 1160819) B1160819
theorem B773903 : Blo 515797 773903 := bstep (se 1 (by rfl) ⟨580427, by rfl⟩ : syracuseStep 773903 = 1160855) B1160855
theorem B1167119 : Blo 515797 1167119 := bstep (se 1 (by rfl) ⟨875339, by rfl⟩ : syracuseStep 1167119 = 1750679) B1750679
theorem B1167137 : Blo 515797 1167137 := bstep (se 2 (by rfl) ⟨437676, by rfl⟩ : syracuseStep 1167137 = 875353) B875353
theorem B773945 : Blo 515797 773945 := bstep (se 2 (by rfl) ⟨290229, by rfl⟩ : syracuseStep 773945 = 580459) B580459
theorem B774023 : Blo 515797 774023 := bstep (se 1 (by rfl) ⟨580517, by rfl⟩ : syracuseStep 774023 = 1161035) B1161035
theorem B774059 : Blo 515797 774059 := bstep (se 1 (by rfl) ⟨580544, by rfl⟩ : syracuseStep 774059 = 1161089) B1161089
theorem B774089 : Blo 515797 774089 := bstep (se 2 (by rfl) ⟨290283, by rfl⟩ : syracuseStep 774089 = 580567) B580567
theorem B872491 : Blo 515797 872491 := bstep (se 1 (by rfl) ⟨654368, by rfl⟩ : syracuseStep 872491 = 1308737) B1308737
theorem B774203 : Blo 515797 774203 := bstep (se 1 (by rfl) ⟨580652, by rfl⟩ : syracuseStep 774203 = 1161305) B1161305
theorem B774263 : Blo 515797 774263 := bstep (se 1 (by rfl) ⟨580697, by rfl⟩ : syracuseStep 774263 = 1161395) B1161395
theorem B1167479 : Blo 515797 1167479 := bstep (se 1 (by rfl) ⟨875609, by rfl⟩ : syracuseStep 1167479 = 1751219) B1751219
theorem B774287 : Blo 515797 774287 := bstep (se 1 (by rfl) ⟨580715, by rfl⟩ : syracuseStep 774287 = 1161431) B1161431
theorem B774329 : Blo 515797 774329 := bstep (se 2 (by rfl) ⟨290373, by rfl⟩ : syracuseStep 774329 = 580747) B580747
theorem B872633 : Blo 515797 872633 := bstep (se 2 (by rfl) ⟨327237, by rfl⟩ : syracuseStep 872633 = 654475) B654475
theorem B774407 : Blo 515797 774407 := bstep (se 1 (by rfl) ⟨580805, by rfl⟩ : syracuseStep 774407 = 1161611) B1161611
theorem B774443 : Blo 515797 774443 := bstep (se 1 (by rfl) ⟨580832, by rfl⟩ : syracuseStep 774443 = 1161665) B1161665
theorem B1167659 : Blo 515797 1167659 := bstep (se 1 (by rfl) ⟨875744, by rfl⟩ : syracuseStep 1167659 = 1751489) B1751489
theorem B2216251 : Blo 515797 2216251 := bstep (se 1 (by rfl) ⟨1662188, by rfl⟩ : syracuseStep 2216251 = 3324377) B3324377
theorem B774473 : Blo 515797 774473 := bstep (se 2 (by rfl) ⟨290427, by rfl⟩ : syracuseStep 774473 = 580855) B580855
theorem B774587 : Blo 515797 774587 := bstep (se 1 (by rfl) ⟨580940, by rfl⟩ : syracuseStep 774587 = 1161881) B1161881
theorem B774647 : Blo 515797 774647 := bstep (se 1 (by rfl) ⟨580985, by rfl⟩ : syracuseStep 774647 = 1161971) B1161971
theorem B1102351 : Blo 515797 1102351 := bstep (se 1 (by rfl) ⟨826763, by rfl⟩ : syracuseStep 1102351 = 1653527) B1653527
theorem B774671 : Blo 515797 774671 := bstep (se 1 (by rfl) ⟨581003, by rfl⟩ : syracuseStep 774671 = 1162007) B1162007
theorem B774713 : Blo 515797 774713 := bstep (se 2 (by rfl) ⟨290517, by rfl⟩ : syracuseStep 774713 = 581035) B581035
theorem B774791 : Blo 515797 774791 := bstep (se 1 (by rfl) ⟨581093, by rfl⟩ : syracuseStep 774791 = 1162187) B1162187
theorem B1168019 : Blo 515797 1168019 := bstep (se 1 (by rfl) ⟨876014, by rfl⟩ : syracuseStep 1168019 = 1752029) B1752029
theorem B774827 : Blo 515797 774827 := bstep (se 1 (by rfl) ⟨581120, by rfl⟩ : syracuseStep 774827 = 1162241) B1162241
theorem B774857 : Blo 515797 774857 := bstep (se 2 (by rfl) ⟨290571, by rfl⟩ : syracuseStep 774857 = 581143) B581143
theorem B1168073 : Blo 515797 1168073 := bstep (se 2 (by rfl) ⟨438027, by rfl⟩ : syracuseStep 1168073 = 876055) B876055
theorem B774971 : Blo 515797 774971 := bstep (se 1 (by rfl) ⟨581228, by rfl⟩ : syracuseStep 774971 = 1162457) B1162457
theorem B775031 : Blo 515797 775031 := bstep (se 1 (by rfl) ⟨581273, by rfl⟩ : syracuseStep 775031 = 1162547) B1162547
theorem B873335 : Blo 515797 873335 := bstep (se 1 (by rfl) ⟨655001, by rfl⟩ : syracuseStep 873335 = 1310003) B1310003
theorem B1102727 : Blo 515797 1102727 := bstep (se 1 (by rfl) ⟨827045, by rfl⟩ : syracuseStep 1102727 = 1654091) B1654091
theorem B775055 : Blo 515797 775055 := bstep (se 1 (by rfl) ⟨581291, by rfl⟩ : syracuseStep 775055 = 1162583) B1162583
theorem B775097 : Blo 515797 775097 := bstep (se 2 (by rfl) ⟨290661, by rfl⟩ : syracuseStep 775097 = 581323) B581323
theorem B775175 : Blo 515797 775175 := bstep (se 1 (by rfl) ⟨581381, by rfl⟩ : syracuseStep 775175 = 1162763) B1162763
theorem B775211 : Blo 515797 775211 := bstep (se 1 (by rfl) ⟨581408, by rfl⟩ : syracuseStep 775211 = 1162817) B1162817
theorem B775241 : Blo 515797 775241 := bstep (se 2 (by rfl) ⟨290715, by rfl⟩ : syracuseStep 775241 = 581431) B581431
theorem B775355 : Blo 515797 775355 := bstep (se 1 (by rfl) ⟨581516, by rfl⟩ : syracuseStep 775355 = 1163033) B1163033
theorem B775415 : Blo 515797 775415 := bstep (se 1 (by rfl) ⟨581561, by rfl⟩ : syracuseStep 775415 = 1163123) B1163123
theorem B1496321 : Blo 515797 1496321 := bstep (se 2 (by rfl) ⟨561120, by rfl⟩ : syracuseStep 1496321 = 1122241) B1122241
theorem B775439 : Blo 515797 775439 := bstep (se 1 (by rfl) ⟨581579, by rfl⟩ : syracuseStep 775439 = 1163159) B1163159
theorem B775481 : Blo 515797 775481 := bstep (se 2 (by rfl) ⟨290805, by rfl⟩ : syracuseStep 775481 = 581611) B581611
theorem B873787 : Blo 515797 873787 := bstep (se 1 (by rfl) ⟨655340, by rfl⟩ : syracuseStep 873787 = 1310681) B1310681
theorem B775559 : Blo 515797 775559 := bstep (se 1 (by rfl) ⟨581669, by rfl⟩ : syracuseStep 775559 = 1163339) B1163339
theorem B1168775 : Blo 515797 1168775 := bstep (se 1 (by rfl) ⟨876581, by rfl⟩ : syracuseStep 1168775 = 1753163) B1753163
theorem B4412819 : Blo 515797 4412819 := bstep (se 1 (by rfl) ⟨3309614, by rfl⟩ : syracuseStep 4412819 = 6619229) B6619229
theorem B775595 : Blo 515797 775595 := bstep (se 1 (by rfl) ⟨581696, by rfl⟩ : syracuseStep 775595 = 1163393) B1163393
theorem B775625 : Blo 515797 775625 := bstep (se 2 (by rfl) ⟨290859, by rfl⟩ : syracuseStep 775625 = 581719) B581719
theorem B873929 : Blo 515797 873929 := bstep (se 2 (by rfl) ⟨327723, by rfl⟩ : syracuseStep 873929 = 655447) B655447
theorem B775739 : Blo 515797 775739 := bstep (se 1 (by rfl) ⟨581804, by rfl⟩ : syracuseStep 775739 = 1163609) B1163609
theorem B1168955 : Blo 515797 1168955 := bstep (se 1 (by rfl) ⟨876716, by rfl⟩ : syracuseStep 1168955 = 1753433) B1753433
theorem B775799 : Blo 515797 775799 := bstep (se 1 (by rfl) ⟨581849, by rfl⟩ : syracuseStep 775799 = 1163699) B1163699
theorem B775823 : Blo 515797 775823 := bstep (se 1 (by rfl) ⟨581867, by rfl⟩ : syracuseStep 775823 = 1163735) B1163735
theorem B775865 : Blo 515797 775865 := bstep (se 2 (by rfl) ⟨290949, by rfl⟩ : syracuseStep 775865 = 581899) B581899
theorem B1169081 : Blo 515797 1169081 := bstep (se 2 (by rfl) ⟨438405, by rfl⟩ : syracuseStep 1169081 = 876811) B876811
theorem B775943 : Blo 515797 775943 := bstep (se 1 (by rfl) ⟨581957, by rfl⟩ : syracuseStep 775943 = 1163915) B1163915
theorem B2807585 : Blo 515797 2807585 := bstep (se 2 (by rfl) ⟨1052844, by rfl⟩ : syracuseStep 2807585 = 2105689) B2105689
theorem B775979 : Blo 515797 775979 := bstep (se 1 (by rfl) ⟨581984, by rfl⟩ : syracuseStep 775979 = 1163969) B1163969
theorem B776009 : Blo 515797 776009 := bstep (se 2 (by rfl) ⟨291003, by rfl⟩ : syracuseStep 776009 = 582007) B582007
theorem B9983897 : Blo 515797 9983897 := bstep (se 2 (by rfl) ⟨3743961, by rfl⟩ : syracuseStep 9983897 = 7487923) B7487923
theorem B776123 : Blo 515797 776123 := bstep (se 1 (by rfl) ⟨582092, by rfl⟩ : syracuseStep 776123 = 1164185) B1164185
theorem B776183 : Blo 515797 776183 := bstep (se 1 (by rfl) ⟨582137, by rfl⟩ : syracuseStep 776183 = 1164275) B1164275
theorem B776207 : Blo 515797 776207 := bstep (se 1 (by rfl) ⟨582155, by rfl⟩ : syracuseStep 776207 = 1164311) B1164311
theorem B1169423 : Blo 515797 1169423 := bstep (se 1 (by rfl) ⟨877067, by rfl⟩ : syracuseStep 1169423 = 1754135) B1754135
theorem B2218013 : Blo 515797 2218013 := bstep (se 3 (by rfl) ⟨415877, by rfl⟩ : syracuseStep 2218013 = 831755) B831755
theorem B1169441 : Blo 515797 1169441 := bstep (se 2 (by rfl) ⟨438540, by rfl⟩ : syracuseStep 1169441 = 877081) B877081
theorem B776249 : Blo 515797 776249 := bstep (se 2 (by rfl) ⟨291093, by rfl⟩ : syracuseStep 776249 = 582187) B582187
theorem B2480195 : Blo 515797 2480195 := bstep (se 1 (by rfl) ⟨1860146, by rfl⟩ : syracuseStep 2480195 = 3720293) B3720293
theorem B776327 : Blo 515797 776327 := bstep (se 1 (by rfl) ⟨582245, by rfl⟩ : syracuseStep 776327 = 1164491) B1164491
theorem B874631 : Blo 515797 874631 := bstep (se 1 (by rfl) ⟨655973, by rfl⟩ : syracuseStep 874631 = 1311947) B1311947
theorem B776363 : Blo 515797 776363 := bstep (se 1 (by rfl) ⟨582272, by rfl⟩ : syracuseStep 776363 = 1164545) B1164545
theorem B776393 : Blo 515797 776393 := bstep (se 2 (by rfl) ⟨291147, by rfl⟩ : syracuseStep 776393 = 582295) B582295
theorem B776507 : Blo 515797 776507 := bstep (se 1 (by rfl) ⟨582380, by rfl⟩ : syracuseStep 776507 = 1164761) B1164761
theorem B776567 : Blo 515797 776567 := bstep (se 1 (by rfl) ⟨582425, by rfl⟩ : syracuseStep 776567 = 1164851) B1164851
theorem B776591 : Blo 515797 776591 := bstep (se 1 (by rfl) ⟨582443, by rfl⟩ : syracuseStep 776591 = 1164887) B1164887
theorem B2611601 : Blo 515797 2611601 := bstep (se 2 (by rfl) ⟨979350, by rfl⟩ : syracuseStep 2611601 = 1958701) B1958701
theorem B2808211 : Blo 515797 2808211 := bstep (se 1 (by rfl) ⟨2106158, by rfl⟩ : syracuseStep 2808211 = 4212317) B4212317
theorem B776633 : Blo 515797 776633 := bstep (se 2 (by rfl) ⟨291237, by rfl⟩ : syracuseStep 776633 = 582475) B582475
theorem B776711 : Blo 515797 776711 := bstep (se 1 (by rfl) ⟨582533, by rfl⟩ : syracuseStep 776711 = 1165067) B1165067
theorem B776747 : Blo 515797 776747 := bstep (se 1 (by rfl) ⟨582560, by rfl⟩ : syracuseStep 776747 = 1165121) B1165121
theorem B776777 : Blo 515797 776777 := bstep (se 2 (by rfl) ⟨291291, by rfl⟩ : syracuseStep 776777 = 582583) B582583
theorem B776891 : Blo 515797 776891 := bstep (se 1 (by rfl) ⟨582668, by rfl⟩ : syracuseStep 776891 = 1165337) B1165337
theorem B2218697 : Blo 515797 2218697 := bstep (se 2 (by rfl) ⟨832011, by rfl⟩ : syracuseStep 2218697 = 1664023) B1664023
theorem B776951 : Blo 515797 776951 := bstep (se 1 (by rfl) ⟨582713, by rfl⟩ : syracuseStep 776951 = 1165427) B1165427
theorem B776975 : Blo 515797 776975 := bstep (se 1 (by rfl) ⟨582731, by rfl⟩ : syracuseStep 776975 = 1165463) B1165463
theorem B875279 : Blo 515797 875279 := bstep (se 1 (by rfl) ⟨656459, by rfl⟩ : syracuseStep 875279 = 1312919) B1312919
theorem B6282035 : Blo 515797 6282035 := bstep (se 1 (by rfl) ⟨4711526, by rfl⟩ : syracuseStep 6282035 = 9423053) B9423053
theorem B777017 : Blo 515797 777017 := bstep (se 2 (by rfl) ⟨291381, by rfl⟩ : syracuseStep 777017 = 582763) B582763
theorem B777095 : Blo 515797 777095 := bstep (se 1 (by rfl) ⟨582821, by rfl⟩ : syracuseStep 777095 = 1165643) B1165643
theorem B580495 : Blo 515797 580495 := bstep (se 1 (by rfl) ⟨435371, by rfl⟩ : syracuseStep 580495 = 870743) B870743
theorem B777131 : Blo 515797 777131 := bstep (se 1 (by rfl) ⟨582848, by rfl⟩ : syracuseStep 777131 = 1165697) B1165697
theorem B777161 : Blo 515797 777161 := bstep (se 2 (by rfl) ⟨291435, by rfl⟩ : syracuseStep 777161 = 582871) B582871
theorem B777275 : Blo 515797 777275 := bstep (se 1 (by rfl) ⟨582956, by rfl⟩ : syracuseStep 777275 = 1165913) B1165913
theorem B777335 : Blo 515797 777335 := bstep (se 1 (by rfl) ⟨583001, by rfl⟩ : syracuseStep 777335 = 1166003) B1166003
theorem B777359 : Blo 515797 777359 := bstep (se 1 (by rfl) ⟨583019, by rfl⟩ : syracuseStep 777359 = 1166039) B1166039
theorem B777401 : Blo 515797 777401 := bstep (se 2 (by rfl) ⟨291525, by rfl⟩ : syracuseStep 777401 = 583051) B583051
theorem B777479 : Blo 515797 777479 := bstep (se 1 (by rfl) ⟨583109, by rfl⟩ : syracuseStep 777479 = 1166219) B1166219
theorem B1400075 : Blo 515797 1400075 := bstep (se 1 (by rfl) ⟨1050056, by rfl⟩ : syracuseStep 1400075 = 2100113) B2100113
theorem B1662241 : Blo 515797 1662241 := bstep (se 2 (by rfl) ⟨623340, by rfl⟩ : syracuseStep 1662241 = 1246681) B1246681
theorem B777515 : Blo 515797 777515 := bstep (se 1 (by rfl) ⟨583136, by rfl⟩ : syracuseStep 777515 = 1166273) B1166273
theorem B875819 : Blo 515797 875819 := bstep (se 1 (by rfl) ⟨656864, by rfl⟩ : syracuseStep 875819 = 1313729) B1313729
theorem B3366203 : Blo 515797 3366203 := bstep (se 1 (by rfl) ⟨2524652, by rfl⟩ : syracuseStep 3366203 = 5049305) B5049305
theorem B777545 : Blo 515797 777545 := bstep (se 2 (by rfl) ⟨291579, by rfl⟩ : syracuseStep 777545 = 583159) B583159
theorem B580999 : Blo 515797 580999 := bstep (se 1 (by rfl) ⟨435749, by rfl⟩ : syracuseStep 580999 = 871499) B871499
theorem B777659 : Blo 515797 777659 := bstep (se 1 (by rfl) ⟨583244, by rfl⟩ : syracuseStep 777659 = 1166489) B1166489
theorem B777719 : Blo 515797 777719 := bstep (se 1 (by rfl) ⟨583289, by rfl⟩ : syracuseStep 777719 = 1166579) B1166579
theorem B777743 : Blo 515797 777743 := bstep (se 1 (by rfl) ⟨583307, by rfl⟩ : syracuseStep 777743 = 1166615) B1166615
theorem B777785 : Blo 515797 777785 := bstep (se 2 (by rfl) ⟨291669, by rfl⟩ : syracuseStep 777785 = 583339) B583339
theorem B581179 : Blo 515797 581179 := bstep (se 1 (by rfl) ⟨435884, by rfl⟩ : syracuseStep 581179 = 871769) B871769
theorem B777863 : Blo 515797 777863 := bstep (se 1 (by rfl) ⟨583397, by rfl⟩ : syracuseStep 777863 = 1166795) B1166795
theorem B777899 : Blo 515797 777899 := bstep (se 1 (by rfl) ⟨583424, by rfl⟩ : syracuseStep 777899 = 1166849) B1166849
theorem B876217 : Blo 515797 876217 := bstep (se 2 (by rfl) ⟨328581, by rfl⟩ : syracuseStep 876217 = 657163) B657163
theorem B777929 : Blo 515797 777929 := bstep (se 2 (by rfl) ⟨291723, by rfl⟩ : syracuseStep 777929 = 583447) B583447
theorem B515847 : Blo 515797 515847 := bstep (se 1 (by rfl) ⟨386885, by rfl⟩ : syracuseStep 515847 = 773771) B773771
theorem B515855 : Blo 515797 515855 := bstep (se 1 (by rfl) ⟨386891, by rfl⟩ : syracuseStep 515855 = 773783) B773783
theorem B515899 : Blo 515797 515899 := bstep (se 1 (by rfl) ⟨386924, by rfl⟩ : syracuseStep 515899 = 773849) B773849
theorem B778043 : Blo 515797 778043 := bstep (se 1 (by rfl) ⟨583532, by rfl⟩ : syracuseStep 778043 = 1167065) B1167065
theorem B778103 : Blo 515797 778103 := bstep (se 1 (by rfl) ⟨583577, by rfl⟩ : syracuseStep 778103 = 1167155) B1167155
theorem B515975 : Blo 515797 515975 := bstep (se 1 (by rfl) ⟨386981, by rfl⟩ : syracuseStep 515975 = 773963) B773963
theorem B515983 : Blo 515797 515983 := bstep (se 1 (by rfl) ⟨386987, by rfl⟩ : syracuseStep 515983 = 773975) B773975
theorem B778127 : Blo 515797 778127 := bstep (se 1 (by rfl) ⟨583595, by rfl⟩ : syracuseStep 778127 = 1167191) B1167191
theorem B4186009 : Blo 515797 4186009 := bstep (se 2 (by rfl) ⟨1569753, by rfl⟩ : syracuseStep 4186009 = 3139507) B3139507
theorem B778169 : Blo 515797 778169 := bstep (se 2 (by rfl) ⟨291813, by rfl⟩ : syracuseStep 778169 = 583627) B583627
theorem B516027 : Blo 515797 516027 := bstep (se 1 (by rfl) ⟨387020, by rfl⟩ : syracuseStep 516027 = 774041) B774041
theorem B516103 : Blo 515797 516103 := bstep (se 1 (by rfl) ⟨387077, by rfl⟩ : syracuseStep 516103 = 774155) B774155
theorem B778247 : Blo 515797 778247 := bstep (se 1 (by rfl) ⟨583685, by rfl⟩ : syracuseStep 778247 = 1167371) B1167371
theorem B516111 : Blo 515797 516111 := bstep (se 1 (by rfl) ⟨387083, by rfl⟩ : syracuseStep 516111 = 774167) B774167
theorem B581647 : Blo 515797 581647 := bstep (se 1 (by rfl) ⟨436235, by rfl⟩ : syracuseStep 581647 = 872471) B872471
theorem B778283 : Blo 515797 778283 := bstep (se 1 (by rfl) ⟨583712, by rfl⟩ : syracuseStep 778283 = 1167425) B1167425
theorem B516155 : Blo 515797 516155 := bstep (se 1 (by rfl) ⟨387116, by rfl⟩ : syracuseStep 516155 = 774233) B774233
theorem B778313 : Blo 515797 778313 := bstep (se 2 (by rfl) ⟨291867, by rfl⟩ : syracuseStep 778313 = 583735) B583735
theorem B516231 : Blo 515797 516231 := bstep (se 1 (by rfl) ⟨387173, by rfl⟩ : syracuseStep 516231 = 774347) B774347
theorem B516239 : Blo 515797 516239 := bstep (se 1 (by rfl) ⟨387179, by rfl⟩ : syracuseStep 516239 = 774359) B774359
theorem B516283 : Blo 515797 516283 := bstep (se 1 (by rfl) ⟨387212, by rfl⟩ : syracuseStep 516283 = 774425) B774425
theorem B778427 : Blo 515797 778427 := bstep (se 1 (by rfl) ⟨583820, by rfl⟩ : syracuseStep 778427 = 1167641) B1167641
theorem B778487 : Blo 515797 778487 := bstep (se 1 (by rfl) ⟨583865, by rfl⟩ : syracuseStep 778487 = 1167731) B1167731
theorem B516359 : Blo 515797 516359 := bstep (se 1 (by rfl) ⟨387269, by rfl⟩ : syracuseStep 516359 = 774539) B774539
theorem B516367 : Blo 515797 516367 := bstep (se 1 (by rfl) ⟨387275, by rfl⟩ : syracuseStep 516367 = 774551) B774551
theorem B778511 : Blo 515797 778511 := bstep (se 1 (by rfl) ⟨583883, by rfl⟩ : syracuseStep 778511 = 1167767) B1167767
theorem B778553 : Blo 515797 778553 := bstep (se 2 (by rfl) ⟨291957, by rfl⟩ : syracuseStep 778553 = 583915) B583915
theorem B516411 : Blo 515797 516411 := bstep (se 1 (by rfl) ⟨387308, by rfl⟩ : syracuseStep 516411 = 774617) B774617
theorem B876919 : Blo 515797 876919 := bstep (se 1 (by rfl) ⟨657689, by rfl⟩ : syracuseStep 876919 = 1315379) B1315379
theorem B516487 : Blo 515797 516487 := bstep (se 1 (by rfl) ⟨387365, by rfl⟩ : syracuseStep 516487 = 774731) B774731
theorem B778631 : Blo 515797 778631 := bstep (se 1 (by rfl) ⟨583973, by rfl⟩ : syracuseStep 778631 = 1167947) B1167947
theorem B516495 : Blo 515797 516495 := bstep (se 1 (by rfl) ⟨387371, by rfl⟩ : syracuseStep 516495 = 774743) B774743
theorem B778667 : Blo 515797 778667 := bstep (se 1 (by rfl) ⟨584000, by rfl⟩ : syracuseStep 778667 = 1168001) B1168001
theorem B516539 : Blo 515797 516539 := bstep (se 1 (by rfl) ⟨387404, by rfl⟩ : syracuseStep 516539 = 774809) B774809
theorem B778697 : Blo 515797 778697 := bstep (se 2 (by rfl) ⟨292011, by rfl⟩ : syracuseStep 778697 = 584023) B584023
theorem B2613707 : Blo 515797 2613707 := bstep (se 1 (by rfl) ⟨1960280, by rfl⟩ : syracuseStep 2613707 = 3920561) B3920561
theorem B516615 : Blo 515797 516615 := bstep (se 1 (by rfl) ⟨387461, by rfl⟩ : syracuseStep 516615 = 774923) B774923
theorem B582151 : Blo 515797 582151 := bstep (se 1 (by rfl) ⟨436613, by rfl⟩ : syracuseStep 582151 = 873227) B873227
theorem B516623 : Blo 515797 516623 := bstep (se 1 (by rfl) ⟨387467, by rfl⟩ : syracuseStep 516623 = 774935) B774935
theorem B516667 : Blo 515797 516667 := bstep (se 1 (by rfl) ⟨387500, by rfl⟩ : syracuseStep 516667 = 775001) B775001
theorem B778811 : Blo 515797 778811 := bstep (se 1 (by rfl) ⟨584108, by rfl⟩ : syracuseStep 778811 = 1168217) B1168217
theorem B877115 : Blo 515797 877115 := bstep (se 1 (by rfl) ⟨657836, by rfl⟩ : syracuseStep 877115 = 1315673) B1315673
theorem B1958519 : Blo 515797 1958519 := bstep (se 1 (by rfl) ⟨1468889, by rfl⟩ : syracuseStep 1958519 = 2937779) B2937779
theorem B778871 : Blo 515797 778871 := bstep (se 1 (by rfl) ⟨584153, by rfl⟩ : syracuseStep 778871 = 1168307) B1168307
theorem B516743 : Blo 515797 516743 := bstep (se 1 (by rfl) ⟨387557, by rfl⟩ : syracuseStep 516743 = 775115) B775115
theorem B516751 : Blo 515797 516751 := bstep (se 1 (by rfl) ⟨387563, by rfl⟩ : syracuseStep 516751 = 775127) B775127
theorem B778895 : Blo 515797 778895 := bstep (se 1 (by rfl) ⟨584171, by rfl⟩ : syracuseStep 778895 = 1168343) B1168343
theorem B778937 : Blo 515797 778937 := bstep (se 2 (by rfl) ⟨292101, by rfl⟩ : syracuseStep 778937 = 584203) B584203
theorem B516795 : Blo 515797 516795 := bstep (se 1 (by rfl) ⟨387596, by rfl⟩ : syracuseStep 516795 = 775193) B775193
theorem B582331 : Blo 515797 582331 := bstep (se 1 (by rfl) ⟨436748, by rfl⟩ : syracuseStep 582331 = 873497) B873497
theorem B2941697 : Blo 515797 2941697 := bstep (se 2 (by rfl) ⟨1103136, by rfl⟩ : syracuseStep 2941697 = 2206273) B2206273
theorem B516871 : Blo 515797 516871 := bstep (se 1 (by rfl) ⟨387653, by rfl⟩ : syracuseStep 516871 = 775307) B775307
theorem B779015 : Blo 515797 779015 := bstep (se 1 (by rfl) ⟨584261, by rfl⟩ : syracuseStep 779015 = 1168523) B1168523
theorem B2614031 : Blo 515797 2614031 := bstep (se 1 (by rfl) ⟨1960523, by rfl⟩ : syracuseStep 2614031 = 3921047) B3921047
theorem B516879 : Blo 515797 516879 := bstep (se 1 (by rfl) ⟨387659, by rfl⟩ : syracuseStep 516879 = 775319) B775319
theorem B779051 : Blo 515797 779051 := bstep (se 1 (by rfl) ⟨584288, by rfl⟩ : syracuseStep 779051 = 1168577) B1168577
theorem B516923 : Blo 515797 516923 := bstep (se 1 (by rfl) ⟨387692, by rfl⟩ : syracuseStep 516923 = 775385) B775385
theorem B779081 : Blo 515797 779081 := bstep (se 2 (by rfl) ⟨292155, by rfl⟩ : syracuseStep 779081 = 584311) B584311
theorem B14377817 : Blo 515797 14377817 := bstep (se 2 (by rfl) ⟨5391681, by rfl⟩ : syracuseStep 14377817 = 10783363) B10783363
theorem B516999 : Blo 515797 516999 := bstep (se 1 (by rfl) ⟨387749, by rfl⟩ : syracuseStep 516999 = 775499) B775499
theorem B517007 : Blo 515797 517007 := bstep (se 1 (by rfl) ⟨387755, by rfl⟩ : syracuseStep 517007 = 775511) B775511
theorem B517051 : Blo 515797 517051 := bstep (se 1 (by rfl) ⟨387788, by rfl⟩ : syracuseStep 517051 = 775577) B775577
theorem B779195 : Blo 515797 779195 := bstep (se 1 (by rfl) ⟨584396, by rfl⟩ : syracuseStep 779195 = 1168793) B1168793
theorem B779255 : Blo 515797 779255 := bstep (se 1 (by rfl) ⟨584441, by rfl⟩ : syracuseStep 779255 = 1168883) B1168883
theorem B517127 : Blo 515797 517127 := bstep (se 1 (by rfl) ⟨387845, by rfl⟩ : syracuseStep 517127 = 775691) B775691
theorem B517135 : Blo 515797 517135 := bstep (se 1 (by rfl) ⟨387851, by rfl⟩ : syracuseStep 517135 = 775703) B775703
theorem B779279 : Blo 515797 779279 := bstep (se 1 (by rfl) ⟨584459, by rfl⟩ : syracuseStep 779279 = 1168919) B1168919
theorem B779321 : Blo 515797 779321 := bstep (se 2 (by rfl) ⟨292245, by rfl⟩ : syracuseStep 779321 = 584491) B584491
theorem B517179 : Blo 515797 517179 := bstep (se 1 (by rfl) ⟨387884, by rfl⟩ : syracuseStep 517179 = 775769) B775769
theorem B517255 : Blo 515797 517255 := bstep (se 1 (by rfl) ⟨387941, by rfl⟩ : syracuseStep 517255 = 775883) B775883
theorem B779399 : Blo 515797 779399 := bstep (se 1 (by rfl) ⟨584549, by rfl⟩ : syracuseStep 779399 = 1169099) B1169099
theorem B517263 : Blo 515797 517263 := bstep (se 1 (by rfl) ⟨387947, by rfl⟩ : syracuseStep 517263 = 775895) B775895
theorem B582799 : Blo 515797 582799 := bstep (se 1 (by rfl) ⟨437099, by rfl⟩ : syracuseStep 582799 = 874199) B874199
theorem B779435 : Blo 515797 779435 := bstep (se 1 (by rfl) ⟨584576, by rfl⟩ : syracuseStep 779435 = 1169153) B1169153
theorem B517307 : Blo 515797 517307 := bstep (se 1 (by rfl) ⟨387980, by rfl⟩ : syracuseStep 517307 = 775961) B775961
theorem B2942153 : Blo 515797 2942153 := bstep (se 2 (by rfl) ⟨1103307, by rfl⟩ : syracuseStep 2942153 = 2206615) B2206615
theorem B779465 : Blo 515797 779465 := bstep (se 2 (by rfl) ⟨292299, by rfl⟩ : syracuseStep 779465 = 584599) B584599
theorem B5596397 : Blo 515797 5596397 := bstep (se 3 (by rfl) ⟨1049324, by rfl⟩ : syracuseStep 5596397 = 2098649) B2098649
theorem B517383 : Blo 515797 517383 := bstep (se 1 (by rfl) ⟨388037, by rfl⟩ : syracuseStep 517383 = 776075) B776075
theorem B517391 : Blo 515797 517391 := bstep (se 1 (by rfl) ⟨388043, by rfl⟩ : syracuseStep 517391 = 776087) B776087
theorem B517435 : Blo 515797 517435 := bstep (se 1 (by rfl) ⟨388076, by rfl⟩ : syracuseStep 517435 = 776153) B776153
theorem B779579 : Blo 515797 779579 := bstep (se 1 (by rfl) ⟨584684, by rfl⟩ : syracuseStep 779579 = 1169369) B1169369
theorem B779639 : Blo 515797 779639 := bstep (se 1 (by rfl) ⟨584729, by rfl⟩ : syracuseStep 779639 = 1169459) B1169459
theorem B517511 : Blo 515797 517511 := bstep (se 1 (by rfl) ⟨388133, by rfl⟩ : syracuseStep 517511 = 776267) B776267
theorem B517519 : Blo 515797 517519 := bstep (se 1 (by rfl) ⟨388139, by rfl⟩ : syracuseStep 517519 = 776279) B776279
theorem B779663 : Blo 515797 779663 := bstep (se 1 (by rfl) ⟨584747, by rfl⟩ : syracuseStep 779663 = 1169495) B1169495
theorem B517563 : Blo 515797 517563 := bstep (se 1 (by rfl) ⟨388172, by rfl⟩ : syracuseStep 517563 = 776345) B776345
theorem B517639 : Blo 515797 517639 := bstep (se 1 (by rfl) ⟨388229, by rfl⟩ : syracuseStep 517639 = 776459) B776459
theorem B517647 : Blo 515797 517647 := bstep (se 1 (by rfl) ⟨388235, by rfl⟩ : syracuseStep 517647 = 776471) B776471
theorem B517691 : Blo 515797 517691 := bstep (se 1 (by rfl) ⟨388268, by rfl⟩ : syracuseStep 517691 = 776537) B776537
theorem B1959491 : Blo 515797 1959491 := bstep (se 1 (by rfl) ⟨1469618, by rfl⟩ : syracuseStep 1959491 = 2939237) B2939237
theorem B5596739 : Blo 515797 5596739 := bstep (se 1 (by rfl) ⟨4197554, by rfl⟩ : syracuseStep 5596739 = 8395109) B8395109
theorem B517767 : Blo 515797 517767 := bstep (se 1 (by rfl) ⟨388325, by rfl⟩ : syracuseStep 517767 = 776651) B776651
theorem B583303 : Blo 515797 583303 := bstep (se 1 (by rfl) ⟨437477, by rfl⟩ : syracuseStep 583303 = 874955) B874955
theorem B517775 : Blo 515797 517775 := bstep (se 1 (by rfl) ⟨388331, by rfl⟩ : syracuseStep 517775 = 776663) B776663
theorem B2483885 : Blo 515797 2483885 := bstep (se 3 (by rfl) ⟨465728, by rfl⟩ : syracuseStep 2483885 = 931457) B931457
theorem B517819 : Blo 515797 517819 := bstep (se 1 (by rfl) ⟨388364, by rfl⟩ : syracuseStep 517819 = 776729) B776729
theorem B5891777 : Blo 515797 5891777 := bstep (se 2 (by rfl) ⟨2209416, by rfl⟩ : syracuseStep 5891777 = 4418833) B4418833
theorem B1795841 : Blo 515797 1795841 := bstep (se 2 (by rfl) ⟨673440, by rfl⟩ : syracuseStep 1795841 = 1346881) B1346881
theorem B517895 : Blo 515797 517895 := bstep (se 1 (by rfl) ⟨388421, by rfl⟩ : syracuseStep 517895 = 776843) B776843
theorem B517903 : Blo 515797 517903 := bstep (se 1 (by rfl) ⟨388427, by rfl⟩ : syracuseStep 517903 = 776855) B776855
theorem B1009441 : Blo 515797 1009441 := bstep (se 2 (by rfl) ⟨378540, by rfl⟩ : syracuseStep 1009441 = 757081) B757081
theorem B517947 : Blo 515797 517947 := bstep (se 1 (by rfl) ⟨388460, by rfl⟩ : syracuseStep 517947 = 776921) B776921
theorem B583483 : Blo 515797 583483 := bstep (se 1 (by rfl) ⟨437612, by rfl⟩ : syracuseStep 583483 = 875225) B875225
theorem B518023 : Blo 515797 518023 := bstep (se 1 (by rfl) ⟨388517, by rfl⟩ : syracuseStep 518023 = 777035) B777035
theorem B518031 : Blo 515797 518031 := bstep (se 1 (by rfl) ⟨388523, by rfl⟩ : syracuseStep 518031 = 777047) B777047
theorem B9955223 : Blo 515797 9955223 := bstep (se 1 (by rfl) ⟨7466417, by rfl⟩ : syracuseStep 9955223 = 14932835) B14932835
theorem B518075 : Blo 515797 518075 := bstep (se 1 (by rfl) ⟨388556, by rfl⟩ : syracuseStep 518075 = 777113) B777113
theorem B1107913 : Blo 515797 1107913 := bstep (se 2 (by rfl) ⟨415467, by rfl⟩ : syracuseStep 1107913 = 830935) B830935
theorem B550919 : Blo 515797 550919 := bstep (se 1 (by rfl) ⟨413189, by rfl⟩ : syracuseStep 550919 = 826379) B826379
theorem B518151 : Blo 515797 518151 := bstep (se 1 (by rfl) ⟨388613, by rfl⟩ : syracuseStep 518151 = 777227) B777227
theorem B1959947 : Blo 515797 1959947 := bstep (se 1 (by rfl) ⟨1469960, by rfl⟩ : syracuseStep 1959947 = 2939921) B2939921
theorem B518159 : Blo 515797 518159 := bstep (se 1 (by rfl) ⟨388619, by rfl⟩ : syracuseStep 518159 = 777239) B777239
theorem B518203 : Blo 515797 518203 := bstep (se 1 (by rfl) ⟨388652, by rfl⟩ : syracuseStep 518203 = 777305) B777305
theorem B518279 : Blo 515797 518279 := bstep (se 1 (by rfl) ⟨388709, by rfl⟩ : syracuseStep 518279 = 777419) B777419
theorem B518287 : Blo 515797 518287 := bstep (se 1 (by rfl) ⟨388715, by rfl⟩ : syracuseStep 518287 = 777431) B777431
theorem B518331 : Blo 515797 518331 := bstep (se 1 (by rfl) ⟨388748, by rfl⟩ : syracuseStep 518331 = 777497) B777497
theorem B2615489 : Blo 515797 2615489 := bstep (se 2 (by rfl) ⟨980808, by rfl⟩ : syracuseStep 2615489 = 1961617) B1961617
theorem B518407 : Blo 515797 518407 := bstep (se 1 (by rfl) ⟨388805, by rfl⟩ : syracuseStep 518407 = 777611) B777611
theorem B518415 : Blo 515797 518415 := bstep (se 1 (by rfl) ⟨388811, by rfl⟩ : syracuseStep 518415 = 777623) B777623
theorem B583951 : Blo 515797 583951 := bstep (se 1 (by rfl) ⟨437963, by rfl⟩ : syracuseStep 583951 = 875927) B875927
theorem B518459 : Blo 515797 518459 := bstep (se 1 (by rfl) ⟨388844, by rfl⟩ : syracuseStep 518459 = 777689) B777689
theorem B518535 : Blo 515797 518535 := bstep (se 1 (by rfl) ⟨388901, by rfl⟩ : syracuseStep 518535 = 777803) B777803
theorem B518543 : Blo 515797 518543 := bstep (se 1 (by rfl) ⟨388907, by rfl⟩ : syracuseStep 518543 = 777815) B777815
theorem B518587 : Blo 515797 518587 := bstep (se 1 (by rfl) ⟨388940, by rfl⟩ : syracuseStep 518587 = 777881) B777881
theorem B518663 : Blo 515797 518663 := bstep (se 1 (by rfl) ⟨388997, by rfl⟩ : syracuseStep 518663 = 777995) B777995
theorem B518671 : Blo 515797 518671 := bstep (se 1 (by rfl) ⟨389003, by rfl⟩ : syracuseStep 518671 = 778007) B778007
theorem B518715 : Blo 515797 518715 := bstep (se 1 (by rfl) ⟨389036, by rfl⟩ : syracuseStep 518715 = 778073) B778073
theorem B518791 : Blo 515797 518791 := bstep (se 1 (by rfl) ⟨389093, by rfl⟩ : syracuseStep 518791 = 778187) B778187
theorem B518799 : Blo 515797 518799 := bstep (se 1 (by rfl) ⟨389099, by rfl⟩ : syracuseStep 518799 = 778199) B778199
theorem B518843 : Blo 515797 518843 := bstep (se 1 (by rfl) ⟨389132, by rfl⟩ : syracuseStep 518843 = 778265) B778265
theorem B518919 : Blo 515797 518919 := bstep (se 1 (by rfl) ⟨389189, by rfl⟩ : syracuseStep 518919 = 778379) B778379
theorem B584455 : Blo 515797 584455 := bstep (se 1 (by rfl) ⟨438341, by rfl⟩ : syracuseStep 584455 = 876683) B876683
theorem B518927 : Blo 515797 518927 := bstep (se 1 (by rfl) ⟨389195, by rfl⟩ : syracuseStep 518927 = 778391) B778391
theorem B518971 : Blo 515797 518971 := bstep (se 1 (by rfl) ⟨389228, by rfl⟩ : syracuseStep 518971 = 778457) B778457
theorem B519047 : Blo 515797 519047 := bstep (se 1 (by rfl) ⟨389285, by rfl⟩ : syracuseStep 519047 = 778571) B778571
theorem B519055 : Blo 515797 519055 := bstep (se 1 (by rfl) ⟨389291, by rfl⟩ : syracuseStep 519055 = 778583) B778583
theorem B519099 : Blo 515797 519099 := bstep (se 1 (by rfl) ⟨389324, by rfl⟩ : syracuseStep 519099 = 778649) B778649
theorem B584635 : Blo 515797 584635 := bstep (se 1 (by rfl) ⟨438476, by rfl⟩ : syracuseStep 584635 = 876953) B876953
theorem B519175 : Blo 515797 519175 := bstep (se 1 (by rfl) ⟨389381, by rfl⟩ : syracuseStep 519175 = 778763) B778763
theorem B519183 : Blo 515797 519183 := bstep (se 1 (by rfl) ⟨389387, by rfl⟩ : syracuseStep 519183 = 778775) B778775
theorem B1305659 : Blo 515797 1305659 := bstep (se 1 (by rfl) ⟨979244, by rfl⟩ : syracuseStep 1305659 = 1958489) B1958489
theorem B519227 : Blo 515797 519227 := bstep (se 1 (by rfl) ⟨389420, by rfl⟩ : syracuseStep 519227 = 778841) B778841
theorem B519303 : Blo 515797 519303 := bstep (se 1 (by rfl) ⟨389477, by rfl⟩ : syracuseStep 519303 = 778955) B778955
theorem B519311 : Blo 515797 519311 := bstep (se 1 (by rfl) ⟨389483, by rfl⟩ : syracuseStep 519311 = 778967) B778967
theorem B519355 : Blo 515797 519355 := bstep (se 1 (by rfl) ⟨389516, by rfl⟩ : syracuseStep 519355 = 779033) B779033
theorem B1404161 : Blo 515797 1404161 := bstep (se 2 (by rfl) ⟨526560, by rfl⟩ : syracuseStep 1404161 = 1053121) B1053121
theorem B519431 : Blo 515797 519431 := bstep (se 1 (by rfl) ⟨389573, by rfl⟩ : syracuseStep 519431 = 779147) B779147
theorem B519439 : Blo 515797 519439 := bstep (se 1 (by rfl) ⟨389579, by rfl⟩ : syracuseStep 519439 = 779159) B779159
theorem B1469755 : Blo 515797 1469755 := bstep (se 1 (by rfl) ⟨1102316, by rfl⟩ : syracuseStep 1469755 = 2204633) B2204633
theorem B519483 : Blo 515797 519483 := bstep (se 1 (by rfl) ⟨389612, by rfl⟩ : syracuseStep 519483 = 779225) B779225
theorem B519559 : Blo 515797 519559 := bstep (se 1 (by rfl) ⟨389669, by rfl⟩ : syracuseStep 519559 = 779339) B779339
theorem B519567 : Blo 515797 519567 := bstep (se 1 (by rfl) ⟨389675, by rfl⟩ : syracuseStep 519567 = 779351) B779351
theorem B1306003 : Blo 515797 1306003 := bstep (se 1 (by rfl) ⟨979502, by rfl⟩ : syracuseStep 1306003 = 1959005) B1959005
theorem B519611 : Blo 515797 519611 := bstep (se 1 (by rfl) ⟨389708, by rfl⟩ : syracuseStep 519611 = 779417) B779417
theorem B2616785 : Blo 515797 2616785 := bstep (se 2 (by rfl) ⟨981294, by rfl⟩ : syracuseStep 2616785 = 1962589) B1962589
theorem B519687 : Blo 515797 519687 := bstep (se 1 (by rfl) ⟨389765, by rfl⟩ : syracuseStep 519687 = 779531) B779531
theorem B519695 : Blo 515797 519695 := bstep (se 1 (by rfl) ⟨389771, by rfl⟩ : syracuseStep 519695 = 779543) B779543
theorem B1306145 : Blo 515797 1306145 := bstep (se 2 (by rfl) ⟨489804, by rfl⟩ : syracuseStep 1306145 = 979609) B979609
theorem B519739 : Blo 515797 519739 := bstep (se 1 (by rfl) ⟨389804, by rfl⟩ : syracuseStep 519739 = 779609) B779609
theorem B1601281 : Blo 515797 1601281 := bstep (se 2 (by rfl) ⟨600480, by rfl⟩ : syracuseStep 1601281 = 1200961) B1200961
theorem B23949107 : Blo 515797 23949107 := bstep (se 1 (by rfl) ⟨17961830, by rfl⟩ : syracuseStep 23949107 = 35923661) B35923661
theorem B1241203 : Blo 515797 1241203 := bstep (se 1 (by rfl) ⟨930902, by rfl⟩ : syracuseStep 1241203 = 1861805) B1861805
theorem B1962103 : Blo 515797 1962103 := bstep (se 1 (by rfl) ⟨1471577, by rfl⟩ : syracuseStep 1962103 = 2943155) B2943155
theorem B1470599 : Blo 515797 1470599 := bstep (se 1 (by rfl) ⟨1102949, by rfl⟩ : syracuseStep 1470599 = 2205899) B2205899
theorem B1307137 : Blo 515797 1307137 := bstep (se 2 (by rfl) ⟨490176, by rfl⟩ : syracuseStep 1307137 = 980353) B980353
theorem B1241867 : Blo 515797 1241867 := bstep (se 1 (by rfl) ⟨931400, by rfl⟩ : syracuseStep 1241867 = 1862801) B1862801
theorem B3732313 : Blo 515797 3732313 := bstep (se 2 (by rfl) ⟨1399617, by rfl⟩ : syracuseStep 3732313 = 2799235) B2799235
theorem B1471385 : Blo 515797 1471385 := bstep (se 2 (by rfl) ⟨551769, by rfl⟩ : syracuseStep 1471385 = 1103539) B1103539
theorem B979913 : Blo 515797 979913 := bstep (se 2 (by rfl) ⟨367467, by rfl⟩ : syracuseStep 979913 = 734935) B734935
theorem B1864657 : Blo 515797 1864657 := bstep (se 2 (by rfl) ⟨699246, by rfl⟩ : syracuseStep 1864657 = 1398493) B1398493
theorem B2946071 : Blo 515797 2946071 := bstep (se 1 (by rfl) ⟨2209553, by rfl⟩ : syracuseStep 2946071 = 4419107) B4419107
theorem B1963075 : Blo 515797 1963075 := bstep (se 1 (by rfl) ⟨1472306, by rfl⟩ : syracuseStep 1963075 = 2944613) B2944613
theorem B1307735 : Blo 515797 1307735 := bstep (se 1 (by rfl) ⟨980801, by rfl⟩ : syracuseStep 1307735 = 1961603) B1961603
theorem B1307947 : Blo 515797 1307947 := bstep (se 1 (by rfl) ⟨980960, by rfl⟩ : syracuseStep 1307947 = 1961921) B1961921
theorem B1963379 : Blo 515797 1963379 := bstep (se 1 (by rfl) ⟨1472534, by rfl⟩ : syracuseStep 1963379 = 2945069) B2945069
theorem B23950727 : Blo 515797 23950727 := bstep (se 1 (by rfl) ⟨17963045, by rfl⟩ : syracuseStep 23950727 = 35926091) B35926091
theorem B1308089 : Blo 515797 1308089 := bstep (se 2 (by rfl) ⟨490533, by rfl⟩ : syracuseStep 1308089 = 981067) B981067
theorem B2618891 : Blo 515797 2618891 := bstep (se 1 (by rfl) ⟨1964168, by rfl⟩ : syracuseStep 2618891 = 3928337) B3928337
theorem B1472033 : Blo 515797 1472033 := bstep (se 2 (by rfl) ⟨552012, by rfl⟩ : syracuseStep 1472033 = 1104025) B1104025
theorem B620203 : Blo 515797 620203 := bstep (se 1 (by rfl) ⟨465152, by rfl⟩ : syracuseStep 620203 = 930305) B930305
theorem B2619053 : Blo 515797 2619053 := bstep (se 3 (by rfl) ⟨491072, by rfl⟩ : syracuseStep 2619053 = 982145) B982145
theorem B6649573 : Blo 515797 6649573 := bstep (se 4 (by rfl) ⟨623397, by rfl⟩ : syracuseStep 6649573 = 1246795) B1246795
theorem B620303 : Blo 515797 620303 := bstep (se 1 (by rfl) ⟨465227, by rfl⟩ : syracuseStep 620303 = 930455) B930455
theorem B1963835 : Blo 515797 1963835 := bstep (se 1 (by rfl) ⟨1472876, by rfl⟩ : syracuseStep 1963835 = 2945753) B2945753
theorem B653447 : Blo 515797 653447 := bstep (se 1 (by rfl) ⟨490085, by rfl⟩ : syracuseStep 653447 = 980171) B980171
theorem B1570969 : Blo 515797 1570969 := bstep (se 2 (by rfl) ⟨589113, by rfl⟩ : syracuseStep 1570969 = 1178227) B1178227
theorem B1964321 : Blo 515797 1964321 := bstep (se 2 (by rfl) ⟨736620, by rfl⟩ : syracuseStep 1964321 = 1473241) B1473241
theorem B1309081 : Blo 515797 1309081 := bstep (se 2 (by rfl) ⟨490905, by rfl⟩ : syracuseStep 1309081 = 981811) B981811
theorem B1473025 : Blo 515797 1473025 := bstep (se 2 (by rfl) ⟨552384, by rfl⟩ : syracuseStep 1473025 = 1104769) B1104769
theorem B1178155 : Blo 515797 1178155 := bstep (se 1 (by rfl) ⟨883616, by rfl⟩ : syracuseStep 1178155 = 1767233) B1767233
theorem B1309243 : Blo 515797 1309243 := bstep (se 1 (by rfl) ⟨981932, by rfl⟩ : syracuseStep 1309243 = 1963865) B1963865
theorem B1309385 : Blo 515797 1309385 := bstep (se 2 (by rfl) ⟨491019, by rfl⟩ : syracuseStep 1309385 = 982039) B982039
theorem B654095 : Blo 515797 654095 := bstep (se 1 (by rfl) ⟨490571, by rfl⟩ : syracuseStep 654095 = 981143) B981143
theorem B981895 : Blo 515797 981895 := bstep (se 1 (by rfl) ⟨736421, by rfl⟩ : syracuseStep 981895 = 1472843) B1472843
theorem B2947985 : Blo 515797 2947985 := bstep (se 2 (by rfl) ⟨1105494, by rfl⟩ : syracuseStep 2947985 = 2210989) B2210989
theorem B1309729 : Blo 515797 1309729 := bstep (se 2 (by rfl) ⟨491148, by rfl⟩ : syracuseStep 1309729 = 982297) B982297
theorem B10648709 : Blo 515797 10648709 := bstep (se 4 (by rfl) ⟨998316, by rfl⟩ : syracuseStep 10648709 = 1996633) B1996633
theorem B1965293 : Blo 515797 1965293 := bstep (se 3 (by rfl) ⟨368492, by rfl⟩ : syracuseStep 1965293 = 736985) B736985
theorem B2620673 : Blo 515797 2620673 := bstep (se 2 (by rfl) ⟨982752, by rfl⟩ : syracuseStep 2620673 = 1965505) B1965505
theorem B2489885 : Blo 515797 2489885 := bstep (se 3 (by rfl) ⟨466853, by rfl⟩ : syracuseStep 2489885 = 933707) B933707
theorem B622139 : Blo 515797 622139 := bstep (se 1 (by rfl) ⟨466604, by rfl⟩ : syracuseStep 622139 = 933209) B933209
theorem B2948669 : Blo 515797 2948669 := bstep (se 3 (by rfl) ⟨552875, by rfl⟩ : syracuseStep 2948669 = 1105751) B1105751
theorem B1310327 : Blo 515797 1310327 := bstep (se 1 (by rfl) ⟨982745, by rfl⟩ : syracuseStep 1310327 = 1965491) B1965491
theorem B1965977 : Blo 515797 1965977 := bstep (se 2 (by rfl) ⟨737241, by rfl⟩ : syracuseStep 1965977 = 1474483) B1474483
theorem B1311329 : Blo 515797 1311329 := bstep (se 2 (by rfl) ⟨491748, by rfl⟩ : syracuseStep 1311329 = 983497) B983497
theorem B1966781 : Blo 515797 1966781 := bstep (se 3 (by rfl) ⟨368771, by rfl⟩ : syracuseStep 1966781 = 737543) B737543
theorem B983801 : Blo 515797 983801 := bstep (se 2 (by rfl) ⟨368925, by rfl⟩ : syracuseStep 983801 = 737851) B737851
theorem B1573793 : Blo 515797 1573793 := bstep (se 2 (by rfl) ⟨590172, by rfl⟩ : syracuseStep 1573793 = 1180345) B1180345
theorem B983983 : Blo 515797 983983 := bstep (se 1 (by rfl) ⟨737987, by rfl⟩ : syracuseStep 983983 = 1475975) B1475975
theorem B984143 : Blo 515797 984143 := bstep (se 1 (by rfl) ⟨738107, by rfl⟩ : syracuseStep 984143 = 1476215) B1476215
theorem B590971 : Blo 515797 590971 := bstep (se 1 (by rfl) ⟨443228, by rfl⟩ : syracuseStep 590971 = 886457) B886457
theorem B2622617 : Blo 515797 2622617 := bstep (se 2 (by rfl) ⟨983481, by rfl⟩ : syracuseStep 2622617 = 1966963) B1966963
theorem B8848601 : Blo 515797 8848601 := bstep (se 2 (by rfl) ⟨3318225, by rfl⟩ : syracuseStep 8848601 = 6636451) B6636451
theorem B4195709 : Blo 515797 4195709 := bstep (se 3 (by rfl) ⟨786695, by rfl⟩ : syracuseStep 4195709 = 1573391) B1573391
theorem B3933683 : Blo 515797 3933683 := bstep (se 1 (by rfl) ⟨2950262, by rfl⟩ : syracuseStep 3933683 = 5900525) B5900525
theorem B657335 : Blo 515797 657335 := bstep (se 1 (by rfl) ⟨493001, by rfl⟩ : syracuseStep 657335 = 986003) B986003
theorem B1312787 : Blo 515797 1312787 := bstep (se 1 (by rfl) ⟨984590, by rfl⟩ : syracuseStep 1312787 = 1969181) B1969181
theorem B657487 : Blo 515797 657487 := bstep (se 1 (by rfl) ⟨493115, by rfl⟩ : syracuseStep 657487 = 986231) B986231
theorem B1968209 : Blo 515797 1968209 := bstep (se 2 (by rfl) ⟨738078, by rfl⟩ : syracuseStep 1968209 = 1476157) B1476157
theorem B985259 : Blo 515797 985259 := bstep (se 1 (by rfl) ⟨738944, by rfl⟩ : syracuseStep 985259 = 1477889) B1477889
theorem B526511 : Blo 515797 526511 := bstep (se 1 (by rfl) ⟨394883, by rfl⟩ : syracuseStep 526511 = 789767) B789767
theorem B9439537 : Blo 515797 9439537 := bstep (se 2 (by rfl) ⟨3539826, by rfl⟩ : syracuseStep 9439537 = 7079653) B7079653
theorem B1345921 : Blo 515797 1345921 := bstep (se 2 (by rfl) ⟨504720, by rfl⟩ : syracuseStep 1345921 = 1009441) B1009441
theorem B1313243 : Blo 515797 1313243 := bstep (se 1 (by rfl) ⟨984932, by rfl⟩ : syracuseStep 1313243 = 1969865) B1969865
theorem B789031 : Blo 515797 789031 := bstep (se 1 (by rfl) ⟨591773, by rfl⟩ : syracuseStep 789031 = 1183547) B1183547
theorem B1477217 : Blo 515797 1477217 := bstep (se 2 (by rfl) ⟨553956, by rfl⟩ : syracuseStep 1477217 = 1107913) B1107913
theorem B4787545 : Blo 515797 4787545 := bstep (se 2 (by rfl) ⟨1795329, by rfl⟩ : syracuseStep 4787545 = 3590659) B3590659
theorem B2133373 : Blo 515797 2133373 := bstep (se 3 (by rfl) ⟨400007, by rfl⟩ : syracuseStep 2133373 = 800015) B800015
theorem B1969697 : Blo 515797 1969697 := bstep (se 2 (by rfl) ⟨738636, by rfl⟩ : syracuseStep 1969697 = 1477273) B1477273
theorem B3149435 : Blo 515797 3149435 := bstep (se 1 (by rfl) ⟨2362076, by rfl⟩ : syracuseStep 3149435 = 4724153) B4724153
theorem B1314427 : Blo 515797 1314427 := bstep (se 1 (by rfl) ⟨985820, by rfl⟩ : syracuseStep 1314427 = 1971641) B1971641
theorem B2494091 : Blo 515797 2494091 := bstep (se 1 (by rfl) ⟨1870568, by rfl⟩ : syracuseStep 2494091 = 3741137) B3741137
theorem B1969879 : Blo 515797 1969879 := bstep (se 1 (by rfl) ⟨1477409, by rfl⟩ : syracuseStep 1969879 = 2954819) B2954819
theorem B1871723 : Blo 515797 1871723 := bstep (se 1 (by rfl) ⟨1403792, by rfl⟩ : syracuseStep 1871723 = 2807585) B2807585
theorem B6655931 : Blo 515797 6655931 := bstep (se 1 (by rfl) ⟨4991948, by rfl⟩ : syracuseStep 6655931 = 9983897) B9983897
theorem B1970183 : Blo 515797 1970183 := bstep (se 1 (by rfl) ⟨1477637, by rfl⟩ : syracuseStep 1970183 = 2955275) B2955275
theorem B1478675 : Blo 515797 1478675 := bstep (se 1 (by rfl) ⟨1109006, by rfl⟩ : syracuseStep 1478675 = 2218013) B2218013
theorem B1741067 : Blo 515797 1741067 := bstep (se 1 (by rfl) ⟨1305800, by rfl⟩ : syracuseStep 1741067 = 2611601) B2611601
theorem B3936599 : Blo 515797 3936599 := bstep (se 1 (by rfl) ⟨2952449, by rfl⟩ : syracuseStep 3936599 = 5904899) B5904899
theorem B6623693 : Blo 515797 6623693 := bstep (se 3 (by rfl) ⟨1241942, by rfl⟩ : syracuseStep 6623693 = 2483885) B2483885
theorem B1479131 : Blo 515797 1479131 := bstep (se 1 (by rfl) ⟨1109348, by rfl⟩ : syracuseStep 1479131 = 2218697) B2218697
theorem B1970669 : Blo 515797 1970669 := bstep (se 3 (by rfl) ⟨369500, by rfl⟩ : syracuseStep 1970669 = 739001) B739001
theorem B2494957 : Blo 515797 2494957 := bstep (se 3 (by rfl) ⟨467804, by rfl⟩ : syracuseStep 2494957 = 935609) B935609
theorem B331321873 : Blo 515797 331321873 := bstep (se 2 (by rfl) ⟨124245702, by rfl⟩ : syracuseStep 331321873 = 248491405) B248491405
theorem B1741337 : Blo 515797 1741337 := bstep (se 2 (by rfl) ⟨653001, by rfl⟩ : syracuseStep 1741337 = 1306003) B1306003
theorem B4264633 : Blo 515797 4264633 := bstep (se 2 (by rfl) ⟨1599237, by rfl⟩ : syracuseStep 4264633 = 3198475) B3198475
theorem B1774295 : Blo 515797 1774295 := bstep (se 1 (by rfl) ⟨1330721, by rfl⟩ : syracuseStep 1774295 = 2661443) B2661443
theorem B2560841 : Blo 515797 2560841 := bstep (se 2 (by rfl) ⟨960315, by rfl⟩ : syracuseStep 2560841 = 1920631) B1920631
theorem B2135041 : Blo 515797 2135041 := bstep (se 2 (by rfl) ⟨800640, by rfl⟩ : syracuseStep 2135041 = 1601281) B1601281
theorem B1971809 : Blo 515797 1971809 := bstep (se 2 (by rfl) ⟨739428, by rfl⟩ : syracuseStep 1971809 = 1478857) B1478857
theorem B1742471 : Blo 515797 1742471 := bstep (se 1 (by rfl) ⟨1306853, by rfl⟩ : syracuseStep 1742471 = 2613707) B2613707
theorem B1742525 : Blo 515797 1742525 := bstep (se 3 (by rfl) ⟨326723, by rfl⟩ : syracuseStep 1742525 = 653447) B653447
theorem B1578707 : Blo 515797 1578707 := bstep (se 1 (by rfl) ⟨1184030, by rfl⟩ : syracuseStep 1578707 = 2368061) B2368061
theorem B1185491 : Blo 515797 1185491 := bstep (se 1 (by rfl) ⟨889118, by rfl⟩ : syracuseStep 1185491 = 1778237) B1778237
theorem B2955001 : Blo 515797 2955001 := bstep (se 2 (by rfl) ⟨1108125, by rfl⟩ : syracuseStep 2955001 = 2216251) B2216251
theorem B1742687 : Blo 515797 1742687 := bstep (se 1 (by rfl) ⟨1307015, by rfl⟩ : syracuseStep 1742687 = 2614031) B2614031
theorem B11540333 : Blo 515797 11540333 := bstep (se 3 (by rfl) ⟨2163812, by rfl⟩ : syracuseStep 11540333 = 4327625) B4327625
theorem B1742849 : Blo 515797 1742849 := bstep (se 2 (by rfl) ⟨653568, by rfl⟩ : syracuseStep 1742849 = 1307137) B1307137
theorem B3545633 : Blo 515797 3545633 := bstep (se 2 (by rfl) ⟨1329612, by rfl⟩ : syracuseStep 3545633 = 2659225) B2659225
theorem B1972795 : Blo 515797 1972795 := bstep (se 1 (by rfl) ⟨1479596, by rfl⟩ : syracuseStep 1972795 = 2959193) B2959193
theorem B1743659 : Blo 515797 1743659 := bstep (se 1 (by rfl) ⟨1307744, by rfl⟩ : syracuseStep 1743659 = 2615489) B2615489
theorem B1973099 : Blo 515797 1973099 := bstep (se 1 (by rfl) ⟨1479824, by rfl⟩ : syracuseStep 1973099 = 2959649) B2959649
theorem B1776647 : Blo 515797 1776647 := bstep (se 1 (by rfl) ⟨1332485, by rfl⟩ : syracuseStep 1776647 = 2664971) B2664971
theorem B1973267 : Blo 515797 1973267 := bstep (se 1 (by rfl) ⟨1479950, by rfl⟩ : syracuseStep 1973267 = 2959901) B2959901
theorem B1743929 : Blo 515797 1743929 := bstep (se 2 (by rfl) ⟨653973, by rfl⟩ : syracuseStep 1743929 = 1307947) B1307947
theorem B2956459 : Blo 515797 2956459 := bstep (se 1 (by rfl) ⟨2217344, by rfl⟩ : syracuseStep 2956459 = 4434689) B4434689
theorem B1744253 : Blo 515797 1744253 := bstep (se 3 (by rfl) ⟨327047, by rfl⟩ : syracuseStep 1744253 = 654095) B654095
theorem B826937 : Blo 515797 826937 := bstep (se 2 (by rfl) ⟨310101, by rfl⟩ : syracuseStep 826937 = 620203) B620203
theorem B1744523 : Blo 515797 1744523 := bstep (se 1 (by rfl) ⟨1308392, by rfl⟩ : syracuseStep 1744523 = 2616785) B2616785
theorem B2629259 : Blo 515797 2629259 := bstep (se 1 (by rfl) ⟨1971944, by rfl⟩ : syracuseStep 2629259 = 3943889) B3943889
theorem B1416953 : Blo 515797 1416953 := bstep (se 2 (by rfl) ⟨531357, by rfl⟩ : syracuseStep 1416953 = 1062715) B1062715
theorem B15966071 : Blo 515797 15966071 := bstep (se 1 (by rfl) ⟨11974553, by rfl⟩ : syracuseStep 15966071 = 23949107) B23949107
theorem B827911 : Blo 515797 827911 := bstep (se 1 (by rfl) ⟨620933, by rfl⟩ : syracuseStep 827911 = 1241867) B1241867
theorem B1417753 : Blo 515797 1417753 := bstep (se 2 (by rfl) ⟨531657, by rfl⟩ : syracuseStep 1417753 = 1063315) B1063315
theorem B3744281 : Blo 515797 3744281 := bstep (se 2 (by rfl) ⟨1404105, by rfl⟩ : syracuseStep 3744281 = 2808211) B2808211
theorem B1745441 : Blo 515797 1745441 := bstep (se 2 (by rfl) ⟨654540, by rfl⟩ : syracuseStep 1745441 = 1309081) B1309081
theorem B1745657 : Blo 515797 1745657 := bstep (se 2 (by rfl) ⟨654621, by rfl⟩ : syracuseStep 1745657 = 1309243) B1309243
theorem B15967151 : Blo 515797 15967151 := bstep (se 1 (by rfl) ⟨11975363, by rfl⟩ : syracuseStep 15967151 = 23950727) B23950727
theorem B1745927 : Blo 515797 1745927 := bstep (se 1 (by rfl) ⟨1309445, by rfl⟩ : syracuseStep 1745927 = 2618891) B2618891
theorem B1746035 : Blo 515797 1746035 := bstep (se 1 (by rfl) ⟨1309526, by rfl⟩ : syracuseStep 1746035 = 2619053) B2619053
theorem B53880025 : Blo 515797 53880025 := bstep (se 2 (by rfl) ⟨20205009, by rfl⟩ : syracuseStep 53880025 = 40410019) B40410019
theorem B1746305 : Blo 515797 1746305 := bstep (se 2 (by rfl) ⟨654864, by rfl⟩ : syracuseStep 1746305 = 1309729) B1309729
theorem B3155807 : Blo 515797 3155807 := bstep (se 1 (by rfl) ⟨2366855, by rfl⟩ : syracuseStep 3155807 = 4733711) B4733711
theorem B2959375 : Blo 515797 2959375 := bstep (se 1 (by rfl) ⟨2219531, by rfl⟩ : syracuseStep 2959375 = 4439063) B4439063
theorem B1747115 : Blo 515797 1747115 := bstep (se 1 (by rfl) ⟨1310336, by rfl⟩ : syracuseStep 1747115 = 2620673) B2620673
theorem B5581345 : Blo 515797 5581345 := bstep (se 2 (by rfl) ⟨2093004, by rfl⟩ : syracuseStep 5581345 = 4186009) B4186009
theorem B1747655 : Blo 515797 1747655 := bstep (se 1 (by rfl) ⟨1310741, by rfl⟩ : syracuseStep 1747655 = 2621483) B2621483
theorem B994223 : Blo 515797 994223 := bstep (se 1 (by rfl) ⟨745667, by rfl⟩ : syracuseStep 994223 = 1491335) B1491335
theorem B21605303 : Blo 515797 21605303 := bstep (se 1 (by rfl) ⟨16203977, by rfl⟩ : syracuseStep 21605303 = 32407955) B32407955
theorem B830711 : Blo 515797 830711 := bstep (se 1 (by rfl) ⟨623033, by rfl⟩ : syracuseStep 830711 = 1246067) B1246067
theorem B16166279 : Blo 515797 16166279 := bstep (se 1 (by rfl) ⟨12124709, by rfl⟩ : syracuseStep 16166279 = 24249419) B24249419
theorem B1748519 : Blo 515797 1748519 := bstep (se 1 (by rfl) ⟨1311389, by rfl⟩ : syracuseStep 1748519 = 2622779) B2622779
theorem B1748627 : Blo 515797 1748627 := bstep (se 1 (by rfl) ⟨1311470, by rfl⟩ : syracuseStep 1748627 = 2622941) B2622941
theorem B2797379 : Blo 515797 2797379 := bstep (se 1 (by rfl) ⟨2098034, by rfl⟩ : syracuseStep 2797379 = 4196069) B4196069
theorem B4271939 : Blo 515797 4271939 := bstep (se 1 (by rfl) ⟨3203954, by rfl⟩ : syracuseStep 4271939 = 6407909) B6407909
theorem B1748843 : Blo 515797 1748843 := bstep (se 1 (by rfl) ⟨1311632, by rfl⟩ : syracuseStep 1748843 = 2623265) B2623265
theorem B2994029 : Blo 515797 2994029 := bstep (se 3 (by rfl) ⟨561380, by rfl⟩ : syracuseStep 2994029 = 1122761) B1122761
theorem B1748897 : Blo 515797 1748897 := bstep (se 2 (by rfl) ⟨655836, by rfl⟩ : syracuseStep 1748897 = 1311673) B1311673
theorem B2207675 : Blo 515797 2207675 := bstep (se 1 (by rfl) ⟨1655756, by rfl⟩ : syracuseStep 2207675 = 3311513) B3311513
theorem B3551321 : Blo 515797 3551321 := bstep (se 2 (by rfl) ⟨1331745, by rfl⟩ : syracuseStep 3551321 = 2663491) B2663491
theorem B3321971 : Blo 515797 3321971 := bstep (se 1 (by rfl) ⟨2491478, by rfl⟩ : syracuseStep 3321971 = 4982957) B4982957
theorem B1749491 : Blo 515797 1749491 := bstep (se 1 (by rfl) ⟨1312118, by rfl⟩ : syracuseStep 1749491 = 2624237) B2624237
theorem B832351 : Blo 515797 832351 := bstep (se 1 (by rfl) ⟨624263, by rfl⟩ : syracuseStep 832351 = 1248527) B1248527
theorem B1750031 : Blo 515797 1750031 := bstep (se 1 (by rfl) ⟨1312523, by rfl⟩ : syracuseStep 1750031 = 2625047) B2625047
theorem B3978487 : Blo 515797 3978487 := bstep (se 1 (by rfl) ⟨2983865, by rfl⟩ : syracuseStep 3978487 = 5967731) B5967731
theorem B4207909 : Blo 515797 4207909 := bstep (se 4 (by rfl) ⟨394491, by rfl⟩ : syracuseStep 4207909 = 788983) B788983
theorem B1160801 : Blo 515797 1160801 := bstep (se 2 (by rfl) ⟨435300, by rfl⟩ : syracuseStep 1160801 = 870601) B870601
theorem B1750625 : Blo 515797 1750625 := bstep (se 2 (by rfl) ⟨656484, by rfl⟩ : syracuseStep 1750625 = 1312969) B1312969
theorem B735151 : Blo 515797 735151 := bstep (se 1 (by rfl) ⟨551363, by rfl⟩ : syracuseStep 735151 = 1102727) B1102727
theorem B1161143 : Blo 515797 1161143 := bstep (se 1 (by rfl) ⟨870857, by rfl⟩ : syracuseStep 1161143 = 1741715) B1741715
theorem B5027777 : Blo 515797 5027777 := bstep (se 2 (by rfl) ⟨1885416, by rfl⟩ : syracuseStep 5027777 = 3770833) B3770833
theorem B5027789 : Blo 515797 5027789 := bstep (se 3 (by rfl) ⟨942710, by rfl⟩ : syracuseStep 5027789 = 1885421) B1885421
theorem B2209949 : Blo 515797 2209949 := bstep (se 3 (by rfl) ⟨414365, by rfl⟩ : syracuseStep 2209949 = 828731) B828731
theorem B997547 : Blo 515797 997547 := bstep (se 1 (by rfl) ⟨748160, by rfl⟩ : syracuseStep 997547 = 1496321) B1496321
theorem B5880113 : Blo 515797 5880113 := bstep (se 2 (by rfl) ⟨2205042, by rfl⟩ : syracuseStep 5880113 = 4410085) B4410085
theorem B1161737 : Blo 515797 1161737 := bstep (se 2 (by rfl) ⟨435651, by rfl⟩ : syracuseStep 1161737 = 871303) B871303
theorem B1653463 : Blo 515797 1653463 := bstep (se 1 (by rfl) ⟨1240097, by rfl⟩ : syracuseStep 1653463 = 2480195) B2480195
theorem B1162079 : Blo 515797 1162079 := bstep (se 1 (by rfl) ⟨871559, by rfl⟩ : syracuseStep 1162079 = 1743119) B1743119
theorem B3980215 : Blo 515797 3980215 := bstep (se 1 (by rfl) ⟨2985161, by rfl⟩ : syracuseStep 3980215 = 5970323) B5970323
theorem B1162259 : Blo 515797 1162259 := bstep (se 1 (by rfl) ⟨871694, by rfl⟩ : syracuseStep 1162259 = 1743389) B1743389
theorem B1752083 : Blo 515797 1752083 := bstep (se 1 (by rfl) ⟨1314062, by rfl⟩ : syracuseStep 1752083 = 2628125) B2628125
theorem B1752407 : Blo 515797 1752407 := bstep (se 1 (by rfl) ⟨1314305, by rfl⟩ : syracuseStep 1752407 = 2628611) B2628611
theorem B1162601 : Blo 515797 1162601 := bstep (se 2 (by rfl) ⟨435975, by rfl⟩ : syracuseStep 1162601 = 871951) B871951
theorem B933383 : Blo 515797 933383 := bstep (se 1 (by rfl) ⟨700037, by rfl⟩ : syracuseStep 933383 = 1400075) B1400075
theorem B1163195 : Blo 515797 1163195 := bstep (se 1 (by rfl) ⟨872396, by rfl⟩ : syracuseStep 1163195 = 1744793) B1744793
theorem B1163321 : Blo 515797 1163321 := bstep (se 2 (by rfl) ⟨436245, by rfl⟩ : syracuseStep 1163321 = 872491) B872491
theorem B1654937 : Blo 515797 1654937 := bstep (se 2 (by rfl) ⟨620601, by rfl⟩ : syracuseStep 1654937 = 1241203) B1241203
theorem B1163663 : Blo 515797 1163663 := bstep (se 1 (by rfl) ⟨872747, by rfl⟩ : syracuseStep 1163663 = 1745495) B1745495
theorem B1753487 : Blo 515797 1753487 := bstep (se 1 (by rfl) ⟨1315115, by rfl⟩ : syracuseStep 1753487 = 2630231) B2630231
theorem B3719627 : Blo 515797 3719627 := bstep (se 1 (by rfl) ⟨2789720, by rfl⟩ : syracuseStep 3719627 = 5579441) B5579441
theorem B9585211 : Blo 515797 9585211 := bstep (se 1 (by rfl) ⟨7188908, by rfl⟩ : syracuseStep 9585211 = 14377817) B14377817
theorem B1163987 : Blo 515797 1163987 := bstep (se 1 (by rfl) ⟨872990, by rfl⟩ : syracuseStep 1163987 = 1745981) B1745981
theorem B1753811 : Blo 515797 1753811 := bstep (se 1 (by rfl) ⟨1315358, by rfl⟩ : syracuseStep 1753811 = 2630717) B2630717
theorem B3327095 : Blo 515797 3327095 := bstep (se 1 (by rfl) ⟨2495321, by rfl⟩ : syracuseStep 3327095 = 4990643) B4990643
theorem B1197227 : Blo 515797 1197227 := bstep (se 1 (by rfl) ⟨897920, by rfl⟩ : syracuseStep 1197227 = 1795841) B1795841
theorem B6636815 : Blo 515797 6636815 := bstep (se 1 (by rfl) ⟨4977611, by rfl⟩ : syracuseStep 6636815 = 9955223) B9955223
theorem B3327247 : Blo 515797 3327247 := bstep (se 1 (by rfl) ⟨2495435, by rfl⟩ : syracuseStep 3327247 = 4990871) B4990871
theorem B1164923 : Blo 515797 1164923 := bstep (se 1 (by rfl) ⟨873692, by rfl⟩ : syracuseStep 1164923 = 1747385) B1747385
theorem B1165049 : Blo 515797 1165049 := bstep (se 2 (by rfl) ⟨436893, by rfl⟩ : syracuseStep 1165049 = 873787) B873787
theorem B1165319 : Blo 515797 1165319 := bstep (se 1 (by rfl) ⟨873989, by rfl⟩ : syracuseStep 1165319 = 1747979) B1747979
theorem B870439 : Blo 515797 870439 := bstep (se 1 (by rfl) ⟨652829, by rfl⟩ : syracuseStep 870439 = 1305659) B1305659
theorem B1165391 : Blo 515797 1165391 := bstep (se 1 (by rfl) ⟨874043, by rfl⟩ : syracuseStep 1165391 = 1748087) B1748087
theorem B936107 : Blo 515797 936107 := bstep (se 1 (by rfl) ⟨702080, by rfl⟩ : syracuseStep 936107 = 1404161) B1404161
theorem B8866097 : Blo 515797 8866097 := bstep (se 2 (by rfl) ⟨3324786, by rfl⟩ : syracuseStep 8866097 = 6649573) B6649573
theorem B3918131 : Blo 515797 3918131 := bstep (se 1 (by rfl) ⟨2938598, by rfl⟩ : syracuseStep 3918131 = 5877197) B5877197
theorem B870763 : Blo 515797 870763 := bstep (se 1 (by rfl) ⟨653072, by rfl⟩ : syracuseStep 870763 = 1306145) B1306145
theorem B1165787 : Blo 515797 1165787 := bstep (se 1 (by rfl) ⟨874340, by rfl⟩ : syracuseStep 1165787 = 1748681) B1748681
theorem B3983905 : Blo 515797 3983905 := bstep (se 2 (by rfl) ⟨1493964, by rfl⟩ : syracuseStep 3983905 = 2987929) B2987929
theorem B2214611 : Blo 515797 2214611 := bstep (se 1 (by rfl) ⟨1660958, by rfl⟩ : syracuseStep 2214611 = 3321917) B3321917
theorem B1166255 : Blo 515797 1166255 := bstep (se 1 (by rfl) ⟨874691, by rfl⟩ : syracuseStep 1166255 = 1749383) B1749383
theorem B1166507 : Blo 515797 1166507 := bstep (se 1 (by rfl) ⟨874880, by rfl⟩ : syracuseStep 1166507 = 1749761) B1749761
theorem B871823 : Blo 515797 871823 := bstep (se 1 (by rfl) ⟨653867, by rfl⟩ : syracuseStep 871823 = 1307735) B1307735
theorem B773711 : Blo 515797 773711 := bstep (se 1 (by rfl) ⟨580283, by rfl⟩ : syracuseStep 773711 = 1160567) B1160567
theorem B872059 : Blo 515797 872059 := bstep (se 1 (by rfl) ⟨654044, by rfl⟩ : syracuseStep 872059 = 1308089) B1308089
theorem B773831 : Blo 515797 773831 := bstep (se 1 (by rfl) ⟨580373, by rfl⟩ : syracuseStep 773831 = 1160747) B1160747
theorem B1167047 : Blo 515797 1167047 := bstep (se 1 (by rfl) ⟨875285, by rfl⟩ : syracuseStep 1167047 = 1750571) B1750571
theorem B773993 : Blo 515797 773993 := bstep (se 2 (by rfl) ⟨290247, by rfl⟩ : syracuseStep 773993 = 580495) B580495
theorem B774071 : Blo 515797 774071 := bstep (se 1 (by rfl) ⟨580553, by rfl⟩ : syracuseStep 774071 = 1161107) B1161107
theorem B774107 : Blo 515797 774107 := bstep (se 1 (by rfl) ⟨580580, by rfl⟩ : syracuseStep 774107 = 1161161) B1161161
theorem B4411421 : Blo 515797 4411421 := bstep (se 3 (by rfl) ⟨827141, by rfl⟩ : syracuseStep 4411421 = 1654283) B1654283
theorem B6082675 : Blo 515797 6082675 := bstep (se 1 (by rfl) ⟨4562006, by rfl⟩ : syracuseStep 6082675 = 9124013) B9124013
theorem B1659037 : Blo 515797 1659037 := bstep (se 3 (by rfl) ⟨311069, by rfl⟩ : syracuseStep 1659037 = 622139) B622139
theorem B125751523 : Blo 515797 125751523 := bstep (se 1 (by rfl) ⟨94313642, by rfl⟩ : syracuseStep 125751523 = 188627285) B188627285
theorem B2216321 : Blo 515797 2216321 := bstep (se 2 (by rfl) ⟨831120, by rfl⟩ : syracuseStep 2216321 = 1662241) B1662241
theorem B774575 : Blo 515797 774575 := bstep (se 1 (by rfl) ⟨580931, by rfl⟩ : syracuseStep 774575 = 1161863) B1161863
theorem B872923 : Blo 515797 872923 := bstep (se 1 (by rfl) ⟨654692, by rfl⟩ : syracuseStep 872923 = 1309385) B1309385
theorem B774665 : Blo 515797 774665 := bstep (se 2 (by rfl) ⟨290499, by rfl⟩ : syracuseStep 774665 = 580999) B580999
theorem B774695 : Blo 515797 774695 := bstep (se 1 (by rfl) ⟨581021, by rfl⟩ : syracuseStep 774695 = 1162043) B1162043
theorem B1167911 : Blo 515797 1167911 := bstep (se 1 (by rfl) ⟨875933, by rfl⟩ : syracuseStep 1167911 = 1751867) B1751867
theorem B774779 : Blo 515797 774779 := bstep (se 1 (by rfl) ⟨581084, by rfl⟩ : syracuseStep 774779 = 1162169) B1162169
theorem B774905 : Blo 515797 774905 := bstep (se 2 (by rfl) ⟨290589, by rfl⟩ : syracuseStep 774905 = 581179) B581179
theorem B7099139 : Blo 515797 7099139 := bstep (se 1 (by rfl) ⟨5324354, by rfl⟩ : syracuseStep 7099139 = 10648709) B10648709
theorem B775007 : Blo 515797 775007 := bstep (se 1 (by rfl) ⟨581255, by rfl⟩ : syracuseStep 775007 = 1162511) B1162511
theorem B775019 : Blo 515797 775019 := bstep (se 1 (by rfl) ⟨581264, by rfl⟩ : syracuseStep 775019 = 1162529) B1162529
theorem B1168235 : Blo 515797 1168235 := bstep (se 1 (by rfl) ⟨876176, by rfl⟩ : syracuseStep 1168235 = 1752353) B1752353
theorem B1168289 : Blo 515797 1168289 := bstep (se 2 (by rfl) ⟨438108, by rfl⟩ : syracuseStep 1168289 = 876217) B876217
theorem B1659923 : Blo 515797 1659923 := bstep (se 1 (by rfl) ⟨1244942, by rfl⟩ : syracuseStep 1659923 = 2489885) B2489885
theorem B1725497 : Blo 515797 1725497 := bstep (se 2 (by rfl) ⟨647061, by rfl⟩ : syracuseStep 1725497 = 1294123) B1294123
theorem B775247 : Blo 515797 775247 := bstep (se 1 (by rfl) ⟨581435, by rfl⟩ : syracuseStep 775247 = 1162871) B1162871
theorem B873551 : Blo 515797 873551 := bstep (se 1 (by rfl) ⟨655163, by rfl⟩ : syracuseStep 873551 = 1310327) B1310327
theorem B775367 : Blo 515797 775367 := bstep (se 1 (by rfl) ⟨581525, by rfl⟩ : syracuseStep 775367 = 1163051) B1163051
theorem B1168631 : Blo 515797 1168631 := bstep (se 1 (by rfl) ⟨876473, by rfl⟩ : syracuseStep 1168631 = 1752947) B1752947
theorem B775529 : Blo 515797 775529 := bstep (se 2 (by rfl) ⟨290823, by rfl⟩ : syracuseStep 775529 = 581647) B581647
theorem B775607 : Blo 515797 775607 := bstep (se 1 (by rfl) ⟨581705, by rfl⟩ : syracuseStep 775607 = 1163411) B1163411
theorem B775643 : Blo 515797 775643 := bstep (se 1 (by rfl) ⟨581732, by rfl⟩ : syracuseStep 775643 = 1163465) B1163465
theorem B1660601 : Blo 515797 1660601 := bstep (se 2 (by rfl) ⟨622725, by rfl⟩ : syracuseStep 1660601 = 1245451) B1245451
theorem B1169225 : Blo 515797 1169225 := bstep (se 2 (by rfl) ⟨438459, by rfl⟩ : syracuseStep 1169225 = 876919) B876919
theorem B776111 : Blo 515797 776111 := bstep (se 1 (by rfl) ⟨582083, by rfl⟩ : syracuseStep 776111 = 1164167) B1164167
theorem B874415 : Blo 515797 874415 := bstep (se 1 (by rfl) ⟨655811, by rfl⟩ : syracuseStep 874415 = 1311623) B1311623
theorem B776201 : Blo 515797 776201 := bstep (se 2 (by rfl) ⟨291075, by rfl⟩ : syracuseStep 776201 = 582151) B582151
theorem B776231 : Blo 515797 776231 := bstep (se 1 (by rfl) ⟨582173, by rfl⟩ : syracuseStep 776231 = 1164347) B1164347
theorem B776315 : Blo 515797 776315 := bstep (se 1 (by rfl) ⟨582236, by rfl⟩ : syracuseStep 776315 = 1164473) B1164473
theorem B1104043 : Blo 515797 1104043 := bstep (se 1 (by rfl) ⟨828032, by rfl⟩ : syracuseStep 1104043 = 1656065) B1656065
theorem B16963829 : Blo 515797 16963829 := bstep (se 5 (by rfl) ⟨795179, by rfl⟩ : syracuseStep 16963829 = 1590359) B1590359
theorem B776441 : Blo 515797 776441 := bstep (se 2 (by rfl) ⟨291165, by rfl⟩ : syracuseStep 776441 = 582331) B582331
theorem B11163905 : Blo 515797 11163905 := bstep (se 2 (by rfl) ⟨4186464, by rfl⟩ : syracuseStep 11163905 = 8372929) B8372929
theorem B776543 : Blo 515797 776543 := bstep (se 1 (by rfl) ⟨582407, by rfl⟩ : syracuseStep 776543 = 1164815) B1164815
theorem B874847 : Blo 515797 874847 := bstep (se 1 (by rfl) ⟨656135, by rfl⟩ : syracuseStep 874847 = 1312271) B1312271
theorem B776555 : Blo 515797 776555 := bstep (se 1 (by rfl) ⟨582416, by rfl⟩ : syracuseStep 776555 = 1164833) B1164833
theorem B776783 : Blo 515797 776783 := bstep (se 1 (by rfl) ⟨582587, by rfl⟩ : syracuseStep 776783 = 1165175) B1165175
theorem B776903 : Blo 515797 776903 := bstep (se 1 (by rfl) ⟨582677, by rfl⟩ : syracuseStep 776903 = 1165355) B1165355
theorem B50420465 : Blo 515797 50420465 := bstep (se 2 (by rfl) ⟨18907674, by rfl⟩ : syracuseStep 50420465 = 37815349) B37815349
theorem B5888861 : Blo 515797 5888861 := bstep (se 3 (by rfl) ⟨1104161, by rfl⟩ : syracuseStep 5888861 = 2208323) B2208323
theorem B777065 : Blo 515797 777065 := bstep (se 2 (by rfl) ⟨291399, by rfl⟩ : syracuseStep 777065 = 582799) B582799
theorem B875407 : Blo 515797 875407 := bstep (se 1 (by rfl) ⟨656555, by rfl⟩ : syracuseStep 875407 = 1313111) B1313111
theorem B777143 : Blo 515797 777143 := bstep (se 1 (by rfl) ⟨582857, by rfl⟩ : syracuseStep 777143 = 1165715) B1165715
theorem B777179 : Blo 515797 777179 := bstep (se 1 (by rfl) ⟨582884, by rfl⟩ : syracuseStep 777179 = 1165769) B1165769
theorem B1989647 : Blo 515797 1989647 := bstep (se 1 (by rfl) ⟨1492235, by rfl⟩ : syracuseStep 1989647 = 2984471) B2984471
theorem B777647 : Blo 515797 777647 := bstep (se 1 (by rfl) ⟨583235, by rfl⟩ : syracuseStep 777647 = 1166471) B1166471
theorem B777737 : Blo 515797 777737 := bstep (se 2 (by rfl) ⟨291651, by rfl⟩ : syracuseStep 777737 = 583303) B583303
theorem B1662497 : Blo 515797 1662497 := bstep (se 2 (by rfl) ⟨623436, by rfl⟩ : syracuseStep 1662497 = 1246873) B1246873
theorem B1859111 : Blo 515797 1859111 := bstep (se 1 (by rfl) ⟨1394333, by rfl⟩ : syracuseStep 1859111 = 2788667) B2788667
theorem B777767 : Blo 515797 777767 := bstep (se 1 (by rfl) ⟨583325, by rfl⟩ : syracuseStep 777767 = 1166651) B1166651
theorem B876089 : Blo 515797 876089 := bstep (se 2 (by rfl) ⟨328533, by rfl⟩ : syracuseStep 876089 = 657067) B657067
theorem B2809441 : Blo 515797 2809441 := bstep (se 2 (by rfl) ⟨1053540, by rfl⟩ : syracuseStep 2809441 = 2107081) B2107081
theorem B777851 : Blo 515797 777851 := bstep (se 1 (by rfl) ⟨583388, by rfl⟩ : syracuseStep 777851 = 1166777) B1166777
theorem B1662599 : Blo 515797 1662599 := bstep (se 1 (by rfl) ⟨1246949, by rfl⟩ : syracuseStep 1662599 = 2493899) B2493899
theorem B6610571 : Blo 515797 6610571 := bstep (se 1 (by rfl) ⟨4957928, by rfl⟩ : syracuseStep 6610571 = 9915857) B9915857
theorem B515803 : Blo 515797 515803 := bstep (se 1 (by rfl) ⟨386852, by rfl⟩ : syracuseStep 515803 = 773705) B773705
theorem B777977 : Blo 515797 777977 := bstep (se 2 (by rfl) ⟨291741, by rfl⟩ : syracuseStep 777977 = 583483) B583483
theorem B515879 : Blo 515797 515879 := bstep (se 1 (by rfl) ⟨386909, by rfl⟩ : syracuseStep 515879 = 773819) B773819
theorem B2613059 : Blo 515797 2613059 := bstep (se 1 (by rfl) ⟨1959794, by rfl⟩ : syracuseStep 2613059 = 3919589) B3919589
theorem B515919 : Blo 515797 515919 := bstep (se 1 (by rfl) ⟨386939, by rfl⟩ : syracuseStep 515919 = 773879) B773879
theorem B515935 : Blo 515797 515935 := bstep (se 1 (by rfl) ⟨386951, by rfl⟩ : syracuseStep 515935 = 773903) B773903
theorem B778079 : Blo 515797 778079 := bstep (se 1 (by rfl) ⟨583559, by rfl⟩ : syracuseStep 778079 = 1167119) B1167119
theorem B778091 : Blo 515797 778091 := bstep (se 1 (by rfl) ⟨583568, by rfl⟩ : syracuseStep 778091 = 1167137) B1167137
theorem B515963 : Blo 515797 515963 := bstep (se 1 (by rfl) ⟨386972, by rfl⟩ : syracuseStep 515963 = 773945) B773945
theorem B516015 : Blo 515797 516015 := bstep (se 1 (by rfl) ⟨387011, by rfl⟩ : syracuseStep 516015 = 774023) B774023
theorem B4415417 : Blo 515797 4415417 := bstep (se 2 (by rfl) ⟨1655781, by rfl⟩ : syracuseStep 4415417 = 3311563) B3311563
theorem B516039 : Blo 515797 516039 := bstep (se 1 (by rfl) ⟨387029, by rfl⟩ : syracuseStep 516039 = 774059) B774059
theorem B516059 : Blo 515797 516059 := bstep (se 1 (by rfl) ⟨387044, by rfl⟩ : syracuseStep 516059 = 774089) B774089
theorem B1400851 : Blo 515797 1400851 := bstep (se 1 (by rfl) ⟨1050638, by rfl⟩ : syracuseStep 1400851 = 2101277) B2101277
theorem B516135 : Blo 515797 516135 := bstep (se 1 (by rfl) ⟨387101, by rfl⟩ : syracuseStep 516135 = 774203) B774203
theorem B516175 : Blo 515797 516175 := bstep (se 1 (by rfl) ⟨387131, by rfl⟩ : syracuseStep 516175 = 774263) B774263
theorem B778319 : Blo 515797 778319 := bstep (se 1 (by rfl) ⟨583739, by rfl⟩ : syracuseStep 778319 = 1167479) B1167479
theorem B516191 : Blo 515797 516191 := bstep (se 1 (by rfl) ⟨387143, by rfl⟩ : syracuseStep 516191 = 774287) B774287
theorem B1859699 : Blo 515797 1859699 := bstep (se 1 (by rfl) ⟨1394774, by rfl⟩ : syracuseStep 1859699 = 2789549) B2789549
theorem B516219 : Blo 515797 516219 := bstep (se 1 (by rfl) ⟨387164, by rfl⟩ : syracuseStep 516219 = 774329) B774329
theorem B581755 : Blo 515797 581755 := bstep (se 1 (by rfl) ⟨436316, by rfl⟩ : syracuseStep 581755 = 872633) B872633
theorem B516271 : Blo 515797 516271 := bstep (se 1 (by rfl) ⟨387203, by rfl⟩ : syracuseStep 516271 = 774407) B774407
theorem B516295 : Blo 515797 516295 := bstep (se 1 (by rfl) ⟨387221, by rfl⟩ : syracuseStep 516295 = 774443) B774443
theorem B778439 : Blo 515797 778439 := bstep (se 1 (by rfl) ⟨583829, by rfl⟩ : syracuseStep 778439 = 1167659) B1167659
theorem B516315 : Blo 515797 516315 := bstep (se 1 (by rfl) ⟨387236, by rfl⟩ : syracuseStep 516315 = 774473) B774473
theorem B6283493 : Blo 515797 6283493 := bstep (se 4 (by rfl) ⟨589077, by rfl⟩ : syracuseStep 6283493 = 1178155) B1178155
theorem B876791 : Blo 515797 876791 := bstep (se 1 (by rfl) ⟨657593, by rfl⟩ : syracuseStep 876791 = 1315187) B1315187
theorem B516391 : Blo 515797 516391 := bstep (se 1 (by rfl) ⟨387293, by rfl⟩ : syracuseStep 516391 = 774587) B774587
theorem B516431 : Blo 515797 516431 := bstep (se 1 (by rfl) ⟨387323, by rfl⟩ : syracuseStep 516431 = 774647) B774647
theorem B516447 : Blo 515797 516447 := bstep (se 1 (by rfl) ⟨387335, by rfl⟩ : syracuseStep 516447 = 774671) B774671
theorem B778601 : Blo 515797 778601 := bstep (se 2 (by rfl) ⟨291975, by rfl⟩ : syracuseStep 778601 = 583951) B583951
theorem B516475 : Blo 515797 516475 := bstep (se 1 (by rfl) ⟨387356, by rfl⟩ : syracuseStep 516475 = 774713) B774713
theorem B516527 : Blo 515797 516527 := bstep (se 1 (by rfl) ⟨387395, by rfl⟩ : syracuseStep 516527 = 774791) B774791
theorem B778679 : Blo 515797 778679 := bstep (se 1 (by rfl) ⟨584009, by rfl⟩ : syracuseStep 778679 = 1168019) B1168019
theorem B516551 : Blo 515797 516551 := bstep (se 1 (by rfl) ⟨387413, by rfl⟩ : syracuseStep 516551 = 774827) B774827
theorem B516571 : Blo 515797 516571 := bstep (se 1 (by rfl) ⟨387428, by rfl⟩ : syracuseStep 516571 = 774857) B774857
theorem B778715 : Blo 515797 778715 := bstep (se 1 (by rfl) ⟨584036, by rfl⟩ : syracuseStep 778715 = 1168073) B1168073
theorem B516647 : Blo 515797 516647 := bstep (se 1 (by rfl) ⟨387485, by rfl⟩ : syracuseStep 516647 = 774971) B774971
theorem B7955003 : Blo 515797 7955003 := bstep (se 1 (by rfl) ⟨5966252, by rfl⟩ : syracuseStep 7955003 = 11932505) B11932505
theorem B516687 : Blo 515797 516687 := bstep (se 1 (by rfl) ⟨387515, by rfl⟩ : syracuseStep 516687 = 775031) B775031
theorem B582223 : Blo 515797 582223 := bstep (se 1 (by rfl) ⟨436667, by rfl⟩ : syracuseStep 582223 = 873335) B873335
theorem B877135 : Blo 515797 877135 := bstep (se 1 (by rfl) ⟨657851, by rfl⟩ : syracuseStep 877135 = 1315703) B1315703
theorem B516703 : Blo 515797 516703 := bstep (se 1 (by rfl) ⟨387527, by rfl⟩ : syracuseStep 516703 = 775055) B775055
theorem B516731 : Blo 515797 516731 := bstep (se 1 (by rfl) ⟨387548, by rfl⟩ : syracuseStep 516731 = 775097) B775097
theorem B516783 : Blo 515797 516783 := bstep (se 1 (by rfl) ⟨387587, by rfl⟩ : syracuseStep 516783 = 775175) B775175
theorem B516807 : Blo 515797 516807 := bstep (se 1 (by rfl) ⟨387605, by rfl⟩ : syracuseStep 516807 = 775211) B775211
theorem B516827 : Blo 515797 516827 := bstep (se 1 (by rfl) ⟨387620, by rfl⟩ : syracuseStep 516827 = 775241) B775241
theorem B516903 : Blo 515797 516903 := bstep (se 1 (by rfl) ⟨387677, by rfl⟩ : syracuseStep 516903 = 775355) B775355
theorem B516943 : Blo 515797 516943 := bstep (se 1 (by rfl) ⟨387707, by rfl⟩ : syracuseStep 516943 = 775415) B775415
theorem B516959 : Blo 515797 516959 := bstep (se 1 (by rfl) ⟨387719, by rfl⟩ : syracuseStep 516959 = 775439) B775439
theorem B1401695 : Blo 515797 1401695 := bstep (se 1 (by rfl) ⟨1051271, by rfl⟩ : syracuseStep 1401695 = 2102543) B2102543
theorem B516987 : Blo 515797 516987 := bstep (se 1 (by rfl) ⟨387740, by rfl⟩ : syracuseStep 516987 = 775481) B775481
theorem B517039 : Blo 515797 517039 := bstep (se 1 (by rfl) ⟨387779, by rfl⟩ : syracuseStep 517039 = 775559) B775559
theorem B779183 : Blo 515797 779183 := bstep (se 1 (by rfl) ⟨584387, by rfl⟩ : syracuseStep 779183 = 1168775) B1168775
theorem B2941879 : Blo 515797 2941879 := bstep (se 1 (by rfl) ⟨2206409, by rfl⟩ : syracuseStep 2941879 = 4412819) B4412819
theorem B517063 : Blo 515797 517063 := bstep (se 1 (by rfl) ⟨387797, by rfl⟩ : syracuseStep 517063 = 775595) B775595
theorem B517083 : Blo 515797 517083 := bstep (se 1 (by rfl) ⟨387812, by rfl⟩ : syracuseStep 517083 = 775625) B775625
theorem B582619 : Blo 515797 582619 := bstep (se 1 (by rfl) ⟨436964, by rfl⟩ : syracuseStep 582619 = 873929) B873929
theorem B779273 : Blo 515797 779273 := bstep (se 2 (by rfl) ⟨292227, by rfl⟩ : syracuseStep 779273 = 584455) B584455
theorem B517159 : Blo 515797 517159 := bstep (se 1 (by rfl) ⟨387869, by rfl⟩ : syracuseStep 517159 = 775739) B775739
theorem B779303 : Blo 515797 779303 := bstep (se 1 (by rfl) ⟨584477, by rfl⟩ : syracuseStep 779303 = 1168955) B1168955
theorem B517199 : Blo 515797 517199 := bstep (se 1 (by rfl) ⟨387899, by rfl⟩ : syracuseStep 517199 = 775799) B775799
theorem B517215 : Blo 515797 517215 := bstep (se 1 (by rfl) ⟨387911, by rfl⟩ : syracuseStep 517215 = 775823) B775823
theorem B517243 : Blo 515797 517243 := bstep (se 1 (by rfl) ⟨387932, by rfl⟩ : syracuseStep 517243 = 775865) B775865
theorem B779387 : Blo 515797 779387 := bstep (se 1 (by rfl) ⟨584540, by rfl⟩ : syracuseStep 779387 = 1169081) B1169081
theorem B517295 : Blo 515797 517295 := bstep (se 1 (by rfl) ⟨387971, by rfl⟩ : syracuseStep 517295 = 775943) B775943
theorem B517319 : Blo 515797 517319 := bstep (se 1 (by rfl) ⟨387989, by rfl⟩ : syracuseStep 517319 = 775979) B775979
theorem B517339 : Blo 515797 517339 := bstep (se 1 (by rfl) ⟨388004, by rfl⟩ : syracuseStep 517339 = 776009) B776009
theorem B779513 : Blo 515797 779513 := bstep (se 2 (by rfl) ⟨292317, by rfl⟩ : syracuseStep 779513 = 584635) B584635
theorem B517415 : Blo 515797 517415 := bstep (se 1 (by rfl) ⟨388061, by rfl⟩ : syracuseStep 517415 = 776123) B776123
theorem B517455 : Blo 515797 517455 := bstep (se 1 (by rfl) ⟨388091, by rfl⟩ : syracuseStep 517455 = 776183) B776183
theorem B1992023 : Blo 515797 1992023 := bstep (se 1 (by rfl) ⟨1494017, by rfl⟩ : syracuseStep 1992023 = 2988035) B2988035
theorem B517471 : Blo 515797 517471 := bstep (se 1 (by rfl) ⟨388103, by rfl⟩ : syracuseStep 517471 = 776207) B776207
theorem B779615 : Blo 515797 779615 := bstep (se 1 (by rfl) ⟨584711, by rfl⟩ : syracuseStep 779615 = 1169423) B1169423
theorem B746857 : Blo 515797 746857 := bstep (se 2 (by rfl) ⟨280071, by rfl⟩ : syracuseStep 746857 = 560143) B560143
theorem B779627 : Blo 515797 779627 := bstep (se 1 (by rfl) ⟨584720, by rfl⟩ : syracuseStep 779627 = 1169441) B1169441
theorem B517499 : Blo 515797 517499 := bstep (se 1 (by rfl) ⟨388124, by rfl⟩ : syracuseStep 517499 = 776249) B776249
theorem B3925421 : Blo 515797 3925421 := bstep (se 3 (by rfl) ⟨736016, by rfl⟩ : syracuseStep 3925421 = 1472033) B1472033
theorem B517551 : Blo 515797 517551 := bstep (se 1 (by rfl) ⟨388163, by rfl⟩ : syracuseStep 517551 = 776327) B776327
theorem B583087 : Blo 515797 583087 := bstep (se 1 (by rfl) ⟨437315, by rfl⟩ : syracuseStep 583087 = 874631) B874631
theorem B517575 : Blo 515797 517575 := bstep (se 1 (by rfl) ⟨388181, by rfl⟩ : syracuseStep 517575 = 776363) B776363
theorem B517595 : Blo 515797 517595 := bstep (se 1 (by rfl) ⟨388196, by rfl⟩ : syracuseStep 517595 = 776393) B776393
theorem B517671 : Blo 515797 517671 := bstep (se 1 (by rfl) ⟨388253, by rfl⟩ : syracuseStep 517671 = 776507) B776507
theorem B517711 : Blo 515797 517711 := bstep (se 1 (by rfl) ⟨388283, by rfl⟩ : syracuseStep 517711 = 776567) B776567
theorem B517727 : Blo 515797 517727 := bstep (se 1 (by rfl) ⟨388295, by rfl⟩ : syracuseStep 517727 = 776591) B776591
theorem B517755 : Blo 515797 517755 := bstep (se 1 (by rfl) ⟨388316, by rfl⟩ : syracuseStep 517755 = 776633) B776633
theorem B517807 : Blo 515797 517807 := bstep (se 1 (by rfl) ⟨388355, by rfl⟩ : syracuseStep 517807 = 776711) B776711
theorem B517831 : Blo 515797 517831 := bstep (se 1 (by rfl) ⟨388373, by rfl⟩ : syracuseStep 517831 = 776747) B776747
theorem B517851 : Blo 515797 517851 := bstep (se 1 (by rfl) ⟨388388, by rfl⟩ : syracuseStep 517851 = 776777) B776777
theorem B1959673 : Blo 515797 1959673 := bstep (se 2 (by rfl) ⟨734877, by rfl⟩ : syracuseStep 1959673 = 1469755) B1469755
theorem B517927 : Blo 515797 517927 := bstep (se 1 (by rfl) ⟨388445, by rfl⟩ : syracuseStep 517927 = 776891) B776891
theorem B517967 : Blo 515797 517967 := bstep (se 1 (by rfl) ⟨388475, by rfl⟩ : syracuseStep 517967 = 776951) B776951
theorem B517983 : Blo 515797 517983 := bstep (se 1 (by rfl) ⟨388487, by rfl⟩ : syracuseStep 517983 = 776975) B776975
theorem B583519 : Blo 515797 583519 := bstep (se 1 (by rfl) ⟨437639, by rfl⟩ : syracuseStep 583519 = 875279) B875279
theorem B4188023 : Blo 515797 4188023 := bstep (se 1 (by rfl) ⟨3141017, by rfl⟩ : syracuseStep 4188023 = 6282035) B6282035
theorem B518011 : Blo 515797 518011 := bstep (se 1 (by rfl) ⟨388508, by rfl⟩ : syracuseStep 518011 = 777017) B777017
theorem B518063 : Blo 515797 518063 := bstep (se 1 (by rfl) ⟨388547, by rfl⟩ : syracuseStep 518063 = 777095) B777095
theorem B518087 : Blo 515797 518087 := bstep (se 1 (by rfl) ⟨388565, by rfl⟩ : syracuseStep 518087 = 777131) B777131
theorem B518107 : Blo 515797 518107 := bstep (se 1 (by rfl) ⟨388580, by rfl⟩ : syracuseStep 518107 = 777161) B777161
theorem B518183 : Blo 515797 518183 := bstep (se 1 (by rfl) ⟨388637, by rfl⟩ : syracuseStep 518183 = 777275) B777275
theorem B518223 : Blo 515797 518223 := bstep (se 1 (by rfl) ⟨388667, by rfl⟩ : syracuseStep 518223 = 777335) B777335
theorem B518239 : Blo 515797 518239 := bstep (se 1 (by rfl) ⟨388679, by rfl⟩ : syracuseStep 518239 = 777359) B777359
theorem B518267 : Blo 515797 518267 := bstep (se 1 (by rfl) ⟨388700, by rfl⟩ : syracuseStep 518267 = 777401) B777401
theorem B11954309 : Blo 515797 11954309 := bstep (se 4 (by rfl) ⟨1120716, by rfl⟩ : syracuseStep 11954309 = 2241433) B2241433
theorem B518319 : Blo 515797 518319 := bstep (se 1 (by rfl) ⟨388739, by rfl⟩ : syracuseStep 518319 = 777479) B777479
theorem B518343 : Blo 515797 518343 := bstep (se 1 (by rfl) ⟨388757, by rfl⟩ : syracuseStep 518343 = 777515) B777515
theorem B583879 : Blo 515797 583879 := bstep (se 1 (by rfl) ⟨437909, by rfl⟩ : syracuseStep 583879 = 875819) B875819
theorem B518363 : Blo 515797 518363 := bstep (se 1 (by rfl) ⟨388772, by rfl⟩ : syracuseStep 518363 = 777545) B777545
theorem B518439 : Blo 515797 518439 := bstep (se 1 (by rfl) ⟨388829, by rfl⟩ : syracuseStep 518439 = 777659) B777659
theorem B518479 : Blo 515797 518479 := bstep (se 1 (by rfl) ⟨388859, by rfl⟩ : syracuseStep 518479 = 777719) B777719
theorem B518495 : Blo 515797 518495 := bstep (se 1 (by rfl) ⟨388871, by rfl⟩ : syracuseStep 518495 = 777743) B777743
theorem B2943337 : Blo 515797 2943337 := bstep (se 2 (by rfl) ⟨1103751, by rfl⟩ : syracuseStep 2943337 = 2207503) B2207503
theorem B518523 : Blo 515797 518523 := bstep (se 1 (by rfl) ⟨388892, by rfl⟩ : syracuseStep 518523 = 777785) B777785
theorem B518575 : Blo 515797 518575 := bstep (se 1 (by rfl) ⟨388931, by rfl⟩ : syracuseStep 518575 = 777863) B777863
theorem B518599 : Blo 515797 518599 := bstep (se 1 (by rfl) ⟨388949, by rfl⟩ : syracuseStep 518599 = 777899) B777899
theorem B518619 : Blo 515797 518619 := bstep (se 1 (by rfl) ⟨388964, by rfl⟩ : syracuseStep 518619 = 777929) B777929
theorem B518695 : Blo 515797 518695 := bstep (se 1 (by rfl) ⟨389021, by rfl⟩ : syracuseStep 518695 = 778043) B778043
theorem B518735 : Blo 515797 518735 := bstep (se 1 (by rfl) ⟨389051, by rfl⟩ : syracuseStep 518735 = 778103) B778103
theorem B518751 : Blo 515797 518751 := bstep (se 1 (by rfl) ⟨389063, by rfl⟩ : syracuseStep 518751 = 778127) B778127
theorem B518779 : Blo 515797 518779 := bstep (se 1 (by rfl) ⟨389084, by rfl⟩ : syracuseStep 518779 = 778169) B778169
theorem B518831 : Blo 515797 518831 := bstep (se 1 (by rfl) ⟨389123, by rfl⟩ : syracuseStep 518831 = 778247) B778247
theorem B1469117 : Blo 515797 1469117 := bstep (se 3 (by rfl) ⟨275459, by rfl⟩ : syracuseStep 1469117 = 550919) B550919
theorem B518855 : Blo 515797 518855 := bstep (se 1 (by rfl) ⟨389141, by rfl⟩ : syracuseStep 518855 = 778283) B778283
theorem B518875 : Blo 515797 518875 := bstep (se 1 (by rfl) ⟨389156, by rfl⟩ : syracuseStep 518875 = 778313) B778313
theorem B2648861 : Blo 515797 2648861 := bstep (se 3 (by rfl) ⟨496661, by rfl⟩ : syracuseStep 2648861 = 993323) B993323
theorem B518951 : Blo 515797 518951 := bstep (se 1 (by rfl) ⟨389213, by rfl⟩ : syracuseStep 518951 = 778427) B778427
theorem B2616137 : Blo 515797 2616137 := bstep (se 2 (by rfl) ⟨981051, by rfl⟩ : syracuseStep 2616137 = 1962103) B1962103
theorem B518991 : Blo 515797 518991 := bstep (se 1 (by rfl) ⟨389243, by rfl⟩ : syracuseStep 518991 = 778487) B778487
theorem B519007 : Blo 515797 519007 := bstep (se 1 (by rfl) ⟨389255, by rfl⟩ : syracuseStep 519007 = 778511) B778511
theorem B519035 : Blo 515797 519035 := bstep (se 1 (by rfl) ⟨389276, by rfl⟩ : syracuseStep 519035 = 778553) B778553
theorem B519087 : Blo 515797 519087 := bstep (se 1 (by rfl) ⟨389315, by rfl⟩ : syracuseStep 519087 = 778631) B778631
theorem B519111 : Blo 515797 519111 := bstep (se 1 (by rfl) ⟨389333, by rfl⟩ : syracuseStep 519111 = 778667) B778667
theorem B519131 : Blo 515797 519131 := bstep (se 1 (by rfl) ⟨389348, by rfl⟩ : syracuseStep 519131 = 778697) B778697
theorem B519207 : Blo 515797 519207 := bstep (se 1 (by rfl) ⟨389405, by rfl⟩ : syracuseStep 519207 = 778811) B778811
theorem B584743 : Blo 515797 584743 := bstep (se 1 (by rfl) ⟨438557, by rfl⟩ : syracuseStep 584743 = 877115) B877115
theorem B1305679 : Blo 515797 1305679 := bstep (se 1 (by rfl) ⟨979259, by rfl⟩ : syracuseStep 1305679 = 1958519) B1958519
theorem B519247 : Blo 515797 519247 := bstep (se 1 (by rfl) ⟨389435, by rfl⟩ : syracuseStep 519247 = 778871) B778871
theorem B519263 : Blo 515797 519263 := bstep (se 1 (by rfl) ⟨389447, by rfl⟩ : syracuseStep 519263 = 778895) B778895
theorem B519291 : Blo 515797 519291 := bstep (se 1 (by rfl) ⟨389468, by rfl⟩ : syracuseStep 519291 = 778937) B778937
theorem B1961117 : Blo 515797 1961117 := bstep (se 3 (by rfl) ⟨367709, by rfl⟩ : syracuseStep 1961117 = 735419) B735419
theorem B1961131 : Blo 515797 1961131 := bstep (se 1 (by rfl) ⟨1470848, by rfl⟩ : syracuseStep 1961131 = 2941697) B2941697
theorem B519343 : Blo 515797 519343 := bstep (se 1 (by rfl) ⟨389507, by rfl⟩ : syracuseStep 519343 = 779015) B779015
theorem B519367 : Blo 515797 519367 := bstep (se 1 (by rfl) ⟨389525, by rfl⟩ : syracuseStep 519367 = 779051) B779051
theorem B519387 : Blo 515797 519387 := bstep (se 1 (by rfl) ⟨389540, by rfl⟩ : syracuseStep 519387 = 779081) B779081
theorem B6319397 : Blo 515797 6319397 := bstep (se 4 (by rfl) ⟨592443, by rfl⟩ : syracuseStep 6319397 = 1184887) B1184887
theorem B519463 : Blo 515797 519463 := bstep (se 1 (by rfl) ⟨389597, by rfl⟩ : syracuseStep 519463 = 779195) B779195
theorem B519503 : Blo 515797 519503 := bstep (se 1 (by rfl) ⟨389627, by rfl⟩ : syracuseStep 519503 = 779255) B779255
theorem B519519 : Blo 515797 519519 := bstep (se 1 (by rfl) ⟨389639, by rfl⟩ : syracuseStep 519519 = 779279) B779279
theorem B1764713 : Blo 515797 1764713 := bstep (se 2 (by rfl) ⟨661767, by rfl⟩ : syracuseStep 1764713 = 1323535) B1323535
theorem B1469801 : Blo 515797 1469801 := bstep (se 2 (by rfl) ⟨551175, by rfl⟩ : syracuseStep 1469801 = 1102351) B1102351
theorem B519547 : Blo 515797 519547 := bstep (se 1 (by rfl) ⟨389660, by rfl⟩ : syracuseStep 519547 = 779321) B779321
theorem B519599 : Blo 515797 519599 := bstep (se 1 (by rfl) ⟨389699, by rfl⟩ : syracuseStep 519599 = 779399) B779399
theorem B519623 : Blo 515797 519623 := bstep (se 1 (by rfl) ⟨389717, by rfl⟩ : syracuseStep 519623 = 779435) B779435
theorem B1961435 : Blo 515797 1961435 := bstep (se 1 (by rfl) ⟨1471076, by rfl⟩ : syracuseStep 1961435 = 2942153) B2942153
theorem B519643 : Blo 515797 519643 := bstep (se 1 (by rfl) ⟨389732, by rfl⟩ : syracuseStep 519643 = 779465) B779465
theorem B3730931 : Blo 515797 3730931 := bstep (se 1 (by rfl) ⟨2798198, by rfl⟩ : syracuseStep 3730931 = 5596397) B5596397
theorem B519719 : Blo 515797 519719 := bstep (se 1 (by rfl) ⟨389789, by rfl⟩ : syracuseStep 519719 = 779579) B779579
theorem B519759 : Blo 515797 519759 := bstep (se 1 (by rfl) ⟨389819, by rfl⟩ : syracuseStep 519759 = 779639) B779639
theorem B519775 : Blo 515797 519775 := bstep (se 1 (by rfl) ⟨389831, by rfl⟩ : syracuseStep 519775 = 779663) B779663
theorem B1306327 : Blo 515797 1306327 := bstep (se 1 (by rfl) ⟨979745, by rfl⟩ : syracuseStep 1306327 = 1959491) B1959491
theorem B3731159 : Blo 515797 3731159 := bstep (se 1 (by rfl) ⟨2798369, by rfl⟩ : syracuseStep 3731159 = 5596739) B5596739
theorem B4976417 : Blo 515797 4976417 := bstep (se 2 (by rfl) ⟨1866156, by rfl⟩ : syracuseStep 4976417 = 3732313) B3732313
theorem B3927851 : Blo 515797 3927851 := bstep (se 1 (by rfl) ⟨2945888, by rfl⟩ : syracuseStep 3927851 = 5891777) B5891777
theorem B1470383 : Blo 515797 1470383 := bstep (se 1 (by rfl) ⟨1102787, by rfl⟩ : syracuseStep 1470383 = 2205575) B2205575
theorem B7172027 : Blo 515797 7172027 := bstep (se 1 (by rfl) ⟨5379020, by rfl⟩ : syracuseStep 7172027 = 10758041) B10758041
theorem B2486209 : Blo 515797 2486209 := bstep (se 2 (by rfl) ⟨932328, by rfl⟩ : syracuseStep 2486209 = 1864657) B1864657
theorem B1306631 : Blo 515797 1306631 := bstep (se 1 (by rfl) ⟨979973, by rfl⟩ : syracuseStep 1306631 = 1959947) B1959947
theorem B13463567 : Blo 515797 13463567 := bstep (se 1 (by rfl) ⟨10097675, by rfl⟩ : syracuseStep 13463567 = 20195351) B20195351
theorem B2617433 : Blo 515797 2617433 := bstep (se 2 (by rfl) ⟨981537, by rfl⟩ : syracuseStep 2617433 = 1963075) B1963075
theorem B979465 : Blo 515797 979465 := bstep (se 2 (by rfl) ⟨367299, by rfl⟩ : syracuseStep 979465 = 734599) B734599
theorem B1766137 : Blo 515797 1766137 := bstep (se 2 (by rfl) ⟨662301, by rfl⟩ : syracuseStep 1766137 = 1324603) B1324603
theorem B1471567 : Blo 515797 1471567 := bstep (se 1 (by rfl) ⟨1103675, by rfl⟩ : syracuseStep 1471567 = 2207351) B2207351
theorem B16840037 : Blo 515797 16840037 := bstep (se 4 (by rfl) ⟨1578753, by rfl⟩ : syracuseStep 16840037 = 3157507) B3157507
theorem B980399 : Blo 515797 980399 := bstep (se 1 (by rfl) ⟨735299, by rfl⟩ : syracuseStep 980399 = 1470599) B1470599
theorem B6616565 : Blo 515797 6616565 := bstep (se 5 (by rfl) ⟨310151, by rfl⟩ : syracuseStep 6616565 = 620303) B620303
theorem B2094625 : Blo 515797 2094625 := bstep (se 2 (by rfl) ⟨785484, by rfl⟩ : syracuseStep 2094625 = 1570969) B1570969
theorem B980923 : Blo 515797 980923 := bstep (se 1 (by rfl) ⟨735692, by rfl⟩ : syracuseStep 980923 = 1471385) B1471385
theorem B653275 : Blo 515797 653275 := bstep (se 1 (by rfl) ⟨489956, by rfl⟩ : syracuseStep 653275 = 979913) B979913
theorem B1964033 : Blo 515797 1964033 := bstep (se 2 (by rfl) ⟨736512, by rfl⟩ : syracuseStep 1964033 = 1473025) B1473025
theorem B1964047 : Blo 515797 1964047 := bstep (se 1 (by rfl) ⟨1473035, by rfl⟩ : syracuseStep 1964047 = 2946071) B2946071
theorem B8976541 : Blo 515797 8976541 := bstep (se 3 (by rfl) ⟨1683101, by rfl⟩ : syracuseStep 8976541 = 3366203) B3366203
theorem B1308919 : Blo 515797 1308919 := bstep (se 1 (by rfl) ⟨981689, by rfl⟩ : syracuseStep 1308919 = 1963379) B1963379
theorem B981409 : Blo 515797 981409 := bstep (se 2 (by rfl) ⟨368028, by rfl⟩ : syracuseStep 981409 = 736057) B736057
theorem B1309193 : Blo 515797 1309193 := bstep (se 2 (by rfl) ⟨490947, by rfl⟩ : syracuseStep 1309193 = 981895) B981895
theorem B1309223 : Blo 515797 1309223 := bstep (se 1 (by rfl) ⟨981917, by rfl⟩ : syracuseStep 1309223 = 1963835) B1963835
theorem B1309547 : Blo 515797 1309547 := bstep (se 1 (by rfl) ⟨982160, by rfl⟩ : syracuseStep 1309547 = 1964321) B1964321
theorem B5307281 : Blo 515797 5307281 := bstep (se 2 (by rfl) ⟨1990230, by rfl⟩ : syracuseStep 5307281 = 3980461) B3980461
theorem B1965323 : Blo 515797 1965323 := bstep (se 1 (by rfl) ⟨1473992, by rfl⟩ : syracuseStep 1965323 = 2947985) B2947985
theorem B1310195 : Blo 515797 1310195 := bstep (se 1 (by rfl) ⟨982646, by rfl⟩ : syracuseStep 1310195 = 1965293) B1965293
theorem B4423207 : Blo 515797 4423207 := bstep (se 1 (by rfl) ⟨3317405, by rfl⟩ : syracuseStep 4423207 = 6634811) B6634811
theorem B622279 : Blo 515797 622279 := bstep (se 1 (by rfl) ⟨466709, by rfl⟩ : syracuseStep 622279 = 933419) B933419
theorem B1965779 : Blo 515797 1965779 := bstep (se 1 (by rfl) ⟨1474334, by rfl⟩ : syracuseStep 1965779 = 2948669) B2948669
theorem B1310651 : Blo 515797 1310651 := bstep (se 1 (by rfl) ⟨982988, by rfl⟩ : syracuseStep 1310651 = 1965977) B1965977
theorem B45547541 : Blo 515797 45547541 := bstep (se 6 (by rfl) ⟨1067520, by rfl⟩ : syracuseStep 45547541 = 2135041) B2135041
theorem B1867801 : Blo 515797 1867801 := bstep (se 2 (by rfl) ⟨700425, by rfl⟩ : syracuseStep 1867801 = 1400851) B1400851
theorem B9470189 : Blo 515797 9470189 := bstep (se 3 (by rfl) ⟨1775660, by rfl⟩ : syracuseStep 9470189 = 3551321) B3551321
theorem B1311187 : Blo 515797 1311187 := bstep (se 1 (by rfl) ⟨983390, by rfl⟩ : syracuseStep 1311187 = 1966781) B1966781
theorem B655867 : Blo 515797 655867 := bstep (se 1 (by rfl) ⟨491900, by rfl⟩ : syracuseStep 655867 = 983801) B983801
theorem B32440933 : Blo 515797 32440933 := bstep (se 4 (by rfl) ⟨3041337, by rfl⟩ : syracuseStep 32440933 = 6082675) B6082675
theorem B1049195 : Blo 515797 1049195 := bstep (se 1 (by rfl) ⟨786896, by rfl⟩ : syracuseStep 1049195 = 1573793) B1573793
theorem B656095 : Blo 515797 656095 := bstep (se 1 (by rfl) ⟨492071, by rfl⟩ : syracuseStep 656095 = 984143) B984143
theorem B12780281 : Blo 515797 12780281 := bstep (se 2 (by rfl) ⟨4792605, by rfl⟩ : syracuseStep 12780281 = 9585211) B9585211
theorem B5899067 : Blo 515797 5899067 := bstep (se 1 (by rfl) ⟨4424300, by rfl⟩ : syracuseStep 5899067 = 8848601) B8848601
theorem B4424543 : Blo 515797 4424543 := bstep (se 1 (by rfl) ⟨3318407, by rfl⟩ : syracuseStep 4424543 = 6636815) B6636815
theorem B2622455 : Blo 515797 2622455 := bstep (se 1 (by rfl) ⟨1966841, by rfl⟩ : syracuseStep 2622455 = 3933683) B3933683
theorem B1311977 : Blo 515797 1311977 := bstep (se 2 (by rfl) ⟨491991, by rfl⟩ : syracuseStep 1311977 = 983983) B983983
theorem B1312139 : Blo 515797 1312139 := bstep (se 1 (by rfl) ⟨984104, by rfl⟩ : syracuseStep 1312139 = 1968209) B1968209
theorem B656839 : Blo 515797 656839 := bstep (se 1 (by rfl) ⟨492629, by rfl⟩ : syracuseStep 656839 = 985259) B985259
theorem B624071 : Blo 515797 624071 := bstep (se 1 (by rfl) ⟨468053, by rfl⟩ : syracuseStep 624071 = 936107) B936107
theorem B787961 : Blo 515797 787961 := bstep (se 2 (by rfl) ⟨295485, by rfl⟩ : syracuseStep 787961 = 590971) B590971
theorem B984811 : Blo 515797 984811 := bstep (se 1 (by rfl) ⟨738608, by rfl⟩ : syracuseStep 984811 = 1477217) B1477217
theorem B1476407 : Blo 515797 1476407 := bstep (se 1 (by rfl) ⟨1107305, by rfl⟩ : syracuseStep 1476407 = 2214611) B2214611
theorem B1313131 : Blo 515797 1313131 := bstep (se 1 (by rfl) ⟨984848, by rfl⟩ : syracuseStep 1313131 = 1969697) B1969697
theorem B2099623 : Blo 515797 2099623 := bstep (se 1 (by rfl) ⟨1574717, by rfl⟩ : syracuseStep 2099623 = 3149435) B3149435
theorem B1247815 : Blo 515797 1247815 := bstep (se 1 (by rfl) ⟨935861, by rfl⟩ : syracuseStep 1247815 = 1871723) B1871723
theorem B1313455 : Blo 515797 1313455 := bstep (se 1 (by rfl) ⟨985091, by rfl⟩ : syracuseStep 1313455 = 1970183) B1970183
theorem B985783 : Blo 515797 985783 := bstep (se 1 (by rfl) ⟨739337, by rfl⟩ : syracuseStep 985783 = 1478675) B1478675
theorem B2624399 : Blo 515797 2624399 := bstep (se 1 (by rfl) ⟨1968299, by rfl⟩ : syracuseStep 2624399 = 3936599) B3936599
theorem B1477547 : Blo 515797 1477547 := bstep (se 1 (by rfl) ⟨1108160, by rfl⟩ : syracuseStep 1477547 = 2216321) B2216321
theorem B986087 : Blo 515797 986087 := bstep (se 1 (by rfl) ⟨739565, by rfl⟩ : syracuseStep 986087 = 1479131) B1479131
theorem B1313779 : Blo 515797 1313779 := bstep (se 1 (by rfl) ⟨985334, by rfl⟩ : syracuseStep 1313779 = 1970669) B1970669
theorem B12586049 : Blo 515797 12586049 := bstep (se 2 (by rfl) ⟨4719768, by rfl⟩ : syracuseStep 12586049 = 9439537) B9439537
theorem B1182863 : Blo 515797 1182863 := bstep (se 1 (by rfl) ⟨887147, by rfl⟩ : syracuseStep 1182863 = 1774295) B1774295
theorem B1707227 : Blo 515797 1707227 := bstep (se 1 (by rfl) ⟨1280420, by rfl⟩ : syracuseStep 1707227 = 2560841) B2560841
theorem B1150331 : Blo 515797 1150331 := bstep (se 1 (by rfl) ⟨862748, by rfl⟩ : syracuseStep 1150331 = 1725497) B1725497
theorem B7441793 : Blo 515797 7441793 := bstep (se 2 (by rfl) ⟨2790672, by rfl⟩ : syracuseStep 7441793 = 5581345) B5581345
theorem B5311873 : Blo 515797 5311873 := bstep (se 2 (by rfl) ⟨1991952, by rfl⟩ : syracuseStep 5311873 = 3983905) B3983905
theorem B22744709 : Blo 515797 22744709 := bstep (se 4 (by rfl) ⟨2132316, by rfl⟩ : syracuseStep 22744709 = 4264633) B4264633
theorem B1314539 : Blo 515797 1314539 := bstep (se 1 (by rfl) ⟨985904, by rfl⟩ : syracuseStep 1314539 = 1971809) B1971809
theorem B1052471 : Blo 515797 1052471 := bstep (se 1 (by rfl) ⟨789353, by rfl⟩ : syracuseStep 1052471 = 1578707) B1578707
theorem B790327 : Blo 515797 790327 := bstep (se 1 (by rfl) ⟨592745, by rfl⟩ : syracuseStep 790327 = 1185491) B1185491
theorem B1740905 : Blo 515797 1740905 := bstep (se 2 (by rfl) ⟨652839, by rfl⟩ : syracuseStep 1740905 = 1305679) B1305679
theorem B11309219 : Blo 515797 11309219 := bstep (se 1 (by rfl) ⟨8481914, by rfl⟩ : syracuseStep 11309219 = 16963829) B16963829
theorem B7442603 : Blo 515797 7442603 := bstep (se 1 (by rfl) ⟨5581952, by rfl⟩ : syracuseStep 7442603 = 11163905) B11163905
theorem B2363755 : Blo 515797 2363755 := bstep (se 1 (by rfl) ⟨1772816, by rfl⟩ : syracuseStep 2363755 = 3545633) B3545633
theorem B1315399 : Blo 515797 1315399 := bstep (se 1 (by rfl) ⟨986549, by rfl⟩ : syracuseStep 1315399 = 1973099) B1973099
theorem B1184431 : Blo 515797 1184431 := bstep (se 1 (by rfl) ⟨888323, by rfl⟩ : syracuseStep 1184431 = 1776647) B1776647
theorem B1315511 : Blo 515797 1315511 := bstep (se 1 (by rfl) ⟨986633, by rfl⟩ : syracuseStep 1315511 = 1973267) B1973267
theorem B1741769 : Blo 515797 1741769 := bstep (se 2 (by rfl) ⟨653163, by rfl⟩ : syracuseStep 1741769 = 1306327) B1306327
theorem B2626505 : Blo 515797 2626505 := bstep (se 2 (by rfl) ⟨984939, by rfl⟩ : syracuseStep 2626505 = 1969879) B1969879
theorem B13407437 : Blo 515797 13407437 := bstep (se 3 (by rfl) ⟨2513894, by rfl⟩ : syracuseStep 13407437 = 5027789) B5027789
theorem B1742039 : Blo 515797 1742039 := bstep (se 1 (by rfl) ⟨1306529, by rfl⟩ : syracuseStep 1742039 = 2613059) B2613059
theorem B3314945 : Blo 515797 3314945 := bstep (se 2 (by rfl) ⟨1243104, by rfl⟩ : syracuseStep 3314945 = 2486209) B2486209
theorem B2496187 : Blo 515797 2496187 := bstep (se 1 (by rfl) ⟨1872140, by rfl⟩ : syracuseStep 2496187 = 3744281) B3744281
theorem B2660125 : Blo 515797 2660125 := bstep (se 3 (by rfl) ⟨498773, by rfl⟩ : syracuseStep 2660125 = 997547) B997547
theorem B2792015 : Blo 515797 2792015 := bstep (se 1 (by rfl) ⟨2094011, by rfl⟩ : syracuseStep 2792015 = 4188023) B4188023
theorem B5610545 : Blo 515797 5610545 := bstep (se 2 (by rfl) ⟨2103954, by rfl⟩ : syracuseStep 5610545 = 4207909) B4207909
theorem B1744091 : Blo 515797 1744091 := bstep (se 1 (by rfl) ⟨1308068, by rfl⟩ : syracuseStep 1744091 = 2616137) B2616137
theorem B662815 : Blo 515797 662815 := bstep (se 1 (by rfl) ⟨497111, by rfl⟩ : syracuseStep 662815 = 994223) B994223
theorem B3940001 : Blo 515797 3940001 := bstep (se 2 (by rfl) ⟨1477500, by rfl⟩ : syracuseStep 3940001 = 2955001) B2955001
theorem B57614141 : Blo 515797 57614141 := bstep (se 3 (by rfl) ⟨10802651, by rfl⟩ : syracuseStep 57614141 = 21605303) B21605303
theorem B3317611 : Blo 515797 3317611 := bstep (se 1 (by rfl) ⟨2488208, by rfl⟩ : syracuseStep 3317611 = 4976417) B4976417
theorem B28712981 : Blo 515797 28712981 := bstep (se 6 (by rfl) ⟨672960, by rfl⟩ : syracuseStep 28712981 = 1345921) B1345921
theorem B1744955 : Blo 515797 1744955 := bstep (se 1 (by rfl) ⟨1308716, by rfl⟩ : syracuseStep 1744955 = 2617433) B2617433
theorem B11968721 : Blo 515797 11968721 := bstep (se 2 (by rfl) ⟨4488270, by rfl⟩ : syracuseStep 11968721 = 8976541) B8976541
theorem B1745225 : Blo 515797 1745225 := bstep (se 2 (by rfl) ⟨654459, by rfl⟩ : syracuseStep 1745225 = 1308919) B1308919
theorem B2630393 : Blo 515797 2630393 := bstep (se 2 (by rfl) ⟨986397, by rfl⟩ : syracuseStep 2630393 = 1972795) B1972795
theorem B16851725 : Blo 515797 16851725 := bstep (se 3 (by rfl) ⟨3159698, by rfl⟩ : syracuseStep 16851725 = 6319397) B6319397
theorem B2204617 : Blo 515797 2204617 := bstep (se 2 (by rfl) ⟨826731, by rfl⟩ : syracuseStep 2204617 = 1653463) B1653463
theorem B3351851 : Blo 515797 3351851 := bstep (se 1 (by rfl) ⟨2513888, by rfl⟩ : syracuseStep 3351851 = 5027777) B5027777
theorem B3941945 : Blo 515797 3941945 := bstep (se 2 (by rfl) ⟨1478229, by rfl⟩ : syracuseStep 3941945 = 2956459) B2956459
theorem B3745921 : Blo 515797 3745921 := bstep (se 2 (by rfl) ⟨1404720, by rfl⟩ : syracuseStep 3745921 = 2809441) B2809441
theorem B829705 : Blo 515797 829705 := bstep (se 2 (by rfl) ⟨311139, by rfl⟩ : syracuseStep 829705 = 622279) B622279
theorem B1748411 : Blo 515797 1748411 := bstep (se 1 (by rfl) ⟨1311308, by rfl⟩ : syracuseStep 1748411 = 2622617) B2622617
theorem B2797139 : Blo 515797 2797139 := bstep (se 1 (by rfl) ⟨2097854, by rfl⟩ : syracuseStep 2797139 = 4195709) B4195709
theorem B5910731 : Blo 515797 5910731 := bstep (se 1 (by rfl) ⟨4433048, by rfl⟩ : syracuseStep 5910731 = 8866097) B8866097
theorem B71840033 : Blo 515797 71840033 := bstep (se 2 (by rfl) ⟨26940012, by rfl⟩ : syracuseStep 71840033 = 53880025) B53880025
theorem B4436329 : Blo 515797 4436329 := bstep (se 2 (by rfl) ⟨1663623, by rfl⟩ : syracuseStep 4436329 = 3327247) B3327247
theorem B995809 : Blo 515797 995809 := bstep (se 2 (by rfl) ⟨373428, by rfl⟩ : syracuseStep 995809 = 746857) B746857
theorem B4437287 : Blo 515797 4437287 := bstep (se 1 (by rfl) ⟨3327965, by rfl⟩ : syracuseStep 4437287 = 6655931) B6655931
theorem B3945833 : Blo 515797 3945833 := bstep (se 2 (by rfl) ⟨1479687, by rfl⟩ : syracuseStep 3945833 = 2959375) B2959375
theorem B1160585 : Blo 515797 1160585 := bstep (se 2 (by rfl) ⟨435219, by rfl⟩ : syracuseStep 1160585 = 870439) B870439
theorem B1160711 : Blo 515797 1160711 := bstep (se 1 (by rfl) ⟨870533, by rfl⟩ : syracuseStep 1160711 = 1741067) B1741067
theorem B4208165 : Blo 515797 4208165 := bstep (se 4 (by rfl) ⟨394515, by rfl⟩ : syracuseStep 4208165 = 789031) B789031
theorem B1160891 : Blo 515797 1160891 := bstep (se 1 (by rfl) ⟨870668, by rfl⟩ : syracuseStep 1160891 = 1741337) B1741337
theorem B3192605 : Blo 515797 3192605 := bstep (se 3 (by rfl) ⟨598613, by rfl⟩ : syracuseStep 3192605 = 1197227) B1197227
theorem B1161017 : Blo 515797 1161017 := bstep (se 2 (by rfl) ⟨435381, by rfl⟩ : syracuseStep 1161017 = 870763) B870763
theorem B4732759 : Blo 515797 4732759 := bstep (se 1 (by rfl) ⟨3549569, by rfl⟩ : syracuseStep 4732759 = 7099139) B7099139
theorem B1161647 : Blo 515797 1161647 := bstep (se 1 (by rfl) ⟨871235, by rfl⟩ : syracuseStep 1161647 = 1742471) B1742471
theorem B1161683 : Blo 515797 1161683 := bstep (se 1 (by rfl) ⟨871262, by rfl⟩ : syracuseStep 1161683 = 1742525) B1742525
theorem B1161791 : Blo 515797 1161791 := bstep (se 1 (by rfl) ⟨871343, by rfl⟩ : syracuseStep 1161791 = 1742687) B1742687
theorem B1161899 : Blo 515797 1161899 := bstep (se 1 (by rfl) ⟨871424, by rfl⟩ : syracuseStep 1161899 = 1742849) B1742849
theorem B1162439 : Blo 515797 1162439 := bstep (se 1 (by rfl) ⟨871829, by rfl⟩ : syracuseStep 1162439 = 1743659) B1743659
theorem B1326431 : Blo 515797 1326431 := bstep (se 1 (by rfl) ⟨994823, by rfl⟩ : syracuseStep 1326431 = 1989647) B1989647
theorem B1162619 : Blo 515797 1162619 := bstep (se 1 (by rfl) ⟨871964, by rfl⟩ : syracuseStep 1162619 = 1743929) B1743929
theorem B1162745 : Blo 515797 1162745 := bstep (se 2 (by rfl) ⟨436029, by rfl⟩ : syracuseStep 1162745 = 872059) B872059
theorem B1752569 : Blo 515797 1752569 := bstep (se 2 (by rfl) ⟨657213, by rfl⟩ : syracuseStep 1752569 = 1314427) B1314427
theorem B1162835 : Blo 515797 1162835 := bstep (se 1 (by rfl) ⟨872126, by rfl⟩ : syracuseStep 1162835 = 1744253) B1744253
theorem B4407047 : Blo 515797 4407047 := bstep (se 1 (by rfl) ⟨3305285, by rfl⟩ : syracuseStep 4407047 = 6610571) B6610571
theorem B1163015 : Blo 515797 1163015 := bstep (se 1 (by rfl) ⟨872261, by rfl⟩ : syracuseStep 1163015 = 1744523) B1744523
theorem B1752839 : Blo 515797 1752839 := bstep (se 1 (by rfl) ⟨1314629, by rfl⟩ : syracuseStep 1752839 = 2629259) B2629259
theorem B1752893 : Blo 515797 1752893 := bstep (se 3 (by rfl) ⟨328667, by rfl⟩ : syracuseStep 1752893 = 657335) B657335
theorem B2212049 : Blo 515797 2212049 := bstep (se 2 (by rfl) ⟨829518, by rfl⟩ : syracuseStep 2212049 = 1659037) B1659037
theorem B1163627 : Blo 515797 1163627 := bstep (se 1 (by rfl) ⟨872720, by rfl⟩ : syracuseStep 1163627 = 1745441) B1745441
theorem B1163771 : Blo 515797 1163771 := bstep (se 1 (by rfl) ⟨872828, by rfl⟩ : syracuseStep 1163771 = 1745657) B1745657
theorem B934463 : Blo 515797 934463 := bstep (se 1 (by rfl) ⟨700847, by rfl⟩ : syracuseStep 934463 = 1401695) B1401695
theorem B1163897 : Blo 515797 1163897 := bstep (se 2 (by rfl) ⟨436461, by rfl⟩ : syracuseStep 1163897 = 872923) B872923
theorem B3326609 : Blo 515797 3326609 := bstep (se 2 (by rfl) ⟨1247478, by rfl⟩ : syracuseStep 3326609 = 2494957) B2494957
theorem B1163951 : Blo 515797 1163951 := bstep (se 1 (by rfl) ⟨872963, by rfl⟩ : syracuseStep 1163951 = 1745927) B1745927
theorem B441762497 : Blo 515797 441762497 := bstep (se 2 (by rfl) ⟨165660936, by rfl⟩ : syracuseStep 441762497 = 331321873) B331321873
theorem B1164023 : Blo 515797 1164023 := bstep (se 1 (by rfl) ⟨873017, by rfl⟩ : syracuseStep 1164023 = 1746035) B1746035
theorem B1328015 : Blo 515797 1328015 := bstep (se 1 (by rfl) ⟨996011, by rfl⟩ : syracuseStep 1328015 = 1992023) B1992023
theorem B1164203 : Blo 515797 1164203 := bstep (se 1 (by rfl) ⟨873152, by rfl⟩ : syracuseStep 1164203 = 1746305) B1746305
theorem B1164743 : Blo 515797 1164743 := bstep (se 1 (by rfl) ⟨873557, by rfl⟩ : syracuseStep 1164743 = 1747115) B1747115
theorem B1165103 : Blo 515797 1165103 := bstep (se 1 (by rfl) ⟨873827, by rfl⟩ : syracuseStep 1165103 = 1747655) B1747655
theorem B3917645 : Blo 515797 3917645 := bstep (se 3 (by rfl) ⟨734558, by rfl⟩ : syracuseStep 3917645 = 1469117) B1469117
theorem B1165679 : Blo 515797 1165679 := bstep (se 1 (by rfl) ⟨874259, by rfl⟩ : syracuseStep 1165679 = 1748519) B1748519
theorem B1165751 : Blo 515797 1165751 := bstep (se 1 (by rfl) ⟨874313, by rfl⟩ : syracuseStep 1165751 = 1748627) B1748627
theorem B1165895 : Blo 515797 1165895 := bstep (se 1 (by rfl) ⟨874421, by rfl⟩ : syracuseStep 1165895 = 1748843) B1748843
theorem B1165931 : Blo 515797 1165931 := bstep (se 1 (by rfl) ⟨874448, by rfl⟩ : syracuseStep 1165931 = 1748897) B1748897
theorem B871033 : Blo 515797 871033 := bstep (se 2 (by rfl) ⟨326637, by rfl⟩ : syracuseStep 871033 = 653275) B653275
theorem B871087 : Blo 515797 871087 := bstep (se 1 (by rfl) ⟨653315, by rfl⟩ : syracuseStep 871087 = 1306631) B1306631
theorem B2214647 : Blo 515797 2214647 := bstep (se 1 (by rfl) ⟨1660985, by rfl⟩ : syracuseStep 2214647 = 3321971) B3321971
theorem B1166327 : Blo 515797 1166327 := bstep (se 1 (by rfl) ⟨874745, by rfl⟩ : syracuseStep 1166327 = 1749491) B1749491
theorem B1166687 : Blo 515797 1166687 := bstep (se 1 (by rfl) ⟨875015, by rfl⟩ : syracuseStep 1166687 = 1750031) B1750031
theorem B11226691 : Blo 515797 11226691 := bstep (se 1 (by rfl) ⟨8420018, by rfl⟩ : syracuseStep 11226691 = 16840037) B16840037
theorem B4411043 : Blo 515797 4411043 := bstep (se 1 (by rfl) ⟨3308282, by rfl⟩ : syracuseStep 4411043 = 6616565) B6616565
theorem B773867 : Blo 515797 773867 := bstep (se 1 (by rfl) ⟨580400, by rfl⟩ : syracuseStep 773867 = 1160801) B1160801
theorem B1167083 : Blo 515797 1167083 := bstep (se 1 (by rfl) ⟨875312, by rfl⟩ : syracuseStep 1167083 = 1750625) B1750625
theorem B1167209 : Blo 515797 1167209 := bstep (se 2 (by rfl) ⟨437703, by rfl⟩ : syracuseStep 1167209 = 875407) B875407
theorem B774095 : Blo 515797 774095 := bstep (se 1 (by rfl) ⟨580571, by rfl⟩ : syracuseStep 774095 = 1161143) B1161143
theorem B3920075 : Blo 515797 3920075 := bstep (se 1 (by rfl) ⟨2940056, by rfl⟩ : syracuseStep 3920075 = 5880113) B5880113
theorem B774491 : Blo 515797 774491 := bstep (se 1 (by rfl) ⟨580868, by rfl⟩ : syracuseStep 774491 = 1161737) B1161737
theorem B872795 : Blo 515797 872795 := bstep (se 1 (by rfl) ⟨654596, by rfl⟩ : syracuseStep 872795 = 1309193) B1309193
theorem B872815 : Blo 515797 872815 := bstep (se 1 (by rfl) ⟨654611, by rfl⟩ : syracuseStep 872815 = 1309223) B1309223
theorem B774719 : Blo 515797 774719 := bstep (se 1 (by rfl) ⟨581039, by rfl⟩ : syracuseStep 774719 = 1162079) B1162079
theorem B873031 : Blo 515797 873031 := bstep (se 1 (by rfl) ⟨654773, by rfl⟩ : syracuseStep 873031 = 1309547) B1309547
theorem B774839 : Blo 515797 774839 := bstep (se 1 (by rfl) ⟨581129, by rfl⟩ : syracuseStep 774839 = 1162259) B1162259
theorem B1168055 : Blo 515797 1168055 := bstep (se 1 (by rfl) ⟨876041, by rfl⟩ : syracuseStep 1168055 = 1752083) B1752083
theorem B1168271 : Blo 515797 1168271 := bstep (se 1 (by rfl) ⟨876203, by rfl⟩ : syracuseStep 1168271 = 1752407) B1752407
theorem B775067 : Blo 515797 775067 := bstep (se 1 (by rfl) ⟨581300, by rfl⟩ : syracuseStep 775067 = 1162601) B1162601
theorem B873463 : Blo 515797 873463 := bstep (se 1 (by rfl) ⟨655097, by rfl⟩ : syracuseStep 873463 = 1310195) B1310195
theorem B775463 : Blo 515797 775463 := bstep (se 1 (by rfl) ⟨581597, by rfl⟩ : syracuseStep 775463 = 1163195) B1163195
theorem B873767 : Blo 515797 873767 := bstep (se 1 (by rfl) ⟨655325, by rfl⟩ : syracuseStep 873767 = 1310651) B1310651
theorem B775547 : Blo 515797 775547 := bstep (se 1 (by rfl) ⟨581660, by rfl⟩ : syracuseStep 775547 = 1163321) B1163321
theorem B1103291 : Blo 515797 1103291 := bstep (se 1 (by rfl) ⟨827468, by rfl⟩ : syracuseStep 1103291 = 1654937) B1654937
theorem B775673 : Blo 515797 775673 := bstep (se 2 (by rfl) ⟨290877, by rfl⟩ : syracuseStep 775673 = 581755) B581755
theorem B775775 : Blo 515797 775775 := bstep (se 1 (by rfl) ⟨581831, by rfl⟩ : syracuseStep 775775 = 1163663) B1163663
theorem B1168991 : Blo 515797 1168991 := bstep (se 1 (by rfl) ⟨876743, by rfl⟩ : syracuseStep 1168991 = 1753487) B1753487
theorem B2479751 : Blo 515797 2479751 := bstep (se 1 (by rfl) ⟨1859813, by rfl⟩ : syracuseStep 2479751 = 3719627) B3719627
theorem B874219 : Blo 515797 874219 := bstep (se 1 (by rfl) ⟨655664, by rfl⟩ : syracuseStep 874219 = 1311329) B1311329
theorem B775991 : Blo 515797 775991 := bstep (se 1 (by rfl) ⟨581993, by rfl⟩ : syracuseStep 775991 = 1163987) B1163987
theorem B1169207 : Blo 515797 1169207 := bstep (se 1 (by rfl) ⟨876905, by rfl⟩ : syracuseStep 1169207 = 1753811) B1753811
theorem B1103881 : Blo 515797 1103881 := bstep (se 2 (by rfl) ⟨413955, by rfl⟩ : syracuseStep 1103881 = 827911) B827911
theorem B2218063 : Blo 515797 2218063 := bstep (se 1 (by rfl) ⟨1663547, by rfl⟩ : syracuseStep 2218063 = 3327095) B3327095
theorem B776297 : Blo 515797 776297 := bstep (se 2 (by rfl) ⟨291111, by rfl⟩ : syracuseStep 776297 = 582223) B582223
theorem B1169513 : Blo 515797 1169513 := bstep (se 2 (by rfl) ⟨438567, by rfl⟩ : syracuseStep 1169513 = 877135) B877135
theorem B776615 : Blo 515797 776615 := bstep (se 1 (by rfl) ⟨582461, by rfl⟩ : syracuseStep 776615 = 1164923) B1164923
theorem B776699 : Blo 515797 776699 := bstep (se 1 (by rfl) ⟨582524, by rfl⟩ : syracuseStep 776699 = 1165049) B1165049
theorem B3922505 : Blo 515797 3922505 := bstep (se 2 (by rfl) ⟨1470939, by rfl⟩ : syracuseStep 3922505 = 2941879) B2941879
theorem B776825 : Blo 515797 776825 := bstep (se 2 (by rfl) ⟨291309, by rfl⟩ : syracuseStep 776825 = 582619) B582619
theorem B776879 : Blo 515797 776879 := bstep (se 1 (by rfl) ⟨582659, by rfl⟩ : syracuseStep 776879 = 1165319) B1165319
theorem B875191 : Blo 515797 875191 := bstep (se 1 (by rfl) ⟨656393, by rfl⟩ : syracuseStep 875191 = 1312787) B1312787
theorem B776927 : Blo 515797 776927 := bstep (se 1 (by rfl) ⟨582695, by rfl⟩ : syracuseStep 776927 = 1165391) B1165391
theorem B2612087 : Blo 515797 2612087 := bstep (se 1 (by rfl) ⟨1959065, by rfl⟩ : syracuseStep 2612087 = 3918131) B3918131
theorem B777191 : Blo 515797 777191 := bstep (se 1 (by rfl) ⟨582893, by rfl⟩ : syracuseStep 777191 = 1165787) B1165787
theorem B875495 : Blo 515797 875495 := bstep (se 1 (by rfl) ⟨656621, by rfl⟩ : syracuseStep 875495 = 1313243) B1313243
theorem B777449 : Blo 515797 777449 := bstep (se 2 (by rfl) ⟨291543, by rfl⟩ : syracuseStep 777449 = 583087) B583087
theorem B777503 : Blo 515797 777503 := bstep (se 1 (by rfl) ⟨583127, by rfl⟩ : syracuseStep 777503 = 1166255) B1166255
theorem B777671 : Blo 515797 777671 := bstep (se 1 (by rfl) ⟨583253, by rfl⟩ : syracuseStep 777671 = 1166507) B1166507
theorem B581215 : Blo 515797 581215 := bstep (se 1 (by rfl) ⟨435911, by rfl⟩ : syracuseStep 581215 = 871823) B871823
theorem B2612897 : Blo 515797 2612897 := bstep (se 2 (by rfl) ⟨979836, by rfl⟩ : syracuseStep 2612897 = 1959673) B1959673
theorem B515807 : Blo 515797 515807 := bstep (se 1 (by rfl) ⟨386855, by rfl⟩ : syracuseStep 515807 = 773711) B773711
theorem B778025 : Blo 515797 778025 := bstep (se 2 (by rfl) ⟨291759, by rfl⟩ : syracuseStep 778025 = 583519) B583519
theorem B515887 : Blo 515797 515887 := bstep (se 1 (by rfl) ⟨386915, by rfl⟩ : syracuseStep 515887 = 773831) B773831
theorem B778031 : Blo 515797 778031 := bstep (se 1 (by rfl) ⟨583523, by rfl⟩ : syracuseStep 778031 = 1167047) B1167047
theorem B515995 : Blo 515797 515995 := bstep (se 1 (by rfl) ⟨386996, by rfl⟩ : syracuseStep 515995 = 773993) B773993
theorem B516047 : Blo 515797 516047 := bstep (se 1 (by rfl) ⟨387035, by rfl⟩ : syracuseStep 516047 = 774071) B774071
theorem B516071 : Blo 515797 516071 := bstep (se 1 (by rfl) ⟨387053, by rfl⟩ : syracuseStep 516071 = 774107) B774107
theorem B2940947 : Blo 515797 2940947 := bstep (se 1 (by rfl) ⟨2205710, by rfl⟩ : syracuseStep 2940947 = 4411421) B4411421
theorem B876649 : Blo 515797 876649 := bstep (se 2 (by rfl) ⟨328743, by rfl⟩ : syracuseStep 876649 = 657487) B657487
theorem B7561349 : Blo 515797 7561349 := bstep (se 4 (by rfl) ⟨708876, by rfl⟩ : syracuseStep 7561349 = 1417753) B1417753
theorem B778505 : Blo 515797 778505 := bstep (se 2 (by rfl) ⟨291939, by rfl⟩ : syracuseStep 778505 = 583879) B583879
theorem B516383 : Blo 515797 516383 := bstep (se 1 (by rfl) ⟨387287, by rfl⟩ : syracuseStep 516383 = 774575) B774575
theorem B4415795 : Blo 515797 4415795 := bstep (se 1 (by rfl) ⟨3311846, by rfl⟩ : syracuseStep 4415795 = 6623693) B6623693
theorem B516443 : Blo 515797 516443 := bstep (se 1 (by rfl) ⟨387332, by rfl⟩ : syracuseStep 516443 = 774665) B774665
theorem B516463 : Blo 515797 516463 := bstep (se 1 (by rfl) ⟨387347, by rfl⟩ : syracuseStep 516463 = 774695) B774695
theorem B778607 : Blo 515797 778607 := bstep (se 1 (by rfl) ⟨583955, by rfl⟩ : syracuseStep 778607 = 1167911) B1167911
theorem B516519 : Blo 515797 516519 := bstep (se 1 (by rfl) ⟨387389, by rfl⟩ : syracuseStep 516519 = 774779) B774779
theorem B3924449 : Blo 515797 3924449 := bstep (se 2 (by rfl) ⟨1471668, by rfl⟩ : syracuseStep 3924449 = 2943337) B2943337
theorem B516603 : Blo 515797 516603 := bstep (se 1 (by rfl) ⟨387452, by rfl⟩ : syracuseStep 516603 = 774905) B774905
theorem B516671 : Blo 515797 516671 := bstep (se 1 (by rfl) ⟨387503, by rfl⟩ : syracuseStep 516671 = 775007) B775007
theorem B516679 : Blo 515797 516679 := bstep (se 1 (by rfl) ⟨387509, by rfl⟩ : syracuseStep 516679 = 775019) B775019
theorem B778823 : Blo 515797 778823 := bstep (se 1 (by rfl) ⟨584117, by rfl⟩ : syracuseStep 778823 = 1168235) B1168235
theorem B778859 : Blo 515797 778859 := bstep (se 1 (by rfl) ⟨584144, by rfl⟩ : syracuseStep 778859 = 1168289) B1168289
theorem B1106615 : Blo 515797 1106615 := bstep (se 1 (by rfl) ⟨829961, by rfl⟩ : syracuseStep 1106615 = 1659923) B1659923
theorem B516831 : Blo 515797 516831 := bstep (se 1 (by rfl) ⟨387623, by rfl⟩ : syracuseStep 516831 = 775247) B775247
theorem B582367 : Blo 515797 582367 := bstep (se 1 (by rfl) ⟨436775, by rfl⟩ : syracuseStep 582367 = 873551) B873551
theorem B516911 : Blo 515797 516911 := bstep (se 1 (by rfl) ⟨387683, by rfl⟩ : syracuseStep 516911 = 775367) B775367
theorem B779087 : Blo 515797 779087 := bstep (se 1 (by rfl) ⟨584315, by rfl⟩ : syracuseStep 779087 = 1168631) B1168631
theorem B517019 : Blo 515797 517019 := bstep (se 1 (by rfl) ⟨387764, by rfl⟩ : syracuseStep 517019 = 775529) B775529
theorem B517071 : Blo 515797 517071 := bstep (se 1 (by rfl) ⟨387803, by rfl⟩ : syracuseStep 517071 = 775607) B775607
theorem B517095 : Blo 515797 517095 := bstep (se 1 (by rfl) ⟨387821, by rfl⟩ : syracuseStep 517095 = 775643) B775643
theorem B1107067 : Blo 515797 1107067 := bstep (se 1 (by rfl) ⟨830300, by rfl⟩ : syracuseStep 1107067 = 1660601) B1660601
theorem B779483 : Blo 515797 779483 := bstep (se 1 (by rfl) ⟨584612, by rfl⟩ : syracuseStep 779483 = 1169225) B1169225
theorem B7693555 : Blo 515797 7693555 := bstep (se 1 (by rfl) ⟨5770166, by rfl⟩ : syracuseStep 7693555 = 11540333) B11540333
theorem B517407 : Blo 515797 517407 := bstep (se 1 (by rfl) ⟨388055, by rfl⟩ : syracuseStep 517407 = 776111) B776111
theorem B582943 : Blo 515797 582943 := bstep (se 1 (by rfl) ⟨437207, by rfl⟩ : syracuseStep 582943 = 874415) B874415
theorem B517467 : Blo 515797 517467 := bstep (se 1 (by rfl) ⟨388100, by rfl⟩ : syracuseStep 517467 = 776201) B776201
theorem B517487 : Blo 515797 517487 := bstep (se 1 (by rfl) ⟨388115, by rfl⟩ : syracuseStep 517487 = 776231) B776231
theorem B779657 : Blo 515797 779657 := bstep (se 2 (by rfl) ⟨292371, by rfl⟩ : syracuseStep 779657 = 584743) B584743
theorem B517543 : Blo 515797 517543 := bstep (se 1 (by rfl) ⟨388157, by rfl⟩ : syracuseStep 517543 = 776315) B776315
theorem B517627 : Blo 515797 517627 := bstep (se 1 (by rfl) ⟨388220, by rfl⟩ : syracuseStep 517627 = 776441) B776441
theorem B2614841 : Blo 515797 2614841 := bstep (se 2 (by rfl) ⟨980565, by rfl⟩ : syracuseStep 2614841 = 1961131) B1961131
theorem B517695 : Blo 515797 517695 := bstep (se 1 (by rfl) ⟨388271, by rfl⟩ : syracuseStep 517695 = 776543) B776543
theorem B583231 : Blo 515797 583231 := bstep (se 1 (by rfl) ⟨437423, by rfl⟩ : syracuseStep 583231 = 874847) B874847
theorem B517703 : Blo 515797 517703 := bstep (se 1 (by rfl) ⟨388277, by rfl⟩ : syracuseStep 517703 = 776555) B776555
theorem B517855 : Blo 515797 517855 := bstep (se 1 (by rfl) ⟨388391, by rfl⟩ : syracuseStep 517855 = 776783) B776783
theorem B6383393 : Blo 515797 6383393 := bstep (se 2 (by rfl) ⟨2393772, by rfl⟩ : syracuseStep 6383393 = 4787545) B4787545
theorem B517935 : Blo 515797 517935 := bstep (se 1 (by rfl) ⟨388451, by rfl⟩ : syracuseStep 517935 = 776903) B776903
theorem B33613643 : Blo 515797 33613643 := bstep (se 1 (by rfl) ⟨25210232, by rfl⟩ : syracuseStep 33613643 = 50420465) B50420465
theorem B2844497 : Blo 515797 2844497 := bstep (se 2 (by rfl) ⟨1066686, by rfl⟩ : syracuseStep 2844497 = 2133373) B2133373
theorem B3925907 : Blo 515797 3925907 := bstep (se 1 (by rfl) ⟨2944430, by rfl⟩ : syracuseStep 3925907 = 5888861) B5888861
theorem B518043 : Blo 515797 518043 := bstep (se 1 (by rfl) ⟨388532, by rfl⟩ : syracuseStep 518043 = 777065) B777065
theorem B518095 : Blo 515797 518095 := bstep (se 1 (by rfl) ⟨388571, by rfl⟩ : syracuseStep 518095 = 777143) B777143
theorem B518119 : Blo 515797 518119 := bstep (se 1 (by rfl) ⟨388589, by rfl⟩ : syracuseStep 518119 = 777179) B777179
theorem B8415485 : Blo 515797 8415485 := bstep (se 3 (by rfl) ⟨1577903, by rfl⟩ : syracuseStep 8415485 = 3155807) B3155807
theorem B518431 : Blo 515797 518431 := bstep (se 1 (by rfl) ⟨388823, by rfl⟩ : syracuseStep 518431 = 777647) B777647
theorem B518491 : Blo 515797 518491 := bstep (se 1 (by rfl) ⟨388868, by rfl⟩ : syracuseStep 518491 = 777737) B777737
theorem B1108331 : Blo 515797 1108331 := bstep (se 1 (by rfl) ⟨831248, by rfl⟩ : syracuseStep 1108331 = 1662497) B1662497
theorem B1239407 : Blo 515797 1239407 := bstep (se 1 (by rfl) ⟨929555, by rfl⟩ : syracuseStep 1239407 = 1859111) B1859111
theorem B518511 : Blo 515797 518511 := bstep (se 1 (by rfl) ⟨388883, by rfl⟩ : syracuseStep 518511 = 777767) B777767
theorem B551291 : Blo 515797 551291 := bstep (se 1 (by rfl) ⟨413468, by rfl⟩ : syracuseStep 551291 = 826937) B826937
theorem B584059 : Blo 515797 584059 := bstep (se 1 (by rfl) ⟨438044, by rfl⟩ : syracuseStep 584059 = 876089) B876089
theorem B518567 : Blo 515797 518567 := bstep (se 1 (by rfl) ⟨388925, by rfl⟩ : syracuseStep 518567 = 777851) B777851
theorem B1108399 : Blo 515797 1108399 := bstep (se 1 (by rfl) ⟨831299, by rfl⟩ : syracuseStep 1108399 = 1662599) B1662599
theorem B944635 : Blo 515797 944635 := bstep (se 1 (by rfl) ⟨708476, by rfl⟩ : syracuseStep 944635 = 1416953) B1416953
theorem B518651 : Blo 515797 518651 := bstep (se 1 (by rfl) ⟨388988, by rfl⟩ : syracuseStep 518651 = 777977) B777977
theorem B518719 : Blo 515797 518719 := bstep (se 1 (by rfl) ⟨389039, by rfl⟩ : syracuseStep 518719 = 778079) B778079
theorem B518727 : Blo 515797 518727 := bstep (se 1 (by rfl) ⟨389045, by rfl⟩ : syracuseStep 518727 = 778091) B778091
theorem B10644047 : Blo 515797 10644047 := bstep (se 1 (by rfl) ⟨7983035, by rfl⟩ : syracuseStep 10644047 = 15966071) B15966071
theorem B2943611 : Blo 515797 2943611 := bstep (se 1 (by rfl) ⟨2207708, by rfl⟩ : syracuseStep 2943611 = 4415417) B4415417
theorem B518879 : Blo 515797 518879 := bstep (se 1 (by rfl) ⟨389159, by rfl⟩ : syracuseStep 518879 = 778319) B778319
theorem B1239799 : Blo 515797 1239799 := bstep (se 1 (by rfl) ⟨929849, by rfl⟩ : syracuseStep 1239799 = 1859699) B1859699
theorem B518959 : Blo 515797 518959 := bstep (se 1 (by rfl) ⟨389219, by rfl⟩ : syracuseStep 518959 = 778439) B778439
theorem B4188995 : Blo 515797 4188995 := bstep (se 1 (by rfl) ⟨3141746, by rfl⟩ : syracuseStep 4188995 = 6283493) B6283493
theorem B584527 : Blo 515797 584527 := bstep (se 1 (by rfl) ⟨438395, by rfl⟩ : syracuseStep 584527 = 876791) B876791
theorem B519067 : Blo 515797 519067 := bstep (se 1 (by rfl) ⟨389300, by rfl⟩ : syracuseStep 519067 = 778601) B778601
theorem B519119 : Blo 515797 519119 := bstep (se 1 (by rfl) ⟨389339, by rfl⟩ : syracuseStep 519119 = 778679) B778679
theorem B167668697 : Blo 515797 167668697 := bstep (se 2 (by rfl) ⟨62875761, by rfl⟩ : syracuseStep 167668697 = 125751523) B125751523
theorem B519143 : Blo 515797 519143 := bstep (se 1 (by rfl) ⟨389357, by rfl⟩ : syracuseStep 519143 = 778715) B778715
theorem B31878157 : Blo 515797 31878157 := bstep (se 3 (by rfl) ⟨5977154, by rfl⟩ : syracuseStep 31878157 = 11954309) B11954309
theorem B5303335 : Blo 515797 5303335 := bstep (se 1 (by rfl) ⟨3977501, by rfl⟩ : syracuseStep 5303335 = 7955003) B7955003
theorem B1404029 : Blo 515797 1404029 := bstep (se 3 (by rfl) ⟨263255, by rfl⟩ : syracuseStep 1404029 = 526511) B526511
theorem B10644767 : Blo 515797 10644767 := bstep (se 1 (by rfl) ⟨7983575, by rfl⟩ : syracuseStep 10644767 = 15967151) B15967151
theorem B519455 : Blo 515797 519455 := bstep (se 1 (by rfl) ⟨389591, by rfl⟩ : syracuseStep 519455 = 779183) B779183
theorem B519515 : Blo 515797 519515 := bstep (se 1 (by rfl) ⟨389636, by rfl⟩ : syracuseStep 519515 = 779273) B779273
theorem B1305953 : Blo 515797 1305953 := bstep (se 2 (by rfl) ⟨489732, by rfl⟩ : syracuseStep 1305953 = 979465) B979465
theorem B519535 : Blo 515797 519535 := bstep (se 1 (by rfl) ⟨389651, by rfl⟩ : syracuseStep 519535 = 779303) B779303
theorem B519591 : Blo 515797 519591 := bstep (se 1 (by rfl) ⟨389693, by rfl⟩ : syracuseStep 519591 = 779387) B779387
theorem B519675 : Blo 515797 519675 := bstep (se 1 (by rfl) ⟨389756, by rfl⟩ : syracuseStep 519675 = 779513) B779513
theorem B519743 : Blo 515797 519743 := bstep (se 1 (by rfl) ⟨389807, by rfl⟩ : syracuseStep 519743 = 779615) B779615
theorem B519751 : Blo 515797 519751 := bstep (se 1 (by rfl) ⟨389813, by rfl⟩ : syracuseStep 519751 = 779627) B779627
theorem B2616947 : Blo 515797 2616947 := bstep (se 1 (by rfl) ⟨1962710, by rfl⟩ : syracuseStep 2616947 = 3925421) B3925421
theorem B2354849 : Blo 515797 2354849 := bstep (se 2 (by rfl) ⟨883068, by rfl⟩ : syracuseStep 2354849 = 1766137) B1766137
theorem B1109801 : Blo 515797 1109801 := bstep (se 2 (by rfl) ⟨416175, by rfl⟩ : syracuseStep 1109801 = 832351) B832351
theorem B1962089 : Blo 515797 1962089 := bstep (se 2 (by rfl) ⟨735783, by rfl⟩ : syracuseStep 1962089 = 1471567) B1471567
theorem B5304649 : Blo 515797 5304649 := bstep (se 2 (by rfl) ⟨1989243, by rfl⟩ : syracuseStep 5304649 = 3978487) B3978487
theorem B1765907 : Blo 515797 1765907 := bstep (se 1 (by rfl) ⟨1324430, by rfl⟩ : syracuseStep 1765907 = 2648861) B2648861
theorem B1307411 : Blo 515797 1307411 := bstep (se 1 (by rfl) ⟨980558, by rfl⟩ : syracuseStep 1307411 = 1961117) B1961117
theorem B553807 : Blo 515797 553807 := bstep (se 1 (by rfl) ⟨415355, by rfl⟩ : syracuseStep 553807 = 830711) B830711
theorem B1176475 : Blo 515797 1176475 := bstep (se 1 (by rfl) ⟨882356, by rfl⟩ : syracuseStep 1176475 = 1764713) B1764713
theorem B979867 : Blo 515797 979867 := bstep (se 1 (by rfl) ⟨734900, by rfl⟩ : syracuseStep 979867 = 1469801) B1469801
theorem B10777519 : Blo 515797 10777519 := bstep (se 1 (by rfl) ⟨8083139, by rfl⟩ : syracuseStep 10777519 = 16166279) B16166279
theorem B1307623 : Blo 515797 1307623 := bstep (se 1 (by rfl) ⟨980717, by rfl⟩ : syracuseStep 1307623 = 1961435) B1961435
theorem B2487287 : Blo 515797 2487287 := bstep (se 1 (by rfl) ⟨1865465, by rfl⟩ : syracuseStep 2487287 = 3730931) B3730931
theorem B2487439 : Blo 515797 2487439 := bstep (se 1 (by rfl) ⟨1865579, by rfl⟩ : syracuseStep 2487439 = 3731159) B3731159
theorem B2618567 : Blo 515797 2618567 := bstep (se 1 (by rfl) ⟨1963925, by rfl⟩ : syracuseStep 2618567 = 3927851) B3927851
theorem B1864919 : Blo 515797 1864919 := bstep (se 1 (by rfl) ⟨1398689, by rfl⟩ : syracuseStep 1864919 = 2797379) B2797379
theorem B2847959 : Blo 515797 2847959 := bstep (se 1 (by rfl) ⟨2135969, by rfl⟩ : syracuseStep 2847959 = 4271939) B4271939
theorem B980201 : Blo 515797 980201 := bstep (se 2 (by rfl) ⟨367575, by rfl⟩ : syracuseStep 980201 = 735151) B735151
theorem B1996019 : Blo 515797 1996019 := bstep (se 1 (by rfl) ⟨1497014, by rfl⟩ : syracuseStep 1996019 = 2994029) B2994029
theorem B1307897 : Blo 515797 1307897 := bstep (se 2 (by rfl) ⟨490461, by rfl⟩ : syracuseStep 1307897 = 980923) B980923
theorem B980255 : Blo 515797 980255 := bstep (se 1 (by rfl) ⟨735191, by rfl⟩ : syracuseStep 980255 = 1470383) B1470383
theorem B1471783 : Blo 515797 1471783 := bstep (se 1 (by rfl) ⟨1103837, by rfl⟩ : syracuseStep 1471783 = 2207675) B2207675
theorem B4781351 : Blo 515797 4781351 := bstep (se 1 (by rfl) ⟨3586013, by rfl⟩ : syracuseStep 4781351 = 7172027) B7172027
theorem B8975711 : Blo 515797 8975711 := bstep (se 1 (by rfl) ⟨6731783, by rfl⟩ : syracuseStep 8975711 = 13463567) B13463567
theorem B2618729 : Blo 515797 2618729 := bstep (se 2 (by rfl) ⟨982023, by rfl⟩ : syracuseStep 2618729 = 1964047) B1964047
theorem B11171333 : Blo 515797 11171333 := bstep (se 4 (by rfl) ⟨1047312, by rfl⟩ : syracuseStep 11171333 = 2094625) B2094625
theorem B1472057 : Blo 515797 1472057 := bstep (se 2 (by rfl) ⟨552021, by rfl⟩ : syracuseStep 1472057 = 1104043) B1104043
theorem B1308545 : Blo 515797 1308545 := bstep (se 2 (by rfl) ⟨490704, by rfl⟩ : syracuseStep 1308545 = 981409) B981409
theorem B653599 : Blo 515797 653599 := bstep (se 1 (by rfl) ⟨490199, by rfl⟩ : syracuseStep 653599 = 980399) B980399
theorem B5306953 : Blo 515797 5306953 := bstep (se 2 (by rfl) ⟨1990107, by rfl⟩ : syracuseStep 5306953 = 3980215) B3980215
theorem B1309355 : Blo 515797 1309355 := bstep (se 1 (by rfl) ⟨982016, by rfl⟩ : syracuseStep 1309355 = 1964033) B1964033
theorem B1473299 : Blo 515797 1473299 := bstep (se 1 (by rfl) ⟨1104974, by rfl⟩ : syracuseStep 1473299 = 2209949) B2209949
theorem B6650909 : Blo 515797 6650909 := bstep (se 3 (by rfl) ⟨1247045, by rfl⟩ : syracuseStep 6650909 = 2494091) B2494091
theorem B3538187 : Blo 515797 3538187 := bstep (se 1 (by rfl) ⟨2653640, by rfl⟩ : syracuseStep 3538187 = 5307281) B5307281
theorem B5897609 : Blo 515797 5897609 := bstep (se 2 (by rfl) ⟨2211603, by rfl⟩ : syracuseStep 5897609 = 4423207) B4423207
theorem B1310215 : Blo 515797 1310215 := bstep (se 1 (by rfl) ⟨982661, by rfl⟩ : syracuseStep 1310215 = 1965323) B1965323
theorem B622255 : Blo 515797 622255 := bstep (se 1 (by rfl) ⟨466691, by rfl⟩ : syracuseStep 622255 = 933383) B933383
theorem B1310519 : Blo 515797 1310519 := bstep (se 1 (by rfl) ⟨982889, by rfl⟩ : syracuseStep 1310519 = 1965779) B1965779
theorem B2490401 : Blo 515797 2490401 := bstep (se 2 (by rfl) ⟨933900, by rfl⟩ : syracuseStep 2490401 = 1867801) B1867801
theorem B1474699 : Blo 515797 1474699 := bstep (se 1 (by rfl) ⟨1106024, by rfl⟩ : syracuseStep 1474699 = 2212049) B2212049
theorem B622975 : Blo 515797 622975 := bstep (se 1 (by rfl) ⟨467231, by rfl⟩ : syracuseStep 622975 = 934463) B934463
theorem B8520187 : Blo 515797 8520187 := bstep (se 1 (by rfl) ⟨6390140, by rfl⟩ : syracuseStep 8520187 = 12780281) B12780281
theorem B3932711 : Blo 515797 3932711 := bstep (se 1 (by rfl) ⟨2949533, by rfl⟩ : syracuseStep 3932711 = 5899067) B5899067
theorem B2949695 : Blo 515797 2949695 := bstep (se 1 (by rfl) ⟨2212271, by rfl⟩ : syracuseStep 2949695 = 4424543) B4424543
theorem B885343 : Blo 515797 885343 := bstep (se 1 (by rfl) ⟨664007, by rfl⟩ : syracuseStep 885343 = 1328015) B1328015
theorem B43254577 : Blo 515797 43254577 := bstep (se 2 (by rfl) ⟨16220466, by rfl⟩ : syracuseStep 43254577 = 32440933) B32440933
theorem B1476089 : Blo 515797 1476089 := bstep (se 2 (by rfl) ⟨553533, by rfl⟩ : syracuseStep 1476089 = 1107067) B1107067
theorem B10258073 : Blo 515797 10258073 := bstep (se 2 (by rfl) ⟨3846777, by rfl⟩ : syracuseStep 10258073 = 7693555) B7693555
theorem B1476431 : Blo 515797 1476431 := bstep (se 1 (by rfl) ⟨1107323, by rfl⟩ : syracuseStep 1476431 = 2214647) B2214647
theorem B985031 : Blo 515797 985031 := bstep (se 1 (by rfl) ⟨738773, by rfl⟩ : syracuseStep 985031 = 1477547) B1477547
theorem B657391 : Blo 515797 657391 := bstep (se 1 (by rfl) ⟨493043, by rfl⟩ : syracuseStep 657391 = 986087) B986087
theorem B8390699 : Blo 515797 8390699 := bstep (se 1 (by rfl) ⟨6293024, by rfl⟩ : syracuseStep 8390699 = 12586049) B12586049
theorem B1313081 : Blo 515797 1313081 := bstep (se 2 (by rfl) ⟨492405, by rfl⟩ : syracuseStep 1313081 = 984811) B984811
theorem B7539479 : Blo 515797 7539479 := bstep (se 1 (by rfl) ⟨5654609, by rfl⟩ : syracuseStep 7539479 = 11309219) B11309219
theorem B1477865 : Blo 515797 1477865 := bstep (se 2 (by rfl) ⟨554199, by rfl⟩ : syracuseStep 1477865 = 1108399) B1108399
theorem B1314377 : Blo 515797 1314377 := bstep (se 2 (by rfl) ⟨492891, by rfl⟩ : syracuseStep 1314377 = 985783) B985783
theorem B2101229 : Blo 515797 2101229 := bstep (se 3 (by rfl) ⟨393980, by rfl⟩ : syracuseStep 2101229 = 787961) B787961
theorem B42504209 : Blo 515797 42504209 := bstep (se 2 (by rfl) ⟨15939078, by rfl⟩ : syracuseStep 42504209 = 31878157) B31878157
theorem B7082497 : Blo 515797 7082497 := bstep (se 2 (by rfl) ⟨2655936, by rfl⟩ : syracuseStep 7082497 = 5311873) B5311873
theorem B1741391 : Blo 515797 1741391 := bstep (se 1 (by rfl) ⟨1306043, by rfl⟩ : syracuseStep 1741391 = 2612087) B2612087
theorem B3740363 : Blo 515797 3740363 := bstep (se 1 (by rfl) ⟨2805272, by rfl⟩ : syracuseStep 3740363 = 5610545) B5610545
theorem B3937085 : Blo 515797 3937085 := bstep (se 3 (by rfl) ⟨738203, by rfl⟩ : syracuseStep 3937085 = 1476407) B1476407
theorem B57480101 : Blo 515797 57480101 := bstep (se 4 (by rfl) ⟨5388759, by rfl⟩ : syracuseStep 57480101 = 10777519) B10777519
theorem B1741931 : Blo 515797 1741931 := bstep (se 1 (by rfl) ⟨1306448, by rfl⟩ : syracuseStep 1741931 = 2612897) B2612897
theorem B2626667 : Blo 515797 2626667 := bstep (se 1 (by rfl) ⟨1970000, by rfl⟩ : syracuseStep 2626667 = 3940001) B3940001
theorem B38409427 : Blo 515797 38409427 := bstep (se 1 (by rfl) ⟨28807070, by rfl⟩ : syracuseStep 38409427 = 57614141) B57614141
theorem B3151673 : Blo 515797 3151673 := bstep (se 2 (by rfl) ⟨1181877, by rfl⟩ : syracuseStep 3151673 = 2363755) B2363755
theorem B2234567 : Blo 515797 2234567 := bstep (se 1 (by rfl) ⟨1675925, by rfl⟩ : syracuseStep 2234567 = 3351851) B3351851
theorem B1579241 : Blo 515797 1579241 := bstep (se 2 (by rfl) ⟨592215, by rfl⟩ : syracuseStep 1579241 = 1184431) B1184431
theorem B1743227 : Blo 515797 1743227 := bstep (se 1 (by rfl) ⟨1307420, by rfl⟩ : syracuseStep 1743227 = 2614841) B2614841
theorem B2627963 : Blo 515797 2627963 := bstep (se 1 (by rfl) ⟨1970972, by rfl⟩ : syracuseStep 2627963 = 3941945) B3941945
theorem B1743497 : Blo 515797 1743497 := bstep (se 2 (by rfl) ⟨653811, by rfl⟩ : syracuseStep 1743497 = 1307623) B1307623
theorem B5610323 : Blo 515797 5610323 := bstep (se 1 (by rfl) ⟨4207742, by rfl⟩ : syracuseStep 5610323 = 8415485) B8415485
theorem B826271 : Blo 515797 826271 := bstep (se 1 (by rfl) ⟨619703, by rfl⟩ : syracuseStep 826271 = 1239407) B1239407
theorem B2792663 : Blo 515797 2792663 := bstep (se 1 (by rfl) ⟨2094497, by rfl⟩ : syracuseStep 2792663 = 4188995) B4188995
theorem B111779131 : Blo 515797 111779131 := bstep (se 1 (by rfl) ⟨83834348, by rfl⟩ : syracuseStep 111779131 = 167668697) B167668697
theorem B3546833 : Blo 515797 3546833 := bstep (se 2 (by rfl) ⟨1330062, by rfl⟩ : syracuseStep 3546833 = 2660125) B2660125
theorem B1744631 : Blo 515797 1744631 := bstep (se 1 (by rfl) ⟨1308473, by rfl⟩ : syracuseStep 1744631 = 2616947) B2616947
theorem B2957417 : Blo 515797 2957417 := bstep (se 2 (by rfl) ⟨1109031, by rfl⟩ : syracuseStep 2957417 = 2218063) B2218063
theorem B3940487 : Blo 515797 3940487 := bstep (se 1 (by rfl) ⟨2955365, by rfl⟩ : syracuseStep 3940487 = 5910731) B5910731
theorem B3154301 : Blo 515797 3154301 := bstep (se 3 (by rfl) ⟨591431, by rfl⟩ : syracuseStep 3154301 = 1182863) B1182863
theorem B1745711 : Blo 515797 1745711 := bstep (se 1 (by rfl) ⟨1309283, by rfl⟩ : syracuseStep 1745711 = 2618567) B2618567
theorem B3187567 : Blo 515797 3187567 := bstep (se 1 (by rfl) ⟨2390675, by rfl⟩ : syracuseStep 3187567 = 4781351) B4781351
theorem B2958191 : Blo 515797 2958191 := bstep (se 1 (by rfl) ⟨2218643, by rfl⟩ : syracuseStep 2958191 = 4437287) B4437287
theorem B1745819 : Blo 515797 1745819 := bstep (se 1 (by rfl) ⟨1309364, by rfl⟩ : syracuseStep 1745819 = 2618729) B2618729
theorem B2630555 : Blo 515797 2630555 := bstep (se 1 (by rfl) ⟨1972916, by rfl⟩ : syracuseStep 2630555 = 3945833) B3945833
theorem B7447555 : Blo 515797 7447555 := bstep (se 1 (by rfl) ⟨5585666, by rfl⟩ : syracuseStep 7447555 = 11171333) B11171333
theorem B1746953 : Blo 515797 1746953 := bstep (se 2 (by rfl) ⟨655107, by rfl⟩ : syracuseStep 1746953 = 1310215) B1310215
theorem B4433939 : Blo 515797 4433939 := bstep (se 1 (by rfl) ⟨3325454, by rfl⟩ : syracuseStep 4433939 = 6650909) B6650909
theorem B829673 : Blo 515797 829673 := bstep (se 2 (by rfl) ⟨311127, by rfl⟩ : syracuseStep 829673 = 622255) B622255
theorem B699463 : Blo 515797 699463 := bstep (se 1 (by rfl) ⟨524597, by rfl⟩ : syracuseStep 699463 = 1049195) B1049195
theorem B1748249 : Blo 515797 1748249 := bstep (se 2 (by rfl) ⟨655593, by rfl⟩ : syracuseStep 1748249 = 1311187) B1311187
theorem B1748303 : Blo 515797 1748303 := bstep (se 1 (by rfl) ⟨1311227, by rfl⟩ : syracuseStep 1748303 = 2622455) B2622455
theorem B1749599 : Blo 515797 1749599 := bstep (se 1 (by rfl) ⟨1312199, by rfl⟩ : syracuseStep 1749599 = 2624399) B2624399
theorem B4961195 : Blo 515797 4961195 := bstep (se 1 (by rfl) ⟨3720896, by rfl⟩ : syracuseStep 4961195 = 7441793) B7441793
theorem B1160603 : Blo 515797 1160603 := bstep (se 1 (by rfl) ⟨870452, by rfl⟩ : syracuseStep 1160603 = 1740905) B1740905
theorem B4961735 : Blo 515797 4961735 := bstep (se 1 (by rfl) ⟨3721301, by rfl⟩ : syracuseStep 4961735 = 7442603) B7442603
theorem B4994561 : Blo 515797 4994561 := bstep (se 2 (by rfl) ⟨1872960, by rfl⟩ : syracuseStep 4994561 = 3745921) B3745921
theorem B1750841 : Blo 515797 1750841 := bstep (se 2 (by rfl) ⟨656565, by rfl⟩ : syracuseStep 1750841 = 1313131) B1313131
theorem B2799497 : Blo 515797 2799497 := bstep (se 2 (by rfl) ⟨1049811, by rfl⟩ : syracuseStep 2799497 = 2099623) B2099623
theorem B1161179 : Blo 515797 1161179 := bstep (se 1 (by rfl) ⟨870884, by rfl⟩ : syracuseStep 1161179 = 1741769) B1741769
theorem B1751003 : Blo 515797 1751003 := bstep (se 1 (by rfl) ⟨1313252, by rfl⟩ : syracuseStep 1751003 = 2626505) B2626505
theorem B1259513 : Blo 515797 1259513 := bstep (se 2 (by rfl) ⟨472317, by rfl⟩ : syracuseStep 1259513 = 944635) B944635
theorem B1161359 : Blo 515797 1161359 := bstep (se 1 (by rfl) ⟨871019, by rfl⟩ : syracuseStep 1161359 = 1742039) B1742039
theorem B1161377 : Blo 515797 1161377 := bstep (se 2 (by rfl) ⟨435516, by rfl⟩ : syracuseStep 1161377 = 871033) B871033
theorem B1161449 : Blo 515797 1161449 := bstep (se 2 (by rfl) ⟨435543, by rfl⟩ : syracuseStep 1161449 = 871087) B871087
theorem B1751273 : Blo 515797 1751273 := bstep (se 2 (by rfl) ⟨656727, by rfl⟩ : syracuseStep 1751273 = 1313455) B1313455
theorem B735527 : Blo 515797 735527 := bstep (se 1 (by rfl) ⟨551645, by rfl⟩ : syracuseStep 735527 = 1103291) B1103291
theorem B1653065 : Blo 515797 1653065 := bstep (se 2 (by rfl) ⟨619899, by rfl⟩ : syracuseStep 1653065 = 1239799) B1239799
theorem B1653167 : Blo 515797 1653167 := bstep (se 1 (by rfl) ⟨1239875, by rfl⟩ : syracuseStep 1653167 = 2479751) B2479751
theorem B12270197 : Blo 515797 12270197 := bstep (se 5 (by rfl) ⟨575165, by rfl⟩ : syracuseStep 12270197 = 1150331) B1150331
theorem B1751705 : Blo 515797 1751705 := bstep (se 2 (by rfl) ⟨656889, by rfl⟩ : syracuseStep 1751705 = 1313779) B1313779
theorem B1162727 : Blo 515797 1162727 := bstep (se 1 (by rfl) ⟨872045, by rfl⟩ : syracuseStep 1162727 = 1744091) B1744091
theorem B1163303 : Blo 515797 1163303 := bstep (se 1 (by rfl) ⟨872477, by rfl⟩ : syracuseStep 1163303 = 1744955) B1744955
theorem B7979147 : Blo 515797 7979147 := bstep (se 1 (by rfl) ⟨5984360, by rfl⟩ : syracuseStep 7979147 = 11968721) B11968721
theorem B1163483 : Blo 515797 1163483 := bstep (se 1 (by rfl) ⟨872612, by rfl⟩ : syracuseStep 1163483 = 1745225) B1745225
theorem B737743 : Blo 515797 737743 := bstep (se 1 (by rfl) ⟨553307, by rfl⟩ : syracuseStep 737743 = 1106615) B1106615
theorem B5915105 : Blo 515797 5915105 := bstep (se 2 (by rfl) ⟨2218164, by rfl⟩ : syracuseStep 5915105 = 4436329) B4436329
theorem B1163753 : Blo 515797 1163753 := bstep (se 2 (by rfl) ⟨436407, by rfl⟩ : syracuseStep 1163753 = 872815) B872815
theorem B1753595 : Blo 515797 1753595 := bstep (se 1 (by rfl) ⟨1315196, by rfl⟩ : syracuseStep 1753595 = 2630393) B2630393
theorem B1327745 : Blo 515797 1327745 := bstep (se 2 (by rfl) ⟨497904, by rfl⟩ : syracuseStep 1327745 = 995809) B995809
theorem B1164041 : Blo 515797 1164041 := bstep (se 2 (by rfl) ⟨436515, by rfl⟩ : syracuseStep 1164041 = 873031) B873031
theorem B1753865 : Blo 515797 1753865 := bstep (se 2 (by rfl) ⟨657699, by rfl⟩ : syracuseStep 1753865 = 1315399) B1315399
theorem B738409 : Blo 515797 738409 := bstep (se 2 (by rfl) ⟨276903, by rfl⟩ : syracuseStep 738409 = 553807) B553807
theorem B1164617 : Blo 515797 1164617 := bstep (se 2 (by rfl) ⟨436731, by rfl⟩ : syracuseStep 1164617 = 873463) B873463
theorem B738887 : Blo 515797 738887 := bstep (se 1 (by rfl) ⟨554165, by rfl⟩ : syracuseStep 738887 = 1108331) B1108331
theorem B7096031 : Blo 515797 7096031 := bstep (se 1 (by rfl) ⟨5322023, by rfl⟩ : syracuseStep 7096031 = 10644047) B10644047
theorem B936019 : Blo 515797 936019 := bstep (se 1 (by rfl) ⟨702014, by rfl⟩ : syracuseStep 936019 = 1404029) B1404029
theorem B7096511 : Blo 515797 7096511 := bstep (se 1 (by rfl) ⟨5322383, by rfl⟩ : syracuseStep 7096511 = 10644767) B10644767
theorem B870635 : Blo 515797 870635 := bstep (se 1 (by rfl) ⟨652976, by rfl⟩ : syracuseStep 870635 = 1305953) B1305953
theorem B3328249 : Blo 515797 3328249 := bstep (se 2 (by rfl) ⟨1248093, by rfl⟩ : syracuseStep 3328249 = 2496187) B2496187
theorem B1165607 : Blo 515797 1165607 := bstep (se 1 (by rfl) ⟨874205, by rfl⟩ : syracuseStep 1165607 = 1748411) B1748411
theorem B1165625 : Blo 515797 1165625 := bstep (se 2 (by rfl) ⟨437109, by rfl⟩ : syracuseStep 1165625 = 874219) B874219
theorem B6310345 : Blo 515797 6310345 := bstep (se 2 (by rfl) ⟨2366379, by rfl⟩ : syracuseStep 6310345 = 4732759) B4732759
theorem B739867 : Blo 515797 739867 := bstep (se 1 (by rfl) ⟨554900, by rfl⟩ : syracuseStep 739867 = 1109801) B1109801
theorem B47893355 : Blo 515797 47893355 := bstep (se 1 (by rfl) ⟨35920016, by rfl⟩ : syracuseStep 47893355 = 71840033) B71840033
theorem B871465 : Blo 515797 871465 := bstep (se 2 (by rfl) ⟨326799, by rfl⟩ : syracuseStep 871465 = 653599) B653599
theorem B871607 : Blo 515797 871607 := bstep (se 1 (by rfl) ⟨653705, by rfl⟩ : syracuseStep 871607 = 1307411) B1307411
theorem B1658191 : Blo 515797 1658191 := bstep (se 1 (by rfl) ⟨1243643, by rfl⟩ : syracuseStep 1658191 = 2487287) B2487287
theorem B1330679 : Blo 515797 1330679 := bstep (se 1 (by rfl) ⟨998009, by rfl⟩ : syracuseStep 1330679 = 1996019) B1996019
theorem B871931 : Blo 515797 871931 := bstep (se 1 (by rfl) ⟨653948, by rfl⟩ : syracuseStep 871931 = 1307897) B1307897
theorem B5983807 : Blo 515797 5983807 := bstep (se 1 (by rfl) ⟨4487855, by rfl⟩ : syracuseStep 5983807 = 8975711) B8975711
theorem B1166921 : Blo 515797 1166921 := bstep (se 2 (by rfl) ⟨437595, by rfl⟩ : syracuseStep 1166921 = 875191) B875191
theorem B773723 : Blo 515797 773723 := bstep (se 1 (by rfl) ⟨580292, by rfl⟩ : syracuseStep 773723 = 1160585) B1160585
theorem B773807 : Blo 515797 773807 := bstep (se 1 (by rfl) ⟨580355, by rfl⟩ : syracuseStep 773807 = 1160711) B1160711
theorem B2805443 : Blo 515797 2805443 := bstep (se 1 (by rfl) ⟨2104082, by rfl⟩ : syracuseStep 2805443 = 4208165) B4208165
theorem B773927 : Blo 515797 773927 := bstep (se 1 (by rfl) ⟨580445, by rfl⟩ : syracuseStep 773927 = 1160891) B1160891
theorem B774011 : Blo 515797 774011 := bstep (se 1 (by rfl) ⟨580508, by rfl⟩ : syracuseStep 774011 = 1161017) B1161017
theorem B872363 : Blo 515797 872363 := bstep (se 1 (by rfl) ⟨654272, by rfl⟩ : syracuseStep 872363 = 1308545) B1308545
theorem B7459037 : Blo 515797 7459037 := bstep (se 3 (by rfl) ⟨1398569, by rfl⟩ : syracuseStep 7459037 = 2797139) B2797139
theorem B774431 : Blo 515797 774431 := bstep (se 1 (by rfl) ⟨580823, by rfl⟩ : syracuseStep 774431 = 1161647) B1161647
theorem B4215077 : Blo 515797 4215077 := bstep (se 4 (by rfl) ⟨395163, by rfl⟩ : syracuseStep 4215077 = 790327) B790327
theorem B774455 : Blo 515797 774455 := bstep (se 1 (by rfl) ⟨580841, by rfl⟩ : syracuseStep 774455 = 1161683) B1161683
theorem B774527 : Blo 515797 774527 := bstep (se 1 (by rfl) ⟨580895, by rfl⟩ : syracuseStep 774527 = 1161791) B1161791
theorem B774599 : Blo 515797 774599 := bstep (se 1 (by rfl) ⟨580949, by rfl⟩ : syracuseStep 774599 = 1161899) B1161899
theorem B872903 : Blo 515797 872903 := bstep (se 1 (by rfl) ⟨654677, by rfl⟩ : syracuseStep 872903 = 1309355) B1309355
theorem B774953 : Blo 515797 774953 := bstep (se 2 (by rfl) ⟨290607, by rfl⟩ : syracuseStep 774953 = 581215) B581215
theorem B774959 : Blo 515797 774959 := bstep (se 1 (by rfl) ⟨581219, by rfl⟩ : syracuseStep 774959 = 1162439) B1162439
theorem B2806589 : Blo 515797 2806589 := bstep (se 3 (by rfl) ⟨526235, by rfl⟩ : syracuseStep 2806589 = 1052471) B1052471
theorem B775079 : Blo 515797 775079 := bstep (se 1 (by rfl) ⟨581309, by rfl⟩ : syracuseStep 775079 = 1162619) B1162619
theorem B775163 : Blo 515797 775163 := bstep (se 1 (by rfl) ⟨581372, by rfl⟩ : syracuseStep 775163 = 1162745) B1162745
theorem B1168379 : Blo 515797 1168379 := bstep (se 1 (by rfl) ⟨876284, by rfl⟩ : syracuseStep 1168379 = 1752569) B1752569
theorem B775223 : Blo 515797 775223 := bstep (se 1 (by rfl) ⟨581417, by rfl⟩ : syracuseStep 775223 = 1162835) B1162835
theorem B2938031 : Blo 515797 2938031 := bstep (se 1 (by rfl) ⟨2203523, by rfl⟩ : syracuseStep 2938031 = 4407047) B4407047
theorem B775343 : Blo 515797 775343 := bstep (se 1 (by rfl) ⟨581507, by rfl⟩ : syracuseStep 775343 = 1163015) B1163015
theorem B1168559 : Blo 515797 1168559 := bstep (se 1 (by rfl) ⟨876419, by rfl⟩ : syracuseStep 1168559 = 1752839) B1752839
theorem B873679 : Blo 515797 873679 := bstep (se 1 (by rfl) ⟨655259, by rfl⟩ : syracuseStep 873679 = 1310519) B1310519
theorem B1168595 : Blo 515797 1168595 := bstep (se 1 (by rfl) ⟨876446, by rfl⟩ : syracuseStep 1168595 = 1752893) B1752893
theorem B30365027 : Blo 515797 30365027 := bstep (se 1 (by rfl) ⟨22773770, by rfl⟩ : syracuseStep 30365027 = 45547541) B45547541
theorem B76567949 : Blo 515797 76567949 := bstep (se 3 (by rfl) ⟨14356490, by rfl⟩ : syracuseStep 76567949 = 28712981) B28712981
theorem B1168865 : Blo 515797 1168865 := bstep (se 2 (by rfl) ⟨438324, by rfl⟩ : syracuseStep 1168865 = 876649) B876649
theorem B6313459 : Blo 515797 6313459 := bstep (se 1 (by rfl) ⟨4735094, by rfl⟩ : syracuseStep 6313459 = 9470189) B9470189
theorem B775751 : Blo 515797 775751 := bstep (se 1 (by rfl) ⟨581813, by rfl⟩ : syracuseStep 775751 = 1163627) B1163627
theorem B775847 : Blo 515797 775847 := bstep (se 1 (by rfl) ⟨581885, by rfl⟩ : syracuseStep 775847 = 1163771) B1163771
theorem B775931 : Blo 515797 775931 := bstep (se 1 (by rfl) ⟨581948, by rfl⟩ : syracuseStep 775931 = 1163897) B1163897
theorem B2217739 : Blo 515797 2217739 := bstep (se 1 (by rfl) ⟨1663304, by rfl⟩ : syracuseStep 2217739 = 3326609) B3326609
theorem B775967 : Blo 515797 775967 := bstep (se 1 (by rfl) ⟨581975, by rfl⟩ : syracuseStep 775967 = 1163951) B1163951
theorem B294508331 : Blo 515797 294508331 := bstep (se 1 (by rfl) ⟨220881248, by rfl⟩ : syracuseStep 294508331 = 441762497) B441762497
theorem B776015 : Blo 515797 776015 := bstep (se 1 (by rfl) ⟨582011, by rfl⟩ : syracuseStep 776015 = 1164023) B1164023
theorem B776135 : Blo 515797 776135 := bstep (se 1 (by rfl) ⟨582101, by rfl⟩ : syracuseStep 776135 = 1164203) B1164203
theorem B874489 : Blo 515797 874489 := bstep (se 2 (by rfl) ⟨327933, by rfl⟩ : syracuseStep 874489 = 655867) B655867
theorem B874651 : Blo 515797 874651 := bstep (se 1 (by rfl) ⟨655988, by rfl⟩ : syracuseStep 874651 = 1311977) B1311977
theorem B874759 : Blo 515797 874759 := bstep (se 1 (by rfl) ⟨656069, by rfl⟩ : syracuseStep 874759 = 1312139) B1312139
theorem B776489 : Blo 515797 776489 := bstep (se 2 (by rfl) ⟨291183, by rfl⟩ : syracuseStep 776489 = 582367) B582367
theorem B874793 : Blo 515797 874793 := bstep (se 2 (by rfl) ⟨328047, by rfl⟩ : syracuseStep 874793 = 656095) B656095
theorem B776495 : Blo 515797 776495 := bstep (se 1 (by rfl) ⟨582371, by rfl⟩ : syracuseStep 776495 = 1164743) B1164743
theorem B776735 : Blo 515797 776735 := bstep (se 1 (by rfl) ⟨582551, by rfl⟩ : syracuseStep 776735 = 1165103) B1165103
theorem B2611763 : Blo 515797 2611763 := bstep (se 1 (by rfl) ⟨1958822, by rfl⟩ : syracuseStep 2611763 = 3917645) B3917645
theorem B2939489 : Blo 515797 2939489 := bstep (se 2 (by rfl) ⟨1102308, by rfl⟩ : syracuseStep 2939489 = 2204617) B2204617
theorem B777119 : Blo 515797 777119 := bstep (se 1 (by rfl) ⟨582839, by rfl⟩ : syracuseStep 777119 = 1165679) B1165679
theorem B777167 : Blo 515797 777167 := bstep (se 1 (by rfl) ⟨582875, by rfl⟩ : syracuseStep 777167 = 1165751) B1165751
theorem B777257 : Blo 515797 777257 := bstep (se 2 (by rfl) ⟨291471, by rfl⟩ : syracuseStep 777257 = 582943) B582943
theorem B777263 : Blo 515797 777263 := bstep (se 1 (by rfl) ⟨582947, by rfl⟩ : syracuseStep 777263 = 1165895) B1165895
theorem B777287 : Blo 515797 777287 := bstep (se 1 (by rfl) ⟨582965, by rfl⟩ : syracuseStep 777287 = 1165931) B1165931
theorem B875785 : Blo 515797 875785 := bstep (se 2 (by rfl) ⟨328419, by rfl⟩ : syracuseStep 875785 = 656839) B656839
theorem B777551 : Blo 515797 777551 := bstep (se 1 (by rfl) ⟨583163, by rfl⟩ : syracuseStep 777551 = 1166327) B1166327
theorem B777641 : Blo 515797 777641 := bstep (se 2 (by rfl) ⟨291615, by rfl⟩ : syracuseStep 777641 = 583231) B583231
theorem B1138151 : Blo 515797 1138151 := bstep (se 1 (by rfl) ⟨853613, by rfl⟩ : syracuseStep 1138151 = 1707227) B1707227
theorem B777791 : Blo 515797 777791 := bstep (se 1 (by rfl) ⟨583343, by rfl⟩ : syracuseStep 777791 = 1166687) B1166687
theorem B15163139 : Blo 515797 15163139 := bstep (se 1 (by rfl) ⟨11372354, by rfl⟩ : syracuseStep 15163139 = 22744709) B22744709
theorem B2940695 : Blo 515797 2940695 := bstep (se 1 (by rfl) ⟨2205521, by rfl⟩ : syracuseStep 2940695 = 4411043) B4411043
theorem B515911 : Blo 515797 515911 := bstep (se 1 (by rfl) ⟨386933, by rfl⟩ : syracuseStep 515911 = 773867) B773867
theorem B778055 : Blo 515797 778055 := bstep (se 1 (by rfl) ⟨583541, by rfl⟩ : syracuseStep 778055 = 1167083) B1167083
theorem B876359 : Blo 515797 876359 := bstep (se 1 (by rfl) ⟨657269, by rfl⟩ : syracuseStep 876359 = 1314539) B1314539
theorem B778139 : Blo 515797 778139 := bstep (se 1 (by rfl) ⟨583604, by rfl⟩ : syracuseStep 778139 = 1167209) B1167209
theorem B516063 : Blo 515797 516063 := bstep (se 1 (by rfl) ⟨387047, by rfl⟩ : syracuseStep 516063 = 774095) B774095
theorem B2613383 : Blo 515797 2613383 := bstep (se 1 (by rfl) ⟨1960037, by rfl⟩ : syracuseStep 2613383 = 3920075) B3920075
theorem B516327 : Blo 515797 516327 := bstep (se 1 (by rfl) ⟨387245, by rfl⟩ : syracuseStep 516327 = 774491) B774491
theorem B581863 : Blo 515797 581863 := bstep (se 1 (by rfl) ⟨436397, by rfl⟩ : syracuseStep 581863 = 872795) B872795
theorem B1106273 : Blo 515797 1106273 := bstep (se 2 (by rfl) ⟨414852, by rfl⟩ : syracuseStep 1106273 = 829705) B829705
theorem B516479 : Blo 515797 516479 := bstep (se 1 (by rfl) ⟨387359, by rfl⟩ : syracuseStep 516479 = 774719) B774719
theorem B516559 : Blo 515797 516559 := bstep (se 1 (by rfl) ⟨387419, by rfl⟩ : syracuseStep 516559 = 774839) B774839
theorem B778703 : Blo 515797 778703 := bstep (se 1 (by rfl) ⟨584027, by rfl⟩ : syracuseStep 778703 = 1168055) B1168055
theorem B877007 : Blo 515797 877007 := bstep (se 1 (by rfl) ⟨657755, by rfl⟩ : syracuseStep 877007 = 1315511) B1315511
theorem B778745 : Blo 515797 778745 := bstep (se 2 (by rfl) ⟨292029, by rfl⟩ : syracuseStep 778745 = 584059) B584059
theorem B778847 : Blo 515797 778847 := bstep (se 1 (by rfl) ⟨584135, by rfl⟩ : syracuseStep 778847 = 1168271) B1168271
theorem B516711 : Blo 515797 516711 := bstep (se 1 (by rfl) ⟨387533, by rfl⟩ : syracuseStep 516711 = 775067) B775067
theorem B2613869 : Blo 515797 2613869 := bstep (se 3 (by rfl) ⟨490100, by rfl⟩ : syracuseStep 2613869 = 980201) B980201
theorem B8839853 : Blo 515797 8839853 := bstep (se 3 (by rfl) ⟨1657472, by rfl⟩ : syracuseStep 8839853 = 3314945) B3314945
theorem B1663753 : Blo 515797 1663753 := bstep (se 2 (by rfl) ⟨623907, by rfl⟩ : syracuseStep 1663753 = 1247815) B1247815
theorem B8938291 : Blo 515797 8938291 := bstep (se 1 (by rfl) ⟨6703718, by rfl⟩ : syracuseStep 8938291 = 13407437) B13407437
theorem B516975 : Blo 515797 516975 := bstep (se 1 (by rfl) ⟨387731, by rfl⟩ : syracuseStep 516975 = 775463) B775463
theorem B582511 : Blo 515797 582511 := bstep (se 1 (by rfl) ⟨436883, by rfl⟩ : syracuseStep 582511 = 873767) B873767
theorem B517031 : Blo 515797 517031 := bstep (se 1 (by rfl) ⟨387773, by rfl⟩ : syracuseStep 517031 = 775547) B775547
theorem B517115 : Blo 515797 517115 := bstep (se 1 (by rfl) ⟨387836, by rfl⟩ : syracuseStep 517115 = 775673) B775673
theorem B517183 : Blo 515797 517183 := bstep (se 1 (by rfl) ⟨387887, by rfl⟩ : syracuseStep 517183 = 775775) B775775
theorem B779327 : Blo 515797 779327 := bstep (se 1 (by rfl) ⟨584495, by rfl⟩ : syracuseStep 779327 = 1168991) B1168991
theorem B779369 : Blo 515797 779369 := bstep (se 2 (by rfl) ⟨292263, by rfl⟩ : syracuseStep 779369 = 584527) B584527
theorem B1664189 : Blo 515797 1664189 := bstep (se 3 (by rfl) ⟨312035, by rfl⟩ : syracuseStep 1664189 = 624071) B624071
theorem B517327 : Blo 515797 517327 := bstep (se 1 (by rfl) ⟨387995, by rfl⟩ : syracuseStep 517327 = 775991) B775991
theorem B779471 : Blo 515797 779471 := bstep (se 1 (by rfl) ⟨584603, by rfl⟩ : syracuseStep 779471 = 1169207) B1169207
theorem B7071113 : Blo 515797 7071113 := bstep (se 2 (by rfl) ⟨2651667, by rfl⟩ : syracuseStep 7071113 = 5303335) B5303335
theorem B517531 : Blo 515797 517531 := bstep (se 1 (by rfl) ⟨388148, by rfl⟩ : syracuseStep 517531 = 776297) B776297
theorem B779675 : Blo 515797 779675 := bstep (se 1 (by rfl) ⟨584756, by rfl⟩ : syracuseStep 779675 = 1169513) B1169513
theorem B517743 : Blo 515797 517743 := bstep (se 1 (by rfl) ⟨388307, by rfl⟩ : syracuseStep 517743 = 776615) B776615
theorem B517799 : Blo 515797 517799 := bstep (se 1 (by rfl) ⟨388349, by rfl⟩ : syracuseStep 517799 = 776699) B776699
theorem B2615003 : Blo 515797 2615003 := bstep (se 1 (by rfl) ⟨1961252, by rfl⟩ : syracuseStep 2615003 = 3922505) B3922505
theorem B1861343 : Blo 515797 1861343 := bstep (se 1 (by rfl) ⟨1396007, by rfl⟩ : syracuseStep 1861343 = 2792015) B2792015
theorem B517883 : Blo 515797 517883 := bstep (se 1 (by rfl) ⟨388412, by rfl⟩ : syracuseStep 517883 = 776825) B776825
theorem B517919 : Blo 515797 517919 := bstep (se 1 (by rfl) ⟨388439, by rfl⟩ : syracuseStep 517919 = 776879) B776879
theorem B517951 : Blo 515797 517951 := bstep (se 1 (by rfl) ⟨388463, by rfl⟩ : syracuseStep 517951 = 776927) B776927
theorem B518127 : Blo 515797 518127 := bstep (se 1 (by rfl) ⟨388595, by rfl⟩ : syracuseStep 518127 = 777191) B777191
theorem B583663 : Blo 515797 583663 := bstep (se 1 (by rfl) ⟨437747, by rfl⟩ : syracuseStep 583663 = 875495) B875495
theorem B14968921 : Blo 515797 14968921 := bstep (se 2 (by rfl) ⟨5613345, by rfl⟩ : syracuseStep 14968921 = 11226691) B11226691
theorem B518299 : Blo 515797 518299 := bstep (se 1 (by rfl) ⟨388724, by rfl⟩ : syracuseStep 518299 = 777449) B777449
theorem B518335 : Blo 515797 518335 := bstep (se 1 (by rfl) ⟨388751, by rfl⟩ : syracuseStep 518335 = 777503) B777503
theorem B518447 : Blo 515797 518447 := bstep (se 1 (by rfl) ⟨388835, by rfl⟩ : syracuseStep 518447 = 777671) B777671
theorem B518683 : Blo 515797 518683 := bstep (se 1 (by rfl) ⟨389012, by rfl⟩ : syracuseStep 518683 = 778025) B778025
theorem B518687 : Blo 515797 518687 := bstep (se 1 (by rfl) ⟨389015, by rfl⟩ : syracuseStep 518687 = 778031) B778031
theorem B1960631 : Blo 515797 1960631 := bstep (se 1 (by rfl) ⟨1470473, by rfl⟩ : syracuseStep 1960631 = 2940947) B2940947
theorem B5040899 : Blo 515797 5040899 := bstep (se 1 (by rfl) ⟨3780674, by rfl⟩ : syracuseStep 5040899 = 7561349) B7561349
theorem B519003 : Blo 515797 519003 := bstep (se 1 (by rfl) ⟨389252, by rfl⟩ : syracuseStep 519003 = 778505) B778505
theorem B2943863 : Blo 515797 2943863 := bstep (se 1 (by rfl) ⟨2207897, by rfl⟩ : syracuseStep 2943863 = 4415795) B4415795
theorem B519071 : Blo 515797 519071 := bstep (se 1 (by rfl) ⟨389303, by rfl⟩ : syracuseStep 519071 = 778607) B778607
theorem B2616299 : Blo 515797 2616299 := bstep (se 1 (by rfl) ⟨1962224, by rfl⟩ : syracuseStep 2616299 = 3924449) B3924449
theorem B519215 : Blo 515797 519215 := bstep (se 1 (by rfl) ⟨389411, by rfl⟩ : syracuseStep 519215 = 778823) B778823
theorem B519239 : Blo 515797 519239 := bstep (se 1 (by rfl) ⟨389429, by rfl⟩ : syracuseStep 519239 = 778859) B778859
theorem B7072865 : Blo 515797 7072865 := bstep (se 2 (by rfl) ⟨2652324, by rfl⟩ : syracuseStep 7072865 = 5304649) B5304649
theorem B11234483 : Blo 515797 11234483 := bstep (se 1 (by rfl) ⟨8425862, by rfl⟩ : syracuseStep 11234483 = 16851725) B16851725
theorem B519391 : Blo 515797 519391 := bstep (se 1 (by rfl) ⟨389543, by rfl⟩ : syracuseStep 519391 = 779087) B779087
theorem B13266341 : Blo 515797 13266341 := bstep (se 4 (by rfl) ⟨1243719, by rfl⟩ : syracuseStep 13266341 = 2487439) B2487439
theorem B519655 : Blo 515797 519655 := bstep (se 1 (by rfl) ⟨389741, by rfl⟩ : syracuseStep 519655 = 779483) B779483
theorem B519771 : Blo 515797 519771 := bstep (se 1 (by rfl) ⟨389828, by rfl⟩ : syracuseStep 519771 = 779657) B779657
theorem B1470109 : Blo 515797 1470109 := bstep (se 3 (by rfl) ⟨275645, by rfl⟩ : syracuseStep 1470109 = 551291) B551291
theorem B4255595 : Blo 515797 4255595 := bstep (se 1 (by rfl) ⟨3191696, by rfl⟩ : syracuseStep 4255595 = 6383393) B6383393
theorem B1306489 : Blo 515797 1306489 := bstep (se 2 (by rfl) ⟨489933, by rfl⟩ : syracuseStep 1306489 = 979867) B979867
theorem B22409095 : Blo 515797 22409095 := bstep (se 1 (by rfl) ⟨16806821, by rfl⟩ : syracuseStep 22409095 = 33613643) B33613643
theorem B1896331 : Blo 515797 1896331 := bstep (se 1 (by rfl) ⟨1422248, by rfl⟩ : syracuseStep 1896331 = 2844497) B2844497
theorem B2617271 : Blo 515797 2617271 := bstep (se 1 (by rfl) ⟨1962953, by rfl⟩ : syracuseStep 2617271 = 3925907) B3925907
theorem B1962377 : Blo 515797 1962377 := bstep (se 2 (by rfl) ⟨735891, by rfl⟩ : syracuseStep 1962377 = 1471783) B1471783
theorem B1962407 : Blo 515797 1962407 := bstep (se 1 (by rfl) ⟨1471805, by rfl⟩ : syracuseStep 1962407 = 2943611) B2943611
theorem B1569899 : Blo 515797 1569899 := bstep (se 1 (by rfl) ⟨1177424, by rfl⟩ : syracuseStep 1569899 = 2354849) B2354849
theorem B1471841 : Blo 515797 1471841 := bstep (se 2 (by rfl) ⟨551940, by rfl⟩ : syracuseStep 1471841 = 1103881) B1103881
theorem B1308059 : Blo 515797 1308059 := bstep (se 1 (by rfl) ⟨981044, by rfl⟩ : syracuseStep 1308059 = 1962089) B1962089
theorem B1177271 : Blo 515797 1177271 := bstep (se 1 (by rfl) ⟨882953, by rfl⟩ : syracuseStep 1177271 = 1765907) B1765907
theorem B25098133 : Blo 515797 25098133 := bstep (se 6 (by rfl) ⟨588237, by rfl⟩ : syracuseStep 25098133 = 1176475) B1176475
theorem B7075937 : Blo 515797 7075937 := bstep (se 2 (by rfl) ⟨2653476, by rfl⟩ : syracuseStep 7075937 = 5306953) B5306953
theorem B1243279 : Blo 515797 1243279 := bstep (se 1 (by rfl) ⟨932459, by rfl⟩ : syracuseStep 1243279 = 1864919) B1864919
theorem B1898639 : Blo 515797 1898639 := bstep (se 1 (by rfl) ⟨1423979, by rfl⟩ : syracuseStep 1898639 = 2847959) B2847959
theorem B653503 : Blo 515797 653503 := bstep (se 1 (by rfl) ⟨490127, by rfl⟩ : syracuseStep 653503 = 980255) B980255
theorem B981371 : Blo 515797 981371 := bstep (se 1 (by rfl) ⟨736028, by rfl⟩ : syracuseStep 981371 = 1472057) B1472057
theorem B2128403 : Blo 515797 2128403 := bstep (se 1 (by rfl) ⟨1596302, by rfl⟩ : syracuseStep 2128403 = 3192605) B3192605
theorem B883753 : Blo 515797 883753 := bstep (se 2 (by rfl) ⟨331407, by rfl⟩ : syracuseStep 883753 = 662815) B662815
theorem B982199 : Blo 515797 982199 := bstep (se 1 (by rfl) ⟨736649, by rfl⟩ : syracuseStep 982199 = 1473299) B1473299
theorem B2358791 : Blo 515797 2358791 := bstep (se 1 (by rfl) ⟨1769093, by rfl⟩ : syracuseStep 2358791 = 3538187) B3538187
theorem B884287 : Blo 515797 884287 := bstep (se 1 (by rfl) ⟨663215, by rfl⟩ : syracuseStep 884287 = 1326431) B1326431
theorem B3931739 : Blo 515797 3931739 := bstep (se 1 (by rfl) ⟨2948804, by rfl⟩ : syracuseStep 3931739 = 5897609) B5897609
theorem B4423481 : Blo 515797 4423481 := bstep (se 2 (by rfl) ⟨1658805, by rfl⟩ : syracuseStep 4423481 = 3317611) B3317611
theorem B1966265 : Blo 515797 1966265 := bstep (se 2 (by rfl) ⟨737349, by rfl⟩ : syracuseStep 1966265 = 1474699) B1474699
theorem B2621807 : Blo 515797 2621807 := bstep (se 1 (by rfl) ⟨1966355, by rfl⟩ : syracuseStep 2621807 = 3932711) B3932711
theorem B1966463 : Blo 515797 1966463 := bstep (se 1 (by rfl) ⟨1474847, by rfl⟩ : syracuseStep 1966463 = 2949695) B2949695
theorem B885163 : Blo 515797 885163 := bstep (se 1 (by rfl) ⟨663872, by rfl⟩ : syracuseStep 885163 = 1327745) B1327745
theorem B983657 : Blo 515797 983657 := bstep (se 2 (by rfl) ⟨368871, by rfl⟩ : syracuseStep 983657 = 737743) B737743
theorem B1180457 : Blo 515797 1180457 := bstep (se 2 (by rfl) ⟨442671, by rfl⟩ : syracuseStep 1180457 = 885343) B885343
theorem B984059 : Blo 515797 984059 := bstep (se 1 (by rfl) ⟨738044, by rfl⟩ : syracuseStep 984059 = 1476089) B1476089
theorem B57672769 : Blo 515797 57672769 := bstep (se 2 (by rfl) ⟨21627288, by rfl⟩ : syracuseStep 57672769 = 43254577) B43254577
theorem B984287 : Blo 515797 984287 := bstep (se 1 (by rfl) ⟨738215, by rfl⟩ : syracuseStep 984287 = 1476431) B1476431
theorem B656687 : Blo 515797 656687 := bstep (se 1 (by rfl) ⟨492515, by rfl⟩ : syracuseStep 656687 = 985031) B985031
theorem B9930073 : Blo 515797 9930073 := bstep (se 2 (by rfl) ⟨3723777, by rfl⟩ : syracuseStep 9930073 = 7447555) B7447555
theorem B984545 : Blo 515797 984545 := bstep (se 2 (by rfl) ⟨369204, by rfl⟩ : syracuseStep 984545 = 738409) B738409
theorem B887119 : Blo 515797 887119 := bstep (se 1 (by rfl) ⟨665339, by rfl⟩ : syracuseStep 887119 = 1330679) B1330679
theorem B1870295 : Blo 515797 1870295 := bstep (se 1 (by rfl) ⟨1402721, by rfl⟩ : syracuseStep 1870295 = 2805443) B2805443
theorem B19958561 : Blo 515797 19958561 := bstep (se 2 (by rfl) ⟨7484460, by rfl⟩ : syracuseStep 19958561 = 14968921) B14968921
theorem B2493575 : Blo 515797 2493575 := bstep (se 1 (by rfl) ⟨1870181, by rfl⟩ : syracuseStep 2493575 = 3740363) B3740363
theorem B2624723 : Blo 515797 2624723 := bstep (se 1 (by rfl) ⟨1968542, by rfl⟩ : syracuseStep 2624723 = 3937085) B3937085
theorem B1871059 : Blo 515797 1871059 := bstep (se 1 (by rfl) ⟨1403294, by rfl⟩ : syracuseStep 1871059 = 2806589) B2806589
theorem B986489 : Blo 515797 986489 := bstep (se 2 (by rfl) ⟨369933, by rfl⟩ : syracuseStep 986489 = 739867) B739867
theorem B2101115 : Blo 515797 2101115 := bstep (se 1 (by rfl) ⟨1575836, by rfl⟩ : syracuseStep 2101115 = 3151673) B3151673
theorem B1052827 : Blo 515797 1052827 := bstep (se 1 (by rfl) ⟨789620, by rfl⟩ : syracuseStep 1052827 = 1579241) B1579241
theorem B1970365 : Blo 515797 1970365 := bstep (se 3 (by rfl) ⟨369443, by rfl⟩ : syracuseStep 1970365 = 738887) B738887
theorem B1741175 : Blo 515797 1741175 := bstep (se 1 (by rfl) ⟨1305881, by rfl⟩ : syracuseStep 1741175 = 2611763) B2611763
theorem B3740215 : Blo 515797 3740215 := bstep (se 1 (by rfl) ⟨2805161, by rfl⟩ : syracuseStep 3740215 = 5610323) B5610323
theorem B1741985 : Blo 515797 1741985 := bstep (se 2 (by rfl) ⟨653244, by rfl⟩ : syracuseStep 1741985 = 1306489) B1306489
theorem B2528441 : Blo 515797 2528441 := bstep (se 2 (by rfl) ⟨948165, by rfl⟩ : syracuseStep 2528441 = 1896331) B1896331
theorem B1971611 : Blo 515797 1971611 := bstep (se 1 (by rfl) ⟨1478708, by rfl⟩ : syracuseStep 1971611 = 2957417) B2957417
theorem B1742255 : Blo 515797 1742255 := bstep (se 1 (by rfl) ⟨1306691, by rfl⟩ : syracuseStep 1742255 = 2613383) B2613383
theorem B2626991 : Blo 515797 2626991 := bstep (se 1 (by rfl) ⟨1970243, by rfl⟩ : syracuseStep 2626991 = 3940487) B3940487
theorem B2102867 : Blo 515797 2102867 := bstep (se 1 (by rfl) ⟨1577150, by rfl⟩ : syracuseStep 2102867 = 3154301) B3154301
theorem B1742579 : Blo 515797 1742579 := bstep (se 1 (by rfl) ⟨1306934, by rfl⟩ : syracuseStep 1742579 = 2613869) B2613869
theorem B1972127 : Blo 515797 1972127 := bstep (se 1 (by rfl) ⟨1479095, by rfl⟩ : syracuseStep 1972127 = 2958191) B2958191
theorem B1743335 : Blo 515797 1743335 := bstep (se 1 (by rfl) ⟨1307501, by rfl⟩ : syracuseStep 1743335 = 2615003) B2615003
theorem B2955959 : Blo 515797 2955959 := bstep (se 1 (by rfl) ⟨2216969, by rfl⟩ : syracuseStep 2955959 = 4433939) B4433939
theorem B5675741 : Blo 515797 5675741 := bstep (se 3 (by rfl) ⟨1064201, by rfl⟩ : syracuseStep 5675741 = 2128403) B2128403
theorem B1744199 : Blo 515797 1744199 := bstep (se 1 (by rfl) ⟨1308149, by rfl⟩ : syracuseStep 1744199 = 2616299) B2616299
theorem B2956985 : Blo 515797 2956985 := bstep (se 2 (by rfl) ⟨1108869, by rfl⟩ : syracuseStep 2956985 = 2217739) B2217739
theorem B33464177 : Blo 515797 33464177 := bstep (se 2 (by rfl) ⟨12549066, by rfl⟩ : syracuseStep 33464177 = 25098133) B25098133
theorem B1744847 : Blo 515797 1744847 := bstep (se 1 (by rfl) ⟨1308635, by rfl⟩ : syracuseStep 1744847 = 2617271) B2617271
theorem B3940973 : Blo 515797 3940973 := bstep (se 3 (by rfl) ⟨738932, by rfl⟩ : syracuseStep 3940973 = 1477865) B1477865
theorem B149038841 : Blo 515797 149038841 := bstep (se 2 (by rfl) ⟨55889565, by rfl⟩ : syracuseStep 149038841 = 111779131) B111779131
theorem B5319431 : Blo 515797 5319431 := bstep (se 1 (by rfl) ⟨3989573, by rfl⟩ : syracuseStep 5319431 = 7979147) B7979147
theorem B3943403 : Blo 515797 3943403 := bstep (se 1 (by rfl) ⟨2957552, by rfl⟩ : syracuseStep 3943403 = 5915105) B5915105
theorem B4992101 : Blo 515797 4992101 := bstep (se 4 (by rfl) ⟨468009, by rfl⟩ : syracuseStep 4992101 = 936019) B936019
theorem B830633 : Blo 515797 830633 := bstep (se 2 (by rfl) ⟨311487, by rfl⟩ : syracuseStep 830633 = 622975) B622975
theorem B18853397 : Blo 515797 18853397 := bstep (se 6 (by rfl) ⟨441876, by rfl⟩ : syracuseStep 18853397 = 883753) B883753
theorem B4730687 : Blo 515797 4730687 := bstep (se 1 (by rfl) ⟨3548015, by rfl⟩ : syracuseStep 4730687 = 7096031) B7096031
theorem B5026319 : Blo 515797 5026319 := bstep (se 1 (by rfl) ⟨3769739, by rfl⟩ : syracuseStep 5026319 = 7539479) B7539479
theorem B31928903 : Blo 515797 31928903 := bstep (se 1 (by rfl) ⟨23946677, by rfl⟩ : syracuseStep 31928903 = 47893355) B47893355
theorem B4437665 : Blo 515797 4437665 := bstep (se 2 (by rfl) ⟨1664124, by rfl⟩ : syracuseStep 4437665 = 3328249) B3328249
theorem B1160927 : Blo 515797 1160927 := bstep (se 1 (by rfl) ⟨870695, by rfl⟩ : syracuseStep 1160927 = 1741391) B1741391
theorem B38320067 : Blo 515797 38320067 := bstep (se 1 (by rfl) ⟨28740050, by rfl⟩ : syracuseStep 38320067 = 57480101) B57480101
theorem B1161287 : Blo 515797 1161287 := bstep (se 1 (by rfl) ⟨870965, by rfl⟩ : syracuseStep 1161287 = 1741931) B1741931
theorem B1751111 : Blo 515797 1751111 := bstep (se 1 (by rfl) ⟨1313333, by rfl⟩ : syracuseStep 1751111 = 2626667) B2626667
theorem B13318829 : Blo 515797 13318829 := bstep (se 3 (by rfl) ⟨2497280, by rfl⟩ : syracuseStep 13318829 = 4994561) B4994561
theorem B1161953 : Blo 515797 1161953 := bstep (se 2 (by rfl) ⟨435732, by rfl⟩ : syracuseStep 1161953 = 871465) B871465
theorem B932617 : Blo 515797 932617 := bstep (se 2 (by rfl) ⟨349731, by rfl⟩ : syracuseStep 932617 = 699463) B699463
theorem B1162151 : Blo 515797 1162151 := bstep (se 1 (by rfl) ⟨871613, by rfl⟩ : syracuseStep 1162151 = 1743227) B1743227
theorem B1751975 : Blo 515797 1751975 := bstep (se 1 (by rfl) ⟨1313981, by rfl⟩ : syracuseStep 1751975 = 2627963) B2627963
theorem B1162331 : Blo 515797 1162331 := bstep (se 1 (by rfl) ⟨871748, by rfl⟩ : syracuseStep 1162331 = 1743497) B1743497
theorem B2210921 : Blo 515797 2210921 := bstep (se 2 (by rfl) ⟨829095, by rfl⟩ : syracuseStep 2210921 = 1658191) B1658191
theorem B7978409 : Blo 515797 7978409 := bstep (se 2 (by rfl) ⟨2991903, by rfl⟩ : syracuseStep 7978409 = 5983807) B5983807
theorem B1163087 : Blo 515797 1163087 := bstep (se 1 (by rfl) ⟨872315, by rfl⟩ : syracuseStep 1163087 = 1744631) B1744631
theorem B10108759 : Blo 515797 10108759 := bstep (se 1 (by rfl) ⟨7581569, by rfl⟩ : syracuseStep 10108759 = 15163139) B15163139
theorem B737515 : Blo 515797 737515 := bstep (se 1 (by rfl) ⟨553136, by rfl⟩ : syracuseStep 737515 = 1106273) B1106273
theorem B18924029 : Blo 515797 18924029 := bstep (se 3 (by rfl) ⟨3548255, by rfl⟩ : syracuseStep 18924029 = 7096511) B7096511
theorem B1163807 : Blo 515797 1163807 := bstep (se 1 (by rfl) ⟨872855, by rfl⟩ : syracuseStep 1163807 = 1745711) B1745711
theorem B1163879 : Blo 515797 1163879 := bstep (se 1 (by rfl) ⟨872909, by rfl⟩ : syracuseStep 1163879 = 1745819) B1745819
theorem B1753703 : Blo 515797 1753703 := bstep (se 1 (by rfl) ⟨1315277, by rfl⟩ : syracuseStep 1753703 = 2630555) B2630555
theorem B4408445 : Blo 515797 4408445 := bstep (se 3 (by rfl) ⟨826583, by rfl⟩ : syracuseStep 4408445 = 1653167) B1653167
theorem B1164635 : Blo 515797 1164635 := bstep (se 1 (by rfl) ⟨873476, by rfl⟩ : syracuseStep 1164635 = 1746953) B1746953
theorem B1164905 : Blo 515797 1164905 := bstep (se 2 (by rfl) ⟨436839, by rfl⟩ : syracuseStep 1164905 = 873679) B873679
theorem B32720525 : Blo 515797 32720525 := bstep (se 3 (by rfl) ⟨6135098, by rfl⟩ : syracuseStep 32720525 = 12270197) B12270197
theorem B3360599 : Blo 515797 3360599 := bstep (se 1 (by rfl) ⟨2520449, by rfl⟩ : syracuseStep 3360599 = 5040899) B5040899
theorem B7489655 : Blo 515797 7489655 := bstep (se 1 (by rfl) ⟨5617241, by rfl⟩ : syracuseStep 7489655 = 11234483) B11234483
theorem B1165499 : Blo 515797 1165499 := bstep (se 1 (by rfl) ⟨874124, by rfl⟩ : syracuseStep 1165499 = 1748249) B1748249
theorem B1165535 : Blo 515797 1165535 := bstep (se 1 (by rfl) ⟨874151, by rfl⟩ : syracuseStep 1165535 = 1748303) B1748303
theorem B2837063 : Blo 515797 2837063 := bstep (se 1 (by rfl) ⟨2127797, by rfl⟩ : syracuseStep 2837063 = 4255595) B4255595
theorem B1165985 : Blo 515797 1165985 := bstep (se 2 (by rfl) ⟨437244, by rfl⟩ : syracuseStep 1165985 = 874489) B874489
theorem B1657705 : Blo 515797 1657705 := bstep (se 2 (by rfl) ⟨621639, by rfl⟩ : syracuseStep 1657705 = 1243279) B1243279
theorem B1166201 : Blo 515797 1166201 := bstep (se 2 (by rfl) ⟨437325, by rfl⟩ : syracuseStep 1166201 = 874651) B874651
theorem B871337 : Blo 515797 871337 := bstep (se 2 (by rfl) ⟨326751, by rfl⟩ : syracuseStep 871337 = 653503) B653503
theorem B1166345 : Blo 515797 1166345 := bstep (se 2 (by rfl) ⟨437379, by rfl⟩ : syracuseStep 1166345 = 874759) B874759
theorem B1166399 : Blo 515797 1166399 := bstep (se 1 (by rfl) ⟨874799, by rfl⟩ : syracuseStep 1166399 = 1749599) B1749599
theorem B773735 : Blo 515797 773735 := bstep (se 1 (by rfl) ⟨580301, by rfl⟩ : syracuseStep 773735 = 1160603) B1160603
theorem B872039 : Blo 515797 872039 := bstep (se 1 (by rfl) ⟨654029, by rfl⟩ : syracuseStep 872039 = 1308059) B1308059
theorem B1167227 : Blo 515797 1167227 := bstep (se 1 (by rfl) ⟨875420, by rfl⟩ : syracuseStep 1167227 = 1750841) B1750841
theorem B3035069 : Blo 515797 3035069 := bstep (se 3 (by rfl) ⟨569075, by rfl⟩ : syracuseStep 3035069 = 1138151) B1138151
theorem B774119 : Blo 515797 774119 := bstep (se 1 (by rfl) ⟨580589, by rfl⟩ : syracuseStep 774119 = 1161179) B1161179
theorem B1167335 : Blo 515797 1167335 := bstep (se 1 (by rfl) ⟨875501, by rfl⟩ : syracuseStep 1167335 = 1751003) B1751003
theorem B839675 : Blo 515797 839675 := bstep (se 1 (by rfl) ⟨629756, by rfl⟩ : syracuseStep 839675 = 1259513) B1259513
theorem B774239 : Blo 515797 774239 := bstep (se 1 (by rfl) ⟨580679, by rfl⟩ : syracuseStep 774239 = 1161359) B1161359
theorem B1265759 : Blo 515797 1265759 := bstep (se 1 (by rfl) ⟨949319, by rfl⟩ : syracuseStep 1265759 = 1898639) B1898639
theorem B774251 : Blo 515797 774251 := bstep (se 1 (by rfl) ⟨580688, by rfl⟩ : syracuseStep 774251 = 1161377) B1161377
theorem B774299 : Blo 515797 774299 := bstep (se 1 (by rfl) ⟨580724, by rfl⟩ : syracuseStep 774299 = 1161449) B1161449
theorem B1167515 : Blo 515797 1167515 := bstep (se 1 (by rfl) ⟨875636, by rfl⟩ : syracuseStep 1167515 = 1751273) B1751273
theorem B1102043 : Blo 515797 1102043 := bstep (se 1 (by rfl) ⟨826532, by rfl⟩ : syracuseStep 1102043 = 1653065) B1653065
theorem B1167713 : Blo 515797 1167713 := bstep (se 2 (by rfl) ⟨437892, by rfl⟩ : syracuseStep 1167713 = 875785) B875785
theorem B1167803 : Blo 515797 1167803 := bstep (se 1 (by rfl) ⟨875852, by rfl⟩ : syracuseStep 1167803 = 1751705) B1751705
theorem B9458221 : Blo 515797 9458221 := bstep (se 3 (by rfl) ⟨1773416, by rfl⟩ : syracuseStep 9458221 = 3546833) B3546833
theorem B775151 : Blo 515797 775151 := bstep (se 1 (by rfl) ⟨581363, by rfl⟩ : syracuseStep 775151 = 1162727) B1162727
theorem B1660267 : Blo 515797 1660267 := bstep (se 1 (by rfl) ⟨1245200, by rfl⟩ : syracuseStep 1660267 = 2490401) B2490401
theorem B775535 : Blo 515797 775535 := bstep (se 1 (by rfl) ⟨581651, by rfl⟩ : syracuseStep 775535 = 1163303) B1163303
theorem B775655 : Blo 515797 775655 := bstep (se 1 (by rfl) ⟨581741, by rfl⟩ : syracuseStep 775655 = 1163483) B1163483
theorem B775817 : Blo 515797 775817 := bstep (se 2 (by rfl) ⟨290931, by rfl⟩ : syracuseStep 775817 = 581863) B581863
theorem B775835 : Blo 515797 775835 := bstep (se 1 (by rfl) ⟨581876, by rfl⟩ : syracuseStep 775835 = 1163753) B1163753
theorem B1169063 : Blo 515797 1169063 := bstep (se 1 (by rfl) ⟨876797, by rfl⟩ : syracuseStep 1169063 = 1753595) B1753595
theorem B776027 : Blo 515797 776027 := bstep (se 1 (by rfl) ⟨582020, by rfl⟩ : syracuseStep 776027 = 1164041) B1164041
theorem B1169243 : Blo 515797 1169243 := bstep (se 1 (by rfl) ⟨876932, by rfl⟩ : syracuseStep 1169243 = 1753865) B1753865
theorem B11360249 : Blo 515797 11360249 := bstep (se 2 (by rfl) ⟨4260093, by rfl⟩ : syracuseStep 11360249 = 8520187) B8520187
theorem B776411 : Blo 515797 776411 := bstep (se 1 (by rfl) ⟨582308, by rfl⟩ : syracuseStep 776411 = 1164617) B1164617
theorem B2218337 : Blo 515797 2218337 := bstep (se 2 (by rfl) ⟨831876, by rfl⟩ : syracuseStep 2218337 = 1663753) B1663753
theorem B11917721 : Blo 515797 11917721 := bstep (se 2 (by rfl) ⟨4469145, by rfl⟩ : syracuseStep 11917721 = 8938291) B8938291
theorem B6838715 : Blo 515797 6838715 := bstep (se 1 (by rfl) ⟨5129036, by rfl⟩ : syracuseStep 6838715 = 10258073) B10258073
theorem B4250089 : Blo 515797 4250089 := bstep (se 2 (by rfl) ⟨1593783, by rfl⟩ : syracuseStep 4250089 = 3187567) B3187567
theorem B776681 : Blo 515797 776681 := bstep (se 2 (by rfl) ⟨291255, by rfl⟩ : syracuseStep 776681 = 582511) B582511
theorem B5593799 : Blo 515797 5593799 := bstep (se 1 (by rfl) ⟨4195349, by rfl⟩ : syracuseStep 5593799 = 8390699) B8390699
theorem B580423 : Blo 515797 580423 := bstep (se 1 (by rfl) ⟨435317, by rfl⟩ : syracuseStep 580423 = 870635) B870635
theorem B777071 : Blo 515797 777071 := bstep (se 1 (by rfl) ⟨582803, by rfl⟩ : syracuseStep 777071 = 1165607) B1165607
theorem B777083 : Blo 515797 777083 := bstep (se 1 (by rfl) ⟨582812, by rfl⟩ : syracuseStep 777083 = 1165625) B1165625
theorem B875387 : Blo 515797 875387 := bstep (se 1 (by rfl) ⟨656540, by rfl⟩ : syracuseStep 875387 = 1313081) B1313081
theorem B581071 : Blo 515797 581071 := bstep (se 1 (by rfl) ⟨435803, by rfl⟩ : syracuseStep 581071 = 871607) B871607
theorem B581287 : Blo 515797 581287 := bstep (se 1 (by rfl) ⟨435965, by rfl⟩ : syracuseStep 581287 = 871931) B871931
theorem B777947 : Blo 515797 777947 := bstep (se 1 (by rfl) ⟨583460, by rfl⟩ : syracuseStep 777947 = 1166921) B1166921
theorem B876251 : Blo 515797 876251 := bstep (se 1 (by rfl) ⟨657188, by rfl⟩ : syracuseStep 876251 = 1314377) B1314377
theorem B515815 : Blo 515797 515815 := bstep (se 1 (by rfl) ⟨386861, by rfl⟩ : syracuseStep 515815 = 773723) B773723
theorem B515871 : Blo 515797 515871 := bstep (se 1 (by rfl) ⟨386903, by rfl⟩ : syracuseStep 515871 = 773807) B773807
theorem B515951 : Blo 515797 515951 := bstep (se 1 (by rfl) ⟨386963, by rfl⟩ : syracuseStep 515951 = 773927) B773927
theorem B516007 : Blo 515797 516007 := bstep (se 1 (by rfl) ⟨387005, by rfl⟩ : syracuseStep 516007 = 774011) B774011
theorem B581575 : Blo 515797 581575 := bstep (se 1 (by rfl) ⟨436181, by rfl⟩ : syracuseStep 581575 = 872363) B872363
theorem B778217 : Blo 515797 778217 := bstep (se 2 (by rfl) ⟨291831, by rfl⟩ : syracuseStep 778217 = 583663) B583663
theorem B876521 : Blo 515797 876521 := bstep (se 2 (by rfl) ⟨328695, by rfl⟩ : syracuseStep 876521 = 657391) B657391
theorem B1400819 : Blo 515797 1400819 := bstep (se 1 (by rfl) ⟨1050614, by rfl⟩ : syracuseStep 1400819 = 2101229) B2101229
theorem B37773317 : Blo 515797 37773317 := bstep (se 4 (by rfl) ⟨3541248, by rfl⟩ : syracuseStep 37773317 = 7082497) B7082497
theorem B28336139 : Blo 515797 28336139 := bstep (se 1 (by rfl) ⟨21252104, by rfl⟩ : syracuseStep 28336139 = 42504209) B42504209
theorem B4972691 : Blo 515797 4972691 := bstep (se 1 (by rfl) ⟨3729518, by rfl⟩ : syracuseStep 4972691 = 7459037) B7459037
theorem B516287 : Blo 515797 516287 := bstep (se 1 (by rfl) ⟨387215, by rfl⟩ : syracuseStep 516287 = 774431) B774431
theorem B2810051 : Blo 515797 2810051 := bstep (se 1 (by rfl) ⟨2107538, by rfl⟩ : syracuseStep 2810051 = 4215077) B4215077
theorem B516303 : Blo 515797 516303 := bstep (se 1 (by rfl) ⟨387227, by rfl⟩ : syracuseStep 516303 = 774455) B774455
theorem B516351 : Blo 515797 516351 := bstep (se 1 (by rfl) ⟨387263, by rfl⟩ : syracuseStep 516351 = 774527) B774527
theorem B4186397 : Blo 515797 4186397 := bstep (se 3 (by rfl) ⟨784949, by rfl⟩ : syracuseStep 4186397 = 1569899) B1569899
theorem B516399 : Blo 515797 516399 := bstep (se 1 (by rfl) ⟨387299, by rfl⟩ : syracuseStep 516399 = 774599) B774599
theorem B581935 : Blo 515797 581935 := bstep (se 1 (by rfl) ⟨436451, by rfl⟩ : syracuseStep 581935 = 872903) B872903
theorem B516635 : Blo 515797 516635 := bstep (se 1 (by rfl) ⟨387476, by rfl⟩ : syracuseStep 516635 = 774953) B774953
theorem B516639 : Blo 515797 516639 := bstep (se 1 (by rfl) ⟨387479, by rfl⟩ : syracuseStep 516639 = 774959) B774959
theorem B8413793 : Blo 515797 8413793 := bstep (se 2 (by rfl) ⟨3155172, by rfl⟩ : syracuseStep 8413793 = 6310345) B6310345
theorem B516719 : Blo 515797 516719 := bstep (se 1 (by rfl) ⟨387539, by rfl⟩ : syracuseStep 516719 = 775079) B775079
theorem B516775 : Blo 515797 516775 := bstep (se 1 (by rfl) ⟨387581, by rfl⟩ : syracuseStep 516775 = 775163) B775163
theorem B778919 : Blo 515797 778919 := bstep (se 1 (by rfl) ⟨584189, by rfl⟩ : syracuseStep 778919 = 1168379) B1168379
theorem B516815 : Blo 515797 516815 := bstep (se 1 (by rfl) ⟨387611, by rfl⟩ : syracuseStep 516815 = 775223) B775223
theorem B1958687 : Blo 515797 1958687 := bstep (se 1 (by rfl) ⟨1469015, by rfl⟩ : syracuseStep 1958687 = 2938031) B2938031
theorem B516895 : Blo 515797 516895 := bstep (se 1 (by rfl) ⟨387671, by rfl⟩ : syracuseStep 516895 = 775343) B775343
theorem B779039 : Blo 515797 779039 := bstep (se 1 (by rfl) ⟨584279, by rfl⟩ : syracuseStep 779039 = 1168559) B1168559
theorem B779063 : Blo 515797 779063 := bstep (se 1 (by rfl) ⟨584297, by rfl⟩ : syracuseStep 779063 = 1168595) B1168595
theorem B20243351 : Blo 515797 20243351 := bstep (se 1 (by rfl) ⟨15182513, by rfl⟩ : syracuseStep 20243351 = 30365027) B30365027
theorem B51045299 : Blo 515797 51045299 := bstep (se 1 (by rfl) ⟨38283974, by rfl⟩ : syracuseStep 51045299 = 76567949) B76567949
theorem B779243 : Blo 515797 779243 := bstep (se 1 (by rfl) ⟨584432, by rfl⟩ : syracuseStep 779243 = 1168865) B1168865
theorem B517167 : Blo 515797 517167 := bstep (se 1 (by rfl) ⟨387875, by rfl⟩ : syracuseStep 517167 = 775751) B775751
theorem B517231 : Blo 515797 517231 := bstep (se 1 (by rfl) ⟨387923, by rfl⟩ : syracuseStep 517231 = 775847) B775847
theorem B517287 : Blo 515797 517287 := bstep (se 1 (by rfl) ⟨387965, by rfl⟩ : syracuseStep 517287 = 775931) B775931
theorem B517311 : Blo 515797 517311 := bstep (se 1 (by rfl) ⟨387983, by rfl⟩ : syracuseStep 517311 = 775967) B775967
theorem B196338887 : Blo 515797 196338887 := bstep (se 1 (by rfl) ⟨147254165, by rfl⟩ : syracuseStep 196338887 = 294508331) B294508331
theorem B517343 : Blo 515797 517343 := bstep (se 1 (by rfl) ⟨388007, by rfl⟩ : syracuseStep 517343 = 776015) B776015
theorem B517423 : Blo 515797 517423 := bstep (se 1 (by rfl) ⟨388067, by rfl⟩ : syracuseStep 517423 = 776135) B776135
theorem B517659 : Blo 515797 517659 := bstep (se 1 (by rfl) ⟨388244, by rfl⟩ : syracuseStep 517659 = 776489) B776489
theorem B583195 : Blo 515797 583195 := bstep (se 1 (by rfl) ⟨437396, by rfl⟩ : syracuseStep 583195 = 874793) B874793
theorem B517663 : Blo 515797 517663 := bstep (se 1 (by rfl) ⟨388247, by rfl⟩ : syracuseStep 517663 = 776495) B776495
theorem B517823 : Blo 515797 517823 := bstep (se 1 (by rfl) ⟨388367, by rfl⟩ : syracuseStep 517823 = 776735) B776735
theorem B1959659 : Blo 515797 1959659 := bstep (se 1 (by rfl) ⟨1469744, by rfl⟩ : syracuseStep 1959659 = 2939489) B2939489
theorem B550847 : Blo 515797 550847 := bstep (se 1 (by rfl) ⟨413135, by rfl⟩ : syracuseStep 550847 = 826271) B826271
theorem B518079 : Blo 515797 518079 := bstep (se 1 (by rfl) ⟨388559, by rfl⟩ : syracuseStep 518079 = 777119) B777119
theorem B518111 : Blo 515797 518111 := bstep (se 1 (by rfl) ⟨388583, by rfl⟩ : syracuseStep 518111 = 777167) B777167
theorem B518171 : Blo 515797 518171 := bstep (se 1 (by rfl) ⟨388628, by rfl⟩ : syracuseStep 518171 = 777257) B777257
theorem B518175 : Blo 515797 518175 := bstep (se 1 (by rfl) ⟨388631, by rfl⟩ : syracuseStep 518175 = 777263) B777263
theorem B518191 : Blo 515797 518191 := bstep (se 1 (by rfl) ⟨388643, by rfl⟩ : syracuseStep 518191 = 777287) B777287
theorem B1861775 : Blo 515797 1861775 := bstep (se 1 (by rfl) ⟨1396331, by rfl⟩ : syracuseStep 1861775 = 2792663) B2792663
theorem B1960145 : Blo 515797 1960145 := bstep (se 2 (by rfl) ⟨735054, by rfl⟩ : syracuseStep 1960145 = 1470109) B1470109
theorem B518367 : Blo 515797 518367 := bstep (se 1 (by rfl) ⟨388775, by rfl⟩ : syracuseStep 518367 = 777551) B777551
theorem B518427 : Blo 515797 518427 := bstep (se 1 (by rfl) ⟨388820, by rfl⟩ : syracuseStep 518427 = 777641) B777641
theorem B518527 : Blo 515797 518527 := bstep (se 1 (by rfl) ⟨388895, by rfl⟩ : syracuseStep 518527 = 777791) B777791
theorem B29878793 : Blo 515797 29878793 := bstep (se 2 (by rfl) ⟨11204547, by rfl⟩ : syracuseStep 29878793 = 22409095) B22409095
theorem B1960463 : Blo 515797 1960463 := bstep (se 1 (by rfl) ⟨1470347, by rfl⟩ : syracuseStep 1960463 = 2940695) B2940695
theorem B518703 : Blo 515797 518703 := bstep (se 1 (by rfl) ⟨389027, by rfl⟩ : syracuseStep 518703 = 778055) B778055
theorem B584239 : Blo 515797 584239 := bstep (se 1 (by rfl) ⟨438179, by rfl⟩ : syracuseStep 584239 = 876359) B876359
theorem B518759 : Blo 515797 518759 := bstep (se 1 (by rfl) ⟨389069, by rfl⟩ : syracuseStep 518759 = 778139) B778139
theorem B519135 : Blo 515797 519135 := bstep (se 1 (by rfl) ⟨389351, by rfl⟩ : syracuseStep 519135 = 778703) B778703
theorem B584671 : Blo 515797 584671 := bstep (se 1 (by rfl) ⟨438503, by rfl⟩ : syracuseStep 584671 = 877007) B877007
theorem B519163 : Blo 515797 519163 := bstep (se 1 (by rfl) ⟨389372, by rfl⟩ : syracuseStep 519163 = 778745) B778745
theorem B519231 : Blo 515797 519231 := bstep (se 1 (by rfl) ⟨389423, by rfl⟩ : syracuseStep 519231 = 778847) B778847
theorem B5893235 : Blo 515797 5893235 := bstep (se 1 (by rfl) ⟨4419926, by rfl⟩ : syracuseStep 5893235 = 8839853) B8839853
theorem B5958845 : Blo 515797 5958845 := bstep (se 3 (by rfl) ⟨1117283, by rfl⟩ : syracuseStep 5958845 = 2234567) B2234567
theorem B519551 : Blo 515797 519551 := bstep (se 1 (by rfl) ⟨389663, by rfl⟩ : syracuseStep 519551 = 779327) B779327
theorem B519579 : Blo 515797 519579 := bstep (se 1 (by rfl) ⟨389684, by rfl⟩ : syracuseStep 519579 = 779369) B779369
theorem B1961405 : Blo 515797 1961405 := bstep (se 3 (by rfl) ⟨367763, by rfl⟩ : syracuseStep 1961405 = 735527) B735527
theorem B1109459 : Blo 515797 1109459 := bstep (se 1 (by rfl) ⟨832094, by rfl⟩ : syracuseStep 1109459 = 1664189) B1664189
theorem B519647 : Blo 515797 519647 := bstep (se 1 (by rfl) ⟨389735, by rfl⟩ : syracuseStep 519647 = 779471) B779471
theorem B4714075 : Blo 515797 4714075 := bstep (se 1 (by rfl) ⟨3535556, by rfl⟩ : syracuseStep 4714075 = 7071113) B7071113
theorem B519783 : Blo 515797 519783 := bstep (se 1 (by rfl) ⟨389837, by rfl⟩ : syracuseStep 519783 = 779675) B779675
theorem B1240895 : Blo 515797 1240895 := bstep (se 1 (by rfl) ⟨930671, by rfl⟩ : syracuseStep 1240895 = 1861343) B1861343
theorem B553115 : Blo 515797 553115 := bstep (se 1 (by rfl) ⟨414836, by rfl⟩ : syracuseStep 553115 = 829673) B829673
theorem B51212569 : Blo 515797 51212569 := bstep (se 2 (by rfl) ⟨19204713, by rfl⟩ : syracuseStep 51212569 = 38409427) B38409427
theorem B1307087 : Blo 515797 1307087 := bstep (se 1 (by rfl) ⟨980315, by rfl⟩ : syracuseStep 1307087 = 1960631) B1960631
theorem B1962575 : Blo 515797 1962575 := bstep (se 1 (by rfl) ⟨1471931, by rfl⟩ : syracuseStep 1962575 = 2943863) B2943863
theorem B8417945 : Blo 515797 8417945 := bstep (se 2 (by rfl) ⟨3156729, by rfl⟩ : syracuseStep 8417945 = 6313459) B6313459
theorem B4715243 : Blo 515797 4715243 := bstep (se 1 (by rfl) ⟨3536432, by rfl⟩ : syracuseStep 4715243 = 7072865) B7072865
theorem B8844227 : Blo 515797 8844227 := bstep (se 1 (by rfl) ⟨6633170, by rfl⟩ : syracuseStep 8844227 = 13266341) B13266341
theorem B1308251 : Blo 515797 1308251 := bstep (se 1 (by rfl) ⟨981188, by rfl⟩ : syracuseStep 1308251 = 1962377) B1962377
theorem B1308271 : Blo 515797 1308271 := bstep (se 1 (by rfl) ⟨981203, by rfl⟩ : syracuseStep 1308271 = 1962407) B1962407
theorem B3307463 : Blo 515797 3307463 := bstep (se 1 (by rfl) ⟨2480597, by rfl⟩ : syracuseStep 3307463 = 4961195) B4961195
theorem B981227 : Blo 515797 981227 := bstep (se 1 (by rfl) ⟨735920, by rfl⟩ : syracuseStep 981227 = 1471841) B1471841
theorem B3307823 : Blo 515797 3307823 := bstep (se 1 (by rfl) ⟨2480867, by rfl⟩ : syracuseStep 3307823 = 4961735) B4961735
theorem B784847 : Blo 515797 784847 := bstep (se 1 (by rfl) ⟨588635, by rfl⟩ : syracuseStep 784847 = 1177271) B1177271
theorem B1866331 : Blo 515797 1866331 := bstep (se 1 (by rfl) ⟨1399748, by rfl⟩ : syracuseStep 1866331 = 2799497) B2799497
theorem B4717291 : Blo 515797 4717291 := bstep (se 1 (by rfl) ⟨3537968, by rfl⟩ : syracuseStep 4717291 = 7075937) B7075937
theorem B654247 : Blo 515797 654247 := bstep (se 1 (by rfl) ⟨490685, by rfl⟩ : syracuseStep 654247 = 981371) B981371
theorem B1179049 : Blo 515797 1179049 := bstep (se 2 (by rfl) ⟨442143, by rfl⟩ : syracuseStep 1179049 = 884287) B884287
theorem B654799 : Blo 515797 654799 := bstep (se 1 (by rfl) ⟨491099, by rfl⟩ : syracuseStep 654799 = 982199) B982199
theorem B1572527 : Blo 515797 1572527 := bstep (se 1 (by rfl) ⟨1179395, by rfl⟩ : syracuseStep 1572527 = 2358791) B2358791
theorem B2621159 : Blo 515797 2621159 := bstep (se 1 (by rfl) ⟨1965869, by rfl⟩ : syracuseStep 2621159 = 3931739) B3931739
theorem B2948987 : Blo 515797 2948987 := bstep (se 1 (by rfl) ⟨2211740, by rfl⟩ : syracuseStep 2948987 = 4423481) B4423481
theorem B1310843 : Blo 515797 1310843 := bstep (se 1 (by rfl) ⟨983132, by rfl⟩ : syracuseStep 1310843 = 1966265) B1966265
theorem B1310975 : Blo 515797 1310975 := bstep (se 1 (by rfl) ⟨983231, by rfl⟩ : syracuseStep 1310975 = 1966463) B1966463
theorem B983353 : Blo 515797 983353 := bstep (se 2 (by rfl) ⟨368757, by rfl⟩ : syracuseStep 983353 = 737515) B737515
theorem B12616019 : Blo 515797 12616019 := bstep (se 1 (by rfl) ⟨9462014, by rfl⟩ : syracuseStep 12616019 = 18924029) B18924029
theorem B655771 : Blo 515797 655771 := bstep (se 1 (by rfl) ⟨491828, by rfl⟩ : syracuseStep 655771 = 983657) B983657
theorem B1474973 : Blo 515797 1474973 := bstep (se 3 (by rfl) ⟨276557, by rfl⟩ : syracuseStep 1474973 = 553115) B553115
theorem B786971 : Blo 515797 786971 := bstep (se 1 (by rfl) ⟨590228, by rfl⟩ : syracuseStep 786971 = 1180457) B1180457
theorem B1180217 : Blo 515797 1180217 := bstep (se 2 (by rfl) ⟨442581, by rfl⟩ : syracuseStep 1180217 = 885163) B885163
theorem B656039 : Blo 515797 656039 := bstep (se 1 (by rfl) ⟨492029, by rfl⟩ : syracuseStep 656039 = 984059) B984059
theorem B656191 : Blo 515797 656191 := bstep (se 1 (by rfl) ⟨492143, by rfl⟩ : syracuseStep 656191 = 984287) B984287
theorem B656363 : Blo 515797 656363 := bstep (se 1 (by rfl) ⟨492272, by rfl⟩ : syracuseStep 656363 = 984545) B984545
theorem B13240097 : Blo 515797 13240097 := bstep (se 2 (by rfl) ⟨4965036, by rfl⟩ : syracuseStep 13240097 = 9930073) B9930073
theorem B13305707 : Blo 515797 13305707 := bstep (se 1 (by rfl) ⟨9979280, by rfl⟩ : syracuseStep 13305707 = 19958561) B19958561
theorem B657659 : Blo 515797 657659 := bstep (se 1 (by rfl) ⟨493244, by rfl⟩ : syracuseStep 657659 = 986489) B986489
theorem B559783 : Blo 515797 559783 := bstep (se 1 (by rfl) ⟨419837, by rfl⟩ : syracuseStep 559783 = 839675) B839675
theorem B1314407 : Blo 515797 1314407 := bstep (se 1 (by rfl) ⟨985805, by rfl⟩ : syracuseStep 1314407 = 1971611) B1971611
theorem B1314751 : Blo 515797 1314751 := bstep (se 1 (by rfl) ⟨986063, by rfl⟩ : syracuseStep 1314751 = 1972127) B1972127
theorem B7573499 : Blo 515797 7573499 := bstep (se 1 (by rfl) ⟨5680124, by rfl⟩ : syracuseStep 7573499 = 11360249) B11360249
theorem B1478891 : Blo 515797 1478891 := bstep (se 1 (by rfl) ⟨1109168, by rfl⟩ : syracuseStep 1478891 = 2218337) B2218337
theorem B2494745 : Blo 515797 2494745 := bstep (se 2 (by rfl) ⟨935529, by rfl⟩ : syracuseStep 2494745 = 1871059) B1871059
theorem B1970639 : Blo 515797 1970639 := bstep (se 1 (by rfl) ⟨1477979, by rfl⟩ : syracuseStep 1970639 = 2955959) B2955959
theorem B1971323 : Blo 515797 1971323 := bstep (se 1 (by rfl) ⟨1478492, by rfl⟩ : syracuseStep 1971323 = 2956985) B2956985
theorem B3315127 : Blo 515797 3315127 := bstep (se 1 (by rfl) ⟨2486345, by rfl⟩ : syracuseStep 3315127 = 4972691) B4972691
theorem B1873367 : Blo 515797 1873367 := bstep (se 1 (by rfl) ⟨1405025, by rfl⟩ : syracuseStep 1873367 = 2810051) B2810051
theorem B2790931 : Blo 515797 2790931 := bstep (se 1 (by rfl) ⟨2093198, by rfl⟩ : syracuseStep 2790931 = 4186397) B4186397
theorem B2627153 : Blo 515797 2627153 := bstep (se 2 (by rfl) ⟨985182, by rfl⟩ : syracuseStep 2627153 = 1970365) B1970365
theorem B5609195 : Blo 515797 5609195 := bstep (se 1 (by rfl) ⟨4206896, by rfl⟩ : syracuseStep 5609195 = 8413793) B8413793
theorem B2627315 : Blo 515797 2627315 := bstep (se 1 (by rfl) ⟨1970486, by rfl⟩ : syracuseStep 2627315 = 3940973) B3940973
theorem B4986953 : Blo 515797 4986953 := bstep (se 2 (by rfl) ⟨1870107, by rfl⟩ : syracuseStep 4986953 = 3740215) B3740215
theorem B99359227 : Blo 515797 99359227 := bstep (se 1 (by rfl) ⟨74519420, by rfl⟩ : syracuseStep 99359227 = 149038841) B149038841
theorem B4987453 : Blo 515797 4987453 := bstep (se 3 (by rfl) ⟨935147, by rfl⟩ : syracuseStep 4987453 = 1870295) B1870295
theorem B3546287 : Blo 515797 3546287 := bstep (se 1 (by rfl) ⟨2659715, by rfl⟩ : syracuseStep 3546287 = 5319431) B5319431
theorem B14916797 : Blo 515797 14916797 := bstep (se 3 (by rfl) ⟨2796899, by rfl⟩ : syracuseStep 14916797 = 5593799) B5593799
theorem B2628935 : Blo 515797 2628935 := bstep (se 1 (by rfl) ⟨1971701, by rfl⟩ : syracuseStep 2628935 = 3943403) B3943403
theorem B3972563 : Blo 515797 3972563 := bstep (se 1 (by rfl) ⟨2979422, by rfl⟩ : syracuseStep 3972563 = 5958845) B5958845
theorem B1744361 : Blo 515797 1744361 := bstep (se 2 (by rfl) ⟨654135, by rfl⟩ : syracuseStep 1744361 = 1308271) B1308271
theorem B827263 : Blo 515797 827263 := bstep (se 1 (by rfl) ⟨620447, by rfl⟩ : syracuseStep 827263 = 1240895) B1240895
theorem B3153791 : Blo 515797 3153791 := bstep (se 1 (by rfl) ⟨2365343, by rfl⟩ : syracuseStep 3153791 = 4730687) B4730687
theorem B3350879 : Blo 515797 3350879 := bstep (se 1 (by rfl) ⟨2513159, by rfl⟩ : syracuseStep 3350879 = 5026319) B5026319
theorem B5611963 : Blo 515797 5611963 := bstep (se 1 (by rfl) ⟨4208972, by rfl⟩ : syracuseStep 5611963 = 8417945) B8417945
theorem B2958443 : Blo 515797 2958443 := bstep (se 1 (by rfl) ⟨2218832, by rfl⟩ : syracuseStep 2958443 = 4437665) B4437665
theorem B2204975 : Blo 515797 2204975 := bstep (se 1 (by rfl) ⟨1653731, by rfl⟩ : syracuseStep 2204975 = 3307463) B3307463
theorem B2205215 : Blo 515797 2205215 := bstep (se 1 (by rfl) ⟨1653911, by rfl⟩ : syracuseStep 2205215 = 3307823) B3307823
theorem B5318939 : Blo 515797 5318939 := bstep (se 1 (by rfl) ⟨3989204, by rfl⟩ : syracuseStep 5318939 = 7978409) B7978409
theorem B13478345 : Blo 515797 13478345 := bstep (se 2 (by rfl) ⟨5054379, by rfl⟩ : syracuseStep 13478345 = 10108759) B10108759
theorem B1747439 : Blo 515797 1747439 := bstep (se 1 (by rfl) ⟨1310579, by rfl⟩ : syracuseStep 1747439 = 2621159) B2621159
theorem B1747871 : Blo 515797 1747871 := bstep (se 1 (by rfl) ⟨1310903, by rfl⟩ : syracuseStep 1747871 = 2621807) B2621807
theorem B5615077 : Blo 515797 5615077 := bstep (se 4 (by rfl) ⟨526413, by rfl⟩ : syracuseStep 5615077 = 1052827) B1052827
theorem B2240399 : Blo 515797 2240399 := bstep (se 1 (by rfl) ⟨1680299, by rfl⟩ : syracuseStep 2240399 = 3360599) B3360599
theorem B4993103 : Blo 515797 4993103 := bstep (se 1 (by rfl) ⟨3744827, by rfl⟩ : syracuseStep 4993103 = 7489655) B7489655
theorem B4731301 : Blo 515797 4731301 := bstep (se 4 (by rfl) ⟨443559, by rfl⟩ : syracuseStep 4731301 = 887119) B887119
theorem B1749815 : Blo 515797 1749815 := bstep (se 1 (by rfl) ⟨1312361, by rfl⟩ : syracuseStep 1749815 = 2624723) B2624723
theorem B1160783 : Blo 515797 1160783 := bstep (se 1 (by rfl) ⟨870587, by rfl⟩ : syracuseStep 1160783 = 1741175) B1741175
theorem B1161323 : Blo 515797 1161323 := bstep (se 1 (by rfl) ⟨870992, by rfl⟩ : syracuseStep 1161323 = 1741985) B1741985
theorem B1685627 : Blo 515797 1685627 := bstep (se 1 (by rfl) ⟨1264220, by rfl⟩ : syracuseStep 1685627 = 2528441) B2528441
theorem B1751165 : Blo 515797 1751165 := bstep (se 3 (by rfl) ⟨328343, by rfl⟩ : syracuseStep 1751165 = 656687) B656687
theorem B1161503 : Blo 515797 1161503 := bstep (se 1 (by rfl) ⟨871127, by rfl⟩ : syracuseStep 1161503 = 1742255) B1742255
theorem B1751327 : Blo 515797 1751327 := bstep (se 1 (by rfl) ⟨1313495, by rfl⟩ : syracuseStep 1751327 = 2626991) B2626991
theorem B2210273 : Blo 515797 2210273 := bstep (se 2 (by rfl) ⟨828852, by rfl⟩ : syracuseStep 2210273 = 1657705) B1657705
theorem B1161719 : Blo 515797 1161719 := bstep (se 1 (by rfl) ⟨871289, by rfl⟩ : syracuseStep 1161719 = 1742579) B1742579
theorem B7945147 : Blo 515797 7945147 := bstep (se 1 (by rfl) ⟨5958860, by rfl⟩ : syracuseStep 7945147 = 11917721) B11917721
theorem B1162223 : Blo 515797 1162223 := bstep (se 1 (by rfl) ⟨871667, by rfl⟩ : syracuseStep 1162223 = 1743335) B1743335
theorem B3783827 : Blo 515797 3783827 := bstep (se 1 (by rfl) ⟨2837870, by rfl⟩ : syracuseStep 3783827 = 5675741) B5675741
theorem B1162799 : Blo 515797 1162799 := bstep (se 1 (by rfl) ⟨872099, by rfl⟩ : syracuseStep 1162799 = 1744199) B1744199
theorem B1163231 : Blo 515797 1163231 := bstep (se 1 (by rfl) ⟨872423, by rfl⟩ : syracuseStep 1163231 = 1744847) B1744847
theorem B25182211 : Blo 515797 25182211 := bstep (se 1 (by rfl) ⟨18886658, by rfl⟩ : syracuseStep 25182211 = 37773317) B37773317
theorem B18890759 : Blo 515797 18890759 := bstep (se 1 (by rfl) ⟨14168069, by rfl⟩ : syracuseStep 18890759 = 28336139) B28336139
theorem B34030199 : Blo 515797 34030199 := bstep (se 1 (by rfl) ⟨25522649, by rfl⟩ : syracuseStep 34030199 = 51045299) B51045299
theorem B130892591 : Blo 515797 130892591 := bstep (se 1 (by rfl) ⟨98169443, by rfl⟩ : syracuseStep 130892591 = 196338887) B196338887
theorem B18236573 : Blo 515797 18236573 := bstep (se 3 (by rfl) ⟨3419357, by rfl⟩ : syracuseStep 18236573 = 6838715) B6838715
theorem B2213689 : Blo 515797 2213689 := bstep (se 2 (by rfl) ⟨830133, by rfl⟩ : syracuseStep 2213689 = 1660267) B1660267
theorem B3328067 : Blo 515797 3328067 := bstep (se 1 (by rfl) ⟨2496050, by rfl⟩ : syracuseStep 3328067 = 4992101) B4992101
theorem B739639 : Blo 515797 739639 := bstep (se 1 (by rfl) ⟨554729, by rfl⟩ : syracuseStep 739639 = 1109459) B1109459
theorem B12568931 : Blo 515797 12568931 := bstep (se 1 (by rfl) ⟨9426698, by rfl⟩ : syracuseStep 12568931 = 18853397) B18853397
theorem B871391 : Blo 515797 871391 := bstep (se 1 (by rfl) ⟨653543, by rfl⟩ : syracuseStep 871391 = 1307087) B1307087
theorem B21285935 : Blo 515797 21285935 := bstep (se 1 (by rfl) ⟨15964451, by rfl⟩ : syracuseStep 21285935 = 31928903) B31928903
theorem B2215021 : Blo 515797 2215021 := bstep (se 3 (by rfl) ⟨415316, by rfl⟩ : syracuseStep 2215021 = 830633) B830633
theorem B872167 : Blo 515797 872167 := bstep (se 1 (by rfl) ⟨654125, by rfl⟩ : syracuseStep 872167 = 1308251) B1308251
theorem B773897 : Blo 515797 773897 := bstep (se 2 (by rfl) ⟨290211, by rfl⟩ : syracuseStep 773897 = 580423) B580423
theorem B773951 : Blo 515797 773951 := bstep (se 1 (by rfl) ⟨580463, by rfl⟩ : syracuseStep 773951 = 1160927) B1160927
theorem B872329 : Blo 515797 872329 := bstep (se 2 (by rfl) ⟨327123, by rfl⟩ : syracuseStep 872329 = 654247) B654247
theorem B25546711 : Blo 515797 25546711 := bstep (se 1 (by rfl) ⟨19160033, by rfl⟩ : syracuseStep 25546711 = 38320067) B38320067
theorem B774191 : Blo 515797 774191 := bstep (se 1 (by rfl) ⟨580643, by rfl⟩ : syracuseStep 774191 = 1161287) B1161287
theorem B1167407 : Blo 515797 1167407 := bstep (se 1 (by rfl) ⟨875555, by rfl⟩ : syracuseStep 1167407 = 1751111) B1751111
theorem B774635 : Blo 515797 774635 := bstep (se 1 (by rfl) ⟨580976, by rfl⟩ : syracuseStep 774635 = 1161953) B1161953
theorem B774761 : Blo 515797 774761 := bstep (se 2 (by rfl) ⟨290535, by rfl⟩ : syracuseStep 774761 = 581071) B581071
theorem B873065 : Blo 515797 873065 := bstep (se 2 (by rfl) ⟨327399, by rfl⟩ : syracuseStep 873065 = 654799) B654799
theorem B774767 : Blo 515797 774767 := bstep (se 1 (by rfl) ⟨581075, by rfl⟩ : syracuseStep 774767 = 1162151) B1162151
theorem B1167983 : Blo 515797 1167983 := bstep (se 1 (by rfl) ⟨875987, by rfl⟩ : syracuseStep 1167983 = 1751975) B1751975
theorem B774887 : Blo 515797 774887 := bstep (se 1 (by rfl) ⟨581165, by rfl⟩ : syracuseStep 774887 = 1162331) B1162331
theorem B775049 : Blo 515797 775049 := bstep (se 2 (by rfl) ⟨290643, by rfl⟩ : syracuseStep 775049 = 581287) B581287
theorem B775391 : Blo 515797 775391 := bstep (se 1 (by rfl) ⟨581543, by rfl⟩ : syracuseStep 775391 = 1163087) B1163087
theorem B775433 : Blo 515797 775433 := bstep (se 2 (by rfl) ⟨290787, by rfl⟩ : syracuseStep 775433 = 581575) B581575
theorem B775871 : Blo 515797 775871 := bstep (se 1 (by rfl) ⟨581903, by rfl⟩ : syracuseStep 775871 = 1163807) B1163807
theorem B775913 : Blo 515797 775913 := bstep (se 2 (by rfl) ⟨290967, by rfl⟩ : syracuseStep 775913 = 581935) B581935
theorem B775919 : Blo 515797 775919 := bstep (se 1 (by rfl) ⟨581939, by rfl⟩ : syracuseStep 775919 = 1163879) B1163879
theorem B1169135 : Blo 515797 1169135 := bstep (se 1 (by rfl) ⟨876851, by rfl⟩ : syracuseStep 1169135 = 1753703) B1753703
theorem B2938781 : Blo 515797 2938781 := bstep (se 3 (by rfl) ⟨551021, by rfl⟩ : syracuseStep 2938781 = 1102043) B1102043
theorem B2938963 : Blo 515797 2938963 := bstep (se 1 (by rfl) ⟨2204222, by rfl⟩ : syracuseStep 2938963 = 4408445) B4408445
theorem B776423 : Blo 515797 776423 := bstep (se 1 (by rfl) ⟨582317, by rfl⟩ : syracuseStep 776423 = 1164635) B1164635
theorem B776603 : Blo 515797 776603 := bstep (se 1 (by rfl) ⟨582452, by rfl⟩ : syracuseStep 776603 = 1164905) B1164905
theorem B21813683 : Blo 515797 21813683 := bstep (se 1 (by rfl) ⟨16360262, by rfl⟩ : syracuseStep 21813683 = 32720525) B32720525
theorem B76897025 : Blo 515797 76897025 := bstep (se 2 (by rfl) ⟨28836384, by rfl⟩ : syracuseStep 76897025 = 57672769) B57672769
theorem B776999 : Blo 515797 776999 := bstep (se 1 (by rfl) ⟨582749, by rfl⟩ : syracuseStep 776999 = 1165499) B1165499
theorem B777023 : Blo 515797 777023 := bstep (se 1 (by rfl) ⟨582767, by rfl⟩ : syracuseStep 777023 = 1165535) B1165535
theorem B777323 : Blo 515797 777323 := bstep (se 1 (by rfl) ⟨582992, by rfl⟩ : syracuseStep 777323 = 1165985) B1165985
theorem B777467 : Blo 515797 777467 := bstep (se 1 (by rfl) ⟨583100, by rfl⟩ : syracuseStep 777467 = 1166201) B1166201
theorem B580891 : Blo 515797 580891 := bstep (se 1 (by rfl) ⟨435668, by rfl⟩ : syracuseStep 580891 = 871337) B871337
theorem B777563 : Blo 515797 777563 := bstep (se 1 (by rfl) ⟨583172, by rfl⟩ : syracuseStep 777563 = 1166345) B1166345
theorem B777593 : Blo 515797 777593 := bstep (se 2 (by rfl) ⟨291597, by rfl⟩ : syracuseStep 777593 = 583195) B583195
theorem B777599 : Blo 515797 777599 := bstep (se 1 (by rfl) ⟨583199, by rfl⟩ : syracuseStep 777599 = 1166399) B1166399
theorem B1662383 : Blo 515797 1662383 := bstep (se 1 (by rfl) ⟨1246787, by rfl⟩ : syracuseStep 1662383 = 2493575) B2493575
theorem B515823 : Blo 515797 515823 := bstep (se 1 (by rfl) ⟨386867, by rfl⟩ : syracuseStep 515823 = 773735) B773735
theorem B581359 : Blo 515797 581359 := bstep (se 1 (by rfl) ⟨436019, by rfl⟩ : syracuseStep 581359 = 872039) B872039
theorem B22667141 : Blo 515797 22667141 := bstep (se 4 (by rfl) ⟨2125044, by rfl⟩ : syracuseStep 22667141 = 4250089) B4250089
theorem B1400743 : Blo 515797 1400743 := bstep (se 1 (by rfl) ⟨1050557, by rfl⟩ : syracuseStep 1400743 = 2101115) B2101115
theorem B778151 : Blo 515797 778151 := bstep (se 1 (by rfl) ⟨583613, by rfl⟩ : syracuseStep 778151 = 1167227) B1167227
theorem B2023379 : Blo 515797 2023379 := bstep (se 1 (by rfl) ⟨1517534, by rfl⟩ : syracuseStep 2023379 = 3035069) B3035069
theorem B516079 : Blo 515797 516079 := bstep (se 1 (by rfl) ⟨387059, by rfl⟩ : syracuseStep 516079 = 774119) B774119
theorem B778223 : Blo 515797 778223 := bstep (se 1 (by rfl) ⟨583667, by rfl⟩ : syracuseStep 778223 = 1167335) B1167335
theorem B516159 : Blo 515797 516159 := bstep (se 1 (by rfl) ⟨387119, by rfl⟩ : syracuseStep 516159 = 774239) B774239
theorem B843839 : Blo 515797 843839 := bstep (se 1 (by rfl) ⟨632879, by rfl⟩ : syracuseStep 843839 = 1265759) B1265759
theorem B516167 : Blo 515797 516167 := bstep (se 1 (by rfl) ⟨387125, by rfl⟩ : syracuseStep 516167 = 774251) B774251
theorem B516199 : Blo 515797 516199 := bstep (se 1 (by rfl) ⟨387149, by rfl⟩ : syracuseStep 516199 = 774299) B774299
theorem B778343 : Blo 515797 778343 := bstep (se 1 (by rfl) ⟨583757, by rfl⟩ : syracuseStep 778343 = 1167515) B1167515
theorem B778475 : Blo 515797 778475 := bstep (se 1 (by rfl) ⟨583856, by rfl⟩ : syracuseStep 778475 = 1167713) B1167713
theorem B778535 : Blo 515797 778535 := bstep (se 1 (by rfl) ⟨583901, by rfl⟩ : syracuseStep 778535 = 1167803) B1167803
theorem B516767 : Blo 515797 516767 := bstep (se 1 (by rfl) ⟨387575, by rfl⟩ : syracuseStep 516767 = 775151) B775151
theorem B778985 : Blo 515797 778985 := bstep (se 2 (by rfl) ⟨292119, by rfl⟩ : syracuseStep 778985 = 584239) B584239
theorem B517023 : Blo 515797 517023 := bstep (se 1 (by rfl) ⟨387767, by rfl⟩ : syracuseStep 517023 = 775535) B775535
theorem B517103 : Blo 515797 517103 := bstep (se 1 (by rfl) ⟨387827, by rfl⟩ : syracuseStep 517103 = 775655) B775655
theorem B1401911 : Blo 515797 1401911 := bstep (se 1 (by rfl) ⟨1051433, by rfl⟩ : syracuseStep 1401911 = 2102867) B2102867
theorem B517211 : Blo 515797 517211 := bstep (se 1 (by rfl) ⟨387908, by rfl⟩ : syracuseStep 517211 = 775817) B775817
theorem B517223 : Blo 515797 517223 := bstep (se 1 (by rfl) ⟨387917, by rfl⟩ : syracuseStep 517223 = 775835) B775835
theorem B779375 : Blo 515797 779375 := bstep (se 1 (by rfl) ⟨584531, by rfl⟩ : syracuseStep 779375 = 1169063) B1169063
theorem B517351 : Blo 515797 517351 := bstep (se 1 (by rfl) ⟨388013, by rfl⟩ : syracuseStep 517351 = 776027) B776027
theorem B779495 : Blo 515797 779495 := bstep (se 1 (by rfl) ⟨584621, by rfl⟩ : syracuseStep 779495 = 1169243) B1169243
theorem B779561 : Blo 515797 779561 := bstep (se 2 (by rfl) ⟨292335, by rfl⟩ : syracuseStep 779561 = 584671) B584671
theorem B4973957 : Blo 515797 4973957 := bstep (se 4 (by rfl) ⟨466308, by rfl⟩ : syracuseStep 4973957 = 932617) B932617
theorem B517607 : Blo 515797 517607 := bstep (se 1 (by rfl) ⟨388205, by rfl⟩ : syracuseStep 517607 = 776411) B776411
theorem B517787 : Blo 515797 517787 := bstep (se 1 (by rfl) ⟨388340, by rfl⟩ : syracuseStep 517787 = 776681) B776681
theorem B518047 : Blo 515797 518047 := bstep (se 1 (by rfl) ⟨388535, by rfl⟩ : syracuseStep 518047 = 777071) B777071
theorem B518055 : Blo 515797 518055 := bstep (se 1 (by rfl) ⟨388541, by rfl⟩ : syracuseStep 518055 = 777083) B777083
theorem B583591 : Blo 515797 583591 := bstep (se 1 (by rfl) ⟨437693, by rfl⟩ : syracuseStep 583591 = 875387) B875387
theorem B6285433 : Blo 515797 6285433 := bstep (se 2 (by rfl) ⟨2357037, by rfl⟩ : syracuseStep 6285433 = 4714075) B4714075
theorem B518631 : Blo 515797 518631 := bstep (se 1 (by rfl) ⟨388973, by rfl⟩ : syracuseStep 518631 = 777947) B777947
theorem B584167 : Blo 515797 584167 := bstep (se 1 (by rfl) ⟨438125, by rfl⟩ : syracuseStep 584167 = 876251) B876251
theorem B1468925 : Blo 515797 1468925 := bstep (se 3 (by rfl) ⟨275423, by rfl⟩ : syracuseStep 1468925 = 550847) B550847
theorem B22309451 : Blo 515797 22309451 := bstep (se 1 (by rfl) ⟨16732088, by rfl⟩ : syracuseStep 22309451 = 33464177) B33464177
theorem B518811 : Blo 515797 518811 := bstep (se 1 (by rfl) ⟨389108, by rfl⟩ : syracuseStep 518811 = 778217) B778217
theorem B584347 : Blo 515797 584347 := bstep (se 1 (by rfl) ⟨438260, by rfl⟩ : syracuseStep 584347 = 876521) B876521
theorem B68283425 : Blo 515797 68283425 := bstep (se 2 (by rfl) ⟨25606284, by rfl⟩ : syracuseStep 68283425 = 51212569) B51212569
theorem B519279 : Blo 515797 519279 := bstep (se 1 (by rfl) ⟨389459, by rfl⟩ : syracuseStep 519279 = 778919) B778919
theorem B1305791 : Blo 515797 1305791 := bstep (se 1 (by rfl) ⟨979343, by rfl⟩ : syracuseStep 1305791 = 1958687) B1958687
theorem B519359 : Blo 515797 519359 := bstep (se 1 (by rfl) ⟨389519, by rfl⟩ : syracuseStep 519359 = 779039) B779039
theorem B519375 : Blo 515797 519375 := bstep (se 1 (by rfl) ⟨389531, by rfl⟩ : syracuseStep 519375 = 779063) B779063
theorem B13495567 : Blo 515797 13495567 := bstep (se 1 (by rfl) ⟨10121675, by rfl⟩ : syracuseStep 13495567 = 20243351) B20243351
theorem B519495 : Blo 515797 519495 := bstep (se 1 (by rfl) ⟨389621, by rfl⟩ : syracuseStep 519495 = 779243) B779243
theorem B12610961 : Blo 515797 12610961 := bstep (se 2 (by rfl) ⟨4729110, by rfl⟩ : syracuseStep 12610961 = 9458221) B9458221
theorem B1306439 : Blo 515797 1306439 := bstep (se 1 (by rfl) ⟨979829, by rfl⟩ : syracuseStep 1306439 = 1959659) B1959659
theorem B2092925 : Blo 515797 2092925 := bstep (se 3 (by rfl) ⟨392423, by rfl⟩ : syracuseStep 2092925 = 784847) B784847
theorem B1241183 : Blo 515797 1241183 := bstep (se 1 (by rfl) ⟨930887, by rfl⟩ : syracuseStep 1241183 = 1861775) B1861775
theorem B1306763 : Blo 515797 1306763 := bstep (se 1 (by rfl) ⟨980072, by rfl⟩ : syracuseStep 1306763 = 1960145) B1960145
theorem B7565501 : Blo 515797 7565501 := bstep (se 3 (by rfl) ⟨1418531, by rfl⟩ : syracuseStep 7565501 = 2837063) B2837063
theorem B19919195 : Blo 515797 19919195 := bstep (se 1 (by rfl) ⟨14939396, by rfl⟩ : syracuseStep 19919195 = 29878793) B29878793
theorem B1306975 : Blo 515797 1306975 := bstep (se 1 (by rfl) ⟨980231, by rfl⟩ : syracuseStep 1306975 = 1960463) B1960463
theorem B3928823 : Blo 515797 3928823 := bstep (se 1 (by rfl) ⟨2946617, by rfl⟩ : syracuseStep 3928823 = 5893235) B5893235
theorem B1307603 : Blo 515797 1307603 := bstep (se 1 (by rfl) ⟨980702, by rfl⟩ : syracuseStep 1307603 = 1961405) B1961405
theorem B1308383 : Blo 515797 1308383 := bstep (se 1 (by rfl) ⟨981287, by rfl⟩ : syracuseStep 1308383 = 1962575) B1962575
theorem B3143495 : Blo 515797 3143495 := bstep (se 1 (by rfl) ⟨2357621, by rfl⟩ : syracuseStep 3143495 = 4715243) B4715243
theorem B5896151 : Blo 515797 5896151 := bstep (se 1 (by rfl) ⟨4422113, by rfl⟩ : syracuseStep 5896151 = 8844227) B8844227
theorem B2488441 : Blo 515797 2488441 := bstep (se 2 (by rfl) ⟨933165, by rfl⟩ : syracuseStep 2488441 = 1866331) B1866331
theorem B6289721 : Blo 515797 6289721 := bstep (se 2 (by rfl) ⟨2358645, by rfl⟩ : syracuseStep 6289721 = 4717291) B4717291
theorem B654151 : Blo 515797 654151 := bstep (se 1 (by rfl) ⟨490613, by rfl⟩ : syracuseStep 654151 = 981227) B981227
theorem B8879219 : Blo 515797 8879219 := bstep (se 1 (by rfl) ⟨6659414, by rfl⟩ : syracuseStep 8879219 = 13318829) B13318829
theorem B1572065 : Blo 515797 1572065 := bstep (se 2 (by rfl) ⟨589524, by rfl⟩ : syracuseStep 1572065 = 1179049) B1179049
theorem B1473947 : Blo 515797 1473947 := bstep (se 1 (by rfl) ⟨1105460, by rfl⟩ : syracuseStep 1473947 = 2210921) B2210921
theorem B1048351 : Blo 515797 1048351 := bstep (se 1 (by rfl) ⟨786263, by rfl⟩ : syracuseStep 1048351 = 1572527) B1572527
theorem B1965991 : Blo 515797 1965991 := bstep (se 1 (by rfl) ⟨1474493, by rfl⟩ : syracuseStep 1965991 = 2948987) B2948987
theorem B3735517 : Blo 515797 3735517 := bstep (se 3 (by rfl) ⟨700409, by rfl⟩ : syracuseStep 3735517 = 1400819) B1400819
theorem B3309821 : Blo 515797 3309821 := bstep (se 3 (by rfl) ⟨620591, by rfl⟩ : syracuseStep 3309821 = 1241183) B1241183
theorem B983315 : Blo 515797 983315 := bstep (se 1 (by rfl) ⟨737486, by rfl⟩ : syracuseStep 983315 = 1474973) B1474973
theorem B524647 : Blo 515797 524647 := bstep (se 1 (by rfl) ⟨393485, by rfl⟩ : syracuseStep 524647 = 786971) B786971
theorem B1311137 : Blo 515797 1311137 := bstep (se 2 (by rfl) ⟨491676, by rfl⟩ : syracuseStep 1311137 = 983353) B983353
theorem B12157715 : Blo 515797 12157715 := bstep (se 1 (by rfl) ⟨9118286, by rfl⟩ : syracuseStep 12157715 = 18236573) B18236573
theorem B3147245 : Blo 515797 3147245 := bstep (se 3 (by rfl) ⟨590108, by rfl⟩ : syracuseStep 3147245 = 1180217) B1180217
theorem B14190623 : Blo 515797 14190623 := bstep (se 1 (by rfl) ⟨10642967, by rfl⟩ : syracuseStep 14190623 = 21285935) B21285935
theorem B349046909 : Blo 515797 349046909 := bstep (se 3 (by rfl) ⟨65446295, by rfl⟩ : syracuseStep 349046909 = 130892591) B130892591
theorem B25233605 : Blo 515797 25233605 := bstep (se 4 (by rfl) ⟨2365650, by rfl⟩ : syracuseStep 25233605 = 4731301) B4731301
theorem B2951585 : Blo 515797 2951585 := bstep (se 2 (by rfl) ⟨1106844, by rfl⟩ : syracuseStep 2951585 = 2213689) B2213689
theorem B5048999 : Blo 515797 5048999 := bstep (se 1 (by rfl) ⟨3786749, by rfl⟩ : syracuseStep 5048999 = 7573499) B7573499
theorem B985927 : Blo 515797 985927 := bstep (se 1 (by rfl) ⟨739445, by rfl⟩ : syracuseStep 985927 = 1478891) B1478891
theorem B1313759 : Blo 515797 1313759 := bstep (se 1 (by rfl) ⟨985319, by rfl⟩ : syracuseStep 1313759 = 1970639) B1970639
theorem B986185 : Blo 515797 986185 := bstep (se 2 (by rfl) ⟨369819, by rfl⟩ : syracuseStep 986185 = 739639) B739639
theorem B1314215 : Blo 515797 1314215 := bstep (se 1 (by rfl) ⟨985661, by rfl⟩ : syracuseStep 1314215 = 1971323) B1971323
theorem B1248911 : Blo 515797 1248911 := bstep (se 1 (by rfl) ⟨936683, by rfl⟩ : syracuseStep 1248911 = 1873367) B1873367
theorem B3739463 : Blo 515797 3739463 := bstep (se 1 (by rfl) ⟨2804597, by rfl⟩ : syracuseStep 3739463 = 5609195) B5609195
theorem B2953361 : Blo 515797 2953361 := bstep (se 2 (by rfl) ⟨1107510, by rfl⟩ : syracuseStep 2953361 = 2215021) B2215021
theorem B17994089 : Blo 515797 17994089 := bstep (se 2 (by rfl) ⟨6747783, by rfl⟩ : syracuseStep 17994089 = 13495567) B13495567
theorem B2364191 : Blo 515797 2364191 := bstep (se 1 (by rfl) ⟨1773143, by rfl⟩ : syracuseStep 2364191 = 3546287) B3546287
theorem B42374117 : Blo 515797 42374117 := bstep (se 4 (by rfl) ⟨3972573, by rfl⟩ : syracuseStep 42374117 = 7945147) B7945147
theorem B2102527 : Blo 515797 2102527 := bstep (se 1 (by rfl) ⟨1576895, by rfl⟩ : syracuseStep 2102527 = 3153791) B3153791
theorem B1348919 : Blo 515797 1348919 := bstep (se 1 (by rfl) ⟨1011689, by rfl⟩ : syracuseStep 1348919 = 2023379) B2023379
theorem B562559 : Blo 515797 562559 := bstep (se 1 (by rfl) ⟨421919, by rfl⟩ : syracuseStep 562559 = 843839) B843839
theorem B2233919 : Blo 515797 2233919 := bstep (se 1 (by rfl) ⟨1675439, by rfl⟩ : syracuseStep 2233919 = 3350879) B3350879
theorem B1742633 : Blo 515797 1742633 := bstep (se 2 (by rfl) ⟨653487, by rfl⟩ : syracuseStep 1742633 = 1306975) B1306975
theorem B1972295 : Blo 515797 1972295 := bstep (se 1 (by rfl) ⟨1479221, by rfl⟩ : syracuseStep 1972295 = 2958443) B2958443
theorem B3315971 : Blo 515797 3315971 := bstep (se 1 (by rfl) ⟨2486978, by rfl⟩ : syracuseStep 3315971 = 4973957) B4973957
theorem B58169821 : Blo 515797 58169821 := bstep (se 3 (by rfl) ⟨10906841, by rfl⟩ : syracuseStep 58169821 = 21813683) B21813683
theorem B3545959 : Blo 515797 3545959 := bstep (se 1 (by rfl) ⟨2659469, by rfl⟩ : syracuseStep 3545959 = 5318939) B5318939
theorem B8985563 : Blo 515797 8985563 := bstep (se 1 (by rfl) ⟨6739172, by rfl⟩ : syracuseStep 8985563 = 13478345) B13478345
theorem B45522283 : Blo 515797 45522283 := bstep (se 1 (by rfl) ⟨34141712, by rfl⟩ : syracuseStep 45522283 = 68283425) B68283425
theorem B3317921 : Blo 515797 3317921 := bstep (se 2 (by rfl) ⟨1244220, by rfl⟩ : syracuseStep 3317921 = 2488441) B2488441
theorem B13279463 : Blo 515797 13279463 := bstep (se 1 (by rfl) ⟨9959597, by rfl⟩ : syracuseStep 13279463 = 19919195) B19919195
theorem B1123751 : Blo 515797 1123751 := bstep (se 1 (by rfl) ⟨842813, by rfl⟩ : syracuseStep 1123751 = 1685627) B1685627
theorem B5581133 : Blo 515797 5581133 := bstep (se 3 (by rfl) ⟨1046462, by rfl⟩ : syracuseStep 5581133 = 2092925) B2092925
theorem B12593839 : Blo 515797 12593839 := bstep (se 1 (by rfl) ⟨9445379, by rfl⟩ : syracuseStep 12593839 = 18890759) B18890759
theorem B22686799 : Blo 515797 22686799 := bstep (se 1 (by rfl) ⟨17015099, by rfl⟩ : syracuseStep 22686799 = 34030199) B34030199
theorem B7482617 : Blo 515797 7482617 := bstep (se 2 (by rfl) ⟨2805981, by rfl⟩ : syracuseStep 7482617 = 5611963) B5611963
theorem B8826731 : Blo 515797 8826731 := bstep (se 1 (by rfl) ⟨6620048, by rfl⟩ : syracuseStep 8826731 = 13240097) B13240097
theorem B1749437 : Blo 515797 1749437 := bstep (se 3 (by rfl) ⟨328019, by rfl⟩ : syracuseStep 1749437 = 656039) B656039
theorem B1750301 : Blo 515797 1750301 := bstep (se 3 (by rfl) ⟨328181, by rfl⟩ : syracuseStep 1750301 = 656363) B656363
theorem B1751435 : Blo 515797 1751435 := bstep (se 1 (by rfl) ⟨1313576, by rfl⟩ : syracuseStep 1751435 = 2627153) B2627153
theorem B1751543 : Blo 515797 1751543 := bstep (se 1 (by rfl) ⟨1313657, by rfl⟩ : syracuseStep 1751543 = 2627315) B2627315
theorem B3324635 : Blo 515797 3324635 := bstep (se 1 (by rfl) ⟨2493476, by rfl⟩ : syracuseStep 3324635 = 4986953) B4986953
theorem B51264683 : Blo 515797 51264683 := bstep (se 1 (by rfl) ⟨38448512, by rfl⟩ : syracuseStep 51264683 = 76897025) B76897025
theorem B7486769 : Blo 515797 7486769 := bstep (se 2 (by rfl) ⟨2807538, by rfl⟩ : syracuseStep 7486769 = 5615077) B5615077
theorem B9944531 : Blo 515797 9944531 := bstep (se 1 (by rfl) ⟨7458398, by rfl⟩ : syracuseStep 9944531 = 14916797) B14916797
theorem B1752623 : Blo 515797 1752623 := bstep (se 1 (by rfl) ⟨1314467, by rfl⟩ : syracuseStep 1752623 = 2628935) B2628935
theorem B1162889 : Blo 515797 1162889 := bstep (se 2 (by rfl) ⟨436083, by rfl⟩ : syracuseStep 1162889 = 872167) B872167
theorem B1162907 : Blo 515797 1162907 := bstep (se 1 (by rfl) ⟨872180, by rfl⟩ : syracuseStep 1162907 = 1744361) B1744361
theorem B1163105 : Blo 515797 1163105 := bstep (se 2 (by rfl) ⟨436164, by rfl⟩ : syracuseStep 1163105 = 872329) B872329
theorem B1753001 : Blo 515797 1753001 := bstep (se 2 (by rfl) ⟨657375, by rfl⟩ : syracuseStep 1753001 = 1314751) B1314751
theorem B34062281 : Blo 515797 34062281 := bstep (se 2 (by rfl) ⟨12773355, by rfl⟩ : syracuseStep 34062281 = 25546711) B25546711
theorem B1753757 : Blo 515797 1753757 := bstep (se 3 (by rfl) ⟨328829, by rfl⟩ : syracuseStep 1753757 = 657659) B657659
theorem B934607 : Blo 515797 934607 := bstep (se 1 (by rfl) ⟨700955, by rfl⟩ : syracuseStep 934607 = 1401911) B1401911
theorem B1164959 : Blo 515797 1164959 := bstep (se 1 (by rfl) ⟨873719, by rfl⟩ : syracuseStep 1164959 = 1747439) B1747439
theorem B1165247 : Blo 515797 1165247 := bstep (se 1 (by rfl) ⟨873935, by rfl⟩ : syracuseStep 1165247 = 1747871) B1747871
theorem B3721241 : Blo 515797 3721241 := bstep (se 2 (by rfl) ⟨1395465, by rfl⟩ : syracuseStep 3721241 = 2790931) B2790931
theorem B870527 : Blo 515797 870527 := bstep (se 1 (by rfl) ⟨652895, by rfl⟩ : syracuseStep 870527 = 1305791) B1305791
theorem B8407307 : Blo 515797 8407307 := bstep (se 1 (by rfl) ⟨6305480, by rfl⟩ : syracuseStep 8407307 = 12610961) B12610961
theorem B870959 : Blo 515797 870959 := bstep (se 1 (by rfl) ⟨653219, by rfl⟩ : syracuseStep 870959 = 1306439) B1306439
theorem B1493599 : Blo 515797 1493599 := bstep (se 1 (by rfl) ⟨1120199, by rfl⟩ : syracuseStep 1493599 = 2240399) B2240399
theorem B3328735 : Blo 515797 3328735 := bstep (se 1 (by rfl) ⟨2496551, by rfl⟩ : syracuseStep 3328735 = 4993103) B4993103
theorem B871175 : Blo 515797 871175 := bstep (se 1 (by rfl) ⟨653381, by rfl⟩ : syracuseStep 871175 = 1306763) B1306763
theorem B3918617 : Blo 515797 3918617 := bstep (se 2 (by rfl) ⟨1469481, by rfl⟩ : syracuseStep 3918617 = 2938963) B2938963
theorem B1166543 : Blo 515797 1166543 := bstep (se 1 (by rfl) ⟨874907, by rfl⟩ : syracuseStep 1166543 = 1749815) B1749815
theorem B871735 : Blo 515797 871735 := bstep (se 1 (by rfl) ⟨653801, by rfl⟩ : syracuseStep 871735 = 1307603) B1307603
theorem B773855 : Blo 515797 773855 := bstep (se 1 (by rfl) ⟨580391, by rfl⟩ : syracuseStep 773855 = 1160783) B1160783
theorem B872201 : Blo 515797 872201 := bstep (se 2 (by rfl) ⟨327075, by rfl⟩ : syracuseStep 872201 = 654151) B654151
theorem B872255 : Blo 515797 872255 := bstep (se 1 (by rfl) ⟨654191, by rfl⟩ : syracuseStep 872255 = 1308383) B1308383
theorem B774215 : Blo 515797 774215 := bstep (se 1 (by rfl) ⟨580661, by rfl⟩ : syracuseStep 774215 = 1161323) B1161323
theorem B1167443 : Blo 515797 1167443 := bstep (se 1 (by rfl) ⟨875582, by rfl⟩ : syracuseStep 1167443 = 1751165) B1751165
theorem B774335 : Blo 515797 774335 := bstep (se 1 (by rfl) ⟨580751, by rfl⟩ : syracuseStep 774335 = 1161503) B1161503
theorem B1167551 : Blo 515797 1167551 := bstep (se 1 (by rfl) ⟨875663, by rfl⟩ : syracuseStep 1167551 = 1751327) B1751327
theorem B774479 : Blo 515797 774479 := bstep (se 1 (by rfl) ⟨580859, by rfl⟩ : syracuseStep 774479 = 1161719) B1161719
theorem B774521 : Blo 515797 774521 := bstep (se 2 (by rfl) ⟨290445, by rfl⟩ : syracuseStep 774521 = 580891) B580891
theorem B774815 : Blo 515797 774815 := bstep (se 1 (by rfl) ⟨581111, by rfl⟩ : syracuseStep 774815 = 1162223) B1162223
theorem B4412069 : Blo 515797 4412069 := bstep (se 4 (by rfl) ⟨413631, by rfl⟩ : syracuseStep 4412069 = 827263) B827263
theorem B5919479 : Blo 515797 5919479 := bstep (se 1 (by rfl) ⟨4439609, by rfl⟩ : syracuseStep 5919479 = 8879219) B8879219
theorem B775145 : Blo 515797 775145 := bstep (se 2 (by rfl) ⟨290679, by rfl⟩ : syracuseStep 775145 = 581359) B581359
theorem B60445709 : Blo 515797 60445709 := bstep (se 3 (by rfl) ⟨11333570, by rfl⟩ : syracuseStep 60445709 = 22667141) B22667141
theorem B775199 : Blo 515797 775199 := bstep (se 1 (by rfl) ⟨581399, by rfl⟩ : syracuseStep 775199 = 1162799) B1162799
theorem B1397801 : Blo 515797 1397801 := bstep (se 2 (by rfl) ⟨524175, by rfl⟩ : syracuseStep 1397801 = 1048351) B1048351
theorem B775487 : Blo 515797 775487 := bstep (se 1 (by rfl) ⟨581615, by rfl⟩ : syracuseStep 775487 = 1163231) B1163231
theorem B33576281 : Blo 515797 33576281 := bstep (se 2 (by rfl) ⟨12591105, by rfl⟩ : syracuseStep 33576281 = 25182211) B25182211
theorem B873895 : Blo 515797 873895 := bstep (se 1 (by rfl) ⟨655421, by rfl⟩ : syracuseStep 873895 = 1310843) B1310843
theorem B873983 : Blo 515797 873983 := bstep (se 1 (by rfl) ⟨655487, by rfl⟩ : syracuseStep 873983 = 1310975) B1310975
theorem B8410679 : Blo 515797 8410679 := bstep (se 1 (by rfl) ⟨6308009, by rfl⟩ : syracuseStep 8410679 = 12616019) B12616019
theorem B874361 : Blo 515797 874361 := bstep (se 2 (by rfl) ⟨327885, by rfl⟩ : syracuseStep 874361 = 655771) B655771
theorem B874921 : Blo 515797 874921 := bstep (se 2 (by rfl) ⟨328095, by rfl⟩ : syracuseStep 874921 = 656191) B656191
theorem B8870471 : Blo 515797 8870471 := bstep (se 1 (by rfl) ⟨6652853, by rfl⟩ : syracuseStep 8870471 = 13305707) B13305707
theorem B8379287 : Blo 515797 8379287 := bstep (se 1 (by rfl) ⟨6284465, by rfl⟩ : syracuseStep 8379287 = 12568931) B12568931
theorem B580927 : Blo 515797 580927 := bstep (se 1 (by rfl) ⟨435695, by rfl⟩ : syracuseStep 580927 = 871391) B871391
theorem B876271 : Blo 515797 876271 := bstep (se 1 (by rfl) ⟨657203, by rfl⟩ : syracuseStep 876271 = 1314407) B1314407
theorem B515931 : Blo 515797 515931 := bstep (se 1 (by rfl) ⟨386948, by rfl⟩ : syracuseStep 515931 = 773897) B773897
theorem B515967 : Blo 515797 515967 := bstep (se 1 (by rfl) ⟨386975, by rfl⟩ : syracuseStep 515967 = 773951) B773951
theorem B778121 : Blo 515797 778121 := bstep (se 2 (by rfl) ⟨291795, by rfl⟩ : syracuseStep 778121 = 583591) B583591
theorem B529915877 : Blo 515797 529915877 := bstep (se 4 (by rfl) ⟨49679613, by rfl⟩ : syracuseStep 529915877 = 99359227) B99359227
theorem B516127 : Blo 515797 516127 := bstep (se 1 (by rfl) ⟨387095, by rfl⟩ : syracuseStep 516127 = 774191) B774191
theorem B778271 : Blo 515797 778271 := bstep (se 1 (by rfl) ⟨583703, by rfl⟩ : syracuseStep 778271 = 1167407) B1167407
theorem B8380577 : Blo 515797 8380577 := bstep (se 2 (by rfl) ⟨3142716, by rfl⟩ : syracuseStep 8380577 = 6285433) B6285433
theorem B1663163 : Blo 515797 1663163 := bstep (se 1 (by rfl) ⟨1247372, by rfl⟩ : syracuseStep 1663163 = 2494745) B2494745
theorem B516423 : Blo 515797 516423 := bstep (se 1 (by rfl) ⟨387317, by rfl⟩ : syracuseStep 516423 = 774635) B774635
theorem B516507 : Blo 515797 516507 := bstep (se 1 (by rfl) ⟨387380, by rfl⟩ : syracuseStep 516507 = 774761) B774761
theorem B582043 : Blo 515797 582043 := bstep (se 1 (by rfl) ⟨436532, by rfl⟩ : syracuseStep 582043 = 873065) B873065
theorem B516511 : Blo 515797 516511 := bstep (se 1 (by rfl) ⟨387383, by rfl⟩ : syracuseStep 516511 = 774767) B774767
theorem B778655 : Blo 515797 778655 := bstep (se 1 (by rfl) ⟨583991, by rfl⟩ : syracuseStep 778655 = 1167983) B1167983
theorem B516591 : Blo 515797 516591 := bstep (se 1 (by rfl) ⟨387443, by rfl⟩ : syracuseStep 516591 = 774887) B774887
theorem B516699 : Blo 515797 516699 := bstep (se 1 (by rfl) ⟨387524, by rfl⟩ : syracuseStep 516699 = 775049) B775049
theorem B778889 : Blo 515797 778889 := bstep (se 2 (by rfl) ⟨292083, by rfl⟩ : syracuseStep 778889 = 584167) B584167
theorem B516927 : Blo 515797 516927 := bstep (se 1 (by rfl) ⟨387695, by rfl⟩ : syracuseStep 516927 = 775391) B775391
theorem B516955 : Blo 515797 516955 := bstep (se 1 (by rfl) ⟨387716, by rfl⟩ : syracuseStep 516955 = 775433) B775433
theorem B779129 : Blo 515797 779129 := bstep (se 2 (by rfl) ⟨292173, by rfl⟩ : syracuseStep 779129 = 584347) B584347
theorem B746377 : Blo 515797 746377 := bstep (se 2 (by rfl) ⟨279891, by rfl⟩ : syracuseStep 746377 = 559783) B559783
theorem B517247 : Blo 515797 517247 := bstep (se 1 (by rfl) ⟨387935, by rfl⟩ : syracuseStep 517247 = 775871) B775871
theorem B517275 : Blo 515797 517275 := bstep (se 1 (by rfl) ⟨387956, by rfl⟩ : syracuseStep 517275 = 775913) B775913
theorem B517279 : Blo 515797 517279 := bstep (se 1 (by rfl) ⟨387959, by rfl⟩ : syracuseStep 517279 = 775919) B775919
theorem B779423 : Blo 515797 779423 := bstep (se 1 (by rfl) ⟨584567, by rfl⟩ : syracuseStep 779423 = 1169135) B1169135
theorem B1959187 : Blo 515797 1959187 := bstep (se 1 (by rfl) ⟨1469390, by rfl⟩ : syracuseStep 1959187 = 2938781) B2938781
theorem B517615 : Blo 515797 517615 := bstep (se 1 (by rfl) ⟨388211, by rfl⟩ : syracuseStep 517615 = 776423) B776423
theorem B517735 : Blo 515797 517735 := bstep (se 1 (by rfl) ⟨388301, by rfl⟩ : syracuseStep 517735 = 776603) B776603
theorem B517999 : Blo 515797 517999 := bstep (se 1 (by rfl) ⟨388499, by rfl⟩ : syracuseStep 517999 = 776999) B776999
theorem B518015 : Blo 515797 518015 := bstep (se 1 (by rfl) ⟨388511, by rfl⟩ : syracuseStep 518015 = 777023) B777023
theorem B518215 : Blo 515797 518215 := bstep (se 1 (by rfl) ⟨388661, by rfl⟩ : syracuseStep 518215 = 777323) B777323
theorem B518311 : Blo 515797 518311 := bstep (se 1 (by rfl) ⟨388733, by rfl⟩ : syracuseStep 518311 = 777467) B777467
theorem B8382653 : Blo 515797 8382653 := bstep (se 3 (by rfl) ⟨1571747, by rfl⟩ : syracuseStep 8382653 = 3143495) B3143495
theorem B518375 : Blo 515797 518375 := bstep (se 1 (by rfl) ⟨388781, by rfl⟩ : syracuseStep 518375 = 777563) B777563
theorem B518395 : Blo 515797 518395 := bstep (se 1 (by rfl) ⟨388796, by rfl⟩ : syracuseStep 518395 = 777593) B777593
theorem B518399 : Blo 515797 518399 := bstep (se 1 (by rfl) ⟨388799, by rfl⟩ : syracuseStep 518399 = 777599) B777599
theorem B1108255 : Blo 515797 1108255 := bstep (se 1 (by rfl) ⟨831191, by rfl⟩ : syracuseStep 1108255 = 1662383) B1662383
theorem B2648375 : Blo 515797 2648375 := bstep (se 1 (by rfl) ⟨1986281, by rfl⟩ : syracuseStep 2648375 = 3972563) B3972563
theorem B518767 : Blo 515797 518767 := bstep (se 1 (by rfl) ⟨389075, by rfl⟩ : syracuseStep 518767 = 778151) B778151
theorem B518815 : Blo 515797 518815 := bstep (se 1 (by rfl) ⟨389111, by rfl⟩ : syracuseStep 518815 = 778223) B778223
theorem B518895 : Blo 515797 518895 := bstep (se 1 (by rfl) ⟨389171, by rfl⟩ : syracuseStep 518895 = 778343) B778343
theorem B518983 : Blo 515797 518983 := bstep (se 1 (by rfl) ⟨389237, by rfl⟩ : syracuseStep 518983 = 778475) B778475
theorem B8874845 : Blo 515797 8874845 := bstep (se 3 (by rfl) ⟨1664033, by rfl⟩ : syracuseStep 8874845 = 3328067) B3328067
theorem B519023 : Blo 515797 519023 := bstep (se 1 (by rfl) ⟨389267, by rfl⟩ : syracuseStep 519023 = 778535) B778535
theorem B519323 : Blo 515797 519323 := bstep (se 1 (by rfl) ⟨389492, by rfl⟩ : syracuseStep 519323 = 778985) B778985
theorem B519583 : Blo 515797 519583 := bstep (se 1 (by rfl) ⟨389687, by rfl⟩ : syracuseStep 519583 = 779375) B779375
theorem B519663 : Blo 515797 519663 := bstep (se 1 (by rfl) ⟨389747, by rfl⟩ : syracuseStep 519663 = 779495) B779495
theorem B519707 : Blo 515797 519707 := bstep (se 1 (by rfl) ⟨389780, by rfl⟩ : syracuseStep 519707 = 779561) B779561
theorem B1469983 : Blo 515797 1469983 := bstep (se 1 (by rfl) ⟨1102487, by rfl⟩ : syracuseStep 1469983 = 2204975) B2204975
theorem B1470143 : Blo 515797 1470143 := bstep (se 1 (by rfl) ⟨1102607, by rfl⟩ : syracuseStep 1470143 = 2205215) B2205215
theorem B979283 : Blo 515797 979283 := bstep (se 1 (by rfl) ⟨734462, by rfl⟩ : syracuseStep 979283 = 1468925) B1468925
theorem B14872967 : Blo 515797 14872967 := bstep (se 1 (by rfl) ⟨11154725, by rfl⟩ : syracuseStep 14872967 = 22309451) B22309451
theorem B4420169 : Blo 515797 4420169 := bstep (se 2 (by rfl) ⟨1657563, by rfl⟩ : syracuseStep 4420169 = 3315127) B3315127
theorem B5043667 : Blo 515797 5043667 := bstep (se 1 (by rfl) ⟨3782750, by rfl⟩ : syracuseStep 5043667 = 7565501) B7565501
theorem B2619215 : Blo 515797 2619215 := bstep (se 1 (by rfl) ⟨1964411, by rfl⟩ : syracuseStep 2619215 = 3928823) B3928823
theorem B6649937 : Blo 515797 6649937 := bstep (se 2 (by rfl) ⟨2493726, by rfl⟩ : syracuseStep 6649937 = 4987453) B4987453
theorem B3930767 : Blo 515797 3930767 := bstep (se 1 (by rfl) ⟨2948075, by rfl⟩ : syracuseStep 3930767 = 5896151) B5896151
theorem B4193147 : Blo 515797 4193147 := bstep (se 1 (by rfl) ⟨3144860, by rfl⟩ : syracuseStep 4193147 = 6289721) B6289721
theorem B1473515 : Blo 515797 1473515 := bstep (se 1 (by rfl) ⟨1105136, by rfl⟩ : syracuseStep 1473515 = 2210273) B2210273
theorem B2522551 : Blo 515797 2522551 := bstep (se 1 (by rfl) ⟨1891913, by rfl⟩ : syracuseStep 2522551 = 3783827) B3783827
theorem B1048043 : Blo 515797 1048043 := bstep (se 1 (by rfl) ⟨786032, by rfl⟩ : syracuseStep 1048043 = 1572065) B1572065
theorem B982631 : Blo 515797 982631 := bstep (se 1 (by rfl) ⟨736973, by rfl⟩ : syracuseStep 982631 = 1473947) B1473947
theorem B2621321 : Blo 515797 2621321 := bstep (se 2 (by rfl) ⟨982995, by rfl⟩ : syracuseStep 2621321 = 1965991) B1965991
theorem B1867657 : Blo 515797 1867657 := bstep (se 2 (by rfl) ⟨700371, by rfl⟩ : syracuseStep 1867657 = 1400743) B1400743
theorem B4980689 : Blo 515797 4980689 := bstep (se 2 (by rfl) ⟨1867758, by rfl⟩ : syracuseStep 4980689 = 3735517) B3735517
theorem B655543 : Blo 515797 655543 := bstep (se 1 (by rfl) ⟨491657, by rfl⟩ : syracuseStep 655543 = 983315) B983315
theorem B623071 : Blo 515797 623071 := bstep (se 1 (by rfl) ⟨467303, by rfl⟩ : syracuseStep 623071 = 934607) B934607
theorem B2098163 : Blo 515797 2098163 := bstep (se 1 (by rfl) ⟨1573622, by rfl⟩ : syracuseStep 2098163 = 3147245) B3147245
theorem B5604871 : Blo 515797 5604871 := bstep (se 1 (by rfl) ⟨4203653, by rfl⟩ : syracuseStep 5604871 = 8407307) B8407307
theorem B1967723 : Blo 515797 1967723 := bstep (se 1 (by rfl) ⟨1475792, by rfl⟩ : syracuseStep 1967723 = 2951585) B2951585
theorem B2492975 : Blo 515797 2492975 := bstep (se 1 (by rfl) ⟨1869731, by rfl⟩ : syracuseStep 2492975 = 3739463) B3739463
theorem B1968907 : Blo 515797 1968907 := bstep (se 1 (by rfl) ⟨1476680, by rfl⟩ : syracuseStep 1968907 = 2953361) B2953361
theorem B1477673 : Blo 515797 1477673 := bstep (se 2 (by rfl) ⟨554127, by rfl⟩ : syracuseStep 1477673 = 1108255) B1108255
theorem B1576127 : Blo 515797 1576127 := bstep (se 1 (by rfl) ⟨1182095, by rfl⟩ : syracuseStep 1576127 = 2364191) B2364191
theorem B28249411 : Blo 515797 28249411 := bstep (se 1 (by rfl) ⟨21187058, by rfl⟩ : syracuseStep 28249411 = 42374117) B42374117
theorem B22384187 : Blo 515797 22384187 := bstep (se 1 (by rfl) ⟨16788140, by rfl⟩ : syracuseStep 22384187 = 33576281) B33576281
theorem B5607119 : Blo 515797 5607119 := bstep (se 1 (by rfl) ⟨4205339, by rfl⟩ : syracuseStep 5607119 = 8410679) B8410679
theorem B1314569 : Blo 515797 1314569 := bstep (se 2 (by rfl) ⟨492963, by rfl⟩ : syracuseStep 1314569 = 985927) B985927
theorem B1314863 : Blo 515797 1314863 := bstep (se 1 (by rfl) ⟨986147, by rfl⟩ : syracuseStep 1314863 = 1972295) B1972295
theorem B1314913 : Blo 515797 1314913 := bstep (se 2 (by rfl) ⟨493092, by rfl⟩ : syracuseStep 1314913 = 986185) B986185
theorem B30249065 : Blo 515797 30249065 := bstep (se 2 (by rfl) ⟨11343399, by rfl⟩ : syracuseStep 30249065 = 22686799) B22686799
theorem B353277251 : Blo 515797 353277251 := bstep (se 1 (by rfl) ⟨264957938, by rfl⟩ : syracuseStep 353277251 = 529915877) B529915877
theorem B8852975 : Blo 515797 8852975 := bstep (se 1 (by rfl) ⟨6639731, by rfl⟩ : syracuseStep 8852975 = 13279463) B13279463
theorem B6724889 : Blo 515797 6724889 := bstep (se 2 (by rfl) ⟨2521833, by rfl⟩ : syracuseStep 6724889 = 5043667) B5043667
theorem B4988411 : Blo 515797 4988411 := bstep (se 1 (by rfl) ⟨3741308, by rfl⟩ : syracuseStep 4988411 = 7482617) B7482617
theorem B4727945 : Blo 515797 4727945 := bstep (se 2 (by rfl) ⟨1772979, by rfl⟩ : syracuseStep 4727945 = 3545959) B3545959
theorem B1746143 : Blo 515797 1746143 := bstep (se 1 (by rfl) ⟨1309607, by rfl⟩ : syracuseStep 1746143 = 2619215) B2619215
theorem B2794781 : Blo 515797 2794781 := bstep (se 3 (by rfl) ⟨524021, by rfl⟩ : syracuseStep 2794781 = 1048043) B1048043
theorem B4433291 : Blo 515797 4433291 := bstep (se 1 (by rfl) ⟨3324968, by rfl⟩ : syracuseStep 4433291 = 6649937) B6649937
theorem B60696377 : Blo 515797 60696377 := bstep (se 2 (by rfl) ⟨22761141, by rfl⟩ : syracuseStep 60696377 = 45522283) B45522283
theorem B2795431 : Blo 515797 2795431 := bstep (se 1 (by rfl) ⟨2096573, by rfl⟩ : syracuseStep 2795431 = 4193147) B4193147
theorem B4991179 : Blo 515797 4991179 := bstep (se 1 (by rfl) ⟨3743384, by rfl⟩ : syracuseStep 4991179 = 7486769) B7486769
theorem B6629687 : Blo 515797 6629687 := bstep (se 1 (by rfl) ⟨4972265, by rfl⟩ : syracuseStep 6629687 = 9944531) B9944531
theorem B1747547 : Blo 515797 1747547 := bstep (se 1 (by rfl) ⟨1310660, by rfl⟩ : syracuseStep 1747547 = 2621321) B2621321
theorem B3320459 : Blo 515797 3320459 := bstep (se 1 (by rfl) ⟨2490344, by rfl⟩ : syracuseStep 3320459 = 4980689) B4980689
theorem B2206547 : Blo 515797 2206547 := bstep (se 1 (by rfl) ⟨1654910, by rfl⟩ : syracuseStep 2206547 = 3309821) B3309821
theorem B699529 : Blo 515797 699529 := bstep (se 2 (by rfl) ⟨262323, by rfl⟩ : syracuseStep 699529 = 524647) B524647
theorem B8105143 : Blo 515797 8105143 := bstep (se 1 (by rfl) ⟨6078857, by rfl⟩ : syracuseStep 8105143 = 12157715) B12157715
theorem B47984237 : Blo 515797 47984237 := bstep (se 3 (by rfl) ⟨8997044, by rfl⟩ : syracuseStep 47984237 = 17994089) B17994089
theorem B232697939 : Blo 515797 232697939 := bstep (se 1 (by rfl) ⟨174523454, by rfl⟩ : syracuseStep 232697939 = 349046909) B349046909
theorem B16822403 : Blo 515797 16822403 := bstep (se 1 (by rfl) ⟨12616802, by rfl⟩ : syracuseStep 16822403 = 25233605) B25233605
theorem B832607 : Blo 515797 832607 := bstep (se 1 (by rfl) ⟨624455, by rfl⟩ : syracuseStep 832607 = 1248911) B1248911
theorem B3946319 : Blo 515797 3946319 := bstep (se 1 (by rfl) ⟨2959739, by rfl⟩ : syracuseStep 3946319 = 5919479) B5919479
theorem B931867 : Blo 515797 931867 := bstep (se 1 (by rfl) ⟨698900, by rfl⟩ : syracuseStep 931867 = 1397801) B1397801
theorem B899279 : Blo 515797 899279 := bstep (se 1 (by rfl) ⟨674459, by rfl⟩ : syracuseStep 899279 = 1348919) B1348919
theorem B16791785 : Blo 515797 16791785 := bstep (se 2 (by rfl) ⟨6296919, by rfl⟩ : syracuseStep 16791785 = 12593839) B12593839
theorem B4438313 : Blo 515797 4438313 := bstep (se 2 (by rfl) ⟨1664367, by rfl⟩ : syracuseStep 4438313 = 3328735) B3328735
theorem B1489279 : Blo 515797 1489279 := bstep (se 1 (by rfl) ⟨1116959, by rfl⟩ : syracuseStep 1489279 = 2233919) B2233919
theorem B2996669 : Blo 515797 2996669 := bstep (se 3 (by rfl) ⟨561875, by rfl⟩ : syracuseStep 2996669 = 1123751) B1123751
theorem B1161755 : Blo 515797 1161755 := bstep (se 1 (by rfl) ⟨871316, by rfl⟩ : syracuseStep 1161755 = 1742633) B1742633
theorem B2210647 : Blo 515797 2210647 := bstep (se 1 (by rfl) ⟨1657985, by rfl⟩ : syracuseStep 2210647 = 3315971) B3315971
theorem B5913647 : Blo 515797 5913647 := bstep (se 1 (by rfl) ⟨4435235, by rfl⟩ : syracuseStep 5913647 = 8870471) B8870471
theorem B1162313 : Blo 515797 1162313 := bstep (se 2 (by rfl) ⟨435867, by rfl⟩ : syracuseStep 1162313 = 871735) B871735
theorem B5586191 : Blo 515797 5586191 := bstep (se 1 (by rfl) ⟨4189643, by rfl⟩ : syracuseStep 5586191 = 8379287) B8379287
theorem B3980677 : Blo 515797 3980677 := bstep (se 4 (by rfl) ⟨373188, by rfl⟩ : syracuseStep 3980677 = 746377) B746377
theorem B5587051 : Blo 515797 5587051 := bstep (se 1 (by rfl) ⟨4190288, by rfl⟩ : syracuseStep 5587051 = 8380577) B8380577
theorem B2211947 : Blo 515797 2211947 := bstep (se 1 (by rfl) ⟨1658960, by rfl⟩ : syracuseStep 2211947 = 3317921) B3317921
theorem B5588435 : Blo 515797 5588435 := bstep (se 1 (by rfl) ⟨4191326, by rfl⟩ : syracuseStep 5588435 = 8382653) B8382653
theorem B3720755 : Blo 515797 3720755 := bstep (se 1 (by rfl) ⟨2790566, by rfl⟩ : syracuseStep 3720755 = 5581133) B5581133
theorem B2803369 : Blo 515797 2803369 := bstep (se 2 (by rfl) ⟨1051263, by rfl⟩ : syracuseStep 2803369 = 2102527) B2102527
theorem B1165193 : Blo 515797 1165193 := bstep (se 2 (by rfl) ⟨436947, by rfl⟩ : syracuseStep 1165193 = 873895) B873895
theorem B5916563 : Blo 515797 5916563 := bstep (se 1 (by rfl) ⟨4437422, by rfl⟩ : syracuseStep 5916563 = 8874845) B8874845
theorem B5884487 : Blo 515797 5884487 := bstep (se 1 (by rfl) ⟨4413365, by rfl⟩ : syracuseStep 5884487 = 8826731) B8826731
theorem B9915311 : Blo 515797 9915311 := bstep (se 1 (by rfl) ⟨7436483, by rfl⟩ : syracuseStep 9915311 = 14872967) B14872967
theorem B1166291 : Blo 515797 1166291 := bstep (se 1 (by rfl) ⟨874718, by rfl⟩ : syracuseStep 1166291 = 1749437) B1749437
theorem B1166561 : Blo 515797 1166561 := bstep (se 2 (by rfl) ⟨437460, by rfl⟩ : syracuseStep 1166561 = 874921) B874921
theorem B1166867 : Blo 515797 1166867 := bstep (se 1 (by rfl) ⟨875150, by rfl⟩ : syracuseStep 1166867 = 1750301) B1750301
theorem B1167623 : Blo 515797 1167623 := bstep (se 1 (by rfl) ⟨875717, by rfl⟩ : syracuseStep 1167623 = 1751435) B1751435
theorem B1167695 : Blo 515797 1167695 := bstep (se 1 (by rfl) ⟨875771, by rfl⟩ : syracuseStep 1167695 = 1751543) B1751543
theorem B774569 : Blo 515797 774569 := bstep (se 2 (by rfl) ⟨290463, by rfl⟩ : syracuseStep 774569 = 580927) B580927
theorem B2216423 : Blo 515797 2216423 := bstep (se 1 (by rfl) ⟨1662317, by rfl⟩ : syracuseStep 2216423 = 3324635) B3324635
theorem B3363401 : Blo 515797 3363401 := bstep (se 2 (by rfl) ⟨1261275, by rfl⟩ : syracuseStep 3363401 = 2522551) B2522551
theorem B1168361 : Blo 515797 1168361 := bstep (se 2 (by rfl) ⟨438135, by rfl⟩ : syracuseStep 1168361 = 876271) B876271
theorem B1168415 : Blo 515797 1168415 := bstep (se 1 (by rfl) ⟨876311, by rfl⟩ : syracuseStep 1168415 = 1752623) B1752623
theorem B775259 : Blo 515797 775259 := bstep (se 1 (by rfl) ⟨581444, by rfl⟩ : syracuseStep 775259 = 1162889) B1162889
theorem B775271 : Blo 515797 775271 := bstep (se 1 (by rfl) ⟨581453, by rfl⟩ : syracuseStep 775271 = 1162907) B1162907
theorem B775403 : Blo 515797 775403 := bstep (se 1 (by rfl) ⟨581552, by rfl⟩ : syracuseStep 775403 = 1163105) B1163105
theorem B1168667 : Blo 515797 1168667 := bstep (se 1 (by rfl) ⟨876500, by rfl⟩ : syracuseStep 1168667 = 1753001) B1753001
theorem B874091 : Blo 515797 874091 := bstep (se 1 (by rfl) ⟨655568, by rfl⟩ : syracuseStep 874091 = 1311137) B1311137
theorem B1169171 : Blo 515797 1169171 := bstep (se 1 (by rfl) ⟨876878, by rfl⟩ : syracuseStep 1169171 = 1753757) B1753757
theorem B776057 : Blo 515797 776057 := bstep (se 2 (by rfl) ⟨291021, by rfl⟩ : syracuseStep 776057 = 582043) B582043
theorem B776639 : Blo 515797 776639 := bstep (se 1 (by rfl) ⟨582479, by rfl⟩ : syracuseStep 776639 = 1164959) B1164959
theorem B776831 : Blo 515797 776831 := bstep (se 1 (by rfl) ⟨582623, by rfl⟩ : syracuseStep 776831 = 1165247) B1165247
theorem B9460415 : Blo 515797 9460415 := bstep (se 1 (by rfl) ⟨7095311, by rfl⟩ : syracuseStep 9460415 = 14190623) B14190623
theorem B580351 : Blo 515797 580351 := bstep (se 1 (by rfl) ⟨435263, by rfl⟩ : syracuseStep 580351 = 870527) B870527
theorem B2612249 : Blo 515797 2612249 := bstep (se 2 (by rfl) ⟨979593, by rfl⟩ : syracuseStep 2612249 = 1959187) B1959187
theorem B580639 : Blo 515797 580639 := bstep (se 1 (by rfl) ⟨435479, by rfl⟩ : syracuseStep 580639 = 870959) B870959
theorem B3365999 : Blo 515797 3365999 := bstep (se 1 (by rfl) ⟨2524499, by rfl⟩ : syracuseStep 3365999 = 5048999) B5048999
theorem B580783 : Blo 515797 580783 := bstep (se 1 (by rfl) ⟨435587, by rfl⟩ : syracuseStep 580783 = 871175) B871175
theorem B2612411 : Blo 515797 2612411 := bstep (se 1 (by rfl) ⟨1959308, by rfl⟩ : syracuseStep 2612411 = 3918617) B3918617
theorem B875839 : Blo 515797 875839 := bstep (se 1 (by rfl) ⟨656879, by rfl⟩ : syracuseStep 875839 = 1313759) B1313759
theorem B777695 : Blo 515797 777695 := bstep (se 1 (by rfl) ⟨583271, by rfl⟩ : syracuseStep 777695 = 1166543) B1166543
theorem B876143 : Blo 515797 876143 := bstep (se 1 (by rfl) ⟨657107, by rfl⟩ : syracuseStep 876143 = 1314215) B1314215
theorem B515903 : Blo 515797 515903 := bstep (se 1 (by rfl) ⟨386927, by rfl⟩ : syracuseStep 515903 = 773855) B773855
theorem B581467 : Blo 515797 581467 := bstep (se 1 (by rfl) ⟨436100, by rfl⟩ : syracuseStep 581467 = 872201) B872201
theorem B581503 : Blo 515797 581503 := bstep (se 1 (by rfl) ⟨436127, by rfl⟩ : syracuseStep 581503 = 872255) B872255
theorem B516143 : Blo 515797 516143 := bstep (se 1 (by rfl) ⟨387107, by rfl⟩ : syracuseStep 516143 = 774215) B774215
theorem B778295 : Blo 515797 778295 := bstep (se 1 (by rfl) ⟨583721, by rfl⟩ : syracuseStep 778295 = 1167443) B1167443
theorem B516223 : Blo 515797 516223 := bstep (se 1 (by rfl) ⟨387167, by rfl⟩ : syracuseStep 516223 = 774335) B774335
theorem B778367 : Blo 515797 778367 := bstep (se 1 (by rfl) ⟨583775, by rfl⟩ : syracuseStep 778367 = 1167551) B1167551
theorem B516319 : Blo 515797 516319 := bstep (se 1 (by rfl) ⟨387239, by rfl⟩ : syracuseStep 516319 = 774479) B774479
theorem B516347 : Blo 515797 516347 := bstep (se 1 (by rfl) ⟨387260, by rfl⟩ : syracuseStep 516347 = 774521) B774521
theorem B516543 : Blo 515797 516543 := bstep (se 1 (by rfl) ⟨387407, by rfl⟩ : syracuseStep 516543 = 774815) B774815
theorem B2941379 : Blo 515797 2941379 := bstep (se 1 (by rfl) ⟨2206034, by rfl⟩ : syracuseStep 2941379 = 4412069) B4412069
theorem B516763 : Blo 515797 516763 := bstep (se 1 (by rfl) ⟨387572, by rfl⟩ : syracuseStep 516763 = 775145) B775145
theorem B40297139 : Blo 515797 40297139 := bstep (se 1 (by rfl) ⟨30222854, by rfl⟩ : syracuseStep 40297139 = 60445709) B60445709
theorem B516799 : Blo 515797 516799 := bstep (se 1 (by rfl) ⟨387599, by rfl⟩ : syracuseStep 516799 = 775199) B775199
theorem B1991465 : Blo 515797 1991465 := bstep (se 2 (by rfl) ⟨746799, by rfl⟩ : syracuseStep 1991465 = 1493599) B1493599
theorem B516991 : Blo 515797 516991 := bstep (se 1 (by rfl) ⟨387743, by rfl⟩ : syracuseStep 516991 = 775487) B775487
theorem B582655 : Blo 515797 582655 := bstep (se 1 (by rfl) ⟨436991, by rfl⟩ : syracuseStep 582655 = 873983) B873983
theorem B1500157 : Blo 515797 1500157 := bstep (se 3 (by rfl) ⟨281279, by rfl⟩ : syracuseStep 1500157 = 562559) B562559
theorem B582907 : Blo 515797 582907 := bstep (se 1 (by rfl) ⟨437180, by rfl⟩ : syracuseStep 582907 = 874361) B874361
theorem B5990375 : Blo 515797 5990375 := bstep (se 1 (by rfl) ⟨4492781, by rfl⟩ : syracuseStep 5990375 = 8985563) B8985563
theorem B1959977 : Blo 515797 1959977 := bstep (se 2 (by rfl) ⟨734991, by rfl⟩ : syracuseStep 1959977 = 1469983) B1469983
theorem B518747 : Blo 515797 518747 := bstep (se 1 (by rfl) ⟨389060, by rfl⟩ : syracuseStep 518747 = 778121) B778121
theorem B518847 : Blo 515797 518847 := bstep (se 1 (by rfl) ⟨389135, by rfl⟩ : syracuseStep 518847 = 778271) B778271
theorem B9923309 : Blo 515797 9923309 := bstep (se 3 (by rfl) ⟨1860620, by rfl⟩ : syracuseStep 9923309 = 3721241) B3721241
theorem B1108775 : Blo 515797 1108775 := bstep (se 1 (by rfl) ⟨831581, by rfl⟩ : syracuseStep 1108775 = 1663163) B1663163
theorem B519103 : Blo 515797 519103 := bstep (se 1 (by rfl) ⟨389327, by rfl⟩ : syracuseStep 519103 = 778655) B778655
theorem B519259 : Blo 515797 519259 := bstep (se 1 (by rfl) ⟨389444, by rfl⟩ : syracuseStep 519259 = 778889) B778889
theorem B519419 : Blo 515797 519419 := bstep (se 1 (by rfl) ⟨389564, by rfl⟩ : syracuseStep 519419 = 779129) B779129
theorem B519615 : Blo 515797 519615 := bstep (se 1 (by rfl) ⟨389711, by rfl⟩ : syracuseStep 519615 = 779423) B779423
theorem B1765583 : Blo 515797 1765583 := bstep (se 1 (by rfl) ⟨1324187, by rfl⟩ : syracuseStep 1765583 = 2648375) B2648375
theorem B980095 : Blo 515797 980095 := bstep (se 1 (by rfl) ⟨735071, by rfl⟩ : syracuseStep 980095 = 1470143) B1470143
theorem B652855 : Blo 515797 652855 := bstep (se 1 (by rfl) ⟨489641, by rfl⟩ : syracuseStep 652855 = 979283) B979283
theorem B2946779 : Blo 515797 2946779 := bstep (se 1 (by rfl) ⟨2210084, by rfl⟩ : syracuseStep 2946779 = 4420169) B4420169
theorem B77559761 : Blo 515797 77559761 := bstep (se 2 (by rfl) ⟨29084910, by rfl⟩ : syracuseStep 77559761 = 58169821) B58169821
theorem B2620349 : Blo 515797 2620349 := bstep (se 3 (by rfl) ⟨491315, by rfl⟩ : syracuseStep 2620349 = 982631) B982631
theorem B2620511 : Blo 515797 2620511 := bstep (se 1 (by rfl) ⟨1965383, by rfl⟩ : syracuseStep 2620511 = 3930767) B3930767
theorem B982343 : Blo 515797 982343 := bstep (se 1 (by rfl) ⟨736757, by rfl⟩ : syracuseStep 982343 = 1473515) B1473515
theorem B34176455 : Blo 515797 34176455 := bstep (se 1 (by rfl) ⟨25632341, by rfl⟩ : syracuseStep 34176455 = 51264683) B51264683
theorem B2490209 : Blo 515797 2490209 := bstep (se 2 (by rfl) ⟨933828, by rfl⟩ : syracuseStep 2490209 = 1867657) B1867657
theorem B22708187 : Blo 515797 22708187 := bstep (se 1 (by rfl) ⟨17031140, by rfl⟩ : syracuseStep 22708187 = 34062281) B34062281
theorem B1474631 : Blo 515797 1474631 := bstep (se 1 (by rfl) ⟨1105973, by rfl⟩ : syracuseStep 1474631 = 2211947) B2211947
theorem B620527837 : Blo 515797 620527837 := bstep (se 3 (by rfl) ⟨116348969, by rfl⟩ : syracuseStep 620527837 = 232697939) B232697939
theorem B1311815 : Blo 515797 1311815 := bstep (se 1 (by rfl) ⟨983861, by rfl⟩ : syracuseStep 1311815 = 1967723) B1967723
theorem B2000209 : Blo 515797 2000209 := bstep (se 2 (by rfl) ⟨750078, by rfl⟩ : syracuseStep 2000209 = 1500157) B1500157
theorem B7473161 : Blo 515797 7473161 := bstep (se 2 (by rfl) ⟨2802435, by rfl⟩ : syracuseStep 7473161 = 5604871) B5604871
theorem B985115 : Blo 515797 985115 := bstep (se 1 (by rfl) ⟨738836, by rfl⟩ : syracuseStep 985115 = 1477673) B1477673
theorem B1050751 : Blo 515797 1050751 := bstep (se 1 (by rfl) ⟨788063, by rfl⟩ : syracuseStep 1050751 = 1576127) B1576127
theorem B3737825 : Blo 515797 3737825 := bstep (se 2 (by rfl) ⟨1401684, by rfl⟩ : syracuseStep 3737825 = 2803369) B2803369
theorem B3738079 : Blo 515797 3738079 := bstep (se 1 (by rfl) ⟨2803559, by rfl⟩ : syracuseStep 3738079 = 5607119) B5607119
theorem B6654905 : Blo 515797 6654905 := bstep (se 2 (by rfl) ⟨2495589, by rfl⟩ : syracuseStep 6654905 = 4991179) B4991179
theorem B1477615 : Blo 515797 1477615 := bstep (se 1 (by rfl) ⟨1108211, by rfl⟩ : syracuseStep 1477615 = 2216423) B2216423
theorem B5901983 : Blo 515797 5901983 := bstep (se 1 (by rfl) ⟨4426487, by rfl⟩ : syracuseStep 5901983 = 8852975) B8852975
theorem B2625209 : Blo 515797 2625209 := bstep (se 2 (by rfl) ⟨984453, by rfl⟩ : syracuseStep 2625209 = 1968907) B1968907
theorem B1741499 : Blo 515797 1741499 := bstep (se 1 (by rfl) ⟨1306124, by rfl⟩ : syracuseStep 1741499 = 2612249) B2612249
theorem B1741607 : Blo 515797 1741607 := bstep (se 1 (by rfl) ⟨1306205, by rfl⟩ : syracuseStep 1741607 = 2612411) B2612411
theorem B3151963 : Blo 515797 3151963 := bstep (se 1 (by rfl) ⟨2363972, by rfl⟩ : syracuseStep 3151963 = 4727945) B4727945
theorem B2955527 : Blo 515797 2955527 := bstep (se 1 (by rfl) ⟨2216645, by rfl⟩ : syracuseStep 2955527 = 4433291) B4433291
theorem B2956733 : Blo 515797 2956733 := bstep (se 3 (by rfl) ⟨554387, by rfl⟩ : syracuseStep 2956733 = 1108775) B1108775
theorem B31989491 : Blo 515797 31989491 := bstep (se 1 (by rfl) ⟨23992118, by rfl⟩ : syracuseStep 31989491 = 47984237) B47984237
theorem B11214935 : Blo 515797 11214935 := bstep (se 1 (by rfl) ⟨8411201, by rfl⟩ : syracuseStep 11214935 = 16822403) B16822403
theorem B2630879 : Blo 515797 2630879 := bstep (se 1 (by rfl) ⟨1973159, by rfl⟩ : syracuseStep 2630879 = 3946319) B3946319
theorem B599519 : Blo 515797 599519 := bstep (se 1 (by rfl) ⟨449639, by rfl⟩ : syracuseStep 599519 = 899279) B899279
theorem B2958875 : Blo 515797 2958875 := bstep (se 1 (by rfl) ⟨2219156, by rfl⟩ : syracuseStep 2958875 = 4438313) B4438313
theorem B1746899 : Blo 515797 1746899 := bstep (se 1 (by rfl) ⟨1310174, by rfl⟩ : syracuseStep 1746899 = 2620349) B2620349
theorem B3942431 : Blo 515797 3942431 := bstep (se 1 (by rfl) ⟨2956823, by rfl⟩ : syracuseStep 3942431 = 5913647) B5913647
theorem B1747007 : Blo 515797 1747007 := bstep (se 1 (by rfl) ⟨1310255, by rfl⟩ : syracuseStep 1747007 = 2620511) B2620511
theorem B22784303 : Blo 515797 22784303 := bstep (se 1 (by rfl) ⟨17088227, by rfl⟩ : syracuseStep 22784303 = 34176455) B34176455
theorem B7449401 : Blo 515797 7449401 := bstep (se 2 (by rfl) ⟨2793525, by rfl⟩ : syracuseStep 7449401 = 5587051) B5587051
theorem B3944375 : Blo 515797 3944375 := bstep (se 1 (by rfl) ⟨2958281, by rfl⟩ : syracuseStep 3944375 = 5916563) B5916563
theorem B14922791 : Blo 515797 14922791 := bstep (se 1 (by rfl) ⟨11192093, by rfl⟩ : syracuseStep 14922791 = 22384187) B22384187
theorem B3323045 : Blo 515797 3323045 := bstep (se 4 (by rfl) ⟨311535, by rfl⟩ : syracuseStep 3323045 = 623071) B623071
theorem B20166043 : Blo 515797 20166043 := bstep (se 1 (by rfl) ⟨15124532, by rfl⟩ : syracuseStep 20166043 = 30249065) B30249065
theorem B7452749 : Blo 515797 7452749 := bstep (se 3 (by rfl) ⟨1397390, by rfl⟩ : syracuseStep 7452749 = 2794781) B2794781
theorem B235518167 : Blo 515797 235518167 := bstep (se 1 (by rfl) ⟨176638625, by rfl⟩ : syracuseStep 235518167 = 353277251) B353277251
theorem B932705 : Blo 515797 932705 := bstep (se 2 (by rfl) ⟨349764, by rfl⟩ : syracuseStep 932705 = 699529) B699529
theorem B37665881 : Blo 515797 37665881 := bstep (se 2 (by rfl) ⟨14124705, by rfl⟩ : syracuseStep 37665881 = 28249411) B28249411
theorem B6306943 : Blo 515797 6306943 := bstep (se 1 (by rfl) ⟨4730207, by rfl⟩ : syracuseStep 6306943 = 9460415) B9460415
theorem B2243999 : Blo 515797 2243999 := bstep (se 1 (by rfl) ⟨1682999, by rfl⟩ : syracuseStep 2243999 = 3365999) B3365999
theorem B3325607 : Blo 515797 3325607 := bstep (se 1 (by rfl) ⟨2494205, by rfl⟩ : syracuseStep 3325607 = 4988411) B4988411
theorem B1753217 : Blo 515797 1753217 := bstep (se 2 (by rfl) ⟨657456, by rfl⟩ : syracuseStep 1753217 = 1314913) B1314913
theorem B1327643 : Blo 515797 1327643 := bstep (se 1 (by rfl) ⟨995732, by rfl⟩ : syracuseStep 1327643 = 1991465) B1991465
theorem B1164095 : Blo 515797 1164095 := bstep (se 1 (by rfl) ⟨873071, by rfl⟩ : syracuseStep 1164095 = 1746143) B1746143
theorem B1165031 : Blo 515797 1165031 := bstep (se 1 (by rfl) ⟨873773, by rfl⟩ : syracuseStep 1165031 = 1747547) B1747547
theorem B2213639 : Blo 515797 2213639 := bstep (se 1 (by rfl) ⟨1660229, by rfl⟩ : syracuseStep 2213639 = 3320459) B3320459
theorem B870473 : Blo 515797 870473 := bstep (se 2 (by rfl) ⟨326427, by rfl⟩ : syracuseStep 870473 = 652855) B652855
theorem B1985705 : Blo 515797 1985705 := bstep (se 2 (by rfl) ⟨744639, by rfl⟩ : syracuseStep 1985705 = 1489279) B1489279
theorem B773801 : Blo 515797 773801 := bstep (se 2 (by rfl) ⟨290175, by rfl⟩ : syracuseStep 773801 = 580351) B580351
theorem B774185 : Blo 515797 774185 := bstep (se 2 (by rfl) ⟨290319, by rfl⟩ : syracuseStep 774185 = 580639) B580639
theorem B11194523 : Blo 515797 11194523 := bstep (se 1 (by rfl) ⟨8395892, by rfl⟩ : syracuseStep 11194523 = 16791785) B16791785
theorem B774377 : Blo 515797 774377 := bstep (se 2 (by rfl) ⟨290391, by rfl⟩ : syracuseStep 774377 = 580783) B580783
theorem B774503 : Blo 515797 774503 := bstep (se 1 (by rfl) ⟨580877, by rfl⟩ : syracuseStep 774503 = 1161755) B1161755
theorem B1167785 : Blo 515797 1167785 := bstep (se 2 (by rfl) ⟨437919, by rfl⟩ : syracuseStep 1167785 = 875839) B875839
theorem B774875 : Blo 515797 774875 := bstep (se 1 (by rfl) ⟨581156, by rfl⟩ : syracuseStep 774875 = 1162313) B1162313
theorem B3724127 : Blo 515797 3724127 := bstep (se 1 (by rfl) ⟨2793095, by rfl⟩ : syracuseStep 3724127 = 5586191) B5586191
theorem B775289 : Blo 515797 775289 := bstep (se 2 (by rfl) ⟨290733, by rfl⟩ : syracuseStep 775289 = 581467) B581467
theorem B775337 : Blo 515797 775337 := bstep (se 2 (by rfl) ⟨290751, by rfl⟩ : syracuseStep 775337 = 581503) B581503
theorem B1660139 : Blo 515797 1660139 := bstep (se 1 (by rfl) ⟨1245104, by rfl⟩ : syracuseStep 1660139 = 2490209) B2490209
theorem B874057 : Blo 515797 874057 := bstep (se 2 (by rfl) ⟨327771, by rfl⟩ : syracuseStep 874057 = 655543) B655543
theorem B19879829 : Blo 515797 19879829 := bstep (se 6 (by rfl) ⟨465933, by rfl⟩ : syracuseStep 19879829 = 931867) B931867
theorem B1398775 : Blo 515797 1398775 := bstep (se 1 (by rfl) ⟨1049081, by rfl⟩ : syracuseStep 1398775 = 2098163) B2098163
theorem B3725623 : Blo 515797 3725623 := bstep (se 1 (by rfl) ⟨2794217, by rfl⟩ : syracuseStep 3725623 = 5588435) B5588435
theorem B2480503 : Blo 515797 2480503 := bstep (se 1 (by rfl) ⟨1860377, by rfl⟩ : syracuseStep 2480503 = 3720755) B3720755
theorem B776795 : Blo 515797 776795 := bstep (se 1 (by rfl) ⟨582596, by rfl⟩ : syracuseStep 776795 = 1165193) B1165193
theorem B776873 : Blo 515797 776873 := bstep (se 2 (by rfl) ⟨291327, by rfl⟩ : syracuseStep 776873 = 582655) B582655
theorem B8969069 : Blo 515797 8969069 := bstep (se 3 (by rfl) ⟨1681700, by rfl⟩ : syracuseStep 8969069 = 3363401) B3363401
theorem B777209 : Blo 515797 777209 := bstep (se 2 (by rfl) ⟨291453, by rfl⟩ : syracuseStep 777209 = 582907) B582907
theorem B3922991 : Blo 515797 3922991 := bstep (se 1 (by rfl) ⟨2942243, by rfl⟩ : syracuseStep 3922991 = 5884487) B5884487
theorem B6610207 : Blo 515797 6610207 := bstep (se 1 (by rfl) ⟨4957655, by rfl⟩ : syracuseStep 6610207 = 9915311) B9915311
theorem B777527 : Blo 515797 777527 := bstep (se 1 (by rfl) ⟨583145, by rfl⟩ : syracuseStep 777527 = 1166291) B1166291
theorem B777707 : Blo 515797 777707 := bstep (se 1 (by rfl) ⟨583280, by rfl⟩ : syracuseStep 777707 = 1166561) B1166561
theorem B777911 : Blo 515797 777911 := bstep (se 1 (by rfl) ⟨583433, by rfl⟩ : syracuseStep 777911 = 1166867) B1166867
theorem B876379 : Blo 515797 876379 := bstep (se 1 (by rfl) ⟨657284, by rfl⟩ : syracuseStep 876379 = 1314569) B1314569
theorem B3727241 : Blo 515797 3727241 := bstep (se 2 (by rfl) ⟨1397715, by rfl⟩ : syracuseStep 3727241 = 2795431) B2795431
theorem B876575 : Blo 515797 876575 := bstep (se 1 (by rfl) ⟨657431, by rfl⟩ : syracuseStep 876575 = 1314863) B1314863
theorem B778415 : Blo 515797 778415 := bstep (se 1 (by rfl) ⟨583811, by rfl⟩ : syracuseStep 778415 = 1167623) B1167623
theorem B778463 : Blo 515797 778463 := bstep (se 1 (by rfl) ⟨583847, by rfl⟩ : syracuseStep 778463 = 1167695) B1167695
theorem B516379 : Blo 515797 516379 := bstep (se 1 (by rfl) ⟨387284, by rfl⟩ : syracuseStep 516379 = 774569) B774569
theorem B778907 : Blo 515797 778907 := bstep (se 1 (by rfl) ⟨584180, by rfl⟩ : syracuseStep 778907 = 1168361) B1168361
theorem B778943 : Blo 515797 778943 := bstep (se 1 (by rfl) ⟨584207, by rfl⟩ : syracuseStep 778943 = 1168415) B1168415
theorem B516839 : Blo 515797 516839 := bstep (se 1 (by rfl) ⟨387629, by rfl⟩ : syracuseStep 516839 = 775259) B775259
theorem B516847 : Blo 515797 516847 := bstep (se 1 (by rfl) ⟨387635, by rfl⟩ : syracuseStep 516847 = 775271) B775271
theorem B516935 : Blo 515797 516935 := bstep (se 1 (by rfl) ⟨387701, by rfl⟩ : syracuseStep 516935 = 775403) B775403
theorem B779111 : Blo 515797 779111 := bstep (se 1 (by rfl) ⟨584333, by rfl⟩ : syracuseStep 779111 = 1168667) B1168667
theorem B582727 : Blo 515797 582727 := bstep (se 1 (by rfl) ⟨437045, by rfl⟩ : syracuseStep 582727 = 874091) B874091
theorem B779447 : Blo 515797 779447 := bstep (se 1 (by rfl) ⟨584585, by rfl⟩ : syracuseStep 779447 = 1169171) B1169171
theorem B517371 : Blo 515797 517371 := bstep (se 1 (by rfl) ⟨388028, by rfl⟩ : syracuseStep 517371 = 776057) B776057
theorem B10806857 : Blo 515797 10806857 := bstep (se 2 (by rfl) ⟨4052571, by rfl⟩ : syracuseStep 10806857 = 8105143) B8105143
theorem B517759 : Blo 515797 517759 := bstep (se 1 (by rfl) ⟨388319, by rfl⟩ : syracuseStep 517759 = 776639) B776639
theorem B517887 : Blo 515797 517887 := bstep (se 1 (by rfl) ⟨388415, by rfl⟩ : syracuseStep 517887 = 776831) B776831
theorem B4483259 : Blo 515797 4483259 := bstep (se 1 (by rfl) ⟨3362444, by rfl⟩ : syracuseStep 4483259 = 6724889) B6724889
theorem B518463 : Blo 515797 518463 := bstep (se 1 (by rfl) ⟨388847, by rfl⟩ : syracuseStep 518463 = 777695) B777695
theorem B584095 : Blo 515797 584095 := bstep (se 1 (by rfl) ⟨438071, by rfl⟩ : syracuseStep 584095 = 876143) B876143
theorem B518863 : Blo 515797 518863 := bstep (se 1 (by rfl) ⟨389147, by rfl⟩ : syracuseStep 518863 = 778295) B778295
theorem B518911 : Blo 515797 518911 := bstep (se 1 (by rfl) ⟨389183, by rfl⟩ : syracuseStep 518911 = 778367) B778367
theorem B1960919 : Blo 515797 1960919 := bstep (se 1 (by rfl) ⟨1470689, by rfl⟩ : syracuseStep 1960919 = 2941379) B2941379
theorem B26864759 : Blo 515797 26864759 := bstep (se 1 (by rfl) ⟨20148569, by rfl⟩ : syracuseStep 26864759 = 40297139) B40297139
theorem B40464251 : Blo 515797 40464251 := bstep (se 1 (by rfl) ⟨30348188, by rfl⟩ : syracuseStep 40464251 = 60696377) B60696377
theorem B3993583 : Blo 515797 3993583 := bstep (se 1 (by rfl) ⟨2995187, by rfl⟩ : syracuseStep 3993583 = 5990375) B5990375
theorem B1306651 : Blo 515797 1306651 := bstep (se 1 (by rfl) ⟨979988, by rfl⟩ : syracuseStep 1306651 = 1959977) B1959977
theorem B6647933 : Blo 515797 6647933 := bstep (se 3 (by rfl) ⟨1246487, by rfl⟩ : syracuseStep 6647933 = 2492975) B2492975
theorem B1306793 : Blo 515797 1306793 := bstep (se 2 (by rfl) ⟨490047, by rfl⟩ : syracuseStep 1306793 = 980095) B980095
theorem B4419791 : Blo 515797 4419791 := bstep (se 1 (by rfl) ⟨3314843, by rfl⟩ : syracuseStep 4419791 = 6629687) B6629687
theorem B6615539 : Blo 515797 6615539 := bstep (se 1 (by rfl) ⟨4961654, by rfl⟩ : syracuseStep 6615539 = 9923309) B9923309
theorem B1471031 : Blo 515797 1471031 := bstep (se 1 (by rfl) ⟨1103273, by rfl⟩ : syracuseStep 1471031 = 2206547) B2206547
theorem B1177055 : Blo 515797 1177055 := bstep (se 1 (by rfl) ⟨882791, by rfl⟩ : syracuseStep 1177055 = 1765583) B1765583
theorem B555071 : Blo 515797 555071 := bstep (se 1 (by rfl) ⟨416303, by rfl⟩ : syracuseStep 555071 = 832607) B832607
theorem B2947529 : Blo 515797 2947529 := bstep (se 2 (by rfl) ⟨1105323, by rfl⟩ : syracuseStep 2947529 = 2210647) B2210647
theorem B1964519 : Blo 515797 1964519 := bstep (se 1 (by rfl) ⟨1473389, by rfl⟩ : syracuseStep 1964519 = 2946779) B2946779
theorem B51706507 : Blo 515797 51706507 := bstep (se 1 (by rfl) ⟨38779880, by rfl⟩ : syracuseStep 51706507 = 77559761) B77559761
theorem B1997779 : Blo 515797 1997779 := bstep (se 1 (by rfl) ⟨1498334, by rfl⟩ : syracuseStep 1997779 = 2996669) B2996669
theorem B5307569 : Blo 515797 5307569 := bstep (se 2 (by rfl) ⟨1990338, by rfl⟩ : syracuseStep 5307569 = 3980677) B3980677
theorem B654895 : Blo 515797 654895 := bstep (se 1 (by rfl) ⟨491171, by rfl⟩ : syracuseStep 654895 = 982343) B982343
theorem B15138791 : Blo 515797 15138791 := bstep (se 1 (by rfl) ⟨11354093, by rfl⟩ : syracuseStep 15138791 = 22708187) B22708187
theorem B983087 : Blo 515797 983087 := bstep (se 1 (by rfl) ⟨737315, by rfl⟩ : syracuseStep 983087 = 1474631) B1474631
theorem B885095 : Blo 515797 885095 := bstep (se 1 (by rfl) ⟨663821, by rfl⟩ : syracuseStep 885095 = 1327643) B1327643
theorem B5604005 : Blo 515797 5604005 := bstep (se 4 (by rfl) ⟨525375, by rfl⟩ : syracuseStep 5604005 = 1050751) B1050751
theorem B1475759 : Blo 515797 1475759 := bstep (se 1 (by rfl) ⟨1106819, by rfl⟩ : syracuseStep 1475759 = 2213639) B2213639
theorem B4982107 : Blo 515797 4982107 := bstep (se 1 (by rfl) ⟨3736580, by rfl⟩ : syracuseStep 4982107 = 7473161) B7473161
theorem B656743 : Blo 515797 656743 := bstep (se 1 (by rfl) ⟨492557, by rfl⟩ : syracuseStep 656743 = 985115) B985115
theorem B2491883 : Blo 515797 2491883 := bstep (se 1 (by rfl) ⟨1868912, by rfl⟩ : syracuseStep 2491883 = 3737825) B3737825
theorem B3934655 : Blo 515797 3934655 := bstep (se 1 (by rfl) ⟨2950991, by rfl⟩ : syracuseStep 3934655 = 5901983) B5901983
theorem B4984105 : Blo 515797 4984105 := bstep (se 2 (by rfl) ⟨1869039, by rfl⟩ : syracuseStep 4984105 = 3738079) B3738079
theorem B1970153 : Blo 515797 1970153 := bstep (se 2 (by rfl) ⟨738807, by rfl⟩ : syracuseStep 1970153 = 1477615) B1477615
theorem B1970351 : Blo 515797 1970351 := bstep (se 1 (by rfl) ⟨1477763, by rfl⟩ : syracuseStep 1970351 = 2955527) B2955527
theorem B1971155 : Blo 515797 1971155 := bstep (se 1 (by rfl) ⟨1478366, by rfl⟩ : syracuseStep 1971155 = 2956733) B2956733
theorem B1742201 : Blo 515797 1742201 := bstep (se 2 (by rfl) ⟨653325, by rfl⟩ : syracuseStep 1742201 = 1306651) B1306651
theorem B7476623 : Blo 515797 7476623 := bstep (se 1 (by rfl) ⟨5607467, by rfl⟩ : syracuseStep 7476623 = 11214935) B11214935
theorem B1480189 : Blo 515797 1480189 := bstep (se 3 (by rfl) ⟨277535, by rfl⟩ : syracuseStep 1480189 = 555071) B555071
theorem B1972583 : Blo 515797 1972583 := bstep (se 1 (by rfl) ⟨1479437, by rfl⟩ : syracuseStep 1972583 = 2958875) B2958875
theorem B2628287 : Blo 515797 2628287 := bstep (se 1 (by rfl) ⟨1971215, by rfl⟩ : syracuseStep 2628287 = 3942431) B3942431
theorem B2988839 : Blo 515797 2988839 := bstep (se 1 (by rfl) ⟨2241629, by rfl⟩ : syracuseStep 2988839 = 4483259) B4483259
theorem B26976167 : Blo 515797 26976167 := bstep (se 1 (by rfl) ⟨20232125, by rfl⟩ : syracuseStep 26976167 = 40464251) B40464251
theorem B2629583 : Blo 515797 2629583 := bstep (se 1 (by rfl) ⟨1972187, by rfl⟩ : syracuseStep 2629583 = 3944375) B3944375
theorem B4431955 : Blo 515797 4431955 := bstep (se 1 (by rfl) ⟨3323966, by rfl⟩ : syracuseStep 4431955 = 6647933) B6647933
theorem B4202617 : Blo 515797 4202617 := bstep (se 2 (by rfl) ⟨1575981, by rfl⟩ : syracuseStep 4202617 = 3151963) B3151963
theorem B2663705 : Blo 515797 2663705 := bstep (se 2 (by rfl) ⟨998889, by rfl⟩ : syracuseStep 2663705 = 1997779) B1997779
theorem B25110587 : Blo 515797 25110587 := bstep (se 1 (by rfl) ⟨18832940, by rfl⟩ : syracuseStep 25110587 = 37665881) B37665881
theorem B827370449 : Blo 515797 827370449 := bstep (se 2 (by rfl) ⟨310263918, by rfl⟩ : syracuseStep 827370449 = 620527837) B620527837
theorem B2666945 : Blo 515797 2666945 := bstep (se 2 (by rfl) ⟨1000104, by rfl⟩ : syracuseStep 2666945 = 2000209) B2000209
theorem B4436603 : Blo 515797 4436603 := bstep (se 1 (by rfl) ⟨3327452, by rfl⟩ : syracuseStep 4436603 = 6654905) B6654905
theorem B1323803 : Blo 515797 1323803 := bstep (se 1 (by rfl) ⟨992852, by rfl⟩ : syracuseStep 1323803 = 1985705) B1985705
theorem B1750139 : Blo 515797 1750139 := bstep (se 1 (by rfl) ⟨1312604, by rfl⟩ : syracuseStep 1750139 = 2625209) B2625209
theorem B1160999 : Blo 515797 1160999 := bstep (se 1 (by rfl) ⟨870749, by rfl⟩ : syracuseStep 1160999 = 1741499) B1741499
theorem B1161071 : Blo 515797 1161071 := bstep (se 1 (by rfl) ⟨870803, by rfl⟩ : syracuseStep 1161071 = 1741607) B1741607
theorem B13253219 : Blo 515797 13253219 := bstep (se 1 (by rfl) ⟨9939914, by rfl⟩ : syracuseStep 13253219 = 19879829) B19879829
theorem B5979379 : Blo 515797 5979379 := bstep (se 1 (by rfl) ⟨4484534, by rfl⟩ : syracuseStep 5979379 = 8969069) B8969069
theorem B5324777 : Blo 515797 5324777 := bstep (se 2 (by rfl) ⟨1996791, by rfl⟩ : syracuseStep 5324777 = 3993583) B3993583
theorem B1753919 : Blo 515797 1753919 := bstep (se 1 (by rfl) ⟨1315439, by rfl⟩ : syracuseStep 1753919 = 2630879) B2630879
theorem B1164599 : Blo 515797 1164599 := bstep (se 1 (by rfl) ⟨873449, by rfl⟩ : syracuseStep 1164599 = 1746899) B1746899
theorem B1164671 : Blo 515797 1164671 := bstep (se 1 (by rfl) ⟨873503, by rfl⟩ : syracuseStep 1164671 = 1747007) B1747007
theorem B15189535 : Blo 515797 15189535 := bstep (se 1 (by rfl) ⟨11392151, by rfl⟩ : syracuseStep 15189535 = 22784303) B22784303
theorem B26888057 : Blo 515797 26888057 := bstep (se 2 (by rfl) ⟨10083021, by rfl⟩ : syracuseStep 26888057 = 20166043) B20166043
theorem B4966267 : Blo 515797 4966267 := bstep (se 1 (by rfl) ⟨3724700, by rfl⟩ : syracuseStep 4966267 = 7449401) B7449401
theorem B17909839 : Blo 515797 17909839 := bstep (se 1 (by rfl) ⟨13432379, by rfl⟩ : syracuseStep 17909839 = 26864759) B26864759
theorem B1165409 : Blo 515797 1165409 := bstep (se 2 (by rfl) ⟨437028, by rfl⟩ : syracuseStep 1165409 = 874057) B874057
theorem B871195 : Blo 515797 871195 := bstep (se 1 (by rfl) ⟨653396, by rfl⟩ : syracuseStep 871195 = 1306793) B1306793
theorem B4410359 : Blo 515797 4410359 := bstep (se 1 (by rfl) ⟨3307769, by rfl⟩ : syracuseStep 4410359 = 6615539) B6615539
theorem B4967497 : Blo 515797 4967497 := bstep (se 2 (by rfl) ⟨1862811, by rfl⟩ : syracuseStep 4967497 = 3725623) B3725623
theorem B9948527 : Blo 515797 9948527 := bstep (se 1 (by rfl) ⟨7461395, by rfl⟩ : syracuseStep 9948527 = 14922791) B14922791
theorem B2215363 : Blo 515797 2215363 := bstep (se 1 (by rfl) ⟨1661522, by rfl⟩ : syracuseStep 2215363 = 3323045) B3323045
theorem B4968499 : Blo 515797 4968499 := bstep (se 1 (by rfl) ⟨3726374, by rfl⟩ : syracuseStep 4968499 = 7452749) B7452749
theorem B157012111 : Blo 515797 157012111 := bstep (se 1 (by rfl) ⟨117759083, by rfl⟩ : syracuseStep 157012111 = 235518167) B235518167
theorem B8409257 : Blo 515797 8409257 := bstep (se 2 (by rfl) ⟨3153471, by rfl⟩ : syracuseStep 8409257 = 6306943) B6306943
theorem B873193 : Blo 515797 873193 := bstep (se 2 (by rfl) ⟨327447, by rfl⟩ : syracuseStep 873193 = 654895) B654895
theorem B1495999 : Blo 515797 1495999 := bstep (se 1 (by rfl) ⟨1121999, by rfl⟩ : syracuseStep 1495999 = 2243999) B2243999
theorem B2217071 : Blo 515797 2217071 := bstep (se 1 (by rfl) ⟨1662803, by rfl⟩ : syracuseStep 2217071 = 3325607) B3325607
theorem B1168505 : Blo 515797 1168505 := bstep (se 2 (by rfl) ⟨438189, by rfl⟩ : syracuseStep 1168505 = 876379) B876379
theorem B1168811 : Blo 515797 1168811 := bstep (se 1 (by rfl) ⟨876608, by rfl⟩ : syracuseStep 1168811 = 1753217) B1753217
theorem B776063 : Blo 515797 776063 := bstep (se 1 (by rfl) ⟨582047, by rfl⟩ : syracuseStep 776063 = 1164095) B1164095
theorem B874543 : Blo 515797 874543 := bstep (se 1 (by rfl) ⟨655907, by rfl⟩ : syracuseStep 874543 = 1311815) B1311815
theorem B776687 : Blo 515797 776687 := bstep (se 1 (by rfl) ⟨582515, by rfl⟩ : syracuseStep 776687 = 1165031) B1165031
theorem B580315 : Blo 515797 580315 := bstep (se 1 (by rfl) ⟨435236, by rfl⟩ : syracuseStep 580315 = 870473) B870473
theorem B776969 : Blo 515797 776969 := bstep (se 2 (by rfl) ⟨291363, by rfl⟩ : syracuseStep 776969 = 582727) B582727
theorem B515867 : Blo 515797 515867 := bstep (se 1 (by rfl) ⟨386900, by rfl⟩ : syracuseStep 515867 = 773801) B773801
theorem B516123 : Blo 515797 516123 := bstep (se 1 (by rfl) ⟨387092, by rfl⟩ : syracuseStep 516123 = 774185) B774185
theorem B7463015 : Blo 515797 7463015 := bstep (se 1 (by rfl) ⟨5597261, by rfl⟩ : syracuseStep 7463015 = 11194523) B11194523
theorem B516251 : Blo 515797 516251 := bstep (se 1 (by rfl) ⟨387188, by rfl⟩ : syracuseStep 516251 = 774377) B774377
theorem B516335 : Blo 515797 516335 := bstep (se 1 (by rfl) ⟨387251, by rfl⟩ : syracuseStep 516335 = 774503) B774503
theorem B778523 : Blo 515797 778523 := bstep (se 1 (by rfl) ⟨583892, by rfl⟩ : syracuseStep 778523 = 1167785) B1167785
theorem B516583 : Blo 515797 516583 := bstep (se 1 (by rfl) ⟨387437, by rfl⟩ : syracuseStep 516583 = 774875) B774875
theorem B778793 : Blo 515797 778793 := bstep (se 2 (by rfl) ⟨292047, by rfl⟩ : syracuseStep 778793 = 584095) B584095
theorem B2482751 : Blo 515797 2482751 := bstep (se 1 (by rfl) ⟨1862063, by rfl⟩ : syracuseStep 2482751 = 3724127) B3724127
theorem B516859 : Blo 515797 516859 := bstep (se 1 (by rfl) ⟨387644, by rfl⟩ : syracuseStep 516859 = 775289) B775289
theorem B516891 : Blo 515797 516891 := bstep (se 1 (by rfl) ⟨387668, by rfl⟩ : syracuseStep 516891 = 775337) B775337
theorem B1106759 : Blo 515797 1106759 := bstep (se 1 (by rfl) ⟨830069, by rfl⟩ : syracuseStep 1106759 = 1660139) B1660139
theorem B1598717 : Blo 515797 1598717 := bstep (se 3 (by rfl) ⟨299759, by rfl⟩ : syracuseStep 1598717 = 599519) B599519
theorem B517863 : Blo 515797 517863 := bstep (se 1 (by rfl) ⟨388397, by rfl⟩ : syracuseStep 517863 = 776795) B776795
theorem B517915 : Blo 515797 517915 := bstep (se 1 (by rfl) ⟨388436, by rfl⟩ : syracuseStep 517915 = 776873) B776873
theorem B518139 : Blo 515797 518139 := bstep (se 1 (by rfl) ⟨388604, by rfl⟩ : syracuseStep 518139 = 777209) B777209
theorem B2615327 : Blo 515797 2615327 := bstep (se 1 (by rfl) ⟨1961495, by rfl⟩ : syracuseStep 2615327 = 3922991) B3922991
theorem B518351 : Blo 515797 518351 := bstep (se 1 (by rfl) ⟨388763, by rfl⟩ : syracuseStep 518351 = 777527) B777527
theorem B518471 : Blo 515797 518471 := bstep (se 1 (by rfl) ⟨388853, by rfl⟩ : syracuseStep 518471 = 777707) B777707
theorem B518607 : Blo 515797 518607 := bstep (se 1 (by rfl) ⟨388955, by rfl⟩ : syracuseStep 518607 = 777911) B777911
theorem B21326327 : Blo 515797 21326327 := bstep (se 1 (by rfl) ⟨15994745, by rfl⟩ : syracuseStep 21326327 = 31989491) B31989491
theorem B2484827 : Blo 515797 2484827 := bstep (se 1 (by rfl) ⟨1863620, by rfl⟩ : syracuseStep 2484827 = 3727241) B3727241
theorem B584383 : Blo 515797 584383 := bstep (se 1 (by rfl) ⟨438287, by rfl⟩ : syracuseStep 584383 = 876575) B876575
theorem B518943 : Blo 515797 518943 := bstep (se 1 (by rfl) ⟨389207, by rfl⟩ : syracuseStep 518943 = 778415) B778415
theorem B518975 : Blo 515797 518975 := bstep (se 1 (by rfl) ⟨389231, by rfl⟩ : syracuseStep 518975 = 778463) B778463
theorem B519271 : Blo 515797 519271 := bstep (se 1 (by rfl) ⟨389453, by rfl⟩ : syracuseStep 519271 = 778907) B778907
theorem B519295 : Blo 515797 519295 := bstep (se 1 (by rfl) ⟨389471, by rfl⟩ : syracuseStep 519295 = 778943) B778943
theorem B519407 : Blo 515797 519407 := bstep (se 1 (by rfl) ⟨389555, by rfl⟩ : syracuseStep 519407 = 779111) B779111
theorem B519631 : Blo 515797 519631 := bstep (se 1 (by rfl) ⟨389723, by rfl⟩ : syracuseStep 519631 = 779447) B779447
theorem B7204571 : Blo 515797 7204571 := bstep (se 1 (by rfl) ⟨5403428, by rfl⟩ : syracuseStep 7204571 = 10806857) B10806857
theorem B1307279 : Blo 515797 1307279 := bstep (se 1 (by rfl) ⟨980459, by rfl⟩ : syracuseStep 1307279 = 1960919) B1960919
theorem B1865033 : Blo 515797 1865033 := bstep (se 2 (by rfl) ⟨699387, by rfl⟩ : syracuseStep 1865033 = 1398775) B1398775
theorem B2946527 : Blo 515797 2946527 := bstep (se 1 (by rfl) ⟨2209895, by rfl⟩ : syracuseStep 2946527 = 4419791) B4419791
theorem B980687 : Blo 515797 980687 := bstep (se 1 (by rfl) ⟨735515, by rfl⟩ : syracuseStep 980687 = 1471031) B1471031
theorem B3307337 : Blo 515797 3307337 := bstep (se 2 (by rfl) ⟨1240251, by rfl⟩ : syracuseStep 3307337 = 2480503) B2480503
theorem B68942009 : Blo 515797 68942009 := bstep (se 2 (by rfl) ⟨25853253, by rfl⟩ : syracuseStep 68942009 = 51706507) B51706507
theorem B784703 : Blo 515797 784703 := bstep (se 1 (by rfl) ⟨588527, by rfl⟩ : syracuseStep 784703 = 1177055) B1177055
theorem B1965019 : Blo 515797 1965019 := bstep (se 1 (by rfl) ⟨1473764, by rfl⟩ : syracuseStep 1965019 = 2947529) B2947529
theorem B1309679 : Blo 515797 1309679 := bstep (se 1 (by rfl) ⟨982259, by rfl⟩ : syracuseStep 1309679 = 1964519) B1964519
theorem B8813609 : Blo 515797 8813609 := bstep (se 2 (by rfl) ⟨3305103, by rfl⟩ : syracuseStep 8813609 = 6610207) B6610207
theorem B621803 : Blo 515797 621803 := bstep (se 1 (by rfl) ⟨466352, by rfl⟩ : syracuseStep 621803 = 932705) B932705
theorem B3538379 : Blo 515797 3538379 := bstep (se 1 (by rfl) ⟨2653784, by rfl⟩ : syracuseStep 3538379 = 5307569) B5307569
theorem B10092527 : Blo 515797 10092527 := bstep (se 1 (by rfl) ⟨7569395, by rfl⟩ : syracuseStep 10092527 = 15138791) B15138791
theorem B655391 : Blo 515797 655391 := bstep (se 1 (by rfl) ⟨491543, by rfl⟩ : syracuseStep 655391 = 983087) B983087
theorem B5603489 : Blo 515797 5603489 := bstep (se 2 (by rfl) ⟨2101308, by rfl⟩ : syracuseStep 5603489 = 4202617) B4202617
theorem B590063 : Blo 515797 590063 := bstep (se 1 (by rfl) ⟨442547, by rfl⟩ : syracuseStep 590063 = 885095) B885095
theorem B983839 : Blo 515797 983839 := bstep (se 1 (by rfl) ⟨737879, by rfl⟩ : syracuseStep 983839 = 1475759) B1475759
theorem B17925371 : Blo 515797 17925371 := bstep (se 1 (by rfl) ⟨13444028, by rfl⟩ : syracuseStep 17925371 = 26888057) B26888057
theorem B2623103 : Blo 515797 2623103 := bstep (se 1 (by rfl) ⟨1967327, by rfl⟩ : syracuseStep 2623103 = 3934655) B3934655
theorem B14944013 : Blo 515797 14944013 := bstep (se 3 (by rfl) ⟨2802002, by rfl⟩ : syracuseStep 14944013 = 5604005) B5604005
theorem B6621689 : Blo 515797 6621689 := bstep (se 2 (by rfl) ⟨2483133, by rfl⟩ : syracuseStep 6621689 = 4966267) B4966267
theorem B1313435 : Blo 515797 1313435 := bstep (se 1 (by rfl) ⟨985076, by rfl⟩ : syracuseStep 1313435 = 1970153) B1970153
theorem B5606171 : Blo 515797 5606171 := bstep (se 1 (by rfl) ⟨4204628, by rfl⟩ : syracuseStep 5606171 = 8409257) B8409257
theorem B1313567 : Blo 515797 1313567 := bstep (se 1 (by rfl) ⟨985175, by rfl⟩ : syracuseStep 1313567 = 1970351) B1970351
theorem B1314103 : Blo 515797 1314103 := bstep (se 1 (by rfl) ⟨985577, by rfl⟩ : syracuseStep 1314103 = 1971155) B1971155
theorem B4984415 : Blo 515797 4984415 := bstep (se 1 (by rfl) ⟨3738311, by rfl⟩ : syracuseStep 4984415 = 7476623) B7476623
theorem B6623329 : Blo 515797 6623329 := bstep (se 2 (by rfl) ⟨2483748, by rfl⟩ : syracuseStep 6623329 = 4967497) B4967497
theorem B1315055 : Blo 515797 1315055 := bstep (se 1 (by rfl) ⟨986291, by rfl⟩ : syracuseStep 1315055 = 1972583) B1972583
theorem B2953817 : Blo 515797 2953817 := bstep (se 2 (by rfl) ⟨1107681, by rfl⟩ : syracuseStep 2953817 = 2215363) B2215363
theorem B6624665 : Blo 515797 6624665 := bstep (se 2 (by rfl) ⟨2484249, by rfl⟩ : syracuseStep 6624665 = 4968499) B4968499
theorem B1775803 : Blo 515797 1775803 := bstep (se 1 (by rfl) ⟨1331852, by rfl⟩ : syracuseStep 1775803 = 2663705) B2663705
theorem B1743551 : Blo 515797 1743551 := bstep (se 1 (by rfl) ⟨1307663, by rfl⟩ : syracuseStep 1743551 = 2615327) B2615327
theorem B1973585 : Blo 515797 1973585 := bstep (se 2 (by rfl) ⟨740094, by rfl⟩ : syracuseStep 1973585 = 1480189) B1480189
theorem B81010853 : Blo 515797 81010853 := bstep (se 4 (by rfl) ⟨7594767, by rfl⟩ : syracuseStep 81010853 = 15189535) B15189535
theorem B1777963 : Blo 515797 1777963 := bstep (se 1 (by rfl) ⟨1333472, by rfl⟩ : syracuseStep 1777963 = 2666945) B2666945
theorem B2957735 : Blo 515797 2957735 := bstep (se 1 (by rfl) ⟨2218301, by rfl⟩ : syracuseStep 2957735 = 4436603) B4436603
theorem B2204891 : Blo 515797 2204891 := bstep (se 1 (by rfl) ⟨1653668, by rfl⟩ : syracuseStep 2204891 = 3307337) B3307337
theorem B7972505 : Blo 515797 7972505 := bstep (se 2 (by rfl) ⟨2989689, by rfl⟩ : syracuseStep 7972505 = 5979379) B5979379
theorem B5875739 : Blo 515797 5875739 := bstep (se 1 (by rfl) ⟨4406804, by rfl⟩ : syracuseStep 5875739 = 8813609) B8813609
theorem B3549851 : Blo 515797 3549851 := bstep (se 1 (by rfl) ⟨2662388, by rfl⟩ : syracuseStep 3549851 = 5324777) B5324777
theorem B6728351 : Blo 515797 6728351 := bstep (se 1 (by rfl) ⟨5046263, by rfl⟩ : syracuseStep 6728351 = 10092527) B10092527
theorem B5909273 : Blo 515797 5909273 := bstep (se 2 (by rfl) ⟨2215977, by rfl⟩ : syracuseStep 5909273 = 4431955) B4431955
theorem B837397925 : Blo 515797 837397925 := bstep (se 4 (by rfl) ⟨78506055, by rfl⟩ : syracuseStep 837397925 = 157012111) B157012111
theorem B6632351 : Blo 515797 6632351 := bstep (se 1 (by rfl) ⟨4974263, by rfl⟩ : syracuseStep 6632351 = 9948527) B9948527
theorem B5912189 : Blo 515797 5912189 := bstep (se 3 (by rfl) ⟨1108535, by rfl⟩ : syracuseStep 5912189 = 2217071) B2217071
theorem B1161467 : Blo 515797 1161467 := bstep (se 1 (by rfl) ⟨871100, by rfl⟩ : syracuseStep 1161467 = 1742201) B1742201
theorem B1161593 : Blo 515797 1161593 := bstep (se 2 (by rfl) ⟨435597, by rfl⟩ : syracuseStep 1161593 = 871195) B871195
theorem B1752191 : Blo 515797 1752191 := bstep (se 1 (by rfl) ⟨1314143, by rfl⟩ : syracuseStep 1752191 = 2628287) B2628287
theorem B1753055 : Blo 515797 1753055 := bstep (se 1 (by rfl) ⟨1314791, by rfl⟩ : syracuseStep 1753055 = 2629583) B2629583
theorem B66961565 : Blo 515797 66961565 := bstep (se 3 (by rfl) ⟨12555293, by rfl⟩ : syracuseStep 66961565 = 25110587) B25110587
theorem B1655167 : Blo 515797 1655167 := bstep (se 1 (by rfl) ⟨1241375, by rfl⟩ : syracuseStep 1655167 = 2482751) B2482751
theorem B737839 : Blo 515797 737839 := bstep (se 1 (by rfl) ⟨553379, by rfl⟩ : syracuseStep 737839 = 1106759) B1106759
theorem B1065811 : Blo 515797 1065811 := bstep (se 1 (by rfl) ⟨799358, by rfl⟩ : syracuseStep 1065811 = 1598717) B1598717
theorem B1164257 : Blo 515797 1164257 := bstep (se 2 (by rfl) ⟨436596, by rfl⟩ : syracuseStep 1164257 = 873193) B873193
theorem B1656551 : Blo 515797 1656551 := bstep (se 1 (by rfl) ⟨1242413, by rfl⟩ : syracuseStep 1656551 = 2484827) B2484827
theorem B4803047 : Blo 515797 4803047 := bstep (se 1 (by rfl) ⟨3602285, by rfl⟩ : syracuseStep 4803047 = 7204571) B7204571
theorem B1166057 : Blo 515797 1166057 := bstep (se 2 (by rfl) ⟨437271, by rfl⟩ : syracuseStep 1166057 = 874543) B874543
theorem B871519 : Blo 515797 871519 := bstep (se 1 (by rfl) ⟨653639, by rfl⟩ : syracuseStep 871519 = 1307279) B1307279
theorem B1658141 : Blo 515797 1658141 := bstep (se 3 (by rfl) ⟨310901, by rfl⟩ : syracuseStep 1658141 = 621803) B621803
theorem B1166759 : Blo 515797 1166759 := bstep (se 1 (by rfl) ⟨875069, by rfl⟩ : syracuseStep 1166759 = 1750139) B1750139
theorem B773753 : Blo 515797 773753 := bstep (se 2 (by rfl) ⟨290157, by rfl⟩ : syracuseStep 773753 = 580315) B580315
theorem B773999 : Blo 515797 773999 := bstep (se 1 (by rfl) ⟨580499, by rfl⟩ : syracuseStep 773999 = 1160999) B1160999
theorem B774047 : Blo 515797 774047 := bstep (se 1 (by rfl) ⟨580535, by rfl⟩ : syracuseStep 774047 = 1161071) B1161071
theorem B45961339 : Blo 515797 45961339 := bstep (se 1 (by rfl) ⟨34471004, by rfl⟩ : syracuseStep 45961339 = 68942009) B68942009
theorem B8835479 : Blo 515797 8835479 := bstep (se 1 (by rfl) ⟨6626609, by rfl⟩ : syracuseStep 8835479 = 13253219) B13253219
theorem B873119 : Blo 515797 873119 := bstep (se 1 (by rfl) ⟨654839, by rfl⟩ : syracuseStep 873119 = 1309679) B1309679
theorem B1169279 : Blo 515797 1169279 := bstep (se 1 (by rfl) ⟨876959, by rfl⟩ : syracuseStep 1169279 = 1753919) B1753919
theorem B776399 : Blo 515797 776399 := bstep (se 1 (by rfl) ⟨582299, by rfl⟩ : syracuseStep 776399 = 1164599) B1164599
theorem B776447 : Blo 515797 776447 := bstep (se 1 (by rfl) ⟨582335, by rfl⟩ : syracuseStep 776447 = 1164671) B1164671
theorem B1661255 : Blo 515797 1661255 := bstep (se 1 (by rfl) ⟨1245941, by rfl⟩ : syracuseStep 1661255 = 2491883) B2491883
theorem B776939 : Blo 515797 776939 := bstep (se 1 (by rfl) ⟨582704, by rfl⟩ : syracuseStep 776939 = 1165409) B1165409
theorem B6642809 : Blo 515797 6642809 := bstep (se 2 (by rfl) ⟨2491053, by rfl⟩ : syracuseStep 6642809 = 4982107) B4982107
theorem B875657 : Blo 515797 875657 := bstep (se 2 (by rfl) ⟨328371, by rfl⟩ : syracuseStep 875657 = 656743) B656743
theorem B2940239 : Blo 515797 2940239 := bstep (se 1 (by rfl) ⟨2205179, by rfl⟩ : syracuseStep 2940239 = 4410359) B4410359
theorem B3530141 : Blo 515797 3530141 := bstep (se 3 (by rfl) ⟨661901, by rfl⟩ : syracuseStep 3530141 = 1323803) B1323803
theorem B23879785 : Blo 515797 23879785 := bstep (se 2 (by rfl) ⟨8954919, by rfl⟩ : syracuseStep 23879785 = 17909839) B17909839
theorem B779003 : Blo 515797 779003 := bstep (se 1 (by rfl) ⟨584252, by rfl⟩ : syracuseStep 779003 = 1168505) B1168505
theorem B779177 : Blo 515797 779177 := bstep (se 2 (by rfl) ⟨292191, by rfl⟩ : syracuseStep 779177 = 584383) B584383
theorem B779207 : Blo 515797 779207 := bstep (se 1 (by rfl) ⟨584405, by rfl⟩ : syracuseStep 779207 = 1168811) B1168811
theorem B517375 : Blo 515797 517375 := bstep (se 1 (by rfl) ⟨388031, by rfl⟩ : syracuseStep 517375 = 776063) B776063
theorem B517791 : Blo 515797 517791 := bstep (se 1 (by rfl) ⟨388343, by rfl⟩ : syracuseStep 517791 = 776687) B776687
theorem B6645473 : Blo 515797 6645473 := bstep (se 2 (by rfl) ⟨2492052, by rfl⟩ : syracuseStep 6645473 = 4984105) B4984105
theorem B517979 : Blo 515797 517979 := bstep (se 1 (by rfl) ⟨388484, by rfl⟩ : syracuseStep 517979 = 776969) B776969
theorem B1992559 : Blo 515797 1992559 := bstep (se 1 (by rfl) ⟨1494419, by rfl⟩ : syracuseStep 1992559 = 2988839) B2988839
theorem B2615165 : Blo 515797 2615165 := bstep (se 3 (by rfl) ⟨490343, by rfl⟩ : syracuseStep 2615165 = 980687) B980687
theorem B17984111 : Blo 515797 17984111 := bstep (se 1 (by rfl) ⟨13488083, by rfl⟩ : syracuseStep 17984111 = 26976167) B26976167
theorem B4975343 : Blo 515797 4975343 := bstep (se 1 (by rfl) ⟨3731507, by rfl⟩ : syracuseStep 4975343 = 7463015) B7463015
theorem B519015 : Blo 515797 519015 := bstep (se 1 (by rfl) ⟨389261, by rfl⟩ : syracuseStep 519015 = 778523) B778523
theorem B519195 : Blo 515797 519195 := bstep (se 1 (by rfl) ⟨389396, by rfl⟩ : syracuseStep 519195 = 778793) B778793
theorem B1994665 : Blo 515797 1994665 := bstep (se 2 (by rfl) ⟨747999, by rfl⟩ : syracuseStep 1994665 = 1495999) B1495999
theorem B14217551 : Blo 515797 14217551 := bstep (se 1 (by rfl) ⟨10663163, by rfl⟩ : syracuseStep 14217551 = 21326327) B21326327
theorem B551580299 : Blo 515797 551580299 := bstep (se 1 (by rfl) ⟨413685224, by rfl⟩ : syracuseStep 551580299 = 827370449) B827370449
theorem B1243355 : Blo 515797 1243355 := bstep (se 1 (by rfl) ⟨932516, by rfl⟩ : syracuseStep 1243355 = 1865033) B1865033
theorem B1964351 : Blo 515797 1964351 := bstep (se 1 (by rfl) ⟨1473263, by rfl⟩ : syracuseStep 1964351 = 2946527) B2946527
theorem B2620025 : Blo 515797 2620025 := bstep (se 2 (by rfl) ⟨982509, by rfl⟩ : syracuseStep 2620025 = 1965019) B1965019
theorem B523135 : Blo 515797 523135 := bstep (se 1 (by rfl) ⟨392351, by rfl⟩ : syracuseStep 523135 = 784703) B784703
theorem B2358919 : Blo 515797 2358919 := bstep (se 1 (by rfl) ⟨1769189, by rfl⟩ : syracuseStep 2358919 = 3538379) B3538379
theorem B3735659 : Blo 515797 3735659 := bstep (se 1 (by rfl) ⟨2801744, by rfl⟩ : syracuseStep 3735659 = 5603489) B5603489
theorem B1573501 : Blo 515797 1573501 := bstep (se 3 (by rfl) ⟨295031, by rfl⟩ : syracuseStep 1573501 = 590063) B590063
theorem B1311785 : Blo 515797 1311785 := bstep (se 2 (by rfl) ⟨491919, by rfl⟩ : syracuseStep 1311785 = 983839) B983839
theorem B9962675 : Blo 515797 9962675 := bstep (se 1 (by rfl) ⟨7472006, by rfl⟩ : syracuseStep 9962675 = 14944013) B14944013
theorem B3737447 : Blo 515797 3737447 := bstep (se 1 (by rfl) ⟨2803085, by rfl⟩ : syracuseStep 3737447 = 5606171) B5606171
theorem B2656745 : Blo 515797 2656745 := bstep (se 2 (by rfl) ⟨996279, by rfl⟩ : syracuseStep 2656745 = 1992559) B1992559
theorem B3935141 : Blo 515797 3935141 := bstep (se 4 (by rfl) ⟨368919, by rfl⟩ : syracuseStep 3935141 = 737839) B737839
theorem B1969211 : Blo 515797 1969211 := bstep (se 1 (by rfl) ⟨1476908, by rfl⟩ : syracuseStep 1969211 = 2953817) B2953817
theorem B4428539 : Blo 515797 4428539 := bstep (se 1 (by rfl) ⟨3321404, by rfl⟩ : syracuseStep 4428539 = 6642809) B6642809
theorem B1315723 : Blo 515797 1315723 := bstep (se 1 (by rfl) ⟨986792, by rfl⟩ : syracuseStep 1315723 = 1973585) B1973585
theorem B2659553 : Blo 515797 2659553 := bstep (se 2 (by rfl) ⟨997332, by rfl⟩ : syracuseStep 2659553 = 1994665) B1994665
theorem B54007235 : Blo 515797 54007235 := bstep (se 1 (by rfl) ⟨40505426, by rfl⟩ : syracuseStep 54007235 = 81010853) B81010853
theorem B61281785 : Blo 515797 61281785 := bstep (se 2 (by rfl) ⟨22980669, by rfl⟩ : syracuseStep 61281785 = 45961339) B45961339
theorem B1971823 : Blo 515797 1971823 := bstep (se 1 (by rfl) ⟨1478867, by rfl⟩ : syracuseStep 1971823 = 2957735) B2957735
theorem B3315613 : Blo 515797 3315613 := bstep (se 3 (by rfl) ⟨621677, by rfl⟩ : syracuseStep 3315613 = 1243355) B1243355
theorem B5315003 : Blo 515797 5315003 := bstep (se 1 (by rfl) ⟨3986252, by rfl⟩ : syracuseStep 5315003 = 7972505) B7972505
theorem B4430315 : Blo 515797 4430315 := bstep (se 1 (by rfl) ⟨3322736, by rfl⟩ : syracuseStep 4430315 = 6645473) B6645473
theorem B1743443 : Blo 515797 1743443 := bstep (se 1 (by rfl) ⟨1307582, by rfl⟩ : syracuseStep 1743443 = 2615165) B2615165
theorem B2366567 : Blo 515797 2366567 := bstep (se 1 (by rfl) ⟨1774925, by rfl⟩ : syracuseStep 2366567 = 3549851) B3549851
theorem B3316895 : Blo 515797 3316895 := bstep (se 1 (by rfl) ⟨2487671, by rfl⟩ : syracuseStep 3316895 = 4975343) B4975343
theorem B3939515 : Blo 515797 3939515 := bstep (se 1 (by rfl) ⟨2954636, by rfl⟩ : syracuseStep 3939515 = 5909273) B5909273
theorem B9478367 : Blo 515797 9478367 := bstep (se 1 (by rfl) ⟨7108775, by rfl⟩ : syracuseStep 9478367 = 14217551) B14217551
theorem B2367737 : Blo 515797 2367737 := bstep (se 2 (by rfl) ⟨887901, by rfl⟩ : syracuseStep 2367737 = 1775803) B1775803
theorem B3941459 : Blo 515797 3941459 := bstep (se 1 (by rfl) ⟨2956094, by rfl⟩ : syracuseStep 3941459 = 5912189) B5912189
theorem B697513 : Blo 515797 697513 := bstep (se 2 (by rfl) ⟨261567, by rfl⟩ : syracuseStep 697513 = 523135) B523135
theorem B1746683 : Blo 515797 1746683 := bstep (se 1 (by rfl) ⟨1310012, by rfl⟩ : syracuseStep 1746683 = 2620025) B2620025
theorem B1747709 : Blo 515797 1747709 := bstep (se 3 (by rfl) ⟨327695, by rfl⟩ : syracuseStep 1747709 = 655391) B655391
theorem B44641043 : Blo 515797 44641043 := bstep (se 1 (by rfl) ⟨33480782, by rfl⟩ : syracuseStep 44641043 = 66961565) B66961565
theorem B2370617 : Blo 515797 2370617 := bstep (se 2 (by rfl) ⟨888981, by rfl⟩ : syracuseStep 2370617 = 1777963) B1777963
theorem B2206889 : Blo 515797 2206889 := bstep (se 2 (by rfl) ⟨827583, by rfl⟩ : syracuseStep 2206889 = 1655167) B1655167
theorem B1748735 : Blo 515797 1748735 := bstep (se 1 (by rfl) ⟨1311551, by rfl⟩ : syracuseStep 1748735 = 2623103) B2623103
theorem B1421081 : Blo 515797 1421081 := bstep (se 2 (by rfl) ⟨532905, by rfl⟩ : syracuseStep 1421081 = 1065811) B1065811
theorem B3322943 : Blo 515797 3322943 := bstep (se 1 (by rfl) ⟨2492207, by rfl⟩ : syracuseStep 3322943 = 4984415) B4984415
theorem B1162025 : Blo 515797 1162025 := bstep (se 2 (by rfl) ⟨435759, by rfl⟩ : syracuseStep 1162025 = 871519) B871519
theorem B1752137 : Blo 515797 1752137 := bstep (se 2 (by rfl) ⟨657051, by rfl⟩ : syracuseStep 1752137 = 1314103) B1314103
theorem B1162367 : Blo 515797 1162367 := bstep (se 1 (by rfl) ⟨871775, by rfl⟩ : syracuseStep 1162367 = 1743551) B1743551
theorem B8831105 : Blo 515797 8831105 := bstep (se 2 (by rfl) ⟨3311664, by rfl⟩ : syracuseStep 8831105 = 6623329) B6623329
theorem B3917159 : Blo 515797 3917159 := bstep (se 1 (by rfl) ⟨2937869, by rfl⟩ : syracuseStep 3917159 = 5875739) B5875739
theorem B47957629 : Blo 515797 47957629 := bstep (se 3 (by rfl) ⟨8992055, by rfl⟩ : syracuseStep 47957629 = 17984111) B17984111
theorem B17942269 : Blo 515797 17942269 := bstep (se 3 (by rfl) ⟨3364175, by rfl⟩ : syracuseStep 17942269 = 6728351) B6728351
theorem B774311 : Blo 515797 774311 := bstep (se 1 (by rfl) ⟨580733, by rfl⟩ : syracuseStep 774311 = 1161467) B1161467
theorem B774395 : Blo 515797 774395 := bstep (se 1 (by rfl) ⟨580796, by rfl⟩ : syracuseStep 774395 = 1161593) B1161593
theorem B1168127 : Blo 515797 1168127 := bstep (se 1 (by rfl) ⟨876095, by rfl⟩ : syracuseStep 1168127 = 1752191) B1752191
theorem B1168703 : Blo 515797 1168703 := bstep (se 1 (by rfl) ⟨876527, by rfl⟩ : syracuseStep 1168703 = 1753055) B1753055
theorem B31839713 : Blo 515797 31839713 := bstep (se 2 (by rfl) ⟨11939892, by rfl⟩ : syracuseStep 31839713 = 23879785) B23879785
theorem B776171 : Blo 515797 776171 := bstep (se 1 (by rfl) ⟨582128, by rfl⟩ : syracuseStep 776171 = 1164257) B1164257
theorem B11950247 : Blo 515797 11950247 := bstep (se 1 (by rfl) ⟨8962685, by rfl⟩ : syracuseStep 11950247 = 17925371) B17925371
theorem B1104367 : Blo 515797 1104367 := bstep (se 1 (by rfl) ⟨828275, by rfl⟩ : syracuseStep 1104367 = 1656551) B1656551
theorem B3202031 : Blo 515797 3202031 := bstep (se 1 (by rfl) ⟨2401523, by rfl⟩ : syracuseStep 3202031 = 4803047) B4803047
theorem B4414459 : Blo 515797 4414459 := bstep (se 1 (by rfl) ⟨3310844, by rfl⟩ : syracuseStep 4414459 = 6621689) B6621689
theorem B875623 : Blo 515797 875623 := bstep (se 1 (by rfl) ⟨656717, by rfl⟩ : syracuseStep 875623 = 1313435) B1313435
theorem B777371 : Blo 515797 777371 := bstep (se 1 (by rfl) ⟨583028, by rfl⟩ : syracuseStep 777371 = 1166057) B1166057
theorem B875711 : Blo 515797 875711 := bstep (se 1 (by rfl) ⟨656783, by rfl⟩ : syracuseStep 875711 = 1313567) B1313567
theorem B1105427 : Blo 515797 1105427 := bstep (se 1 (by rfl) ⟨829070, by rfl⟩ : syracuseStep 1105427 = 1658141) B1658141
theorem B777839 : Blo 515797 777839 := bstep (se 1 (by rfl) ⟨583379, by rfl⟩ : syracuseStep 777839 = 1166759) B1166759
theorem B515835 : Blo 515797 515835 := bstep (se 1 (by rfl) ⟨386876, by rfl⟩ : syracuseStep 515835 = 773753) B773753
theorem B515999 : Blo 515797 515999 := bstep (se 1 (by rfl) ⟨386999, by rfl⟩ : syracuseStep 515999 = 773999) B773999
theorem B516031 : Blo 515797 516031 := bstep (se 1 (by rfl) ⟨387023, by rfl⟩ : syracuseStep 516031 = 774047) B774047
theorem B876703 : Blo 515797 876703 := bstep (se 1 (by rfl) ⟨657527, by rfl⟩ : syracuseStep 876703 = 1315055) B1315055
theorem B5890319 : Blo 515797 5890319 := bstep (se 1 (by rfl) ⟨4417739, by rfl⟩ : syracuseStep 5890319 = 8835479) B8835479
theorem B582079 : Blo 515797 582079 := bstep (se 1 (by rfl) ⟨436559, by rfl⟩ : syracuseStep 582079 = 873119) B873119
theorem B4416443 : Blo 515797 4416443 := bstep (se 1 (by rfl) ⟨3312332, by rfl⟩ : syracuseStep 4416443 = 6624665) B6624665
theorem B779519 : Blo 515797 779519 := bstep (se 1 (by rfl) ⟨584639, by rfl⟩ : syracuseStep 779519 = 1169279) B1169279
theorem B517599 : Blo 515797 517599 := bstep (se 1 (by rfl) ⟨388199, by rfl⟩ : syracuseStep 517599 = 776399) B776399
theorem B517631 : Blo 515797 517631 := bstep (se 1 (by rfl) ⟨388223, by rfl⟩ : syracuseStep 517631 = 776447) B776447
theorem B1107503 : Blo 515797 1107503 := bstep (se 1 (by rfl) ⟨830627, by rfl⟩ : syracuseStep 1107503 = 1661255) B1661255
theorem B517959 : Blo 515797 517959 := bstep (se 1 (by rfl) ⟨388469, by rfl⟩ : syracuseStep 517959 = 776939) B776939
theorem B583771 : Blo 515797 583771 := bstep (se 1 (by rfl) ⟨437828, by rfl⟩ : syracuseStep 583771 = 875657) B875657
theorem B1960159 : Blo 515797 1960159 := bstep (se 1 (by rfl) ⟨1470119, by rfl⟩ : syracuseStep 1960159 = 2940239) B2940239
theorem B2353427 : Blo 515797 2353427 := bstep (se 1 (by rfl) ⟨1765070, by rfl⟩ : syracuseStep 2353427 = 3530141) B3530141
theorem B519335 : Blo 515797 519335 := bstep (se 1 (by rfl) ⟨389501, by rfl⟩ : syracuseStep 519335 = 779003) B779003
theorem B519451 : Blo 515797 519451 := bstep (se 1 (by rfl) ⟨389588, by rfl⟩ : syracuseStep 519451 = 779177) B779177
theorem B519471 : Blo 515797 519471 := bstep (se 1 (by rfl) ⟨389603, by rfl⟩ : syracuseStep 519471 = 779207) B779207
theorem B1469927 : Blo 515797 1469927 := bstep (se 1 (by rfl) ⟨1102445, by rfl⟩ : syracuseStep 1469927 = 2204891) B2204891
theorem B558265283 : Blo 515797 558265283 := bstep (se 1 (by rfl) ⟨418698962, by rfl⟩ : syracuseStep 558265283 = 837397925) B837397925
theorem B367720199 : Blo 515797 367720199 := bstep (se 1 (by rfl) ⟨275790149, by rfl⟩ : syracuseStep 367720199 = 551580299) B551580299
theorem B4421567 : Blo 515797 4421567 := bstep (se 1 (by rfl) ⟨3316175, by rfl⟩ : syracuseStep 4421567 = 6632351) B6632351
theorem B1309567 : Blo 515797 1309567 := bstep (se 1 (by rfl) ⟨982175, by rfl⟩ : syracuseStep 1309567 = 1964351) B1964351
theorem B3145225 : Blo 515797 3145225 := bstep (se 2 (by rfl) ⟨1179459, by rfl⟩ : syracuseStep 3145225 = 2358919) B2358919
theorem B2490439 : Blo 515797 2490439 := bstep (se 1 (by rfl) ⟨1867829, by rfl⟩ : syracuseStep 2490439 = 3735659) B3735659
theorem B2098001 : Blo 515797 2098001 := bstep (se 2 (by rfl) ⟨786750, by rfl⟩ : syracuseStep 2098001 = 1573501) B1573501
theorem B2491631 : Blo 515797 2491631 := bstep (se 1 (by rfl) ⟨1868723, by rfl⟩ : syracuseStep 2491631 = 3737447) B3737447
theorem B1771163 : Blo 515797 1771163 := bstep (se 1 (by rfl) ⟨1328372, by rfl⟩ : syracuseStep 1771163 = 2656745) B2656745
theorem B2623427 : Blo 515797 2623427 := bstep (se 1 (by rfl) ⟨1967570, by rfl⟩ : syracuseStep 2623427 = 3935141) B3935141
theorem B1312807 : Blo 515797 1312807 := bstep (se 1 (by rfl) ⟨984605, by rfl⟩ : syracuseStep 1312807 = 1969211) B1969211
theorem B23923025 : Blo 515797 23923025 := bstep (se 2 (by rfl) ⟨8971134, by rfl⟩ : syracuseStep 23923025 = 17942269) B17942269
theorem B2952359 : Blo 515797 2952359 := bstep (se 1 (by rfl) ⟨2214269, by rfl⟩ : syracuseStep 2952359 = 4428539) B4428539
theorem B1773035 : Blo 515797 1773035 := bstep (se 1 (by rfl) ⟨1329776, by rfl⟩ : syracuseStep 1773035 = 2659553) B2659553
theorem B163418093 : Blo 515797 163418093 := bstep (se 3 (by rfl) ⟨30640892, by rfl⟩ : syracuseStep 163418093 = 61281785) B61281785
theorem B7966831 : Blo 515797 7966831 := bstep (se 1 (by rfl) ⟨5975123, by rfl⟩ : syracuseStep 7966831 = 11950247) B11950247
theorem B3543335 : Blo 515797 3543335 := bstep (se 1 (by rfl) ⟨2657501, by rfl⟩ : syracuseStep 3543335 = 5315003) B5315003
theorem B2953543 : Blo 515797 2953543 := bstep (se 1 (by rfl) ⟨2215157, by rfl⟩ : syracuseStep 2953543 = 4430315) B4430315
theorem B2134687 : Blo 515797 2134687 := bstep (se 1 (by rfl) ⟨1601015, by rfl⟩ : syracuseStep 2134687 = 3202031) B3202031
theorem B1577711 : Blo 515797 1577711 := bstep (se 1 (by rfl) ⟨1183283, by rfl⟩ : syracuseStep 1577711 = 2366567) B2366567
theorem B2626343 : Blo 515797 2626343 := bstep (se 1 (by rfl) ⟨1969757, by rfl⟩ : syracuseStep 2626343 = 3939515) B3939515
theorem B1578491 : Blo 515797 1578491 := bstep (se 1 (by rfl) ⟨1183868, by rfl⟩ : syracuseStep 1578491 = 2367737) B2367737
theorem B2627639 : Blo 515797 2627639 := bstep (se 1 (by rfl) ⟨1970729, by rfl⟩ : syracuseStep 2627639 = 3941459) B3941459
theorem B29760695 : Blo 515797 29760695 := bstep (se 1 (by rfl) ⟨22320521, by rfl⟩ : syracuseStep 29760695 = 44641043) B44641043
theorem B1580411 : Blo 515797 1580411 := bstep (se 1 (by rfl) ⟨1185308, by rfl⟩ : syracuseStep 1580411 = 2370617) B2370617
theorem B2629097 : Blo 515797 2629097 := bstep (se 2 (by rfl) ⟨985911, by rfl⟩ : syracuseStep 2629097 = 1971823) B1971823
theorem B1746089 : Blo 515797 1746089 := bstep (se 2 (by rfl) ⟨654783, by rfl⟩ : syracuseStep 1746089 = 1309567) B1309567
theorem B245146799 : Blo 515797 245146799 := bstep (se 1 (by rfl) ⟨183860099, by rfl⟩ : syracuseStep 245146799 = 367720199) B367720199
theorem B930017 : Blo 515797 930017 := bstep (se 2 (by rfl) ⟨348756, by rfl⟩ : syracuseStep 930017 = 697513) B697513
theorem B63943505 : Blo 515797 63943505 := bstep (se 2 (by rfl) ⟨23978814, by rfl⟩ : syracuseStep 63943505 = 47957629) B47957629
theorem B1162295 : Blo 515797 1162295 := bstep (se 1 (by rfl) ⟨871721, by rfl⟩ : syracuseStep 1162295 = 1743443) B1743443
theorem B2211263 : Blo 515797 2211263 := bstep (se 1 (by rfl) ⟨1658447, by rfl⟩ : syracuseStep 2211263 = 3316895) B3316895
theorem B736951 : Blo 515797 736951 := bstep (se 1 (by rfl) ⟨552713, by rfl⟩ : syracuseStep 736951 = 1105427) B1105427
theorem B738335 : Blo 515797 738335 := bstep (se 1 (by rfl) ⟨553751, by rfl⟩ : syracuseStep 738335 = 1107503) B1107503
theorem B1164455 : Blo 515797 1164455 := bstep (se 1 (by rfl) ⟨873341, by rfl⟩ : syracuseStep 1164455 = 1746683) B1746683
theorem B1754297 : Blo 515797 1754297 := bstep (se 2 (by rfl) ⟨657861, by rfl⟩ : syracuseStep 1754297 = 1315723) B1315723
theorem B1165139 : Blo 515797 1165139 := bstep (se 1 (by rfl) ⟨873854, by rfl⟩ : syracuseStep 1165139 = 1747709) B1747709
theorem B1165823 : Blo 515797 1165823 := bstep (se 1 (by rfl) ⟨874367, by rfl⟩ : syracuseStep 1165823 = 1748735) B1748735
theorem B2215295 : Blo 515797 2215295 := bstep (se 1 (by rfl) ⟨1661471, by rfl⟩ : syracuseStep 2215295 = 3322943) B3322943
theorem B5885945 : Blo 515797 5885945 := bstep (se 2 (by rfl) ⟨2207229, by rfl⟩ : syracuseStep 5885945 = 4414459) B4414459
theorem B1167497 : Blo 515797 1167497 := bstep (se 2 (by rfl) ⟨437811, by rfl⟩ : syracuseStep 1167497 = 875623) B875623
theorem B774683 : Blo 515797 774683 := bstep (se 1 (by rfl) ⟨581012, by rfl⟩ : syracuseStep 774683 = 1162025) B1162025
theorem B1168091 : Blo 515797 1168091 := bstep (se 1 (by rfl) ⟨876068, by rfl⟩ : syracuseStep 1168091 = 1752137) B1752137
theorem B774911 : Blo 515797 774911 := bstep (se 1 (by rfl) ⟨581183, by rfl⟩ : syracuseStep 774911 = 1162367) B1162367
theorem B5887403 : Blo 515797 5887403 := bstep (se 1 (by rfl) ⟨4415552, by rfl⟩ : syracuseStep 5887403 = 8831105) B8831105
theorem B1168937 : Blo 515797 1168937 := bstep (se 2 (by rfl) ⟨438351, by rfl⟩ : syracuseStep 1168937 = 876703) B876703
theorem B776105 : Blo 515797 776105 := bstep (se 2 (by rfl) ⟨291039, by rfl⟩ : syracuseStep 776105 = 582079) B582079
theorem B874523 : Blo 515797 874523 := bstep (se 1 (by rfl) ⟨655892, by rfl⟩ : syracuseStep 874523 = 1311785) B1311785
theorem B6641783 : Blo 515797 6641783 := bstep (se 1 (by rfl) ⟨4981337, by rfl⟩ : syracuseStep 6641783 = 9962675) B9962675
theorem B2611439 : Blo 515797 2611439 := bstep (se 1 (by rfl) ⟨1958579, by rfl⟩ : syracuseStep 2611439 = 3917159) B3917159
theorem B516207 : Blo 515797 516207 := bstep (se 1 (by rfl) ⟨387155, by rfl⟩ : syracuseStep 516207 = 774311) B774311
theorem B778361 : Blo 515797 778361 := bstep (se 2 (by rfl) ⟨291885, by rfl⟩ : syracuseStep 778361 = 583771) B583771
theorem B516263 : Blo 515797 516263 := bstep (se 1 (by rfl) ⟨387197, by rfl⟩ : syracuseStep 516263 = 774395) B774395
theorem B2613545 : Blo 515797 2613545 := bstep (se 2 (by rfl) ⟨980079, by rfl⟩ : syracuseStep 2613545 = 1960159) B1960159
theorem B778751 : Blo 515797 778751 := bstep (se 1 (by rfl) ⟨584063, by rfl⟩ : syracuseStep 778751 = 1168127) B1168127
theorem B779135 : Blo 515797 779135 := bstep (se 1 (by rfl) ⟨584351, by rfl⟩ : syracuseStep 779135 = 1168703) B1168703
theorem B36004823 : Blo 515797 36004823 := bstep (se 1 (by rfl) ⟨27003617, by rfl⟩ : syracuseStep 36004823 = 54007235) B54007235
theorem B21226475 : Blo 515797 21226475 := bstep (se 1 (by rfl) ⟨15919856, by rfl⟩ : syracuseStep 21226475 = 31839713) B31839713
theorem B517447 : Blo 515797 517447 := bstep (se 1 (by rfl) ⟨388085, by rfl⟩ : syracuseStep 517447 = 776171) B776171
theorem B518247 : Blo 515797 518247 := bstep (se 1 (by rfl) ⟨388685, by rfl⟩ : syracuseStep 518247 = 777371) B777371
theorem B583807 : Blo 515797 583807 := bstep (se 1 (by rfl) ⟨437855, by rfl⟩ : syracuseStep 583807 = 875711) B875711
theorem B518559 : Blo 515797 518559 := bstep (se 1 (by rfl) ⟨388919, by rfl⟩ : syracuseStep 518559 = 777839) B777839
theorem B6318911 : Blo 515797 6318911 := bstep (se 1 (by rfl) ⟨4739183, by rfl⟩ : syracuseStep 6318911 = 9478367) B9478367
theorem B3926879 : Blo 515797 3926879 := bstep (se 1 (by rfl) ⟨2945159, by rfl⟩ : syracuseStep 3926879 = 5890319) B5890319
theorem B2944295 : Blo 515797 2944295 := bstep (se 1 (by rfl) ⟨2208221, by rfl⟩ : syracuseStep 2944295 = 4416443) B4416443
theorem B519679 : Blo 515797 519679 := bstep (se 1 (by rfl) ⟨389759, by rfl⟩ : syracuseStep 519679 = 779519) B779519
theorem B1568951 : Blo 515797 1568951 := bstep (se 1 (by rfl) ⟨1176713, by rfl⟩ : syracuseStep 1568951 = 2353427) B2353427
theorem B1471259 : Blo 515797 1471259 := bstep (se 1 (by rfl) ⟨1103444, by rfl⟩ : syracuseStep 1471259 = 2206889) B2206889
theorem B979951 : Blo 515797 979951 := bstep (se 1 (by rfl) ⟨734963, by rfl⟩ : syracuseStep 979951 = 1469927) B1469927
theorem B947387 : Blo 515797 947387 := bstep (se 1 (by rfl) ⟨710540, by rfl⟩ : syracuseStep 947387 = 1421081) B1421081
theorem B4420817 : Blo 515797 4420817 := bstep (se 2 (by rfl) ⟨1657806, by rfl⟩ : syracuseStep 4420817 = 3315613) B3315613
theorem B372176855 : Blo 515797 372176855 := bstep (se 1 (by rfl) ⟨279132641, by rfl⟩ : syracuseStep 372176855 = 558265283) B558265283
theorem B1472489 : Blo 515797 1472489 := bstep (se 2 (by rfl) ⟨552183, by rfl⟩ : syracuseStep 1472489 = 1104367) B1104367
theorem B2947711 : Blo 515797 2947711 := bstep (se 1 (by rfl) ⟨2210783, by rfl⟩ : syracuseStep 2947711 = 4421567) B4421567
theorem B4193633 : Blo 515797 4193633 := bstep (se 2 (by rfl) ⟨1572612, by rfl⟩ : syracuseStep 4193633 = 3145225) B3145225
theorem B1180775 : Blo 515797 1180775 := bstep (se 1 (by rfl) ⟨885581, by rfl⟩ : syracuseStep 1180775 = 1771163) B1771163
theorem B1968239 : Blo 515797 1968239 := bstep (se 1 (by rfl) ⟨1476179, by rfl⟩ : syracuseStep 1968239 = 2952359) B2952359
theorem B1476863 : Blo 515797 1476863 := bstep (se 1 (by rfl) ⟨1107647, by rfl⟩ : syracuseStep 1476863 = 2215295) B2215295
theorem B1182023 : Blo 515797 1182023 := bstep (se 1 (by rfl) ⟨886517, by rfl⟩ : syracuseStep 1182023 = 1773035) B1773035
theorem B1968893 : Blo 515797 1968893 := bstep (se 3 (by rfl) ⟨369167, by rfl⟩ : syracuseStep 1968893 = 738335) B738335
theorem B2362223 : Blo 515797 2362223 := bstep (se 1 (by rfl) ⟨1771667, by rfl⟩ : syracuseStep 2362223 = 3543335) B3543335
theorem B2526365 : Blo 515797 2526365 := bstep (se 3 (by rfl) ⟨473693, by rfl⟩ : syracuseStep 2526365 = 947387) B947387
theorem B1051807 : Blo 515797 1051807 := bstep (se 1 (by rfl) ⟨788855, by rfl⟩ : syracuseStep 1051807 = 1577711) B1577711
theorem B1052327 : Blo 515797 1052327 := bstep (se 1 (by rfl) ⟨789245, by rfl⟩ : syracuseStep 1052327 = 1578491) B1578491
theorem B4427855 : Blo 515797 4427855 := bstep (se 1 (by rfl) ⟨3320891, by rfl⟩ : syracuseStep 4427855 = 6641783) B6641783
theorem B1740959 : Blo 515797 1740959 := bstep (se 1 (by rfl) ⟨1305719, by rfl⟩ : syracuseStep 1740959 = 2611439) B2611439
theorem B1053607 : Blo 515797 1053607 := bstep (se 1 (by rfl) ⟨790205, by rfl⟩ : syracuseStep 1053607 = 1580411) B1580411
theorem B10622441 : Blo 515797 10622441 := bstep (se 2 (by rfl) ⟨3983415, by rfl⟩ : syracuseStep 10622441 = 7966831) B7966831
theorem B1742363 : Blo 515797 1742363 := bstep (se 1 (by rfl) ⟨1306772, by rfl⟩ : syracuseStep 1742363 = 2613545) B2613545
theorem B3938057 : Blo 515797 3938057 := bstep (se 2 (by rfl) ⟨1476771, by rfl⟩ : syracuseStep 3938057 = 2953543) B2953543
theorem B11183021 : Blo 515797 11183021 := bstep (se 3 (by rfl) ⟨2096816, by rfl⟩ : syracuseStep 11183021 = 4193633) B4193633
theorem B3320585 : Blo 515797 3320585 := bstep (se 2 (by rfl) ⟨1245219, by rfl⟩ : syracuseStep 3320585 = 2490439) B2490439
theorem B1748951 : Blo 515797 1748951 := bstep (se 1 (by rfl) ⟨1311713, by rfl⟩ : syracuseStep 1748951 = 2623427) B2623427
theorem B56603933 : Blo 515797 56603933 := bstep (se 3 (by rfl) ⟨10613237, by rfl⟩ : syracuseStep 56603933 = 21226475) B21226475
theorem B1750409 : Blo 515797 1750409 := bstep (se 2 (by rfl) ⟨656403, by rfl⟩ : syracuseStep 1750409 = 1312807) B1312807
theorem B1750895 : Blo 515797 1750895 := bstep (se 1 (by rfl) ⟨1313171, by rfl⟩ : syracuseStep 1750895 = 2626343) B2626343
theorem B1751759 : Blo 515797 1751759 := bstep (se 1 (by rfl) ⟨1313819, by rfl⟩ : syracuseStep 1751759 = 2627639) B2627639
theorem B19840463 : Blo 515797 19840463 := bstep (se 1 (by rfl) ⟨14880347, by rfl⟩ : syracuseStep 19840463 = 29760695) B29760695
theorem B1752731 : Blo 515797 1752731 := bstep (se 1 (by rfl) ⟨1314548, by rfl⟩ : syracuseStep 1752731 = 2629097) B2629097
theorem B24003215 : Blo 515797 24003215 := bstep (se 1 (by rfl) ⟨18002411, by rfl⟩ : syracuseStep 24003215 = 36004823) B36004823
theorem B1164059 : Blo 515797 1164059 := bstep (se 1 (by rfl) ⟨873044, by rfl⟩ : syracuseStep 1164059 = 1746089) B1746089
theorem B163431199 : Blo 515797 163431199 := bstep (se 1 (by rfl) ⟨122573399, by rfl⟩ : syracuseStep 163431199 = 245146799) B245146799
theorem B4212607 : Blo 515797 4212607 := bstep (se 1 (by rfl) ⟨3159455, by rfl⟩ : syracuseStep 4212607 = 6318911) B6318911
theorem B774863 : Blo 515797 774863 := bstep (se 1 (by rfl) ⟨581147, by rfl⟩ : syracuseStep 774863 = 1162295) B1162295
theorem B1398667 : Blo 515797 1398667 := bstep (se 1 (by rfl) ⟨1049000, by rfl⟩ : syracuseStep 1398667 = 2098001) B2098001
theorem B776303 : Blo 515797 776303 := bstep (se 1 (by rfl) ⟨582227, by rfl⟩ : syracuseStep 776303 = 1164455) B1164455
theorem B1169531 : Blo 515797 1169531 := bstep (se 1 (by rfl) ⟨877148, by rfl⟩ : syracuseStep 1169531 = 1754297) B1754297
theorem B1661087 : Blo 515797 1661087 := bstep (se 1 (by rfl) ⟨1245815, by rfl⟩ : syracuseStep 1661087 = 2491631) B2491631
theorem B776759 : Blo 515797 776759 := bstep (se 1 (by rfl) ⟨582569, by rfl⟩ : syracuseStep 776759 = 1165139) B1165139
theorem B15948683 : Blo 515797 15948683 := bstep (se 1 (by rfl) ⟨11961512, by rfl⟩ : syracuseStep 15948683 = 23923025) B23923025
theorem B777215 : Blo 515797 777215 := bstep (se 1 (by rfl) ⟨582911, by rfl⟩ : syracuseStep 777215 = 1165823) B1165823
theorem B108945395 : Blo 515797 108945395 := bstep (se 1 (by rfl) ⟨81709046, by rfl⟩ : syracuseStep 108945395 = 163418093) B163418093
theorem B3923963 : Blo 515797 3923963 := bstep (se 1 (by rfl) ⟨2942972, by rfl⟩ : syracuseStep 3923963 = 5885945) B5885945
theorem B778331 : Blo 515797 778331 := bstep (se 1 (by rfl) ⟨583748, by rfl⟩ : syracuseStep 778331 = 1167497) B1167497
theorem B778409 : Blo 515797 778409 := bstep (se 2 (by rfl) ⟨291903, by rfl⟩ : syracuseStep 778409 = 583807) B583807
theorem B516455 : Blo 515797 516455 := bstep (se 1 (by rfl) ⟨387341, by rfl⟩ : syracuseStep 516455 = 774683) B774683
theorem B778727 : Blo 515797 778727 := bstep (se 1 (by rfl) ⟨584045, by rfl⟩ : syracuseStep 778727 = 1168091) B1168091
theorem B516607 : Blo 515797 516607 := bstep (se 1 (by rfl) ⟨387455, by rfl⟩ : syracuseStep 516607 = 774911) B774911
theorem B3924935 : Blo 515797 3924935 := bstep (se 1 (by rfl) ⟨2943701, by rfl⟩ : syracuseStep 3924935 = 5887403) B5887403
theorem B779291 : Blo 515797 779291 := bstep (se 1 (by rfl) ⟨584468, by rfl⟩ : syracuseStep 779291 = 1168937) B1168937
theorem B517403 : Blo 515797 517403 := bstep (se 1 (by rfl) ⟨388052, by rfl⟩ : syracuseStep 517403 = 776105) B776105
theorem B583015 : Blo 515797 583015 := bstep (se 1 (by rfl) ⟨437261, by rfl⟩ : syracuseStep 583015 = 874523) B874523
theorem B518907 : Blo 515797 518907 := bstep (se 1 (by rfl) ⟨389180, by rfl⟩ : syracuseStep 518907 = 778361) B778361
theorem B519167 : Blo 515797 519167 := bstep (se 1 (by rfl) ⟨389375, by rfl⟩ : syracuseStep 519167 = 778751) B778751
theorem B519423 : Blo 515797 519423 := bstep (se 1 (by rfl) ⟨389567, by rfl⟩ : syracuseStep 519423 = 779135) B779135
theorem B2846249 : Blo 515797 2846249 := bstep (se 2 (by rfl) ⟨1067343, by rfl⟩ : syracuseStep 2846249 = 2134687) B2134687
theorem B1306601 : Blo 515797 1306601 := bstep (se 2 (by rfl) ⟨489975, by rfl⟩ : syracuseStep 1306601 = 979951) B979951
theorem B2617919 : Blo 515797 2617919 := bstep (se 1 (by rfl) ⟨1963439, by rfl⟩ : syracuseStep 2617919 = 3926879) B3926879
theorem B1962863 : Blo 515797 1962863 := bstep (se 1 (by rfl) ⟨1472147, by rfl⟩ : syracuseStep 1962863 = 2944295) B2944295
theorem B1045967 : Blo 515797 1045967 := bstep (se 1 (by rfl) ⟨784475, by rfl⟩ : syracuseStep 1045967 = 1568951) B1568951
theorem B620011 : Blo 515797 620011 := bstep (se 1 (by rfl) ⟨465008, by rfl⟩ : syracuseStep 620011 = 930017) B930017
theorem B980839 : Blo 515797 980839 := bstep (se 1 (by rfl) ⟨735629, by rfl⟩ : syracuseStep 980839 = 1471259) B1471259
theorem B42629003 : Blo 515797 42629003 := bstep (se 1 (by rfl) ⟨31971752, by rfl⟩ : syracuseStep 42629003 = 63943505) B63943505
theorem B2947211 : Blo 515797 2947211 := bstep (se 1 (by rfl) ⟨2210408, by rfl⟩ : syracuseStep 2947211 = 4420817) B4420817
theorem B3930281 : Blo 515797 3930281 := bstep (se 2 (by rfl) ⟨1473855, by rfl⟩ : syracuseStep 3930281 = 2947711) B2947711
theorem B248117903 : Blo 515797 248117903 := bstep (se 1 (by rfl) ⟨186088427, by rfl⟩ : syracuseStep 248117903 = 372176855) B372176855
theorem B981659 : Blo 515797 981659 := bstep (se 1 (by rfl) ⟨736244, by rfl⟩ : syracuseStep 981659 = 1472489) B1472489
theorem B982601 : Blo 515797 982601 := bstep (se 2 (by rfl) ⟨368475, by rfl⟩ : syracuseStep 982601 = 736951) B736951
theorem B1474175 : Blo 515797 1474175 := bstep (se 1 (by rfl) ⟨1105631, by rfl⟩ : syracuseStep 1474175 = 2211263) B2211263
theorem B217908265 : Blo 515797 217908265 := bstep (se 2 (by rfl) ⟨81715599, by rfl⟩ : syracuseStep 217908265 = 163431199) B163431199
theorem B1312159 : Blo 515797 1312159 := bstep (se 1 (by rfl) ⟨984119, by rfl⟩ : syracuseStep 1312159 = 1968239) B1968239
theorem B984575 : Blo 515797 984575 := bstep (se 1 (by rfl) ⟨738431, by rfl⟩ : syracuseStep 984575 = 1476863) B1476863
theorem B788015 : Blo 515797 788015 := bstep (se 1 (by rfl) ⟨591011, by rfl⟩ : syracuseStep 788015 = 1182023) B1182023
theorem B1312595 : Blo 515797 1312595 := bstep (se 1 (by rfl) ⟨984446, by rfl⟩ : syracuseStep 1312595 = 1968893) B1968893
theorem B1574815 : Blo 515797 1574815 := bstep (se 1 (by rfl) ⟨1181111, by rfl⟩ : syracuseStep 1574815 = 2362223) B2362223
theorem B2951903 : Blo 515797 2951903 := bstep (se 1 (by rfl) ⟨2213927, by rfl⟩ : syracuseStep 2951903 = 4427855) B4427855
theorem B3148733 : Blo 515797 3148733 := bstep (se 3 (by rfl) ⟨590387, by rfl⟩ : syracuseStep 3148733 = 1180775) B1180775
theorem B7081627 : Blo 515797 7081627 := bstep (se 1 (by rfl) ⟨5311220, by rfl⟩ : syracuseStep 7081627 = 10622441) B10622441
theorem B2625371 : Blo 515797 2625371 := bstep (se 1 (by rfl) ⟨1969028, by rfl⟩ : syracuseStep 2625371 = 3938057) B3938057
theorem B2789245 : Blo 515797 2789245 := bstep (se 3 (by rfl) ⟨522983, by rfl⟩ : syracuseStep 2789245 = 1045967) B1045967
theorem B4429565 : Blo 515797 4429565 := bstep (se 3 (by rfl) ⟨830543, by rfl⟩ : syracuseStep 4429565 = 1661087) B1661087
theorem B826681 : Blo 515797 826681 := bstep (se 2 (by rfl) ⟨310005, by rfl⟩ : syracuseStep 826681 = 620011) B620011
theorem B1745279 : Blo 515797 1745279 := bstep (se 1 (by rfl) ⟨1308959, by rfl⟩ : syracuseStep 1745279 = 2617919) B2617919
theorem B28419335 : Blo 515797 28419335 := bstep (se 1 (by rfl) ⟨21314501, by rfl⟩ : syracuseStep 28419335 = 42629003) B42629003
theorem B16002143 : Blo 515797 16002143 := bstep (se 1 (by rfl) ⟨12001607, by rfl⟩ : syracuseStep 16002143 = 24003215) B24003215
theorem B1684243 : Blo 515797 1684243 := bstep (se 1 (by rfl) ⟨1263182, by rfl⟩ : syracuseStep 1684243 = 2526365) B2526365
theorem B701551 : Blo 515797 701551 := bstep (se 1 (by rfl) ⟨526163, by rfl⟩ : syracuseStep 701551 = 1052327) B1052327
theorem B5616809 : Blo 515797 5616809 := bstep (se 2 (by rfl) ⟨2106303, by rfl⟩ : syracuseStep 5616809 = 4212607) B4212607
theorem B1160639 : Blo 515797 1160639 := bstep (se 1 (by rfl) ⟨870479, by rfl⟩ : syracuseStep 1160639 = 1740959) B1740959
theorem B1161575 : Blo 515797 1161575 := bstep (se 1 (by rfl) ⟨871181, by rfl⟩ : syracuseStep 1161575 = 1742363) B1742363
theorem B10632455 : Blo 515797 10632455 := bstep (se 1 (by rfl) ⟨7974341, by rfl⟩ : syracuseStep 10632455 = 15948683) B15948683
theorem B72630263 : Blo 515797 72630263 := bstep (se 1 (by rfl) ⟨54472697, by rfl⟩ : syracuseStep 72630263 = 108945395) B108945395
theorem B7455347 : Blo 515797 7455347 := bstep (se 1 (by rfl) ⟨5591510, by rfl⟩ : syracuseStep 7455347 = 11183021) B11183021
theorem B2213723 : Blo 515797 2213723 := bstep (se 1 (by rfl) ⟨1660292, by rfl⟩ : syracuseStep 2213723 = 3320585) B3320585
theorem B1165967 : Blo 515797 1165967 := bstep (se 1 (by rfl) ⟨874475, by rfl⟩ : syracuseStep 1165967 = 1748951) B1748951
theorem B871067 : Blo 515797 871067 := bstep (se 1 (by rfl) ⟨653300, by rfl⟩ : syracuseStep 871067 = 1306601) B1306601
theorem B37735955 : Blo 515797 37735955 := bstep (se 1 (by rfl) ⟨28301966, by rfl⟩ : syracuseStep 37735955 = 56603933) B56603933
theorem B1166939 : Blo 515797 1166939 := bstep (se 1 (by rfl) ⟨875204, by rfl⟩ : syracuseStep 1166939 = 1750409) B1750409
theorem B1167263 : Blo 515797 1167263 := bstep (se 1 (by rfl) ⟨875447, by rfl⟩ : syracuseStep 1167263 = 1750895) B1750895
theorem B1167839 : Blo 515797 1167839 := bstep (se 1 (by rfl) ⟨875879, by rfl⟩ : syracuseStep 1167839 = 1751759) B1751759
theorem B13226975 : Blo 515797 13226975 := bstep (se 1 (by rfl) ⟨9920231, by rfl⟩ : syracuseStep 13226975 = 19840463) B19840463
theorem B1168487 : Blo 515797 1168487 := bstep (se 1 (by rfl) ⟨876365, by rfl⟩ : syracuseStep 1168487 = 1752731) B1752731
theorem B776039 : Blo 515797 776039 := bstep (se 1 (by rfl) ⟨582029, by rfl⟩ : syracuseStep 776039 = 1164059) B1164059
theorem B777353 : Blo 515797 777353 := bstep (se 2 (by rfl) ⟨291507, by rfl⟩ : syracuseStep 777353 = 583015) B583015
theorem B516575 : Blo 515797 516575 := bstep (se 1 (by rfl) ⟨387431, by rfl⟩ : syracuseStep 516575 = 774863) B774863
theorem B517535 : Blo 515797 517535 := bstep (se 1 (by rfl) ⟨388151, by rfl⟩ : syracuseStep 517535 = 776303) B776303
theorem B779687 : Blo 515797 779687 := bstep (se 1 (by rfl) ⟨584765, by rfl⟩ : syracuseStep 779687 = 1169531) B1169531
theorem B1402409 : Blo 515797 1402409 := bstep (se 2 (by rfl) ⟨525903, by rfl⟩ : syracuseStep 1402409 = 1051807) B1051807
theorem B517839 : Blo 515797 517839 := bstep (se 1 (by rfl) ⟨388379, by rfl⟩ : syracuseStep 517839 = 776759) B776759
theorem B518143 : Blo 515797 518143 := bstep (se 1 (by rfl) ⟨388607, by rfl⟩ : syracuseStep 518143 = 777215) B777215
theorem B2615975 : Blo 515797 2615975 := bstep (se 1 (by rfl) ⟨1961981, by rfl⟩ : syracuseStep 2615975 = 3923963) B3923963
theorem B518887 : Blo 515797 518887 := bstep (se 1 (by rfl) ⟨389165, by rfl⟩ : syracuseStep 518887 = 778331) B778331
theorem B518939 : Blo 515797 518939 := bstep (se 1 (by rfl) ⟨389204, by rfl⟩ : syracuseStep 518939 = 778409) B778409
theorem B519151 : Blo 515797 519151 := bstep (se 1 (by rfl) ⟨389363, by rfl⟩ : syracuseStep 519151 = 778727) B778727
theorem B2616623 : Blo 515797 2616623 := bstep (se 1 (by rfl) ⟨1962467, by rfl⟩ : syracuseStep 2616623 = 3924935) B3924935
theorem B519527 : Blo 515797 519527 := bstep (se 1 (by rfl) ⟨389645, by rfl⟩ : syracuseStep 519527 = 779291) B779291
theorem B1404809 : Blo 515797 1404809 := bstep (se 2 (by rfl) ⟨526803, by rfl⟩ : syracuseStep 1404809 = 1053607) B1053607
theorem B2617757 : Blo 515797 2617757 := bstep (se 3 (by rfl) ⟨490829, by rfl⟩ : syracuseStep 2617757 = 981659) B981659
theorem B1897499 : Blo 515797 1897499 := bstep (se 1 (by rfl) ⟨1423124, by rfl⟩ : syracuseStep 1897499 = 2846249) B2846249
theorem B1307785 : Blo 515797 1307785 := bstep (se 2 (by rfl) ⟨490419, by rfl⟩ : syracuseStep 1307785 = 980839) B980839
theorem B1864889 : Blo 515797 1864889 := bstep (se 2 (by rfl) ⟨699333, by rfl⟩ : syracuseStep 1864889 = 1398667) B1398667
theorem B1308575 : Blo 515797 1308575 := bstep (se 1 (by rfl) ⟨981431, by rfl⟩ : syracuseStep 1308575 = 1962863) B1962863
theorem B1964807 : Blo 515797 1964807 := bstep (se 1 (by rfl) ⟨1473605, by rfl⟩ : syracuseStep 1964807 = 2947211) B2947211
theorem B2620187 : Blo 515797 2620187 := bstep (se 1 (by rfl) ⟨1965140, by rfl⟩ : syracuseStep 2620187 = 3930281) B3930281
theorem B165411935 : Blo 515797 165411935 := bstep (se 1 (by rfl) ⟨124058951, by rfl⟩ : syracuseStep 165411935 = 248117903) B248117903
theorem B655067 : Blo 515797 655067 := bstep (se 1 (by rfl) ⟨491300, by rfl⟩ : syracuseStep 655067 = 982601) B982601
theorem B982783 : Blo 515797 982783 := bstep (se 1 (by rfl) ⟨737087, by rfl⟩ : syracuseStep 982783 = 1474175) B1474175
theorem B1475815 : Blo 515797 1475815 := bstep (se 1 (by rfl) ⟨1106861, by rfl⟩ : syracuseStep 1475815 = 2213723) B2213723
theorem B1967935 : Blo 515797 1967935 := bstep (se 1 (by rfl) ⟨1475951, by rfl⟩ : syracuseStep 1967935 = 2951903) B2951903
theorem B2099155 : Blo 515797 2099155 := bstep (se 1 (by rfl) ⟨1574366, by rfl⟩ : syracuseStep 2099155 = 3148733) B3148733
theorem B2099753 : Blo 515797 2099753 := bstep (se 2 (by rfl) ⟨787407, by rfl⟩ : syracuseStep 2099753 = 1574815) B1574815
theorem B8817983 : Blo 515797 8817983 := bstep (se 1 (by rfl) ⟨6613487, by rfl⟩ : syracuseStep 8817983 = 13226975) B13226975
theorem B2953043 : Blo 515797 2953043 := bstep (se 1 (by rfl) ⟨2214782, by rfl⟩ : syracuseStep 2953043 = 4429565) B4429565
theorem B2625533 : Blo 515797 2625533 := bstep (se 3 (by rfl) ⟨492287, by rfl⟩ : syracuseStep 2625533 = 984575) B984575
theorem B8982629 : Blo 515797 8982629 := bstep (se 4 (by rfl) ⟨842121, by rfl⟩ : syracuseStep 8982629 = 1684243) B1684243
theorem B2101373 : Blo 515797 2101373 := bstep (se 3 (by rfl) ⟨394007, by rfl⟩ : syracuseStep 2101373 = 788015) B788015
theorem B9442169 : Blo 515797 9442169 := bstep (se 2 (by rfl) ⟨3540813, by rfl⟩ : syracuseStep 9442169 = 7081627) B7081627
theorem B18946223 : Blo 515797 18946223 := bstep (se 1 (by rfl) ⟨14209667, by rfl⟩ : syracuseStep 18946223 = 28419335) B28419335
theorem B1743713 : Blo 515797 1743713 := bstep (se 2 (by rfl) ⟨653892, by rfl⟩ : syracuseStep 1743713 = 1307785) B1307785
theorem B1743983 : Blo 515797 1743983 := bstep (se 1 (by rfl) ⟨1307987, by rfl⟩ : syracuseStep 1743983 = 2615975) B2615975
theorem B1744415 : Blo 515797 1744415 := bstep (se 1 (by rfl) ⟨1308311, by rfl⟩ : syracuseStep 1744415 = 2616623) B2616623
theorem B1745171 : Blo 515797 1745171 := bstep (se 1 (by rfl) ⟨1308878, by rfl⟩ : syracuseStep 1745171 = 2617757) B2617757
theorem B3744539 : Blo 515797 3744539 := bstep (se 1 (by rfl) ⟨2808404, by rfl⟩ : syracuseStep 3744539 = 5616809) B5616809
theorem B1746791 : Blo 515797 1746791 := bstep (se 1 (by rfl) ⟨1310093, by rfl⟩ : syracuseStep 1746791 = 2620187) B2620187
theorem B1746845 : Blo 515797 1746845 := bstep (se 3 (by rfl) ⟨327533, by rfl⟩ : syracuseStep 1746845 = 655067) B655067
theorem B110274623 : Blo 515797 110274623 := bstep (se 1 (by rfl) ⟨82705967, by rfl⟩ : syracuseStep 110274623 = 165411935) B165411935
theorem B7088303 : Blo 515797 7088303 := bstep (se 1 (by rfl) ⟨5316227, by rfl⟩ : syracuseStep 7088303 = 10632455) B10632455
theorem B1749545 : Blo 515797 1749545 := bstep (se 2 (by rfl) ⟨656079, by rfl⟩ : syracuseStep 1749545 = 1312159) B1312159
theorem B1750247 : Blo 515797 1750247 := bstep (se 1 (by rfl) ⟨1312685, by rfl⟩ : syracuseStep 1750247 = 2625371) B2625371
theorem B1163519 : Blo 515797 1163519 := bstep (se 1 (by rfl) ⟨872639, by rfl⟩ : syracuseStep 1163519 = 1745279) B1745279
theorem B934939 : Blo 515797 934939 := bstep (se 1 (by rfl) ⟨701204, by rfl⟩ : syracuseStep 934939 = 1402409) B1402409
theorem B935401 : Blo 515797 935401 := bstep (se 2 (by rfl) ⟨350775, by rfl⟩ : syracuseStep 935401 = 701551) B701551
theorem B10668095 : Blo 515797 10668095 := bstep (se 1 (by rfl) ⟨8001071, by rfl⟩ : syracuseStep 10668095 = 16002143) B16002143
theorem B936539 : Blo 515797 936539 := bstep (se 1 (by rfl) ⟨702404, by rfl⟩ : syracuseStep 936539 = 1404809) B1404809
theorem B1264999 : Blo 515797 1264999 := bstep (se 1 (by rfl) ⟨948749, by rfl⟩ : syracuseStep 1264999 = 1897499) B1897499
theorem B773759 : Blo 515797 773759 := bstep (se 1 (by rfl) ⟨580319, by rfl⟩ : syracuseStep 773759 = 1160639) B1160639
theorem B872383 : Blo 515797 872383 := bstep (se 1 (by rfl) ⟨654287, by rfl⟩ : syracuseStep 872383 = 1308575) B1308575
theorem B774383 : Blo 515797 774383 := bstep (se 1 (by rfl) ⟨580787, by rfl⟩ : syracuseStep 774383 = 1161575) B1161575
theorem B1102241 : Blo 515797 1102241 := bstep (se 2 (by rfl) ⟨413340, by rfl⟩ : syracuseStep 1102241 = 826681) B826681
theorem B48420175 : Blo 515797 48420175 := bstep (se 1 (by rfl) ⟨36315131, by rfl⟩ : syracuseStep 48420175 = 72630263) B72630263
theorem B4970231 : Blo 515797 4970231 := bstep (se 1 (by rfl) ⟨3727673, by rfl⟩ : syracuseStep 4970231 = 7455347) B7455347
theorem B875063 : Blo 515797 875063 := bstep (se 1 (by rfl) ⟨656297, by rfl⟩ : syracuseStep 875063 = 1312595) B1312595
theorem B290544353 : Blo 515797 290544353 := bstep (se 2 (by rfl) ⟨108954132, by rfl⟩ : syracuseStep 290544353 = 217908265) B217908265
theorem B777311 : Blo 515797 777311 := bstep (se 1 (by rfl) ⟨582983, by rfl⟩ : syracuseStep 777311 = 1165967) B1165967
theorem B580711 : Blo 515797 580711 := bstep (se 1 (by rfl) ⟨435533, by rfl⟩ : syracuseStep 580711 = 871067) B871067
theorem B25157303 : Blo 515797 25157303 := bstep (se 1 (by rfl) ⟨18867977, by rfl⟩ : syracuseStep 25157303 = 37735955) B37735955
theorem B777959 : Blo 515797 777959 := bstep (se 1 (by rfl) ⟨583469, by rfl⟩ : syracuseStep 777959 = 1166939) B1166939
theorem B778175 : Blo 515797 778175 := bstep (se 1 (by rfl) ⟨583631, by rfl⟩ : syracuseStep 778175 = 1167263) B1167263
theorem B778559 : Blo 515797 778559 := bstep (se 1 (by rfl) ⟨583919, by rfl⟩ : syracuseStep 778559 = 1167839) B1167839
theorem B778991 : Blo 515797 778991 := bstep (se 1 (by rfl) ⟨584243, by rfl⟩ : syracuseStep 778991 = 1168487) B1168487
theorem B517359 : Blo 515797 517359 := bstep (se 1 (by rfl) ⟨388019, by rfl⟩ : syracuseStep 517359 = 776039) B776039
theorem B518235 : Blo 515797 518235 := bstep (se 1 (by rfl) ⟨388676, by rfl⟩ : syracuseStep 518235 = 777353) B777353
theorem B519791 : Blo 515797 519791 := bstep (se 1 (by rfl) ⟨389843, by rfl⟩ : syracuseStep 519791 = 779687) B779687
theorem B1243259 : Blo 515797 1243259 := bstep (se 1 (by rfl) ⟨932444, by rfl⟩ : syracuseStep 1243259 = 1864889) B1864889
theorem B1309871 : Blo 515797 1309871 := bstep (se 1 (by rfl) ⟨982403, by rfl⟩ : syracuseStep 1309871 = 1964807) B1964807
theorem B14875973 : Blo 515797 14875973 := bstep (se 4 (by rfl) ⟨1394622, by rfl⟩ : syracuseStep 14875973 = 2789245) B2789245
theorem B1310377 : Blo 515797 1310377 := bstep (se 2 (by rfl) ⟨491391, by rfl⟩ : syracuseStep 1310377 = 982783) B982783
theorem B1246585 : Blo 515797 1246585 := bstep (se 2 (by rfl) ⟨467469, by rfl⟩ : syracuseStep 1246585 = 934939) B934939
theorem B7112063 : Blo 515797 7112063 := bstep (se 1 (by rfl) ⟨5334047, by rfl⟩ : syracuseStep 7112063 = 10668095) B10668095
theorem B1967753 : Blo 515797 1967753 := bstep (se 2 (by rfl) ⟨737907, by rfl⟩ : syracuseStep 1967753 = 1475815) B1475815
theorem B624359 : Blo 515797 624359 := bstep (se 1 (by rfl) ⟨468269, by rfl⟩ : syracuseStep 624359 = 936539) B936539
theorem B1247201 : Blo 515797 1247201 := bstep (se 2 (by rfl) ⟨467700, by rfl⟩ : syracuseStep 1247201 = 935401) B935401
theorem B2623913 : Blo 515797 2623913 := bstep (se 2 (by rfl) ⟨983967, by rfl⟩ : syracuseStep 2623913 = 1967935) B1967935
theorem B1968695 : Blo 515797 1968695 := bstep (se 1 (by rfl) ⟨1476521, by rfl⟩ : syracuseStep 1968695 = 2953043) B2953043
theorem B6294779 : Blo 515797 6294779 := bstep (se 1 (by rfl) ⟨4721084, by rfl⟩ : syracuseStep 6294779 = 9442169) B9442169
theorem B3313487 : Blo 515797 3313487 := bstep (se 1 (by rfl) ⟨2485115, by rfl⟩ : syracuseStep 3313487 = 4970231) B4970231
theorem B193696235 : Blo 515797 193696235 := bstep (se 1 (by rfl) ⟨145272176, by rfl⟩ : syracuseStep 193696235 = 290544353) B290544353
theorem B2496359 : Blo 515797 2496359 := bstep (se 1 (by rfl) ⟨1872269, by rfl⟩ : syracuseStep 2496359 = 3744539) B3744539
theorem B4725535 : Blo 515797 4725535 := bstep (se 1 (by rfl) ⟨3544151, by rfl⟩ : syracuseStep 4725535 = 7088303) B7088303
theorem B64560233 : Blo 515797 64560233 := bstep (se 2 (by rfl) ⟨24210087, by rfl⟩ : syracuseStep 64560233 = 48420175) B48420175
theorem B828839 : Blo 515797 828839 := bstep (se 1 (by rfl) ⟨621629, by rfl⟩ : syracuseStep 828839 = 1243259) B1243259
theorem B1747169 : Blo 515797 1747169 := bstep (se 2 (by rfl) ⟨655188, by rfl⟩ : syracuseStep 1747169 = 1310377) B1310377
theorem B5878655 : Blo 515797 5878655 := bstep (se 1 (by rfl) ⟨4408991, by rfl⟩ : syracuseStep 5878655 = 8817983) B8817983
theorem B2798873 : Blo 515797 2798873 := bstep (se 2 (by rfl) ⟨1049577, by rfl⟩ : syracuseStep 2798873 = 2099155) B2099155
theorem B1750355 : Blo 515797 1750355 := bstep (se 1 (by rfl) ⟨1312766, by rfl⟩ : syracuseStep 1750355 = 2625533) B2625533
theorem B734827 : Blo 515797 734827 := bstep (se 1 (by rfl) ⟨551120, by rfl⟩ : syracuseStep 734827 = 1102241) B1102241
theorem B12630815 : Blo 515797 12630815 := bstep (se 1 (by rfl) ⟨9473111, by rfl⟩ : syracuseStep 12630815 = 18946223) B18946223
theorem B1686665 : Blo 515797 1686665 := bstep (se 2 (by rfl) ⟨632499, by rfl⟩ : syracuseStep 1686665 = 1264999) B1264999
theorem B1162475 : Blo 515797 1162475 := bstep (se 1 (by rfl) ⟨871856, by rfl⟩ : syracuseStep 1162475 = 1743713) B1743713
theorem B1162655 : Blo 515797 1162655 := bstep (se 1 (by rfl) ⟨871991, by rfl⟩ : syracuseStep 1162655 = 1743983) B1743983
theorem B1162943 : Blo 515797 1162943 := bstep (se 1 (by rfl) ⟨872207, by rfl⟩ : syracuseStep 1162943 = 1744415) B1744415
theorem B1163177 : Blo 515797 1163177 := bstep (se 2 (by rfl) ⟨436191, by rfl⟩ : syracuseStep 1163177 = 872383) B872383
theorem B1163447 : Blo 515797 1163447 := bstep (se 1 (by rfl) ⟨872585, by rfl⟩ : syracuseStep 1163447 = 1745171) B1745171
theorem B1164527 : Blo 515797 1164527 := bstep (se 1 (by rfl) ⟨873395, by rfl⟩ : syracuseStep 1164527 = 1746791) B1746791
theorem B1164563 : Blo 515797 1164563 := bstep (se 1 (by rfl) ⟨873422, by rfl⟩ : syracuseStep 1164563 = 1746845) B1746845
theorem B73516415 : Blo 515797 73516415 := bstep (se 1 (by rfl) ⟨55137311, by rfl⟩ : syracuseStep 73516415 = 110274623) B110274623
theorem B1166363 : Blo 515797 1166363 := bstep (se 1 (by rfl) ⟨874772, by rfl⟩ : syracuseStep 1166363 = 1749545) B1749545
theorem B1166831 : Blo 515797 1166831 := bstep (se 1 (by rfl) ⟨875123, by rfl⟩ : syracuseStep 1166831 = 1750247) B1750247
theorem B774281 : Blo 515797 774281 := bstep (se 2 (by rfl) ⟨290355, by rfl⟩ : syracuseStep 774281 = 580711) B580711
theorem B873247 : Blo 515797 873247 := bstep (se 1 (by rfl) ⟨654935, by rfl⟩ : syracuseStep 873247 = 1309871) B1309871
theorem B9917315 : Blo 515797 9917315 := bstep (se 1 (by rfl) ⟨7437986, by rfl⟩ : syracuseStep 9917315 = 14875973) B14875973
theorem B775679 : Blo 515797 775679 := bstep (se 1 (by rfl) ⟨581759, by rfl⟩ : syracuseStep 775679 = 1163519) B1163519
theorem B1399835 : Blo 515797 1399835 := bstep (se 1 (by rfl) ⟨1049876, by rfl⟩ : syracuseStep 1399835 = 2099753) B2099753
theorem B515839 : Blo 515797 515839 := bstep (se 1 (by rfl) ⟨386879, by rfl⟩ : syracuseStep 515839 = 773759) B773759
theorem B5988419 : Blo 515797 5988419 := bstep (se 1 (by rfl) ⟨4491314, by rfl⟩ : syracuseStep 5988419 = 8982629) B8982629
theorem B1400915 : Blo 515797 1400915 := bstep (se 1 (by rfl) ⟨1050686, by rfl⟩ : syracuseStep 1400915 = 2101373) B2101373
theorem B516255 : Blo 515797 516255 := bstep (se 1 (by rfl) ⟨387191, by rfl⟩ : syracuseStep 516255 = 774383) B774383
theorem B583375 : Blo 515797 583375 := bstep (se 1 (by rfl) ⟨437531, by rfl⟩ : syracuseStep 583375 = 875063) B875063
theorem B518207 : Blo 515797 518207 := bstep (se 1 (by rfl) ⟨388655, by rfl⟩ : syracuseStep 518207 = 777311) B777311
theorem B16771535 : Blo 515797 16771535 := bstep (se 1 (by rfl) ⟨12578651, by rfl⟩ : syracuseStep 16771535 = 25157303) B25157303
theorem B518639 : Blo 515797 518639 := bstep (se 1 (by rfl) ⟨388979, by rfl⟩ : syracuseStep 518639 = 777959) B777959
theorem B518783 : Blo 515797 518783 := bstep (se 1 (by rfl) ⟨389087, by rfl⟩ : syracuseStep 518783 = 778175) B778175
theorem B519039 : Blo 515797 519039 := bstep (se 1 (by rfl) ⟨389279, by rfl⟩ : syracuseStep 519039 = 778559) B778559
theorem B519327 : Blo 515797 519327 := bstep (se 1 (by rfl) ⟨389495, by rfl⟩ : syracuseStep 519327 = 778991) B778991
theorem B3735773 : Blo 515797 3735773 := bstep (se 3 (by rfl) ⟨700457, by rfl⟩ : syracuseStep 3735773 = 1400915) B1400915
theorem B1311835 : Blo 515797 1311835 := bstep (se 1 (by rfl) ⟨983876, by rfl⟩ : syracuseStep 1311835 = 1967753) B1967753
theorem B1312463 : Blo 515797 1312463 := bstep (se 1 (by rfl) ⟨984347, by rfl⟩ : syracuseStep 1312463 = 1968695) B1968695
theorem B4196519 : Blo 515797 4196519 := bstep (se 1 (by rfl) ⟨3147389, by rfl⟩ : syracuseStep 4196519 = 6294779) B6294779
theorem B11181023 : Blo 515797 11181023 := bstep (se 1 (by rfl) ⟨8385767, by rfl⟩ : syracuseStep 11181023 = 16771535) B16771535
theorem B6300713 : Blo 515797 6300713 := bstep (se 2 (by rfl) ⟨2362767, by rfl⟩ : syracuseStep 6300713 = 4725535) B4725535
theorem B1124443 : Blo 515797 1124443 := bstep (se 1 (by rfl) ⟨843332, by rfl⟩ : syracuseStep 1124443 = 1686665) B1686665
theorem B831467 : Blo 515797 831467 := bstep (se 1 (by rfl) ⟨623600, by rfl⟩ : syracuseStep 831467 = 1247201) B1247201
theorem B1749275 : Blo 515797 1749275 := bstep (se 1 (by rfl) ⟨1311956, by rfl⟩ : syracuseStep 1749275 = 2623913) B2623913
theorem B2208991 : Blo 515797 2208991 := bstep (se 1 (by rfl) ⟨1656743, by rfl⟩ : syracuseStep 2208991 = 3313487) B3313487
theorem B2210237 : Blo 515797 2210237 := bstep (se 3 (by rfl) ⟨414419, by rfl⟩ : syracuseStep 2210237 = 828839) B828839
theorem B933223 : Blo 515797 933223 := bstep (se 1 (by rfl) ⟨699917, by rfl⟩ : syracuseStep 933223 = 1399835) B1399835
theorem B43040155 : Blo 515797 43040155 := bstep (se 1 (by rfl) ⟨32280116, by rfl⟩ : syracuseStep 43040155 = 64560233) B64560233
theorem B1164329 : Blo 515797 1164329 := bstep (se 2 (by rfl) ⟨436623, by rfl⟩ : syracuseStep 1164329 = 873247) B873247
theorem B1164779 : Blo 515797 1164779 := bstep (se 1 (by rfl) ⟨873584, by rfl⟩ : syracuseStep 1164779 = 1747169) B1747169
theorem B3919103 : Blo 515797 3919103 := bstep (se 1 (by rfl) ⟨2939327, by rfl⟩ : syracuseStep 3919103 = 5878655) B5878655
theorem B1166903 : Blo 515797 1166903 := bstep (se 1 (by rfl) ⟨875177, by rfl⟩ : syracuseStep 1166903 = 1750355) B1750355
theorem B774983 : Blo 515797 774983 := bstep (se 1 (by rfl) ⟨581237, by rfl⟩ : syracuseStep 774983 = 1162475) B1162475
theorem B775103 : Blo 515797 775103 := bstep (se 1 (by rfl) ⟨581327, by rfl⟩ : syracuseStep 775103 = 1162655) B1162655
theorem B775295 : Blo 515797 775295 := bstep (se 1 (by rfl) ⟨581471, by rfl⟩ : syracuseStep 775295 = 1162943) B1162943
theorem B775451 : Blo 515797 775451 := bstep (se 1 (by rfl) ⟨581588, by rfl⟩ : syracuseStep 775451 = 1163177) B1163177
theorem B775631 : Blo 515797 775631 := bstep (se 1 (by rfl) ⟨581723, by rfl⟩ : syracuseStep 775631 = 1163447) B1163447
theorem B776351 : Blo 515797 776351 := bstep (se 1 (by rfl) ⟨582263, by rfl⟩ : syracuseStep 776351 = 1164527) B1164527
theorem B776375 : Blo 515797 776375 := bstep (se 1 (by rfl) ⟨582281, by rfl⟩ : syracuseStep 776375 = 1164563) B1164563
theorem B4741375 : Blo 515797 4741375 := bstep (se 1 (by rfl) ⟨3556031, by rfl⟩ : syracuseStep 4741375 = 7112063) B7112063
theorem B1662113 : Blo 515797 1662113 := bstep (se 2 (by rfl) ⟨623292, by rfl⟩ : syracuseStep 1662113 = 1246585) B1246585
theorem B777575 : Blo 515797 777575 := bstep (se 1 (by rfl) ⟨583181, by rfl⟩ : syracuseStep 777575 = 1166363) B1166363
theorem B777833 : Blo 515797 777833 := bstep (se 2 (by rfl) ⟨291687, by rfl⟩ : syracuseStep 777833 = 583375) B583375
theorem B777887 : Blo 515797 777887 := bstep (se 1 (by rfl) ⟨583415, by rfl⟩ : syracuseStep 777887 = 1166831) B1166831
theorem B516187 : Blo 515797 516187 := bstep (se 1 (by rfl) ⟨387140, by rfl⟩ : syracuseStep 516187 = 774281) B774281
theorem B129130823 : Blo 515797 129130823 := bstep (se 1 (by rfl) ⟨96848117, by rfl⟩ : syracuseStep 129130823 = 193696235) B193696235
theorem B6611543 : Blo 515797 6611543 := bstep (se 1 (by rfl) ⟨4958657, by rfl⟩ : syracuseStep 6611543 = 9917315) B9917315
theorem B196043773 : Blo 515797 196043773 := bstep (se 3 (by rfl) ⟨36758207, by rfl⟩ : syracuseStep 196043773 = 73516415) B73516415
theorem B517119 : Blo 515797 517119 := bstep (se 1 (by rfl) ⟨387839, by rfl⟩ : syracuseStep 517119 = 775679) B775679
theorem B1664239 : Blo 515797 1664239 := bstep (se 1 (by rfl) ⟨1248179, by rfl⟩ : syracuseStep 1664239 = 2496359) B2496359
theorem B1664957 : Blo 515797 1664957 := bstep (se 3 (by rfl) ⟨312179, by rfl⟩ : syracuseStep 1664957 = 624359) B624359
theorem B3992279 : Blo 515797 3992279 := bstep (se 1 (by rfl) ⟨2994209, by rfl⟩ : syracuseStep 3992279 = 5988419) B5988419
theorem B979769 : Blo 515797 979769 := bstep (se 2 (by rfl) ⟨367413, by rfl⟩ : syracuseStep 979769 = 734827) B734827
theorem B1865915 : Blo 515797 1865915 := bstep (se 1 (by rfl) ⟨1399436, by rfl⟩ : syracuseStep 1865915 = 2798873) B2798873
theorem B8420543 : Blo 515797 8420543 := bstep (se 1 (by rfl) ⟨6315407, by rfl⟩ : syracuseStep 8420543 = 12630815) B12630815
theorem B2490515 : Blo 515797 2490515 := bstep (se 1 (by rfl) ⟨1867886, by rfl⟩ : syracuseStep 2490515 = 3735773) B3735773
theorem B261391697 : Blo 515797 261391697 := bstep (se 2 (by rfl) ⟨98021886, by rfl⟩ : syracuseStep 261391697 = 196043773) B196043773
theorem B86087215 : Blo 515797 86087215 := bstep (se 1 (by rfl) ⟨64565411, by rfl⟩ : syracuseStep 86087215 = 129130823) B129130823
theorem B57386873 : Blo 515797 57386873 := bstep (se 2 (by rfl) ⟨21520077, by rfl⟩ : syracuseStep 57386873 = 43040155) B43040155
theorem B5613695 : Blo 515797 5613695 := bstep (se 1 (by rfl) ⟨4210271, by rfl⟩ : syracuseStep 5613695 = 8420543) B8420543
theorem B2797679 : Blo 515797 2797679 := bstep (se 1 (by rfl) ⟨2098259, by rfl⟩ : syracuseStep 2797679 = 4196519) B4196519
theorem B1749113 : Blo 515797 1749113 := bstep (se 2 (by rfl) ⟨655917, by rfl⟩ : syracuseStep 1749113 = 1311835) B1311835
theorem B7454015 : Blo 515797 7454015 := bstep (se 1 (by rfl) ⟨5590511, by rfl⟩ : syracuseStep 7454015 = 11181023) B11181023
theorem B4407695 : Blo 515797 4407695 := bstep (se 1 (by rfl) ⟨3305771, by rfl⟩ : syracuseStep 4407695 = 6611543) B6611543
theorem B1166183 : Blo 515797 1166183 := bstep (se 1 (by rfl) ⟨874637, by rfl⟩ : syracuseStep 1166183 = 1749275) B1749275
theorem B776219 : Blo 515797 776219 := bstep (se 1 (by rfl) ⟨582164, by rfl⟩ : syracuseStep 776219 = 1164329) B1164329
theorem B776519 : Blo 515797 776519 := bstep (se 1 (by rfl) ⟨582389, by rfl⟩ : syracuseStep 776519 = 1164779) B1164779
theorem B874975 : Blo 515797 874975 := bstep (se 1 (by rfl) ⟨656231, by rfl⟩ : syracuseStep 874975 = 1312463) B1312463
theorem B2218985 : Blo 515797 2218985 := bstep (se 2 (by rfl) ⟨832119, by rfl⟩ : syracuseStep 2218985 = 1664239) B1664239
theorem B2612735 : Blo 515797 2612735 := bstep (se 1 (by rfl) ⟨1959551, by rfl⟩ : syracuseStep 2612735 = 3919103) B3919103
theorem B777935 : Blo 515797 777935 := bstep (se 1 (by rfl) ⟨583451, by rfl⟩ : syracuseStep 777935 = 1166903) B1166903
theorem B16801901 : Blo 515797 16801901 := bstep (se 3 (by rfl) ⟨3150356, by rfl⟩ : syracuseStep 16801901 = 6300713) B6300713
theorem B1499257 : Blo 515797 1499257 := bstep (se 2 (by rfl) ⟨562221, by rfl⟩ : syracuseStep 1499257 = 1124443) B1124443
theorem B516655 : Blo 515797 516655 := bstep (se 1 (by rfl) ⟨387491, by rfl⟩ : syracuseStep 516655 = 774983) B774983
theorem B516735 : Blo 515797 516735 := bstep (se 1 (by rfl) ⟨387551, by rfl⟩ : syracuseStep 516735 = 775103) B775103
theorem B516863 : Blo 515797 516863 := bstep (se 1 (by rfl) ⟨387647, by rfl⟩ : syracuseStep 516863 = 775295) B775295
theorem B516967 : Blo 515797 516967 := bstep (se 1 (by rfl) ⟨387725, by rfl⟩ : syracuseStep 516967 = 775451) B775451
theorem B517087 : Blo 515797 517087 := bstep (se 1 (by rfl) ⟨387815, by rfl⟩ : syracuseStep 517087 = 775631) B775631
theorem B517567 : Blo 515797 517567 := bstep (se 1 (by rfl) ⟨388175, by rfl⟩ : syracuseStep 517567 = 776351) B776351
theorem B517583 : Blo 515797 517583 := bstep (se 1 (by rfl) ⟨388187, by rfl⟩ : syracuseStep 517583 = 776375) B776375
theorem B1108075 : Blo 515797 1108075 := bstep (se 1 (by rfl) ⟨831056, by rfl⟩ : syracuseStep 1108075 = 1662113) B1662113
theorem B518383 : Blo 515797 518383 := bstep (se 1 (by rfl) ⟨388787, by rfl⟩ : syracuseStep 518383 = 777575) B777575
theorem B518555 : Blo 515797 518555 := bstep (se 1 (by rfl) ⟨388916, by rfl⟩ : syracuseStep 518555 = 777833) B777833
theorem B518591 : Blo 515797 518591 := bstep (se 1 (by rfl) ⟨388943, by rfl⟩ : syracuseStep 518591 = 777887) B777887
theorem B1109971 : Blo 515797 1109971 := bstep (se 1 (by rfl) ⟨832478, by rfl⟩ : syracuseStep 1109971 = 1664957) B1664957
theorem B2945321 : Blo 515797 2945321 := bstep (se 2 (by rfl) ⟨1104495, by rfl⟩ : syracuseStep 2945321 = 2208991) B2208991
theorem B10646077 : Blo 515797 10646077 := bstep (se 3 (by rfl) ⟨1996139, by rfl⟩ : syracuseStep 10646077 = 3992279) B3992279
theorem B554311 : Blo 515797 554311 := bstep (se 1 (by rfl) ⟨415733, by rfl⟩ : syracuseStep 554311 = 831467) B831467
theorem B6321833 : Blo 515797 6321833 := bstep (se 2 (by rfl) ⟨2370687, by rfl⟩ : syracuseStep 6321833 = 4741375) B4741375
theorem B653179 : Blo 515797 653179 := bstep (se 1 (by rfl) ⟨489884, by rfl⟩ : syracuseStep 653179 = 979769) B979769
theorem B1243943 : Blo 515797 1243943 := bstep (se 1 (by rfl) ⟨932957, by rfl⟩ : syracuseStep 1243943 = 1865915) B1865915
theorem B1473491 : Blo 515797 1473491 := bstep (se 1 (by rfl) ⟨1105118, by rfl⟩ : syracuseStep 1473491 = 2210237) B2210237
theorem B1244297 : Blo 515797 1244297 := bstep (se 2 (by rfl) ⟨466611, by rfl⟩ : syracuseStep 1244297 = 933223) B933223
theorem B1999009 : Blo 515797 1999009 := bstep (se 2 (by rfl) ⟨749628, by rfl⟩ : syracuseStep 1999009 = 1499257) B1499257
theorem B174261131 : Blo 515797 174261131 := bstep (se 1 (by rfl) ⟨130695848, by rfl⟩ : syracuseStep 174261131 = 261391697) B261391697
theorem B1477433 : Blo 515797 1477433 := bstep (se 2 (by rfl) ⟨554037, by rfl⟩ : syracuseStep 1477433 = 1108075) B1108075
theorem B1479323 : Blo 515797 1479323 := bstep (se 1 (by rfl) ⟨1109492, by rfl⟩ : syracuseStep 1479323 = 2218985) B2218985
theorem B1741823 : Blo 515797 1741823 := bstep (se 1 (by rfl) ⟨1306367, by rfl⟩ : syracuseStep 1741823 = 2612735) B2612735
theorem B1479961 : Blo 515797 1479961 := bstep (se 2 (by rfl) ⟨554985, by rfl⟩ : syracuseStep 1479961 = 1109971) B1109971
theorem B14194769 : Blo 515797 14194769 := bstep (se 2 (by rfl) ⟨5323038, by rfl⟩ : syracuseStep 14194769 = 10646077) B10646077
theorem B3742463 : Blo 515797 3742463 := bstep (se 1 (by rfl) ⟨2806847, by rfl⟩ : syracuseStep 3742463 = 5613695) B5613695
theorem B829295 : Blo 515797 829295 := bstep (se 1 (by rfl) ⟨621971, by rfl⟩ : syracuseStep 829295 = 1243943) B1243943
theorem B829531 : Blo 515797 829531 := bstep (se 1 (by rfl) ⟨622148, by rfl⟩ : syracuseStep 829531 = 1244297) B1244297
theorem B38257915 : Blo 515797 38257915 := bstep (se 1 (by rfl) ⟨28693436, by rfl⟩ : syracuseStep 38257915 = 57386873) B57386873
theorem B739081 : Blo 515797 739081 := bstep (se 2 (by rfl) ⟨277155, by rfl⟩ : syracuseStep 739081 = 554311) B554311
theorem B870905 : Blo 515797 870905 := bstep (se 2 (by rfl) ⟨326589, by rfl⟩ : syracuseStep 870905 = 653179) B653179
theorem B1166075 : Blo 515797 1166075 := bstep (se 1 (by rfl) ⟨874556, by rfl⟩ : syracuseStep 1166075 = 1749113) B1749113
theorem B1166633 : Blo 515797 1166633 := bstep (se 2 (by rfl) ⟨437487, by rfl⟩ : syracuseStep 1166633 = 874975) B874975
theorem B4214555 : Blo 515797 4214555 := bstep (se 1 (by rfl) ⟨3160916, by rfl⟩ : syracuseStep 4214555 = 6321833) B6321833
theorem B4969343 : Blo 515797 4969343 := bstep (se 1 (by rfl) ⟨3727007, by rfl⟩ : syracuseStep 4969343 = 7454015) B7454015
theorem B1660343 : Blo 515797 1660343 := bstep (se 1 (by rfl) ⟨1245257, by rfl⟩ : syracuseStep 1660343 = 2490515) B2490515
theorem B2938463 : Blo 515797 2938463 := bstep (se 1 (by rfl) ⟨2203847, by rfl⟩ : syracuseStep 2938463 = 4407695) B4407695
theorem B777455 : Blo 515797 777455 := bstep (se 1 (by rfl) ⟨583091, by rfl⟩ : syracuseStep 777455 = 1166183) B1166183
theorem B517479 : Blo 515797 517479 := bstep (se 1 (by rfl) ⟨388109, by rfl⟩ : syracuseStep 517479 = 776219) B776219
theorem B517679 : Blo 515797 517679 := bstep (se 1 (by rfl) ⟨388259, by rfl⟩ : syracuseStep 517679 = 776519) B776519
theorem B518623 : Blo 515797 518623 := bstep (se 1 (by rfl) ⟨388967, by rfl⟩ : syracuseStep 518623 = 777935) B777935
theorem B11201267 : Blo 515797 11201267 := bstep (se 1 (by rfl) ⟨8400950, by rfl⟩ : syracuseStep 11201267 = 16801901) B16801901
theorem B114782953 : Blo 515797 114782953 := bstep (se 2 (by rfl) ⟨43043607, by rfl⟩ : syracuseStep 114782953 = 86087215) B86087215
theorem B3929309 : Blo 515797 3929309 := bstep (se 3 (by rfl) ⟨736745, by rfl⟩ : syracuseStep 3929309 = 1473491) B1473491
theorem B1865119 : Blo 515797 1865119 := bstep (se 1 (by rfl) ⟨1398839, by rfl⟩ : syracuseStep 1865119 = 2797679) B2797679
theorem B1963547 : Blo 515797 1963547 := bstep (se 1 (by rfl) ⟨1472660, by rfl⟩ : syracuseStep 1963547 = 2945321) B2945321
theorem B4424165 : Blo 515797 4424165 := bstep (se 4 (by rfl) ⟨414765, by rfl⟩ : syracuseStep 4424165 = 829531) B829531
theorem B984955 : Blo 515797 984955 := bstep (se 1 (by rfl) ⟨738716, by rfl⟩ : syracuseStep 984955 = 1477433) B1477433
theorem B985441 : Blo 515797 985441 := bstep (se 2 (by rfl) ⟨369540, by rfl⟩ : syracuseStep 985441 = 739081) B739081
theorem B3312895 : Blo 515797 3312895 := bstep (se 1 (by rfl) ⟨2484671, by rfl⟩ : syracuseStep 3312895 = 4969343) B4969343
theorem B4427581 : Blo 515797 4427581 := bstep (se 3 (by rfl) ⟨830171, by rfl⟩ : syracuseStep 4427581 = 1660343) B1660343
theorem B2494975 : Blo 515797 2494975 := bstep (se 1 (by rfl) ⟨1871231, by rfl⟩ : syracuseStep 2494975 = 3742463) B3742463
theorem B37852717 : Blo 515797 37852717 := bstep (se 3 (by rfl) ⟨7097384, by rfl⟩ : syracuseStep 37852717 = 14194769) B14194769
theorem B1973281 : Blo 515797 1973281 := bstep (se 2 (by rfl) ⟨739980, by rfl⟩ : syracuseStep 1973281 = 1479961) B1479961
theorem B2665345 : Blo 515797 2665345 := bstep (se 2 (by rfl) ⟨999504, by rfl⟩ : syracuseStep 2665345 = 1999009) B1999009
theorem B116174087 : Blo 515797 116174087 := bstep (se 1 (by rfl) ⟨87130565, by rfl⟩ : syracuseStep 116174087 = 174261131) B174261131
theorem B3944861 : Blo 515797 3944861 := bstep (se 3 (by rfl) ⟨739661, by rfl⟩ : syracuseStep 3944861 = 1479323) B1479323
theorem B1161215 : Blo 515797 1161215 := bstep (se 1 (by rfl) ⟨870911, by rfl⟩ : syracuseStep 1161215 = 1741823) B1741823
theorem B153043937 : Blo 515797 153043937 := bstep (se 2 (by rfl) ⟨57391476, by rfl⟩ : syracuseStep 153043937 = 114782953) B114782953
theorem B51010553 : Blo 515797 51010553 := bstep (se 2 (by rfl) ⟨19128957, by rfl⟩ : syracuseStep 51010553 = 38257915) B38257915
theorem B580603 : Blo 515797 580603 := bstep (se 1 (by rfl) ⟨435452, by rfl⟩ : syracuseStep 580603 = 870905) B870905
theorem B777383 : Blo 515797 777383 := bstep (se 1 (by rfl) ⟨583037, by rfl⟩ : syracuseStep 777383 = 1166075) B1166075
theorem B777755 : Blo 515797 777755 := bstep (se 1 (by rfl) ⟨583316, by rfl⟩ : syracuseStep 777755 = 1166633) B1166633
theorem B2809703 : Blo 515797 2809703 := bstep (se 1 (by rfl) ⟨2107277, by rfl⟩ : syracuseStep 2809703 = 4214555) B4214555
theorem B1958975 : Blo 515797 1958975 := bstep (se 1 (by rfl) ⟨1469231, by rfl⟩ : syracuseStep 1958975 = 2938463) B2938463
theorem B518303 : Blo 515797 518303 := bstep (se 1 (by rfl) ⟨388727, by rfl⟩ : syracuseStep 518303 = 777455) B777455
theorem B552863 : Blo 515797 552863 := bstep (se 1 (by rfl) ⟨414647, by rfl⟩ : syracuseStep 552863 = 829295) B829295
theorem B7467511 : Blo 515797 7467511 := bstep (se 1 (by rfl) ⟨5600633, by rfl⟩ : syracuseStep 7467511 = 11201267) B11201267
theorem B2486825 : Blo 515797 2486825 := bstep (se 2 (by rfl) ⟨932559, by rfl⟩ : syracuseStep 2486825 = 1865119) B1865119
theorem B2619539 : Blo 515797 2619539 := bstep (se 1 (by rfl) ⟨1964654, by rfl⟩ : syracuseStep 2619539 = 3929309) B3929309
theorem B1309031 : Blo 515797 1309031 := bstep (se 1 (by rfl) ⟨981773, by rfl⟩ : syracuseStep 1309031 = 1963547) B1963547
theorem B2949443 : Blo 515797 2949443 := bstep (se 1 (by rfl) ⟨2212082, by rfl⟩ : syracuseStep 2949443 = 4424165) B4424165
theorem B1313273 : Blo 515797 1313273 := bstep (se 2 (by rfl) ⟨492477, by rfl⟩ : syracuseStep 1313273 = 984955) B984955
theorem B1313921 : Blo 515797 1313921 := bstep (se 2 (by rfl) ⟨492720, by rfl⟩ : syracuseStep 1313921 = 985441) B985441
theorem B5903441 : Blo 515797 5903441 := bstep (se 2 (by rfl) ⟨2213790, by rfl⟩ : syracuseStep 5903441 = 4427581) B4427581
theorem B1873135 : Blo 515797 1873135 := bstep (se 1 (by rfl) ⟨1404851, by rfl⟩ : syracuseStep 1873135 = 2809703) B2809703
theorem B50470289 : Blo 515797 50470289 := bstep (se 2 (by rfl) ⟨18926358, by rfl⟩ : syracuseStep 50470289 = 37852717) B37852717
theorem B2629907 : Blo 515797 2629907 := bstep (se 1 (by rfl) ⟨1972430, by rfl⟩ : syracuseStep 2629907 = 3944861) B3944861
theorem B2631041 : Blo 515797 2631041 := bstep (se 2 (by rfl) ⟨986640, by rfl⟩ : syracuseStep 2631041 = 1973281) B1973281
theorem B1746359 : Blo 515797 1746359 := bstep (se 1 (by rfl) ⟨1309769, by rfl⟩ : syracuseStep 1746359 = 2619539) B2619539
theorem B3553793 : Blo 515797 3553793 := bstep (se 2 (by rfl) ⟨1332672, by rfl⟩ : syracuseStep 3553793 = 2665345) B2665345
theorem B3326633 : Blo 515797 3326633 := bstep (se 2 (by rfl) ⟨1247487, by rfl⟩ : syracuseStep 3326633 = 2494975) B2494975
theorem B77449391 : Blo 515797 77449391 := bstep (se 1 (by rfl) ⟨58087043, by rfl⟩ : syracuseStep 77449391 = 116174087) B116174087
theorem B1657883 : Blo 515797 1657883 := bstep (se 1 (by rfl) ⟨1243412, by rfl⟩ : syracuseStep 1657883 = 2486825) B2486825
theorem B774137 : Blo 515797 774137 := bstep (se 2 (by rfl) ⟨290301, by rfl⟩ : syracuseStep 774137 = 580603) B580603
theorem B774143 : Blo 515797 774143 := bstep (se 1 (by rfl) ⟨580607, by rfl⟩ : syracuseStep 774143 = 1161215) B1161215
theorem B872687 : Blo 515797 872687 := bstep (se 1 (by rfl) ⟨654515, by rfl⟩ : syracuseStep 872687 = 1309031) B1309031
theorem B102029291 : Blo 515797 102029291 := bstep (se 1 (by rfl) ⟨76521968, by rfl⟩ : syracuseStep 102029291 = 153043937) B153043937
theorem B4417193 : Blo 515797 4417193 := bstep (se 2 (by rfl) ⟨1656447, by rfl⟩ : syracuseStep 4417193 = 3312895) B3312895
theorem B34007035 : Blo 515797 34007035 := bstep (se 1 (by rfl) ⟨25505276, by rfl⟩ : syracuseStep 34007035 = 51010553) B51010553
theorem B518255 : Blo 515797 518255 := bstep (se 1 (by rfl) ⟨388691, by rfl⟩ : syracuseStep 518255 = 777383) B777383
theorem B518503 : Blo 515797 518503 := bstep (se 1 (by rfl) ⟨388877, by rfl⟩ : syracuseStep 518503 = 777755) B777755
theorem B9956681 : Blo 515797 9956681 := bstep (se 2 (by rfl) ⟨3733755, by rfl⟩ : syracuseStep 9956681 = 7467511) B7467511
theorem B1305983 : Blo 515797 1305983 := bstep (se 1 (by rfl) ⟨979487, by rfl⟩ : syracuseStep 1305983 = 1958975) B1958975
theorem B1474301 : Blo 515797 1474301 := bstep (se 3 (by rfl) ⟨276431, by rfl⟩ : syracuseStep 1474301 = 552863) B552863
theorem B1966295 : Blo 515797 1966295 := bstep (se 1 (by rfl) ⟨1474721, by rfl⟩ : syracuseStep 1966295 = 2949443) B2949443
theorem B3935627 : Blo 515797 3935627 := bstep (se 1 (by rfl) ⟨2951720, by rfl⟩ : syracuseStep 3935627 = 5903441) B5903441
theorem B2497513 : Blo 515797 2497513 := bstep (se 2 (by rfl) ⟨936567, by rfl⟩ : syracuseStep 2497513 = 1873135) B1873135
theorem B2369195 : Blo 515797 2369195 := bstep (se 1 (by rfl) ⟨1776896, by rfl⟩ : syracuseStep 2369195 = 3553793) B3553793
theorem B1753271 : Blo 515797 1753271 := bstep (se 1 (by rfl) ⟨1314953, by rfl⟩ : syracuseStep 1753271 = 2629907) B2629907
theorem B1754027 : Blo 515797 1754027 := bstep (se 1 (by rfl) ⟨1315520, by rfl⟩ : syracuseStep 1754027 = 2631041) B2631041
theorem B1164239 : Blo 515797 1164239 := bstep (se 1 (by rfl) ⟨873179, by rfl⟩ : syracuseStep 1164239 = 1746359) B1746359
theorem B6637787 : Blo 515797 6637787 := bstep (se 1 (by rfl) ⟨4978340, by rfl⟩ : syracuseStep 6637787 = 9956681) B9956681
theorem B870655 : Blo 515797 870655 := bstep (se 1 (by rfl) ⟨652991, by rfl⟩ : syracuseStep 870655 = 1305983) B1305983
theorem B2217755 : Blo 515797 2217755 := bstep (se 1 (by rfl) ⟨1663316, by rfl⟩ : syracuseStep 2217755 = 3326633) B3326633
theorem B51632927 : Blo 515797 51632927 := bstep (se 1 (by rfl) ⟨38724695, by rfl⟩ : syracuseStep 51632927 = 77449391) B77449391
theorem B875515 : Blo 515797 875515 := bstep (se 1 (by rfl) ⟨656636, by rfl⟩ : syracuseStep 875515 = 1313273) B1313273
theorem B1105255 : Blo 515797 1105255 := bstep (se 1 (by rfl) ⟨828941, by rfl⟩ : syracuseStep 1105255 = 1657883) B1657883
theorem B875947 : Blo 515797 875947 := bstep (se 1 (by rfl) ⟨656960, by rfl⟩ : syracuseStep 875947 = 1313921) B1313921
theorem B45342713 : Blo 515797 45342713 := bstep (se 2 (by rfl) ⟨17003517, by rfl⟩ : syracuseStep 45342713 = 34007035) B34007035
theorem B516091 : Blo 515797 516091 := bstep (se 1 (by rfl) ⟨387068, by rfl⟩ : syracuseStep 516091 = 774137) B774137
theorem B516095 : Blo 515797 516095 := bstep (se 1 (by rfl) ⟨387071, by rfl⟩ : syracuseStep 516095 = 774143) B774143
theorem B581791 : Blo 515797 581791 := bstep (se 1 (by rfl) ⟨436343, by rfl⟩ : syracuseStep 581791 = 872687) B872687
theorem B68019527 : Blo 515797 68019527 := bstep (se 1 (by rfl) ⟨51014645, by rfl⟩ : syracuseStep 68019527 = 102029291) B102029291
theorem B33646859 : Blo 515797 33646859 := bstep (se 1 (by rfl) ⟨25235144, by rfl⟩ : syracuseStep 33646859 = 50470289) B50470289
theorem B2944795 : Blo 515797 2944795 := bstep (se 1 (by rfl) ⟨2208596, by rfl⟩ : syracuseStep 2944795 = 4417193) B4417193
theorem B982867 : Blo 515797 982867 := bstep (se 1 (by rfl) ⟨737150, by rfl⟩ : syracuseStep 982867 = 1474301) B1474301
theorem B1310863 : Blo 515797 1310863 := bstep (se 1 (by rfl) ⟨983147, by rfl⟩ : syracuseStep 1310863 = 1966295) B1966295
theorem B4425191 : Blo 515797 4425191 := bstep (se 1 (by rfl) ⟨3318893, by rfl⟩ : syracuseStep 4425191 = 6637787) B6637787
theorem B2623751 : Blo 515797 2623751 := bstep (se 1 (by rfl) ⟨1967813, by rfl⟩ : syracuseStep 2623751 = 3935627) B3935627
theorem B1478503 : Blo 515797 1478503 := bstep (se 1 (by rfl) ⟨1108877, by rfl⟩ : syracuseStep 1478503 = 2217755) B2217755
theorem B1579463 : Blo 515797 1579463 := bstep (se 1 (by rfl) ⟨1184597, by rfl⟩ : syracuseStep 1579463 = 2369195) B2369195
theorem B1160873 : Blo 515797 1160873 := bstep (se 2 (by rfl) ⟨435327, by rfl⟩ : syracuseStep 1160873 = 870655) B870655
theorem B34421951 : Blo 515797 34421951 := bstep (se 1 (by rfl) ⟨25816463, by rfl⟩ : syracuseStep 34421951 = 51632927) B51632927
theorem B30228475 : Blo 515797 30228475 := bstep (se 1 (by rfl) ⟨22671356, by rfl⟩ : syracuseStep 30228475 = 45342713) B45342713
theorem B22431239 : Blo 515797 22431239 := bstep (se 1 (by rfl) ⟨16823429, by rfl⟩ : syracuseStep 22431239 = 33646859) B33646859
theorem B3330017 : Blo 515797 3330017 := bstep (se 2 (by rfl) ⟨1248756, by rfl⟩ : syracuseStep 3330017 = 2497513) B2497513
theorem B1167353 : Blo 515797 1167353 := bstep (se 2 (by rfl) ⟨437757, by rfl⟩ : syracuseStep 1167353 = 875515) B875515
theorem B1167929 : Blo 515797 1167929 := bstep (se 2 (by rfl) ⟨437973, by rfl⟩ : syracuseStep 1167929 = 875947) B875947
theorem B1168847 : Blo 515797 1168847 := bstep (se 1 (by rfl) ⟨876635, by rfl⟩ : syracuseStep 1168847 = 1753271) B1753271
theorem B775721 : Blo 515797 775721 := bstep (se 2 (by rfl) ⟨290895, by rfl⟩ : syracuseStep 775721 = 581791) B581791
theorem B1169351 : Blo 515797 1169351 := bstep (se 1 (by rfl) ⟨877013, by rfl⟩ : syracuseStep 1169351 = 1754027) B1754027
theorem B776159 : Blo 515797 776159 := bstep (se 1 (by rfl) ⟨582119, by rfl⟩ : syracuseStep 776159 = 1164239) B1164239
theorem B3926393 : Blo 515797 3926393 := bstep (se 2 (by rfl) ⟨1472397, by rfl⟩ : syracuseStep 3926393 = 2944795) B2944795
theorem B45346351 : Blo 515797 45346351 := bstep (se 1 (by rfl) ⟨34009763, by rfl⟩ : syracuseStep 45346351 = 68019527) B68019527
theorem B5894693 : Blo 515797 5894693 := bstep (se 4 (by rfl) ⟨552627, by rfl⟩ : syracuseStep 5894693 = 1105255) B1105255
theorem B1310489 : Blo 515797 1310489 := bstep (se 2 (by rfl) ⟨491433, by rfl⟩ : syracuseStep 1310489 = 982867) B982867
theorem B2950127 : Blo 515797 2950127 := bstep (se 1 (by rfl) ⟨2212595, by rfl⟩ : syracuseStep 2950127 = 4425191) B4425191
theorem B1052975 : Blo 515797 1052975 := bstep (se 1 (by rfl) ⟨789731, by rfl⟩ : syracuseStep 1052975 = 1579463) B1579463
theorem B60461801 : Blo 515797 60461801 := bstep (se 2 (by rfl) ⟨22673175, by rfl⟩ : syracuseStep 60461801 = 45346351) B45346351
theorem B1971337 : Blo 515797 1971337 := bstep (se 2 (by rfl) ⟨739251, by rfl⟩ : syracuseStep 1971337 = 1478503) B1478503
theorem B22947967 : Blo 515797 22947967 := bstep (se 1 (by rfl) ⟨17210975, by rfl⟩ : syracuseStep 22947967 = 34421951) B34421951
theorem B1747817 : Blo 515797 1747817 := bstep (se 2 (by rfl) ⟨655431, by rfl⟩ : syracuseStep 1747817 = 1310863) B1310863
theorem B14954159 : Blo 515797 14954159 := bstep (se 1 (by rfl) ⟨11215619, by rfl⟩ : syracuseStep 14954159 = 22431239) B22431239
theorem B1749167 : Blo 515797 1749167 := bstep (se 1 (by rfl) ⟨1311875, by rfl⟩ : syracuseStep 1749167 = 2623751) B2623751
theorem B773915 : Blo 515797 773915 := bstep (se 1 (by rfl) ⟨580436, by rfl⟩ : syracuseStep 773915 = 1160873) B1160873
theorem B873659 : Blo 515797 873659 := bstep (se 1 (by rfl) ⟨655244, by rfl⟩ : syracuseStep 873659 = 1310489) B1310489
theorem B2220011 : Blo 515797 2220011 := bstep (se 1 (by rfl) ⟨1665008, by rfl⟩ : syracuseStep 2220011 = 3330017) B3330017
theorem B778235 : Blo 515797 778235 := bstep (se 1 (by rfl) ⟨583676, by rfl⟩ : syracuseStep 778235 = 1167353) B1167353
theorem B778619 : Blo 515797 778619 := bstep (se 1 (by rfl) ⟨583964, by rfl⟩ : syracuseStep 778619 = 1167929) B1167929
theorem B779231 : Blo 515797 779231 := bstep (se 1 (by rfl) ⟨584423, by rfl⟩ : syracuseStep 779231 = 1168847) B1168847
theorem B517147 : Blo 515797 517147 := bstep (se 1 (by rfl) ⟨387860, by rfl⟩ : syracuseStep 517147 = 775721) B775721
theorem B779567 : Blo 515797 779567 := bstep (se 1 (by rfl) ⟨584675, by rfl⟩ : syracuseStep 779567 = 1169351) B1169351
theorem B517439 : Blo 515797 517439 := bstep (se 1 (by rfl) ⟨388079, by rfl⟩ : syracuseStep 517439 = 776159) B776159
theorem B2617595 : Blo 515797 2617595 := bstep (se 1 (by rfl) ⟨1963196, by rfl⟩ : syracuseStep 2617595 = 3926393) B3926393
theorem B3929795 : Blo 515797 3929795 := bstep (se 1 (by rfl) ⟨2947346, by rfl⟩ : syracuseStep 3929795 = 5894693) B5894693
theorem B40304633 : Blo 515797 40304633 := bstep (se 2 (by rfl) ⟨15114237, by rfl⟩ : syracuseStep 40304633 = 30228475) B30228475
theorem B1966751 : Blo 515797 1966751 := bstep (se 1 (by rfl) ⟨1475063, by rfl⟩ : syracuseStep 1966751 = 2950127) B2950127
theorem B122389157 : Blo 515797 122389157 := bstep (se 4 (by rfl) ⟨11473983, by rfl⟩ : syracuseStep 122389157 = 22947967) B22947967
theorem B40307867 : Blo 515797 40307867 := bstep (se 1 (by rfl) ⟨30230900, by rfl⟩ : syracuseStep 40307867 = 60461801) B60461801
theorem B1480007 : Blo 515797 1480007 := bstep (se 1 (by rfl) ⟨1110005, by rfl⟩ : syracuseStep 1480007 = 2220011) B2220011
theorem B2628449 : Blo 515797 2628449 := bstep (se 2 (by rfl) ⟨985668, by rfl⟩ : syracuseStep 2628449 = 1971337) B1971337
theorem B9969439 : Blo 515797 9969439 := bstep (se 1 (by rfl) ⟨7477079, by rfl⟩ : syracuseStep 9969439 = 14954159) B14954159
theorem B1745063 : Blo 515797 1745063 := bstep (se 1 (by rfl) ⟨1308797, by rfl⟩ : syracuseStep 1745063 = 2617595) B2617595
theorem B701983 : Blo 515797 701983 := bstep (se 1 (by rfl) ⟨526487, by rfl⟩ : syracuseStep 701983 = 1052975) B1052975
theorem B1165211 : Blo 515797 1165211 := bstep (se 1 (by rfl) ⟨873908, by rfl⟩ : syracuseStep 1165211 = 1747817) B1747817
theorem B1166111 : Blo 515797 1166111 := bstep (se 1 (by rfl) ⟨874583, by rfl⟩ : syracuseStep 1166111 = 1749167) B1749167
theorem B515943 : Blo 515797 515943 := bstep (se 1 (by rfl) ⟨386957, by rfl⟩ : syracuseStep 515943 = 773915) B773915
theorem B582439 : Blo 515797 582439 := bstep (se 1 (by rfl) ⟨436829, by rfl⟩ : syracuseStep 582439 = 873659) B873659
theorem B518823 : Blo 515797 518823 := bstep (se 1 (by rfl) ⟨389117, by rfl⟩ : syracuseStep 518823 = 778235) B778235
theorem B519079 : Blo 515797 519079 := bstep (se 1 (by rfl) ⟨389309, by rfl⟩ : syracuseStep 519079 = 778619) B778619
theorem B519487 : Blo 515797 519487 := bstep (se 1 (by rfl) ⟨389615, by rfl⟩ : syracuseStep 519487 = 779231) B779231
theorem B519711 : Blo 515797 519711 := bstep (se 1 (by rfl) ⟨389783, by rfl⟩ : syracuseStep 519711 = 779567) B779567
theorem B2619863 : Blo 515797 2619863 := bstep (se 1 (by rfl) ⟨1964897, by rfl⟩ : syracuseStep 2619863 = 3929795) B3929795
theorem B107479021 : Blo 515797 107479021 := bstep (se 3 (by rfl) ⟨20152316, by rfl⟩ : syracuseStep 107479021 = 40304633) B40304633
theorem B1311167 : Blo 515797 1311167 := bstep (se 1 (by rfl) ⟨983375, by rfl⟩ : syracuseStep 1311167 = 1966751) B1966751
theorem B81592771 : Blo 515797 81592771 := bstep (se 1 (by rfl) ⟨61194578, by rfl⟩ : syracuseStep 81592771 = 122389157) B122389157
theorem B26871911 : Blo 515797 26871911 := bstep (se 1 (by rfl) ⟨20153933, by rfl⟩ : syracuseStep 26871911 = 40307867) B40307867
theorem B986671 : Blo 515797 986671 := bstep (se 1 (by rfl) ⟨740003, by rfl⟩ : syracuseStep 986671 = 1480007) B1480007
theorem B1746575 : Blo 515797 1746575 := bstep (se 1 (by rfl) ⟨1309931, by rfl⟩ : syracuseStep 1746575 = 2619863) B2619863
theorem B143305361 : Blo 515797 143305361 := bstep (se 2 (by rfl) ⟨53739510, by rfl⟩ : syracuseStep 143305361 = 107479021) B107479021
theorem B1752299 : Blo 515797 1752299 := bstep (se 1 (by rfl) ⟨1314224, by rfl⟩ : syracuseStep 1752299 = 2628449) B2628449
theorem B1163375 : Blo 515797 1163375 := bstep (se 1 (by rfl) ⟨872531, by rfl⟩ : syracuseStep 1163375 = 1745063) B1745063
theorem B935977 : Blo 515797 935977 := bstep (se 2 (by rfl) ⟨350991, by rfl⟩ : syracuseStep 935977 = 701983) B701983
theorem B13292585 : Blo 515797 13292585 := bstep (se 2 (by rfl) ⟨4984719, by rfl⟩ : syracuseStep 13292585 = 9969439) B9969439
theorem B776585 : Blo 515797 776585 := bstep (se 2 (by rfl) ⟨291219, by rfl⟩ : syracuseStep 776585 = 582439) B582439
theorem B776807 : Blo 515797 776807 := bstep (se 1 (by rfl) ⟨582605, by rfl⟩ : syracuseStep 776807 = 1165211) B1165211
theorem B777407 : Blo 515797 777407 := bstep (se 1 (by rfl) ⟨583055, by rfl⟩ : syracuseStep 777407 = 1166111) B1166111
theorem B108790361 : Blo 515797 108790361 := bstep (se 2 (by rfl) ⟨40796385, by rfl⟩ : syracuseStep 108790361 = 81592771) B81592771
theorem B1247969 : Blo 515797 1247969 := bstep (se 2 (by rfl) ⟨467988, by rfl⟩ : syracuseStep 1247969 = 935977) B935977
theorem B1315561 : Blo 515797 1315561 := bstep (se 2 (by rfl) ⟨493335, by rfl⟩ : syracuseStep 1315561 = 986671) B986671
theorem B8861723 : Blo 515797 8861723 := bstep (se 1 (by rfl) ⟨6646292, by rfl⟩ : syracuseStep 8861723 = 13292585) B13292585
theorem B1164383 : Blo 515797 1164383 := bstep (se 1 (by rfl) ⟨873287, by rfl⟩ : syracuseStep 1164383 = 1746575) B1746575
theorem B95536907 : Blo 515797 95536907 := bstep (se 1 (by rfl) ⟨71652680, by rfl⟩ : syracuseStep 95536907 = 143305361) B143305361
theorem B1168199 : Blo 515797 1168199 := bstep (se 1 (by rfl) ⟨876149, by rfl⟩ : syracuseStep 1168199 = 1752299) B1752299
theorem B775583 : Blo 515797 775583 := bstep (se 1 (by rfl) ⟨581687, by rfl⟩ : syracuseStep 775583 = 1163375) B1163375
theorem B874111 : Blo 515797 874111 := bstep (se 1 (by rfl) ⟨655583, by rfl⟩ : syracuseStep 874111 = 1311167) B1311167
theorem B17914607 : Blo 515797 17914607 := bstep (se 1 (by rfl) ⟨13435955, by rfl⟩ : syracuseStep 17914607 = 26871911) B26871911
theorem B517723 : Blo 515797 517723 := bstep (se 1 (by rfl) ⟨388292, by rfl⟩ : syracuseStep 517723 = 776585) B776585
theorem B517871 : Blo 515797 517871 := bstep (se 1 (by rfl) ⟨388403, by rfl⟩ : syracuseStep 517871 = 776807) B776807
theorem B518271 : Blo 515797 518271 := bstep (se 1 (by rfl) ⟨388703, by rfl⟩ : syracuseStep 518271 = 777407) B777407
theorem B5907815 : Blo 515797 5907815 := bstep (se 1 (by rfl) ⟨4430861, by rfl⟩ : syracuseStep 5907815 = 8861723) B8861723
theorem B72526907 : Blo 515797 72526907 := bstep (se 1 (by rfl) ⟨54395180, by rfl⟩ : syracuseStep 72526907 = 108790361) B108790361
theorem B831979 : Blo 515797 831979 := bstep (se 1 (by rfl) ⟨623984, by rfl⟩ : syracuseStep 831979 = 1247969) B1247969
theorem B11943071 : Blo 515797 11943071 := bstep (se 1 (by rfl) ⟨8957303, by rfl⟩ : syracuseStep 11943071 = 17914607) B17914607
theorem B1754081 : Blo 515797 1754081 := bstep (se 2 (by rfl) ⟨657780, by rfl⟩ : syracuseStep 1754081 = 1315561) B1315561
theorem B1165481 : Blo 515797 1165481 := bstep (se 2 (by rfl) ⟨437055, by rfl⟩ : syracuseStep 1165481 = 874111) B874111
theorem B776255 : Blo 515797 776255 := bstep (se 1 (by rfl) ⟨582191, by rfl⟩ : syracuseStep 776255 = 1164383) B1164383
theorem B63691271 : Blo 515797 63691271 := bstep (se 1 (by rfl) ⟨47768453, by rfl⟩ : syracuseStep 63691271 = 95536907) B95536907
theorem B778799 : Blo 515797 778799 := bstep (se 1 (by rfl) ⟨584099, by rfl⟩ : syracuseStep 778799 = 1168199) B1168199
theorem B517055 : Blo 515797 517055 := bstep (se 1 (by rfl) ⟨387791, by rfl⟩ : syracuseStep 517055 = 775583) B775583
theorem B3938543 : Blo 515797 3938543 := bstep (se 1 (by rfl) ⟨2953907, by rfl⟩ : syracuseStep 3938543 = 5907815) B5907815
theorem B48351271 : Blo 515797 48351271 := bstep (se 1 (by rfl) ⟨36263453, by rfl⟩ : syracuseStep 48351271 = 72526907) B72526907
theorem B1169387 : Blo 515797 1169387 := bstep (se 1 (by rfl) ⟨877040, by rfl⟩ : syracuseStep 1169387 = 1754081) B1754081
theorem B776987 : Blo 515797 776987 := bstep (se 1 (by rfl) ⟨582740, by rfl⟩ : syracuseStep 776987 = 1165481) B1165481
theorem B517503 : Blo 515797 517503 := bstep (se 1 (by rfl) ⟨388127, by rfl⟩ : syracuseStep 517503 = 776255) B776255
theorem B42460847 : Blo 515797 42460847 := bstep (se 1 (by rfl) ⟨31845635, by rfl⟩ : syracuseStep 42460847 = 63691271) B63691271
theorem B519199 : Blo 515797 519199 := bstep (se 1 (by rfl) ⟨389399, by rfl⟩ : syracuseStep 519199 = 778799) B778799
theorem B1109305 : Blo 515797 1109305 := bstep (se 2 (by rfl) ⟨415989, by rfl⟩ : syracuseStep 1109305 = 831979) B831979
theorem B7962047 : Blo 515797 7962047 := bstep (se 1 (by rfl) ⟨5971535, by rfl⟩ : syracuseStep 7962047 = 11943071) B11943071
theorem B2625695 : Blo 515797 2625695 := bstep (se 1 (by rfl) ⟨1969271, by rfl⟩ : syracuseStep 2625695 = 3938543) B3938543
theorem B1479073 : Blo 515797 1479073 := bstep (se 2 (by rfl) ⟨554652, by rfl⟩ : syracuseStep 1479073 = 1109305) B1109305
theorem B64468361 : Blo 515797 64468361 := bstep (se 2 (by rfl) ⟨24175635, by rfl⟩ : syracuseStep 64468361 = 48351271) B48351271
theorem B779591 : Blo 515797 779591 := bstep (se 1 (by rfl) ⟨584693, by rfl⟩ : syracuseStep 779591 = 1169387) B1169387
theorem B517991 : Blo 515797 517991 := bstep (se 1 (by rfl) ⟨388493, by rfl⟩ : syracuseStep 517991 = 776987) B776987
theorem B28307231 : Blo 515797 28307231 := bstep (se 1 (by rfl) ⟨21230423, by rfl⟩ : syracuseStep 28307231 = 42460847) B42460847
theorem B5308031 : Blo 515797 5308031 := bstep (se 1 (by rfl) ⟨3981023, by rfl⟩ : syracuseStep 5308031 = 7962047) B7962047
theorem B1972097 : Blo 515797 1972097 := bstep (se 2 (by rfl) ⟨739536, by rfl⟩ : syracuseStep 1972097 = 1479073) B1479073
theorem B1750463 : Blo 515797 1750463 := bstep (se 1 (by rfl) ⟨1312847, by rfl⟩ : syracuseStep 1750463 = 2625695) B2625695
theorem B42978907 : Blo 515797 42978907 := bstep (se 1 (by rfl) ⟨32234180, by rfl⟩ : syracuseStep 42978907 = 64468361) B64468361
theorem B519727 : Blo 515797 519727 := bstep (se 1 (by rfl) ⟨389795, by rfl⟩ : syracuseStep 519727 = 779591) B779591
theorem B18871487 : Blo 515797 18871487 := bstep (se 1 (by rfl) ⟨14153615, by rfl⟩ : syracuseStep 18871487 = 28307231) B28307231
theorem B3538687 : Blo 515797 3538687 := bstep (se 1 (by rfl) ⟨2654015, by rfl⟩ : syracuseStep 3538687 = 5308031) B5308031
theorem B1314731 : Blo 515797 1314731 := bstep (se 1 (by rfl) ⟨986048, by rfl⟩ : syracuseStep 1314731 = 1972097) B1972097
theorem B229220837 : Blo 515797 229220837 := bstep (se 4 (by rfl) ⟨21489453, by rfl⟩ : syracuseStep 229220837 = 42978907) B42978907
theorem B1166975 : Blo 515797 1166975 := bstep (se 1 (by rfl) ⟨875231, by rfl⟩ : syracuseStep 1166975 = 1750463) B1750463
theorem B12580991 : Blo 515797 12580991 := bstep (se 1 (by rfl) ⟨9435743, by rfl⟩ : syracuseStep 12580991 = 18871487) B18871487
theorem B4718249 : Blo 515797 4718249 := bstep (se 2 (by rfl) ⟨1769343, by rfl⟩ : syracuseStep 4718249 = 3538687) B3538687
theorem B152813891 : Blo 515797 152813891 := bstep (se 1 (by rfl) ⟨114610418, by rfl⟩ : syracuseStep 152813891 = 229220837) B229220837
theorem B777983 : Blo 515797 777983 := bstep (se 1 (by rfl) ⟨583487, by rfl⟩ : syracuseStep 777983 = 1166975) B1166975
theorem B876487 : Blo 515797 876487 := bstep (se 1 (by rfl) ⟨657365, by rfl⟩ : syracuseStep 876487 = 1314731) B1314731
theorem B8387327 : Blo 515797 8387327 := bstep (se 1 (by rfl) ⟨6290495, by rfl⟩ : syracuseStep 8387327 = 12580991) B12580991
theorem B3145499 : Blo 515797 3145499 := bstep (se 1 (by rfl) ⟨2359124, by rfl⟩ : syracuseStep 3145499 = 4718249) B4718249
theorem B101875927 : Blo 515797 101875927 := bstep (se 1 (by rfl) ⟨76406945, by rfl⟩ : syracuseStep 101875927 = 152813891) B152813891
theorem B5591551 : Blo 515797 5591551 := bstep (se 1 (by rfl) ⟨4193663, by rfl⟩ : syracuseStep 5591551 = 8387327) B8387327
theorem B1168649 : Blo 515797 1168649 := bstep (se 2 (by rfl) ⟨438243, by rfl⟩ : syracuseStep 1168649 = 876487) B876487
theorem B518655 : Blo 515797 518655 := bstep (se 1 (by rfl) ⟨388991, by rfl⟩ : syracuseStep 518655 = 777983) B777983
theorem B2096999 : Blo 515797 2096999 := bstep (se 1 (by rfl) ⟨1572749, by rfl⟩ : syracuseStep 2096999 = 3145499) B3145499
theorem B135834569 : Blo 515797 135834569 := bstep (se 2 (by rfl) ⟨50937963, by rfl⟩ : syracuseStep 135834569 = 101875927) B101875927
theorem B7455401 : Blo 515797 7455401 := bstep (se 2 (by rfl) ⟨2795775, by rfl⟩ : syracuseStep 7455401 = 5591551) B5591551
theorem B1397999 : Blo 515797 1397999 := bstep (se 1 (by rfl) ⟨1048499, by rfl⟩ : syracuseStep 1397999 = 2096999) B2096999
theorem B779099 : Blo 515797 779099 := bstep (se 1 (by rfl) ⟨584324, by rfl⟩ : syracuseStep 779099 = 1168649) B1168649
theorem B931999 : Blo 515797 931999 := bstep (se 1 (by rfl) ⟨698999, by rfl⟩ : syracuseStep 931999 = 1397999) B1397999
theorem B90556379 : Blo 515797 90556379 := bstep (se 1 (by rfl) ⟨67917284, by rfl⟩ : syracuseStep 90556379 = 135834569) B135834569
theorem B4970267 : Blo 515797 4970267 := bstep (se 1 (by rfl) ⟨3727700, by rfl⟩ : syracuseStep 4970267 = 7455401) B7455401
theorem B519399 : Blo 515797 519399 := bstep (se 1 (by rfl) ⟨389549, by rfl⟩ : syracuseStep 519399 = 779099) B779099
theorem B3313511 : Blo 515797 3313511 := bstep (se 1 (by rfl) ⟨2485133, by rfl⟩ : syracuseStep 3313511 = 4970267) B4970267
theorem B60370919 : Blo 515797 60370919 := bstep (se 1 (by rfl) ⟨45278189, by rfl⟩ : syracuseStep 60370919 = 90556379) B90556379
theorem B1242665 : Blo 515797 1242665 := bstep (se 2 (by rfl) ⟨465999, by rfl⟩ : syracuseStep 1242665 = 931999) B931999
theorem B40247279 : Blo 515797 40247279 := bstep (se 1 (by rfl) ⟨30185459, by rfl⟩ : syracuseStep 40247279 = 60370919) B60370919
theorem B828443 : Blo 515797 828443 := bstep (se 1 (by rfl) ⟨621332, by rfl⟩ : syracuseStep 828443 = 1242665) B1242665
theorem B2209007 : Blo 515797 2209007 := bstep (se 1 (by rfl) ⟨1656755, by rfl⟩ : syracuseStep 2209007 = 3313511) B3313511
theorem B26831519 : Blo 515797 26831519 := bstep (se 1 (by rfl) ⟨20123639, by rfl⟩ : syracuseStep 26831519 = 40247279) B40247279
theorem B552295 : Blo 515797 552295 := bstep (se 1 (by rfl) ⟨414221, by rfl⟩ : syracuseStep 552295 = 828443) B828443
theorem B1472671 : Blo 515797 1472671 := bstep (se 1 (by rfl) ⟨1104503, by rfl⟩ : syracuseStep 1472671 = 2209007) B2209007
theorem B736393 : Blo 515797 736393 := bstep (se 2 (by rfl) ⟨276147, by rfl⟩ : syracuseStep 736393 = 552295) B552295
theorem B17887679 : Blo 515797 17887679 := bstep (se 1 (by rfl) ⟨13415759, by rfl⟩ : syracuseStep 17887679 = 26831519) B26831519
theorem B1963561 : Blo 515797 1963561 := bstep (se 2 (by rfl) ⟨736335, by rfl⟩ : syracuseStep 1963561 = 1472671) B1472671
theorem B2618081 : Blo 515797 2618081 := bstep (se 2 (by rfl) ⟨981780, by rfl⟩ : syracuseStep 2618081 = 1963561) B1963561
theorem B11925119 : Blo 515797 11925119 := bstep (se 1 (by rfl) ⟨8943839, by rfl⟩ : syracuseStep 11925119 = 17887679) B17887679
theorem B981857 : Blo 515797 981857 := bstep (se 2 (by rfl) ⟨368196, by rfl⟩ : syracuseStep 981857 = 736393) B736393
theorem B1745387 : Blo 515797 1745387 := bstep (se 1 (by rfl) ⟨1309040, by rfl⟩ : syracuseStep 1745387 = 2618081) B2618081
theorem B7950079 : Blo 515797 7950079 := bstep (se 1 (by rfl) ⟨5962559, by rfl⟩ : syracuseStep 7950079 = 11925119) B11925119
theorem B654571 : Blo 515797 654571 := bstep (se 1 (by rfl) ⟨490928, by rfl⟩ : syracuseStep 654571 = 981857) B981857
theorem B10600105 : Blo 515797 10600105 := bstep (se 2 (by rfl) ⟨3975039, by rfl⟩ : syracuseStep 10600105 = 7950079) B7950079
theorem B1163591 : Blo 515797 1163591 := bstep (se 1 (by rfl) ⟨872693, by rfl⟩ : syracuseStep 1163591 = 1745387) B1745387
theorem B872761 : Blo 515797 872761 := bstep (se 2 (by rfl) ⟨327285, by rfl⟩ : syracuseStep 872761 = 654571) B654571
theorem B14133473 : Blo 515797 14133473 := bstep (se 2 (by rfl) ⟨5300052, by rfl⟩ : syracuseStep 14133473 = 10600105) B10600105
theorem B1163681 : Blo 515797 1163681 := bstep (se 2 (by rfl) ⟨436380, by rfl⟩ : syracuseStep 1163681 = 872761) B872761
theorem B775727 : Blo 515797 775727 := bstep (se 1 (by rfl) ⟨581795, by rfl⟩ : syracuseStep 775727 = 1163591) B1163591
theorem B9422315 : Blo 515797 9422315 := bstep (se 1 (by rfl) ⟨7066736, by rfl⟩ : syracuseStep 9422315 = 14133473) B14133473
theorem B775787 : Blo 515797 775787 := bstep (se 1 (by rfl) ⟨581840, by rfl⟩ : syracuseStep 775787 = 1163681) B1163681
theorem B517151 : Blo 515797 517151 := bstep (se 1 (by rfl) ⟨387863, by rfl⟩ : syracuseStep 517151 = 775727) B775727
theorem B6281543 : Blo 515797 6281543 := bstep (se 1 (by rfl) ⟨4711157, by rfl⟩ : syracuseStep 6281543 = 9422315) B9422315
theorem B517191 : Blo 515797 517191 := bstep (se 1 (by rfl) ⟨387893, by rfl⟩ : syracuseStep 517191 = 775787) B775787
theorem B4187695 : Blo 515797 4187695 := bstep (se 1 (by rfl) ⟨3140771, by rfl⟩ : syracuseStep 4187695 = 6281543) B6281543
theorem B5583593 : Blo 515797 5583593 := bstep (se 2 (by rfl) ⟨2093847, by rfl⟩ : syracuseStep 5583593 = 4187695) B4187695
theorem B3722395 : Blo 515797 3722395 := bstep (se 1 (by rfl) ⟨2791796, by rfl⟩ : syracuseStep 3722395 = 5583593) B5583593
theorem B4963193 : Blo 515797 4963193 := bstep (se 2 (by rfl) ⟨1861197, by rfl⟩ : syracuseStep 4963193 = 3722395) B3722395
theorem B3308795 : Blo 515797 3308795 := bstep (se 1 (by rfl) ⟨2481596, by rfl⟩ : syracuseStep 3308795 = 4963193) B4963193
theorem B2205863 : Blo 515797 2205863 := bstep (se 1 (by rfl) ⟨1654397, by rfl⟩ : syracuseStep 2205863 = 3308795) B3308795
theorem B1470575 : Blo 515797 1470575 := bstep (se 1 (by rfl) ⟨1102931, by rfl⟩ : syracuseStep 1470575 = 2205863) B2205863
theorem B3921533 : Blo 515797 3921533 := bstep (se 3 (by rfl) ⟨735287, by rfl⟩ : syracuseStep 3921533 = 1470575) B1470575
theorem B2614355 : Blo 515797 2614355 := bstep (se 1 (by rfl) ⟨1960766, by rfl⟩ : syracuseStep 2614355 = 3921533) B3921533
theorem B1742903 : Blo 515797 1742903 := bstep (se 1 (by rfl) ⟨1307177, by rfl⟩ : syracuseStep 1742903 = 2614355) B2614355
theorem B1161935 : Blo 515797 1161935 := bstep (se 1 (by rfl) ⟨871451, by rfl⟩ : syracuseStep 1161935 = 1742903) B1742903
theorem B774623 : Blo 515797 774623 := bstep (se 1 (by rfl) ⟨580967, by rfl⟩ : syracuseStep 774623 = 1161935) B1161935
theorem B516415 : Blo 515797 516415 := bstep (se 1 (by rfl) ⟨387311, by rfl⟩ : syracuseStep 516415 = 774623) B774623

theorem C0 (j : ℕ) (h1 : 128949 ≤ j) (h2 : j ≤ 129648) : Blo 515797 (4 * j + 3) := by
  interval_cases j
  · exact B515799
  · exact B515803
  · exact B515807
  · exact B515811
  · exact B515815
  · exact B515819
  · exact B515823
  · exact B515827
  · exact B515831
  · exact B515835
  · exact B515839
  · exact B515843
  · exact B515847
  · exact B515851
  · exact B515855
  · exact B515859
  · exact B515863
  · exact B515867
  · exact B515871
  · exact B515875
  · exact B515879
  · exact B515883
  · exact B515887
  · exact B515891
  · exact B515895
  · exact B515899
  · exact B515903
  · exact B515907
  · exact B515911
  · exact B515915
  · exact B515919
  · exact B515923
  · exact B515927
  · exact B515931
  · exact B515935
  · exact B515939
  · exact B515943
  · exact B515947
  · exact B515951
  · exact B515955
  · exact B515959
  · exact B515963
  · exact B515967
  · exact B515971
  · exact B515975
  · exact B515979
  · exact B515983
  · exact B515987
  · exact B515991
  · exact B515995
  · exact B515999
  · exact B516003
  · exact B516007
  · exact B516011
  · exact B516015
  · exact B516019
  · exact B516023
  · exact B516027
  · exact B516031
  · exact B516035
  · exact B516039
  · exact B516043
  · exact B516047
  · exact B516051
  · exact B516055
  · exact B516059
  · exact B516063
  · exact B516067
  · exact B516071
  · exact B516075
  · exact B516079
  · exact B516083
  · exact B516087
  · exact B516091
  · exact B516095
  · exact B516099
  · exact B516103
  · exact B516107
  · exact B516111
  · exact B516115
  · exact B516119
  · exact B516123
  · exact B516127
  · exact B516131
  · exact B516135
  · exact B516139
  · exact B516143
  · exact B516147
  · exact B516151
  · exact B516155
  · exact B516159
  · exact B516163
  · exact B516167
  · exact B516171
  · exact B516175
  · exact B516179
  · exact B516183
  · exact B516187
  · exact B516191
  · exact B516195
  · exact B516199
  · exact B516203
  · exact B516207
  · exact B516211
  · exact B516215
  · exact B516219
  · exact B516223
  · exact B516227
  · exact B516231
  · exact B516235
  · exact B516239
  · exact B516243
  · exact B516247
  · exact B516251
  · exact B516255
  · exact B516259
  · exact B516263
  · exact B516267
  · exact B516271
  · exact B516275
  · exact B516279
  · exact B516283
  · exact B516287
  · exact B516291
  · exact B516295
  · exact B516299
  · exact B516303
  · exact B516307
  · exact B516311
  · exact B516315
  · exact B516319
  · exact B516323
  · exact B516327
  · exact B516331
  · exact B516335
  · exact B516339
  · exact B516343
  · exact B516347
  · exact B516351
  · exact B516355
  · exact B516359
  · exact B516363
  · exact B516367
  · exact B516371
  · exact B516375
  · exact B516379
  · exact B516383
  · exact B516387
  · exact B516391
  · exact B516395
  · exact B516399
  · exact B516403
  · exact B516407
  · exact B516411
  · exact B516415
  · exact B516419
  · exact B516423
  · exact B516427
  · exact B516431
  · exact B516435
  · exact B516439
  · exact B516443
  · exact B516447
  · exact B516451
  · exact B516455
  · exact B516459
  · exact B516463
  · exact B516467
  · exact B516471
  · exact B516475
  · exact B516479
  · exact B516483
  · exact B516487
  · exact B516491
  · exact B516495
  · exact B516499
  · exact B516503
  · exact B516507
  · exact B516511
  · exact B516515
  · exact B516519
  · exact B516523
  · exact B516527
  · exact B516531
  · exact B516535
  · exact B516539
  · exact B516543
  · exact B516547
  · exact B516551
  · exact B516555
  · exact B516559
  · exact B516563
  · exact B516567
  · exact B516571
  · exact B516575
  · exact B516579
  · exact B516583
  · exact B516587
  · exact B516591
  · exact B516595
  · exact B516599
  · exact B516603
  · exact B516607
  · exact B516611
  · exact B516615
  · exact B516619
  · exact B516623
  · exact B516627
  · exact B516631
  · exact B516635
  · exact B516639
  · exact B516643
  · exact B516647
  · exact B516651
  · exact B516655
  · exact B516659
  · exact B516663
  · exact B516667
  · exact B516671
  · exact B516675
  · exact B516679
  · exact B516683
  · exact B516687
  · exact B516691
  · exact B516695
  · exact B516699
  · exact B516703
  · exact B516707
  · exact B516711
  · exact B516715
  · exact B516719
  · exact B516723
  · exact B516727
  · exact B516731
  · exact B516735
  · exact B516739
  · exact B516743
  · exact B516747
  · exact B516751
  · exact B516755
  · exact B516759
  · exact B516763
  · exact B516767
  · exact B516771
  · exact B516775
  · exact B516779
  · exact B516783
  · exact B516787
  · exact B516791
  · exact B516795
  · exact B516799
  · exact B516803
  · exact B516807
  · exact B516811
  · exact B516815
  · exact B516819
  · exact B516823
  · exact B516827
  · exact B516831
  · exact B516835
  · exact B516839
  · exact B516843
  · exact B516847
  · exact B516851
  · exact B516855
  · exact B516859
  · exact B516863
  · exact B516867
  · exact B516871
  · exact B516875
  · exact B516879
  · exact B516883
  · exact B516887
  · exact B516891
  · exact B516895
  · exact B516899
  · exact B516903
  · exact B516907
  · exact B516911
  · exact B516915
  · exact B516919
  · exact B516923
  · exact B516927
  · exact B516931
  · exact B516935
  · exact B516939
  · exact B516943
  · exact B516947
  · exact B516951
  · exact B516955
  · exact B516959
  · exact B516963
  · exact B516967
  · exact B516971
  · exact B516975
  · exact B516979
  · exact B516983
  · exact B516987
  · exact B516991
  · exact B516995
  · exact B516999
  · exact B517003
  · exact B517007
  · exact B517011
  · exact B517015
  · exact B517019
  · exact B517023
  · exact B517027
  · exact B517031
  · exact B517035
  · exact B517039
  · exact B517043
  · exact B517047
  · exact B517051
  · exact B517055
  · exact B517059
  · exact B517063
  · exact B517067
  · exact B517071
  · exact B517075
  · exact B517079
  · exact B517083
  · exact B517087
  · exact B517091
  · exact B517095
  · exact B517099
  · exact B517103
  · exact B517107
  · exact B517111
  · exact B517115
  · exact B517119
  · exact B517123
  · exact B517127
  · exact B517131
  · exact B517135
  · exact B517139
  · exact B517143
  · exact B517147
  · exact B517151
  · exact B517155
  · exact B517159
  · exact B517163
  · exact B517167
  · exact B517171
  · exact B517175
  · exact B517179
  · exact B517183
  · exact B517187
  · exact B517191
  · exact B517195
  · exact B517199
  · exact B517203
  · exact B517207
  · exact B517211
  · exact B517215
  · exact B517219
  · exact B517223
  · exact B517227
  · exact B517231
  · exact B517235
  · exact B517239
  · exact B517243
  · exact B517247
  · exact B517251
  · exact B517255
  · exact B517259
  · exact B517263
  · exact B517267
  · exact B517271
  · exact B517275
  · exact B517279
  · exact B517283
  · exact B517287
  · exact B517291
  · exact B517295
  · exact B517299
  · exact B517303
  · exact B517307
  · exact B517311
  · exact B517315
  · exact B517319
  · exact B517323
  · exact B517327
  · exact B517331
  · exact B517335
  · exact B517339
  · exact B517343
  · exact B517347
  · exact B517351
  · exact B517355
  · exact B517359
  · exact B517363
  · exact B517367
  · exact B517371
  · exact B517375
  · exact B517379
  · exact B517383
  · exact B517387
  · exact B517391
  · exact B517395
  · exact B517399
  · exact B517403
  · exact B517407
  · exact B517411
  · exact B517415
  · exact B517419
  · exact B517423
  · exact B517427
  · exact B517431
  · exact B517435
  · exact B517439
  · exact B517443
  · exact B517447
  · exact B517451
  · exact B517455
  · exact B517459
  · exact B517463
  · exact B517467
  · exact B517471
  · exact B517475
  · exact B517479
  · exact B517483
  · exact B517487
  · exact B517491
  · exact B517495
  · exact B517499
  · exact B517503
  · exact B517507
  · exact B517511
  · exact B517515
  · exact B517519
  · exact B517523
  · exact B517527
  · exact B517531
  · exact B517535
  · exact B517539
  · exact B517543
  · exact B517547
  · exact B517551
  · exact B517555
  · exact B517559
  · exact B517563
  · exact B517567
  · exact B517571
  · exact B517575
  · exact B517579
  · exact B517583
  · exact B517587
  · exact B517591
  · exact B517595
  · exact B517599
  · exact B517603
  · exact B517607
  · exact B517611
  · exact B517615
  · exact B517619
  · exact B517623
  · exact B517627
  · exact B517631
  · exact B517635
  · exact B517639
  · exact B517643
  · exact B517647
  · exact B517651
  · exact B517655
  · exact B517659
  · exact B517663
  · exact B517667
  · exact B517671
  · exact B517675
  · exact B517679
  · exact B517683
  · exact B517687
  · exact B517691
  · exact B517695
  · exact B517699
  · exact B517703
  · exact B517707
  · exact B517711
  · exact B517715
  · exact B517719
  · exact B517723
  · exact B517727
  · exact B517731
  · exact B517735
  · exact B517739
  · exact B517743
  · exact B517747
  · exact B517751
  · exact B517755
  · exact B517759
  · exact B517763
  · exact B517767
  · exact B517771
  · exact B517775
  · exact B517779
  · exact B517783
  · exact B517787
  · exact B517791
  · exact B517795
  · exact B517799
  · exact B517803
  · exact B517807
  · exact B517811
  · exact B517815
  · exact B517819
  · exact B517823
  · exact B517827
  · exact B517831
  · exact B517835
  · exact B517839
  · exact B517843
  · exact B517847
  · exact B517851
  · exact B517855
  · exact B517859
  · exact B517863
  · exact B517867
  · exact B517871
  · exact B517875
  · exact B517879
  · exact B517883
  · exact B517887
  · exact B517891
  · exact B517895
  · exact B517899
  · exact B517903
  · exact B517907
  · exact B517911
  · exact B517915
  · exact B517919
  · exact B517923
  · exact B517927
  · exact B517931
  · exact B517935
  · exact B517939
  · exact B517943
  · exact B517947
  · exact B517951
  · exact B517955
  · exact B517959
  · exact B517963
  · exact B517967
  · exact B517971
  · exact B517975
  · exact B517979
  · exact B517983
  · exact B517987
  · exact B517991
  · exact B517995
  · exact B517999
  · exact B518003
  · exact B518007
  · exact B518011
  · exact B518015
  · exact B518019
  · exact B518023
  · exact B518027
  · exact B518031
  · exact B518035
  · exact B518039
  · exact B518043
  · exact B518047
  · exact B518051
  · exact B518055
  · exact B518059
  · exact B518063
  · exact B518067
  · exact B518071
  · exact B518075
  · exact B518079
  · exact B518083
  · exact B518087
  · exact B518091
  · exact B518095
  · exact B518099
  · exact B518103
  · exact B518107
  · exact B518111
  · exact B518115
  · exact B518119
  · exact B518123
  · exact B518127
  · exact B518131
  · exact B518135
  · exact B518139
  · exact B518143
  · exact B518147
  · exact B518151
  · exact B518155
  · exact B518159
  · exact B518163
  · exact B518167
  · exact B518171
  · exact B518175
  · exact B518179
  · exact B518183
  · exact B518187
  · exact B518191
  · exact B518195
  · exact B518199
  · exact B518203
  · exact B518207
  · exact B518211
  · exact B518215
  · exact B518219
  · exact B518223
  · exact B518227
  · exact B518231
  · exact B518235
  · exact B518239
  · exact B518243
  · exact B518247
  · exact B518251
  · exact B518255
  · exact B518259
  · exact B518263
  · exact B518267
  · exact B518271
  · exact B518275
  · exact B518279
  · exact B518283
  · exact B518287
  · exact B518291
  · exact B518295
  · exact B518299
  · exact B518303
  · exact B518307
  · exact B518311
  · exact B518315
  · exact B518319
  · exact B518323
  · exact B518327
  · exact B518331
  · exact B518335
  · exact B518339
  · exact B518343
  · exact B518347
  · exact B518351
  · exact B518355
  · exact B518359
  · exact B518363
  · exact B518367
  · exact B518371
  · exact B518375
  · exact B518379
  · exact B518383
  · exact B518387
  · exact B518391
  · exact B518395
  · exact B518399
  · exact B518403
  · exact B518407
  · exact B518411
  · exact B518415
  · exact B518419
  · exact B518423
  · exact B518427
  · exact B518431
  · exact B518435
  · exact B518439
  · exact B518443
  · exact B518447
  · exact B518451
  · exact B518455
  · exact B518459
  · exact B518463
  · exact B518467
  · exact B518471
  · exact B518475
  · exact B518479
  · exact B518483
  · exact B518487
  · exact B518491
  · exact B518495
  · exact B518499
  · exact B518503
  · exact B518507
  · exact B518511
  · exact B518515
  · exact B518519
  · exact B518523
  · exact B518527
  · exact B518531
  · exact B518535
  · exact B518539
  · exact B518543
  · exact B518547
  · exact B518551
  · exact B518555
  · exact B518559
  · exact B518563
  · exact B518567
  · exact B518571
  · exact B518575
  · exact B518579
  · exact B518583
  · exact B518587
  · exact B518591
  · exact B518595

theorem C1 (j : ℕ) (h1 : 129649 ≤ j) (h2 : j ≤ 129948) : Blo 515797 (4 * j + 3) := by
  interval_cases j
  · exact B518599
  · exact B518603
  · exact B518607
  · exact B518611
  · exact B518615
  · exact B518619
  · exact B518623
  · exact B518627
  · exact B518631
  · exact B518635
  · exact B518639
  · exact B518643
  · exact B518647
  · exact B518651
  · exact B518655
  · exact B518659
  · exact B518663
  · exact B518667
  · exact B518671
  · exact B518675
  · exact B518679
  · exact B518683
  · exact B518687
  · exact B518691
  · exact B518695
  · exact B518699
  · exact B518703
  · exact B518707
  · exact B518711
  · exact B518715
  · exact B518719
  · exact B518723
  · exact B518727
  · exact B518731
  · exact B518735
  · exact B518739
  · exact B518743
  · exact B518747
  · exact B518751
  · exact B518755
  · exact B518759
  · exact B518763
  · exact B518767
  · exact B518771
  · exact B518775
  · exact B518779
  · exact B518783
  · exact B518787
  · exact B518791
  · exact B518795
  · exact B518799
  · exact B518803
  · exact B518807
  · exact B518811
  · exact B518815
  · exact B518819
  · exact B518823
  · exact B518827
  · exact B518831
  · exact B518835
  · exact B518839
  · exact B518843
  · exact B518847
  · exact B518851
  · exact B518855
  · exact B518859
  · exact B518863
  · exact B518867
  · exact B518871
  · exact B518875
  · exact B518879
  · exact B518883
  · exact B518887
  · exact B518891
  · exact B518895
  · exact B518899
  · exact B518903
  · exact B518907
  · exact B518911
  · exact B518915
  · exact B518919
  · exact B518923
  · exact B518927
  · exact B518931
  · exact B518935
  · exact B518939
  · exact B518943
  · exact B518947
  · exact B518951
  · exact B518955
  · exact B518959
  · exact B518963
  · exact B518967
  · exact B518971
  · exact B518975
  · exact B518979
  · exact B518983
  · exact B518987
  · exact B518991
  · exact B518995
  · exact B518999
  · exact B519003
  · exact B519007
  · exact B519011
  · exact B519015
  · exact B519019
  · exact B519023
  · exact B519027
  · exact B519031
  · exact B519035
  · exact B519039
  · exact B519043
  · exact B519047
  · exact B519051
  · exact B519055
  · exact B519059
  · exact B519063
  · exact B519067
  · exact B519071
  · exact B519075
  · exact B519079
  · exact B519083
  · exact B519087
  · exact B519091
  · exact B519095
  · exact B519099
  · exact B519103
  · exact B519107
  · exact B519111
  · exact B519115
  · exact B519119
  · exact B519123
  · exact B519127
  · exact B519131
  · exact B519135
  · exact B519139
  · exact B519143
  · exact B519147
  · exact B519151
  · exact B519155
  · exact B519159
  · exact B519163
  · exact B519167
  · exact B519171
  · exact B519175
  · exact B519179
  · exact B519183
  · exact B519187
  · exact B519191
  · exact B519195
  · exact B519199
  · exact B519203
  · exact B519207
  · exact B519211
  · exact B519215
  · exact B519219
  · exact B519223
  · exact B519227
  · exact B519231
  · exact B519235
  · exact B519239
  · exact B519243
  · exact B519247
  · exact B519251
  · exact B519255
  · exact B519259
  · exact B519263
  · exact B519267
  · exact B519271
  · exact B519275
  · exact B519279
  · exact B519283
  · exact B519287
  · exact B519291
  · exact B519295
  · exact B519299
  · exact B519303
  · exact B519307
  · exact B519311
  · exact B519315
  · exact B519319
  · exact B519323
  · exact B519327
  · exact B519331
  · exact B519335
  · exact B519339
  · exact B519343
  · exact B519347
  · exact B519351
  · exact B519355
  · exact B519359
  · exact B519363
  · exact B519367
  · exact B519371
  · exact B519375
  · exact B519379
  · exact B519383
  · exact B519387
  · exact B519391
  · exact B519395
  · exact B519399
  · exact B519403
  · exact B519407
  · exact B519411
  · exact B519415
  · exact B519419
  · exact B519423
  · exact B519427
  · exact B519431
  · exact B519435
  · exact B519439
  · exact B519443
  · exact B519447
  · exact B519451
  · exact B519455
  · exact B519459
  · exact B519463
  · exact B519467
  · exact B519471
  · exact B519475
  · exact B519479
  · exact B519483
  · exact B519487
  · exact B519491
  · exact B519495
  · exact B519499
  · exact B519503
  · exact B519507
  · exact B519511
  · exact B519515
  · exact B519519
  · exact B519523
  · exact B519527
  · exact B519531
  · exact B519535
  · exact B519539
  · exact B519543
  · exact B519547
  · exact B519551
  · exact B519555
  · exact B519559
  · exact B519563
  · exact B519567
  · exact B519571
  · exact B519575
  · exact B519579
  · exact B519583
  · exact B519587
  · exact B519591
  · exact B519595
  · exact B519599
  · exact B519603
  · exact B519607
  · exact B519611
  · exact B519615
  · exact B519619
  · exact B519623
  · exact B519627
  · exact B519631
  · exact B519635
  · exact B519639
  · exact B519643
  · exact B519647
  · exact B519651
  · exact B519655
  · exact B519659
  · exact B519663
  · exact B519667
  · exact B519671
  · exact B519675
  · exact B519679
  · exact B519683
  · exact B519687
  · exact B519691
  · exact B519695
  · exact B519699
  · exact B519703
  · exact B519707
  · exact B519711
  · exact B519715
  · exact B519719
  · exact B519723
  · exact B519727
  · exact B519731
  · exact B519735
  · exact B519739
  · exact B519743
  · exact B519747
  · exact B519751
  · exact B519755
  · exact B519759
  · exact B519763
  · exact B519767
  · exact B519771
  · exact B519775
  · exact B519779
  · exact B519783
  · exact B519787
  · exact B519791
  · exact B519795

theorem solution (m : ℕ) (hlo : 515797 ≤ m) (hhi : m ≤ 519797) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 128949 ≤ j := by omega
    have hj2 : j ≤ 129948 := by omega
    have hb : Blo 515797 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 129649 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
