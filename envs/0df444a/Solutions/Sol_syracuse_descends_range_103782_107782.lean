-- Prove2me | solution 1 for syracuse_descends_range_103782_107782
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:25.638366+00:00
-- url     : https://prove2.me/submissions/9b65223d-7a5e-46d8-938c-0600a809133f

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


theorem B131377 : Blo 103782 131377 := bbase (se 2 (by rfl) ⟨49266, by rfl⟩ : syracuseStep 131377 = 98533) (by norm_num)
theorem B360773 : Blo 103782 360773 := bbase (se 4 (by rfl) ⟨33822, by rfl⟩ : syracuseStep 360773 = 67645) (by norm_num)
theorem B131473 : Blo 103782 131473 := bbase (se 2 (by rfl) ⟨49302, by rfl⟩ : syracuseStep 131473 = 98605) (by norm_num)
theorem B164333 : Blo 103782 164333 := bbase (se 3 (by rfl) ⟨30812, by rfl⟩ : syracuseStep 164333 = 61625) (by norm_num)
theorem B197149 : Blo 103782 197149 := bbase (se 3 (by rfl) ⟨36965, by rfl⟩ : syracuseStep 197149 = 73931) (by norm_num)
theorem B131645 : Blo 103782 131645 := bbase (se 3 (by rfl) ⟨24683, by rfl⟩ : syracuseStep 131645 = 49367) (by norm_num)
theorem B131701 : Blo 103782 131701 := bbase (se 5 (by rfl) ⟨6173, by rfl⟩ : syracuseStep 131701 = 12347) (by norm_num)
theorem B230045 : Blo 103782 230045 := bbase (se 3 (by rfl) ⟨43133, by rfl⟩ : syracuseStep 230045 = 86267) (by norm_num)
theorem B197309 : Blo 103782 197309 := bbase (se 3 (by rfl) ⟨36995, by rfl⟩ : syracuseStep 197309 = 73991) (by norm_num)
theorem B131797 : Blo 103782 131797 := bbase (se 7 (by rfl) ⟨1544, by rfl⟩ : syracuseStep 131797 = 3089) (by norm_num)
theorem B262885 : Blo 103782 262885 := bbase (se 4 (by rfl) ⟨24645, by rfl⟩ : syracuseStep 262885 = 49291) (by norm_num)
theorem B361205 : Blo 103782 361205 := bbase (se 5 (by rfl) ⟨16931, by rfl⟩ : syracuseStep 361205 = 33863) (by norm_num)
theorem B197453 : Blo 103782 197453 := bbase (se 3 (by rfl) ⟨37022, by rfl⟩ : syracuseStep 197453 = 74045) (by norm_num)
theorem B262997 : Blo 103782 262997 := bbase (se 9 (by rfl) ⟨770, by rfl⟩ : syracuseStep 262997 = 1541) (by norm_num)
theorem B394085 : Blo 103782 394085 := bbase (se 4 (by rfl) ⟨36945, by rfl⟩ : syracuseStep 394085 = 73891) (by norm_num)
theorem B426869 : Blo 103782 426869 := bbase (se 5 (by rfl) ⟨20009, by rfl⟩ : syracuseStep 426869 = 40019) (by norm_num)
theorem B131969 : Blo 103782 131969 := bbase (se 2 (by rfl) ⟨49488, by rfl⟩ : syracuseStep 131969 = 98977) (by norm_num)
theorem B263093 : Blo 103782 263093 := bbase (se 5 (by rfl) ⟨12332, by rfl⟩ : syracuseStep 263093 = 24665) (by norm_num)
theorem B132025 : Blo 103782 132025 := bbase (se 2 (by rfl) ⟨49509, by rfl⟩ : syracuseStep 132025 = 99019) (by norm_num)
theorem B459749 : Blo 103782 459749 := bbase (se 4 (by rfl) ⟨43101, by rfl⟩ : syracuseStep 459749 = 86203) (by norm_num)
theorem B263189 : Blo 103782 263189 := bbase (se 6 (by rfl) ⟨6168, by rfl⟩ : syracuseStep 263189 = 12337) (by norm_num)
theorem B132121 : Blo 103782 132121 := bbase (se 2 (by rfl) ⟨49545, by rfl⟩ : syracuseStep 132121 = 99091) (by norm_num)
theorem B197741 : Blo 103782 197741 := bbase (se 3 (by rfl) ⟨37076, by rfl⟩ : syracuseStep 197741 = 74153) (by norm_num)
theorem B361637 : Blo 103782 361637 := bbase (se 4 (by rfl) ⟨33903, by rfl⟩ : syracuseStep 361637 = 67807) (by norm_num)
theorem B132293 : Blo 103782 132293 := bbase (se 4 (by rfl) ⟨12402, by rfl⟩ : syracuseStep 132293 = 24805) (by norm_num)
theorem B459989 : Blo 103782 459989 := bbase (se 7 (by rfl) ⟨5390, by rfl⟩ : syracuseStep 459989 = 10781) (by norm_num)
theorem B132349 : Blo 103782 132349 := bbase (se 3 (by rfl) ⟨24815, by rfl⟩ : syracuseStep 132349 = 49631) (by norm_num)
theorem B197893 : Blo 103782 197893 := bbase (se 4 (by rfl) ⟨18552, by rfl⟩ : syracuseStep 197893 = 37105) (by norm_num)
theorem B132445 : Blo 103782 132445 := bbase (se 3 (by rfl) ⟨24833, by rfl⟩ : syracuseStep 132445 = 49667) (by norm_num)
theorem B296293 : Blo 103782 296293 := bbase (se 4 (by rfl) ⟨27777, by rfl⟩ : syracuseStep 296293 = 55555) (by norm_num)
theorem B263533 : Blo 103782 263533 := bbase (se 3 (by rfl) ⟨49412, by rfl⟩ : syracuseStep 263533 = 98825) (by norm_num)
theorem B263645 : Blo 103782 263645 := bbase (se 3 (by rfl) ⟨49433, by rfl⟩ : syracuseStep 263645 = 98867) (by norm_num)
theorem B296453 : Blo 103782 296453 := bbase (se 4 (by rfl) ⟨27792, by rfl⟩ : syracuseStep 296453 = 55585) (by norm_num)
theorem B132617 : Blo 103782 132617 := bbase (se 2 (by rfl) ⟨49731, by rfl⟩ : syracuseStep 132617 = 99463) (by norm_num)
theorem B198197 : Blo 103782 198197 := bbase (se 5 (by rfl) ⟨9290, by rfl⟩ : syracuseStep 198197 = 18581) (by norm_num)
theorem B132673 : Blo 103782 132673 := bbase (se 2 (by rfl) ⟨49752, by rfl⟩ : syracuseStep 132673 = 99505) (by norm_num)
theorem B362069 : Blo 103782 362069 := bbase (se 8 (by rfl) ⟨2121, by rfl⟩ : syracuseStep 362069 = 4243) (by norm_num)
theorem B263837 : Blo 103782 263837 := bbase (se 3 (by rfl) ⟨49469, by rfl⟩ : syracuseStep 263837 = 98939) (by norm_num)
theorem B132769 : Blo 103782 132769 := bbase (se 2 (by rfl) ⟨49788, by rfl⟩ : syracuseStep 132769 = 99577) (by norm_num)
theorem B296693 : Blo 103782 296693 := bbase (se 5 (by rfl) ⟨13907, by rfl⟩ : syracuseStep 296693 = 27815) (by norm_num)
theorem B132941 : Blo 103782 132941 := bbase (se 3 (by rfl) ⟨24926, by rfl⟩ : syracuseStep 132941 = 49853) (by norm_num)
theorem B132997 : Blo 103782 132997 := bbase (se 4 (by rfl) ⟨12468, by rfl⟩ : syracuseStep 132997 = 24937) (by norm_num)
theorem B296885 : Blo 103782 296885 := bbase (se 5 (by rfl) ⟨13916, by rfl⟩ : syracuseStep 296885 = 27833) (by norm_num)
theorem B133093 : Blo 103782 133093 := bbase (se 4 (by rfl) ⟨12477, by rfl⟩ : syracuseStep 133093 = 24955) (by norm_num)
theorem B264173 : Blo 103782 264173 := bbase (se 3 (by rfl) ⟨49532, by rfl⟩ : syracuseStep 264173 = 99065) (by norm_num)
theorem B264181 : Blo 103782 264181 := bbase (se 5 (by rfl) ⟨12383, by rfl⟩ : syracuseStep 264181 = 24767) (by norm_num)
theorem B362501 : Blo 103782 362501 := bbase (se 4 (by rfl) ⟨33984, by rfl⟩ : syracuseStep 362501 = 67969) (by norm_num)
theorem B264293 : Blo 103782 264293 := bbase (se 4 (by rfl) ⟨24777, by rfl⟩ : syracuseStep 264293 = 49555) (by norm_num)
theorem B133265 : Blo 103782 133265 := bbase (se 2 (by rfl) ⟨49974, by rfl⟩ : syracuseStep 133265 = 99949) (by norm_num)
theorem B133321 : Blo 103782 133321 := bbase (se 2 (by rfl) ⟨49995, by rfl⟩ : syracuseStep 133321 = 99991) (by norm_num)
theorem B264485 : Blo 103782 264485 := bbase (se 4 (by rfl) ⟨24795, by rfl⟩ : syracuseStep 264485 = 49591) (by norm_num)
theorem B198949 : Blo 103782 198949 := bbase (se 4 (by rfl) ⟨18651, by rfl⟩ : syracuseStep 198949 = 37303) (by norm_num)
theorem B133417 : Blo 103782 133417 := bbase (se 2 (by rfl) ⟨50031, by rfl⟩ : syracuseStep 133417 = 100063) (by norm_num)
theorem B526661 : Blo 103782 526661 := bbase (se 4 (by rfl) ⟨49374, by rfl⟩ : syracuseStep 526661 = 98749) (by norm_num)
theorem B559445 : Blo 103782 559445 := bbase (se 10 (by rfl) ⟨819, by rfl⟩ : syracuseStep 559445 = 1639) (by norm_num)
theorem B199093 : Blo 103782 199093 := bbase (se 5 (by rfl) ⟨9332, by rfl⟩ : syracuseStep 199093 = 18665) (by norm_num)
theorem B362933 : Blo 103782 362933 := bbase (se 5 (by rfl) ⟨17012, by rfl⟩ : syracuseStep 362933 = 34025) (by norm_num)
theorem B133589 : Blo 103782 133589 := bbase (se 7 (by rfl) ⟨1565, by rfl⟩ : syracuseStep 133589 = 3131) (by norm_num)
theorem B133645 : Blo 103782 133645 := bbase (se 3 (by rfl) ⟨25058, by rfl⟩ : syracuseStep 133645 = 50117) (by norm_num)
theorem B232013 : Blo 103782 232013 := bbase (se 3 (by rfl) ⟨43502, by rfl⟩ : syracuseStep 232013 = 87005) (by norm_num)
theorem B199253 : Blo 103782 199253 := bbase (se 8 (by rfl) ⟨1167, by rfl⟩ : syracuseStep 199253 = 2335) (by norm_num)
theorem B133741 : Blo 103782 133741 := bbase (se 3 (by rfl) ⟨25076, by rfl⟩ : syracuseStep 133741 = 50153) (by norm_num)
theorem B264829 : Blo 103782 264829 := bbase (se 3 (by rfl) ⟨49655, by rfl⟩ : syracuseStep 264829 = 99311) (by norm_num)
theorem B199397 : Blo 103782 199397 := bbase (se 4 (by rfl) ⟨18693, by rfl⟩ : syracuseStep 199397 = 37387) (by norm_num)
theorem B264941 : Blo 103782 264941 := bbase (se 3 (by rfl) ⟨49676, by rfl⟩ : syracuseStep 264941 = 99353) (by norm_num)
theorem B133913 : Blo 103782 133913 := bbase (se 2 (by rfl) ⟨50217, by rfl⟩ : syracuseStep 133913 = 100435) (by norm_num)
theorem B133969 : Blo 103782 133969 := bbase (se 2 (by rfl) ⟨50238, by rfl⟩ : syracuseStep 133969 = 100477) (by norm_num)
theorem B363365 : Blo 103782 363365 := bbase (se 4 (by rfl) ⟨34065, by rfl⟩ : syracuseStep 363365 = 68131) (by norm_num)
theorem B297877 : Blo 103782 297877 := bbase (se 6 (by rfl) ⟨6981, by rfl⟩ : syracuseStep 297877 = 13963) (by norm_num)
theorem B396197 : Blo 103782 396197 := bbase (se 4 (by rfl) ⟨37143, by rfl⟩ : syracuseStep 396197 = 74287) (by norm_num)
theorem B265133 : Blo 103782 265133 := bbase (se 3 (by rfl) ⟨49712, by rfl⟩ : syracuseStep 265133 = 99425) (by norm_num)
theorem B134065 : Blo 103782 134065 := bbase (se 2 (by rfl) ⟨50274, by rfl⟩ : syracuseStep 134065 = 100549) (by norm_num)
theorem B330725 : Blo 103782 330725 := bbase (se 4 (by rfl) ⟨31005, by rfl⟩ : syracuseStep 330725 = 62011) (by norm_num)
theorem B199685 : Blo 103782 199685 := bbase (se 4 (by rfl) ⟨18720, by rfl⟩ : syracuseStep 199685 = 37441) (by norm_num)
theorem B1346645 : Blo 103782 1346645 := bbase (se 8 (by rfl) ⟨7890, by rfl⟩ : syracuseStep 1346645 = 15781) (by norm_num)
theorem B134237 : Blo 103782 134237 := bbase (se 3 (by rfl) ⟨25169, by rfl⟩ : syracuseStep 134237 = 50339) (by norm_num)
theorem B134293 : Blo 103782 134293 := bbase (se 6 (by rfl) ⟨3147, by rfl⟩ : syracuseStep 134293 = 6295) (by norm_num)
theorem B199837 : Blo 103782 199837 := bbase (se 3 (by rfl) ⟨37469, by rfl⟩ : syracuseStep 199837 = 74939) (by norm_num)
theorem B396485 : Blo 103782 396485 := bbase (se 4 (by rfl) ⟨37170, by rfl⟩ : syracuseStep 396485 = 74341) (by norm_num)
theorem B789749 : Blo 103782 789749 := bbase (se 5 (by rfl) ⟨37019, by rfl⟩ : syracuseStep 789749 = 74039) (by norm_num)
theorem B134389 : Blo 103782 134389 := bbase (se 5 (by rfl) ⟨6299, by rfl⟩ : syracuseStep 134389 = 12599) (by norm_num)
theorem B265477 : Blo 103782 265477 := bbase (se 4 (by rfl) ⟨24888, by rfl⟩ : syracuseStep 265477 = 49777) (by norm_num)
theorem B265589 : Blo 103782 265589 := bbase (se 5 (by rfl) ⟨12449, by rfl⟩ : syracuseStep 265589 = 24899) (by norm_num)
theorem B134561 : Blo 103782 134561 := bbase (se 2 (by rfl) ⟨50460, by rfl⟩ : syracuseStep 134561 = 100921) (by norm_num)
theorem B167357 : Blo 103782 167357 := bbase (se 3 (by rfl) ⟨31379, by rfl⟩ : syracuseStep 167357 = 62759) (by norm_num)
theorem B200141 : Blo 103782 200141 := bbase (se 3 (by rfl) ⟨37526, by rfl⟩ : syracuseStep 200141 = 75053) (by norm_num)
theorem B134617 : Blo 103782 134617 := bbase (se 2 (by rfl) ⟨50481, by rfl⟩ : syracuseStep 134617 = 100963) (by norm_num)
theorem B1379861 : Blo 103782 1379861 := bbase (se 6 (by rfl) ⟨32340, by rfl⟩ : syracuseStep 1379861 = 64681) (by norm_num)
theorem B265781 : Blo 103782 265781 := bbase (se 5 (by rfl) ⟨12458, by rfl⟩ : syracuseStep 265781 = 24917) (by norm_num)
theorem B134713 : Blo 103782 134713 := bbase (se 2 (by rfl) ⟨50517, by rfl⟩ : syracuseStep 134713 = 101035) (by norm_num)
theorem B527957 : Blo 103782 527957 := bbase (se 8 (by rfl) ⟨3093, by rfl⟩ : syracuseStep 527957 = 6187) (by norm_num)
theorem B134885 : Blo 103782 134885 := bbase (se 4 (by rfl) ⟨12645, by rfl⟩ : syracuseStep 134885 = 25291) (by norm_num)
theorem B134941 : Blo 103782 134941 := bbase (se 3 (by rfl) ⟨25301, by rfl⟩ : syracuseStep 134941 = 50603) (by norm_num)
theorem B135037 : Blo 103782 135037 := bbase (se 3 (by rfl) ⟨25319, by rfl⟩ : syracuseStep 135037 = 50639) (by norm_num)
theorem B266125 : Blo 103782 266125 := bbase (se 3 (by rfl) ⟨49898, by rfl⟩ : syracuseStep 266125 = 99797) (by norm_num)
theorem B298981 : Blo 103782 298981 := bbase (se 4 (by rfl) ⟨28029, by rfl⟩ : syracuseStep 298981 = 56059) (by norm_num)
theorem B266237 : Blo 103782 266237 := bbase (se 3 (by rfl) ⟨49919, by rfl⟩ : syracuseStep 266237 = 99839) (by norm_num)
theorem B757781 : Blo 103782 757781 := bbase (se 6 (by rfl) ⟨17760, by rfl⟩ : syracuseStep 757781 = 35521) (by norm_num)
theorem B135209 : Blo 103782 135209 := bbase (se 2 (by rfl) ⟨50703, by rfl⟩ : syracuseStep 135209 = 101407) (by norm_num)
theorem B233549 : Blo 103782 233549 := bbase (se 3 (by rfl) ⟨43790, by rfl⟩ : syracuseStep 233549 = 87581) (by norm_num)
theorem B135265 : Blo 103782 135265 := bbase (se 2 (by rfl) ⟨50724, by rfl⟩ : syracuseStep 135265 = 101449) (by norm_num)
theorem B233621 : Blo 103782 233621 := bbase (se 6 (by rfl) ⟨5475, by rfl⟩ : syracuseStep 233621 = 10951) (by norm_num)
theorem B266429 : Blo 103782 266429 := bbase (se 3 (by rfl) ⟨49955, by rfl⟩ : syracuseStep 266429 = 99911) (by norm_num)
theorem B200893 : Blo 103782 200893 := bbase (se 3 (by rfl) ⟨37667, by rfl⟩ : syracuseStep 200893 = 75335) (by norm_num)
theorem B135361 : Blo 103782 135361 := bbase (se 2 (by rfl) ⟨50760, by rfl⟩ : syracuseStep 135361 = 101521) (by norm_num)
theorem B233693 : Blo 103782 233693 := bbase (se 3 (by rfl) ⟨43817, by rfl⟩ : syracuseStep 233693 = 87635) (by norm_num)
theorem B200989 : Blo 103782 200989 := bbase (se 3 (by rfl) ⟨37685, by rfl⟩ : syracuseStep 200989 = 75371) (by norm_num)
theorem B233765 : Blo 103782 233765 := bbase (se 4 (by rfl) ⟨21915, by rfl⟩ : syracuseStep 233765 = 43831) (by norm_num)
theorem B758069 : Blo 103782 758069 := bbase (se 5 (by rfl) ⟨35534, by rfl⟩ : syracuseStep 758069 = 71069) (by norm_num)
theorem B201037 : Blo 103782 201037 := bbase (se 3 (by rfl) ⟨37694, by rfl⟩ : syracuseStep 201037 = 75389) (by norm_num)
theorem B397669 : Blo 103782 397669 := bbase (se 4 (by rfl) ⟨37281, by rfl⟩ : syracuseStep 397669 = 74563) (by norm_num)
theorem B168293 : Blo 103782 168293 := bbase (se 4 (by rfl) ⟨15777, by rfl⟩ : syracuseStep 168293 = 31555) (by norm_num)
theorem B233837 : Blo 103782 233837 := bbase (se 3 (by rfl) ⟨43844, by rfl⟩ : syracuseStep 233837 = 87689) (by norm_num)
theorem B135533 : Blo 103782 135533 := bbase (se 3 (by rfl) ⟨25412, by rfl⟩ : syracuseStep 135533 = 50825) (by norm_num)
theorem B135589 : Blo 103782 135589 := bbase (se 4 (by rfl) ⟨12711, by rfl⟩ : syracuseStep 135589 = 25423) (by norm_num)
theorem B233909 : Blo 103782 233909 := bbase (se 5 (by rfl) ⟨10964, by rfl⟩ : syracuseStep 233909 = 21929) (by norm_num)
theorem B201197 : Blo 103782 201197 := bbase (se 3 (by rfl) ⟨37724, by rfl⟩ : syracuseStep 201197 = 75449) (by norm_num)
theorem B233981 : Blo 103782 233981 := bbase (se 3 (by rfl) ⟨43871, by rfl⟩ : syracuseStep 233981 = 87743) (by norm_num)
theorem B135685 : Blo 103782 135685 := bbase (se 4 (by rfl) ⟨12720, by rfl⟩ : syracuseStep 135685 = 25441) (by norm_num)
theorem B266773 : Blo 103782 266773 := bbase (se 6 (by rfl) ⟨6252, by rfl⟩ : syracuseStep 266773 = 12505) (by norm_num)
theorem B234053 : Blo 103782 234053 := bbase (se 4 (by rfl) ⟨21942, by rfl⟩ : syracuseStep 234053 = 43885) (by norm_num)
theorem B201341 : Blo 103782 201341 := bbase (se 3 (by rfl) ⟨37751, by rfl⟩ : syracuseStep 201341 = 75503) (by norm_num)
theorem B266885 : Blo 103782 266885 := bbase (se 4 (by rfl) ⟨25020, by rfl⟩ : syracuseStep 266885 = 50041) (by norm_num)
theorem B234125 : Blo 103782 234125 := bbase (se 3 (by rfl) ⟨43898, by rfl⟩ : syracuseStep 234125 = 87797) (by norm_num)
theorem B397973 : Blo 103782 397973 := bbase (se 6 (by rfl) ⟨9327, by rfl⟩ : syracuseStep 397973 = 18655) (by norm_num)
theorem B135857 : Blo 103782 135857 := bbase (se 2 (by rfl) ⟨50946, by rfl⟩ : syracuseStep 135857 = 101893) (by norm_num)
theorem B234197 : Blo 103782 234197 := bbase (se 7 (by rfl) ⟨2744, by rfl⟩ : syracuseStep 234197 = 5489) (by norm_num)
theorem B135913 : Blo 103782 135913 := bbase (se 2 (by rfl) ⟨50967, by rfl⟩ : syracuseStep 135913 = 101935) (by norm_num)
theorem B1151765 : Blo 103782 1151765 := bbase (se 6 (by rfl) ⟨26994, by rfl⟩ : syracuseStep 1151765 = 53989) (by norm_num)
theorem B234269 : Blo 103782 234269 := bbase (se 3 (by rfl) ⟨43925, by rfl⟩ : syracuseStep 234269 = 87851) (by norm_num)
theorem B267077 : Blo 103782 267077 := bbase (se 4 (by rfl) ⟨25038, by rfl⟩ : syracuseStep 267077 = 50077) (by norm_num)
theorem B136009 : Blo 103782 136009 := bbase (se 2 (by rfl) ⟨51003, by rfl⟩ : syracuseStep 136009 = 102007) (by norm_num)
theorem B594773 : Blo 103782 594773 := bbase (se 9 (by rfl) ⟨1742, by rfl⟩ : syracuseStep 594773 = 3485) (by norm_num)
theorem B234341 : Blo 103782 234341 := bbase (se 4 (by rfl) ⟨21969, by rfl⟩ : syracuseStep 234341 = 43939) (by norm_num)
theorem B529253 : Blo 103782 529253 := bbase (se 4 (by rfl) ⟨49617, by rfl⟩ : syracuseStep 529253 = 99235) (by norm_num)
theorem B758645 : Blo 103782 758645 := bbase (se 5 (by rfl) ⟨35561, by rfl⟩ : syracuseStep 758645 = 71123) (by norm_num)
theorem B1217429 : Blo 103782 1217429 := bbase (se 6 (by rfl) ⟨28533, by rfl⟩ : syracuseStep 1217429 = 57067) (by norm_num)
theorem B201629 : Blo 103782 201629 := bbase (se 3 (by rfl) ⟨37805, by rfl⟩ : syracuseStep 201629 = 75611) (by norm_num)
theorem B234413 : Blo 103782 234413 := bbase (se 3 (by rfl) ⟨43952, by rfl⟩ : syracuseStep 234413 = 87905) (by norm_num)
theorem B168941 : Blo 103782 168941 := bbase (se 3 (by rfl) ⟨31676, by rfl⟩ : syracuseStep 168941 = 63353) (by norm_num)
theorem B234485 : Blo 103782 234485 := bbase (se 5 (by rfl) ⟨10991, by rfl⟩ : syracuseStep 234485 = 21983) (by norm_num)
theorem B136181 : Blo 103782 136181 := bbase (se 5 (by rfl) ⟨6383, by rfl⟩ : syracuseStep 136181 = 12767) (by norm_num)
theorem B136237 : Blo 103782 136237 := bbase (se 3 (by rfl) ⟨25544, by rfl⟩ : syracuseStep 136237 = 51089) (by norm_num)
theorem B201781 : Blo 103782 201781 := bbase (se 5 (by rfl) ⟨9458, by rfl⟩ : syracuseStep 201781 = 18917) (by norm_num)
theorem B234557 : Blo 103782 234557 := bbase (se 3 (by rfl) ⟨43979, by rfl⟩ : syracuseStep 234557 = 87959) (by norm_num)
theorem B332869 : Blo 103782 332869 := bbase (se 4 (by rfl) ⟨31206, by rfl⟩ : syracuseStep 332869 = 62413) (by norm_num)
theorem B889973 : Blo 103782 889973 := bbase (se 5 (by rfl) ⟨41717, by rfl⟩ : syracuseStep 889973 = 83435) (by norm_num)
theorem B234629 : Blo 103782 234629 := bbase (se 4 (by rfl) ⟨21996, by rfl⟩ : syracuseStep 234629 = 43993) (by norm_num)
theorem B136333 : Blo 103782 136333 := bbase (se 3 (by rfl) ⟨25562, by rfl⟩ : syracuseStep 136333 = 51125) (by norm_num)
theorem B267421 : Blo 103782 267421 := bbase (se 3 (by rfl) ⟨50141, by rfl⟩ : syracuseStep 267421 = 100283) (by norm_num)
theorem B234701 : Blo 103782 234701 := bbase (se 3 (by rfl) ⟨44006, by rfl⟩ : syracuseStep 234701 = 88013) (by norm_num)
theorem B267533 : Blo 103782 267533 := bbase (se 3 (by rfl) ⟨50162, by rfl⟩ : syracuseStep 267533 = 100325) (by norm_num)
theorem B234773 : Blo 103782 234773 := bbase (se 6 (by rfl) ⟨5502, by rfl⟩ : syracuseStep 234773 = 11005) (by norm_num)
theorem B234845 : Blo 103782 234845 := bbase (se 3 (by rfl) ⟨44033, by rfl⟩ : syracuseStep 234845 = 88067) (by norm_num)
theorem B202085 : Blo 103782 202085 := bbase (se 4 (by rfl) ⟨18945, by rfl⟩ : syracuseStep 202085 = 37891) (by norm_num)
theorem B234917 : Blo 103782 234917 := bbase (se 4 (by rfl) ⟨22023, by rfl⟩ : syracuseStep 234917 = 44047) (by norm_num)
theorem B300485 : Blo 103782 300485 := bbase (se 4 (by rfl) ⟨28170, by rfl⟩ : syracuseStep 300485 = 56341) (by norm_num)
theorem B267725 : Blo 103782 267725 := bbase (se 3 (by rfl) ⟨50198, by rfl⟩ : syracuseStep 267725 = 100397) (by norm_num)
theorem B234989 : Blo 103782 234989 := bbase (se 3 (by rfl) ⟨44060, by rfl⟩ : syracuseStep 234989 = 88121) (by norm_num)
theorem B235061 : Blo 103782 235061 := bbase (se 5 (by rfl) ⟨11018, by rfl⟩ : syracuseStep 235061 = 22037) (by norm_num)
theorem B235133 : Blo 103782 235133 := bbase (se 3 (by rfl) ⟨44087, by rfl⟩ : syracuseStep 235133 = 88175) (by norm_num)
theorem B136829 : Blo 103782 136829 := bbase (se 3 (by rfl) ⟨25655, by rfl⟩ : syracuseStep 136829 = 51311) (by norm_num)
theorem B235205 : Blo 103782 235205 := bbase (se 4 (by rfl) ⟨22050, by rfl⟩ : syracuseStep 235205 = 44101) (by norm_num)
theorem B235277 : Blo 103782 235277 := bbase (se 3 (by rfl) ⟨44114, by rfl⟩ : syracuseStep 235277 = 88229) (by norm_num)
theorem B268069 : Blo 103782 268069 := bbase (se 4 (by rfl) ⟨25131, by rfl⟩ : syracuseStep 268069 = 50263) (by norm_num)
theorem B235349 : Blo 103782 235349 := bbase (se 9 (by rfl) ⟨689, by rfl⟩ : syracuseStep 235349 = 1379) (by norm_num)
theorem B268181 : Blo 103782 268181 := bbase (se 6 (by rfl) ⟨6285, by rfl⟩ : syracuseStep 268181 = 12571) (by norm_num)
theorem B235421 : Blo 103782 235421 := bbase (se 3 (by rfl) ⟨44141, by rfl⟩ : syracuseStep 235421 = 88283) (by norm_num)
theorem B169933 : Blo 103782 169933 := bbase (se 3 (by rfl) ⟨31862, by rfl⟩ : syracuseStep 169933 = 63725) (by norm_num)
theorem B235493 : Blo 103782 235493 := bbase (se 4 (by rfl) ⟨22077, by rfl⟩ : syracuseStep 235493 = 44155) (by norm_num)
theorem B595957 : Blo 103782 595957 := bbase (se 5 (by rfl) ⟨27935, by rfl⟩ : syracuseStep 595957 = 55871) (by norm_num)
theorem B235565 : Blo 103782 235565 := bbase (se 3 (by rfl) ⟨44168, by rfl⟩ : syracuseStep 235565 = 88337) (by norm_num)
theorem B268373 : Blo 103782 268373 := bbase (se 8 (by rfl) ⟨1572, by rfl⟩ : syracuseStep 268373 = 3145) (by norm_num)
theorem B202837 : Blo 103782 202837 := bbase (se 8 (by rfl) ⟨1188, by rfl⟩ : syracuseStep 202837 = 2377) (by norm_num)
theorem B235637 : Blo 103782 235637 := bbase (se 5 (by rfl) ⟨11045, by rfl⟩ : syracuseStep 235637 = 22091) (by norm_num)
theorem B530549 : Blo 103782 530549 := bbase (se 5 (by rfl) ⟨24869, by rfl⟩ : syracuseStep 530549 = 49739) (by norm_num)
theorem B235709 : Blo 103782 235709 := bbase (se 3 (by rfl) ⟨44195, by rfl⟩ : syracuseStep 235709 = 88391) (by norm_num)
theorem B202981 : Blo 103782 202981 := bbase (se 4 (by rfl) ⟨19029, by rfl⟩ : syracuseStep 202981 = 38059) (by norm_num)
theorem B235781 : Blo 103782 235781 := bbase (se 4 (by rfl) ⟨22104, by rfl⟩ : syracuseStep 235781 = 44209) (by norm_num)
theorem B235853 : Blo 103782 235853 := bbase (se 3 (by rfl) ⟨44222, by rfl⟩ : syracuseStep 235853 = 88445) (by norm_num)
theorem B203141 : Blo 103782 203141 := bbase (se 4 (by rfl) ⟨19044, by rfl⟩ : syracuseStep 203141 = 38089) (by norm_num)
theorem B170381 : Blo 103782 170381 := bbase (se 3 (by rfl) ⟨31946, by rfl⟩ : syracuseStep 170381 = 63893) (by norm_num)
theorem B235925 : Blo 103782 235925 := bbase (se 6 (by rfl) ⟨5529, by rfl⟩ : syracuseStep 235925 = 11059) (by norm_num)
theorem B268717 : Blo 103782 268717 := bbase (se 3 (by rfl) ⟨50384, by rfl⟩ : syracuseStep 268717 = 100769) (by norm_num)
theorem B235997 : Blo 103782 235997 := bbase (se 3 (by rfl) ⟨44249, by rfl⟩ : syracuseStep 235997 = 88499) (by norm_num)
theorem B203285 : Blo 103782 203285 := bbase (se 6 (by rfl) ⟨4764, by rfl⟩ : syracuseStep 203285 = 9529) (by norm_num)
theorem B203293 : Blo 103782 203293 := bbase (se 3 (by rfl) ⟨38117, by rfl⟩ : syracuseStep 203293 = 76235) (by norm_num)
theorem B268829 : Blo 103782 268829 := bbase (se 3 (by rfl) ⟨50405, by rfl⟩ : syracuseStep 268829 = 100811) (by norm_num)
theorem B236069 : Blo 103782 236069 := bbase (se 4 (by rfl) ⟨22131, by rfl⟩ : syracuseStep 236069 = 44263) (by norm_num)
theorem B170581 : Blo 103782 170581 := bbase (se 8 (by rfl) ⟨999, by rfl⟩ : syracuseStep 170581 = 1999) (by norm_num)
theorem B236141 : Blo 103782 236141 := bbase (se 3 (by rfl) ⟨44276, by rfl⟩ : syracuseStep 236141 = 88553) (by norm_num)
theorem B236213 : Blo 103782 236213 := bbase (se 5 (by rfl) ⟨11072, by rfl⟩ : syracuseStep 236213 = 22145) (by norm_num)
theorem B432821 : Blo 103782 432821 := bbase (se 5 (by rfl) ⟨20288, by rfl⟩ : syracuseStep 432821 = 40577) (by norm_num)
theorem B400085 : Blo 103782 400085 := bbase (se 7 (by rfl) ⟨4688, by rfl⟩ : syracuseStep 400085 = 9377) (by norm_num)
theorem B269021 : Blo 103782 269021 := bbase (se 3 (by rfl) ⟨50441, by rfl⟩ : syracuseStep 269021 = 100883) (by norm_num)
theorem B236285 : Blo 103782 236285 := bbase (se 3 (by rfl) ⟨44303, by rfl⟩ : syracuseStep 236285 = 88607) (by norm_num)
theorem B203573 : Blo 103782 203573 := bbase (se 5 (by rfl) ⟨9542, by rfl⟩ : syracuseStep 203573 = 19085) (by norm_num)
theorem B236357 : Blo 103782 236357 := bbase (se 4 (by rfl) ⟨22158, by rfl⟩ : syracuseStep 236357 = 44317) (by norm_num)
theorem B170837 : Blo 103782 170837 := bbase (se 9 (by rfl) ⟨500, by rfl⟩ : syracuseStep 170837 = 1001) (by norm_num)
theorem B236429 : Blo 103782 236429 := bbase (se 3 (by rfl) ⟨44330, by rfl⟩ : syracuseStep 236429 = 88661) (by norm_num)
theorem B203725 : Blo 103782 203725 := bbase (se 3 (by rfl) ⟨38198, by rfl⟩ : syracuseStep 203725 = 76397) (by norm_num)
theorem B236501 : Blo 103782 236501 := bbase (se 7 (by rfl) ⟨2771, by rfl⟩ : syracuseStep 236501 = 5543) (by norm_num)
theorem B400373 : Blo 103782 400373 := bbase (se 5 (by rfl) ⟨18767, by rfl⟩ : syracuseStep 400373 = 37535) (by norm_num)
theorem B302069 : Blo 103782 302069 := bbase (se 5 (by rfl) ⟨14159, by rfl⟩ : syracuseStep 302069 = 28319) (by norm_num)
theorem B236573 : Blo 103782 236573 := bbase (se 3 (by rfl) ⟨44357, by rfl⟩ : syracuseStep 236573 = 88715) (by norm_num)
theorem B269365 : Blo 103782 269365 := bbase (se 5 (by rfl) ⟨12626, by rfl⟩ : syracuseStep 269365 = 25253) (by norm_num)
theorem B826453 : Blo 103782 826453 := bbase (se 8 (by rfl) ⟨4842, by rfl⟩ : syracuseStep 826453 = 9685) (by norm_num)
theorem B236645 : Blo 103782 236645 := bbase (se 4 (by rfl) ⟨22185, by rfl⟩ : syracuseStep 236645 = 44371) (by norm_num)
theorem B1055861 : Blo 103782 1055861 := bbase (se 5 (by rfl) ⟨49493, by rfl⟩ : syracuseStep 1055861 = 98987) (by norm_num)
theorem B236701 : Blo 103782 236701 := bbase (se 3 (by rfl) ⟨44381, by rfl⟩ : syracuseStep 236701 = 88763) (by norm_num)
theorem B269477 : Blo 103782 269477 := bbase (se 4 (by rfl) ⟨25263, by rfl⟩ : syracuseStep 269477 = 50527) (by norm_num)
theorem B236717 : Blo 103782 236717 := bbase (se 3 (by rfl) ⟨44384, by rfl⟩ : syracuseStep 236717 = 88769) (by norm_num)
theorem B204005 : Blo 103782 204005 := bbase (se 4 (by rfl) ⟨19125, by rfl⟩ : syracuseStep 204005 = 38251) (by norm_num)
theorem B236789 : Blo 103782 236789 := bbase (se 5 (by rfl) ⟨11099, by rfl⟩ : syracuseStep 236789 = 22199) (by norm_num)
theorem B204029 : Blo 103782 204029 := bbase (se 3 (by rfl) ⟨38255, by rfl⟩ : syracuseStep 204029 = 76511) (by norm_num)
theorem B236861 : Blo 103782 236861 := bbase (se 3 (by rfl) ⟨44411, by rfl⟩ : syracuseStep 236861 = 88823) (by norm_num)
theorem B269669 : Blo 103782 269669 := bbase (se 4 (by rfl) ⟨25281, by rfl⟩ : syracuseStep 269669 = 50563) (by norm_num)
theorem B531845 : Blo 103782 531845 := bbase (se 4 (by rfl) ⟨49860, by rfl⟩ : syracuseStep 531845 = 99721) (by norm_num)
theorem B236933 : Blo 103782 236933 := bbase (se 4 (by rfl) ⟨22212, by rfl⟩ : syracuseStep 236933 = 44425) (by norm_num)
theorem B237005 : Blo 103782 237005 := bbase (se 3 (by rfl) ⟨44438, by rfl⟩ : syracuseStep 237005 = 88877) (by norm_num)
theorem B237077 : Blo 103782 237077 := bbase (se 6 (by rfl) ⟨5556, by rfl⟩ : syracuseStep 237077 = 11113) (by norm_num)
theorem B237149 : Blo 103782 237149 := bbase (se 3 (by rfl) ⟨44465, by rfl⟩ : syracuseStep 237149 = 88931) (by norm_num)
theorem B302741 : Blo 103782 302741 := bbase (se 6 (by rfl) ⟨7095, by rfl⟩ : syracuseStep 302741 = 14191) (by norm_num)
theorem B237221 : Blo 103782 237221 := bbase (se 4 (by rfl) ⟨22239, by rfl⟩ : syracuseStep 237221 = 44479) (by norm_num)
theorem B270013 : Blo 103782 270013 := bbase (se 3 (by rfl) ⟨50627, by rfl⟩ : syracuseStep 270013 = 101255) (by norm_num)
theorem B237293 : Blo 103782 237293 := bbase (se 3 (by rfl) ⟨44492, by rfl⟩ : syracuseStep 237293 = 88985) (by norm_num)
theorem B270125 : Blo 103782 270125 := bbase (se 3 (by rfl) ⟨50648, by rfl⟩ : syracuseStep 270125 = 101297) (by norm_num)
theorem B237365 : Blo 103782 237365 := bbase (se 5 (by rfl) ⟨11126, by rfl⟩ : syracuseStep 237365 = 22253) (by norm_num)
theorem B237413 : Blo 103782 237413 := bbase (se 4 (by rfl) ⟨22257, by rfl⟩ : syracuseStep 237413 = 44515) (by norm_num)
theorem B237437 : Blo 103782 237437 := bbase (se 3 (by rfl) ⟨44519, by rfl⟩ : syracuseStep 237437 = 89039) (by norm_num)
theorem B434069 : Blo 103782 434069 := bbase (se 6 (by rfl) ⟨10173, by rfl⟩ : syracuseStep 434069 = 20347) (by norm_num)
theorem B335765 : Blo 103782 335765 := bbase (se 6 (by rfl) ⟨7869, by rfl⟩ : syracuseStep 335765 = 15739) (by norm_num)
theorem B597941 : Blo 103782 597941 := bbase (se 5 (by rfl) ⟨28028, by rfl⟩ : syracuseStep 597941 = 56057) (by norm_num)
theorem B171965 : Blo 103782 171965 := bbase (se 3 (by rfl) ⟨32243, by rfl⟩ : syracuseStep 171965 = 64487) (by norm_num)
theorem B237509 : Blo 103782 237509 := bbase (se 4 (by rfl) ⟨22266, by rfl⟩ : syracuseStep 237509 = 44533) (by norm_num)
theorem B270317 : Blo 103782 270317 := bbase (se 3 (by rfl) ⟨50684, by rfl⟩ : syracuseStep 270317 = 101369) (by norm_num)
theorem B237581 : Blo 103782 237581 := bbase (se 3 (by rfl) ⟨44546, by rfl⟩ : syracuseStep 237581 = 89093) (by norm_num)
theorem B303173 : Blo 103782 303173 := bbase (se 4 (by rfl) ⟨28422, by rfl⟩ : syracuseStep 303173 = 56845) (by norm_num)
theorem B237653 : Blo 103782 237653 := bbase (se 8 (by rfl) ⟨1392, by rfl⟩ : syracuseStep 237653 = 2785) (by norm_num)
theorem B401557 : Blo 103782 401557 := bbase (se 6 (by rfl) ⟨9411, by rfl⟩ : syracuseStep 401557 = 18823) (by norm_num)
theorem B237725 : Blo 103782 237725 := bbase (se 3 (by rfl) ⟨44573, by rfl⟩ : syracuseStep 237725 = 89147) (by norm_num)
theorem B237797 : Blo 103782 237797 := bbase (se 4 (by rfl) ⟨22293, by rfl⟩ : syracuseStep 237797 = 44587) (by norm_num)
theorem B237869 : Blo 103782 237869 := bbase (se 3 (by rfl) ⟨44600, by rfl⟩ : syracuseStep 237869 = 89201) (by norm_num)
theorem B270661 : Blo 103782 270661 := bbase (se 4 (by rfl) ⟨25374, by rfl⟩ : syracuseStep 270661 = 50749) (by norm_num)
theorem B237941 : Blo 103782 237941 := bbase (se 5 (by rfl) ⟨11153, by rfl⟩ : syracuseStep 237941 = 22307) (by norm_num)
theorem B270773 : Blo 103782 270773 := bbase (se 5 (by rfl) ⟨12692, by rfl⟩ : syracuseStep 270773 = 25385) (by norm_num)
theorem B238013 : Blo 103782 238013 := bbase (se 3 (by rfl) ⟨44627, by rfl⟩ : syracuseStep 238013 = 89255) (by norm_num)
theorem B172477 : Blo 103782 172477 := bbase (se 3 (by rfl) ⟨32339, by rfl⟩ : syracuseStep 172477 = 64679) (by norm_num)
theorem B401861 : Blo 103782 401861 := bbase (se 4 (by rfl) ⟨37674, by rfl⟩ : syracuseStep 401861 = 75349) (by norm_num)
theorem B238085 : Blo 103782 238085 := bbase (se 4 (by rfl) ⟨22320, by rfl⟩ : syracuseStep 238085 = 44641) (by norm_num)
theorem B238157 : Blo 103782 238157 := bbase (se 3 (by rfl) ⟨44654, by rfl⟩ : syracuseStep 238157 = 89309) (by norm_num)
theorem B270965 : Blo 103782 270965 := bbase (se 5 (by rfl) ⟨12701, by rfl⟩ : syracuseStep 270965 = 25403) (by norm_num)
theorem B533141 : Blo 103782 533141 := bbase (se 6 (by rfl) ⟨12495, by rfl⟩ : syracuseStep 533141 = 24991) (by norm_num)
theorem B238229 : Blo 103782 238229 := bbase (se 6 (by rfl) ⟨5583, by rfl⟩ : syracuseStep 238229 = 11167) (by norm_num)
theorem B238301 : Blo 103782 238301 := bbase (se 3 (by rfl) ⟨44681, by rfl⟩ : syracuseStep 238301 = 89363) (by norm_num)
theorem B238373 : Blo 103782 238373 := bbase (se 4 (by rfl) ⟨22347, by rfl⟩ : syracuseStep 238373 = 44695) (by norm_num)
theorem B303925 : Blo 103782 303925 := bbase (se 5 (by rfl) ⟨14246, by rfl⟩ : syracuseStep 303925 = 28493) (by norm_num)
theorem B238445 : Blo 103782 238445 := bbase (se 3 (by rfl) ⟨44708, by rfl⟩ : syracuseStep 238445 = 89417) (by norm_num)
theorem B238517 : Blo 103782 238517 := bbase (se 5 (by rfl) ⟨11180, by rfl⟩ : syracuseStep 238517 = 22361) (by norm_num)
theorem B271309 : Blo 103782 271309 := bbase (se 3 (by rfl) ⟨50870, by rfl⟩ : syracuseStep 271309 = 101741) (by norm_num)
theorem B238589 : Blo 103782 238589 := bbase (se 3 (by rfl) ⟨44735, by rfl⟩ : syracuseStep 238589 = 89471) (by norm_num)
theorem B205861 : Blo 103782 205861 := bbase (se 4 (by rfl) ⟨19299, by rfl⟩ : syracuseStep 205861 = 38599) (by norm_num)
theorem B271421 : Blo 103782 271421 := bbase (se 3 (by rfl) ⟨50891, by rfl⟩ : syracuseStep 271421 = 101783) (by norm_num)
theorem B238661 : Blo 103782 238661 := bbase (se 4 (by rfl) ⟨22374, by rfl⟩ : syracuseStep 238661 = 44749) (by norm_num)
theorem B238733 : Blo 103782 238733 := bbase (se 3 (by rfl) ⟨44762, by rfl⟩ : syracuseStep 238733 = 89525) (by norm_num)
theorem B337061 : Blo 103782 337061 := bbase (se 4 (by rfl) ⟨31599, by rfl⟩ : syracuseStep 337061 = 63199) (by norm_num)
theorem B238805 : Blo 103782 238805 := bbase (se 7 (by rfl) ⟨2798, by rfl⟩ : syracuseStep 238805 = 5597) (by norm_num)
theorem B271613 : Blo 103782 271613 := bbase (se 3 (by rfl) ⟨50927, by rfl⟩ : syracuseStep 271613 = 101855) (by norm_num)
theorem B238877 : Blo 103782 238877 := bbase (se 3 (by rfl) ⟨44789, by rfl⟩ : syracuseStep 238877 = 89579) (by norm_num)
theorem B2663765 : Blo 103782 2663765 := bbase (se 12 (by rfl) ⟨975, by rfl⟩ : syracuseStep 2663765 = 1951) (by norm_num)
theorem B238949 : Blo 103782 238949 := bbase (se 4 (by rfl) ⟨22401, by rfl⟩ : syracuseStep 238949 = 44803) (by norm_num)
theorem B239021 : Blo 103782 239021 := bbase (se 3 (by rfl) ⟨44816, by rfl⟩ : syracuseStep 239021 = 89633) (by norm_num)
theorem B2041301 : Blo 103782 2041301 := bbase (se 7 (by rfl) ⟨23921, by rfl⟩ : syracuseStep 2041301 = 47843) (by norm_num)
theorem B239093 : Blo 103782 239093 := bbase (se 5 (by rfl) ⟨11207, by rfl⟩ : syracuseStep 239093 = 22415) (by norm_num)
theorem B239165 : Blo 103782 239165 := bbase (se 3 (by rfl) ⟨44843, by rfl⟩ : syracuseStep 239165 = 89687) (by norm_num)
theorem B271957 : Blo 103782 271957 := bbase (se 8 (by rfl) ⟨1593, by rfl⟩ : syracuseStep 271957 = 3187) (by norm_num)
theorem B239237 : Blo 103782 239237 := bbase (se 4 (by rfl) ⟨22428, by rfl⟩ : syracuseStep 239237 = 44857) (by norm_num)
theorem B272069 : Blo 103782 272069 := bbase (se 4 (by rfl) ⟨25506, by rfl⟩ : syracuseStep 272069 = 51013) (by norm_num)
theorem B239309 : Blo 103782 239309 := bbase (se 3 (by rfl) ⟨44870, by rfl⟩ : syracuseStep 239309 = 89741) (by norm_num)
theorem B239381 : Blo 103782 239381 := bbase (se 6 (by rfl) ⟨5610, by rfl⟩ : syracuseStep 239381 = 11221) (by norm_num)
theorem B239453 : Blo 103782 239453 := bbase (se 3 (by rfl) ⟨44897, by rfl⟩ : syracuseStep 239453 = 89795) (by norm_num)
theorem B272261 : Blo 103782 272261 := bbase (se 4 (by rfl) ⟨25524, by rfl⟩ : syracuseStep 272261 = 51049) (by norm_num)
theorem B534437 : Blo 103782 534437 := bbase (se 4 (by rfl) ⟨50103, by rfl⟩ : syracuseStep 534437 = 100207) (by norm_num)
theorem B239525 : Blo 103782 239525 := bbase (se 4 (by rfl) ⟨22455, by rfl⟩ : syracuseStep 239525 = 44911) (by norm_num)
theorem B567253 : Blo 103782 567253 := bbase (se 7 (by rfl) ⟨6647, by rfl⟩ : syracuseStep 567253 = 13295) (by norm_num)
theorem B239597 : Blo 103782 239597 := bbase (se 3 (by rfl) ⟨44924, by rfl⟩ : syracuseStep 239597 = 89849) (by norm_num)
theorem B239669 : Blo 103782 239669 := bbase (se 5 (by rfl) ⟨11234, by rfl⟩ : syracuseStep 239669 = 22469) (by norm_num)
theorem B600149 : Blo 103782 600149 := bbase (se 8 (by rfl) ⟨3516, by rfl⟩ : syracuseStep 600149 = 7033) (by norm_num)
theorem B239741 : Blo 103782 239741 := bbase (se 3 (by rfl) ⟨44951, by rfl⟩ : syracuseStep 239741 = 89903) (by norm_num)
theorem B436373 : Blo 103782 436373 := bbase (se 6 (by rfl) ⟨10227, by rfl⟩ : syracuseStep 436373 = 20455) (by norm_num)
theorem B239813 : Blo 103782 239813 := bbase (se 4 (by rfl) ⟨22482, by rfl⟩ : syracuseStep 239813 = 44965) (by norm_num)
theorem B272605 : Blo 103782 272605 := bbase (se 3 (by rfl) ⟨51113, by rfl⟩ : syracuseStep 272605 = 102227) (by norm_num)
theorem B108793 : Blo 103782 108793 := bbase (se 2 (by rfl) ⟨40797, by rfl⟩ : syracuseStep 108793 = 81595) (by norm_num)
theorem B239885 : Blo 103782 239885 := bbase (se 3 (by rfl) ⟨44978, by rfl⟩ : syracuseStep 239885 = 89957) (by norm_num)
theorem B960821 : Blo 103782 960821 := bbase (se 5 (by rfl) ⟨45038, by rfl⟩ : syracuseStep 960821 = 90077) (by norm_num)
theorem B272717 : Blo 103782 272717 := bbase (se 3 (by rfl) ⟨51134, by rfl⟩ : syracuseStep 272717 = 102269) (by norm_num)
theorem B239957 : Blo 103782 239957 := bbase (se 10 (by rfl) ⟨351, by rfl⟩ : syracuseStep 239957 = 703) (by norm_num)
theorem B240029 : Blo 103782 240029 := bbase (se 3 (by rfl) ⟨45005, by rfl⟩ : syracuseStep 240029 = 90011) (by norm_num)
theorem B240101 : Blo 103782 240101 := bbase (se 4 (by rfl) ⟨22509, by rfl⟩ : syracuseStep 240101 = 45019) (by norm_num)
theorem B403973 : Blo 103782 403973 := bbase (se 4 (by rfl) ⟨37872, by rfl⟩ : syracuseStep 403973 = 75745) (by norm_num)
theorem B240173 : Blo 103782 240173 := bbase (se 3 (by rfl) ⟨45032, by rfl⟩ : syracuseStep 240173 = 90065) (by norm_num)
theorem B109117 : Blo 103782 109117 := bbase (se 3 (by rfl) ⟨20459, by rfl⟩ : syracuseStep 109117 = 40919) (by norm_num)
theorem B240245 : Blo 103782 240245 := bbase (se 5 (by rfl) ⟨11261, by rfl⟩ : syracuseStep 240245 = 22523) (by norm_num)
theorem B240317 : Blo 103782 240317 := bbase (se 3 (by rfl) ⟨45059, by rfl⟩ : syracuseStep 240317 = 90119) (by norm_num)
theorem B240389 : Blo 103782 240389 := bbase (se 4 (by rfl) ⟨22536, by rfl⟩ : syracuseStep 240389 = 45073) (by norm_num)
theorem B404261 : Blo 103782 404261 := bbase (se 4 (by rfl) ⟨37899, by rfl⟩ : syracuseStep 404261 = 75799) (by norm_num)
theorem B240461 : Blo 103782 240461 := bbase (se 3 (by rfl) ⟨45086, by rfl⟩ : syracuseStep 240461 = 90173) (by norm_num)
theorem B797525 : Blo 103782 797525 := bbase (se 9 (by rfl) ⟨2336, by rfl⟩ : syracuseStep 797525 = 4673) (by norm_num)
theorem B240533 : Blo 103782 240533 := bbase (se 6 (by rfl) ⟨5637, by rfl⟩ : syracuseStep 240533 = 11275) (by norm_num)
theorem B732053 : Blo 103782 732053 := bbase (se 6 (by rfl) ⟨17157, by rfl⟩ : syracuseStep 732053 = 34315) (by norm_num)
theorem B240605 : Blo 103782 240605 := bbase (se 3 (by rfl) ⟨45113, by rfl⟩ : syracuseStep 240605 = 90227) (by norm_num)
theorem B338917 : Blo 103782 338917 := bbase (se 4 (by rfl) ⟨31773, by rfl⟩ : syracuseStep 338917 = 63547) (by norm_num)
theorem B240677 : Blo 103782 240677 := bbase (se 4 (by rfl) ⟨22563, by rfl⟩ : syracuseStep 240677 = 45127) (by norm_num)
theorem B601141 : Blo 103782 601141 := bbase (se 5 (by rfl) ⟨28178, by rfl⟩ : syracuseStep 601141 = 56357) (by norm_num)
theorem B175189 : Blo 103782 175189 := bbase (se 8 (by rfl) ⟨1026, by rfl⟩ : syracuseStep 175189 = 2053) (by norm_num)
theorem B240749 : Blo 103782 240749 := bbase (se 3 (by rfl) ⟨45140, by rfl⟩ : syracuseStep 240749 = 90281) (by norm_num)
theorem B175277 : Blo 103782 175277 := bbase (se 3 (by rfl) ⟨32864, by rfl⟩ : syracuseStep 175277 = 65729) (by norm_num)
theorem B535733 : Blo 103782 535733 := bbase (se 5 (by rfl) ⟨25112, by rfl⟩ : syracuseStep 535733 = 50225) (by norm_num)
theorem B240821 : Blo 103782 240821 := bbase (se 5 (by rfl) ⟨11288, by rfl⟩ : syracuseStep 240821 = 22577) (by norm_num)
theorem B240893 : Blo 103782 240893 := bbase (se 3 (by rfl) ⟨45167, by rfl⟩ : syracuseStep 240893 = 90335) (by norm_num)
theorem B175405 : Blo 103782 175405 := bbase (se 3 (by rfl) ⟨32888, by rfl⟩ : syracuseStep 175405 = 65777) (by norm_num)
theorem B240965 : Blo 103782 240965 := bbase (se 4 (by rfl) ⟨22590, by rfl⟩ : syracuseStep 240965 = 45181) (by norm_num)
theorem B3026261 : Blo 103782 3026261 := bbase (se 11 (by rfl) ⟨2216, by rfl⟩ : syracuseStep 3026261 = 4433) (by norm_num)
theorem B175493 : Blo 103782 175493 := bbase (se 4 (by rfl) ⟨16452, by rfl⟩ : syracuseStep 175493 = 32905) (by norm_num)
theorem B241037 : Blo 103782 241037 := bbase (se 3 (by rfl) ⟨45194, by rfl⟩ : syracuseStep 241037 = 90389) (by norm_num)
theorem B241109 : Blo 103782 241109 := bbase (se 7 (by rfl) ⟨2825, by rfl⟩ : syracuseStep 241109 = 5651) (by norm_num)
theorem B175621 : Blo 103782 175621 := bbase (se 4 (by rfl) ⟨16464, by rfl⟩ : syracuseStep 175621 = 32929) (by norm_num)
theorem B241181 : Blo 103782 241181 := bbase (se 3 (by rfl) ⟨45221, by rfl⟩ : syracuseStep 241181 = 90443) (by norm_num)
theorem B142933 : Blo 103782 142933 := bbase (se 8 (by rfl) ⟨837, by rfl⟩ : syracuseStep 142933 = 1675) (by norm_num)
theorem B306773 : Blo 103782 306773 := bbase (se 8 (by rfl) ⟨1797, by rfl⟩ : syracuseStep 306773 = 3595) (by norm_num)
theorem B175709 : Blo 103782 175709 := bbase (se 3 (by rfl) ⟨32945, by rfl⟩ : syracuseStep 175709 = 65891) (by norm_num)
theorem B241253 : Blo 103782 241253 := bbase (se 4 (by rfl) ⟨22617, by rfl⟩ : syracuseStep 241253 = 45235) (by norm_num)
theorem B241325 : Blo 103782 241325 := bbase (se 3 (by rfl) ⟨45248, by rfl⟩ : syracuseStep 241325 = 90497) (by norm_num)
theorem B175837 : Blo 103782 175837 := bbase (se 3 (by rfl) ⟨32969, by rfl⟩ : syracuseStep 175837 = 65939) (by norm_num)
theorem B241373 : Blo 103782 241373 := bbase (se 3 (by rfl) ⟨45257, by rfl⟩ : syracuseStep 241373 = 90515) (by norm_num)
theorem B143077 : Blo 103782 143077 := bbase (se 4 (by rfl) ⟨13413, by rfl⟩ : syracuseStep 143077 = 26827) (by norm_num)
theorem B241397 : Blo 103782 241397 := bbase (se 5 (by rfl) ⟨11315, by rfl⟩ : syracuseStep 241397 = 22631) (by norm_num)
theorem B306965 : Blo 103782 306965 := bbase (se 6 (by rfl) ⟨7194, by rfl⟩ : syracuseStep 306965 = 14389) (by norm_num)
theorem B175925 : Blo 103782 175925 := bbase (se 5 (by rfl) ⟨8246, by rfl⟩ : syracuseStep 175925 = 16493) (by norm_num)
theorem B241469 : Blo 103782 241469 := bbase (se 3 (by rfl) ⟨45275, by rfl⟩ : syracuseStep 241469 = 90551) (by norm_num)
theorem B634709 : Blo 103782 634709 := bbase (se 9 (by rfl) ⟨1859, by rfl⟩ : syracuseStep 634709 = 3719) (by norm_num)
theorem B241541 : Blo 103782 241541 := bbase (se 4 (by rfl) ⟨22644, by rfl⟩ : syracuseStep 241541 = 45289) (by norm_num)
theorem B176053 : Blo 103782 176053 := bbase (se 5 (by rfl) ⟨8252, by rfl⟩ : syracuseStep 176053 = 16505) (by norm_num)
theorem B405445 : Blo 103782 405445 := bbase (se 4 (by rfl) ⟨38010, by rfl⟩ : syracuseStep 405445 = 76021) (by norm_num)
theorem B241613 : Blo 103782 241613 := bbase (se 3 (by rfl) ⟨45302, by rfl⟩ : syracuseStep 241613 = 90605) (by norm_num)
theorem B176141 : Blo 103782 176141 := bbase (se 3 (by rfl) ⟨33026, by rfl⟩ : syracuseStep 176141 = 66053) (by norm_num)
theorem B241685 : Blo 103782 241685 := bbase (se 6 (by rfl) ⟨5664, by rfl⟩ : syracuseStep 241685 = 11329) (by norm_num)
theorem B143413 : Blo 103782 143413 := bbase (se 5 (by rfl) ⟨6722, by rfl⟩ : syracuseStep 143413 = 13445) (by norm_num)
theorem B241757 : Blo 103782 241757 := bbase (se 3 (by rfl) ⟨45329, by rfl⟩ : syracuseStep 241757 = 90659) (by norm_num)
theorem B176269 : Blo 103782 176269 := bbase (se 3 (by rfl) ⟨33050, by rfl⟩ : syracuseStep 176269 = 66101) (by norm_num)
theorem B241829 : Blo 103782 241829 := bbase (se 4 (by rfl) ⟨22671, by rfl⟩ : syracuseStep 241829 = 45343) (by norm_num)
theorem B176357 : Blo 103782 176357 := bbase (se 4 (by rfl) ⟨16533, by rfl⟩ : syracuseStep 176357 = 33067) (by norm_num)
theorem B241901 : Blo 103782 241901 := bbase (se 3 (by rfl) ⟨45356, by rfl⟩ : syracuseStep 241901 = 90713) (by norm_num)
theorem B405749 : Blo 103782 405749 := bbase (se 5 (by rfl) ⟨19019, by rfl⟩ : syracuseStep 405749 = 38039) (by norm_num)
theorem B241973 : Blo 103782 241973 := bbase (se 5 (by rfl) ⟨11342, by rfl⟩ : syracuseStep 241973 = 22685) (by norm_num)
theorem B176485 : Blo 103782 176485 := bbase (se 4 (by rfl) ⟨16545, by rfl⟩ : syracuseStep 176485 = 33091) (by norm_num)
theorem B110965 : Blo 103782 110965 := bbase (se 5 (by rfl) ⟨5201, by rfl⟩ : syracuseStep 110965 = 10403) (by norm_num)
theorem B242045 : Blo 103782 242045 := bbase (se 3 (by rfl) ⟨45383, by rfl⟩ : syracuseStep 242045 = 90767) (by norm_num)
theorem B176573 : Blo 103782 176573 := bbase (se 3 (by rfl) ⟨33107, by rfl⟩ : syracuseStep 176573 = 66215) (by norm_num)
theorem B537029 : Blo 103782 537029 := bbase (se 4 (by rfl) ⟨50346, by rfl⟩ : syracuseStep 537029 = 100693) (by norm_num)
theorem B242117 : Blo 103782 242117 := bbase (se 4 (by rfl) ⟨22698, by rfl⟩ : syracuseStep 242117 = 45397) (by norm_num)
theorem B111089 : Blo 103782 111089 := bbase (se 2 (by rfl) ⟨41658, by rfl⟩ : syracuseStep 111089 = 83317) (by norm_num)
theorem B242189 : Blo 103782 242189 := bbase (se 3 (by rfl) ⟨45410, by rfl⟩ : syracuseStep 242189 = 90821) (by norm_num)
theorem B176701 : Blo 103782 176701 := bbase (se 3 (by rfl) ⟨33131, by rfl⟩ : syracuseStep 176701 = 66263) (by norm_num)
theorem B242261 : Blo 103782 242261 := bbase (se 8 (by rfl) ⟨1419, by rfl⟩ : syracuseStep 242261 = 2839) (by norm_num)
theorem B176789 : Blo 103782 176789 := bbase (se 6 (by rfl) ⟨4143, by rfl⟩ : syracuseStep 176789 = 8287) (by norm_num)
theorem B242333 : Blo 103782 242333 := bbase (se 3 (by rfl) ⟨45437, by rfl⟩ : syracuseStep 242333 = 90875) (by norm_num)
theorem B242405 : Blo 103782 242405 := bbase (se 4 (by rfl) ⟨22725, by rfl⟩ : syracuseStep 242405 = 45451) (by norm_num)
theorem B111341 : Blo 103782 111341 := bbase (se 3 (by rfl) ⟨20876, by rfl⟩ : syracuseStep 111341 = 41753) (by norm_num)
theorem B176917 : Blo 103782 176917 := bbase (se 6 (by rfl) ⟨4146, by rfl⟩ : syracuseStep 176917 = 8293) (by norm_num)
theorem B242477 : Blo 103782 242477 := bbase (se 3 (by rfl) ⟨45464, by rfl⟩ : syracuseStep 242477 = 90929) (by norm_num)
theorem B177005 : Blo 103782 177005 := bbase (se 3 (by rfl) ⟨33188, by rfl⟩ : syracuseStep 177005 = 66377) (by norm_num)
theorem B177133 : Blo 103782 177133 := bbase (se 3 (by rfl) ⟨33212, by rfl⟩ : syracuseStep 177133 = 66425) (by norm_num)
theorem B242669 : Blo 103782 242669 := bbase (se 3 (by rfl) ⟨45500, by rfl⟩ : syracuseStep 242669 = 91001) (by norm_num)
theorem B898037 : Blo 103782 898037 := bbase (se 5 (by rfl) ⟨42095, by rfl⟩ : syracuseStep 898037 = 84191) (by norm_num)
theorem B177221 : Blo 103782 177221 := bbase (se 4 (by rfl) ⟨16614, by rfl⟩ : syracuseStep 177221 = 33229) (by norm_num)
theorem B504917 : Blo 103782 504917 := bbase (se 8 (by rfl) ⟨2958, by rfl⟩ : syracuseStep 504917 = 5917) (by norm_num)
theorem B144493 : Blo 103782 144493 := bbase (se 3 (by rfl) ⟨27092, by rfl⟩ : syracuseStep 144493 = 54185) (by norm_num)
theorem B111785 : Blo 103782 111785 := bbase (se 2 (by rfl) ⟨41919, by rfl⟩ : syracuseStep 111785 = 83839) (by norm_num)
theorem B177349 : Blo 103782 177349 := bbase (se 4 (by rfl) ⟨16626, by rfl⟩ : syracuseStep 177349 = 33253) (by norm_num)
theorem B177437 : Blo 103782 177437 := bbase (se 3 (by rfl) ⟨33269, by rfl⟩ : syracuseStep 177437 = 66539) (by norm_num)
theorem B177565 : Blo 103782 177565 := bbase (se 3 (by rfl) ⟨33293, by rfl⟩ : syracuseStep 177565 = 66587) (by norm_num)
theorem B144797 : Blo 103782 144797 := bbase (se 3 (by rfl) ⟨27149, by rfl⟩ : syracuseStep 144797 = 54299) (by norm_num)
theorem B112033 : Blo 103782 112033 := bbase (se 2 (by rfl) ⟨42012, by rfl⟩ : syracuseStep 112033 = 84025) (by norm_num)
theorem B177653 : Blo 103782 177653 := bbase (se 5 (by rfl) ⟨8327, by rfl⟩ : syracuseStep 177653 = 16655) (by norm_num)
theorem B177781 : Blo 103782 177781 := bbase (se 5 (by rfl) ⟨8333, by rfl⟩ : syracuseStep 177781 = 16667) (by norm_num)
theorem B210613 : Blo 103782 210613 := bbase (se 5 (by rfl) ⟨9872, by rfl⟩ : syracuseStep 210613 = 19745) (by norm_num)
theorem B177869 : Blo 103782 177869 := bbase (se 3 (by rfl) ⟨33350, by rfl⟩ : syracuseStep 177869 = 66701) (by norm_num)
theorem B538325 : Blo 103782 538325 := bbase (se 7 (by rfl) ⟨6308, by rfl⟩ : syracuseStep 538325 = 12617) (by norm_num)
theorem B177965 : Blo 103782 177965 := bbase (se 3 (by rfl) ⟨33368, by rfl⟩ : syracuseStep 177965 = 66737) (by norm_num)
theorem B1029941 : Blo 103782 1029941 := bbase (se 5 (by rfl) ⟨48278, by rfl⟩ : syracuseStep 1029941 = 96557) (by norm_num)
theorem B177997 : Blo 103782 177997 := bbase (se 3 (by rfl) ⟨33374, by rfl⟩ : syracuseStep 177997 = 66749) (by norm_num)
theorem B112477 : Blo 103782 112477 := bbase (se 3 (by rfl) ⟨21089, by rfl⟩ : syracuseStep 112477 = 42179) (by norm_num)
theorem B112537 : Blo 103782 112537 := bbase (se 2 (by rfl) ⟨42201, by rfl⟩ : syracuseStep 112537 = 84403) (by norm_num)
theorem B178085 : Blo 103782 178085 := bbase (se 4 (by rfl) ⟨16695, by rfl⟩ : syracuseStep 178085 = 33391) (by norm_num)
theorem B178213 : Blo 103782 178213 := bbase (se 4 (by rfl) ⟨16707, by rfl⟩ : syracuseStep 178213 = 33415) (by norm_num)
theorem B178301 : Blo 103782 178301 := bbase (se 3 (by rfl) ⟨33431, by rfl⟩ : syracuseStep 178301 = 66863) (by norm_num)
theorem B112853 : Blo 103782 112853 := bbase (se 7 (by rfl) ⟨1322, by rfl⟩ : syracuseStep 112853 = 2645) (by norm_num)
theorem B669941 : Blo 103782 669941 := bbase (se 5 (by rfl) ⟨31403, by rfl⟩ : syracuseStep 669941 = 62807) (by norm_num)
theorem B178429 : Blo 103782 178429 := bbase (se 3 (by rfl) ⟨33455, by rfl⟩ : syracuseStep 178429 = 66911) (by norm_num)
theorem B112921 : Blo 103782 112921 := bbase (se 2 (by rfl) ⟨42345, by rfl⟩ : syracuseStep 112921 = 84691) (by norm_num)
theorem B637237 : Blo 103782 637237 := bbase (se 5 (by rfl) ⟨29870, by rfl⟩ : syracuseStep 637237 = 59741) (by norm_num)
theorem B407861 : Blo 103782 407861 := bbase (se 5 (by rfl) ⟨19118, by rfl⟩ : syracuseStep 407861 = 38237) (by norm_num)
theorem B178517 : Blo 103782 178517 := bbase (se 10 (by rfl) ⟨261, by rfl⟩ : syracuseStep 178517 = 523) (by norm_num)
theorem B178645 : Blo 103782 178645 := bbase (se 7 (by rfl) ⟨2093, by rfl⟩ : syracuseStep 178645 = 4187) (by norm_num)
theorem B178733 : Blo 103782 178733 := bbase (se 3 (by rfl) ⟨33512, by rfl⟩ : syracuseStep 178733 = 67025) (by norm_num)
theorem B408149 : Blo 103782 408149 := bbase (se 8 (by rfl) ⟨2391, by rfl⟩ : syracuseStep 408149 = 4783) (by norm_num)
theorem B113297 : Blo 103782 113297 := bbase (se 2 (by rfl) ⟨42486, by rfl⟩ : syracuseStep 113297 = 84973) (by norm_num)
theorem B178861 : Blo 103782 178861 := bbase (se 3 (by rfl) ⟨33536, by rfl⟩ : syracuseStep 178861 = 67073) (by norm_num)
theorem B113333 : Blo 103782 113333 := bbase (se 5 (by rfl) ⟨5312, by rfl⟩ : syracuseStep 113333 = 10625) (by norm_num)
theorem B244421 : Blo 103782 244421 := bbase (se 4 (by rfl) ⟨22914, by rfl⟩ : syracuseStep 244421 = 45829) (by norm_num)
theorem B113357 : Blo 103782 113357 := bbase (se 3 (by rfl) ⟨21254, by rfl⟩ : syracuseStep 113357 = 42509) (by norm_num)
theorem B178949 : Blo 103782 178949 := bbase (se 4 (by rfl) ⟨16776, by rfl⟩ : syracuseStep 178949 = 33553) (by norm_num)
theorem B310085 : Blo 103782 310085 := bbase (se 4 (by rfl) ⟨29070, by rfl⟩ : syracuseStep 310085 = 58141) (by norm_num)
theorem B113485 : Blo 103782 113485 := bbase (se 3 (by rfl) ⟨21278, by rfl⟩ : syracuseStep 113485 = 42557) (by norm_num)
theorem B211805 : Blo 103782 211805 := bbase (se 3 (by rfl) ⟨39713, by rfl⟩ : syracuseStep 211805 = 79427) (by norm_num)
theorem B179077 : Blo 103782 179077 := bbase (se 4 (by rfl) ⟨16788, by rfl⟩ : syracuseStep 179077 = 33577) (by norm_num)
theorem B179165 : Blo 103782 179165 := bbase (se 3 (by rfl) ⟨33593, by rfl⟩ : syracuseStep 179165 = 67187) (by norm_num)
theorem B539621 : Blo 103782 539621 := bbase (se 4 (by rfl) ⟨50589, by rfl⟩ : syracuseStep 539621 = 101179) (by norm_num)
theorem B113689 : Blo 103782 113689 := bbase (se 2 (by rfl) ⟨42633, by rfl⟩ : syracuseStep 113689 = 85267) (by norm_num)
theorem B343109 : Blo 103782 343109 := bbase (se 4 (by rfl) ⟨32166, by rfl⟩ : syracuseStep 343109 = 64333) (by norm_num)
theorem B179293 : Blo 103782 179293 := bbase (se 3 (by rfl) ⟨33617, by rfl⟩ : syracuseStep 179293 = 67235) (by norm_num)
theorem B474245 : Blo 103782 474245 := bbase (se 4 (by rfl) ⟨44460, by rfl⟩ : syracuseStep 474245 = 88921) (by norm_num)
theorem B179381 : Blo 103782 179381 := bbase (se 5 (by rfl) ⟨8408, by rfl⟩ : syracuseStep 179381 = 16817) (by norm_num)
theorem B113921 : Blo 103782 113921 := bbase (se 2 (by rfl) ⟨42720, by rfl⟩ : syracuseStep 113921 = 85441) (by norm_num)
theorem B113929 : Blo 103782 113929 := bbase (se 2 (by rfl) ⟨42723, by rfl⟩ : syracuseStep 113929 = 85447) (by norm_num)
theorem B179509 : Blo 103782 179509 := bbase (se 5 (by rfl) ⟨8414, by rfl⟩ : syracuseStep 179509 = 16829) (by norm_num)
theorem B114049 : Blo 103782 114049 := bbase (se 2 (by rfl) ⟨42768, by rfl⟩ : syracuseStep 114049 = 85537) (by norm_num)
theorem B179597 : Blo 103782 179597 := bbase (se 3 (by rfl) ⟨33674, by rfl⟩ : syracuseStep 179597 = 67349) (by norm_num)
theorem B245149 : Blo 103782 245149 := bbase (se 3 (by rfl) ⟨45965, by rfl⟩ : syracuseStep 245149 = 91931) (by norm_num)
theorem B376325 : Blo 103782 376325 := bbase (se 4 (by rfl) ⟨35280, by rfl⟩ : syracuseStep 376325 = 70561) (by norm_num)
theorem B179725 : Blo 103782 179725 := bbase (se 3 (by rfl) ⟨33698, by rfl⟩ : syracuseStep 179725 = 67397) (by norm_num)
theorem B179813 : Blo 103782 179813 := bbase (se 4 (by rfl) ⟨16857, by rfl⟩ : syracuseStep 179813 = 33715) (by norm_num)
theorem B114301 : Blo 103782 114301 := bbase (se 3 (by rfl) ⟨21431, by rfl⟩ : syracuseStep 114301 = 42863) (by norm_num)
theorem B114305 : Blo 103782 114305 := bbase (se 2 (by rfl) ⟨42864, by rfl⟩ : syracuseStep 114305 = 85729) (by norm_num)
theorem B245389 : Blo 103782 245389 := bbase (se 3 (by rfl) ⟨46010, by rfl⟩ : syracuseStep 245389 = 92021) (by norm_num)
theorem B179941 : Blo 103782 179941 := bbase (se 4 (by rfl) ⟨16869, by rfl⟩ : syracuseStep 179941 = 33739) (by norm_num)
theorem B376613 : Blo 103782 376613 := bbase (se 4 (by rfl) ⟨35307, by rfl⟩ : syracuseStep 376613 = 70615) (by norm_num)
theorem B180029 : Blo 103782 180029 := bbase (se 3 (by rfl) ⟨33755, by rfl⟩ : syracuseStep 180029 = 67511) (by norm_num)
theorem B180157 : Blo 103782 180157 := bbase (se 3 (by rfl) ⟨33779, by rfl⟩ : syracuseStep 180157 = 67559) (by norm_num)
theorem B180245 : Blo 103782 180245 := bbase (se 6 (by rfl) ⟨4224, by rfl⟩ : syracuseStep 180245 = 8449) (by norm_num)
theorem B180373 : Blo 103782 180373 := bbase (se 6 (by rfl) ⟨4227, by rfl⟩ : syracuseStep 180373 = 8455) (by norm_num)
theorem B114869 : Blo 103782 114869 := bbase (se 5 (by rfl) ⟨5384, by rfl⟩ : syracuseStep 114869 = 10769) (by norm_num)
theorem B377045 : Blo 103782 377045 := bbase (se 7 (by rfl) ⟨4418, by rfl⟩ : syracuseStep 377045 = 8837) (by norm_num)
theorem B180461 : Blo 103782 180461 := bbase (se 3 (by rfl) ⟨33836, by rfl⟩ : syracuseStep 180461 = 67673) (by norm_num)
theorem B540917 : Blo 103782 540917 := bbase (se 5 (by rfl) ⟨25355, by rfl⟩ : syracuseStep 540917 = 50711) (by norm_num)
theorem B1294613 : Blo 103782 1294613 := bbase (se 6 (by rfl) ⟨30342, by rfl⟩ : syracuseStep 1294613 = 60685) (by norm_num)
theorem B180589 : Blo 103782 180589 := bbase (se 3 (by rfl) ⟨33860, by rfl⟩ : syracuseStep 180589 = 67721) (by norm_num)
theorem B115057 : Blo 103782 115057 := bbase (se 2 (by rfl) ⟨43146, by rfl⟩ : syracuseStep 115057 = 86293) (by norm_num)
theorem B147845 : Blo 103782 147845 := bbase (se 4 (by rfl) ⟨13860, by rfl⟩ : syracuseStep 147845 = 27721) (by norm_num)
theorem B180677 : Blo 103782 180677 := bbase (se 4 (by rfl) ⟨16938, by rfl⟩ : syracuseStep 180677 = 33877) (by norm_num)
theorem B180805 : Blo 103782 180805 := bbase (se 4 (by rfl) ⟨16950, by rfl⟩ : syracuseStep 180805 = 33901) (by norm_num)
theorem B180893 : Blo 103782 180893 := bbase (se 3 (by rfl) ⟨33917, by rfl⟩ : syracuseStep 180893 = 67835) (by norm_num)
theorem B181021 : Blo 103782 181021 := bbase (se 3 (by rfl) ⟨33941, by rfl⟩ : syracuseStep 181021 = 67883) (by norm_num)
theorem B181109 : Blo 103782 181109 := bbase (se 5 (by rfl) ⟨8489, by rfl⟩ : syracuseStep 181109 = 16979) (by norm_num)
theorem B508837 : Blo 103782 508837 := bbase (se 4 (by rfl) ⟨47703, by rfl⟩ : syracuseStep 508837 = 95407) (by norm_num)
theorem B148397 : Blo 103782 148397 := bbase (se 3 (by rfl) ⟨27824, by rfl⟩ : syracuseStep 148397 = 55649) (by norm_num)
theorem B181237 : Blo 103782 181237 := bbase (se 5 (by rfl) ⟨8495, by rfl⟩ : syracuseStep 181237 = 16991) (by norm_num)
theorem B181325 : Blo 103782 181325 := bbase (se 3 (by rfl) ⟨33998, by rfl⟩ : syracuseStep 181325 = 67997) (by norm_num)
theorem B181453 : Blo 103782 181453 := bbase (se 3 (by rfl) ⟨34022, by rfl⟩ : syracuseStep 181453 = 68045) (by norm_num)
theorem B214309 : Blo 103782 214309 := bbase (se 4 (by rfl) ⟨20091, by rfl⟩ : syracuseStep 214309 = 40183) (by norm_num)
theorem B181541 : Blo 103782 181541 := bbase (se 4 (by rfl) ⟨17019, by rfl⟩ : syracuseStep 181541 = 34039) (by norm_num)
theorem B247157 : Blo 103782 247157 := bbase (se 5 (by rfl) ⟨11585, by rfl⟩ : syracuseStep 247157 = 23171) (by norm_num)
theorem B181645 : Blo 103782 181645 := bbase (se 3 (by rfl) ⟨34058, by rfl⟩ : syracuseStep 181645 = 68117) (by norm_num)
theorem B181669 : Blo 103782 181669 := bbase (se 4 (by rfl) ⟨17031, by rfl⟩ : syracuseStep 181669 = 34063) (by norm_num)
theorem B148933 : Blo 103782 148933 := bbase (se 4 (by rfl) ⟨13962, by rfl⟩ : syracuseStep 148933 = 27925) (by norm_num)
theorem B443893 : Blo 103782 443893 := bbase (se 5 (by rfl) ⟨20807, by rfl⟩ : syracuseStep 443893 = 41615) (by norm_num)
theorem B181757 : Blo 103782 181757 := bbase (se 3 (by rfl) ⟨34079, by rfl⟩ : syracuseStep 181757 = 68159) (by norm_num)
theorem B542213 : Blo 103782 542213 := bbase (se 4 (by rfl) ⟨50832, by rfl⟩ : syracuseStep 542213 = 101665) (by norm_num)
theorem B476725 : Blo 103782 476725 := bbase (se 5 (by rfl) ⟨22346, by rfl⟩ : syracuseStep 476725 = 44693) (by norm_num)
theorem B149149 : Blo 103782 149149 := bbase (se 3 (by rfl) ⟨27965, by rfl⟩ : syracuseStep 149149 = 55931) (by norm_num)
theorem B214829 : Blo 103782 214829 := bbase (se 3 (by rfl) ⟨40280, by rfl⟩ : syracuseStep 214829 = 80561) (by norm_num)
theorem B116761 : Blo 103782 116761 := bbase (se 2 (by rfl) ⟨43785, by rfl⟩ : syracuseStep 116761 = 87571) (by norm_num)
theorem B116797 : Blo 103782 116797 := bbase (se 3 (by rfl) ⟨21899, by rfl⟩ : syracuseStep 116797 = 43799) (by norm_num)
theorem B116833 : Blo 103782 116833 := bbase (se 2 (by rfl) ⟨43812, by rfl⟩ : syracuseStep 116833 = 87625) (by norm_num)
theorem B116869 : Blo 103782 116869 := bbase (se 4 (by rfl) ⟨10956, by rfl⟩ : syracuseStep 116869 = 21913) (by norm_num)
theorem B116885 : Blo 103782 116885 := bbase (se 6 (by rfl) ⟨2739, by rfl⟩ : syracuseStep 116885 = 5479) (by norm_num)
theorem B116905 : Blo 103782 116905 := bbase (se 2 (by rfl) ⟨43839, by rfl⟩ : syracuseStep 116905 = 87679) (by norm_num)
theorem B116941 : Blo 103782 116941 := bbase (se 3 (by rfl) ⟨21926, by rfl⟩ : syracuseStep 116941 = 43853) (by norm_num)
theorem B444629 : Blo 103782 444629 := bbase (se 7 (by rfl) ⟨5210, by rfl⟩ : syracuseStep 444629 = 10421) (by norm_num)
theorem B116977 : Blo 103782 116977 := bbase (se 2 (by rfl) ⟨43866, by rfl⟩ : syracuseStep 116977 = 87733) (by norm_num)
theorem B117013 : Blo 103782 117013 := bbase (se 6 (by rfl) ⟨2742, by rfl⟩ : syracuseStep 117013 = 5485) (by norm_num)
theorem B117049 : Blo 103782 117049 := bbase (se 2 (by rfl) ⟨43893, by rfl⟩ : syracuseStep 117049 = 87787) (by norm_num)
theorem B117085 : Blo 103782 117085 := bbase (se 3 (by rfl) ⟨21953, by rfl⟩ : syracuseStep 117085 = 43907) (by norm_num)
theorem B117121 : Blo 103782 117121 := bbase (se 2 (by rfl) ⟨43920, by rfl⟩ : syracuseStep 117121 = 87841) (by norm_num)
theorem B117157 : Blo 103782 117157 := bbase (se 4 (by rfl) ⟨10983, by rfl⟩ : syracuseStep 117157 = 21967) (by norm_num)
theorem B149941 : Blo 103782 149941 := bbase (se 5 (by rfl) ⟨7028, by rfl⟩ : syracuseStep 149941 = 14057) (by norm_num)
theorem B805301 : Blo 103782 805301 := bbase (se 5 (by rfl) ⟨37748, by rfl⟩ : syracuseStep 805301 = 75497) (by norm_num)
theorem B1100213 : Blo 103782 1100213 := bbase (se 5 (by rfl) ⟨51572, by rfl⟩ : syracuseStep 1100213 = 103145) (by norm_num)
theorem B117193 : Blo 103782 117193 := bbase (se 2 (by rfl) ⟨43947, by rfl⟩ : syracuseStep 117193 = 87895) (by norm_num)
theorem B117229 : Blo 103782 117229 := bbase (se 3 (by rfl) ⟨21980, by rfl⟩ : syracuseStep 117229 = 43961) (by norm_num)
theorem B117265 : Blo 103782 117265 := bbase (se 2 (by rfl) ⟨43974, by rfl⟩ : syracuseStep 117265 = 87949) (by norm_num)
theorem B117301 : Blo 103782 117301 := bbase (se 5 (by rfl) ⟨5498, by rfl⟩ : syracuseStep 117301 = 10997) (by norm_num)
theorem B117337 : Blo 103782 117337 := bbase (se 2 (by rfl) ⟨44001, by rfl⟩ : syracuseStep 117337 = 88003) (by norm_num)
theorem B117373 : Blo 103782 117373 := bbase (se 3 (by rfl) ⟨22007, by rfl⟩ : syracuseStep 117373 = 44015) (by norm_num)
theorem B117409 : Blo 103782 117409 := bbase (se 2 (by rfl) ⟨44028, by rfl⟩ : syracuseStep 117409 = 88057) (by norm_num)
theorem B117445 : Blo 103782 117445 := bbase (se 4 (by rfl) ⟨11010, by rfl⟩ : syracuseStep 117445 = 22021) (by norm_num)
theorem B117481 : Blo 103782 117481 := bbase (se 2 (by rfl) ⟨44055, by rfl⟩ : syracuseStep 117481 = 88111) (by norm_num)
theorem B150277 : Blo 103782 150277 := bbase (se 4 (by rfl) ⟨14088, by rfl⟩ : syracuseStep 150277 = 28177) (by norm_num)
theorem B117517 : Blo 103782 117517 := bbase (se 3 (by rfl) ⟨22034, by rfl⟩ : syracuseStep 117517 = 44069) (by norm_num)
theorem B543509 : Blo 103782 543509 := bbase (se 6 (by rfl) ⟨12738, by rfl⟩ : syracuseStep 543509 = 25477) (by norm_num)
theorem B117553 : Blo 103782 117553 := bbase (se 2 (by rfl) ⟨44082, by rfl⟩ : syracuseStep 117553 = 88165) (by norm_num)
theorem B117589 : Blo 103782 117589 := bbase (se 9 (by rfl) ⟨344, by rfl⟩ : syracuseStep 117589 = 689) (by norm_num)
theorem B117625 : Blo 103782 117625 := bbase (se 2 (by rfl) ⟨44109, by rfl⟩ : syracuseStep 117625 = 88219) (by norm_num)
theorem B117661 : Blo 103782 117661 := bbase (se 3 (by rfl) ⟨22061, by rfl⟩ : syracuseStep 117661 = 44123) (by norm_num)
theorem B117697 : Blo 103782 117697 := bbase (se 2 (by rfl) ⟨44136, by rfl⟩ : syracuseStep 117697 = 88273) (by norm_num)
theorem B150493 : Blo 103782 150493 := bbase (se 3 (by rfl) ⟨28217, by rfl⟩ : syracuseStep 150493 = 56435) (by norm_num)
theorem B281573 : Blo 103782 281573 := bbase (se 4 (by rfl) ⟨26397, by rfl⟩ : syracuseStep 281573 = 52795) (by norm_num)
theorem B117733 : Blo 103782 117733 := bbase (se 4 (by rfl) ⟨11037, by rfl⟩ : syracuseStep 117733 = 22075) (by norm_num)
theorem B117769 : Blo 103782 117769 := bbase (se 2 (by rfl) ⟨44163, by rfl⟩ : syracuseStep 117769 = 88327) (by norm_num)
theorem B117805 : Blo 103782 117805 := bbase (se 3 (by rfl) ⟨22088, by rfl⟩ : syracuseStep 117805 = 44177) (by norm_num)
theorem B773173 : Blo 103782 773173 := bbase (se 5 (by rfl) ⟨36242, by rfl⟩ : syracuseStep 773173 = 72485) (by norm_num)
theorem B117841 : Blo 103782 117841 := bbase (se 2 (by rfl) ⟨44190, by rfl⟩ : syracuseStep 117841 = 88381) (by norm_num)
theorem B117877 : Blo 103782 117877 := bbase (se 5 (by rfl) ⟨5525, by rfl⟩ : syracuseStep 117877 = 11051) (by norm_num)
theorem B117913 : Blo 103782 117913 := bbase (se 2 (by rfl) ⟨44217, by rfl⟩ : syracuseStep 117913 = 88435) (by norm_num)
theorem B117949 : Blo 103782 117949 := bbase (se 3 (by rfl) ⟨22115, by rfl⟩ : syracuseStep 117949 = 44231) (by norm_num)
theorem B117985 : Blo 103782 117985 := bbase (se 2 (by rfl) ⟨44244, by rfl⟩ : syracuseStep 117985 = 88489) (by norm_num)
theorem B118021 : Blo 103782 118021 := bbase (se 4 (by rfl) ⟨11064, by rfl⟩ : syracuseStep 118021 = 22129) (by norm_num)
theorem B118057 : Blo 103782 118057 := bbase (se 2 (by rfl) ⟨44271, by rfl⟩ : syracuseStep 118057 = 88543) (by norm_num)
theorem B118093 : Blo 103782 118093 := bbase (se 3 (by rfl) ⟨22142, by rfl⟩ : syracuseStep 118093 = 44285) (by norm_num)
theorem B150869 : Blo 103782 150869 := bbase (se 11 (by rfl) ⟨110, by rfl⟩ : syracuseStep 150869 = 221) (by norm_num)
theorem B118129 : Blo 103782 118129 := bbase (se 2 (by rfl) ⟨44298, by rfl⟩ : syracuseStep 118129 = 88597) (by norm_num)
theorem B118165 : Blo 103782 118165 := bbase (se 6 (by rfl) ⟨2769, by rfl⟩ : syracuseStep 118165 = 5539) (by norm_num)
theorem B118201 : Blo 103782 118201 := bbase (se 2 (by rfl) ⟨44325, by rfl⟩ : syracuseStep 118201 = 88651) (by norm_num)
theorem B118237 : Blo 103782 118237 := bbase (se 3 (by rfl) ⟨22169, by rfl⟩ : syracuseStep 118237 = 44339) (by norm_num)
theorem B118273 : Blo 103782 118273 := bbase (se 2 (by rfl) ⟨44352, by rfl⟩ : syracuseStep 118273 = 88705) (by norm_num)
theorem B118309 : Blo 103782 118309 := bbase (se 4 (by rfl) ⟨11091, by rfl⟩ : syracuseStep 118309 = 22183) (by norm_num)
theorem B151093 : Blo 103782 151093 := bbase (se 5 (by rfl) ⟨7082, by rfl⟩ : syracuseStep 151093 = 14165) (by norm_num)
theorem B118345 : Blo 103782 118345 := bbase (se 2 (by rfl) ⟨44379, by rfl⟩ : syracuseStep 118345 = 88759) (by norm_num)
theorem B249421 : Blo 103782 249421 := bbase (se 3 (by rfl) ⟨46766, by rfl⟩ : syracuseStep 249421 = 93533) (by norm_num)
theorem B216677 : Blo 103782 216677 := bbase (se 4 (by rfl) ⟨20313, by rfl⟩ : syracuseStep 216677 = 40627) (by norm_num)
theorem B118381 : Blo 103782 118381 := bbase (se 3 (by rfl) ⟨22196, by rfl⟩ : syracuseStep 118381 = 44393) (by norm_num)
theorem B380533 : Blo 103782 380533 := bbase (se 5 (by rfl) ⟨17837, by rfl⟩ : syracuseStep 380533 = 35675) (by norm_num)
theorem B118417 : Blo 103782 118417 := bbase (se 2 (by rfl) ⟨44406, by rfl⟩ : syracuseStep 118417 = 88813) (by norm_num)
theorem B118453 : Blo 103782 118453 := bbase (se 5 (by rfl) ⟨5552, by rfl⟩ : syracuseStep 118453 = 11105) (by norm_num)
theorem B118489 : Blo 103782 118489 := bbase (se 2 (by rfl) ⟨44433, by rfl⟩ : syracuseStep 118489 = 88867) (by norm_num)
theorem B610037 : Blo 103782 610037 := bbase (se 5 (by rfl) ⟨28595, by rfl⟩ : syracuseStep 610037 = 57191) (by norm_num)
theorem B118525 : Blo 103782 118525 := bbase (se 3 (by rfl) ⟨22223, by rfl⟩ : syracuseStep 118525 = 44447) (by norm_num)
theorem B380693 : Blo 103782 380693 := bbase (se 6 (by rfl) ⟨8922, by rfl⟩ : syracuseStep 380693 = 17845) (by norm_num)
theorem B118561 : Blo 103782 118561 := bbase (se 2 (by rfl) ⟨44460, by rfl⟩ : syracuseStep 118561 = 88921) (by norm_num)
theorem B118597 : Blo 103782 118597 := bbase (se 4 (by rfl) ⟨11118, by rfl⟩ : syracuseStep 118597 = 22237) (by norm_num)
theorem B118633 : Blo 103782 118633 := bbase (se 2 (by rfl) ⟨44487, by rfl⟩ : syracuseStep 118633 = 88975) (by norm_num)
theorem B118669 : Blo 103782 118669 := bbase (se 3 (by rfl) ⟨22250, by rfl⟩ : syracuseStep 118669 = 44501) (by norm_num)
theorem B380821 : Blo 103782 380821 := bbase (se 6 (by rfl) ⟨8925, by rfl⟩ : syracuseStep 380821 = 17851) (by norm_num)
theorem B282533 : Blo 103782 282533 := bbase (se 4 (by rfl) ⟨26487, by rfl⟩ : syracuseStep 282533 = 52975) (by norm_num)
theorem B118705 : Blo 103782 118705 := bbase (se 2 (by rfl) ⟨44514, by rfl⟩ : syracuseStep 118705 = 89029) (by norm_num)
theorem B249797 : Blo 103782 249797 := bbase (se 4 (by rfl) ⟨23418, by rfl⟩ : syracuseStep 249797 = 46837) (by norm_num)
theorem B118741 : Blo 103782 118741 := bbase (se 7 (by rfl) ⟨1391, by rfl⟩ : syracuseStep 118741 = 2783) (by norm_num)
theorem B118777 : Blo 103782 118777 := bbase (se 2 (by rfl) ⟨44541, by rfl⟩ : syracuseStep 118777 = 89083) (by norm_num)
theorem B118813 : Blo 103782 118813 := bbase (se 3 (by rfl) ⟨22277, by rfl⟩ : syracuseStep 118813 = 44555) (by norm_num)
theorem B544805 : Blo 103782 544805 := bbase (se 4 (by rfl) ⟨51075, by rfl⟩ : syracuseStep 544805 = 102151) (by norm_num)
theorem B118849 : Blo 103782 118849 := bbase (se 2 (by rfl) ⟨44568, by rfl⟩ : syracuseStep 118849 = 89137) (by norm_num)
theorem B1527893 : Blo 103782 1527893 := bbase (se 8 (by rfl) ⟨8952, by rfl⟩ : syracuseStep 1527893 = 17905) (by norm_num)
theorem B118885 : Blo 103782 118885 := bbase (se 4 (by rfl) ⟨11145, by rfl⟩ : syracuseStep 118885 = 22291) (by norm_num)
theorem B118921 : Blo 103782 118921 := bbase (se 2 (by rfl) ⟨44595, by rfl⟩ : syracuseStep 118921 = 89191) (by norm_num)
theorem B675989 : Blo 103782 675989 := bbase (se 6 (by rfl) ⟨15843, by rfl⟩ : syracuseStep 675989 = 31687) (by norm_num)
theorem B118957 : Blo 103782 118957 := bbase (se 3 (by rfl) ⟨22304, by rfl⟩ : syracuseStep 118957 = 44609) (by norm_num)
theorem B118993 : Blo 103782 118993 := bbase (se 2 (by rfl) ⟨44622, by rfl⟩ : syracuseStep 118993 = 89245) (by norm_num)
theorem B119029 : Blo 103782 119029 := bbase (se 5 (by rfl) ⟨5579, by rfl⟩ : syracuseStep 119029 = 11159) (by norm_num)
theorem B119065 : Blo 103782 119065 := bbase (se 2 (by rfl) ⟨44649, by rfl⟩ : syracuseStep 119065 = 89299) (by norm_num)
theorem B119101 : Blo 103782 119101 := bbase (se 3 (by rfl) ⟨22331, by rfl⟩ : syracuseStep 119101 = 44663) (by norm_num)
theorem B119137 : Blo 103782 119137 := bbase (se 2 (by rfl) ⟨44676, by rfl⟩ : syracuseStep 119137 = 89353) (by norm_num)
theorem B250229 : Blo 103782 250229 := bbase (se 5 (by rfl) ⟨11729, by rfl⟩ : syracuseStep 250229 = 23459) (by norm_num)
theorem B119173 : Blo 103782 119173 := bbase (se 4 (by rfl) ⟨11172, by rfl⟩ : syracuseStep 119173 = 22345) (by norm_num)
theorem B119209 : Blo 103782 119209 := bbase (se 2 (by rfl) ⟨44703, by rfl⟩ : syracuseStep 119209 = 89407) (by norm_num)
theorem B119245 : Blo 103782 119245 := bbase (se 3 (by rfl) ⟨22358, by rfl⟩ : syracuseStep 119245 = 44717) (by norm_num)
theorem B119281 : Blo 103782 119281 := bbase (se 2 (by rfl) ⟨44730, by rfl⟩ : syracuseStep 119281 = 89461) (by norm_num)
theorem B119317 : Blo 103782 119317 := bbase (se 6 (by rfl) ⟨2796, by rfl⟩ : syracuseStep 119317 = 5593) (by norm_num)
theorem B119353 : Blo 103782 119353 := bbase (se 2 (by rfl) ⟨44757, by rfl⟩ : syracuseStep 119353 = 89515) (by norm_num)
theorem B119389 : Blo 103782 119389 := bbase (se 3 (by rfl) ⟨22385, by rfl⟩ : syracuseStep 119389 = 44771) (by norm_num)
theorem B479861 : Blo 103782 479861 := bbase (se 5 (by rfl) ⟨22493, by rfl⟩ : syracuseStep 479861 = 44987) (by norm_num)
theorem B119425 : Blo 103782 119425 := bbase (se 2 (by rfl) ⟨44784, by rfl⟩ : syracuseStep 119425 = 89569) (by norm_num)
theorem B119461 : Blo 103782 119461 := bbase (se 4 (by rfl) ⟨11199, by rfl⟩ : syracuseStep 119461 = 22399) (by norm_num)
theorem B119497 : Blo 103782 119497 := bbase (se 2 (by rfl) ⟨44811, by rfl⟩ : syracuseStep 119497 = 89623) (by norm_num)
theorem B152293 : Blo 103782 152293 := bbase (se 4 (by rfl) ⟨14277, by rfl⟩ : syracuseStep 152293 = 28555) (by norm_num)
theorem B119533 : Blo 103782 119533 := bbase (se 3 (by rfl) ⟨22412, by rfl⟩ : syracuseStep 119533 = 44825) (by norm_num)
theorem B119569 : Blo 103782 119569 := bbase (se 2 (by rfl) ⟨44838, by rfl⟩ : syracuseStep 119569 = 89677) (by norm_num)
theorem B283445 : Blo 103782 283445 := bbase (se 5 (by rfl) ⟨13286, by rfl⟩ : syracuseStep 283445 = 26573) (by norm_num)
theorem B119605 : Blo 103782 119605 := bbase (se 5 (by rfl) ⟨5606, by rfl⟩ : syracuseStep 119605 = 11213) (by norm_num)
theorem B512837 : Blo 103782 512837 := bbase (se 4 (by rfl) ⟨48078, by rfl⟩ : syracuseStep 512837 = 96157) (by norm_num)
theorem B119641 : Blo 103782 119641 := bbase (se 2 (by rfl) ⟨44865, by rfl⟩ : syracuseStep 119641 = 89731) (by norm_num)
theorem B119677 : Blo 103782 119677 := bbase (se 3 (by rfl) ⟨22439, by rfl⟩ : syracuseStep 119677 = 44879) (by norm_num)
theorem B119713 : Blo 103782 119713 := bbase (se 2 (by rfl) ⟨44892, by rfl⟩ : syracuseStep 119713 = 89785) (by norm_num)
theorem B250805 : Blo 103782 250805 := bbase (se 5 (by rfl) ⟨11756, by rfl⟩ : syracuseStep 250805 = 23513) (by norm_num)
theorem B119749 : Blo 103782 119749 := bbase (se 4 (by rfl) ⟨11226, by rfl⟩ : syracuseStep 119749 = 22453) (by norm_num)
theorem B119785 : Blo 103782 119785 := bbase (se 2 (by rfl) ⟨44919, by rfl⟩ : syracuseStep 119785 = 89839) (by norm_num)
theorem B119821 : Blo 103782 119821 := bbase (se 3 (by rfl) ⟨22466, by rfl⟩ : syracuseStep 119821 = 44933) (by norm_num)
theorem B119857 : Blo 103782 119857 := bbase (se 2 (by rfl) ⟨44946, by rfl⟩ : syracuseStep 119857 = 89893) (by norm_num)
theorem B119893 : Blo 103782 119893 := bbase (se 8 (by rfl) ⟨702, by rfl⟩ : syracuseStep 119893 = 1405) (by norm_num)
theorem B513125 : Blo 103782 513125 := bbase (se 4 (by rfl) ⟨48105, by rfl⟩ : syracuseStep 513125 = 96211) (by norm_num)
theorem B119929 : Blo 103782 119929 := bbase (se 2 (by rfl) ⟨44973, by rfl⟩ : syracuseStep 119929 = 89947) (by norm_num)
theorem B119965 : Blo 103782 119965 := bbase (se 3 (by rfl) ⟨22493, by rfl⟩ : syracuseStep 119965 = 44987) (by norm_num)
theorem B120001 : Blo 103782 120001 := bbase (se 2 (by rfl) ⟨45000, by rfl⟩ : syracuseStep 120001 = 90001) (by norm_num)
theorem B1823957 : Blo 103782 1823957 := bbase (se 7 (by rfl) ⟨21374, by rfl⟩ : syracuseStep 1823957 = 42749) (by norm_num)
theorem B120037 : Blo 103782 120037 := bbase (se 4 (by rfl) ⟨11253, by rfl⟩ : syracuseStep 120037 = 22507) (by norm_num)
theorem B120073 : Blo 103782 120073 := bbase (se 2 (by rfl) ⟨45027, by rfl⟩ : syracuseStep 120073 = 90055) (by norm_num)
theorem B120109 : Blo 103782 120109 := bbase (se 3 (by rfl) ⟨22520, by rfl⟩ : syracuseStep 120109 = 45041) (by norm_num)
theorem B152885 : Blo 103782 152885 := bbase (se 5 (by rfl) ⟨7166, by rfl⟩ : syracuseStep 152885 = 14333) (by norm_num)
theorem B120145 : Blo 103782 120145 := bbase (se 2 (by rfl) ⟨45054, by rfl⟩ : syracuseStep 120145 = 90109) (by norm_num)
theorem B218461 : Blo 103782 218461 := bbase (se 3 (by rfl) ⟨40961, by rfl⟩ : syracuseStep 218461 = 81923) (by norm_num)
theorem B120181 : Blo 103782 120181 := bbase (se 5 (by rfl) ⟨5633, by rfl⟩ : syracuseStep 120181 = 11267) (by norm_num)
theorem B152965 : Blo 103782 152965 := bbase (se 4 (by rfl) ⟨14340, by rfl⟩ : syracuseStep 152965 = 28681) (by norm_num)
theorem B120217 : Blo 103782 120217 := bbase (se 2 (by rfl) ⟨45081, by rfl⟩ : syracuseStep 120217 = 90163) (by norm_num)
theorem B447925 : Blo 103782 447925 := bbase (se 5 (by rfl) ⟨20996, by rfl⟩ : syracuseStep 447925 = 41993) (by norm_num)
theorem B120253 : Blo 103782 120253 := bbase (se 3 (by rfl) ⟨22547, by rfl⟩ : syracuseStep 120253 = 45095) (by norm_num)
theorem B120289 : Blo 103782 120289 := bbase (se 2 (by rfl) ⟨45108, by rfl⟩ : syracuseStep 120289 = 90217) (by norm_num)
theorem B153085 : Blo 103782 153085 := bbase (se 3 (by rfl) ⟨28703, by rfl⟩ : syracuseStep 153085 = 57407) (by norm_num)
theorem B120325 : Blo 103782 120325 := bbase (se 4 (by rfl) ⟨11280, by rfl⟩ : syracuseStep 120325 = 22561) (by norm_num)
theorem B120361 : Blo 103782 120361 := bbase (se 2 (by rfl) ⟨45135, by rfl⟩ : syracuseStep 120361 = 90271) (by norm_num)
theorem B874037 : Blo 103782 874037 := bbase (se 5 (by rfl) ⟨40970, by rfl⟩ : syracuseStep 874037 = 81941) (by norm_num)
theorem B120397 : Blo 103782 120397 := bbase (se 3 (by rfl) ⟨22574, by rfl⟩ : syracuseStep 120397 = 45149) (by norm_num)
theorem B153181 : Blo 103782 153181 := bbase (se 3 (by rfl) ⟨28721, by rfl⟩ : syracuseStep 153181 = 57443) (by norm_num)
theorem B120433 : Blo 103782 120433 := bbase (se 2 (by rfl) ⟨45162, by rfl⟩ : syracuseStep 120433 = 90325) (by norm_num)
theorem B120469 : Blo 103782 120469 := bbase (se 6 (by rfl) ⟨2823, by rfl⟩ : syracuseStep 120469 = 5647) (by norm_num)
theorem B120505 : Blo 103782 120505 := bbase (se 2 (by rfl) ⟨45189, by rfl⟩ : syracuseStep 120505 = 90379) (by norm_num)
theorem B120541 : Blo 103782 120541 := bbase (se 3 (by rfl) ⟨22601, by rfl⟩ : syracuseStep 120541 = 45203) (by norm_num)
theorem B120577 : Blo 103782 120577 := bbase (se 2 (by rfl) ⟨45216, by rfl⟩ : syracuseStep 120577 = 90433) (by norm_num)
theorem B120613 : Blo 103782 120613 := bbase (se 4 (by rfl) ⟨11307, by rfl⟩ : syracuseStep 120613 = 22615) (by norm_num)
theorem B120649 : Blo 103782 120649 := bbase (se 2 (by rfl) ⟨45243, by rfl⟩ : syracuseStep 120649 = 90487) (by norm_num)
theorem B120685 : Blo 103782 120685 := bbase (se 3 (by rfl) ⟨22628, by rfl⟩ : syracuseStep 120685 = 45257) (by norm_num)
theorem B120721 : Blo 103782 120721 := bbase (se 2 (by rfl) ⟨45270, by rfl⟩ : syracuseStep 120721 = 90541) (by norm_num)
theorem B120757 : Blo 103782 120757 := bbase (se 5 (by rfl) ⟨5660, by rfl⟩ : syracuseStep 120757 = 11321) (by norm_num)
theorem B120793 : Blo 103782 120793 := bbase (se 2 (by rfl) ⟨45297, by rfl⟩ : syracuseStep 120793 = 90595) (by norm_num)
theorem B120829 : Blo 103782 120829 := bbase (se 3 (by rfl) ⟨22655, by rfl⟩ : syracuseStep 120829 = 45311) (by norm_num)
theorem B120865 : Blo 103782 120865 := bbase (se 2 (by rfl) ⟨45324, by rfl⟩ : syracuseStep 120865 = 90649) (by norm_num)
theorem B120901 : Blo 103782 120901 := bbase (se 4 (by rfl) ⟨11334, by rfl⟩ : syracuseStep 120901 = 22669) (by norm_num)
theorem B120937 : Blo 103782 120937 := bbase (se 2 (by rfl) ⟨45351, by rfl⟩ : syracuseStep 120937 = 90703) (by norm_num)
theorem B252029 : Blo 103782 252029 := bbase (se 3 (by rfl) ⟨47255, by rfl⟩ : syracuseStep 252029 = 94511) (by norm_num)
theorem B120973 : Blo 103782 120973 := bbase (se 3 (by rfl) ⟨22682, by rfl⟩ : syracuseStep 120973 = 45365) (by norm_num)
theorem B121009 : Blo 103782 121009 := bbase (se 2 (by rfl) ⟨45378, by rfl⟩ : syracuseStep 121009 = 90757) (by norm_num)
theorem B350405 : Blo 103782 350405 := bbase (se 4 (by rfl) ⟨32850, by rfl⟩ : syracuseStep 350405 = 65701) (by norm_num)
theorem B121045 : Blo 103782 121045 := bbase (se 7 (by rfl) ⟨1418, by rfl⟩ : syracuseStep 121045 = 2837) (by norm_num)
theorem B1038581 : Blo 103782 1038581 := bbase (se 5 (by rfl) ⟨48683, by rfl⟩ : syracuseStep 1038581 = 97367) (by norm_num)
theorem B121081 : Blo 103782 121081 := bbase (se 2 (by rfl) ⟨45405, by rfl⟩ : syracuseStep 121081 = 90811) (by norm_num)
theorem B1497365 : Blo 103782 1497365 := bbase (se 6 (by rfl) ⟨35094, by rfl⟩ : syracuseStep 1497365 = 70189) (by norm_num)
theorem B121117 : Blo 103782 121117 := bbase (se 3 (by rfl) ⟨22709, by rfl⟩ : syracuseStep 121117 = 45419) (by norm_num)
theorem B121153 : Blo 103782 121153 := bbase (se 2 (by rfl) ⟨45432, by rfl⟩ : syracuseStep 121153 = 90865) (by norm_num)
theorem B121189 : Blo 103782 121189 := bbase (se 4 (by rfl) ⟨11361, by rfl⟩ : syracuseStep 121189 = 22723) (by norm_num)
theorem B121225 : Blo 103782 121225 := bbase (se 2 (by rfl) ⟨45459, by rfl⟩ : syracuseStep 121225 = 90919) (by norm_num)
theorem B350837 : Blo 103782 350837 := bbase (se 5 (by rfl) ⟨16445, by rfl⟩ : syracuseStep 350837 = 32891) (by norm_num)
theorem B121549 : Blo 103782 121549 := bbase (se 3 (by rfl) ⟨22790, by rfl⟩ : syracuseStep 121549 = 45581) (by norm_num)
theorem B351269 : Blo 103782 351269 := bbase (se 4 (by rfl) ⟨32931, by rfl⟩ : syracuseStep 351269 = 65863) (by norm_num)
theorem B613493 : Blo 103782 613493 := bbase (se 5 (by rfl) ⟨28757, by rfl⟩ : syracuseStep 613493 = 57515) (by norm_num)
theorem B253381 : Blo 103782 253381 := bbase (se 4 (by rfl) ⟨23754, by rfl⟩ : syracuseStep 253381 = 47509) (by norm_num)
theorem B351701 : Blo 103782 351701 := bbase (se 7 (by rfl) ⟨4121, by rfl⟩ : syracuseStep 351701 = 8243) (by norm_num)
theorem B286213 : Blo 103782 286213 := bbase (se 4 (by rfl) ⟨26832, by rfl⟩ : syracuseStep 286213 = 53665) (by norm_num)
theorem B1367765 : Blo 103782 1367765 := bbase (se 7 (by rfl) ⟨16028, by rfl⟩ : syracuseStep 1367765 = 32057) (by norm_num)
theorem B352133 : Blo 103782 352133 := bbase (se 4 (by rfl) ⟨33012, by rfl⟩ : syracuseStep 352133 = 66025) (by norm_num)
theorem B155693 : Blo 103782 155693 := bbase (se 3 (by rfl) ⟨29192, by rfl⟩ : syracuseStep 155693 = 58385) (by norm_num)
theorem B155717 : Blo 103782 155717 := bbase (se 4 (by rfl) ⟨14598, by rfl⟩ : syracuseStep 155717 = 29197) (by norm_num)
theorem B680021 : Blo 103782 680021 := bbase (se 8 (by rfl) ⟨3984, by rfl⟩ : syracuseStep 680021 = 7969) (by norm_num)
theorem B155741 : Blo 103782 155741 := bbase (se 3 (by rfl) ⟨29201, by rfl⟩ : syracuseStep 155741 = 58403) (by norm_num)
theorem B155765 : Blo 103782 155765 := bbase (se 5 (by rfl) ⟨7301, by rfl⟩ : syracuseStep 155765 = 14603) (by norm_num)
theorem B155789 : Blo 103782 155789 := bbase (se 3 (by rfl) ⟨29210, by rfl⟩ : syracuseStep 155789 = 58421) (by norm_num)
theorem B155813 : Blo 103782 155813 := bbase (se 4 (by rfl) ⟨14607, by rfl⟩ : syracuseStep 155813 = 29215) (by norm_num)
theorem B155837 : Blo 103782 155837 := bbase (se 3 (by rfl) ⟨29219, by rfl⟩ : syracuseStep 155837 = 58439) (by norm_num)
theorem B155861 : Blo 103782 155861 := bbase (se 7 (by rfl) ⟨1826, by rfl⟩ : syracuseStep 155861 = 3653) (by norm_num)
theorem B155885 : Blo 103782 155885 := bbase (se 3 (by rfl) ⟨29228, by rfl⟩ : syracuseStep 155885 = 58457) (by norm_num)
theorem B155909 : Blo 103782 155909 := bbase (se 4 (by rfl) ⟨14616, by rfl⟩ : syracuseStep 155909 = 29233) (by norm_num)
theorem B155933 : Blo 103782 155933 := bbase (se 3 (by rfl) ⟨29237, by rfl⟩ : syracuseStep 155933 = 58475) (by norm_num)
theorem B155957 : Blo 103782 155957 := bbase (se 5 (by rfl) ⟨7310, by rfl⟩ : syracuseStep 155957 = 14621) (by norm_num)
theorem B352565 : Blo 103782 352565 := bbase (se 5 (by rfl) ⟨16526, by rfl⟩ : syracuseStep 352565 = 33053) (by norm_num)
theorem B155981 : Blo 103782 155981 := bbase (se 3 (by rfl) ⟨29246, by rfl⟩ : syracuseStep 155981 = 58493) (by norm_num)
theorem B156005 : Blo 103782 156005 := bbase (se 4 (by rfl) ⟨14625, by rfl⟩ : syracuseStep 156005 = 29251) (by norm_num)
theorem B450917 : Blo 103782 450917 := bbase (se 4 (by rfl) ⟨42273, by rfl⟩ : syracuseStep 450917 = 84547) (by norm_num)
theorem B156029 : Blo 103782 156029 := bbase (se 3 (by rfl) ⟨29255, by rfl⟩ : syracuseStep 156029 = 58511) (by norm_num)
theorem B156053 : Blo 103782 156053 := bbase (se 6 (by rfl) ⟨3657, by rfl⟩ : syracuseStep 156053 = 7315) (by norm_num)
theorem B156077 : Blo 103782 156077 := bbase (se 3 (by rfl) ⟨29264, by rfl⟩ : syracuseStep 156077 = 58529) (by norm_num)
theorem B156101 : Blo 103782 156101 := bbase (se 4 (by rfl) ⟨14634, by rfl⟩ : syracuseStep 156101 = 29269) (by norm_num)
theorem B156125 : Blo 103782 156125 := bbase (se 3 (by rfl) ⟨29273, by rfl⟩ : syracuseStep 156125 = 58547) (by norm_num)
theorem B156149 : Blo 103782 156149 := bbase (se 5 (by rfl) ⟨7319, by rfl⟩ : syracuseStep 156149 = 14639) (by norm_num)
theorem B156173 : Blo 103782 156173 := bbase (se 3 (by rfl) ⟨29282, by rfl⟩ : syracuseStep 156173 = 58565) (by norm_num)
theorem B156197 : Blo 103782 156197 := bbase (se 4 (by rfl) ⟨14643, by rfl⟩ : syracuseStep 156197 = 29287) (by norm_num)
theorem B156221 : Blo 103782 156221 := bbase (se 3 (by rfl) ⟨29291, by rfl⟩ : syracuseStep 156221 = 58583) (by norm_num)
theorem B156245 : Blo 103782 156245 := bbase (se 8 (by rfl) ⟨915, by rfl⟩ : syracuseStep 156245 = 1831) (by norm_num)
theorem B156269 : Blo 103782 156269 := bbase (se 3 (by rfl) ⟨29300, by rfl⟩ : syracuseStep 156269 = 58601) (by norm_num)
theorem B254573 : Blo 103782 254573 := bbase (se 3 (by rfl) ⟨47732, by rfl⟩ : syracuseStep 254573 = 95465) (by norm_num)
theorem B156293 : Blo 103782 156293 := bbase (se 4 (by rfl) ⟨14652, by rfl⟩ : syracuseStep 156293 = 29305) (by norm_num)
theorem B156317 : Blo 103782 156317 := bbase (se 3 (by rfl) ⟨29309, by rfl⟩ : syracuseStep 156317 = 58619) (by norm_num)
theorem B156341 : Blo 103782 156341 := bbase (se 5 (by rfl) ⟨7328, by rfl⟩ : syracuseStep 156341 = 14657) (by norm_num)
theorem B156365 : Blo 103782 156365 := bbase (se 3 (by rfl) ⟨29318, by rfl⟩ : syracuseStep 156365 = 58637) (by norm_num)
theorem B156389 : Blo 103782 156389 := bbase (se 4 (by rfl) ⟨14661, by rfl⟩ : syracuseStep 156389 = 29323) (by norm_num)
theorem B352997 : Blo 103782 352997 := bbase (se 4 (by rfl) ⟨33093, by rfl⟩ : syracuseStep 352997 = 66187) (by norm_num)
theorem B156413 : Blo 103782 156413 := bbase (se 3 (by rfl) ⟨29327, by rfl⟩ : syracuseStep 156413 = 58655) (by norm_num)
theorem B156437 : Blo 103782 156437 := bbase (se 6 (by rfl) ⟨3666, by rfl⟩ : syracuseStep 156437 = 7333) (by norm_num)
theorem B156461 : Blo 103782 156461 := bbase (se 3 (by rfl) ⟨29336, by rfl⟩ : syracuseStep 156461 = 58673) (by norm_num)
theorem B189229 : Blo 103782 189229 := bbase (se 3 (by rfl) ⟨35480, by rfl⟩ : syracuseStep 189229 = 70961) (by norm_num)
theorem B254765 : Blo 103782 254765 := bbase (se 3 (by rfl) ⟨47768, by rfl⟩ : syracuseStep 254765 = 95537) (by norm_num)
theorem B156485 : Blo 103782 156485 := bbase (se 4 (by rfl) ⟨14670, by rfl⟩ : syracuseStep 156485 = 29341) (by norm_num)
theorem B156509 : Blo 103782 156509 := bbase (se 3 (by rfl) ⟨29345, by rfl⟩ : syracuseStep 156509 = 58691) (by norm_num)
theorem B156533 : Blo 103782 156533 := bbase (se 5 (by rfl) ⟨7337, by rfl⟩ : syracuseStep 156533 = 14675) (by norm_num)
theorem B156557 : Blo 103782 156557 := bbase (se 3 (by rfl) ⟨29354, by rfl⟩ : syracuseStep 156557 = 58709) (by norm_num)
theorem B156581 : Blo 103782 156581 := bbase (se 4 (by rfl) ⟨14679, by rfl⟩ : syracuseStep 156581 = 29359) (by norm_num)
theorem B156605 : Blo 103782 156605 := bbase (se 3 (by rfl) ⟨29363, by rfl⟩ : syracuseStep 156605 = 58727) (by norm_num)
theorem B156629 : Blo 103782 156629 := bbase (se 7 (by rfl) ⟨1835, by rfl⟩ : syracuseStep 156629 = 3671) (by norm_num)
theorem B156653 : Blo 103782 156653 := bbase (se 3 (by rfl) ⟨29372, by rfl⟩ : syracuseStep 156653 = 58745) (by norm_num)
theorem B156677 : Blo 103782 156677 := bbase (se 4 (by rfl) ⟨14688, by rfl⟩ : syracuseStep 156677 = 29377) (by norm_num)
theorem B156701 : Blo 103782 156701 := bbase (se 3 (by rfl) ⟨29381, by rfl⟩ : syracuseStep 156701 = 58763) (by norm_num)
theorem B156725 : Blo 103782 156725 := bbase (se 5 (by rfl) ⟨7346, by rfl⟩ : syracuseStep 156725 = 14693) (by norm_num)
theorem B123961 : Blo 103782 123961 := bbase (se 2 (by rfl) ⟨46485, by rfl⟩ : syracuseStep 123961 = 92971) (by norm_num)
theorem B156749 : Blo 103782 156749 := bbase (se 3 (by rfl) ⟨29390, by rfl⟩ : syracuseStep 156749 = 58781) (by norm_num)
theorem B156773 : Blo 103782 156773 := bbase (se 4 (by rfl) ⟨14697, by rfl⟩ : syracuseStep 156773 = 29395) (by norm_num)
theorem B156797 : Blo 103782 156797 := bbase (se 3 (by rfl) ⟨29399, by rfl⟩ : syracuseStep 156797 = 58799) (by norm_num)
theorem B156821 : Blo 103782 156821 := bbase (se 6 (by rfl) ⟨3675, by rfl⟩ : syracuseStep 156821 = 7351) (by norm_num)
theorem B353429 : Blo 103782 353429 := bbase (se 6 (by rfl) ⟨8283, by rfl⟩ : syracuseStep 353429 = 16567) (by norm_num)
theorem B156845 : Blo 103782 156845 := bbase (se 3 (by rfl) ⟨29408, by rfl⟩ : syracuseStep 156845 = 58817) (by norm_num)
theorem B156869 : Blo 103782 156869 := bbase (se 4 (by rfl) ⟨14706, by rfl⟩ : syracuseStep 156869 = 29413) (by norm_num)
theorem B156893 : Blo 103782 156893 := bbase (se 3 (by rfl) ⟨29417, by rfl⟩ : syracuseStep 156893 = 58835) (by norm_num)
theorem B156917 : Blo 103782 156917 := bbase (se 5 (by rfl) ⟨7355, by rfl⟩ : syracuseStep 156917 = 14711) (by norm_num)
theorem B156941 : Blo 103782 156941 := bbase (se 3 (by rfl) ⟨29426, by rfl⟩ : syracuseStep 156941 = 58853) (by norm_num)
theorem B156965 : Blo 103782 156965 := bbase (se 4 (by rfl) ⟨14715, by rfl⟩ : syracuseStep 156965 = 29431) (by norm_num)
theorem B156989 : Blo 103782 156989 := bbase (se 3 (by rfl) ⟨29435, by rfl⟩ : syracuseStep 156989 = 58871) (by norm_num)
theorem B157013 : Blo 103782 157013 := bbase (se 12 (by rfl) ⟨57, by rfl⟩ : syracuseStep 157013 = 115) (by norm_num)
theorem B451925 : Blo 103782 451925 := bbase (se 12 (by rfl) ⟨165, by rfl⟩ : syracuseStep 451925 = 331) (by norm_num)
theorem B157037 : Blo 103782 157037 := bbase (se 3 (by rfl) ⟨29444, by rfl⟩ : syracuseStep 157037 = 58889) (by norm_num)
theorem B157061 : Blo 103782 157061 := bbase (se 4 (by rfl) ⟨14724, by rfl⟩ : syracuseStep 157061 = 29449) (by norm_num)
theorem B157085 : Blo 103782 157085 := bbase (se 3 (by rfl) ⟨29453, by rfl⟩ : syracuseStep 157085 = 58907) (by norm_num)
theorem B157109 : Blo 103782 157109 := bbase (se 5 (by rfl) ⟨7364, by rfl⟩ : syracuseStep 157109 = 14729) (by norm_num)
theorem B157133 : Blo 103782 157133 := bbase (se 3 (by rfl) ⟨29462, by rfl⟩ : syracuseStep 157133 = 58925) (by norm_num)
theorem B157157 : Blo 103782 157157 := bbase (se 4 (by rfl) ⟨14733, by rfl⟩ : syracuseStep 157157 = 29467) (by norm_num)
theorem B157181 : Blo 103782 157181 := bbase (se 3 (by rfl) ⟨29471, by rfl⟩ : syracuseStep 157181 = 58943) (by norm_num)
theorem B189949 : Blo 103782 189949 := bbase (se 3 (by rfl) ⟨35615, by rfl⟩ : syracuseStep 189949 = 71231) (by norm_num)
theorem B222725 : Blo 103782 222725 := bbase (se 4 (by rfl) ⟨20880, by rfl⟩ : syracuseStep 222725 = 41761) (by norm_num)
theorem B157205 : Blo 103782 157205 := bbase (se 6 (by rfl) ⟨3684, by rfl⟩ : syracuseStep 157205 = 7369) (by norm_num)
theorem B157229 : Blo 103782 157229 := bbase (se 3 (by rfl) ⟨29480, by rfl⟩ : syracuseStep 157229 = 58961) (by norm_num)
theorem B157253 : Blo 103782 157253 := bbase (se 4 (by rfl) ⟨14742, by rfl⟩ : syracuseStep 157253 = 29485) (by norm_num)
theorem B353861 : Blo 103782 353861 := bbase (se 4 (by rfl) ⟨33174, by rfl⟩ : syracuseStep 353861 = 66349) (by norm_num)
theorem B157277 : Blo 103782 157277 := bbase (se 3 (by rfl) ⟨29489, by rfl⟩ : syracuseStep 157277 = 58979) (by norm_num)
theorem B157301 : Blo 103782 157301 := bbase (se 5 (by rfl) ⟨7373, by rfl⟩ : syracuseStep 157301 = 14747) (by norm_num)
theorem B157325 : Blo 103782 157325 := bbase (se 3 (by rfl) ⟨29498, by rfl⟩ : syracuseStep 157325 = 58997) (by norm_num)
theorem B222869 : Blo 103782 222869 := bbase (se 6 (by rfl) ⟨5223, by rfl⟩ : syracuseStep 222869 = 10447) (by norm_num)
theorem B157349 : Blo 103782 157349 := bbase (se 4 (by rfl) ⟨14751, by rfl⟩ : syracuseStep 157349 = 29503) (by norm_num)
theorem B157373 : Blo 103782 157373 := bbase (se 3 (by rfl) ⟨29507, by rfl⟩ : syracuseStep 157373 = 59015) (by norm_num)
theorem B321221 : Blo 103782 321221 := bbase (se 4 (by rfl) ⟨30114, by rfl⟩ : syracuseStep 321221 = 60229) (by norm_num)
theorem B157397 : Blo 103782 157397 := bbase (se 7 (by rfl) ⟨1844, by rfl⟩ : syracuseStep 157397 = 3689) (by norm_num)
theorem B190181 : Blo 103782 190181 := bbase (se 4 (by rfl) ⟨17829, by rfl⟩ : syracuseStep 190181 = 35659) (by norm_num)
theorem B157421 : Blo 103782 157421 := bbase (se 3 (by rfl) ⟨29516, by rfl⟩ : syracuseStep 157421 = 59033) (by norm_num)
theorem B157445 : Blo 103782 157445 := bbase (se 4 (by rfl) ⟨14760, by rfl⟩ : syracuseStep 157445 = 29521) (by norm_num)
theorem B517909 : Blo 103782 517909 := bbase (se 6 (by rfl) ⟨12138, by rfl⟩ : syracuseStep 517909 = 24277) (by norm_num)
theorem B157469 : Blo 103782 157469 := bbase (se 3 (by rfl) ⟨29525, by rfl⟩ : syracuseStep 157469 = 59051) (by norm_num)
theorem B157493 : Blo 103782 157493 := bbase (se 5 (by rfl) ⟨7382, by rfl⟩ : syracuseStep 157493 = 14765) (by norm_num)
theorem B157517 : Blo 103782 157517 := bbase (se 3 (by rfl) ⟨29534, by rfl⟩ : syracuseStep 157517 = 59069) (by norm_num)
theorem B6022997 : Blo 103782 6022997 := bbase (se 9 (by rfl) ⟨17645, by rfl⟩ : syracuseStep 6022997 = 35291) (by norm_num)
theorem B157541 : Blo 103782 157541 := bbase (se 4 (by rfl) ⟨14769, by rfl⟩ : syracuseStep 157541 = 29539) (by norm_num)
theorem B157565 : Blo 103782 157565 := bbase (se 3 (by rfl) ⟨29543, by rfl⟩ : syracuseStep 157565 = 59087) (by norm_num)
theorem B157589 : Blo 103782 157589 := bbase (se 6 (by rfl) ⟨3693, by rfl⟩ : syracuseStep 157589 = 7387) (by norm_num)
theorem B157613 : Blo 103782 157613 := bbase (se 3 (by rfl) ⟨29552, by rfl⟩ : syracuseStep 157613 = 59105) (by norm_num)
theorem B157637 : Blo 103782 157637 := bbase (se 4 (by rfl) ⟨14778, by rfl⟩ : syracuseStep 157637 = 29557) (by norm_num)
theorem B157661 : Blo 103782 157661 := bbase (se 3 (by rfl) ⟨29561, by rfl⟩ : syracuseStep 157661 = 59123) (by norm_num)
theorem B354293 : Blo 103782 354293 := bbase (se 5 (by rfl) ⟨16607, by rfl⟩ : syracuseStep 354293 = 33215) (by norm_num)
theorem B157685 : Blo 103782 157685 := bbase (se 5 (by rfl) ⟨7391, by rfl⟩ : syracuseStep 157685 = 14783) (by norm_num)
theorem B223229 : Blo 103782 223229 := bbase (se 3 (by rfl) ⟨41855, by rfl⟩ : syracuseStep 223229 = 83711) (by norm_num)
theorem B256013 : Blo 103782 256013 := bbase (se 3 (by rfl) ⟨48002, by rfl⟩ : syracuseStep 256013 = 96005) (by norm_num)
theorem B157709 : Blo 103782 157709 := bbase (se 3 (by rfl) ⟨29570, by rfl⟩ : syracuseStep 157709 = 59141) (by norm_num)
theorem B813077 : Blo 103782 813077 := bbase (se 6 (by rfl) ⟨19056, by rfl⟩ : syracuseStep 813077 = 38113) (by norm_num)
theorem B157733 : Blo 103782 157733 := bbase (se 4 (by rfl) ⟨14787, by rfl⟩ : syracuseStep 157733 = 29575) (by norm_num)
theorem B157757 : Blo 103782 157757 := bbase (se 3 (by rfl) ⟨29579, by rfl⟩ : syracuseStep 157757 = 59159) (by norm_num)
theorem B157781 : Blo 103782 157781 := bbase (se 8 (by rfl) ⟨924, by rfl⟩ : syracuseStep 157781 = 1849) (by norm_num)
theorem B157805 : Blo 103782 157805 := bbase (se 3 (by rfl) ⟨29588, by rfl⟩ : syracuseStep 157805 = 59177) (by norm_num)
theorem B911477 : Blo 103782 911477 := bbase (se 5 (by rfl) ⟨42725, by rfl⟩ : syracuseStep 911477 = 85451) (by norm_num)
theorem B157829 : Blo 103782 157829 := bbase (se 4 (by rfl) ⟨14796, by rfl⟩ : syracuseStep 157829 = 29593) (by norm_num)
theorem B190613 : Blo 103782 190613 := bbase (se 6 (by rfl) ⟨4467, by rfl⟩ : syracuseStep 190613 = 8935) (by norm_num)
theorem B157853 : Blo 103782 157853 := bbase (se 3 (by rfl) ⟨29597, by rfl⟩ : syracuseStep 157853 = 59195) (by norm_num)
theorem B157877 : Blo 103782 157877 := bbase (se 5 (by rfl) ⟨7400, by rfl⟩ : syracuseStep 157877 = 14801) (by norm_num)
theorem B157901 : Blo 103782 157901 := bbase (se 3 (by rfl) ⟨29606, by rfl⟩ : syracuseStep 157901 = 59213) (by norm_num)
theorem B157925 : Blo 103782 157925 := bbase (se 4 (by rfl) ⟨14805, by rfl⟩ : syracuseStep 157925 = 29611) (by norm_num)
theorem B157949 : Blo 103782 157949 := bbase (se 3 (by rfl) ⟨29615, by rfl⟩ : syracuseStep 157949 = 59231) (by norm_num)
theorem B157973 : Blo 103782 157973 := bbase (se 6 (by rfl) ⟨3702, by rfl⟩ : syracuseStep 157973 = 7405) (by norm_num)
theorem B190757 : Blo 103782 190757 := bbase (se 4 (by rfl) ⟨17883, by rfl⟩ : syracuseStep 190757 = 35767) (by norm_num)
theorem B157997 : Blo 103782 157997 := bbase (se 3 (by rfl) ⟨29624, by rfl⟩ : syracuseStep 157997 = 59249) (by norm_num)
theorem B158021 : Blo 103782 158021 := bbase (se 4 (by rfl) ⟨14814, by rfl⟩ : syracuseStep 158021 = 29629) (by norm_num)
theorem B158045 : Blo 103782 158045 := bbase (se 3 (by rfl) ⟨29633, by rfl⟩ : syracuseStep 158045 = 59267) (by norm_num)
theorem B158069 : Blo 103782 158069 := bbase (se 5 (by rfl) ⟨7409, by rfl⟩ : syracuseStep 158069 = 14819) (by norm_num)
theorem B158093 : Blo 103782 158093 := bbase (se 3 (by rfl) ⟨29642, by rfl⟩ : syracuseStep 158093 = 59285) (by norm_num)
theorem B354725 : Blo 103782 354725 := bbase (se 4 (by rfl) ⟨33255, by rfl⟩ : syracuseStep 354725 = 66511) (by norm_num)
theorem B158117 : Blo 103782 158117 := bbase (se 4 (by rfl) ⟨14823, by rfl⟩ : syracuseStep 158117 = 29647) (by norm_num)
theorem B387509 : Blo 103782 387509 := bbase (se 5 (by rfl) ⟨18164, by rfl⟩ : syracuseStep 387509 = 36329) (by norm_num)
theorem B158141 : Blo 103782 158141 := bbase (se 3 (by rfl) ⟨29651, by rfl⟩ : syracuseStep 158141 = 59303) (by norm_num)
theorem B158165 : Blo 103782 158165 := bbase (se 7 (by rfl) ⟨1853, by rfl⟩ : syracuseStep 158165 = 3707) (by norm_num)
theorem B158189 : Blo 103782 158189 := bbase (se 3 (by rfl) ⟨29660, by rfl⟩ : syracuseStep 158189 = 59321) (by norm_num)
theorem B158213 : Blo 103782 158213 := bbase (se 4 (by rfl) ⟨14832, by rfl⟩ : syracuseStep 158213 = 29665) (by norm_num)
theorem B158237 : Blo 103782 158237 := bbase (se 3 (by rfl) ⟨29669, by rfl⟩ : syracuseStep 158237 = 59339) (by norm_num)
theorem B158261 : Blo 103782 158261 := bbase (se 5 (by rfl) ⟨7418, by rfl⟩ : syracuseStep 158261 = 14837) (by norm_num)
theorem B191045 : Blo 103782 191045 := bbase (se 4 (by rfl) ⟨17910, by rfl⟩ : syracuseStep 191045 = 35821) (by norm_num)
theorem B158285 : Blo 103782 158285 := bbase (se 3 (by rfl) ⟨29678, by rfl⟩ : syracuseStep 158285 = 59357) (by norm_num)
theorem B158309 : Blo 103782 158309 := bbase (se 4 (by rfl) ⟨14841, by rfl⟩ : syracuseStep 158309 = 29683) (by norm_num)
theorem B158333 : Blo 103782 158333 := bbase (se 3 (by rfl) ⟨29687, by rfl⟩ : syracuseStep 158333 = 59375) (by norm_num)
theorem B158357 : Blo 103782 158357 := bbase (se 6 (by rfl) ⟨3711, by rfl⟩ : syracuseStep 158357 = 7423) (by norm_num)
theorem B158381 : Blo 103782 158381 := bbase (se 3 (by rfl) ⟨29696, by rfl⟩ : syracuseStep 158381 = 59393) (by norm_num)
theorem B125633 : Blo 103782 125633 := bbase (se 2 (by rfl) ⟨47112, by rfl⟩ : syracuseStep 125633 = 94225) (by norm_num)
theorem B158405 : Blo 103782 158405 := bbase (se 4 (by rfl) ⟨14850, by rfl⟩ : syracuseStep 158405 = 29701) (by norm_num)
theorem B158429 : Blo 103782 158429 := bbase (se 3 (by rfl) ⟨29705, by rfl⟩ : syracuseStep 158429 = 59411) (by norm_num)
theorem B158453 : Blo 103782 158453 := bbase (se 5 (by rfl) ⟨7427, by rfl⟩ : syracuseStep 158453 = 14855) (by norm_num)
theorem B158477 : Blo 103782 158477 := bbase (se 3 (by rfl) ⟨29714, by rfl⟩ : syracuseStep 158477 = 59429) (by norm_num)
theorem B158501 : Blo 103782 158501 := bbase (se 4 (by rfl) ⟨14859, by rfl⟩ : syracuseStep 158501 = 29719) (by norm_num)
theorem B191269 : Blo 103782 191269 := bbase (se 4 (by rfl) ⟨17931, by rfl⟩ : syracuseStep 191269 = 35863) (by norm_num)
theorem B125749 : Blo 103782 125749 := bbase (se 5 (by rfl) ⟨5894, by rfl⟩ : syracuseStep 125749 = 11789) (by norm_num)
theorem B158525 : Blo 103782 158525 := bbase (se 3 (by rfl) ⟨29723, by rfl⟩ : syracuseStep 158525 = 59447) (by norm_num)
theorem B355157 : Blo 103782 355157 := bbase (se 9 (by rfl) ⟨1040, by rfl⟩ : syracuseStep 355157 = 2081) (by norm_num)
theorem B158549 : Blo 103782 158549 := bbase (se 9 (by rfl) ⟨464, by rfl⟩ : syracuseStep 158549 = 929) (by norm_num)
theorem B191333 : Blo 103782 191333 := bbase (se 4 (by rfl) ⟨17937, by rfl⟩ : syracuseStep 191333 = 35875) (by norm_num)
theorem B158573 : Blo 103782 158573 := bbase (se 3 (by rfl) ⟨29732, by rfl⟩ : syracuseStep 158573 = 59465) (by norm_num)
theorem B224117 : Blo 103782 224117 := bbase (se 5 (by rfl) ⟨10505, by rfl⟩ : syracuseStep 224117 = 21011) (by norm_num)
theorem B125821 : Blo 103782 125821 := bbase (se 3 (by rfl) ⟨23591, by rfl⟩ : syracuseStep 125821 = 47183) (by norm_num)
theorem B158597 : Blo 103782 158597 := bbase (se 4 (by rfl) ⟨14868, by rfl⟩ : syracuseStep 158597 = 29737) (by norm_num)
theorem B158621 : Blo 103782 158621 := bbase (se 3 (by rfl) ⟨29741, by rfl⟩ : syracuseStep 158621 = 59483) (by norm_num)
theorem B158645 : Blo 103782 158645 := bbase (se 5 (by rfl) ⟨7436, by rfl⟩ : syracuseStep 158645 = 14873) (by norm_num)
theorem B158669 : Blo 103782 158669 := bbase (se 3 (by rfl) ⟨29750, by rfl⟩ : syracuseStep 158669 = 59501) (by norm_num)
theorem B158693 : Blo 103782 158693 := bbase (se 4 (by rfl) ⟨14877, by rfl⟩ : syracuseStep 158693 = 29755) (by norm_num)
theorem B125941 : Blo 103782 125941 := bbase (se 5 (by rfl) ⟨5903, by rfl⟩ : syracuseStep 125941 = 11807) (by norm_num)
theorem B158717 : Blo 103782 158717 := bbase (se 3 (by rfl) ⟨29759, by rfl⟩ : syracuseStep 158717 = 59519) (by norm_num)
theorem B158741 : Blo 103782 158741 := bbase (se 6 (by rfl) ⟨3720, by rfl⟩ : syracuseStep 158741 = 7441) (by norm_num)
theorem B257053 : Blo 103782 257053 := bbase (se 3 (by rfl) ⟨48197, by rfl⟩ : syracuseStep 257053 = 96395) (by norm_num)
theorem B158765 : Blo 103782 158765 := bbase (se 3 (by rfl) ⟨29768, by rfl⟩ : syracuseStep 158765 = 59537) (by norm_num)
theorem B158789 : Blo 103782 158789 := bbase (se 4 (by rfl) ⟨14886, by rfl⟩ : syracuseStep 158789 = 29773) (by norm_num)
theorem B453701 : Blo 103782 453701 := bbase (se 4 (by rfl) ⟨42534, by rfl⟩ : syracuseStep 453701 = 85069) (by norm_num)
theorem B158813 : Blo 103782 158813 := bbase (se 3 (by rfl) ⟨29777, by rfl⟩ : syracuseStep 158813 = 59555) (by norm_num)
theorem B224365 : Blo 103782 224365 := bbase (se 3 (by rfl) ⟨42068, by rfl⟩ : syracuseStep 224365 = 84137) (by norm_num)
theorem B158837 : Blo 103782 158837 := bbase (se 5 (by rfl) ⟨7445, by rfl⟩ : syracuseStep 158837 = 14891) (by norm_num)
theorem B158861 : Blo 103782 158861 := bbase (se 3 (by rfl) ⟨29786, by rfl⟩ : syracuseStep 158861 = 59573) (by norm_num)
theorem B257189 : Blo 103782 257189 := bbase (se 4 (by rfl) ⟨24111, by rfl⟩ : syracuseStep 257189 = 48223) (by norm_num)
theorem B158885 : Blo 103782 158885 := bbase (se 4 (by rfl) ⟨14895, by rfl⟩ : syracuseStep 158885 = 29791) (by norm_num)
theorem B158909 : Blo 103782 158909 := bbase (se 3 (by rfl) ⟨29795, by rfl⟩ : syracuseStep 158909 = 59591) (by norm_num)
theorem B158933 : Blo 103782 158933 := bbase (se 7 (by rfl) ⟨1862, by rfl⟩ : syracuseStep 158933 = 3725) (by norm_num)
theorem B158957 : Blo 103782 158957 := bbase (se 3 (by rfl) ⟨29804, by rfl⟩ : syracuseStep 158957 = 59609) (by norm_num)
theorem B355589 : Blo 103782 355589 := bbase (se 4 (by rfl) ⟨33336, by rfl⟩ : syracuseStep 355589 = 66673) (by norm_num)
theorem B158981 : Blo 103782 158981 := bbase (se 4 (by rfl) ⟨14904, by rfl⟩ : syracuseStep 158981 = 29809) (by norm_num)
theorem B159005 : Blo 103782 159005 := bbase (se 3 (by rfl) ⟨29813, by rfl⟩ : syracuseStep 159005 = 59627) (by norm_num)
theorem B421157 : Blo 103782 421157 := bbase (se 4 (by rfl) ⟨39483, by rfl⟩ : syracuseStep 421157 = 78967) (by norm_num)
theorem B159029 : Blo 103782 159029 := bbase (se 5 (by rfl) ⟨7454, by rfl⟩ : syracuseStep 159029 = 14909) (by norm_num)
theorem B388421 : Blo 103782 388421 := bbase (se 4 (by rfl) ⟨36414, by rfl⟩ : syracuseStep 388421 = 72829) (by norm_num)
theorem B159053 : Blo 103782 159053 := bbase (se 3 (by rfl) ⟨29822, by rfl⟩ : syracuseStep 159053 = 59645) (by norm_num)
theorem B159077 : Blo 103782 159077 := bbase (se 4 (by rfl) ⟨14913, by rfl⟩ : syracuseStep 159077 = 29827) (by norm_num)
theorem B126325 : Blo 103782 126325 := bbase (se 5 (by rfl) ⟨5921, by rfl⟩ : syracuseStep 126325 = 11843) (by norm_num)
theorem B159101 : Blo 103782 159101 := bbase (se 3 (by rfl) ⟨29831, by rfl⟩ : syracuseStep 159101 = 59663) (by norm_num)
theorem B159125 : Blo 103782 159125 := bbase (se 6 (by rfl) ⟨3729, by rfl⟩ : syracuseStep 159125 = 7459) (by norm_num)
theorem B159149 : Blo 103782 159149 := bbase (se 3 (by rfl) ⟨29840, by rfl⟩ : syracuseStep 159149 = 59681) (by norm_num)
theorem B159173 : Blo 103782 159173 := bbase (se 4 (by rfl) ⟨14922, by rfl⟩ : syracuseStep 159173 = 29845) (by norm_num)
theorem B159197 : Blo 103782 159197 := bbase (se 3 (by rfl) ⟨29849, by rfl⟩ : syracuseStep 159197 = 59699) (by norm_num)
theorem B159221 : Blo 103782 159221 := bbase (se 5 (by rfl) ⟨7463, by rfl⟩ : syracuseStep 159221 = 14927) (by norm_num)
theorem B159245 : Blo 103782 159245 := bbase (se 3 (by rfl) ⟨29858, by rfl⟩ : syracuseStep 159245 = 59717) (by norm_num)
theorem B159269 : Blo 103782 159269 := bbase (se 4 (by rfl) ⟨14931, by rfl⟩ : syracuseStep 159269 = 29863) (by norm_num)
theorem B159293 : Blo 103782 159293 := bbase (se 3 (by rfl) ⟨29867, by rfl⟩ : syracuseStep 159293 = 59735) (by norm_num)
theorem B159317 : Blo 103782 159317 := bbase (se 8 (by rfl) ⟨933, by rfl⟩ : syracuseStep 159317 = 1867) (by norm_num)
theorem B224869 : Blo 103782 224869 := bbase (se 4 (by rfl) ⟨21081, by rfl⟩ : syracuseStep 224869 = 42163) (by norm_num)
theorem B159341 : Blo 103782 159341 := bbase (se 3 (by rfl) ⟨29876, by rfl⟩ : syracuseStep 159341 = 59753) (by norm_num)
theorem B159365 : Blo 103782 159365 := bbase (se 4 (by rfl) ⟨14940, by rfl⟩ : syracuseStep 159365 = 29881) (by norm_num)
theorem B192149 : Blo 103782 192149 := bbase (se 6 (by rfl) ⟨4503, by rfl⟩ : syracuseStep 192149 = 9007) (by norm_num)
theorem B159389 : Blo 103782 159389 := bbase (se 3 (by rfl) ⟨29885, by rfl⟩ : syracuseStep 159389 = 59771) (by norm_num)
theorem B356021 : Blo 103782 356021 := bbase (se 5 (by rfl) ⟨16688, by rfl⟩ : syracuseStep 356021 = 33377) (by norm_num)
theorem B159413 : Blo 103782 159413 := bbase (se 5 (by rfl) ⟨7472, by rfl⟩ : syracuseStep 159413 = 14945) (by norm_num)
theorem B257717 : Blo 103782 257717 := bbase (se 5 (by rfl) ⟨12080, by rfl⟩ : syracuseStep 257717 = 24161) (by norm_num)
theorem B159437 : Blo 103782 159437 := bbase (se 3 (by rfl) ⟨29894, by rfl⟩ : syracuseStep 159437 = 59789) (by norm_num)
theorem B159461 : Blo 103782 159461 := bbase (se 4 (by rfl) ⟨14949, by rfl⟩ : syracuseStep 159461 = 29899) (by norm_num)
theorem B159485 : Blo 103782 159485 := bbase (se 3 (by rfl) ⟨29903, by rfl⟩ : syracuseStep 159485 = 59807) (by norm_num)
theorem B159509 : Blo 103782 159509 := bbase (se 6 (by rfl) ⟨3738, by rfl⟩ : syracuseStep 159509 = 7477) (by norm_num)
theorem B159533 : Blo 103782 159533 := bbase (se 3 (by rfl) ⟨29912, by rfl⟩ : syracuseStep 159533 = 59825) (by norm_num)
theorem B159557 : Blo 103782 159557 := bbase (se 4 (by rfl) ⟨14958, by rfl⟩ : syracuseStep 159557 = 29917) (by norm_num)
theorem B159565 : Blo 103782 159565 := bbase (se 3 (by rfl) ⟨29918, by rfl⟩ : syracuseStep 159565 = 59837) (by norm_num)
theorem B159581 : Blo 103782 159581 := bbase (se 3 (by rfl) ⟨29921, by rfl⟩ : syracuseStep 159581 = 59843) (by norm_num)
theorem B159605 : Blo 103782 159605 := bbase (se 5 (by rfl) ⟨7481, by rfl⟩ : syracuseStep 159605 = 14963) (by norm_num)
theorem B159629 : Blo 103782 159629 := bbase (se 3 (by rfl) ⟨29930, by rfl⟩ : syracuseStep 159629 = 59861) (by norm_num)
theorem B159653 : Blo 103782 159653 := bbase (se 4 (by rfl) ⟨14967, by rfl⟩ : syracuseStep 159653 = 29935) (by norm_num)
theorem B159677 : Blo 103782 159677 := bbase (se 3 (by rfl) ⟨29939, by rfl⟩ : syracuseStep 159677 = 59879) (by norm_num)
theorem B159701 : Blo 103782 159701 := bbase (se 7 (by rfl) ⟨1871, by rfl⟩ : syracuseStep 159701 = 3743) (by norm_num)
theorem B159725 : Blo 103782 159725 := bbase (se 3 (by rfl) ⟨29948, by rfl⟩ : syracuseStep 159725 = 59897) (by norm_num)
theorem B159749 : Blo 103782 159749 := bbase (se 4 (by rfl) ⟨14976, by rfl⟩ : syracuseStep 159749 = 29953) (by norm_num)
theorem B159773 : Blo 103782 159773 := bbase (se 3 (by rfl) ⟨29957, by rfl⟩ : syracuseStep 159773 = 59915) (by norm_num)
theorem B127013 : Blo 103782 127013 := bbase (se 4 (by rfl) ⟨11907, by rfl⟩ : syracuseStep 127013 = 23815) (by norm_num)
theorem B159797 : Blo 103782 159797 := bbase (se 5 (by rfl) ⟨7490, by rfl⟩ : syracuseStep 159797 = 14981) (by norm_num)
theorem B159821 : Blo 103782 159821 := bbase (se 3 (by rfl) ⟨29966, by rfl⟩ : syracuseStep 159821 = 59933) (by norm_num)
theorem B356453 : Blo 103782 356453 := bbase (se 4 (by rfl) ⟨33417, by rfl⟩ : syracuseStep 356453 = 66835) (by norm_num)
theorem B159845 : Blo 103782 159845 := bbase (se 4 (by rfl) ⟨14985, by rfl⟩ : syracuseStep 159845 = 29971) (by norm_num)
theorem B159869 : Blo 103782 159869 := bbase (se 3 (by rfl) ⟨29975, by rfl⟩ : syracuseStep 159869 = 59951) (by norm_num)
theorem B159893 : Blo 103782 159893 := bbase (se 6 (by rfl) ⟨3747, by rfl⟩ : syracuseStep 159893 = 7495) (by norm_num)
theorem B159917 : Blo 103782 159917 := bbase (se 3 (by rfl) ⟨29984, by rfl⟩ : syracuseStep 159917 = 59969) (by norm_num)
theorem B913589 : Blo 103782 913589 := bbase (se 5 (by rfl) ⟨42824, by rfl⟩ : syracuseStep 913589 = 85649) (by norm_num)
theorem B159941 : Blo 103782 159941 := bbase (se 4 (by rfl) ⟨14994, by rfl⟩ : syracuseStep 159941 = 29989) (by norm_num)
theorem B159965 : Blo 103782 159965 := bbase (se 3 (by rfl) ⟨29993, by rfl⟩ : syracuseStep 159965 = 59987) (by norm_num)
theorem B159989 : Blo 103782 159989 := bbase (se 5 (by rfl) ⟨7499, by rfl⟩ : syracuseStep 159989 = 14999) (by norm_num)
theorem B160013 : Blo 103782 160013 := bbase (se 3 (by rfl) ⟨30002, by rfl⟩ : syracuseStep 160013 = 60005) (by norm_num)
theorem B160037 : Blo 103782 160037 := bbase (se 4 (by rfl) ⟨15003, by rfl⟩ : syracuseStep 160037 = 30007) (by norm_num)
theorem B520501 : Blo 103782 520501 := bbase (se 5 (by rfl) ⟨24398, by rfl⟩ : syracuseStep 520501 = 48797) (by norm_num)
theorem B160061 : Blo 103782 160061 := bbase (se 3 (by rfl) ⟨30011, by rfl⟩ : syracuseStep 160061 = 60023) (by norm_num)
theorem B160085 : Blo 103782 160085 := bbase (se 10 (by rfl) ⟨234, by rfl⟩ : syracuseStep 160085 = 469) (by norm_num)
theorem B160109 : Blo 103782 160109 := bbase (se 3 (by rfl) ⟨30020, by rfl⟩ : syracuseStep 160109 = 60041) (by norm_num)
theorem B160133 : Blo 103782 160133 := bbase (se 4 (by rfl) ⟨15012, by rfl⟩ : syracuseStep 160133 = 30025) (by norm_num)
theorem B160157 : Blo 103782 160157 := bbase (se 3 (by rfl) ⟨30029, by rfl⟩ : syracuseStep 160157 = 60059) (by norm_num)
theorem B160181 : Blo 103782 160181 := bbase (se 5 (by rfl) ⟨7508, by rfl⟩ : syracuseStep 160181 = 15017) (by norm_num)
theorem B160205 : Blo 103782 160205 := bbase (se 3 (by rfl) ⟨30038, by rfl⟩ : syracuseStep 160205 = 60077) (by norm_num)
theorem B225757 : Blo 103782 225757 := bbase (se 3 (by rfl) ⟨42329, by rfl⟩ : syracuseStep 225757 = 84659) (by norm_num)
theorem B160229 : Blo 103782 160229 := bbase (se 4 (by rfl) ⟨15021, by rfl⟩ : syracuseStep 160229 = 30043) (by norm_num)
theorem B160253 : Blo 103782 160253 := bbase (se 3 (by rfl) ⟨30047, by rfl⟩ : syracuseStep 160253 = 60095) (by norm_num)
theorem B356885 : Blo 103782 356885 := bbase (se 6 (by rfl) ⟨8364, by rfl⟩ : syracuseStep 356885 = 16729) (by norm_num)
theorem B160277 : Blo 103782 160277 := bbase (se 6 (by rfl) ⟨3756, by rfl⟩ : syracuseStep 160277 = 7513) (by norm_num)
theorem B160301 : Blo 103782 160301 := bbase (se 3 (by rfl) ⟨30056, by rfl⟩ : syracuseStep 160301 = 60113) (by norm_num)
theorem B160325 : Blo 103782 160325 := bbase (se 4 (by rfl) ⟨15030, by rfl⟩ : syracuseStep 160325 = 30061) (by norm_num)
theorem B160349 : Blo 103782 160349 := bbase (se 3 (by rfl) ⟨30065, by rfl⟩ : syracuseStep 160349 = 60131) (by norm_num)
theorem B160373 : Blo 103782 160373 := bbase (se 5 (by rfl) ⟨7517, by rfl⟩ : syracuseStep 160373 = 15035) (by norm_num)
theorem B127613 : Blo 103782 127613 := bbase (se 3 (by rfl) ⟨23927, by rfl⟩ : syracuseStep 127613 = 47855) (by norm_num)
theorem B160397 : Blo 103782 160397 := bbase (se 3 (by rfl) ⟨30074, by rfl⟩ : syracuseStep 160397 = 60149) (by norm_num)
theorem B160421 : Blo 103782 160421 := bbase (se 4 (by rfl) ⟨15039, by rfl⟩ : syracuseStep 160421 = 30079) (by norm_num)
theorem B160445 : Blo 103782 160445 := bbase (se 3 (by rfl) ⟨30083, by rfl⟩ : syracuseStep 160445 = 60167) (by norm_num)
theorem B160469 : Blo 103782 160469 := bbase (se 7 (by rfl) ⟨1880, by rfl⟩ : syracuseStep 160469 = 3761) (by norm_num)
theorem B160493 : Blo 103782 160493 := bbase (se 3 (by rfl) ⟨30092, by rfl⟩ : syracuseStep 160493 = 60185) (by norm_num)
theorem B160517 : Blo 103782 160517 := bbase (se 4 (by rfl) ⟨15048, by rfl⟩ : syracuseStep 160517 = 30097) (by norm_num)
theorem B160541 : Blo 103782 160541 := bbase (se 3 (by rfl) ⟨30101, by rfl⟩ : syracuseStep 160541 = 60203) (by norm_num)
theorem B160565 : Blo 103782 160565 := bbase (se 5 (by rfl) ⟨7526, by rfl⟩ : syracuseStep 160565 = 15053) (by norm_num)
theorem B160589 : Blo 103782 160589 := bbase (se 3 (by rfl) ⟨30110, by rfl⟩ : syracuseStep 160589 = 60221) (by norm_num)
theorem B160613 : Blo 103782 160613 := bbase (se 4 (by rfl) ⟨15057, by rfl⟩ : syracuseStep 160613 = 30115) (by norm_num)
theorem B160637 : Blo 103782 160637 := bbase (se 3 (by rfl) ⟨30119, by rfl⟩ : syracuseStep 160637 = 60239) (by norm_num)
theorem B160661 : Blo 103782 160661 := bbase (se 6 (by rfl) ⟨3765, by rfl⟩ : syracuseStep 160661 = 7531) (by norm_num)
theorem B160685 : Blo 103782 160685 := bbase (se 3 (by rfl) ⟨30128, by rfl⟩ : syracuseStep 160685 = 60257) (by norm_num)
theorem B127921 : Blo 103782 127921 := bbase (se 2 (by rfl) ⟨47970, by rfl⟩ : syracuseStep 127921 = 95941) (by norm_num)
theorem B357317 : Blo 103782 357317 := bbase (se 4 (by rfl) ⟨33498, by rfl⟩ : syracuseStep 357317 = 66997) (by norm_num)
theorem B160709 : Blo 103782 160709 := bbase (se 4 (by rfl) ⟨15066, by rfl⟩ : syracuseStep 160709 = 30133) (by norm_num)
theorem B226253 : Blo 103782 226253 := bbase (se 3 (by rfl) ⟨42422, by rfl⟩ : syracuseStep 226253 = 84845) (by norm_num)
theorem B160733 : Blo 103782 160733 := bbase (se 3 (by rfl) ⟨30137, by rfl⟩ : syracuseStep 160733 = 60275) (by norm_num)
theorem B160757 : Blo 103782 160757 := bbase (se 5 (by rfl) ⟨7535, by rfl⟩ : syracuseStep 160757 = 15071) (by norm_num)
theorem B160781 : Blo 103782 160781 := bbase (se 3 (by rfl) ⟨30146, by rfl⟩ : syracuseStep 160781 = 60293) (by norm_num)
theorem B128017 : Blo 103782 128017 := bbase (se 2 (by rfl) ⟨48006, by rfl⟩ : syracuseStep 128017 = 96013) (by norm_num)
theorem B160805 : Blo 103782 160805 := bbase (se 4 (by rfl) ⟨15075, by rfl⟩ : syracuseStep 160805 = 30151) (by norm_num)
theorem B160829 : Blo 103782 160829 := bbase (se 3 (by rfl) ⟨30155, by rfl⟩ : syracuseStep 160829 = 60311) (by norm_num)
theorem B128065 : Blo 103782 128065 := bbase (se 2 (by rfl) ⟨48024, by rfl⟩ : syracuseStep 128065 = 96049) (by norm_num)
theorem B160853 : Blo 103782 160853 := bbase (se 8 (by rfl) ⟨942, by rfl⟩ : syracuseStep 160853 = 1885) (by norm_num)
theorem B160877 : Blo 103782 160877 := bbase (se 3 (by rfl) ⟨30164, by rfl⟩ : syracuseStep 160877 = 60329) (by norm_num)
theorem B160901 : Blo 103782 160901 := bbase (se 4 (by rfl) ⟨15084, by rfl⟩ : syracuseStep 160901 = 30169) (by norm_num)
theorem B1766549 : Blo 103782 1766549 := bbase (se 6 (by rfl) ⟨41403, by rfl⟩ : syracuseStep 1766549 = 82807) (by norm_num)
theorem B160925 : Blo 103782 160925 := bbase (se 3 (by rfl) ⟨30173, by rfl⟩ : syracuseStep 160925 = 60347) (by norm_num)
theorem B160949 : Blo 103782 160949 := bbase (se 5 (by rfl) ⟨7544, by rfl⟩ : syracuseStep 160949 = 15089) (by norm_num)
theorem B160973 : Blo 103782 160973 := bbase (se 3 (by rfl) ⟨30182, by rfl⟩ : syracuseStep 160973 = 60365) (by norm_num)
theorem B324821 : Blo 103782 324821 := bbase (se 7 (by rfl) ⟨3806, by rfl⟩ : syracuseStep 324821 = 7613) (by norm_num)
theorem B160997 : Blo 103782 160997 := bbase (se 4 (by rfl) ⟨15093, by rfl⟩ : syracuseStep 160997 = 30187) (by norm_num)
theorem B161021 : Blo 103782 161021 := bbase (se 3 (by rfl) ⟨30191, by rfl⟩ : syracuseStep 161021 = 60383) (by norm_num)
theorem B161045 : Blo 103782 161045 := bbase (se 6 (by rfl) ⟨3774, by rfl⟩ : syracuseStep 161045 = 7549) (by norm_num)
theorem B161069 : Blo 103782 161069 := bbase (se 3 (by rfl) ⟨30200, by rfl⟩ : syracuseStep 161069 = 60401) (by norm_num)
theorem B161093 : Blo 103782 161093 := bbase (se 4 (by rfl) ⟨15102, by rfl⟩ : syracuseStep 161093 = 30205) (by norm_num)
theorem B161117 : Blo 103782 161117 := bbase (se 3 (by rfl) ⟨30209, by rfl⟩ : syracuseStep 161117 = 60419) (by norm_num)
theorem B357749 : Blo 103782 357749 := bbase (se 5 (by rfl) ⟨16769, by rfl⟩ : syracuseStep 357749 = 33539) (by norm_num)
theorem B161141 : Blo 103782 161141 := bbase (se 5 (by rfl) ⟨7553, by rfl⟩ : syracuseStep 161141 = 15107) (by norm_num)
theorem B161165 : Blo 103782 161165 := bbase (se 3 (by rfl) ⟨30218, by rfl⟩ : syracuseStep 161165 = 60437) (by norm_num)
theorem B161189 : Blo 103782 161189 := bbase (se 4 (by rfl) ⟨15111, by rfl⟩ : syracuseStep 161189 = 30223) (by norm_num)
theorem B390581 : Blo 103782 390581 := bbase (se 5 (by rfl) ⟨18308, by rfl⟩ : syracuseStep 390581 = 36617) (by norm_num)
theorem B161213 : Blo 103782 161213 := bbase (se 3 (by rfl) ⟨30227, by rfl⟩ : syracuseStep 161213 = 60455) (by norm_num)
theorem B161237 : Blo 103782 161237 := bbase (se 7 (by rfl) ⟨1889, by rfl⟩ : syracuseStep 161237 = 3779) (by norm_num)
theorem B161261 : Blo 103782 161261 := bbase (se 3 (by rfl) ⟨30236, by rfl⟩ : syracuseStep 161261 = 60473) (by norm_num)
theorem B161285 : Blo 103782 161285 := bbase (se 4 (by rfl) ⟨15120, by rfl⟩ : syracuseStep 161285 = 30241) (by norm_num)
theorem B161309 : Blo 103782 161309 := bbase (se 3 (by rfl) ⟨30245, by rfl⟩ : syracuseStep 161309 = 60491) (by norm_num)
theorem B161333 : Blo 103782 161333 := bbase (se 5 (by rfl) ⟨7562, by rfl⟩ : syracuseStep 161333 = 15125) (by norm_num)
theorem B161357 : Blo 103782 161357 := bbase (se 3 (by rfl) ⟨30254, by rfl⟩ : syracuseStep 161357 = 60509) (by norm_num)
theorem B161381 : Blo 103782 161381 := bbase (se 4 (by rfl) ⟨15129, by rfl⟩ : syracuseStep 161381 = 30259) (by norm_num)
theorem B161389 : Blo 103782 161389 := bbase (se 3 (by rfl) ⟨30260, by rfl⟩ : syracuseStep 161389 = 60521) (by norm_num)
theorem B161405 : Blo 103782 161405 := bbase (se 3 (by rfl) ⟨30263, by rfl⟩ : syracuseStep 161405 = 60527) (by norm_num)
theorem B358037 : Blo 103782 358037 := bbase (se 6 (by rfl) ⟨8391, by rfl⟩ : syracuseStep 358037 = 16783) (by norm_num)
theorem B161429 : Blo 103782 161429 := bbase (se 6 (by rfl) ⟨3783, by rfl⟩ : syracuseStep 161429 = 7567) (by norm_num)
theorem B161453 : Blo 103782 161453 := bbase (se 3 (by rfl) ⟨30272, by rfl⟩ : syracuseStep 161453 = 60545) (by norm_num)
theorem B259781 : Blo 103782 259781 := bbase (se 4 (by rfl) ⟨24354, by rfl⟩ : syracuseStep 259781 = 48709) (by norm_num)
theorem B161477 : Blo 103782 161477 := bbase (se 4 (by rfl) ⟨15138, by rfl⟩ : syracuseStep 161477 = 30277) (by norm_num)
theorem B161501 : Blo 103782 161501 := bbase (se 3 (by rfl) ⟨30281, by rfl⟩ : syracuseStep 161501 = 60563) (by norm_num)
theorem B161525 : Blo 103782 161525 := bbase (se 5 (by rfl) ⟨7571, by rfl⟩ : syracuseStep 161525 = 15143) (by norm_num)
theorem B161549 : Blo 103782 161549 := bbase (se 3 (by rfl) ⟨30290, by rfl⟩ : syracuseStep 161549 = 60581) (by norm_num)
theorem B358181 : Blo 103782 358181 := bbase (se 4 (by rfl) ⟨33579, by rfl⟩ : syracuseStep 358181 = 67159) (by norm_num)
theorem B161573 : Blo 103782 161573 := bbase (se 4 (by rfl) ⟨15147, by rfl⟩ : syracuseStep 161573 = 30295) (by norm_num)
theorem B161597 : Blo 103782 161597 := bbase (se 3 (by rfl) ⟨30299, by rfl⟩ : syracuseStep 161597 = 60599) (by norm_num)
theorem B227141 : Blo 103782 227141 := bbase (se 4 (by rfl) ⟨21294, by rfl⟩ : syracuseStep 227141 = 42589) (by norm_num)
theorem B161621 : Blo 103782 161621 := bbase (se 9 (by rfl) ⟨473, by rfl⟩ : syracuseStep 161621 = 947) (by norm_num)
theorem B161645 : Blo 103782 161645 := bbase (se 3 (by rfl) ⟨30308, by rfl⟩ : syracuseStep 161645 = 60617) (by norm_num)
theorem B161669 : Blo 103782 161669 := bbase (se 4 (by rfl) ⟨15156, by rfl⟩ : syracuseStep 161669 = 30313) (by norm_num)
theorem B227261 : Blo 103782 227261 := bbase (se 3 (by rfl) ⟨42611, by rfl⟩ : syracuseStep 227261 = 85223) (by norm_num)
theorem B358613 : Blo 103782 358613 := bbase (se 7 (by rfl) ⟨4202, by rfl⟩ : syracuseStep 358613 = 8405) (by norm_num)
theorem B129281 : Blo 103782 129281 := bbase (se 2 (by rfl) ⟨48480, by rfl⟩ : syracuseStep 129281 = 96961) (by norm_num)
theorem B391493 : Blo 103782 391493 := bbase (se 4 (by rfl) ⟨36702, by rfl⟩ : syracuseStep 391493 = 73405) (by norm_num)
theorem B1603925 : Blo 103782 1603925 := bbase (se 10 (by rfl) ⟨2349, by rfl⟩ : syracuseStep 1603925 = 4699) (by norm_num)
theorem B129449 : Blo 103782 129449 := bbase (se 2 (by rfl) ⟨48543, by rfl⟩ : syracuseStep 129449 = 97087) (by norm_num)
theorem B227893 : Blo 103782 227893 := bbase (se 5 (by rfl) ⟨10682, by rfl⟩ : syracuseStep 227893 = 21365) (by norm_num)
theorem B359045 : Blo 103782 359045 := bbase (se 4 (by rfl) ⟨33660, by rfl⟩ : syracuseStep 359045 = 67321) (by norm_num)
theorem B129745 : Blo 103782 129745 := bbase (se 2 (by rfl) ⟨48654, by rfl⟩ : syracuseStep 129745 = 97309) (by norm_num)
theorem B326405 : Blo 103782 326405 := bbase (se 4 (by rfl) ⟨30600, by rfl⟩ : syracuseStep 326405 = 61201) (by norm_num)
theorem B162605 : Blo 103782 162605 := bbase (se 3 (by rfl) ⟨30488, by rfl⟩ : syracuseStep 162605 = 60977) (by norm_num)
theorem B1014677 : Blo 103782 1014677 := bbase (se 6 (by rfl) ⟨23781, by rfl⟩ : syracuseStep 1014677 = 47563) (by norm_num)
theorem B359477 : Blo 103782 359477 := bbase (se 5 (by rfl) ⟨16850, by rfl⟩ : syracuseStep 359477 = 33701) (by norm_num)
theorem B457973 : Blo 103782 457973 := bbase (se 5 (by rfl) ⟨21467, by rfl⟩ : syracuseStep 457973 = 42935) (by norm_num)
theorem B228781 : Blo 103782 228781 := bbase (se 3 (by rfl) ⟨42896, by rfl⟩ : syracuseStep 228781 = 85793) (by norm_num)
theorem B359909 : Blo 103782 359909 := bbase (se 4 (by rfl) ⟨33741, by rfl⟩ : syracuseStep 359909 = 67483) (by norm_num)
theorem B228901 : Blo 103782 228901 := bbase (se 4 (by rfl) ⟨21459, by rfl⟩ : syracuseStep 228901 = 42919) (by norm_num)
theorem B1375829 : Blo 103782 1375829 := bbase (se 8 (by rfl) ⟨8061, by rfl⟩ : syracuseStep 1375829 = 16123) (by norm_num)
theorem B261829 : Blo 103782 261829 := bbase (se 4 (by rfl) ⟨24546, by rfl⟩ : syracuseStep 261829 = 49093) (by norm_num)
theorem B229157 : Blo 103782 229157 := bbase (se 4 (by rfl) ⟨21483, by rfl⟩ : syracuseStep 229157 = 42967) (by norm_num)
theorem B360341 : Blo 103782 360341 := bbase (se 6 (by rfl) ⟨8445, by rfl⟩ : syracuseStep 360341 = 16891) (by norm_num)
theorem B360389 : Blo 103782 360389 := bbase (se 4 (by rfl) ⟨33786, by rfl⟩ : syracuseStep 360389 = 67573) (by norm_num)
theorem B688085 : Blo 103782 688085 := bbase (se 7 (by rfl) ⟨8063, by rfl⟩ : syracuseStep 688085 = 16127) (by norm_num)
theorem B360557 : Blo 103782 360557 := bstep (se 3 (by rfl) ⟨67604, by rfl⟩ : syracuseStep 360557 = 135209) B135209
theorem B360611 : Blo 103782 360611 := bstep (se 1 (by rfl) ⟨270458, by rfl⟩ : syracuseStep 360611 = 540917) B540917
theorem B360881 : Blo 103782 360881 := bstep (se 2 (by rfl) ⟨135330, by rfl⟩ : syracuseStep 360881 = 270661) B270661
theorem B131539 : Blo 103782 131539 := bstep (se 1 (by rfl) ⟨98654, by rfl⟩ : syracuseStep 131539 = 197309) B197309
theorem B131635 : Blo 103782 131635 := bstep (se 1 (by rfl) ⟨98726, by rfl⟩ : syracuseStep 131635 = 197453) B197453
theorem B262723 : Blo 103782 262723 := bstep (se 1 (by rfl) ⟨197042, by rfl⟩ : syracuseStep 262723 = 394085) B394085
theorem B229969 : Blo 103782 229969 := bstep (se 2 (by rfl) ⟨86238, by rfl⟩ : syracuseStep 229969 = 172477) B172477
theorem B262865 : Blo 103782 262865 := bstep (se 2 (by rfl) ⟨98574, by rfl⟩ : syracuseStep 262865 = 197149) B197149
theorem B164771 : Blo 103782 164771 := bstep (se 1 (by rfl) ⟨123578, by rfl⟩ : syracuseStep 164771 = 247157) B247157
theorem B361421 : Blo 103782 361421 := bstep (se 3 (by rfl) ⟨67766, by rfl⟩ : syracuseStep 361421 = 135533) B135533
theorem B197635 : Blo 103782 197635 := bstep (se 1 (by rfl) ⟨148226, by rfl⟩ : syracuseStep 197635 = 296453) B296453
theorem B361475 : Blo 103782 361475 := bstep (se 1 (by rfl) ⟨271106, by rfl⟩ : syracuseStep 361475 = 542213) B542213
theorem B394253 : Blo 103782 394253 := bstep (se 3 (by rfl) ⟨73922, by rfl⟩ : syracuseStep 394253 = 147845) B147845
theorem B132131 : Blo 103782 132131 := bstep (se 1 (by rfl) ⟨99098, by rfl⟩ : syracuseStep 132131 = 198197) B198197
theorem B197795 : Blo 103782 197795 := bstep (se 1 (by rfl) ⟨148346, by rfl⟩ : syracuseStep 197795 = 296693) B296693
theorem B361745 : Blo 103782 361745 := bstep (se 2 (by rfl) ⟨135654, by rfl⟩ : syracuseStep 361745 = 271309) B271309
theorem B296237 : Blo 103782 296237 := bstep (se 3 (by rfl) ⟨55544, by rfl⟩ : syracuseStep 296237 = 111089) B111089
theorem B165281 : Blo 103782 165281 := bstep (se 2 (by rfl) ⟨61980, by rfl⟩ : syracuseStep 165281 = 123961) B123961
theorem B296419 : Blo 103782 296419 := bstep (se 1 (by rfl) ⟨222314, by rfl⟩ : syracuseStep 296419 = 444629) B444629
theorem B263857 : Blo 103782 263857 := bstep (se 2 (by rfl) ⟨98946, by rfl⟩ : syracuseStep 263857 = 197893) B197893
theorem B132835 : Blo 103782 132835 := bstep (se 1 (by rfl) ⟨99626, by rfl⟩ : syracuseStep 132835 = 199253) B199253
theorem B362285 : Blo 103782 362285 := bstep (se 3 (by rfl) ⟨67928, by rfl⟩ : syracuseStep 362285 = 135857) B135857
theorem B395057 : Blo 103782 395057 := bstep (se 2 (by rfl) ⟨148146, by rfl⟩ : syracuseStep 395057 = 296293) B296293
theorem B132931 : Blo 103782 132931 := bstep (se 1 (by rfl) ⟨99698, by rfl⟩ : syracuseStep 132931 = 199397) B199397
theorem B362339 : Blo 103782 362339 := bstep (se 1 (by rfl) ⟨271754, by rfl⟩ : syracuseStep 362339 = 543509) B543509
theorem B198577 : Blo 103782 198577 := bstep (se 2 (by rfl) ⟨74466, by rfl⟩ : syracuseStep 198577 = 148933) B148933
theorem B264131 : Blo 103782 264131 := bstep (se 1 (by rfl) ⟨198098, by rfl⟩ : syracuseStep 264131 = 396197) B396197
theorem B296909 : Blo 103782 296909 := bstep (se 3 (by rfl) ⟨55670, by rfl⟩ : syracuseStep 296909 = 111341) B111341
theorem B591857 : Blo 103782 591857 := bstep (se 2 (by rfl) ⟨221946, by rfl⟩ : syracuseStep 591857 = 443893) B443893
theorem B362609 : Blo 103782 362609 := bstep (se 2 (by rfl) ⟨135978, by rfl⟩ : syracuseStep 362609 = 271957) B271957
theorem B264323 : Blo 103782 264323 := bstep (se 1 (by rfl) ⟨198242, by rfl⟩ : syracuseStep 264323 = 396485) B396485
theorem B526499 : Blo 103782 526499 := bstep (se 1 (by rfl) ⟨394874, by rfl⟩ : syracuseStep 526499 = 789749) B789749
theorem B198865 : Blo 103782 198865 := bstep (se 2 (by rfl) ⟨74574, by rfl⟩ : syracuseStep 198865 = 149149) B149149
theorem B133427 : Blo 103782 133427 := bstep (se 1 (by rfl) ⟨100070, by rfl⟩ : syracuseStep 133427 = 200141) B200141
theorem B919907 : Blo 103782 919907 := bstep (se 1 (by rfl) ⟨689930, by rfl⟩ : syracuseStep 919907 = 1379861) B1379861
theorem B690545 : Blo 103782 690545 := bstep (se 2 (by rfl) ⟨258954, by rfl⟩ : syracuseStep 690545 = 517909) B517909
theorem B395725 : Blo 103782 395725 := bstep (se 3 (by rfl) ⟨74198, by rfl⟩ : syracuseStep 395725 = 148397) B148397
theorem B756337 : Blo 103782 756337 := bstep (se 2 (by rfl) ⟨283626, by rfl⟩ : syracuseStep 756337 = 567253) B567253
theorem B166531 : Blo 103782 166531 := bstep (se 1 (by rfl) ⟨124898, by rfl⟩ : syracuseStep 166531 = 249797) B249797
theorem B363149 : Blo 103782 363149 := bstep (se 3 (by rfl) ⟨68090, by rfl⟩ : syracuseStep 363149 = 136181) B136181
theorem B1215157 : Blo 103782 1215157 := bstep (se 5 (by rfl) ⟨56960, by rfl⟩ : syracuseStep 1215157 = 113921) B113921
theorem B363203 : Blo 103782 363203 := bstep (se 1 (by rfl) ⟨272402, by rfl⟩ : syracuseStep 363203 = 544805) B544805
theorem B1018595 : Blo 103782 1018595 := bstep (se 1 (by rfl) ⟨763946, by rfl⟩ : syracuseStep 1018595 = 1527893) B1527893
theorem B1084229 : Blo 103782 1084229 := bstep (se 4 (by rfl) ⟨101646, by rfl⟩ : syracuseStep 1084229 = 203293) B203293
theorem B527309 : Blo 103782 527309 := bstep (se 3 (by rfl) ⟨98870, by rfl⟩ : syracuseStep 527309 = 197741) B197741
theorem B363473 : Blo 103782 363473 := bstep (se 2 (by rfl) ⟨136302, by rfl⟩ : syracuseStep 363473 = 272605) B272605
theorem B134131 : Blo 103782 134131 := bstep (se 1 (by rfl) ⟨100598, by rfl⟩ : syracuseStep 134131 = 201197) B201197
theorem B265265 : Blo 103782 265265 := bstep (se 2 (by rfl) ⟨99474, by rfl⟩ : syracuseStep 265265 = 198949) B198949
theorem B134227 : Blo 103782 134227 := bstep (se 1 (by rfl) ⟨100670, by rfl⟩ : syracuseStep 134227 = 201341) B201341
theorem B265315 : Blo 103782 265315 := bstep (se 1 (by rfl) ⟨198986, by rfl⟩ : syracuseStep 265315 = 397973) B397973
theorem B298093 : Blo 103782 298093 := bstep (se 3 (by rfl) ⟨55892, by rfl⟩ : syracuseStep 298093 = 111785) B111785
theorem B396515 : Blo 103782 396515 := bstep (se 1 (by rfl) ⟨297386, by rfl⟩ : syracuseStep 396515 = 594773) B594773
theorem B265457 : Blo 103782 265457 := bstep (se 2 (by rfl) ⟨99546, by rfl⟩ : syracuseStep 265457 = 199093) B199093
theorem B199921 : Blo 103782 199921 := bstep (se 2 (by rfl) ⟨74970, by rfl⟩ : syracuseStep 199921 = 149941) B149941
theorem B167203 : Blo 103782 167203 := bstep (se 1 (by rfl) ⟨125402, by rfl⟩ : syracuseStep 167203 = 250805) B250805
theorem B593315 : Blo 103782 593315 := bstep (se 1 (by rfl) ⟨444986, by rfl⟩ : syracuseStep 593315 = 889973) B889973
theorem B1215971 : Blo 103782 1215971 := bstep (se 1 (by rfl) ⟨911978, by rfl⟩ : syracuseStep 1215971 = 1823957) B1823957
theorem B134723 : Blo 103782 134723 := bstep (se 1 (by rfl) ⟨101042, by rfl⟩ : syracuseStep 134723 = 202085) B202085
theorem B200323 : Blo 103782 200323 := bstep (se 1 (by rfl) ⟨150242, by rfl⟩ : syracuseStep 200323 = 300485) B300485
theorem B200369 : Blo 103782 200369 := bstep (se 2 (by rfl) ⟨75138, by rfl⟩ : syracuseStep 200369 = 150277) B150277
theorem B167665 : Blo 103782 167665 := bstep (se 2 (by rfl) ⟨62874, by rfl⟩ : syracuseStep 167665 = 125749) B125749
theorem B691973 : Blo 103782 691973 := bstep (se 4 (by rfl) ⟨64872, by rfl⟩ : syracuseStep 691973 = 129745) B129745
theorem B167761 : Blo 103782 167761 := bstep (se 2 (by rfl) ⟨62910, by rfl⟩ : syracuseStep 167761 = 125821) B125821
theorem B397169 : Blo 103782 397169 := bstep (se 2 (by rfl) ⟨148938, by rfl⟩ : syracuseStep 397169 = 297877) B297877
theorem B200657 : Blo 103782 200657 := bstep (se 2 (by rfl) ⟨75246, by rfl⟩ : syracuseStep 200657 = 150493) B150493
theorem B167921 : Blo 103782 167921 := bstep (se 2 (by rfl) ⟨62970, by rfl⟩ : syracuseStep 167921 = 125941) B125941
theorem B233585 : Blo 103782 233585 := bstep (se 2 (by rfl) ⟨87594, by rfl⟩ : syracuseStep 233585 = 175189) B175189
theorem B233603 : Blo 103782 233603 := bstep (se 1 (by rfl) ⟨175202, by rfl⟩ : syracuseStep 233603 = 350405) B350405
theorem B2330765 : Blo 103782 2330765 := bstep (se 3 (by rfl) ⟨437018, by rfl⟩ : syracuseStep 2330765 = 874037) B874037
theorem B299153 : Blo 103782 299153 := bstep (se 2 (by rfl) ⟨112182, by rfl⟩ : syracuseStep 299153 = 224365) B224365
theorem B692387 : Blo 103782 692387 := bstep (se 1 (by rfl) ⟨519290, by rfl⟩ : syracuseStep 692387 = 1038581) B1038581
theorem B266449 : Blo 103782 266449 := bstep (se 2 (by rfl) ⟨99918, by rfl⟩ : syracuseStep 266449 = 199837) B199837
theorem B135427 : Blo 103782 135427 := bstep (se 1 (by rfl) ⟨101570, by rfl⟩ : syracuseStep 135427 = 203141) B203141
theorem B1544501 : Blo 103782 1544501 := bstep (se 5 (by rfl) ⟨72398, by rfl⟩ : syracuseStep 1544501 = 144797) B144797
theorem B364877 : Blo 103782 364877 := bstep (se 3 (by rfl) ⟨68414, by rfl⟩ : syracuseStep 364877 = 136829) B136829
theorem B135523 : Blo 103782 135523 := bstep (se 1 (by rfl) ⟨101642, by rfl⟩ : syracuseStep 135523 = 203285) B203285
theorem B594317 : Blo 103782 594317 := bstep (se 3 (by rfl) ⟨111434, by rfl⟩ : syracuseStep 594317 = 222869) B222869
theorem B233873 : Blo 103782 233873 := bstep (se 2 (by rfl) ⟨87702, by rfl⟩ : syracuseStep 233873 = 175405) B175405
theorem B233891 : Blo 103782 233891 := bstep (se 1 (by rfl) ⟨175418, by rfl⟩ : syracuseStep 233891 = 350837) B350837
theorem B266723 : Blo 103782 266723 := bstep (se 1 (by rfl) ⟨200042, by rfl⟩ : syracuseStep 266723 = 400085) B400085
theorem B692749 : Blo 103782 692749 := bstep (se 3 (by rfl) ⟨129890, by rfl⟩ : syracuseStep 692749 = 259781) B259781
theorem B4133429 : Blo 103782 4133429 := bstep (se 5 (by rfl) ⟨193754, by rfl⟩ : syracuseStep 4133429 = 387509) B387509
theorem B266915 : Blo 103782 266915 := bstep (se 1 (by rfl) ⟨200186, by rfl⟩ : syracuseStep 266915 = 400373) B400373
theorem B201379 : Blo 103782 201379 := bstep (se 1 (by rfl) ⟨151034, by rfl⟩ : syracuseStep 201379 = 302069) B302069
theorem B234161 : Blo 103782 234161 := bstep (se 2 (by rfl) ⟨87810, by rfl⟩ : syracuseStep 234161 = 175621) B175621
theorem B234179 : Blo 103782 234179 := bstep (se 1 (by rfl) ⟨175634, by rfl⟩ : syracuseStep 234179 = 351269) B351269
theorem B201457 : Blo 103782 201457 := bstep (se 2 (by rfl) ⟨75546, by rfl⟩ : syracuseStep 201457 = 151093) B151093
theorem B332561 : Blo 103782 332561 := bstep (se 2 (by rfl) ⟨124710, by rfl⟩ : syracuseStep 332561 = 249421) B249421
theorem B299825 : Blo 103782 299825 := bstep (se 2 (by rfl) ⟨112434, by rfl⟩ : syracuseStep 299825 = 224869) B224869
theorem B136019 : Blo 103782 136019 := bstep (se 1 (by rfl) ⟨102014, by rfl⟩ : syracuseStep 136019 = 204029) B204029
theorem B234449 : Blo 103782 234449 := bstep (se 2 (by rfl) ⟨87918, by rfl⟩ : syracuseStep 234449 = 175837) B175837
theorem B234467 : Blo 103782 234467 := bstep (se 1 (by rfl) ⟨175850, by rfl⟩ : syracuseStep 234467 = 351701) B351701
theorem B201827 : Blo 103782 201827 := bstep (se 1 (by rfl) ⟨151370, by rfl⟩ : syracuseStep 201827 = 302741) B302741
theorem B791693 : Blo 103782 791693 := bstep (se 3 (by rfl) ⟨148442, by rfl⟩ : syracuseStep 791693 = 296885) B296885
theorem B234737 : Blo 103782 234737 := bstep (se 2 (by rfl) ⟨88026, by rfl⟩ : syracuseStep 234737 = 176053) B176053
theorem B234755 : Blo 103782 234755 := bstep (se 1 (by rfl) ⟨176066, by rfl⟩ : syracuseStep 234755 = 352133) B352133
theorem B398627 : Blo 103782 398627 := bstep (se 1 (by rfl) ⟨298970, by rfl⟩ : syracuseStep 398627 = 597941) B597941
theorem B398641 : Blo 103782 398641 := bstep (se 2 (by rfl) ⟨149490, by rfl⟩ : syracuseStep 398641 = 298981) B298981
theorem B103795 : Blo 103782 103795 := bstep (se 1 (by rfl) ⟨77846, by rfl⟩ : syracuseStep 103795 = 155693) B155693
theorem B103811 : Blo 103782 103811 := bstep (se 1 (by rfl) ⟨77858, by rfl⟩ : syracuseStep 103811 = 155717) B155717
theorem B202115 : Blo 103782 202115 := bstep (se 1 (by rfl) ⟨151586, by rfl⟩ : syracuseStep 202115 = 303173) B303173
theorem B103827 : Blo 103782 103827 := bstep (se 1 (by rfl) ⟨77870, by rfl⟩ : syracuseStep 103827 = 155741) B155741
theorem B103843 : Blo 103782 103843 := bstep (se 1 (by rfl) ⟨77882, by rfl⟩ : syracuseStep 103843 = 155765) B155765
theorem B103859 : Blo 103782 103859 := bstep (se 1 (by rfl) ⟨77894, by rfl⟩ : syracuseStep 103859 = 155789) B155789
theorem B103875 : Blo 103782 103875 := bstep (se 1 (by rfl) ⟨77906, by rfl⟩ : syracuseStep 103875 = 155813) B155813
theorem B103891 : Blo 103782 103891 := bstep (se 1 (by rfl) ⟨77918, by rfl⟩ : syracuseStep 103891 = 155837) B155837
theorem B103907 : Blo 103782 103907 := bstep (se 1 (by rfl) ⟨77930, by rfl⟩ : syracuseStep 103907 = 155861) B155861
theorem B103923 : Blo 103782 103923 := bstep (se 1 (by rfl) ⟨77942, by rfl⟩ : syracuseStep 103923 = 155885) B155885
theorem B103939 : Blo 103782 103939 := bstep (se 1 (by rfl) ⟨77954, by rfl⟩ : syracuseStep 103939 = 155909) B155909
theorem B235025 : Blo 103782 235025 := bstep (se 2 (by rfl) ⟨88134, by rfl⟩ : syracuseStep 235025 = 176269) B176269
theorem B103955 : Blo 103782 103955 := bstep (se 1 (by rfl) ⟨77966, by rfl⟩ : syracuseStep 103955 = 155933) B155933
theorem B103971 : Blo 103782 103971 := bstep (se 1 (by rfl) ⟨77978, by rfl⟩ : syracuseStep 103971 = 155957) B155957
theorem B235043 : Blo 103782 235043 := bstep (se 1 (by rfl) ⟨176282, by rfl⟩ : syracuseStep 235043 = 352565) B352565
theorem B103987 : Blo 103782 103987 := bstep (se 1 (by rfl) ⟨77990, by rfl⟩ : syracuseStep 103987 = 155981) B155981
theorem B104003 : Blo 103782 104003 := bstep (se 1 (by rfl) ⟨78002, by rfl⟩ : syracuseStep 104003 = 156005) B156005
theorem B300611 : Blo 103782 300611 := bstep (se 1 (by rfl) ⟨225458, by rfl⟩ : syracuseStep 300611 = 450917) B450917
theorem B267857 : Blo 103782 267857 := bstep (se 2 (by rfl) ⟨100446, by rfl⟩ : syracuseStep 267857 = 200893) B200893
theorem B104019 : Blo 103782 104019 := bstep (se 1 (by rfl) ⟨78014, by rfl⟩ : syracuseStep 104019 = 156029) B156029
theorem B104035 : Blo 103782 104035 := bstep (se 1 (by rfl) ⟨78026, by rfl⟩ : syracuseStep 104035 = 156053) B156053
theorem B104051 : Blo 103782 104051 := bstep (se 1 (by rfl) ⟨78038, by rfl⟩ : syracuseStep 104051 = 156077) B156077
theorem B104067 : Blo 103782 104067 := bstep (se 1 (by rfl) ⟨78050, by rfl⟩ : syracuseStep 104067 = 156101) B156101
theorem B267907 : Blo 103782 267907 := bstep (se 1 (by rfl) ⟨200930, by rfl⟩ : syracuseStep 267907 = 401861) B401861
theorem B104083 : Blo 103782 104083 := bstep (se 1 (by rfl) ⟨78062, by rfl⟩ : syracuseStep 104083 = 156125) B156125
theorem B104099 : Blo 103782 104099 := bstep (se 1 (by rfl) ⟨78074, by rfl⟩ : syracuseStep 104099 = 156149) B156149
theorem B104115 : Blo 103782 104115 := bstep (se 1 (by rfl) ⟨78086, by rfl⟩ : syracuseStep 104115 = 156173) B156173
theorem B104131 : Blo 103782 104131 := bstep (se 1 (by rfl) ⟨78098, by rfl⟩ : syracuseStep 104131 = 156197) B156197
theorem B267985 : Blo 103782 267985 := bstep (se 2 (by rfl) ⟨100494, by rfl⟩ : syracuseStep 267985 = 200989) B200989
theorem B104147 : Blo 103782 104147 := bstep (se 1 (by rfl) ⟨78110, by rfl⟩ : syracuseStep 104147 = 156221) B156221
theorem B104163 : Blo 103782 104163 := bstep (se 1 (by rfl) ⟨78122, by rfl⟩ : syracuseStep 104163 = 156245) B156245
theorem B694001 : Blo 103782 694001 := bstep (se 2 (by rfl) ⟨260250, by rfl⟩ : syracuseStep 694001 = 520501) B520501
theorem B104179 : Blo 103782 104179 := bstep (se 1 (by rfl) ⟨78134, by rfl⟩ : syracuseStep 104179 = 156269) B156269
theorem B169715 : Blo 103782 169715 := bstep (se 1 (by rfl) ⟨127286, by rfl⟩ : syracuseStep 169715 = 254573) B254573
theorem B104195 : Blo 103782 104195 := bstep (se 1 (by rfl) ⟨78146, by rfl⟩ : syracuseStep 104195 = 156293) B156293
theorem B268049 : Blo 103782 268049 := bstep (se 2 (by rfl) ⟨100518, by rfl⟩ : syracuseStep 268049 = 201037) B201037
theorem B104211 : Blo 103782 104211 := bstep (se 1 (by rfl) ⟨78158, by rfl⟩ : syracuseStep 104211 = 156317) B156317
theorem B104227 : Blo 103782 104227 := bstep (se 1 (by rfl) ⟨78170, by rfl⟩ : syracuseStep 104227 = 156341) B156341
theorem B235313 : Blo 103782 235313 := bstep (se 2 (by rfl) ⟨88242, by rfl⟩ : syracuseStep 235313 = 176485) B176485
theorem B530225 : Blo 103782 530225 := bstep (se 2 (by rfl) ⟨198834, by rfl⟩ : syracuseStep 530225 = 397669) B397669
theorem B104243 : Blo 103782 104243 := bstep (se 1 (by rfl) ⟨78182, by rfl⟩ : syracuseStep 104243 = 156365) B156365
theorem B104259 : Blo 103782 104259 := bstep (se 1 (by rfl) ⟨78194, by rfl⟩ : syracuseStep 104259 = 156389) B156389
theorem B235331 : Blo 103782 235331 := bstep (se 1 (by rfl) ⟨176498, by rfl⟩ : syracuseStep 235331 = 352997) B352997
theorem B104275 : Blo 103782 104275 := bstep (se 1 (by rfl) ⟨78206, by rfl⟩ : syracuseStep 104275 = 156413) B156413
theorem B104291 : Blo 103782 104291 := bstep (se 1 (by rfl) ⟨78218, by rfl⟩ : syracuseStep 104291 = 156437) B156437
theorem B104307 : Blo 103782 104307 := bstep (se 1 (by rfl) ⟨78230, by rfl⟩ : syracuseStep 104307 = 156461) B156461
theorem B104323 : Blo 103782 104323 := bstep (se 1 (by rfl) ⟨78242, by rfl⟩ : syracuseStep 104323 = 156485) B156485
theorem B300941 : Blo 103782 300941 := bstep (se 3 (by rfl) ⟨56426, by rfl⟩ : syracuseStep 300941 = 112853) B112853
theorem B104339 : Blo 103782 104339 := bstep (se 1 (by rfl) ⟨78254, by rfl⟩ : syracuseStep 104339 = 156509) B156509
theorem B104355 : Blo 103782 104355 := bstep (se 1 (by rfl) ⟨78266, by rfl⟩ : syracuseStep 104355 = 156533) B156533
theorem B104371 : Blo 103782 104371 := bstep (se 1 (by rfl) ⟨78278, by rfl⟩ : syracuseStep 104371 = 156557) B156557
theorem B104387 : Blo 103782 104387 := bstep (se 1 (by rfl) ⟨78290, by rfl⟩ : syracuseStep 104387 = 156581) B156581
theorem B301009 : Blo 103782 301009 := bstep (se 2 (by rfl) ⟨112878, by rfl⟩ : syracuseStep 301009 = 225757) B225757
theorem B104403 : Blo 103782 104403 := bstep (se 1 (by rfl) ⟨78302, by rfl⟩ : syracuseStep 104403 = 156605) B156605
theorem B104419 : Blo 103782 104419 := bstep (se 1 (by rfl) ⟨78314, by rfl⟩ : syracuseStep 104419 = 156629) B156629
theorem B104435 : Blo 103782 104435 := bstep (se 1 (by rfl) ⟨78326, by rfl⟩ : syracuseStep 104435 = 156653) B156653
theorem B104451 : Blo 103782 104451 := bstep (se 1 (by rfl) ⟨78338, by rfl⟩ : syracuseStep 104451 = 156677) B156677
theorem B104467 : Blo 103782 104467 := bstep (se 1 (by rfl) ⟨78350, by rfl⟩ : syracuseStep 104467 = 156701) B156701
theorem B104483 : Blo 103782 104483 := bstep (se 1 (by rfl) ⟨78362, by rfl⟩ : syracuseStep 104483 = 156725) B156725
theorem B104499 : Blo 103782 104499 := bstep (se 1 (by rfl) ⟨78374, by rfl⟩ : syracuseStep 104499 = 156749) B156749
theorem B104515 : Blo 103782 104515 := bstep (se 1 (by rfl) ⟨78386, by rfl⟩ : syracuseStep 104515 = 156773) B156773
theorem B235601 : Blo 103782 235601 := bstep (se 2 (by rfl) ⟨88350, by rfl⟩ : syracuseStep 235601 = 176701) B176701
theorem B104531 : Blo 103782 104531 := bstep (se 1 (by rfl) ⟨78398, by rfl⟩ : syracuseStep 104531 = 156797) B156797
theorem B104547 : Blo 103782 104547 := bstep (se 1 (by rfl) ⟨78410, by rfl⟩ : syracuseStep 104547 = 156821) B156821
theorem B235619 : Blo 103782 235619 := bstep (se 1 (by rfl) ⟨176714, by rfl⟩ : syracuseStep 235619 = 353429) B353429
theorem B104563 : Blo 103782 104563 := bstep (se 1 (by rfl) ⟨78422, by rfl⟩ : syracuseStep 104563 = 156845) B156845
theorem B104579 : Blo 103782 104579 := bstep (se 1 (by rfl) ⟨78434, by rfl⟩ : syracuseStep 104579 = 156869) B156869
theorem B104595 : Blo 103782 104595 := bstep (se 1 (by rfl) ⟨78446, by rfl⟩ : syracuseStep 104595 = 156893) B156893
theorem B104611 : Blo 103782 104611 := bstep (se 1 (by rfl) ⟨78458, by rfl⟩ : syracuseStep 104611 = 156917) B156917
theorem B104627 : Blo 103782 104627 := bstep (se 1 (by rfl) ⟨78470, by rfl⟩ : syracuseStep 104627 = 156941) B156941
theorem B104643 : Blo 103782 104643 := bstep (se 1 (by rfl) ⟨78482, by rfl⟩ : syracuseStep 104643 = 156965) B156965
theorem B104659 : Blo 103782 104659 := bstep (se 1 (by rfl) ⟨78494, by rfl⟩ : syracuseStep 104659 = 156989) B156989
theorem B1775843 : Blo 103782 1775843 := bstep (se 1 (by rfl) ⟨1331882, by rfl⟩ : syracuseStep 1775843 = 2663765) B2663765
theorem B104675 : Blo 103782 104675 := bstep (se 1 (by rfl) ⟨78506, by rfl⟩ : syracuseStep 104675 = 157013) B157013
theorem B301283 : Blo 103782 301283 := bstep (se 1 (by rfl) ⟨225962, by rfl⟩ : syracuseStep 301283 = 451925) B451925
theorem B104691 : Blo 103782 104691 := bstep (se 1 (by rfl) ⟨78518, by rfl⟩ : syracuseStep 104691 = 157037) B157037
theorem B104707 : Blo 103782 104707 := bstep (se 1 (by rfl) ⟨78530, by rfl⟩ : syracuseStep 104707 = 157061) B157061
theorem B104723 : Blo 103782 104723 := bstep (se 1 (by rfl) ⟨78542, by rfl⟩ : syracuseStep 104723 = 157085) B157085
theorem B104739 : Blo 103782 104739 := bstep (se 1 (by rfl) ⟨78554, by rfl⟩ : syracuseStep 104739 = 157109) B157109
theorem B203057 : Blo 103782 203057 := bstep (se 2 (by rfl) ⟨76146, by rfl⟩ : syracuseStep 203057 = 152293) B152293
theorem B104755 : Blo 103782 104755 := bstep (se 1 (by rfl) ⟨78566, by rfl⟩ : syracuseStep 104755 = 157133) B157133
theorem B104771 : Blo 103782 104771 := bstep (se 1 (by rfl) ⟨78578, by rfl⟩ : syracuseStep 104771 = 157157) B157157
theorem B104787 : Blo 103782 104787 := bstep (se 1 (by rfl) ⟨78590, by rfl⟩ : syracuseStep 104787 = 157181) B157181
theorem B104803 : Blo 103782 104803 := bstep (se 1 (by rfl) ⟨78602, by rfl⟩ : syracuseStep 104803 = 157205) B157205
theorem B235889 : Blo 103782 235889 := bstep (se 2 (by rfl) ⟨88458, by rfl⟩ : syracuseStep 235889 = 176917) B176917
theorem B104819 : Blo 103782 104819 := bstep (se 1 (by rfl) ⟨78614, by rfl⟩ : syracuseStep 104819 = 157229) B157229
theorem B104835 : Blo 103782 104835 := bstep (se 1 (by rfl) ⟨78626, by rfl⟩ : syracuseStep 104835 = 157253) B157253
theorem B235907 : Blo 103782 235907 := bstep (se 1 (by rfl) ⟨176930, by rfl⟩ : syracuseStep 235907 = 353861) B353861
theorem B104851 : Blo 103782 104851 := bstep (se 1 (by rfl) ⟨78638, by rfl⟩ : syracuseStep 104851 = 157277) B157277
theorem B104867 : Blo 103782 104867 := bstep (se 1 (by rfl) ⟨78650, by rfl⟩ : syracuseStep 104867 = 157301) B157301
theorem B104883 : Blo 103782 104883 := bstep (se 1 (by rfl) ⟨78662, by rfl⟩ : syracuseStep 104883 = 157325) B157325
theorem B104899 : Blo 103782 104899 := bstep (se 1 (by rfl) ⟨78674, by rfl⟩ : syracuseStep 104899 = 157349) B157349
theorem B104915 : Blo 103782 104915 := bstep (se 1 (by rfl) ⟨78686, by rfl⟩ : syracuseStep 104915 = 157373) B157373
theorem B104931 : Blo 103782 104931 := bstep (se 1 (by rfl) ⟨78698, by rfl⟩ : syracuseStep 104931 = 157397) B157397
theorem B104947 : Blo 103782 104947 := bstep (se 1 (by rfl) ⟨78710, by rfl⟩ : syracuseStep 104947 = 157421) B157421
theorem B104963 : Blo 103782 104963 := bstep (se 1 (by rfl) ⟨78722, by rfl⟩ : syracuseStep 104963 = 157445) B157445
theorem B104979 : Blo 103782 104979 := bstep (se 1 (by rfl) ⟨78734, by rfl⟩ : syracuseStep 104979 = 157469) B157469
theorem B104995 : Blo 103782 104995 := bstep (se 1 (by rfl) ⟨78746, by rfl⟩ : syracuseStep 104995 = 157493) B157493
theorem B105011 : Blo 103782 105011 := bstep (se 1 (by rfl) ⟨78758, by rfl⟩ : syracuseStep 105011 = 157517) B157517
theorem B170561 : Blo 103782 170561 := bstep (se 2 (by rfl) ⟨63960, by rfl⟩ : syracuseStep 170561 = 127921) B127921
theorem B105027 : Blo 103782 105027 := bstep (se 1 (by rfl) ⟨78770, by rfl⟩ : syracuseStep 105027 = 157541) B157541
theorem B105043 : Blo 103782 105043 := bstep (se 1 (by rfl) ⟨78782, by rfl⟩ : syracuseStep 105043 = 157565) B157565
theorem B105059 : Blo 103782 105059 := bstep (se 1 (by rfl) ⟨78794, by rfl⟩ : syracuseStep 105059 = 157589) B157589
theorem B105075 : Blo 103782 105075 := bstep (se 1 (by rfl) ⟨78806, by rfl⟩ : syracuseStep 105075 = 157613) B157613
theorem B105091 : Blo 103782 105091 := bstep (se 1 (by rfl) ⟨78818, by rfl⟩ : syracuseStep 105091 = 157637) B157637
theorem B236177 : Blo 103782 236177 := bstep (se 2 (by rfl) ⟨88566, by rfl⟩ : syracuseStep 236177 = 177133) B177133
theorem B105107 : Blo 103782 105107 := bstep (se 1 (by rfl) ⟨78830, by rfl⟩ : syracuseStep 105107 = 157661) B157661
theorem B236195 : Blo 103782 236195 := bstep (se 1 (by rfl) ⟨177146, by rfl⟩ : syracuseStep 236195 = 354293) B354293
theorem B105123 : Blo 103782 105123 := bstep (se 1 (by rfl) ⟨78842, by rfl⟩ : syracuseStep 105123 = 157685) B157685
theorem B170675 : Blo 103782 170675 := bstep (se 1 (by rfl) ⟨128006, by rfl⟩ : syracuseStep 170675 = 256013) B256013
theorem B105139 : Blo 103782 105139 := bstep (se 1 (by rfl) ⟨78854, by rfl⟩ : syracuseStep 105139 = 157709) B157709
theorem B170689 : Blo 103782 170689 := bstep (se 2 (by rfl) ⟨64008, by rfl⟩ : syracuseStep 170689 = 128017) B128017
theorem B105155 : Blo 103782 105155 := bstep (se 1 (by rfl) ⟨78866, by rfl⟩ : syracuseStep 105155 = 157733) B157733
theorem B105171 : Blo 103782 105171 := bstep (se 1 (by rfl) ⟨78878, by rfl⟩ : syracuseStep 105171 = 157757) B157757
theorem B105187 : Blo 103782 105187 := bstep (se 1 (by rfl) ⟨78890, by rfl⟩ : syracuseStep 105187 = 157781) B157781
theorem B400099 : Blo 103782 400099 := bstep (se 1 (by rfl) ⟨300074, by rfl⟩ : syracuseStep 400099 = 600149) B600149
theorem B269041 : Blo 103782 269041 := bstep (se 2 (by rfl) ⟨100890, by rfl⟩ : syracuseStep 269041 = 201781) B201781
theorem B105203 : Blo 103782 105203 := bstep (se 1 (by rfl) ⟨78902, by rfl⟩ : syracuseStep 105203 = 157805) B157805
theorem B170753 : Blo 103782 170753 := bstep (se 2 (by rfl) ⟨64032, by rfl⟩ : syracuseStep 170753 = 128065) B128065
theorem B105219 : Blo 103782 105219 := bstep (se 1 (by rfl) ⟨78914, by rfl⟩ : syracuseStep 105219 = 157829) B157829
theorem B105235 : Blo 103782 105235 := bstep (se 1 (by rfl) ⟨78926, by rfl⟩ : syracuseStep 105235 = 157853) B157853
theorem B105251 : Blo 103782 105251 := bstep (se 1 (by rfl) ⟨78938, by rfl⟩ : syracuseStep 105251 = 157877) B157877
theorem B105267 : Blo 103782 105267 := bstep (se 1 (by rfl) ⟨78950, by rfl⟩ : syracuseStep 105267 = 157901) B157901
theorem B105283 : Blo 103782 105283 := bstep (se 1 (by rfl) ⟨78962, by rfl⟩ : syracuseStep 105283 = 157925) B157925
theorem B105299 : Blo 103782 105299 := bstep (se 1 (by rfl) ⟨78974, by rfl⟩ : syracuseStep 105299 = 157949) B157949
theorem B105315 : Blo 103782 105315 := bstep (se 1 (by rfl) ⟨78986, by rfl⟩ : syracuseStep 105315 = 157973) B157973
theorem B105331 : Blo 103782 105331 := bstep (se 1 (by rfl) ⟨78998, by rfl⟩ : syracuseStep 105331 = 157997) B157997
theorem B105347 : Blo 103782 105347 := bstep (se 1 (by rfl) ⟨79010, by rfl⟩ : syracuseStep 105347 = 158021) B158021
theorem B105363 : Blo 103782 105363 := bstep (se 1 (by rfl) ⟨79022, by rfl⟩ : syracuseStep 105363 = 158045) B158045
theorem B105379 : Blo 103782 105379 := bstep (se 1 (by rfl) ⟨79034, by rfl⟩ : syracuseStep 105379 = 158069) B158069
theorem B236465 : Blo 103782 236465 := bstep (se 2 (by rfl) ⟨88674, by rfl⟩ : syracuseStep 236465 = 177349) B177349
theorem B105395 : Blo 103782 105395 := bstep (se 1 (by rfl) ⟨79046, by rfl⟩ : syracuseStep 105395 = 158093) B158093
theorem B236483 : Blo 103782 236483 := bstep (se 1 (by rfl) ⟨177362, by rfl⟩ : syracuseStep 236483 = 354725) B354725
theorem B105411 : Blo 103782 105411 := bstep (se 1 (by rfl) ⟨79058, by rfl⟩ : syracuseStep 105411 = 158117) B158117
theorem B105427 : Blo 103782 105427 := bstep (se 1 (by rfl) ⟨79070, by rfl⟩ : syracuseStep 105427 = 158141) B158141
theorem B105443 : Blo 103782 105443 := bstep (se 1 (by rfl) ⟨79082, by rfl⟩ : syracuseStep 105443 = 158165) B158165
theorem B105459 : Blo 103782 105459 := bstep (se 1 (by rfl) ⟨79094, by rfl⟩ : syracuseStep 105459 = 158189) B158189
theorem B105475 : Blo 103782 105475 := bstep (se 1 (by rfl) ⟨79106, by rfl⟩ : syracuseStep 105475 = 158213) B158213
theorem B269315 : Blo 103782 269315 := bstep (se 1 (by rfl) ⟨201986, by rfl⟩ : syracuseStep 269315 = 403973) B403973
theorem B105491 : Blo 103782 105491 := bstep (se 1 (by rfl) ⟨79118, by rfl⟩ : syracuseStep 105491 = 158237) B158237
theorem B105507 : Blo 103782 105507 := bstep (se 1 (by rfl) ⟨79130, by rfl⟩ : syracuseStep 105507 = 158261) B158261
theorem B302125 : Blo 103782 302125 := bstep (se 3 (by rfl) ⟨56648, by rfl⟩ : syracuseStep 302125 = 113297) B113297
theorem B105523 : Blo 103782 105523 := bstep (se 1 (by rfl) ⟨79142, by rfl⟩ : syracuseStep 105523 = 158285) B158285
theorem B105539 : Blo 103782 105539 := bstep (se 1 (by rfl) ⟨79154, by rfl⟩ : syracuseStep 105539 = 158309) B158309
theorem B105555 : Blo 103782 105555 := bstep (se 1 (by rfl) ⟨79166, by rfl⟩ : syracuseStep 105555 = 158333) B158333
theorem B105571 : Blo 103782 105571 := bstep (se 1 (by rfl) ⟨79178, by rfl⟩ : syracuseStep 105571 = 158357) B158357
theorem B105587 : Blo 103782 105587 := bstep (se 1 (by rfl) ⟨79190, by rfl⟩ : syracuseStep 105587 = 158381) B158381
theorem B105603 : Blo 103782 105603 := bstep (se 1 (by rfl) ⟨79202, by rfl⟩ : syracuseStep 105603 = 158405) B158405
theorem B302221 : Blo 103782 302221 := bstep (se 3 (by rfl) ⟨56666, by rfl⟩ : syracuseStep 302221 = 113333) B113333
theorem B1154189 : Blo 103782 1154189 := bstep (se 3 (by rfl) ⟨216410, by rfl⟩ : syracuseStep 1154189 = 432821) B432821
theorem B105619 : Blo 103782 105619 := bstep (se 1 (by rfl) ⟨79214, by rfl⟩ : syracuseStep 105619 = 158429) B158429
theorem B105635 : Blo 103782 105635 := bstep (se 1 (by rfl) ⟨79226, by rfl⟩ : syracuseStep 105635 = 158453) B158453
theorem B335021 : Blo 103782 335021 := bstep (se 3 (by rfl) ⟨62816, by rfl⟩ : syracuseStep 335021 = 125633) B125633
theorem B203953 : Blo 103782 203953 := bstep (se 2 (by rfl) ⟨76482, by rfl⟩ : syracuseStep 203953 = 152965) B152965
theorem B105651 : Blo 103782 105651 := bstep (se 1 (by rfl) ⟨79238, by rfl⟩ : syracuseStep 105651 = 158477) B158477
theorem B105667 : Blo 103782 105667 := bstep (se 1 (by rfl) ⟨79250, by rfl⟩ : syracuseStep 105667 = 158501) B158501
theorem B269507 : Blo 103782 269507 := bstep (se 1 (by rfl) ⟨202130, by rfl⟩ : syracuseStep 269507 = 404261) B404261
theorem B302285 : Blo 103782 302285 := bstep (se 3 (by rfl) ⟨56678, by rfl⟩ : syracuseStep 302285 = 113357) B113357
theorem B236753 : Blo 103782 236753 := bstep (se 2 (by rfl) ⟨88782, by rfl⟩ : syracuseStep 236753 = 177565) B177565
theorem B105683 : Blo 103782 105683 := bstep (se 1 (by rfl) ⟨79262, by rfl⟩ : syracuseStep 105683 = 158525) B158525
theorem B531683 : Blo 103782 531683 := bstep (se 1 (by rfl) ⟨398762, by rfl⟩ : syracuseStep 531683 = 797525) B797525
theorem B236771 : Blo 103782 236771 := bstep (se 1 (by rfl) ⟨177578, by rfl⟩ : syracuseStep 236771 = 355157) B355157
theorem B105699 : Blo 103782 105699 := bstep (se 1 (by rfl) ⟨79274, by rfl⟩ : syracuseStep 105699 = 158549) B158549
theorem B597233 : Blo 103782 597233 := bstep (se 2 (by rfl) ⟨223962, by rfl⟩ : syracuseStep 597233 = 447925) B447925
theorem B105715 : Blo 103782 105715 := bstep (se 1 (by rfl) ⟨79286, by rfl⟩ : syracuseStep 105715 = 158573) B158573
theorem B105731 : Blo 103782 105731 := bstep (se 1 (by rfl) ⟨79298, by rfl⟩ : syracuseStep 105731 = 158597) B158597
theorem B105747 : Blo 103782 105747 := bstep (se 1 (by rfl) ⟨79310, by rfl⟩ : syracuseStep 105747 = 158621) B158621
theorem B105763 : Blo 103782 105763 := bstep (se 1 (by rfl) ⟨79322, by rfl⟩ : syracuseStep 105763 = 158645) B158645
theorem B105779 : Blo 103782 105779 := bstep (se 1 (by rfl) ⟨79334, by rfl⟩ : syracuseStep 105779 = 158669) B158669
theorem B105795 : Blo 103782 105795 := bstep (se 1 (by rfl) ⟨79346, by rfl⟩ : syracuseStep 105795 = 158693) B158693
theorem B204113 : Blo 103782 204113 := bstep (se 2 (by rfl) ⟨76542, by rfl⟩ : syracuseStep 204113 = 153085) B153085
theorem B105811 : Blo 103782 105811 := bstep (se 1 (by rfl) ⟨79358, by rfl⟩ : syracuseStep 105811 = 158717) B158717
theorem B105827 : Blo 103782 105827 := bstep (se 1 (by rfl) ⟨79370, by rfl⟩ : syracuseStep 105827 = 158741) B158741
theorem B105843 : Blo 103782 105843 := bstep (se 1 (by rfl) ⟨79382, by rfl⟩ : syracuseStep 105843 = 158765) B158765
theorem B105859 : Blo 103782 105859 := bstep (se 1 (by rfl) ⟨79394, by rfl⟩ : syracuseStep 105859 = 158789) B158789
theorem B302467 : Blo 103782 302467 := bstep (se 1 (by rfl) ⟨226850, by rfl⟩ : syracuseStep 302467 = 453701) B453701
theorem B105875 : Blo 103782 105875 := bstep (se 1 (by rfl) ⟨79406, by rfl⟩ : syracuseStep 105875 = 158813) B158813
theorem B105891 : Blo 103782 105891 := bstep (se 1 (by rfl) ⟨79418, by rfl⟩ : syracuseStep 105891 = 158837) B158837
theorem B105907 : Blo 103782 105907 := bstep (se 1 (by rfl) ⟨79430, by rfl⟩ : syracuseStep 105907 = 158861) B158861
theorem B105923 : Blo 103782 105923 := bstep (se 1 (by rfl) ⟨79442, by rfl⟩ : syracuseStep 105923 = 158885) B158885
theorem B433613 : Blo 103782 433613 := bstep (se 3 (by rfl) ⟨81302, by rfl⟩ : syracuseStep 433613 = 162605) B162605
theorem B105939 : Blo 103782 105939 := bstep (se 1 (by rfl) ⟨79454, by rfl⟩ : syracuseStep 105939 = 158909) B158909
theorem B105955 : Blo 103782 105955 := bstep (se 1 (by rfl) ⟨79466, by rfl⟩ : syracuseStep 105955 = 158933) B158933
theorem B237041 : Blo 103782 237041 := bstep (se 2 (by rfl) ⟨88890, by rfl⟩ : syracuseStep 237041 = 177781) B177781
theorem B105971 : Blo 103782 105971 := bstep (se 1 (by rfl) ⟨79478, by rfl⟩ : syracuseStep 105971 = 158957) B158957
theorem B237059 : Blo 103782 237059 := bstep (se 1 (by rfl) ⟨177794, by rfl⟩ : syracuseStep 237059 = 355589) B355589
theorem B105987 : Blo 103782 105987 := bstep (se 1 (by rfl) ⟨79490, by rfl⟩ : syracuseStep 105987 = 158981) B158981
theorem B106003 : Blo 103782 106003 := bstep (se 1 (by rfl) ⟨79502, by rfl⟩ : syracuseStep 106003 = 159005) B159005
theorem B106019 : Blo 103782 106019 := bstep (se 1 (by rfl) ⟨79514, by rfl⟩ : syracuseStep 106019 = 159029) B159029
theorem B106035 : Blo 103782 106035 := bstep (se 1 (by rfl) ⟨79526, by rfl⟩ : syracuseStep 106035 = 159053) B159053
theorem B106051 : Blo 103782 106051 := bstep (se 1 (by rfl) ⟨79538, by rfl⟩ : syracuseStep 106051 = 159077) B159077
theorem B106067 : Blo 103782 106067 := bstep (se 1 (by rfl) ⟨79550, by rfl⟩ : syracuseStep 106067 = 159101) B159101
theorem B106083 : Blo 103782 106083 := bstep (se 1 (by rfl) ⟨79562, by rfl⟩ : syracuseStep 106083 = 159125) B159125
theorem B106099 : Blo 103782 106099 := bstep (se 1 (by rfl) ⟨79574, by rfl⟩ : syracuseStep 106099 = 159149) B159149
theorem B106115 : Blo 103782 106115 := bstep (se 1 (by rfl) ⟨79586, by rfl⟩ : syracuseStep 106115 = 159173) B159173
theorem B106131 : Blo 103782 106131 := bstep (se 1 (by rfl) ⟨79598, by rfl⟩ : syracuseStep 106131 = 159197) B159197
theorem B106147 : Blo 103782 106147 := bstep (se 1 (by rfl) ⟨79610, by rfl⟩ : syracuseStep 106147 = 159221) B159221
theorem B106163 : Blo 103782 106163 := bstep (se 1 (by rfl) ⟨79622, by rfl⟩ : syracuseStep 106163 = 159245) B159245
theorem B106179 : Blo 103782 106179 := bstep (se 1 (by rfl) ⟨79634, by rfl⟩ : syracuseStep 106179 = 159269) B159269
theorem B106195 : Blo 103782 106195 := bstep (se 1 (by rfl) ⟨79646, by rfl⟩ : syracuseStep 106195 = 159293) B159293
theorem B106211 : Blo 103782 106211 := bstep (se 1 (by rfl) ⟨79658, by rfl⟩ : syracuseStep 106211 = 159317) B159317
theorem B204515 : Blo 103782 204515 := bstep (se 1 (by rfl) ⟨153386, by rfl⟩ : syracuseStep 204515 = 306773) B306773
theorem B106227 : Blo 103782 106227 := bstep (se 1 (by rfl) ⟨79670, by rfl⟩ : syracuseStep 106227 = 159341) B159341
theorem B106243 : Blo 103782 106243 := bstep (se 1 (by rfl) ⟨79682, by rfl⟩ : syracuseStep 106243 = 159365) B159365
theorem B237329 : Blo 103782 237329 := bstep (se 2 (by rfl) ⟨88998, by rfl⟩ : syracuseStep 237329 = 177997) B177997
theorem B106259 : Blo 103782 106259 := bstep (se 1 (by rfl) ⟨79694, by rfl⟩ : syracuseStep 106259 = 159389) B159389
theorem B237347 : Blo 103782 237347 := bstep (se 1 (by rfl) ⟨178010, by rfl⟩ : syracuseStep 237347 = 356021) B356021
theorem B106275 : Blo 103782 106275 := bstep (se 1 (by rfl) ⟨79706, by rfl⟩ : syracuseStep 106275 = 159413) B159413
theorem B171811 : Blo 103782 171811 := bstep (se 1 (by rfl) ⟨128858, by rfl⟩ : syracuseStep 171811 = 257717) B257717
theorem B106291 : Blo 103782 106291 := bstep (se 1 (by rfl) ⟨79718, by rfl⟩ : syracuseStep 106291 = 159437) B159437
theorem B106307 : Blo 103782 106307 := bstep (se 1 (by rfl) ⟨79730, by rfl⟩ : syracuseStep 106307 = 159461) B159461
theorem B106323 : Blo 103782 106323 := bstep (se 1 (by rfl) ⟨79742, by rfl⟩ : syracuseStep 106323 = 159485) B159485
theorem B106339 : Blo 103782 106339 := bstep (se 1 (by rfl) ⟨79754, by rfl⟩ : syracuseStep 106339 = 159509) B159509
theorem B204643 : Blo 103782 204643 := bstep (se 1 (by rfl) ⟨153482, by rfl⟩ : syracuseStep 204643 = 306965) B306965
theorem B106355 : Blo 103782 106355 := bstep (se 1 (by rfl) ⟨79766, by rfl⟩ : syracuseStep 106355 = 159533) B159533
theorem B106371 : Blo 103782 106371 := bstep (se 1 (by rfl) ⟨79778, by rfl⟩ : syracuseStep 106371 = 159557) B159557
theorem B106387 : Blo 103782 106387 := bstep (se 1 (by rfl) ⟨79790, by rfl⟩ : syracuseStep 106387 = 159581) B159581
theorem B106403 : Blo 103782 106403 := bstep (se 1 (by rfl) ⟨79802, by rfl⟩ : syracuseStep 106403 = 159605) B159605
theorem B106419 : Blo 103782 106419 := bstep (se 1 (by rfl) ⟨79814, by rfl⟩ : syracuseStep 106419 = 159629) B159629
theorem B106435 : Blo 103782 106435 := bstep (se 1 (by rfl) ⟨79826, by rfl⟩ : syracuseStep 106435 = 159653) B159653
theorem B106451 : Blo 103782 106451 := bstep (se 1 (by rfl) ⟨79838, by rfl⟩ : syracuseStep 106451 = 159677) B159677
theorem B106467 : Blo 103782 106467 := bstep (se 1 (by rfl) ⟨79850, by rfl⟩ : syracuseStep 106467 = 159701) B159701
theorem B794609 : Blo 103782 794609 := bstep (se 2 (by rfl) ⟨297978, by rfl⟩ : syracuseStep 794609 = 595957) B595957
theorem B106483 : Blo 103782 106483 := bstep (se 1 (by rfl) ⟨79862, by rfl⟩ : syracuseStep 106483 = 159725) B159725
theorem B106499 : Blo 103782 106499 := bstep (se 1 (by rfl) ⟨79874, by rfl⟩ : syracuseStep 106499 = 159749) B159749
theorem B532493 : Blo 103782 532493 := bstep (se 3 (by rfl) ⟨99842, by rfl⟩ : syracuseStep 532493 = 199685) B199685
theorem B106515 : Blo 103782 106515 := bstep (se 1 (by rfl) ⟨79886, by rfl⟩ : syracuseStep 106515 = 159773) B159773
theorem B106531 : Blo 103782 106531 := bstep (se 1 (by rfl) ⟨79898, by rfl⟩ : syracuseStep 106531 = 159797) B159797
theorem B237617 : Blo 103782 237617 := bstep (se 2 (by rfl) ⟨89106, by rfl⟩ : syracuseStep 237617 = 178213) B178213
theorem B106547 : Blo 103782 106547 := bstep (se 1 (by rfl) ⟨79910, by rfl⟩ : syracuseStep 106547 = 159821) B159821
theorem B237635 : Blo 103782 237635 := bstep (se 1 (by rfl) ⟨178226, by rfl⟩ : syracuseStep 237635 = 356453) B356453
theorem B106563 : Blo 103782 106563 := bstep (se 1 (by rfl) ⟨79922, by rfl⟩ : syracuseStep 106563 = 159845) B159845
theorem B106579 : Blo 103782 106579 := bstep (se 1 (by rfl) ⟨79934, by rfl⟩ : syracuseStep 106579 = 159869) B159869
theorem B106595 : Blo 103782 106595 := bstep (se 1 (by rfl) ⟨79946, by rfl⟩ : syracuseStep 106595 = 159893) B159893
theorem B270449 : Blo 103782 270449 := bstep (se 2 (by rfl) ⟨101418, by rfl⟩ : syracuseStep 270449 = 202837) B202837
theorem B106611 : Blo 103782 106611 := bstep (se 1 (by rfl) ⟨79958, by rfl⟩ : syracuseStep 106611 = 159917) B159917
theorem B106627 : Blo 103782 106627 := bstep (se 1 (by rfl) ⟨79970, by rfl⟩ : syracuseStep 106627 = 159941) B159941
theorem B106643 : Blo 103782 106643 := bstep (se 1 (by rfl) ⟨79982, by rfl⟩ : syracuseStep 106643 = 159965) B159965
theorem B106659 : Blo 103782 106659 := bstep (se 1 (by rfl) ⟨79994, by rfl⟩ : syracuseStep 106659 = 159989) B159989
theorem B270499 : Blo 103782 270499 := bstep (se 1 (by rfl) ⟨202874, by rfl⟩ : syracuseStep 270499 = 405749) B405749
theorem B106675 : Blo 103782 106675 := bstep (se 1 (by rfl) ⟨80006, by rfl⟩ : syracuseStep 106675 = 160013) B160013
theorem B106691 : Blo 103782 106691 := bstep (se 1 (by rfl) ⟨80018, by rfl⟩ : syracuseStep 106691 = 160037) B160037
theorem B106707 : Blo 103782 106707 := bstep (se 1 (by rfl) ⟨80030, by rfl⟩ : syracuseStep 106707 = 160061) B160061
theorem B106723 : Blo 103782 106723 := bstep (se 1 (by rfl) ⟨80042, by rfl⟩ : syracuseStep 106723 = 160085) B160085
theorem B106739 : Blo 103782 106739 := bstep (se 1 (by rfl) ⟨80054, by rfl⟩ : syracuseStep 106739 = 160109) B160109
theorem B106755 : Blo 103782 106755 := bstep (se 1 (by rfl) ⟨80066, by rfl⟩ : syracuseStep 106755 = 160133) B160133
theorem B106771 : Blo 103782 106771 := bstep (se 1 (by rfl) ⟨80078, by rfl⟩ : syracuseStep 106771 = 160157) B160157
theorem B106787 : Blo 103782 106787 := bstep (se 1 (by rfl) ⟨80090, by rfl⟩ : syracuseStep 106787 = 160181) B160181
theorem B270641 : Blo 103782 270641 := bstep (se 2 (by rfl) ⟨101490, by rfl⟩ : syracuseStep 270641 = 202981) B202981
theorem B106803 : Blo 103782 106803 := bstep (se 1 (by rfl) ⟨80102, by rfl⟩ : syracuseStep 106803 = 160205) B160205
theorem B106819 : Blo 103782 106819 := bstep (se 1 (by rfl) ⟨80114, by rfl⟩ : syracuseStep 106819 = 160229) B160229
theorem B237905 : Blo 103782 237905 := bstep (se 2 (by rfl) ⟨89214, by rfl⟩ : syracuseStep 237905 = 178429) B178429
theorem B106835 : Blo 103782 106835 := bstep (se 1 (by rfl) ⟨80126, by rfl⟩ : syracuseStep 106835 = 160253) B160253
theorem B237923 : Blo 103782 237923 := bstep (se 1 (by rfl) ⟨178442, by rfl⟩ : syracuseStep 237923 = 356885) B356885
theorem B106851 : Blo 103782 106851 := bstep (se 1 (by rfl) ⟨80138, by rfl⟩ : syracuseStep 106851 = 160277) B160277
theorem B106867 : Blo 103782 106867 := bstep (se 1 (by rfl) ⟨80150, by rfl⟩ : syracuseStep 106867 = 160301) B160301
theorem B106883 : Blo 103782 106883 := bstep (se 1 (by rfl) ⟨80162, by rfl⟩ : syracuseStep 106883 = 160325) B160325
theorem B106899 : Blo 103782 106899 := bstep (se 1 (by rfl) ⟨80174, by rfl⟩ : syracuseStep 106899 = 160349) B160349
theorem B106915 : Blo 103782 106915 := bstep (se 1 (by rfl) ⟨80186, by rfl⟩ : syracuseStep 106915 = 160373) B160373
theorem B106931 : Blo 103782 106931 := bstep (se 1 (by rfl) ⟨80198, by rfl⟩ : syracuseStep 106931 = 160397) B160397
theorem B106947 : Blo 103782 106947 := bstep (se 1 (by rfl) ⟨80210, by rfl⟩ : syracuseStep 106947 = 160421) B160421
theorem B106963 : Blo 103782 106963 := bstep (se 1 (by rfl) ⟨80222, by rfl⟩ : syracuseStep 106963 = 160445) B160445
theorem B106979 : Blo 103782 106979 := bstep (se 1 (by rfl) ⟨80234, by rfl⟩ : syracuseStep 106979 = 160469) B160469
theorem B106995 : Blo 103782 106995 := bstep (se 1 (by rfl) ⟨80246, by rfl⟩ : syracuseStep 106995 = 160493) B160493
theorem B107011 : Blo 103782 107011 := bstep (se 1 (by rfl) ⟨80258, by rfl⟩ : syracuseStep 107011 = 160517) B160517
theorem B107027 : Blo 103782 107027 := bstep (se 1 (by rfl) ⟨80270, by rfl⟩ : syracuseStep 107027 = 160541) B160541
theorem B107043 : Blo 103782 107043 := bstep (se 1 (by rfl) ⟨80282, by rfl⟩ : syracuseStep 107043 = 160565) B160565
theorem B107059 : Blo 103782 107059 := bstep (se 1 (by rfl) ⟨80294, by rfl⟩ : syracuseStep 107059 = 160589) B160589
theorem B107075 : Blo 103782 107075 := bstep (se 1 (by rfl) ⟨80306, by rfl⟩ : syracuseStep 107075 = 160613) B160613
theorem B107091 : Blo 103782 107091 := bstep (se 1 (by rfl) ⟨80318, by rfl⟩ : syracuseStep 107091 = 160637) B160637
theorem B107107 : Blo 103782 107107 := bstep (se 1 (by rfl) ⟨80330, by rfl⟩ : syracuseStep 107107 = 160661) B160661
theorem B238193 : Blo 103782 238193 := bstep (se 2 (by rfl) ⟨89322, by rfl⟩ : syracuseStep 238193 = 178645) B178645
theorem B107123 : Blo 103782 107123 := bstep (se 1 (by rfl) ⟨80342, by rfl⟩ : syracuseStep 107123 = 160685) B160685
theorem B238211 : Blo 103782 238211 := bstep (se 1 (by rfl) ⟨178658, by rfl⟩ : syracuseStep 238211 = 357317) B357317
theorem B107139 : Blo 103782 107139 := bstep (se 1 (by rfl) ⟨80354, by rfl⟩ : syracuseStep 107139 = 160709) B160709
theorem B107155 : Blo 103782 107155 := bstep (se 1 (by rfl) ⟨80366, by rfl⟩ : syracuseStep 107155 = 160733) B160733
theorem B598691 : Blo 103782 598691 := bstep (se 1 (by rfl) ⟨449018, by rfl⟩ : syracuseStep 598691 = 898037) B898037
theorem B107171 : Blo 103782 107171 := bstep (se 1 (by rfl) ⟨80378, by rfl⟩ : syracuseStep 107171 = 160757) B160757
theorem B107187 : Blo 103782 107187 := bstep (se 1 (by rfl) ⟨80390, by rfl⟩ : syracuseStep 107187 = 160781) B160781
theorem B107203 : Blo 103782 107203 := bstep (se 1 (by rfl) ⟨80402, by rfl⟩ : syracuseStep 107203 = 160805) B160805
theorem B107219 : Blo 103782 107219 := bstep (se 1 (by rfl) ⟨80414, by rfl⟩ : syracuseStep 107219 = 160829) B160829
theorem B336611 : Blo 103782 336611 := bstep (se 1 (by rfl) ⟨252458, by rfl⟩ : syracuseStep 336611 = 504917) B504917
theorem B107235 : Blo 103782 107235 := bstep (se 1 (by rfl) ⟨80426, by rfl⟩ : syracuseStep 107235 = 160853) B160853
theorem B303857 : Blo 103782 303857 := bstep (se 2 (by rfl) ⟨113946, by rfl⟩ : syracuseStep 303857 = 227893) B227893
theorem B107251 : Blo 103782 107251 := bstep (se 1 (by rfl) ⟨80438, by rfl⟩ : syracuseStep 107251 = 160877) B160877
theorem B107267 : Blo 103782 107267 := bstep (se 1 (by rfl) ⟨80450, by rfl⟩ : syracuseStep 107267 = 160901) B160901
theorem B1123085 : Blo 103782 1123085 := bstep (se 3 (by rfl) ⟨210578, by rfl⟩ : syracuseStep 1123085 = 421157) B421157
theorem B107283 : Blo 103782 107283 := bstep (se 1 (by rfl) ⟨80462, by rfl⟩ : syracuseStep 107283 = 160925) B160925
theorem B107299 : Blo 103782 107299 := bstep (se 1 (by rfl) ⟨80474, by rfl⟩ : syracuseStep 107299 = 160949) B160949
theorem B107315 : Blo 103782 107315 := bstep (se 1 (by rfl) ⟨80486, by rfl⟩ : syracuseStep 107315 = 160973) B160973
theorem B107331 : Blo 103782 107331 := bstep (se 1 (by rfl) ⟨80498, by rfl⟩ : syracuseStep 107331 = 160997) B160997
theorem B107347 : Blo 103782 107347 := bstep (se 1 (by rfl) ⟨80510, by rfl⟩ : syracuseStep 107347 = 161021) B161021
theorem B107363 : Blo 103782 107363 := bstep (se 1 (by rfl) ⟨80522, by rfl⟩ : syracuseStep 107363 = 161045) B161045
theorem B107379 : Blo 103782 107379 := bstep (se 1 (by rfl) ⟨80534, by rfl⟩ : syracuseStep 107379 = 161069) B161069
theorem B107395 : Blo 103782 107395 := bstep (se 1 (by rfl) ⟨80546, by rfl⟩ : syracuseStep 107395 = 161093) B161093
theorem B402317 : Blo 103782 402317 := bstep (se 3 (by rfl) ⟨75434, by rfl⟩ : syracuseStep 402317 = 150869) B150869
theorem B238481 : Blo 103782 238481 := bstep (se 2 (by rfl) ⟨89430, by rfl⟩ : syracuseStep 238481 = 178861) B178861
theorem B107411 : Blo 103782 107411 := bstep (se 1 (by rfl) ⟨80558, by rfl⟩ : syracuseStep 107411 = 161117) B161117
theorem B238499 : Blo 103782 238499 := bstep (se 1 (by rfl) ⟨178874, by rfl⟩ : syracuseStep 238499 = 357749) B357749
theorem B107427 : Blo 103782 107427 := bstep (se 1 (by rfl) ⟨80570, by rfl⟩ : syracuseStep 107427 = 161141) B161141
theorem B107443 : Blo 103782 107443 := bstep (se 1 (by rfl) ⟨80582, by rfl⟩ : syracuseStep 107443 = 161165) B161165
theorem B107459 : Blo 103782 107459 := bstep (se 1 (by rfl) ⟨80594, by rfl⟩ : syracuseStep 107459 = 161189) B161189
theorem B107475 : Blo 103782 107475 := bstep (se 1 (by rfl) ⟨80606, by rfl⟩ : syracuseStep 107475 = 161213) B161213
theorem B107491 : Blo 103782 107491 := bstep (se 1 (by rfl) ⟨80618, by rfl⟩ : syracuseStep 107491 = 161237) B161237
theorem B107507 : Blo 103782 107507 := bstep (se 1 (by rfl) ⟨80630, by rfl⟩ : syracuseStep 107507 = 161261) B161261
theorem B107523 : Blo 103782 107523 := bstep (se 1 (by rfl) ⟨80642, by rfl⟩ : syracuseStep 107523 = 161285) B161285
theorem B107539 : Blo 103782 107539 := bstep (se 1 (by rfl) ⟨80654, by rfl⟩ : syracuseStep 107539 = 161309) B161309
theorem B107555 : Blo 103782 107555 := bstep (se 1 (by rfl) ⟨80666, by rfl⟩ : syracuseStep 107555 = 161333) B161333
theorem B107571 : Blo 103782 107571 := bstep (se 1 (by rfl) ⟨80678, by rfl⟩ : syracuseStep 107571 = 161357) B161357
theorem B107587 : Blo 103782 107587 := bstep (se 1 (by rfl) ⟨80690, by rfl⟩ : syracuseStep 107587 = 161381) B161381
theorem B107603 : Blo 103782 107603 := bstep (se 1 (by rfl) ⟨80702, by rfl⟩ : syracuseStep 107603 = 161405) B161405
theorem B238691 : Blo 103782 238691 := bstep (se 1 (by rfl) ⟨179018, by rfl⟩ : syracuseStep 238691 = 358037) B358037
theorem B107619 : Blo 103782 107619 := bstep (se 1 (by rfl) ⟨80714, by rfl⟩ : syracuseStep 107619 = 161429) B161429
theorem B107635 : Blo 103782 107635 := bstep (se 1 (by rfl) ⟨80726, by rfl⟩ : syracuseStep 107635 = 161453) B161453
theorem B107651 : Blo 103782 107651 := bstep (se 1 (by rfl) ⟨80738, by rfl⟩ : syracuseStep 107651 = 161477) B161477
theorem B107667 : Blo 103782 107667 := bstep (se 1 (by rfl) ⟨80750, by rfl⟩ : syracuseStep 107667 = 161501) B161501
theorem B107683 : Blo 103782 107683 := bstep (se 1 (by rfl) ⟨80762, by rfl⟩ : syracuseStep 107683 = 161525) B161525
theorem B238769 : Blo 103782 238769 := bstep (se 2 (by rfl) ⟨89538, by rfl⟩ : syracuseStep 238769 = 179077) B179077
theorem B107699 : Blo 103782 107699 := bstep (se 1 (by rfl) ⟨80774, by rfl⟩ : syracuseStep 107699 = 161549) B161549
theorem B238787 : Blo 103782 238787 := bstep (se 1 (by rfl) ⟨179090, by rfl⟩ : syracuseStep 238787 = 358181) B358181
theorem B107715 : Blo 103782 107715 := bstep (se 1 (by rfl) ⟨80786, by rfl⟩ : syracuseStep 107715 = 161573) B161573
theorem B107731 : Blo 103782 107731 := bstep (se 1 (by rfl) ⟨80798, by rfl⟩ : syracuseStep 107731 = 161597) B161597
theorem B107747 : Blo 103782 107747 := bstep (se 1 (by rfl) ⟨80810, by rfl⟩ : syracuseStep 107747 = 161621) B161621
theorem B107763 : Blo 103782 107763 := bstep (se 1 (by rfl) ⟨80822, by rfl⟩ : syracuseStep 107763 = 161645) B161645
theorem B107779 : Blo 103782 107779 := bstep (se 1 (by rfl) ⟨80834, by rfl⟩ : syracuseStep 107779 = 161669) B161669
theorem B271633 : Blo 103782 271633 := bstep (se 2 (by rfl) ⟨101862, by rfl⟩ : syracuseStep 271633 = 203725) B203725
theorem B239057 : Blo 103782 239057 := bstep (se 2 (by rfl) ⟨89646, by rfl⟩ : syracuseStep 239057 = 179293) B179293
theorem B239075 : Blo 103782 239075 := bstep (se 1 (by rfl) ⟨179306, by rfl⟩ : syracuseStep 239075 = 358613) B358613
theorem B271907 : Blo 103782 271907 := bstep (se 1 (by rfl) ⟨203930, by rfl⟩ : syracuseStep 271907 = 407861) B407861
theorem B304813 : Blo 103782 304813 := bstep (se 3 (by rfl) ⟨57152, by rfl⟩ : syracuseStep 304813 = 114305) B114305
theorem B272099 : Blo 103782 272099 := bstep (se 1 (by rfl) ⟨204074, by rfl⟩ : syracuseStep 272099 = 408149) B408149
theorem B239345 : Blo 103782 239345 := bstep (se 2 (by rfl) ⟨89754, by rfl⟩ : syracuseStep 239345 = 179509) B179509
theorem B239363 : Blo 103782 239363 := bstep (se 1 (by rfl) ⟨179522, by rfl⟩ : syracuseStep 239363 = 359045) B359045
theorem B206723 : Blo 103782 206723 := bstep (se 1 (by rfl) ⟨155042, by rfl⟩ : syracuseStep 206723 = 310085) B310085
theorem B305041 : Blo 103782 305041 := bstep (se 2 (by rfl) ⟨114390, by rfl⟩ : syracuseStep 305041 = 228781) B228781
theorem B141203 : Blo 103782 141203 := bstep (se 1 (by rfl) ⟨105902, by rfl⟩ : syracuseStep 141203 = 211805) B211805
theorem B337841 : Blo 103782 337841 := bstep (se 2 (by rfl) ⟨126690, by rfl⟩ : syracuseStep 337841 = 253381) B253381
theorem B239633 : Blo 103782 239633 := bstep (se 2 (by rfl) ⟨89862, by rfl⟩ : syracuseStep 239633 = 179725) B179725
theorem B239651 : Blo 103782 239651 := bstep (se 1 (by rfl) ⟨179738, by rfl⟩ : syracuseStep 239651 = 359477) B359477
theorem B305201 : Blo 103782 305201 := bstep (se 2 (by rfl) ⟨114450, by rfl⟩ : syracuseStep 305201 = 228901) B228901
theorem B305315 : Blo 103782 305315 := bstep (se 1 (by rfl) ⟨228986, by rfl⟩ : syracuseStep 305315 = 457973) B457973
theorem B239921 : Blo 103782 239921 := bstep (se 2 (by rfl) ⟨89970, by rfl⟩ : syracuseStep 239921 = 179941) B179941
theorem B239939 : Blo 103782 239939 := bstep (se 1 (by rfl) ⟨179954, by rfl⟩ : syracuseStep 239939 = 359909) B359909
theorem B895373 : Blo 103782 895373 := bstep (se 3 (by rfl) ⟨167882, by rfl⟩ : syracuseStep 895373 = 335765) B335765
theorem B240209 : Blo 103782 240209 := bstep (se 2 (by rfl) ⟨90078, by rfl⟩ : syracuseStep 240209 = 180157) B180157
theorem B240227 : Blo 103782 240227 := bstep (se 1 (by rfl) ⟨180170, by rfl⟩ : syracuseStep 240227 = 360341) B360341
theorem B240259 : Blo 103782 240259 := bstep (se 1 (by rfl) ⟨180194, by rfl⟩ : syracuseStep 240259 = 360389) B360389
theorem B338701 : Blo 103782 338701 := bstep (se 3 (by rfl) ⟨63506, by rfl⟩ : syracuseStep 338701 = 127013) B127013
theorem B863075 : Blo 103782 863075 := bstep (se 1 (by rfl) ⟨647306, by rfl⟩ : syracuseStep 863075 = 1294613) B1294613
theorem B535409 : Blo 103782 535409 := bstep (se 2 (by rfl) ⟨200778, by rfl⟩ : syracuseStep 535409 = 401557) B401557
theorem B240497 : Blo 103782 240497 := bstep (se 2 (by rfl) ⟨90186, by rfl⟩ : syracuseStep 240497 = 180373) B180373
theorem B240515 : Blo 103782 240515 := bstep (se 1 (by rfl) ⟨180386, by rfl⟩ : syracuseStep 240515 = 360773) B360773
theorem B109555 : Blo 103782 109555 := bstep (se 1 (by rfl) ⟨82166, by rfl⟩ : syracuseStep 109555 = 164333) B164333
theorem B175169 : Blo 103782 175169 := bstep (se 2 (by rfl) ⟨65688, by rfl⟩ : syracuseStep 175169 = 131377) B131377
theorem B306317 : Blo 103782 306317 := bstep (se 3 (by rfl) ⟨57434, by rfl⟩ : syracuseStep 306317 = 114869) B114869
theorem B240785 : Blo 103782 240785 := bstep (se 2 (by rfl) ⟨90294, by rfl⟩ : syracuseStep 240785 = 180589) B180589
theorem B240803 : Blo 103782 240803 := bstep (se 1 (by rfl) ⟨180602, by rfl⟩ : syracuseStep 240803 = 361205) B361205
theorem B175297 : Blo 103782 175297 := bstep (se 2 (by rfl) ⟨65736, by rfl⟩ : syracuseStep 175297 = 131473) B131473
theorem B175331 : Blo 103782 175331 := bstep (se 1 (by rfl) ⟨131498, by rfl⟩ : syracuseStep 175331 = 262997) B262997
theorem B306499 : Blo 103782 306499 := bstep (se 1 (by rfl) ⟨229874, by rfl⟩ : syracuseStep 306499 = 459749) B459749
theorem B175459 : Blo 103782 175459 := bstep (se 1 (by rfl) ⟨131594, by rfl⟩ : syracuseStep 175459 = 263189) B263189
theorem B241073 : Blo 103782 241073 := bstep (se 2 (by rfl) ⟨90402, by rfl⟩ : syracuseStep 241073 = 180805) B180805
theorem B241091 : Blo 103782 241091 := bstep (se 1 (by rfl) ⟨180818, by rfl⟩ : syracuseStep 241091 = 361637) B361637
theorem B306659 : Blo 103782 306659 := bstep (se 1 (by rfl) ⟨229994, by rfl⟩ : syracuseStep 306659 = 459989) B459989
theorem B175601 : Blo 103782 175601 := bstep (se 2 (by rfl) ⟨65850, by rfl⟩ : syracuseStep 175601 = 131701) B131701
theorem B175729 : Blo 103782 175729 := bstep (se 2 (by rfl) ⟨65898, by rfl⟩ : syracuseStep 175729 = 131797) B131797
theorem B667277 : Blo 103782 667277 := bstep (se 3 (by rfl) ⟨125114, by rfl⟩ : syracuseStep 667277 = 250229) B250229
theorem B175763 : Blo 103782 175763 := bstep (se 1 (by rfl) ⟨131822, by rfl⟩ : syracuseStep 175763 = 263645) B263645
theorem B241361 : Blo 103782 241361 := bstep (se 2 (by rfl) ⟨90510, by rfl⟩ : syracuseStep 241361 = 181021) B181021
theorem B241379 : Blo 103782 241379 := bstep (se 1 (by rfl) ⟨181034, by rfl⟩ : syracuseStep 241379 = 362069) B362069
theorem B405233 : Blo 103782 405233 := bstep (se 2 (by rfl) ⟨151962, by rfl⟩ : syracuseStep 405233 = 303925) B303925
theorem B175891 : Blo 103782 175891 := bstep (se 1 (by rfl) ⟨131918, by rfl⟩ : syracuseStep 175891 = 263837) B263837
theorem B3059477 : Blo 103782 3059477 := bstep (se 6 (by rfl) ⟨71706, by rfl⟩ : syracuseStep 3059477 = 143413) B143413
theorem B143219 : Blo 103782 143219 := bstep (se 1 (by rfl) ⟨107414, by rfl⟩ : syracuseStep 143219 = 214829) B214829
theorem B176033 : Blo 103782 176033 := bstep (se 2 (by rfl) ⟨66012, by rfl⟩ : syracuseStep 176033 = 132025) B132025
theorem B241649 : Blo 103782 241649 := bstep (se 2 (by rfl) ⟨90618, by rfl⟩ : syracuseStep 241649 = 181237) B181237
theorem B241667 : Blo 103782 241667 := bstep (se 1 (by rfl) ⟨181250, by rfl⟩ : syracuseStep 241667 = 362501) B362501
theorem B176161 : Blo 103782 176161 := bstep (se 2 (by rfl) ⟨66060, by rfl⟩ : syracuseStep 176161 = 132121) B132121
theorem B274481 : Blo 103782 274481 := bstep (se 2 (by rfl) ⟨102930, by rfl⟩ : syracuseStep 274481 = 205861) B205861
theorem B176195 : Blo 103782 176195 := bstep (se 1 (by rfl) ⟨132146, by rfl⟩ : syracuseStep 176195 = 264293) B264293
theorem B602245 : Blo 103782 602245 := bstep (se 4 (by rfl) ⟨56460, by rfl⟩ : syracuseStep 602245 = 112921) B112921
theorem B176323 : Blo 103782 176323 := bstep (se 1 (by rfl) ⟨132242, by rfl⟩ : syracuseStep 176323 = 264485) B264485
theorem B241937 : Blo 103782 241937 := bstep (se 2 (by rfl) ⟨90726, by rfl⟩ : syracuseStep 241937 = 181453) B181453
theorem B536867 : Blo 103782 536867 := bstep (se 1 (by rfl) ⟨402650, by rfl⟩ : syracuseStep 536867 = 805301) B805301
theorem B733475 : Blo 103782 733475 := bstep (se 1 (by rfl) ⟨550106, by rfl⟩ : syracuseStep 733475 = 1100213) B1100213
theorem B241955 : Blo 103782 241955 := bstep (se 1 (by rfl) ⟨181466, by rfl⟩ : syracuseStep 241955 = 362933) B362933
theorem B340301 : Blo 103782 340301 := bstep (se 3 (by rfl) ⟨63806, by rfl⟩ : syracuseStep 340301 = 127613) B127613
theorem B176465 : Blo 103782 176465 := bstep (se 2 (by rfl) ⟨66174, by rfl⟩ : syracuseStep 176465 = 132349) B132349
theorem B176593 : Blo 103782 176593 := bstep (se 2 (by rfl) ⟨66222, by rfl⟩ : syracuseStep 176593 = 132445) B132445
theorem B176627 : Blo 103782 176627 := bstep (se 1 (by rfl) ⟨132470, by rfl⟩ : syracuseStep 176627 = 264941) B264941
theorem B242225 : Blo 103782 242225 := bstep (se 2 (by rfl) ⟨90834, by rfl⟩ : syracuseStep 242225 = 181669) B181669
theorem B242243 : Blo 103782 242243 := bstep (se 1 (by rfl) ⟨181682, by rfl⟩ : syracuseStep 242243 = 363365) B363365
theorem B176755 : Blo 103782 176755 := bstep (se 1 (by rfl) ⟨132566, by rfl⟩ : syracuseStep 176755 = 265133) B265133
theorem B897763 : Blo 103782 897763 := bstep (se 1 (by rfl) ⟨673322, by rfl⟩ : syracuseStep 897763 = 1346645) B1346645
theorem B635633 : Blo 103782 635633 := bstep (se 2 (by rfl) ⟨238362, by rfl⟩ : syracuseStep 635633 = 476725) B476725
theorem B176897 : Blo 103782 176897 := bstep (se 2 (by rfl) ⟨66336, by rfl⟩ : syracuseStep 176897 = 132673) B132673
theorem B177025 : Blo 103782 177025 := bstep (se 2 (by rfl) ⟨66384, by rfl⟩ : syracuseStep 177025 = 132769) B132769
theorem B177059 : Blo 103782 177059 := bstep (se 1 (by rfl) ⟨132794, by rfl⟩ : syracuseStep 177059 = 265589) B265589
theorem B177187 : Blo 103782 177187 := bstep (se 1 (by rfl) ⟨132890, by rfl⟩ : syracuseStep 177187 = 265781) B265781
theorem B144451 : Blo 103782 144451 := bstep (se 1 (by rfl) ⟨108338, by rfl⟩ : syracuseStep 144451 = 216677) B216677
theorem B537677 : Blo 103782 537677 := bstep (se 3 (by rfl) ⟨100814, by rfl⟩ : syracuseStep 537677 = 201629) B201629
theorem B701581 : Blo 103782 701581 := bstep (se 3 (by rfl) ⟨131546, by rfl⟩ : syracuseStep 701581 = 263093) B263093
theorem B406691 : Blo 103782 406691 := bstep (se 1 (by rfl) ⟨305018, by rfl⟩ : syracuseStep 406691 = 610037) B610037
theorem B177329 : Blo 103782 177329 := bstep (se 2 (by rfl) ⟨66498, by rfl⟩ : syracuseStep 177329 = 132997) B132997
theorem B177457 : Blo 103782 177457 := bstep (se 2 (by rfl) ⟨66546, by rfl⟩ : syracuseStep 177457 = 133093) B133093
theorem B177491 : Blo 103782 177491 := bstep (se 1 (by rfl) ⟨133118, by rfl⟩ : syracuseStep 177491 = 266237) B266237
theorem B505187 : Blo 103782 505187 := bstep (se 1 (by rfl) ⟨378890, by rfl⟩ : syracuseStep 505187 = 757781) B757781
theorem B177619 : Blo 103782 177619 := bstep (se 1 (by rfl) ⟨133214, by rfl⟩ : syracuseStep 177619 = 266429) B266429
theorem B505379 : Blo 103782 505379 := bstep (se 1 (by rfl) ⟨379034, by rfl⟩ : syracuseStep 505379 = 758069) B758069
theorem B112195 : Blo 103782 112195 := bstep (se 1 (by rfl) ⟨84146, by rfl⟩ : syracuseStep 112195 = 168293) B168293
theorem B177761 : Blo 103782 177761 := bstep (se 2 (by rfl) ⟨66660, by rfl⟩ : syracuseStep 177761 = 133321) B133321
theorem B177889 : Blo 103782 177889 := bstep (se 2 (by rfl) ⟨66708, by rfl⟩ : syracuseStep 177889 = 133417) B133417
theorem B177923 : Blo 103782 177923 := bstep (se 1 (by rfl) ⟨133442, by rfl⟩ : syracuseStep 177923 = 266885) B266885
theorem B767843 : Blo 103782 767843 := bstep (se 1 (by rfl) ⟨575882, by rfl⟩ : syracuseStep 767843 = 1151765) B1151765
theorem B178051 : Blo 103782 178051 := bstep (se 1 (by rfl) ⟨133538, by rfl⟩ : syracuseStep 178051 = 267077) B267077
theorem B341891 : Blo 103782 341891 := bstep (se 1 (by rfl) ⟨256418, by rfl⟩ : syracuseStep 341891 = 512837) B512837
theorem B866189 : Blo 103782 866189 := bstep (se 3 (by rfl) ⟨162410, by rfl⟩ : syracuseStep 866189 = 324821) B324821
theorem B505763 : Blo 103782 505763 := bstep (se 1 (by rfl) ⟨379322, by rfl⟩ : syracuseStep 505763 = 758645) B758645
theorem B112627 : Blo 103782 112627 := bstep (se 1 (by rfl) ⟨84470, by rfl⟩ : syracuseStep 112627 = 168941) B168941
theorem B178193 : Blo 103782 178193 := bstep (se 2 (by rfl) ⟨66822, by rfl⟩ : syracuseStep 178193 = 133645) B133645
theorem B342083 : Blo 103782 342083 := bstep (se 1 (by rfl) ⟨256562, by rfl⟩ : syracuseStep 342083 = 513125) B513125
theorem B407693 : Blo 103782 407693 := bstep (se 3 (by rfl) ⟨76442, by rfl⟩ : syracuseStep 407693 = 152885) B152885
theorem B178321 : Blo 103782 178321 := bstep (se 2 (by rfl) ⟨66870, by rfl⟩ : syracuseStep 178321 = 133741) B133741
theorem B178355 : Blo 103782 178355 := bstep (se 1 (by rfl) ⟨133766, by rfl⟩ : syracuseStep 178355 = 267533) B267533
theorem B178483 : Blo 103782 178483 := bstep (se 1 (by rfl) ⟨133862, by rfl⟩ : syracuseStep 178483 = 267725) B267725
theorem B178625 : Blo 103782 178625 := bstep (se 2 (by rfl) ⟨66984, by rfl⟩ : syracuseStep 178625 = 133969) B133969
theorem B178753 : Blo 103782 178753 := bstep (se 2 (by rfl) ⟨67032, by rfl⟩ : syracuseStep 178753 = 134065) B134065
theorem B178787 : Blo 103782 178787 := bstep (se 1 (by rfl) ⟨134090, by rfl⟩ : syracuseStep 178787 = 268181) B268181
theorem B342737 : Blo 103782 342737 := bstep (se 2 (by rfl) ⟨128526, by rfl⟩ : syracuseStep 342737 = 257053) B257053
theorem B178915 : Blo 103782 178915 := bstep (se 1 (by rfl) ⟨134186, by rfl⟩ : syracuseStep 178915 = 268373) B268373
theorem B801521 : Blo 103782 801521 := bstep (se 2 (by rfl) ⟨300570, by rfl⟩ : syracuseStep 801521 = 601141) B601141
theorem B1030897 : Blo 103782 1030897 := bstep (se 2 (by rfl) ⟨386586, by rfl⟩ : syracuseStep 1030897 = 773173) B773173
theorem B998243 : Blo 103782 998243 := bstep (se 1 (by rfl) ⟨748682, by rfl⟩ : syracuseStep 998243 = 1497365) B1497365
theorem B179057 : Blo 103782 179057 := bstep (se 2 (by rfl) ⟨67146, by rfl⟩ : syracuseStep 179057 = 134293) B134293
theorem B179185 : Blo 103782 179185 := bstep (se 2 (by rfl) ⟨67194, by rfl⟩ : syracuseStep 179185 = 134389) B134389
theorem B179219 : Blo 103782 179219 := bstep (se 1 (by rfl) ⟨134414, by rfl⟩ : syracuseStep 179219 = 268829) B268829
theorem B179347 : Blo 103782 179347 := bstep (se 1 (by rfl) ⟨134510, by rfl⟩ : syracuseStep 179347 = 269021) B269021
theorem B113891 : Blo 103782 113891 := bstep (se 1 (by rfl) ⟨85418, by rfl⟩ : syracuseStep 113891 = 170837) B170837
theorem B179489 : Blo 103782 179489 := bstep (se 2 (by rfl) ⟨67308, by rfl⟩ : syracuseStep 179489 = 134617) B134617
theorem B179617 : Blo 103782 179617 := bstep (se 2 (by rfl) ⟨67356, by rfl⟩ : syracuseStep 179617 = 134713) B134713
theorem B703907 : Blo 103782 703907 := bstep (se 1 (by rfl) ⟨527930, by rfl⟩ : syracuseStep 703907 = 1055861) B1055861
theorem B408995 : Blo 103782 408995 := bstep (se 1 (by rfl) ⟨306746, by rfl⟩ : syracuseStep 408995 = 613493) B613493
theorem B179651 : Blo 103782 179651 := bstep (se 1 (by rfl) ⟨134738, by rfl⟩ : syracuseStep 179651 = 269477) B269477
theorem B507377 : Blo 103782 507377 := bstep (se 2 (by rfl) ⟨190266, by rfl⟩ : syracuseStep 507377 = 380533) B380533
theorem B179779 : Blo 103782 179779 := bstep (se 1 (by rfl) ⟨134834, by rfl⟩ : syracuseStep 179779 = 269669) B269669
theorem B179921 : Blo 103782 179921 := bstep (se 2 (by rfl) ⟨67470, by rfl⟩ : syracuseStep 179921 = 134941) B134941
theorem B212753 : Blo 103782 212753 := bstep (se 2 (by rfl) ⟨79782, by rfl⟩ : syracuseStep 212753 = 159565) B159565
theorem B180049 : Blo 103782 180049 := bstep (se 2 (by rfl) ⟨67518, by rfl⟩ : syracuseStep 180049 = 135037) B135037
theorem B507761 : Blo 103782 507761 := bstep (se 2 (by rfl) ⟨190410, by rfl⟩ : syracuseStep 507761 = 380821) B380821
theorem B180083 : Blo 103782 180083 := bstep (se 1 (by rfl) ⟨135062, by rfl⟩ : syracuseStep 180083 = 270125) B270125
theorem B540593 : Blo 103782 540593 := bstep (se 2 (by rfl) ⟨202722, by rfl⟩ : syracuseStep 540593 = 405445) B405445
theorem B114643 : Blo 103782 114643 := bstep (se 1 (by rfl) ⟨85982, by rfl⟩ : syracuseStep 114643 = 171965) B171965
theorem B180211 : Blo 103782 180211 := bstep (se 1 (by rfl) ⟨135158, by rfl⟩ : syracuseStep 180211 = 270317) B270317
theorem B180353 : Blo 103782 180353 := bstep (se 2 (by rfl) ⟨67632, by rfl⟩ : syracuseStep 180353 = 135265) B135265
theorem B606341 : Blo 103782 606341 := bstep (se 4 (by rfl) ⟨56844, by rfl⟩ : syracuseStep 606341 = 113689) B113689
theorem B180481 : Blo 103782 180481 := bstep (se 2 (by rfl) ⟨67680, by rfl⟩ : syracuseStep 180481 = 135361) B135361
theorem B180515 : Blo 103782 180515 := bstep (se 1 (by rfl) ⟨135386, by rfl⟩ : syracuseStep 180515 = 270773) B270773
theorem B672077 : Blo 103782 672077 := bstep (se 3 (by rfl) ⟨126014, by rfl⟩ : syracuseStep 672077 = 252029) B252029
theorem B508301 : Blo 103782 508301 := bstep (se 3 (by rfl) ⟨95306, by rfl⟩ : syracuseStep 508301 = 190613) B190613
theorem B311693 : Blo 103782 311693 := bstep (se 3 (by rfl) ⟨58442, by rfl⟩ : syracuseStep 311693 = 116885) B116885
theorem B180643 : Blo 103782 180643 := bstep (se 1 (by rfl) ⟨135482, by rfl⟩ : syracuseStep 180643 = 270965) B270965
theorem B147953 : Blo 103782 147953 := bstep (se 2 (by rfl) ⟨55482, by rfl⟩ : syracuseStep 147953 = 110965) B110965
theorem B180785 : Blo 103782 180785 := bstep (se 2 (by rfl) ⟨67794, by rfl⟩ : syracuseStep 180785 = 135589) B135589
theorem B770629 : Blo 103782 770629 := bstep (se 4 (by rfl) ⟨72246, by rfl⟩ : syracuseStep 770629 = 144493) B144493
theorem B344749 : Blo 103782 344749 := bstep (se 3 (by rfl) ⟨64640, by rfl⟩ : syracuseStep 344749 = 129281) B129281
theorem B180913 : Blo 103782 180913 := bstep (se 2 (by rfl) ⟨67842, by rfl⟩ : syracuseStep 180913 = 135685) B135685
theorem B180947 : Blo 103782 180947 := bstep (se 1 (by rfl) ⟨135710, by rfl⟩ : syracuseStep 180947 = 271421) B271421
theorem B1262405 : Blo 103782 1262405 := bstep (se 4 (by rfl) ⟨118350, by rfl⟩ : syracuseStep 1262405 = 236701) B236701
theorem B181075 : Blo 103782 181075 := bstep (se 1 (by rfl) ⟨135806, by rfl⟩ : syracuseStep 181075 = 271613) B271613
theorem B1491853 : Blo 103782 1491853 := bstep (se 3 (by rfl) ⟨279722, by rfl⟩ : syracuseStep 1491853 = 559445) B559445
theorem B181217 : Blo 103782 181217 := bstep (se 2 (by rfl) ⟨67956, by rfl⟩ : syracuseStep 181217 = 135913) B135913
theorem B1360867 : Blo 103782 1360867 := bstep (se 1 (by rfl) ⟨1020650, by rfl⟩ : syracuseStep 1360867 = 2041301) B2041301
theorem B148483 : Blo 103782 148483 := bstep (se 1 (by rfl) ⟨111362, by rfl⟩ : syracuseStep 148483 = 222725) B222725
theorem B181345 : Blo 103782 181345 := bstep (se 2 (by rfl) ⟨68004, by rfl⟩ : syracuseStep 181345 = 136009) B136009
theorem B345197 : Blo 103782 345197 := bstep (se 3 (by rfl) ⟨64724, by rfl⟩ : syracuseStep 345197 = 129449) B129449
theorem B214147 : Blo 103782 214147 := bstep (se 1 (by rfl) ⟨160610, by rfl⟩ : syracuseStep 214147 = 321221) B321221
theorem B181379 : Blo 103782 181379 := bstep (se 1 (by rfl) ⟨136034, by rfl⟩ : syracuseStep 181379 = 272069) B272069
theorem B4015331 : Blo 103782 4015331 := bstep (se 1 (by rfl) ⟨3011498, by rfl⟩ : syracuseStep 4015331 = 6022997) B6022997
theorem B181507 : Blo 103782 181507 := bstep (se 1 (by rfl) ⟨136130, by rfl⟩ : syracuseStep 181507 = 272261) B272261
theorem B148819 : Blo 103782 148819 := bstep (se 1 (by rfl) ⟨111614, by rfl⟩ : syracuseStep 148819 = 223229) B223229
theorem B542051 : Blo 103782 542051 := bstep (se 1 (by rfl) ⟨406538, by rfl⟩ : syracuseStep 542051 = 813077) B813077
theorem B607621 : Blo 103782 607621 := bstep (se 4 (by rfl) ⟨56964, by rfl⟩ : syracuseStep 607621 = 113929) B113929
theorem B181649 : Blo 103782 181649 := bstep (se 2 (by rfl) ⟨68118, by rfl⟩ : syracuseStep 181649 = 136237) B136237
theorem B607651 : Blo 103782 607651 := bstep (se 1 (by rfl) ⟨455738, by rfl⟩ : syracuseStep 607651 = 911477) B911477
theorem B443825 : Blo 103782 443825 := bstep (se 2 (by rfl) ⟨166434, by rfl⟩ : syracuseStep 443825 = 332869) B332869
theorem B509453 : Blo 103782 509453 := bstep (se 3 (by rfl) ⟨95522, by rfl⟩ : syracuseStep 509453 = 191045) B191045
theorem B181777 : Blo 103782 181777 := bstep (se 2 (by rfl) ⟨68166, by rfl⟩ : syracuseStep 181777 = 136333) B136333
theorem B640547 : Blo 103782 640547 := bstep (se 1 (by rfl) ⟨480410, by rfl⟩ : syracuseStep 640547 = 960821) B960821
theorem B181811 : Blo 103782 181811 := bstep (se 1 (by rfl) ⟨136358, by rfl⟩ : syracuseStep 181811 = 272717) B272717
theorem B149377 : Blo 103782 149377 := bstep (se 2 (by rfl) ⟨56016, by rfl⟩ : syracuseStep 149377 = 112033) B112033
theorem B149411 : Blo 103782 149411 := bstep (se 1 (by rfl) ⟨112058, by rfl⟩ : syracuseStep 149411 = 224117) B224117
theorem B673733 : Blo 103782 673733 := bstep (se 4 (by rfl) ⟨63162, by rfl⟩ : syracuseStep 673733 = 126325) B126325
theorem B968773 : Blo 103782 968773 := bstep (se 4 (by rfl) ⟨90822, by rfl⟩ : syracuseStep 968773 = 181645) B181645
theorem B116851 : Blo 103782 116851 := bstep (se 1 (by rfl) ⟨87638, by rfl⟩ : syracuseStep 116851 = 175277) B175277
theorem B542861 : Blo 103782 542861 := bstep (se 3 (by rfl) ⟨101786, by rfl⟩ : syracuseStep 542861 = 203573) B203573
theorem B215185 : Blo 103782 215185 := bstep (se 2 (by rfl) ⟨80694, by rfl⟩ : syracuseStep 215185 = 161389) B161389
theorem B2017507 : Blo 103782 2017507 := bstep (se 1 (by rfl) ⟨1513130, by rfl⟩ : syracuseStep 2017507 = 3026261) B3026261
theorem B280817 : Blo 103782 280817 := bstep (se 2 (by rfl) ⟨105306, by rfl⟩ : syracuseStep 280817 = 210613) B210613
theorem B116995 : Blo 103782 116995 := bstep (se 1 (by rfl) ⟨87746, by rfl⟩ : syracuseStep 116995 = 175493) B175493
theorem B510221 : Blo 103782 510221 := bstep (se 3 (by rfl) ⟨95666, by rfl⟩ : syracuseStep 510221 = 191333) B191333
theorem B117139 : Blo 103782 117139 := bstep (se 1 (by rfl) ⟨87854, by rfl⟩ : syracuseStep 117139 = 175709) B175709
theorem B149969 : Blo 103782 149969 := bstep (se 2 (by rfl) ⟨56238, by rfl⟩ : syracuseStep 149969 = 112477) B112477
theorem B150049 : Blo 103782 150049 := bstep (se 2 (by rfl) ⟨56268, by rfl⟩ : syracuseStep 150049 = 112537) B112537
theorem B117283 : Blo 103782 117283 := bstep (se 1 (by rfl) ⟨87962, by rfl⟩ : syracuseStep 117283 = 175925) B175925
theorem B117427 : Blo 103782 117427 := bstep (se 1 (by rfl) ⟨88070, by rfl⟩ : syracuseStep 117427 = 176141) B176141
theorem B609059 : Blo 103782 609059 := bstep (se 1 (by rfl) ⟨456794, by rfl⟩ : syracuseStep 609059 = 913589) B913589
theorem B117571 : Blo 103782 117571 := bstep (se 1 (by rfl) ⟨88178, by rfl⟩ : syracuseStep 117571 = 176357) B176357
theorem B117715 : Blo 103782 117715 := bstep (se 1 (by rfl) ⟨88286, by rfl⟩ : syracuseStep 117715 = 176573) B176573
theorem B117859 : Blo 103782 117859 := bstep (se 1 (by rfl) ⟨88394, by rfl⟩ : syracuseStep 117859 = 176789) B176789
theorem B118003 : Blo 103782 118003 := bstep (se 1 (by rfl) ⟨88502, by rfl⟩ : syracuseStep 118003 = 177005) B177005
theorem B544013 : Blo 103782 544013 := bstep (se 3 (by rfl) ⟨102002, by rfl⟩ : syracuseStep 544013 = 204005) B204005
theorem B150835 : Blo 103782 150835 := bstep (se 1 (by rfl) ⟨113126, by rfl⟩ : syracuseStep 150835 = 226253) B226253
theorem B609605 : Blo 103782 609605 := bstep (se 4 (by rfl) ⟨57150, by rfl⟩ : syracuseStep 609605 = 114301) B114301
theorem B118147 : Blo 103782 118147 := bstep (se 1 (by rfl) ⟨88610, by rfl⟩ : syracuseStep 118147 = 177221) B177221
theorem B118291 : Blo 103782 118291 := bstep (se 1 (by rfl) ⟨88718, by rfl⟩ : syracuseStep 118291 = 177437) B177437
theorem B118435 : Blo 103782 118435 := bstep (se 1 (by rfl) ⟨88826, by rfl⟩ : syracuseStep 118435 = 177653) B177653
theorem B151313 : Blo 103782 151313 := bstep (se 2 (by rfl) ⟨56742, by rfl⟩ : syracuseStep 151313 = 113485) B113485
theorem B118579 : Blo 103782 118579 := bstep (se 1 (by rfl) ⟨88934, by rfl⟩ : syracuseStep 118579 = 177869) B177869
theorem B446285 : Blo 103782 446285 := bstep (se 3 (by rfl) ⟨83678, by rfl⟩ : syracuseStep 446285 = 167357) B167357
theorem B118643 : Blo 103782 118643 := bstep (se 1 (by rfl) ⟨88982, by rfl⟩ : syracuseStep 118643 = 177965) B177965
theorem B151427 : Blo 103782 151427 := bstep (se 1 (by rfl) ⟨113570, by rfl⟩ : syracuseStep 151427 = 227141) B227141
theorem B118723 : Blo 103782 118723 := bstep (se 1 (by rfl) ⟨89042, by rfl⟩ : syracuseStep 118723 = 178085) B178085
theorem B151507 : Blo 103782 151507 := bstep (se 1 (by rfl) ⟨113630, by rfl⟩ : syracuseStep 151507 = 227261) B227261
theorem B118867 : Blo 103782 118867 := bstep (se 1 (by rfl) ⟨89150, by rfl⟩ : syracuseStep 118867 = 178301) B178301
theorem B1101937 : Blo 103782 1101937 := bstep (se 2 (by rfl) ⟨413226, by rfl⟩ : syracuseStep 1101937 = 826453) B826453
theorem B446627 : Blo 103782 446627 := bstep (se 1 (by rfl) ⟨334970, by rfl⟩ : syracuseStep 446627 = 669941) B669941
theorem B119011 : Blo 103782 119011 := bstep (se 1 (by rfl) ⟨89258, by rfl⟩ : syracuseStep 119011 = 178517) B178517
theorem B1069283 : Blo 103782 1069283 := bstep (se 1 (by rfl) ⟨801962, by rfl⟩ : syracuseStep 1069283 = 1603925) B1603925
theorem B119155 : Blo 103782 119155 := bstep (se 1 (by rfl) ⟨89366, by rfl⟩ : syracuseStep 119155 = 178733) B178733
theorem B152065 : Blo 103782 152065 := bstep (se 2 (by rfl) ⟨57024, by rfl⟩ : syracuseStep 152065 = 114049) B114049
theorem B119299 : Blo 103782 119299 := bstep (se 1 (by rfl) ⟨89474, by rfl⟩ : syracuseStep 119299 = 178949) B178949
theorem B217603 : Blo 103782 217603 := bstep (se 1 (by rfl) ⟨163202, by rfl⟩ : syracuseStep 217603 = 326405) B326405
theorem B676451 : Blo 103782 676451 := bstep (se 1 (by rfl) ⟨507338, by rfl⟩ : syracuseStep 676451 = 1014677) B1014677
theorem B119443 : Blo 103782 119443 := bstep (se 1 (by rfl) ⟨89582, by rfl⟩ : syracuseStep 119443 = 179165) B179165
theorem B381617 : Blo 103782 381617 := bstep (se 2 (by rfl) ⟨143106, by rfl⟩ : syracuseStep 381617 = 286213) B286213
theorem B316163 : Blo 103782 316163 := bstep (se 1 (by rfl) ⟨237122, by rfl⟩ : syracuseStep 316163 = 474245) B474245
theorem B119587 : Blo 103782 119587 := bstep (se 1 (by rfl) ⟨89690, by rfl⟩ : syracuseStep 119587 = 179381) B179381
theorem B349105 : Blo 103782 349105 := bstep (se 2 (by rfl) ⟨130914, by rfl⟩ : syracuseStep 349105 = 261829) B261829
theorem B119731 : Blo 103782 119731 := bstep (se 1 (by rfl) ⟨89798, by rfl⟩ : syracuseStep 119731 = 179597) B179597
theorem B250883 : Blo 103782 250883 := bstep (se 1 (by rfl) ⟨188162, by rfl⟩ : syracuseStep 250883 = 376325) B376325
theorem B119875 : Blo 103782 119875 := bstep (se 1 (by rfl) ⟨89906, by rfl⟩ : syracuseStep 119875 = 179813) B179813
theorem B251075 : Blo 103782 251075 := bstep (se 1 (by rfl) ⟨188306, by rfl⟩ : syracuseStep 251075 = 376613) B376613
theorem B152771 : Blo 103782 152771 := bstep (se 1 (by rfl) ⟨114578, by rfl⟩ : syracuseStep 152771 = 229157) B229157
theorem B120019 : Blo 103782 120019 := bstep (se 1 (by rfl) ⟨90014, by rfl⟩ : syracuseStep 120019 = 180029) B180029
theorem B120163 : Blo 103782 120163 := bstep (se 1 (by rfl) ⟨90122, by rfl⟩ : syracuseStep 120163 = 180245) B180245
theorem B251363 : Blo 103782 251363 := bstep (se 1 (by rfl) ⟨188522, by rfl⟩ : syracuseStep 251363 = 377045) B377045
theorem B120307 : Blo 103782 120307 := bstep (se 1 (by rfl) ⟨90230, by rfl⟩ : syracuseStep 120307 = 180461) B180461
theorem B120451 : Blo 103782 120451 := bstep (se 1 (by rfl) ⟨90338, by rfl⟩ : syracuseStep 120451 = 180677) B180677
theorem B120595 : Blo 103782 120595 := bstep (se 1 (by rfl) ⟨90446, by rfl⟩ : syracuseStep 120595 = 180893) B180893
theorem B153409 : Blo 103782 153409 := bstep (se 2 (by rfl) ⟨57528, by rfl⟩ : syracuseStep 153409 = 115057) B115057
theorem B284579 : Blo 103782 284579 := bstep (se 1 (by rfl) ⟨213434, by rfl⟩ : syracuseStep 284579 = 426869) B426869
theorem B120739 : Blo 103782 120739 := bstep (se 1 (by rfl) ⟨90554, by rfl⟩ : syracuseStep 120739 = 181109) B181109
theorem B120883 : Blo 103782 120883 := bstep (se 1 (by rfl) ⟨90662, by rfl⟩ : syracuseStep 120883 = 181325) B181325
theorem B121027 : Blo 103782 121027 := bstep (se 1 (by rfl) ⟨90770, by rfl⟩ : syracuseStep 121027 = 181541) B181541
theorem B350513 : Blo 103782 350513 := bstep (se 2 (by rfl) ⟨131442, by rfl⟩ : syracuseStep 350513 = 262885) B262885
theorem B121171 : Blo 103782 121171 := bstep (se 1 (by rfl) ⟨90878, by rfl⟩ : syracuseStep 121171 = 181757) B181757
theorem B252305 : Blo 103782 252305 := bstep (se 2 (by rfl) ⟨94614, by rfl⟩ : syracuseStep 252305 = 189229) B189229
theorem B678449 : Blo 103782 678449 := bstep (se 2 (by rfl) ⟨254418, by rfl⟩ : syracuseStep 678449 = 508837) B508837
theorem B580229 : Blo 103782 580229 := bstep (se 4 (by rfl) ⟨54396, by rfl⟩ : syracuseStep 580229 = 108793) B108793
theorem B351053 : Blo 103782 351053 := bstep (se 3 (by rfl) ⟨65822, by rfl⟩ : syracuseStep 351053 = 131645) B131645
theorem B351107 : Blo 103782 351107 := bstep (se 1 (by rfl) ⟨263330, by rfl⟩ : syracuseStep 351107 = 526661) B526661
theorem B3398597 : Blo 103782 3398597 := bstep (se 4 (by rfl) ⟨318618, by rfl⟩ : syracuseStep 3398597 = 637237) B637237
theorem B154675 : Blo 103782 154675 := bstep (se 1 (by rfl) ⟨116006, by rfl⟩ : syracuseStep 154675 = 232013) B232013
theorem B613453 : Blo 103782 613453 := bstep (se 3 (by rfl) ⟨115022, by rfl⟩ : syracuseStep 613453 = 230045) B230045
theorem B351377 : Blo 103782 351377 := bstep (se 2 (by rfl) ⟨131766, by rfl⟩ : syracuseStep 351377 = 263533) B263533
theorem B187715 : Blo 103782 187715 := bstep (se 1 (by rfl) ⟨140786, by rfl⟩ : syracuseStep 187715 = 281573) B281573
theorem B220483 : Blo 103782 220483 := bstep (se 1 (by rfl) ⟨165362, by rfl⟩ : syracuseStep 220483 = 330725) B330725
theorem B253265 : Blo 103782 253265 := bstep (se 2 (by rfl) ⟨94974, by rfl⟩ : syracuseStep 253265 = 189949) B189949
theorem B679373 : Blo 103782 679373 := bstep (se 3 (by rfl) ⟨127382, by rfl⟩ : syracuseStep 679373 = 254765) B254765
theorem B351917 : Blo 103782 351917 := bstep (se 3 (by rfl) ⟨65984, by rfl⟩ : syracuseStep 351917 = 131969) B131969
theorem B351971 : Blo 103782 351971 := bstep (se 1 (by rfl) ⟨263978, by rfl⟩ : syracuseStep 351971 = 527957) B527957
theorem B253795 : Blo 103782 253795 := bstep (se 1 (by rfl) ⟨190346, by rfl⟩ : syracuseStep 253795 = 380693) B380693
theorem B352241 : Blo 103782 352241 := bstep (se 2 (by rfl) ⟨132090, by rfl⟩ : syracuseStep 352241 = 264181) B264181
theorem B155681 : Blo 103782 155681 := bstep (se 2 (by rfl) ⟨58380, by rfl⟩ : syracuseStep 155681 = 116761) B116761
theorem B155699 : Blo 103782 155699 := bstep (se 1 (by rfl) ⟨116774, by rfl⟩ : syracuseStep 155699 = 233549) B233549
theorem B155729 : Blo 103782 155729 := bstep (se 2 (by rfl) ⟨58398, by rfl⟩ : syracuseStep 155729 = 116797) B116797
theorem B155747 : Blo 103782 155747 := bstep (se 1 (by rfl) ⟨116810, by rfl⟩ : syracuseStep 155747 = 233621) B233621
theorem B450659 : Blo 103782 450659 := bstep (se 1 (by rfl) ⟨337994, by rfl⟩ : syracuseStep 450659 = 675989) B675989
theorem B155777 : Blo 103782 155777 := bstep (se 2 (by rfl) ⟨58416, by rfl⟩ : syracuseStep 155777 = 116833) B116833
theorem B155795 : Blo 103782 155795 := bstep (se 1 (by rfl) ⟨116846, by rfl⟩ : syracuseStep 155795 = 233693) B233693
theorem B155825 : Blo 103782 155825 := bstep (se 2 (by rfl) ⟨58434, by rfl⟩ : syracuseStep 155825 = 116869) B116869
theorem B155843 : Blo 103782 155843 := bstep (se 1 (by rfl) ⟨116882, by rfl⟩ : syracuseStep 155843 = 233765) B233765
theorem B155873 : Blo 103782 155873 := bstep (se 2 (by rfl) ⟨58452, by rfl⟩ : syracuseStep 155873 = 116905) B116905
theorem B155891 : Blo 103782 155891 := bstep (se 1 (by rfl) ⟨116918, by rfl⟩ : syracuseStep 155891 = 233837) B233837
theorem B155921 : Blo 103782 155921 := bstep (se 2 (by rfl) ⟨58470, by rfl⟩ : syracuseStep 155921 = 116941) B116941
theorem B155939 : Blo 103782 155939 := bstep (se 1 (by rfl) ⟨116954, by rfl⟩ : syracuseStep 155939 = 233909) B233909
theorem B155969 : Blo 103782 155969 := bstep (se 2 (by rfl) ⟨58488, by rfl⟩ : syracuseStep 155969 = 116977) B116977
theorem B581957 : Blo 103782 581957 := bstep (se 4 (by rfl) ⟨54558, by rfl⟩ : syracuseStep 581957 = 109117) B109117
theorem B155987 : Blo 103782 155987 := bstep (se 1 (by rfl) ⟨116990, by rfl⟩ : syracuseStep 155987 = 233981) B233981
theorem B156017 : Blo 103782 156017 := bstep (se 2 (by rfl) ⟨58506, by rfl⟩ : syracuseStep 156017 = 117013) B117013
theorem B156035 : Blo 103782 156035 := bstep (se 1 (by rfl) ⟨117026, by rfl⟩ : syracuseStep 156035 = 234053) B234053
theorem B156065 : Blo 103782 156065 := bstep (se 2 (by rfl) ⟨58524, by rfl⟩ : syracuseStep 156065 = 117049) B117049
theorem B319907 : Blo 103782 319907 := bstep (se 1 (by rfl) ⟨239930, by rfl⟩ : syracuseStep 319907 = 479861) B479861
theorem B156083 : Blo 103782 156083 := bstep (se 1 (by rfl) ⟨117062, by rfl⟩ : syracuseStep 156083 = 234125) B234125
theorem B156113 : Blo 103782 156113 := bstep (se 2 (by rfl) ⟨58542, by rfl⟩ : syracuseStep 156113 = 117085) B117085
theorem B156131 : Blo 103782 156131 := bstep (se 1 (by rfl) ⟨117098, by rfl⟩ : syracuseStep 156131 = 234197) B234197
theorem B156161 : Blo 103782 156161 := bstep (se 2 (by rfl) ⟨58560, by rfl⟩ : syracuseStep 156161 = 117121) B117121
theorem B352781 : Blo 103782 352781 := bstep (se 3 (by rfl) ⟨66146, by rfl⟩ : syracuseStep 352781 = 132293) B132293
theorem B156179 : Blo 103782 156179 := bstep (se 1 (by rfl) ⟨117134, by rfl⟩ : syracuseStep 156179 = 234269) B234269
theorem B188963 : Blo 103782 188963 := bstep (se 1 (by rfl) ⟨141722, by rfl⟩ : syracuseStep 188963 = 283445) B283445
theorem B156209 : Blo 103782 156209 := bstep (se 2 (by rfl) ⟨58578, by rfl⟩ : syracuseStep 156209 = 117157) B117157
theorem B156227 : Blo 103782 156227 := bstep (se 1 (by rfl) ⟨117170, by rfl⟩ : syracuseStep 156227 = 234341) B234341
theorem B352835 : Blo 103782 352835 := bstep (se 1 (by rfl) ⟨264626, by rfl⟩ : syracuseStep 352835 = 529253) B529253
theorem B156257 : Blo 103782 156257 := bstep (se 2 (by rfl) ⟨58596, by rfl⟩ : syracuseStep 156257 = 117193) B117193
theorem B811619 : Blo 103782 811619 := bstep (se 1 (by rfl) ⟨608714, by rfl⟩ : syracuseStep 811619 = 1217429) B1217429
theorem B156275 : Blo 103782 156275 := bstep (se 1 (by rfl) ⟨117206, by rfl⟩ : syracuseStep 156275 = 234413) B234413
theorem B156305 : Blo 103782 156305 := bstep (se 2 (by rfl) ⟨58614, by rfl⟩ : syracuseStep 156305 = 117229) B117229
theorem B156323 : Blo 103782 156323 := bstep (se 1 (by rfl) ⟨117242, by rfl⟩ : syracuseStep 156323 = 234485) B234485
theorem B156353 : Blo 103782 156353 := bstep (se 2 (by rfl) ⟨58632, by rfl⟩ : syracuseStep 156353 = 117265) B117265
theorem B156371 : Blo 103782 156371 := bstep (se 1 (by rfl) ⟨117278, by rfl⟩ : syracuseStep 156371 = 234557) B234557
theorem B156401 : Blo 103782 156401 := bstep (se 2 (by rfl) ⟨58650, by rfl⟩ : syracuseStep 156401 = 117301) B117301
theorem B156419 : Blo 103782 156419 := bstep (se 1 (by rfl) ⟨117314, by rfl⟩ : syracuseStep 156419 = 234629) B234629
theorem B156449 : Blo 103782 156449 := bstep (se 2 (by rfl) ⟨58668, by rfl⟩ : syracuseStep 156449 = 117337) B117337
theorem B156467 : Blo 103782 156467 := bstep (se 1 (by rfl) ⟨117350, by rfl⟩ : syracuseStep 156467 = 234701) B234701
theorem B1696565 : Blo 103782 1696565 := bstep (se 5 (by rfl) ⟨79526, by rfl⟩ : syracuseStep 1696565 = 159053) B159053
theorem B156497 : Blo 103782 156497 := bstep (se 2 (by rfl) ⟨58686, by rfl⟩ : syracuseStep 156497 = 117373) B117373
theorem B353105 : Blo 103782 353105 := bstep (se 2 (by rfl) ⟨132414, by rfl⟩ : syracuseStep 353105 = 264829) B264829
theorem B156515 : Blo 103782 156515 := bstep (se 1 (by rfl) ⟨117386, by rfl⟩ : syracuseStep 156515 = 234773) B234773
theorem B156545 : Blo 103782 156545 := bstep (se 2 (by rfl) ⟨58704, by rfl⟩ : syracuseStep 156545 = 117409) B117409
theorem B156563 : Blo 103782 156563 := bstep (se 1 (by rfl) ⟨117422, by rfl⟩ : syracuseStep 156563 = 234845) B234845
theorem B156593 : Blo 103782 156593 := bstep (se 2 (by rfl) ⟨58722, by rfl⟩ : syracuseStep 156593 = 117445) B117445
theorem B156611 : Blo 103782 156611 := bstep (se 1 (by rfl) ⟨117458, by rfl⟩ : syracuseStep 156611 = 234917) B234917
theorem B156641 : Blo 103782 156641 := bstep (se 2 (by rfl) ⟨58740, by rfl⟩ : syracuseStep 156641 = 117481) B117481
theorem B156659 : Blo 103782 156659 := bstep (se 1 (by rfl) ⟨117494, by rfl⟩ : syracuseStep 156659 = 234989) B234989
theorem B156689 : Blo 103782 156689 := bstep (se 2 (by rfl) ⟨58758, by rfl⟩ : syracuseStep 156689 = 117517) B117517
theorem B156707 : Blo 103782 156707 := bstep (se 1 (by rfl) ⟨117530, by rfl⟩ : syracuseStep 156707 = 235061) B235061
theorem B255025 : Blo 103782 255025 := bstep (se 2 (by rfl) ⟨95634, by rfl⟩ : syracuseStep 255025 = 191269) B191269
theorem B156737 : Blo 103782 156737 := bstep (se 2 (by rfl) ⟨58776, by rfl⟩ : syracuseStep 156737 = 117553) B117553
theorem B156755 : Blo 103782 156755 := bstep (se 1 (by rfl) ⟨117566, by rfl⟩ : syracuseStep 156755 = 235133) B235133
theorem B156785 : Blo 103782 156785 := bstep (se 2 (by rfl) ⟨58794, by rfl⟩ : syracuseStep 156785 = 117589) B117589
theorem B156803 : Blo 103782 156803 := bstep (se 1 (by rfl) ⟨117602, by rfl⟩ : syracuseStep 156803 = 235205) B235205
theorem B156833 : Blo 103782 156833 := bstep (se 2 (by rfl) ⟨58812, by rfl⟩ : syracuseStep 156833 = 117625) B117625
theorem B156851 : Blo 103782 156851 := bstep (se 1 (by rfl) ⟨117638, by rfl⟩ : syracuseStep 156851 = 235277) B235277
theorem B156881 : Blo 103782 156881 := bstep (se 2 (by rfl) ⟨58830, by rfl⟩ : syracuseStep 156881 = 117661) B117661
theorem B156899 : Blo 103782 156899 := bstep (se 1 (by rfl) ⟨117674, by rfl⟩ : syracuseStep 156899 = 235349) B235349
theorem B156929 : Blo 103782 156929 := bstep (se 2 (by rfl) ⟨58848, by rfl⟩ : syracuseStep 156929 = 117697) B117697
theorem B156947 : Blo 103782 156947 := bstep (se 1 (by rfl) ⟨117710, by rfl⟩ : syracuseStep 156947 = 235421) B235421
theorem B156977 : Blo 103782 156977 := bstep (se 2 (by rfl) ⟨58866, by rfl⟩ : syracuseStep 156977 = 117733) B117733
theorem B451889 : Blo 103782 451889 := bstep (se 2 (by rfl) ⟨169458, by rfl⟩ : syracuseStep 451889 = 338917) B338917
theorem B156995 : Blo 103782 156995 := bstep (se 1 (by rfl) ⟨117746, by rfl⟩ : syracuseStep 156995 = 235493) B235493
theorem B157025 : Blo 103782 157025 := bstep (se 2 (by rfl) ⟨58884, by rfl⟩ : syracuseStep 157025 = 117769) B117769
theorem B353645 : Blo 103782 353645 := bstep (se 3 (by rfl) ⟨66308, by rfl⟩ : syracuseStep 353645 = 132617) B132617
theorem B157043 : Blo 103782 157043 := bstep (se 1 (by rfl) ⟨117782, by rfl⟩ : syracuseStep 157043 = 235565) B235565
theorem B157073 : Blo 103782 157073 := bstep (se 2 (by rfl) ⟨58902, by rfl⟩ : syracuseStep 157073 = 117805) B117805
theorem B157091 : Blo 103782 157091 := bstep (se 1 (by rfl) ⟨117818, by rfl⟩ : syracuseStep 157091 = 235637) B235637
theorem B353699 : Blo 103782 353699 := bstep (se 1 (by rfl) ⟨265274, by rfl⟩ : syracuseStep 353699 = 530549) B530549
theorem B157121 : Blo 103782 157121 := bstep (se 2 (by rfl) ⟨58920, by rfl⟩ : syracuseStep 157121 = 117841) B117841
theorem B157139 : Blo 103782 157139 := bstep (se 1 (by rfl) ⟨117854, by rfl⟩ : syracuseStep 157139 = 235709) B235709
theorem B157169 : Blo 103782 157169 := bstep (se 2 (by rfl) ⟨58938, by rfl⟩ : syracuseStep 157169 = 117877) B117877
theorem B157187 : Blo 103782 157187 := bstep (se 1 (by rfl) ⟨117890, by rfl⟩ : syracuseStep 157187 = 235781) B235781
theorem B157217 : Blo 103782 157217 := bstep (se 2 (by rfl) ⟨58956, by rfl⟩ : syracuseStep 157217 = 117913) B117913
theorem B157235 : Blo 103782 157235 := bstep (se 1 (by rfl) ⟨117926, by rfl⟩ : syracuseStep 157235 = 235853) B235853
theorem B157265 : Blo 103782 157265 := bstep (se 2 (by rfl) ⟨58974, by rfl⟩ : syracuseStep 157265 = 117949) B117949
theorem B157283 : Blo 103782 157283 := bstep (se 1 (by rfl) ⟨117962, by rfl⟩ : syracuseStep 157283 = 235925) B235925
theorem B157313 : Blo 103782 157313 := bstep (se 2 (by rfl) ⟨58992, by rfl⟩ : syracuseStep 157313 = 117985) B117985
theorem B157331 : Blo 103782 157331 := bstep (se 1 (by rfl) ⟨117998, by rfl⟩ : syracuseStep 157331 = 235997) B235997
theorem B353969 : Blo 103782 353969 := bstep (se 2 (by rfl) ⟨132738, by rfl⟩ : syracuseStep 353969 = 265477) B265477
theorem B157361 : Blo 103782 157361 := bstep (se 2 (by rfl) ⟨59010, by rfl⟩ : syracuseStep 157361 = 118021) B118021
theorem B157379 : Blo 103782 157379 := bstep (se 1 (by rfl) ⟨118034, by rfl⟩ : syracuseStep 157379 = 236069) B236069
theorem B157409 : Blo 103782 157409 := bstep (se 2 (by rfl) ⟨59028, by rfl⟩ : syracuseStep 157409 = 118057) B118057
theorem B157427 : Blo 103782 157427 := bstep (se 1 (by rfl) ⟨118070, by rfl⟩ : syracuseStep 157427 = 236141) B236141
theorem B157457 : Blo 103782 157457 := bstep (se 2 (by rfl) ⟨59046, by rfl⟩ : syracuseStep 157457 = 118093) B118093
theorem B157475 : Blo 103782 157475 := bstep (se 1 (by rfl) ⟨118106, by rfl⟩ : syracuseStep 157475 = 236213) B236213
theorem B157505 : Blo 103782 157505 := bstep (se 2 (by rfl) ⟨59064, by rfl⟩ : syracuseStep 157505 = 118129) B118129
theorem B157523 : Blo 103782 157523 := bstep (se 1 (by rfl) ⟨118142, by rfl⟩ : syracuseStep 157523 = 236285) B236285
theorem B157553 : Blo 103782 157553 := bstep (se 2 (by rfl) ⟨59082, by rfl⟩ : syracuseStep 157553 = 118165) B118165
theorem B157571 : Blo 103782 157571 := bstep (se 1 (by rfl) ⟨118178, by rfl⟩ : syracuseStep 157571 = 236357) B236357
theorem B157601 : Blo 103782 157601 := bstep (se 2 (by rfl) ⟨59100, by rfl⟩ : syracuseStep 157601 = 118201) B118201
theorem B157619 : Blo 103782 157619 := bstep (se 1 (by rfl) ⟨118214, by rfl⟩ : syracuseStep 157619 = 236429) B236429
theorem B157649 : Blo 103782 157649 := bstep (se 2 (by rfl) ⟨59118, by rfl⟩ : syracuseStep 157649 = 118237) B118237
theorem B157667 : Blo 103782 157667 := bstep (se 1 (by rfl) ⟨118250, by rfl⟩ : syracuseStep 157667 = 236501) B236501
theorem B157697 : Blo 103782 157697 := bstep (se 2 (by rfl) ⟨59136, by rfl⟩ : syracuseStep 157697 = 118273) B118273
theorem B157715 : Blo 103782 157715 := bstep (se 1 (by rfl) ⟨118286, by rfl⟩ : syracuseStep 157715 = 236573) B236573
theorem B157745 : Blo 103782 157745 := bstep (se 2 (by rfl) ⟨59154, by rfl⟩ : syracuseStep 157745 = 118309) B118309
theorem B157763 : Blo 103782 157763 := bstep (se 1 (by rfl) ⟨118322, by rfl⟩ : syracuseStep 157763 = 236645) B236645
theorem B157793 : Blo 103782 157793 := bstep (se 2 (by rfl) ⟨59172, by rfl⟩ : syracuseStep 157793 = 118345) B118345
theorem B190577 : Blo 103782 190577 := bstep (se 2 (by rfl) ⟨71466, by rfl⟩ : syracuseStep 190577 = 142933) B142933
theorem B157811 : Blo 103782 157811 := bstep (se 1 (by rfl) ⟨118358, by rfl⟩ : syracuseStep 157811 = 236717) B236717
theorem B157841 : Blo 103782 157841 := bstep (se 2 (by rfl) ⟨59190, by rfl⟩ : syracuseStep 157841 = 118381) B118381
theorem B157859 : Blo 103782 157859 := bstep (se 1 (by rfl) ⟨118394, by rfl⟩ : syracuseStep 157859 = 236789) B236789
theorem B157889 : Blo 103782 157889 := bstep (se 2 (by rfl) ⟨59208, by rfl⟩ : syracuseStep 157889 = 118417) B118417
theorem B354509 : Blo 103782 354509 := bstep (se 3 (by rfl) ⟨66470, by rfl⟩ : syracuseStep 354509 = 132941) B132941
theorem B157907 : Blo 103782 157907 := bstep (se 1 (by rfl) ⟨118430, by rfl⟩ : syracuseStep 157907 = 236861) B236861
theorem B157937 : Blo 103782 157937 := bstep (se 2 (by rfl) ⟨59226, by rfl⟩ : syracuseStep 157937 = 118453) B118453
theorem B354563 : Blo 103782 354563 := bstep (se 1 (by rfl) ⟨265922, by rfl⟩ : syracuseStep 354563 = 531845) B531845
theorem B157955 : Blo 103782 157955 := bstep (se 1 (by rfl) ⟨118466, by rfl⟩ : syracuseStep 157955 = 236933) B236933
theorem B157985 : Blo 103782 157985 := bstep (se 2 (by rfl) ⟨59244, by rfl⟩ : syracuseStep 157985 = 118489) B118489
theorem B190769 : Blo 103782 190769 := bstep (se 2 (by rfl) ⟨71538, by rfl⟩ : syracuseStep 190769 = 143077) B143077
theorem B158003 : Blo 103782 158003 := bstep (se 1 (by rfl) ⟨118502, by rfl⟩ : syracuseStep 158003 = 237005) B237005
theorem B158033 : Blo 103782 158033 := bstep (se 2 (by rfl) ⟨59262, by rfl⟩ : syracuseStep 158033 = 118525) B118525
theorem B158051 : Blo 103782 158051 := bstep (se 1 (by rfl) ⟨118538, by rfl⟩ : syracuseStep 158051 = 237077) B237077
theorem B158081 : Blo 103782 158081 := bstep (se 2 (by rfl) ⟨59280, by rfl⟩ : syracuseStep 158081 = 118561) B118561
theorem B158099 : Blo 103782 158099 := bstep (se 1 (by rfl) ⟨118574, by rfl⟩ : syracuseStep 158099 = 237149) B237149
theorem B158129 : Blo 103782 158129 := bstep (se 2 (by rfl) ⟨59298, by rfl⟩ : syracuseStep 158129 = 118597) B118597
theorem B158147 : Blo 103782 158147 := bstep (se 1 (by rfl) ⟨118610, by rfl⟩ : syracuseStep 158147 = 237221) B237221
theorem B158177 : Blo 103782 158177 := bstep (se 2 (by rfl) ⟨59316, by rfl⟩ : syracuseStep 158177 = 118633) B118633
theorem B911843 : Blo 103782 911843 := bstep (se 1 (by rfl) ⟨683882, by rfl⟩ : syracuseStep 911843 = 1367765) B1367765
theorem B158195 : Blo 103782 158195 := bstep (se 1 (by rfl) ⟨118646, by rfl⟩ : syracuseStep 158195 = 237293) B237293
theorem B354833 : Blo 103782 354833 := bstep (se 2 (by rfl) ⟨133062, by rfl⟩ : syracuseStep 354833 = 266125) B266125
theorem B158225 : Blo 103782 158225 := bstep (se 2 (by rfl) ⟨59334, by rfl⟩ : syracuseStep 158225 = 118669) B118669
theorem B158243 : Blo 103782 158243 := bstep (se 1 (by rfl) ⟨118682, by rfl⟩ : syracuseStep 158243 = 237365) B237365
theorem B158273 : Blo 103782 158273 := bstep (se 2 (by rfl) ⟨59352, by rfl⟩ : syracuseStep 158273 = 118705) B118705
theorem B158275 : Blo 103782 158275 := bstep (se 1 (by rfl) ⟨118706, by rfl⟩ : syracuseStep 158275 = 237413) B237413
theorem B158291 : Blo 103782 158291 := bstep (se 1 (by rfl) ⟨118718, by rfl⟩ : syracuseStep 158291 = 237437) B237437
theorem B289379 : Blo 103782 289379 := bstep (se 1 (by rfl) ⟨217034, by rfl⟩ : syracuseStep 289379 = 434069) B434069
theorem B158321 : Blo 103782 158321 := bstep (se 2 (by rfl) ⟨59370, by rfl⟩ : syracuseStep 158321 = 118741) B118741
theorem B158339 : Blo 103782 158339 := bstep (se 1 (by rfl) ⟨118754, by rfl⟩ : syracuseStep 158339 = 237509) B237509
theorem B158369 : Blo 103782 158369 := bstep (se 2 (by rfl) ⟨59388, by rfl⟩ : syracuseStep 158369 = 118777) B118777
theorem B158387 : Blo 103782 158387 := bstep (se 1 (by rfl) ⟨118790, by rfl⟩ : syracuseStep 158387 = 237581) B237581
theorem B158417 : Blo 103782 158417 := bstep (se 2 (by rfl) ⟨59406, by rfl⟩ : syracuseStep 158417 = 118813) B118813
theorem B453347 : Blo 103782 453347 := bstep (se 1 (by rfl) ⟨340010, by rfl⟩ : syracuseStep 453347 = 680021) B680021
theorem B158435 : Blo 103782 158435 := bstep (se 1 (by rfl) ⟨118826, by rfl⟩ : syracuseStep 158435 = 237653) B237653
theorem B158465 : Blo 103782 158465 := bstep (se 2 (by rfl) ⟨59424, by rfl⟩ : syracuseStep 158465 = 118849) B118849
theorem B158483 : Blo 103782 158483 := bstep (se 1 (by rfl) ⟨118862, by rfl⟩ : syracuseStep 158483 = 237725) B237725
theorem B158513 : Blo 103782 158513 := bstep (se 2 (by rfl) ⟨59442, by rfl⟩ : syracuseStep 158513 = 118885) B118885
theorem B158531 : Blo 103782 158531 := bstep (se 1 (by rfl) ⟨118898, by rfl⟩ : syracuseStep 158531 = 237797) B237797
theorem B158561 : Blo 103782 158561 := bstep (se 2 (by rfl) ⟨59460, by rfl⟩ : syracuseStep 158561 = 118921) B118921
theorem B158579 : Blo 103782 158579 := bstep (se 1 (by rfl) ⟨118934, by rfl⟩ : syracuseStep 158579 = 237869) B237869
theorem B158609 : Blo 103782 158609 := bstep (se 2 (by rfl) ⟨59478, by rfl⟩ : syracuseStep 158609 = 118957) B118957
theorem B158627 : Blo 103782 158627 := bstep (se 1 (by rfl) ⟨118970, by rfl⟩ : syracuseStep 158627 = 237941) B237941
theorem B158657 : Blo 103782 158657 := bstep (se 2 (by rfl) ⟨59496, by rfl⟩ : syracuseStep 158657 = 118993) B118993
theorem B158675 : Blo 103782 158675 := bstep (se 1 (by rfl) ⟨119006, by rfl⟩ : syracuseStep 158675 = 238013) B238013
theorem B158705 : Blo 103782 158705 := bstep (se 2 (by rfl) ⟨59514, by rfl⟩ : syracuseStep 158705 = 119029) B119029
theorem B158723 : Blo 103782 158723 := bstep (se 1 (by rfl) ⟨119042, by rfl⟩ : syracuseStep 158723 = 238085) B238085
theorem B158753 : Blo 103782 158753 := bstep (se 2 (by rfl) ⟨59532, by rfl⟩ : syracuseStep 158753 = 119065) B119065
theorem B355373 : Blo 103782 355373 := bstep (se 3 (by rfl) ⟨66632, by rfl⟩ : syracuseStep 355373 = 133265) B133265
theorem B158771 : Blo 103782 158771 := bstep (se 1 (by rfl) ⟨119078, by rfl⟩ : syracuseStep 158771 = 238157) B238157
theorem B158801 : Blo 103782 158801 := bstep (se 2 (by rfl) ⟨59550, by rfl⟩ : syracuseStep 158801 = 119101) B119101
theorem B355427 : Blo 103782 355427 := bstep (se 1 (by rfl) ⟨266570, by rfl⟩ : syracuseStep 355427 = 533141) B533141
theorem B158819 : Blo 103782 158819 := bstep (se 1 (by rfl) ⟨119114, by rfl⟩ : syracuseStep 158819 = 238229) B238229
theorem B158849 : Blo 103782 158849 := bstep (se 2 (by rfl) ⟨59568, by rfl⟩ : syracuseStep 158849 = 119137) B119137
theorem B158867 : Blo 103782 158867 := bstep (se 1 (by rfl) ⟨119150, by rfl⟩ : syracuseStep 158867 = 238301) B238301
theorem B158897 : Blo 103782 158897 := bstep (se 2 (by rfl) ⟨59586, by rfl⟩ : syracuseStep 158897 = 119173) B119173
theorem B158915 : Blo 103782 158915 := bstep (se 1 (by rfl) ⟨119186, by rfl⟩ : syracuseStep 158915 = 238373) B238373
theorem B158945 : Blo 103782 158945 := bstep (se 2 (by rfl) ⟨59604, by rfl⟩ : syracuseStep 158945 = 119209) B119209
theorem B158963 : Blo 103782 158963 := bstep (se 1 (by rfl) ⟨119222, by rfl⟩ : syracuseStep 158963 = 238445) B238445
theorem B158993 : Blo 103782 158993 := bstep (se 2 (by rfl) ⟨59622, by rfl⟩ : syracuseStep 158993 = 119245) B119245
theorem B159011 : Blo 103782 159011 := bstep (se 1 (by rfl) ⟨119258, by rfl⟩ : syracuseStep 159011 = 238517) B238517
theorem B159041 : Blo 103782 159041 := bstep (se 2 (by rfl) ⟨59640, by rfl⟩ : syracuseStep 159041 = 119281) B119281
theorem B159059 : Blo 103782 159059 := bstep (se 1 (by rfl) ⟨119294, by rfl⟩ : syracuseStep 159059 = 238589) B238589
theorem B355697 : Blo 103782 355697 := bstep (se 2 (by rfl) ⟨133386, by rfl⟩ : syracuseStep 355697 = 266773) B266773
theorem B159089 : Blo 103782 159089 := bstep (se 2 (by rfl) ⟨59658, by rfl⟩ : syracuseStep 159089 = 119317) B119317
theorem B159107 : Blo 103782 159107 := bstep (se 1 (by rfl) ⟨119330, by rfl⟩ : syracuseStep 159107 = 238661) B238661
theorem B159137 : Blo 103782 159137 := bstep (se 2 (by rfl) ⟨59676, by rfl⟩ : syracuseStep 159137 = 119353) B119353
theorem B159155 : Blo 103782 159155 := bstep (se 1 (by rfl) ⟨119366, by rfl⟩ : syracuseStep 159155 = 238733) B238733
theorem B224707 : Blo 103782 224707 := bstep (se 1 (by rfl) ⟨168530, by rfl⟩ : syracuseStep 224707 = 337061) B337061
theorem B159185 : Blo 103782 159185 := bstep (se 2 (by rfl) ⟨59694, by rfl⟩ : syracuseStep 159185 = 119389) B119389
theorem B159203 : Blo 103782 159203 := bstep (se 1 (by rfl) ⟨119402, by rfl⟩ : syracuseStep 159203 = 238805) B238805
theorem B159233 : Blo 103782 159233 := bstep (se 2 (by rfl) ⟨59712, by rfl⟩ : syracuseStep 159233 = 119425) B119425
theorem B159251 : Blo 103782 159251 := bstep (se 1 (by rfl) ⟨119438, by rfl⟩ : syracuseStep 159251 = 238877) B238877
theorem B159281 : Blo 103782 159281 := bstep (se 2 (by rfl) ⟨59730, by rfl⟩ : syracuseStep 159281 = 119461) B119461
theorem B159299 : Blo 103782 159299 := bstep (se 1 (by rfl) ⟨119474, by rfl⟩ : syracuseStep 159299 = 238949) B238949
theorem B159329 : Blo 103782 159329 := bstep (se 2 (by rfl) ⟨59748, by rfl⟩ : syracuseStep 159329 = 119497) B119497
theorem B159347 : Blo 103782 159347 := bstep (se 1 (by rfl) ⟨119510, by rfl⟩ : syracuseStep 159347 = 239021) B239021
theorem B159377 : Blo 103782 159377 := bstep (se 2 (by rfl) ⟨59766, by rfl⟩ : syracuseStep 159377 = 119533) B119533
theorem B159395 : Blo 103782 159395 := bstep (se 1 (by rfl) ⟨119546, by rfl⟩ : syracuseStep 159395 = 239093) B239093
theorem B159425 : Blo 103782 159425 := bstep (se 2 (by rfl) ⟨59784, by rfl⟩ : syracuseStep 159425 = 119569) B119569
theorem B454349 : Blo 103782 454349 := bstep (se 3 (by rfl) ⟨85190, by rfl⟩ : syracuseStep 454349 = 170381) B170381
theorem B159443 : Blo 103782 159443 := bstep (se 1 (by rfl) ⟨119582, by rfl⟩ : syracuseStep 159443 = 239165) B239165
theorem B159473 : Blo 103782 159473 := bstep (se 2 (by rfl) ⟨59802, by rfl⟩ : syracuseStep 159473 = 119605) B119605
theorem B159491 : Blo 103782 159491 := bstep (se 1 (by rfl) ⟨119618, by rfl⟩ : syracuseStep 159491 = 239237) B239237
theorem B159521 : Blo 103782 159521 := bstep (se 2 (by rfl) ⟨59820, by rfl⟩ : syracuseStep 159521 = 119641) B119641
theorem B159539 : Blo 103782 159539 := bstep (se 1 (by rfl) ⟨119654, by rfl⟩ : syracuseStep 159539 = 239309) B239309
theorem B126787 : Blo 103782 126787 := bstep (se 1 (by rfl) ⟨95090, by rfl⟩ : syracuseStep 126787 = 190181) B190181
theorem B159569 : Blo 103782 159569 := bstep (se 2 (by rfl) ⟨59838, by rfl⟩ : syracuseStep 159569 = 119677) B119677
theorem B159587 : Blo 103782 159587 := bstep (se 1 (by rfl) ⟨119690, by rfl⟩ : syracuseStep 159587 = 239381) B239381
theorem B159617 : Blo 103782 159617 := bstep (se 2 (by rfl) ⟨59856, by rfl⟩ : syracuseStep 159617 = 119713) B119713
theorem B356237 : Blo 103782 356237 := bstep (se 3 (by rfl) ⟨66794, by rfl⟩ : syracuseStep 356237 = 133589) B133589
theorem B159635 : Blo 103782 159635 := bstep (se 1 (by rfl) ⟨119726, by rfl⟩ : syracuseStep 159635 = 239453) B239453
theorem B159665 : Blo 103782 159665 := bstep (se 2 (by rfl) ⟨59874, by rfl⟩ : syracuseStep 159665 = 119749) B119749
theorem B356291 : Blo 103782 356291 := bstep (se 1 (by rfl) ⟨267218, by rfl⟩ : syracuseStep 356291 = 534437) B534437
theorem B159683 : Blo 103782 159683 := bstep (se 1 (by rfl) ⟨119762, by rfl⟩ : syracuseStep 159683 = 239525) B239525
theorem B159713 : Blo 103782 159713 := bstep (se 2 (by rfl) ⟨59892, by rfl⟩ : syracuseStep 159713 = 119785) B119785
theorem B159731 : Blo 103782 159731 := bstep (se 1 (by rfl) ⟨119798, by rfl⟩ : syracuseStep 159731 = 239597) B239597
theorem B159761 : Blo 103782 159761 := bstep (se 2 (by rfl) ⟨59910, by rfl⟩ : syracuseStep 159761 = 119821) B119821
theorem B159779 : Blo 103782 159779 := bstep (se 1 (by rfl) ⟨119834, by rfl⟩ : syracuseStep 159779 = 239669) B239669
theorem B159809 : Blo 103782 159809 := bstep (se 2 (by rfl) ⟨59928, by rfl⟩ : syracuseStep 159809 = 119857) B119857
theorem B159827 : Blo 103782 159827 := bstep (se 1 (by rfl) ⟨119870, by rfl⟩ : syracuseStep 159827 = 239741) B239741
theorem B290915 : Blo 103782 290915 := bstep (se 1 (by rfl) ⟨218186, by rfl⟩ : syracuseStep 290915 = 436373) B436373
theorem B159857 : Blo 103782 159857 := bstep (se 2 (by rfl) ⟨59946, by rfl⟩ : syracuseStep 159857 = 119893) B119893
theorem B159875 : Blo 103782 159875 := bstep (se 1 (by rfl) ⟨119906, by rfl⟩ : syracuseStep 159875 = 239813) B239813
theorem B159905 : Blo 103782 159905 := bstep (se 2 (by rfl) ⟨59964, by rfl⟩ : syracuseStep 159905 = 119929) B119929
theorem B159923 : Blo 103782 159923 := bstep (se 1 (by rfl) ⟨119942, by rfl⟩ : syracuseStep 159923 = 239885) B239885
theorem B127171 : Blo 103782 127171 := bstep (se 1 (by rfl) ⟨95378, by rfl⟩ : syracuseStep 127171 = 190757) B190757
theorem B1142981 : Blo 103782 1142981 := bstep (se 4 (by rfl) ⟨107154, by rfl⟩ : syracuseStep 1142981 = 214309) B214309
theorem B356561 : Blo 103782 356561 := bstep (se 2 (by rfl) ⟨133710, by rfl⟩ : syracuseStep 356561 = 267421) B267421
theorem B159953 : Blo 103782 159953 := bstep (se 2 (by rfl) ⟨59982, by rfl⟩ : syracuseStep 159953 = 119965) B119965
theorem B159971 : Blo 103782 159971 := bstep (se 1 (by rfl) ⟨119978, by rfl⟩ : syracuseStep 159971 = 239957) B239957
theorem B160001 : Blo 103782 160001 := bstep (se 2 (by rfl) ⟨60000, by rfl⟩ : syracuseStep 160001 = 120001) B120001
theorem B160019 : Blo 103782 160019 := bstep (se 1 (by rfl) ⟨120014, by rfl⟩ : syracuseStep 160019 = 240029) B240029
theorem B160049 : Blo 103782 160049 := bstep (se 2 (by rfl) ⟨60018, by rfl⟩ : syracuseStep 160049 = 120037) B120037
theorem B160067 : Blo 103782 160067 := bstep (se 1 (by rfl) ⟨120050, by rfl⟩ : syracuseStep 160067 = 240101) B240101
theorem B160097 : Blo 103782 160097 := bstep (se 2 (by rfl) ⟨60036, by rfl⟩ : syracuseStep 160097 = 120073) B120073
theorem B160115 : Blo 103782 160115 := bstep (se 1 (by rfl) ⟨120086, by rfl⟩ : syracuseStep 160115 = 240173) B240173
theorem B160145 : Blo 103782 160145 := bstep (se 2 (by rfl) ⟨60054, by rfl⟩ : syracuseStep 160145 = 120109) B120109
theorem B160163 : Blo 103782 160163 := bstep (se 1 (by rfl) ⟨120122, by rfl⟩ : syracuseStep 160163 = 240245) B240245
theorem B160193 : Blo 103782 160193 := bstep (se 2 (by rfl) ⟨60072, by rfl⟩ : syracuseStep 160193 = 120145) B120145
theorem B291281 : Blo 103782 291281 := bstep (se 2 (by rfl) ⟨109230, by rfl⟩ : syracuseStep 291281 = 218461) B218461
theorem B160211 : Blo 103782 160211 := bstep (se 1 (by rfl) ⟨120158, by rfl⟩ : syracuseStep 160211 = 240317) B240317
theorem B160241 : Blo 103782 160241 := bstep (se 2 (by rfl) ⟨60090, by rfl⟩ : syracuseStep 160241 = 120181) B120181
theorem B160259 : Blo 103782 160259 := bstep (se 1 (by rfl) ⟨120194, by rfl⟩ : syracuseStep 160259 = 240389) B240389
theorem B160289 : Blo 103782 160289 := bstep (se 2 (by rfl) ⟨60108, by rfl⟩ : syracuseStep 160289 = 120217) B120217
theorem B160307 : Blo 103782 160307 := bstep (se 1 (by rfl) ⟨120230, by rfl⟩ : syracuseStep 160307 = 240461) B240461
theorem B160337 : Blo 103782 160337 := bstep (se 2 (by rfl) ⟨60126, by rfl⟩ : syracuseStep 160337 = 120253) B120253
theorem B160355 : Blo 103782 160355 := bstep (se 1 (by rfl) ⟨120266, by rfl⟩ : syracuseStep 160355 = 240533) B240533
theorem B488035 : Blo 103782 488035 := bstep (se 1 (by rfl) ⟨366026, by rfl⟩ : syracuseStep 488035 = 732053) B732053
theorem B160385 : Blo 103782 160385 := bstep (se 2 (by rfl) ⟨60144, by rfl⟩ : syracuseStep 160385 = 120289) B120289
theorem B160403 : Blo 103782 160403 := bstep (se 1 (by rfl) ⟨120302, by rfl⟩ : syracuseStep 160403 = 240605) B240605
theorem B160433 : Blo 103782 160433 := bstep (se 2 (by rfl) ⟨60162, by rfl⟩ : syracuseStep 160433 = 120325) B120325
theorem B160451 : Blo 103782 160451 := bstep (se 1 (by rfl) ⟨120338, by rfl⟩ : syracuseStep 160451 = 240677) B240677
theorem B160481 : Blo 103782 160481 := bstep (se 2 (by rfl) ⟨60180, by rfl⟩ : syracuseStep 160481 = 120361) B120361
theorem B357101 : Blo 103782 357101 := bstep (se 3 (by rfl) ⟨66956, by rfl⟩ : syracuseStep 357101 = 133913) B133913
theorem B160499 : Blo 103782 160499 := bstep (se 1 (by rfl) ⟨120374, by rfl⟩ : syracuseStep 160499 = 240749) B240749
theorem B160529 : Blo 103782 160529 := bstep (se 2 (by rfl) ⟨60198, by rfl⟩ : syracuseStep 160529 = 120397) B120397
theorem B357155 : Blo 103782 357155 := bstep (se 1 (by rfl) ⟨267866, by rfl⟩ : syracuseStep 357155 = 535733) B535733
theorem B160547 : Blo 103782 160547 := bstep (se 1 (by rfl) ⟨120410, by rfl⟩ : syracuseStep 160547 = 240821) B240821
theorem B160577 : Blo 103782 160577 := bstep (se 2 (by rfl) ⟨60216, by rfl⟩ : syracuseStep 160577 = 120433) B120433
theorem B1307461 : Blo 103782 1307461 := bstep (se 4 (by rfl) ⟨122574, by rfl⟩ : syracuseStep 1307461 = 245149) B245149
theorem B160595 : Blo 103782 160595 := bstep (se 1 (by rfl) ⟨120446, by rfl⟩ : syracuseStep 160595 = 240893) B240893
theorem B160625 : Blo 103782 160625 := bstep (se 2 (by rfl) ⟨60234, by rfl⟩ : syracuseStep 160625 = 120469) B120469
theorem B160643 : Blo 103782 160643 := bstep (se 1 (by rfl) ⟨120482, by rfl⟩ : syracuseStep 160643 = 240965) B240965
theorem B258947 : Blo 103782 258947 := bstep (se 1 (by rfl) ⟨194210, by rfl⟩ : syracuseStep 258947 = 388421) B388421
theorem B160673 : Blo 103782 160673 := bstep (se 2 (by rfl) ⟨60252, by rfl⟩ : syracuseStep 160673 = 120505) B120505
theorem B160691 : Blo 103782 160691 := bstep (se 1 (by rfl) ⟨120518, by rfl⟩ : syracuseStep 160691 = 241037) B241037
theorem B160721 : Blo 103782 160721 := bstep (se 2 (by rfl) ⟨60270, by rfl⟩ : syracuseStep 160721 = 120541) B120541
theorem B160739 : Blo 103782 160739 := bstep (se 1 (by rfl) ⟨120554, by rfl⟩ : syracuseStep 160739 = 241109) B241109
theorem B160769 : Blo 103782 160769 := bstep (se 2 (by rfl) ⟨60288, by rfl⟩ : syracuseStep 160769 = 120577) B120577
theorem B160787 : Blo 103782 160787 := bstep (se 1 (by rfl) ⟨120590, by rfl⟩ : syracuseStep 160787 = 241181) B241181
theorem B357425 : Blo 103782 357425 := bstep (se 2 (by rfl) ⟨134034, by rfl⟩ : syracuseStep 357425 = 268069) B268069
theorem B160817 : Blo 103782 160817 := bstep (se 2 (by rfl) ⟨60306, by rfl⟩ : syracuseStep 160817 = 120613) B120613
theorem B160835 : Blo 103782 160835 := bstep (se 1 (by rfl) ⟨120626, by rfl⟩ : syracuseStep 160835 = 241253) B241253
theorem B160865 : Blo 103782 160865 := bstep (se 2 (by rfl) ⟨60324, by rfl⟩ : syracuseStep 160865 = 120649) B120649
theorem B128099 : Blo 103782 128099 := bstep (se 1 (by rfl) ⟨96074, by rfl⟩ : syracuseStep 128099 = 192149) B192149
theorem B160883 : Blo 103782 160883 := bstep (se 1 (by rfl) ⟨120662, by rfl⟩ : syracuseStep 160883 = 241325) B241325
theorem B160913 : Blo 103782 160913 := bstep (se 2 (by rfl) ⟨60342, by rfl⟩ : syracuseStep 160913 = 120685) B120685
theorem B160915 : Blo 103782 160915 := bstep (se 1 (by rfl) ⟨120686, by rfl⟩ : syracuseStep 160915 = 241373) B241373
theorem B160931 : Blo 103782 160931 := bstep (se 1 (by rfl) ⟨120698, by rfl⟩ : syracuseStep 160931 = 241397) B241397
theorem B160961 : Blo 103782 160961 := bstep (se 2 (by rfl) ⟨60360, by rfl⟩ : syracuseStep 160961 = 120721) B120721
theorem B160979 : Blo 103782 160979 := bstep (se 1 (by rfl) ⟨120734, by rfl⟩ : syracuseStep 160979 = 241469) B241469
theorem B423139 : Blo 103782 423139 := bstep (se 1 (by rfl) ⟨317354, by rfl⟩ : syracuseStep 423139 = 634709) B634709
theorem B161009 : Blo 103782 161009 := bstep (se 2 (by rfl) ⟨60378, by rfl⟩ : syracuseStep 161009 = 120757) B120757
theorem B161027 : Blo 103782 161027 := bstep (se 1 (by rfl) ⟨120770, by rfl⟩ : syracuseStep 161027 = 241541) B241541
theorem B226577 : Blo 103782 226577 := bstep (se 2 (by rfl) ⟨84966, by rfl⟩ : syracuseStep 226577 = 169933) B169933
theorem B161057 : Blo 103782 161057 := bstep (se 2 (by rfl) ⟨60396, by rfl⟩ : syracuseStep 161057 = 120793) B120793
theorem B161075 : Blo 103782 161075 := bstep (se 1 (by rfl) ⟨120806, by rfl⟩ : syracuseStep 161075 = 241613) B241613
theorem B161105 : Blo 103782 161105 := bstep (se 2 (by rfl) ⟨60414, by rfl⟩ : syracuseStep 161105 = 120829) B120829
theorem B161123 : Blo 103782 161123 := bstep (se 1 (by rfl) ⟨120842, by rfl⟩ : syracuseStep 161123 = 241685) B241685
theorem B161153 : Blo 103782 161153 := bstep (se 2 (by rfl) ⟨60432, by rfl⟩ : syracuseStep 161153 = 120865) B120865
theorem B161171 : Blo 103782 161171 := bstep (se 1 (by rfl) ⟨120878, by rfl⟩ : syracuseStep 161171 = 241757) B241757
theorem B161201 : Blo 103782 161201 := bstep (se 2 (by rfl) ⟨60450, by rfl⟩ : syracuseStep 161201 = 120901) B120901
theorem B161219 : Blo 103782 161219 := bstep (se 1 (by rfl) ⟨120914, by rfl⟩ : syracuseStep 161219 = 241829) B241829
theorem B161249 : Blo 103782 161249 := bstep (se 2 (by rfl) ⟨60468, by rfl⟩ : syracuseStep 161249 = 120937) B120937
theorem B161267 : Blo 103782 161267 := bstep (se 1 (by rfl) ⟨120950, by rfl⟩ : syracuseStep 161267 = 241901) B241901
theorem B161297 : Blo 103782 161297 := bstep (se 2 (by rfl) ⟨60486, by rfl⟩ : syracuseStep 161297 = 120973) B120973
theorem B161315 : Blo 103782 161315 := bstep (se 1 (by rfl) ⟨120986, by rfl⟩ : syracuseStep 161315 = 241973) B241973
theorem B161345 : Blo 103782 161345 := bstep (se 2 (by rfl) ⟨60504, by rfl⟩ : syracuseStep 161345 = 121009) B121009
theorem B357965 : Blo 103782 357965 := bstep (se 3 (by rfl) ⟨67118, by rfl⟩ : syracuseStep 357965 = 134237) B134237
theorem B161363 : Blo 103782 161363 := bstep (se 1 (by rfl) ⟨121022, by rfl⟩ : syracuseStep 161363 = 242045) B242045
theorem B161393 : Blo 103782 161393 := bstep (se 2 (by rfl) ⟨60522, by rfl⟩ : syracuseStep 161393 = 121045) B121045
theorem B358019 : Blo 103782 358019 := bstep (se 1 (by rfl) ⟨268514, by rfl⟩ : syracuseStep 358019 = 537029) B537029
theorem B161411 : Blo 103782 161411 := bstep (se 1 (by rfl) ⟨121058, by rfl⟩ : syracuseStep 161411 = 242117) B242117
theorem B161441 : Blo 103782 161441 := bstep (se 2 (by rfl) ⟨60540, by rfl⟩ : syracuseStep 161441 = 121081) B121081
theorem B161459 : Blo 103782 161459 := bstep (se 1 (by rfl) ⟨121094, by rfl⟩ : syracuseStep 161459 = 242189) B242189
theorem B161489 : Blo 103782 161489 := bstep (se 2 (by rfl) ⟨60558, by rfl⟩ : syracuseStep 161489 = 121117) B121117
theorem B161507 : Blo 103782 161507 := bstep (se 1 (by rfl) ⟨121130, by rfl⟩ : syracuseStep 161507 = 242261) B242261
theorem B161537 : Blo 103782 161537 := bstep (se 2 (by rfl) ⟨60576, by rfl⟩ : syracuseStep 161537 = 121153) B121153
theorem B685837 : Blo 103782 685837 := bstep (se 3 (by rfl) ⟨128594, by rfl⟩ : syracuseStep 685837 = 257189) B257189
theorem B161555 : Blo 103782 161555 := bstep (se 1 (by rfl) ⟨121166, by rfl⟩ : syracuseStep 161555 = 242333) B242333
theorem B161585 : Blo 103782 161585 := bstep (se 2 (by rfl) ⟨60594, by rfl⟩ : syracuseStep 161585 = 121189) B121189
theorem B161603 : Blo 103782 161603 := bstep (se 1 (by rfl) ⟨121202, by rfl⟩ : syracuseStep 161603 = 242405) B242405
theorem B816965 : Blo 103782 816965 := bstep (se 4 (by rfl) ⟨76590, by rfl⟩ : syracuseStep 816965 = 153181) B153181
theorem B161633 : Blo 103782 161633 := bstep (se 2 (by rfl) ⟨60612, by rfl⟩ : syracuseStep 161633 = 121225) B121225
theorem B161651 : Blo 103782 161651 := bstep (se 1 (by rfl) ⟨121238, by rfl⟩ : syracuseStep 161651 = 242477) B242477
theorem B358289 : Blo 103782 358289 := bstep (se 2 (by rfl) ⟨134358, by rfl⟩ : syracuseStep 358289 = 268717) B268717
theorem B161779 : Blo 103782 161779 := bstep (se 1 (by rfl) ⟨121334, by rfl⟩ : syracuseStep 161779 = 242669) B242669
theorem B1177699 : Blo 103782 1177699 := bstep (se 1 (by rfl) ⟨883274, by rfl⟩ : syracuseStep 1177699 = 1766549) B1766549
theorem B227441 : Blo 103782 227441 := bstep (se 2 (by rfl) ⟨85290, by rfl⟩ : syracuseStep 227441 = 170581) B170581
theorem B162065 : Blo 103782 162065 := bstep (se 2 (by rfl) ⟨60774, by rfl⟩ : syracuseStep 162065 = 121549) B121549
theorem B260387 : Blo 103782 260387 := bstep (se 1 (by rfl) ⟨195290, by rfl⟩ : syracuseStep 260387 = 390581) B390581
theorem B358829 : Blo 103782 358829 := bstep (se 3 (by rfl) ⟨67280, by rfl⟩ : syracuseStep 358829 = 134561) B134561
theorem B358883 : Blo 103782 358883 := bstep (se 1 (by rfl) ⟨269162, by rfl⟩ : syracuseStep 358883 = 538325) B538325
theorem B686627 : Blo 103782 686627 := bstep (se 1 (by rfl) ⟨514970, by rfl⟩ : syracuseStep 686627 = 1029941) B1029941
theorem B359153 : Blo 103782 359153 := bstep (se 2 (by rfl) ⟨134682, by rfl⟩ : syracuseStep 359153 = 269365) B269365
theorem B260995 : Blo 103782 260995 := bstep (se 1 (by rfl) ⟨195746, by rfl⟩ : syracuseStep 260995 = 391493) B391493
theorem B3013685 : Blo 103782 3013685 := bstep (se 5 (by rfl) ⟨141266, by rfl⟩ : syracuseStep 3013685 = 282533) B282533
theorem B162947 : Blo 103782 162947 := bstep (se 1 (by rfl) ⟨122210, by rfl⟩ : syracuseStep 162947 = 244421) B244421
theorem B359693 : Blo 103782 359693 := bstep (se 3 (by rfl) ⟨67442, by rfl⟩ : syracuseStep 359693 = 134885) B134885
theorem B359747 : Blo 103782 359747 := bstep (se 1 (by rfl) ⟨269810, by rfl⟩ : syracuseStep 359747 = 539621) B539621
theorem B228739 : Blo 103782 228739 := bstep (se 1 (by rfl) ⟨171554, by rfl⟩ : syracuseStep 228739 = 343109) B343109
theorem B327185 : Blo 103782 327185 := bstep (se 2 (by rfl) ⟨122694, by rfl⟩ : syracuseStep 327185 = 245389) B245389
theorem B360017 : Blo 103782 360017 := bstep (se 2 (by rfl) ⟨135006, by rfl⟩ : syracuseStep 360017 = 270013) B270013
theorem B917219 : Blo 103782 917219 := bstep (se 1 (by rfl) ⟨687914, by rfl⟩ : syracuseStep 917219 = 1375829) B1375829
theorem B2817845 : Blo 103782 2817845 := bstep (se 5 (by rfl) ⟨132086, by rfl⟩ : syracuseStep 2817845 = 264173) B264173
theorem B458723 : Blo 103782 458723 := bstep (se 1 (by rfl) ⟨344042, by rfl⟩ : syracuseStep 458723 = 688085) B688085
theorem B360665 : Blo 103782 360665 := bstep (se 2 (by rfl) ⟨135249, by rfl⟩ : syracuseStep 360665 = 270499) B270499
theorem B2851421 : Blo 103782 2851421 := bstep (se 3 (by rfl) ⟨534641, by rfl⟩ : syracuseStep 2851421 = 1069283) B1069283
theorem B262835 : Blo 103782 262835 := bstep (se 1 (by rfl) ⟨197126, by rfl⟩ : syracuseStep 262835 = 394253) B394253
theorem B3211973 : Blo 103782 3211973 := bstep (se 4 (by rfl) ⟨301122, by rfl⟩ : syracuseStep 3211973 = 602245) B602245
theorem B230131 : Blo 103782 230131 := bstep (se 1 (by rfl) ⟨172598, by rfl⟩ : syracuseStep 230131 = 345197) B345197
theorem B131863 : Blo 103782 131863 := bstep (se 1 (by rfl) ⟨98897, by rfl⟩ : syracuseStep 131863 = 197795) B197795
theorem B197491 : Blo 103782 197491 := bstep (se 1 (by rfl) ⟨148118, by rfl⟩ : syracuseStep 197491 = 296237) B296237
theorem B459665 : Blo 103782 459665 := bstep (se 2 (by rfl) ⟨172374, by rfl⟩ : syracuseStep 459665 = 344749) B344749
theorem B361367 : Blo 103782 361367 := bstep (se 1 (by rfl) ⟨271025, by rfl⟩ : syracuseStep 361367 = 542051) B542051
theorem B295883 : Blo 103782 295883 := bstep (se 1 (by rfl) ⟨221912, by rfl⟩ : syracuseStep 295883 = 443825) B443825
theorem B427031 : Blo 103782 427031 := bstep (se 1 (by rfl) ⟨320273, by rfl⟩ : syracuseStep 427031 = 640547) B640547
theorem B853085 : Blo 103782 853085 := bstep (se 3 (by rfl) ⟨159953, by rfl⟩ : syracuseStep 853085 = 319907) B319907
theorem B263371 : Blo 103782 263371 := bstep (se 1 (by rfl) ⟨197528, by rfl⟩ : syracuseStep 263371 = 395057) B395057
theorem B394541 : Blo 103782 394541 := bstep (se 3 (by rfl) ⟨73976, by rfl⟩ : syracuseStep 394541 = 147953) B147953
theorem B197939 : Blo 103782 197939 := bstep (se 1 (by rfl) ⟨148454, by rfl⟩ : syracuseStep 197939 = 296909) B296909
theorem B394571 : Blo 103782 394571 := bstep (se 1 (by rfl) ⟨295928, by rfl⟩ : syracuseStep 394571 = 591857) B591857
theorem B263513 : Blo 103782 263513 := bstep (se 2 (by rfl) ⟨98817, by rfl⟩ : syracuseStep 263513 = 197635) B197635
theorem B197977 : Blo 103782 197977 := bstep (se 2 (by rfl) ⟨74241, by rfl⟩ : syracuseStep 197977 = 148483) B148483
theorem B361907 : Blo 103782 361907 := bstep (se 1 (by rfl) ⟨271430, by rfl⟩ : syracuseStep 361907 = 542861) B542861
theorem B362177 : Blo 103782 362177 := bstep (se 2 (by rfl) ⟨135816, by rfl⟩ : syracuseStep 362177 = 271633) B271633
theorem B198425 : Blo 103782 198425 := bstep (se 2 (by rfl) ⟨74409, by rfl⟩ : syracuseStep 198425 = 148819) B148819
theorem B722819 : Blo 103782 722819 := bstep (se 1 (by rfl) ⟨542114, by rfl⟩ : syracuseStep 722819 = 1084229) B1084229
theorem B395225 : Blo 103782 395225 := bstep (se 2 (by rfl) ⟨148209, by rfl⟩ : syracuseStep 395225 = 296419) B296419
theorem B4524173 : Blo 103782 4524173 := bstep (se 3 (by rfl) ⟨848282, by rfl⟩ : syracuseStep 4524173 = 1696565) B1696565
theorem B264343 : Blo 103782 264343 := bstep (se 1 (by rfl) ⟨198257, by rfl⟩ : syracuseStep 264343 = 396515) B396515
theorem B362675 : Blo 103782 362675 := bstep (se 1 (by rfl) ⟨272006, by rfl⟩ : syracuseStep 362675 = 544013) B544013
theorem B362717 : Blo 103782 362717 := bstep (se 3 (by rfl) ⟨68009, by rfl⟩ : syracuseStep 362717 = 136019) B136019
theorem B395543 : Blo 103782 395543 := bstep (se 1 (by rfl) ⟨296657, by rfl⟩ : syracuseStep 395543 = 593315) B593315
theorem B133579 : Blo 103782 133579 := bstep (se 1 (by rfl) ⟨100184, by rfl⟩ : syracuseStep 133579 = 200369) B200369
theorem B199169 : Blo 103782 199169 := bstep (se 2 (by rfl) ⟨74688, by rfl⟩ : syracuseStep 199169 = 149377) B149377
theorem B461315 : Blo 103782 461315 := bstep (se 1 (by rfl) ⟨345986, by rfl⟩ : syracuseStep 461315 = 691973) B691973
theorem B297523 : Blo 103782 297523 := bstep (se 1 (by rfl) ⟨223142, by rfl⟩ : syracuseStep 297523 = 446285) B446285
theorem B264779 : Blo 103782 264779 := bstep (se 1 (by rfl) ⟨198584, by rfl⟩ : syracuseStep 264779 = 397169) B397169
theorem B199435 : Blo 103782 199435 := bstep (se 1 (by rfl) ⟨149576, by rfl⟩ : syracuseStep 199435 = 299153) B299153
theorem B297751 : Blo 103782 297751 := bstep (se 1 (by rfl) ⟨223313, by rfl⟩ : syracuseStep 297751 = 446627) B446627
theorem B461591 : Blo 103782 461591 := bstep (se 1 (by rfl) ⟨346193, by rfl⟩ : syracuseStep 461591 = 692387) B692387
theorem B396211 : Blo 103782 396211 := bstep (se 1 (by rfl) ⟨297158, by rfl⟩ : syracuseStep 396211 = 594317) B594317
theorem B265153 : Blo 103782 265153 := bstep (se 2 (by rfl) ⟨99432, by rfl⟩ : syracuseStep 265153 = 198865) B198865
theorem B2690009 : Blo 103782 2690009 := bstep (se 2 (by rfl) ⟨1008753, by rfl⟩ : syracuseStep 2690009 = 2017507) B2017507
theorem B2755619 : Blo 103782 2755619 := bstep (se 1 (by rfl) ⟨2066714, by rfl⟩ : syracuseStep 2755619 = 4133429) B4133429
theorem B199883 : Blo 103782 199883 := bstep (se 1 (by rfl) ⟨149912, by rfl⟩ : syracuseStep 199883 = 299825) B299825
theorem B527633 : Blo 103782 527633 := bstep (se 2 (by rfl) ⟨197862, by rfl⟩ : syracuseStep 527633 = 395725) B395725
theorem B167255 : Blo 103782 167255 := bstep (se 1 (by rfl) ⟨125441, by rfl⟩ : syracuseStep 167255 = 250883) B250883
theorem B200065 : Blo 103782 200065 := bstep (se 2 (by rfl) ⟨75024, by rfl⟩ : syracuseStep 200065 = 150049) B150049
theorem B134551 : Blo 103782 134551 := bstep (se 1 (by rfl) ⟨100913, by rfl⟩ : syracuseStep 134551 = 201827) B201827
theorem B527795 : Blo 103782 527795 := bstep (se 1 (by rfl) ⟨395846, by rfl⟩ : syracuseStep 527795 = 791693) B791693
theorem B167383 : Blo 103782 167383 := bstep (se 1 (by rfl) ⟨125537, by rfl⟩ : syracuseStep 167383 = 251075) B251075
theorem B265751 : Blo 103782 265751 := bstep (se 1 (by rfl) ⟨199313, by rfl⟩ : syracuseStep 265751 = 398627) B398627
theorem B200407 : Blo 103782 200407 := bstep (se 1 (by rfl) ⟨150305, by rfl⟩ : syracuseStep 200407 = 300611) B300611
theorem B462667 : Blo 103782 462667 := bstep (se 1 (by rfl) ⟨347000, by rfl⟩ : syracuseStep 462667 = 694001) B694001
theorem B200627 : Blo 103782 200627 := bstep (se 1 (by rfl) ⟨150470, by rfl⟩ : syracuseStep 200627 = 300941) B300941
theorem B397457 : Blo 103782 397457 := bstep (se 2 (by rfl) ⟨149046, by rfl⟩ : syracuseStep 397457 = 298093) B298093
theorem B1183895 : Blo 103782 1183895 := bstep (se 1 (by rfl) ⟨887921, by rfl⟩ : syracuseStep 1183895 = 1775843) B1775843
theorem B200855 : Blo 103782 200855 := bstep (se 1 (by rfl) ⟨150641, by rfl⟩ : syracuseStep 200855 = 301283) B301283
theorem B233675 : Blo 103782 233675 := bstep (se 1 (by rfl) ⟨175256, by rfl⟩ : syracuseStep 233675 = 350513) B350513
theorem B135371 : Blo 103782 135371 := bstep (se 1 (by rfl) ⟨101528, by rfl⟩ : syracuseStep 135371 = 203057) B203057
theorem B233729 : Blo 103782 233729 := bstep (se 2 (by rfl) ⟨87648, by rfl⟩ : syracuseStep 233729 = 175297) B175297
theorem B168203 : Blo 103782 168203 := bstep (se 1 (by rfl) ⟨126152, by rfl⟩ : syracuseStep 168203 = 252305) B252305
theorem B266561 : Blo 103782 266561 := bstep (se 2 (by rfl) ⟨99960, by rfl⟩ : syracuseStep 266561 = 199921) B199921
theorem B201113 : Blo 103782 201113 := bstep (se 2 (by rfl) ⟨75417, by rfl⟩ : syracuseStep 201113 = 150835) B150835
theorem B233945 : Blo 103782 233945 := bstep (se 2 (by rfl) ⟨87729, by rfl⟩ : syracuseStep 233945 = 175459) B175459
theorem B234035 : Blo 103782 234035 := bstep (se 1 (by rfl) ⟨175526, by rfl⟩ : syracuseStep 234035 = 351053) B351053
theorem B234071 : Blo 103782 234071 := bstep (se 1 (by rfl) ⟨175553, by rfl⟩ : syracuseStep 234071 = 351107) B351107
theorem B299609 : Blo 103782 299609 := bstep (se 2 (by rfl) ⟨112353, by rfl⟩ : syracuseStep 299609 = 224707) B224707
theorem B2265731 : Blo 103782 2265731 := bstep (se 1 (by rfl) ⟨1699298, by rfl⟩ : syracuseStep 2265731 = 3398597) B3398597
theorem B234251 : Blo 103782 234251 := bstep (se 1 (by rfl) ⟨175688, by rfl⟩ : syracuseStep 234251 = 351377) B351377
theorem B201523 : Blo 103782 201523 := bstep (se 1 (by rfl) ⟨151142, by rfl⟩ : syracuseStep 201523 = 302285) B302285
theorem B234305 : Blo 103782 234305 := bstep (se 2 (by rfl) ⟨87864, by rfl⟩ : syracuseStep 234305 = 175729) B175729
theorem B398155 : Blo 103782 398155 := bstep (se 1 (by rfl) ⟨298616, by rfl⟩ : syracuseStep 398155 = 597233) B597233
theorem B267097 : Blo 103782 267097 := bstep (se 2 (by rfl) ⟨100161, by rfl⟩ : syracuseStep 267097 = 200323) B200323
theorem B136075 : Blo 103782 136075 := bstep (se 1 (by rfl) ⟨102056, by rfl⟩ : syracuseStep 136075 = 204113) B204113
theorem B431021 : Blo 103782 431021 := bstep (se 3 (by rfl) ⟨80816, by rfl⟩ : syracuseStep 431021 = 161633) B161633
theorem B234521 : Blo 103782 234521 := bstep (se 2 (by rfl) ⟨87945, by rfl⟩ : syracuseStep 234521 = 175891) B175891
theorem B169049 : Blo 103782 169049 := bstep (se 2 (by rfl) ⟨63393, by rfl⟩ : syracuseStep 169049 = 126787) B126787
theorem B398429 : Blo 103782 398429 := bstep (se 3 (by rfl) ⟨74705, by rfl⟩ : syracuseStep 398429 = 149411) B149411
theorem B234611 : Blo 103782 234611 := bstep (se 1 (by rfl) ⟨175958, by rfl⟩ : syracuseStep 234611 = 351917) B351917
theorem B234647 : Blo 103782 234647 := bstep (se 1 (by rfl) ⟨175985, by rfl⟩ : syracuseStep 234647 = 351971) B351971
theorem B136343 : Blo 103782 136343 := bstep (se 1 (by rfl) ⟨102257, by rfl⟩ : syracuseStep 136343 = 204515) B204515
theorem B202009 : Blo 103782 202009 := bstep (se 2 (by rfl) ⟨75753, by rfl⟩ : syracuseStep 202009 = 151507) B151507
theorem B234827 : Blo 103782 234827 := bstep (se 1 (by rfl) ⟨176120, by rfl⟩ : syracuseStep 234827 = 352241) B352241
theorem B529739 : Blo 103782 529739 := bstep (se 1 (by rfl) ⟨397304, by rfl⟩ : syracuseStep 529739 = 794609) B794609
theorem B103787 : Blo 103782 103787 := bstep (se 1 (by rfl) ⟨77840, by rfl⟩ : syracuseStep 103787 = 155681) B155681
theorem B103799 : Blo 103782 103799 := bstep (se 1 (by rfl) ⟨77849, by rfl⟩ : syracuseStep 103799 = 155699) B155699
theorem B234881 : Blo 103782 234881 := bstep (se 2 (by rfl) ⟨88080, by rfl⟩ : syracuseStep 234881 = 176161) B176161
theorem B103819 : Blo 103782 103819 := bstep (se 1 (by rfl) ⟨77864, by rfl⟩ : syracuseStep 103819 = 155729) B155729
theorem B103831 : Blo 103782 103831 := bstep (se 1 (by rfl) ⟨77873, by rfl⟩ : syracuseStep 103831 = 155747) B155747
theorem B300439 : Blo 103782 300439 := bstep (se 1 (by rfl) ⟨225329, by rfl⟩ : syracuseStep 300439 = 450659) B450659
theorem B103851 : Blo 103782 103851 := bstep (se 1 (by rfl) ⟨77888, by rfl⟩ : syracuseStep 103851 = 155777) B155777
theorem B103863 : Blo 103782 103863 := bstep (se 1 (by rfl) ⟨77897, by rfl⟩ : syracuseStep 103863 = 155795) B155795
theorem B103883 : Blo 103782 103883 := bstep (se 1 (by rfl) ⟨77912, by rfl⟩ : syracuseStep 103883 = 155825) B155825
theorem B103895 : Blo 103782 103895 := bstep (se 1 (by rfl) ⟨77921, by rfl⟩ : syracuseStep 103895 = 155843) B155843
theorem B103915 : Blo 103782 103915 := bstep (se 1 (by rfl) ⟨77936, by rfl⟩ : syracuseStep 103915 = 155873) B155873
theorem B103927 : Blo 103782 103927 := bstep (se 1 (by rfl) ⟨77945, by rfl⟩ : syracuseStep 103927 = 155891) B155891
theorem B103947 : Blo 103782 103947 := bstep (se 1 (by rfl) ⟨77960, by rfl⟩ : syracuseStep 103947 = 155921) B155921
theorem B103959 : Blo 103782 103959 := bstep (se 1 (by rfl) ⟨77969, by rfl⟩ : syracuseStep 103959 = 155939) B155939
theorem B103979 : Blo 103782 103979 := bstep (se 1 (by rfl) ⟨77984, by rfl⟩ : syracuseStep 103979 = 155969) B155969
theorem B103991 : Blo 103782 103991 := bstep (se 1 (by rfl) ⟨77993, by rfl⟩ : syracuseStep 103991 = 155987) B155987
theorem B104011 : Blo 103782 104011 := bstep (se 1 (by rfl) ⟨78008, by rfl⟩ : syracuseStep 104011 = 156017) B156017
theorem B104023 : Blo 103782 104023 := bstep (se 1 (by rfl) ⟨78017, by rfl⟩ : syracuseStep 104023 = 156035) B156035
theorem B235097 : Blo 103782 235097 := bstep (se 2 (by rfl) ⟨88161, by rfl⟩ : syracuseStep 235097 = 176323) B176323
theorem B169561 : Blo 103782 169561 := bstep (se 2 (by rfl) ⟨63585, by rfl⟩ : syracuseStep 169561 = 127171) B127171
theorem B104043 : Blo 103782 104043 := bstep (se 1 (by rfl) ⟨78032, by rfl⟩ : syracuseStep 104043 = 156065) B156065
theorem B104055 : Blo 103782 104055 := bstep (se 1 (by rfl) ⟨78041, by rfl⟩ : syracuseStep 104055 = 156083) B156083
theorem B104075 : Blo 103782 104075 := bstep (se 1 (by rfl) ⟨78056, by rfl⟩ : syracuseStep 104075 = 156113) B156113
theorem B104087 : Blo 103782 104087 := bstep (se 1 (by rfl) ⟨78065, by rfl⟩ : syracuseStep 104087 = 156131) B156131
theorem B104107 : Blo 103782 104107 := bstep (se 1 (by rfl) ⟨78080, by rfl⟩ : syracuseStep 104107 = 156161) B156161
theorem B235187 : Blo 103782 235187 := bstep (se 1 (by rfl) ⟨176390, by rfl⟩ : syracuseStep 235187 = 352781) B352781
theorem B104119 : Blo 103782 104119 := bstep (se 1 (by rfl) ⟨78089, by rfl⟩ : syracuseStep 104119 = 156179) B156179
theorem B104139 : Blo 103782 104139 := bstep (se 1 (by rfl) ⟨78104, by rfl⟩ : syracuseStep 104139 = 156209) B156209
theorem B104151 : Blo 103782 104151 := bstep (se 1 (by rfl) ⟨78113, by rfl⟩ : syracuseStep 104151 = 156227) B156227
theorem B235223 : Blo 103782 235223 := bstep (se 1 (by rfl) ⟨176417, by rfl⟩ : syracuseStep 235223 = 352835) B352835
theorem B104171 : Blo 103782 104171 := bstep (se 1 (by rfl) ⟨78128, by rfl⟩ : syracuseStep 104171 = 156257) B156257
theorem B104183 : Blo 103782 104183 := bstep (se 1 (by rfl) ⟨78137, by rfl⟩ : syracuseStep 104183 = 156275) B156275
theorem B104203 : Blo 103782 104203 := bstep (se 1 (by rfl) ⟨78152, by rfl⟩ : syracuseStep 104203 = 156305) B156305
theorem B104215 : Blo 103782 104215 := bstep (se 1 (by rfl) ⟨78161, by rfl⟩ : syracuseStep 104215 = 156323) B156323
theorem B399127 : Blo 103782 399127 := bstep (se 1 (by rfl) ⟨299345, by rfl⟩ : syracuseStep 399127 = 598691) B598691
theorem B104235 : Blo 103782 104235 := bstep (se 1 (by rfl) ⟨78176, by rfl⟩ : syracuseStep 104235 = 156353) B156353
theorem B104247 : Blo 103782 104247 := bstep (se 1 (by rfl) ⟨78185, by rfl⟩ : syracuseStep 104247 = 156371) B156371
theorem B104267 : Blo 103782 104267 := bstep (se 1 (by rfl) ⟨78200, by rfl⟩ : syracuseStep 104267 = 156401) B156401
theorem B202571 : Blo 103782 202571 := bstep (se 1 (by rfl) ⟨151928, by rfl⟩ : syracuseStep 202571 = 303857) B303857
theorem B104279 : Blo 103782 104279 := bstep (se 1 (by rfl) ⟨78209, by rfl⟩ : syracuseStep 104279 = 156419) B156419
theorem B104299 : Blo 103782 104299 := bstep (se 1 (by rfl) ⟨78224, by rfl⟩ : syracuseStep 104299 = 156449) B156449
theorem B104311 : Blo 103782 104311 := bstep (se 1 (by rfl) ⟨78233, by rfl⟩ : syracuseStep 104311 = 156467) B156467
theorem B104331 : Blo 103782 104331 := bstep (se 1 (by rfl) ⟨78248, by rfl⟩ : syracuseStep 104331 = 156497) B156497
theorem B235403 : Blo 103782 235403 := bstep (se 1 (by rfl) ⟨176552, by rfl⟩ : syracuseStep 235403 = 353105) B353105
theorem B104343 : Blo 103782 104343 := bstep (se 1 (by rfl) ⟨78257, by rfl⟩ : syracuseStep 104343 = 156515) B156515
theorem B104363 : Blo 103782 104363 := bstep (se 1 (by rfl) ⟨78272, by rfl⟩ : syracuseStep 104363 = 156545) B156545
theorem B268211 : Blo 103782 268211 := bstep (se 1 (by rfl) ⟨201158, by rfl⟩ : syracuseStep 268211 = 402317) B402317
theorem B104375 : Blo 103782 104375 := bstep (se 1 (by rfl) ⟨78281, by rfl⟩ : syracuseStep 104375 = 156563) B156563
theorem B235457 : Blo 103782 235457 := bstep (se 2 (by rfl) ⟨88296, by rfl⟩ : syracuseStep 235457 = 176593) B176593
theorem B104395 : Blo 103782 104395 := bstep (se 1 (by rfl) ⟨78296, by rfl⟩ : syracuseStep 104395 = 156593) B156593
theorem B104407 : Blo 103782 104407 := bstep (se 1 (by rfl) ⟨78305, by rfl⟩ : syracuseStep 104407 = 156611) B156611
theorem B104427 : Blo 103782 104427 := bstep (se 1 (by rfl) ⟨78320, by rfl⟩ : syracuseStep 104427 = 156641) B156641
theorem B104439 : Blo 103782 104439 := bstep (se 1 (by rfl) ⟨78329, by rfl⟩ : syracuseStep 104439 = 156659) B156659
theorem B202753 : Blo 103782 202753 := bstep (se 2 (by rfl) ⟨76032, by rfl⟩ : syracuseStep 202753 = 152065) B152065
theorem B104459 : Blo 103782 104459 := bstep (se 1 (by rfl) ⟨78344, by rfl⟩ : syracuseStep 104459 = 156689) B156689
theorem B923665 : Blo 103782 923665 := bstep (se 2 (by rfl) ⟨346374, by rfl⟩ : syracuseStep 923665 = 692749) B692749
theorem B104471 : Blo 103782 104471 := bstep (se 1 (by rfl) ⟨78353, by rfl⟩ : syracuseStep 104471 = 156707) B156707
theorem B104491 : Blo 103782 104491 := bstep (se 1 (by rfl) ⟨78368, by rfl⟩ : syracuseStep 104491 = 156737) B156737
theorem B104503 : Blo 103782 104503 := bstep (se 1 (by rfl) ⟨78377, by rfl⟩ : syracuseStep 104503 = 156755) B156755
theorem B104523 : Blo 103782 104523 := bstep (se 1 (by rfl) ⟨78392, by rfl⟩ : syracuseStep 104523 = 156785) B156785
theorem B104535 : Blo 103782 104535 := bstep (se 1 (by rfl) ⟨78401, by rfl⟩ : syracuseStep 104535 = 156803) B156803
theorem B104555 : Blo 103782 104555 := bstep (se 1 (by rfl) ⟨78416, by rfl⟩ : syracuseStep 104555 = 156833) B156833
theorem B104567 : Blo 103782 104567 := bstep (se 1 (by rfl) ⟨78425, by rfl⟩ : syracuseStep 104567 = 156851) B156851
theorem B104587 : Blo 103782 104587 := bstep (se 1 (by rfl) ⟨78440, by rfl⟩ : syracuseStep 104587 = 156881) B156881
theorem B104599 : Blo 103782 104599 := bstep (se 1 (by rfl) ⟨78449, by rfl⟩ : syracuseStep 104599 = 156899) B156899
theorem B235673 : Blo 103782 235673 := bstep (se 2 (by rfl) ⟨88377, by rfl⟩ : syracuseStep 235673 = 176755) B176755
theorem B104619 : Blo 103782 104619 := bstep (se 1 (by rfl) ⟨78464, by rfl⟩ : syracuseStep 104619 = 156929) B156929
theorem B104631 : Blo 103782 104631 := bstep (se 1 (by rfl) ⟨78473, by rfl⟩ : syracuseStep 104631 = 156947) B156947
theorem B104651 : Blo 103782 104651 := bstep (se 1 (by rfl) ⟨78488, by rfl⟩ : syracuseStep 104651 = 156977) B156977
theorem B301259 : Blo 103782 301259 := bstep (se 1 (by rfl) ⟨225944, by rfl⟩ : syracuseStep 301259 = 451889) B451889
theorem B104663 : Blo 103782 104663 := bstep (se 1 (by rfl) ⟨78497, by rfl⟩ : syracuseStep 104663 = 156995) B156995
theorem B268505 : Blo 103782 268505 := bstep (se 2 (by rfl) ⟨100689, by rfl⟩ : syracuseStep 268505 = 201379) B201379
theorem B104683 : Blo 103782 104683 := bstep (se 1 (by rfl) ⟨78512, by rfl⟩ : syracuseStep 104683 = 157025) B157025
theorem B235763 : Blo 103782 235763 := bstep (se 1 (by rfl) ⟨176822, by rfl⟩ : syracuseStep 235763 = 353645) B353645
theorem B104695 : Blo 103782 104695 := bstep (se 1 (by rfl) ⟨78521, by rfl⟩ : syracuseStep 104695 = 157043) B157043
theorem B104715 : Blo 103782 104715 := bstep (se 1 (by rfl) ⟨78536, by rfl⟩ : syracuseStep 104715 = 157073) B157073
theorem B104727 : Blo 103782 104727 := bstep (se 1 (by rfl) ⟨78545, by rfl⟩ : syracuseStep 104727 = 157091) B157091
theorem B235799 : Blo 103782 235799 := bstep (se 1 (by rfl) ⟨176849, by rfl⟩ : syracuseStep 235799 = 353699) B353699
theorem B104747 : Blo 103782 104747 := bstep (se 1 (by rfl) ⟨78560, by rfl⟩ : syracuseStep 104747 = 157121) B157121
theorem B1841453 : Blo 103782 1841453 := bstep (se 3 (by rfl) ⟨345272, by rfl⟩ : syracuseStep 1841453 = 690545) B690545
theorem B104759 : Blo 103782 104759 := bstep (se 1 (by rfl) ⟨78569, by rfl⟩ : syracuseStep 104759 = 157139) B157139
theorem B268609 : Blo 103782 268609 := bstep (se 2 (by rfl) ⟨100728, by rfl⟩ : syracuseStep 268609 = 201457) B201457
theorem B104779 : Blo 103782 104779 := bstep (se 1 (by rfl) ⟨78584, by rfl⟩ : syracuseStep 104779 = 157169) B157169
theorem B104791 : Blo 103782 104791 := bstep (se 1 (by rfl) ⟨78593, by rfl⟩ : syracuseStep 104791 = 157187) B157187
theorem B104811 : Blo 103782 104811 := bstep (se 1 (by rfl) ⟨78608, by rfl⟩ : syracuseStep 104811 = 157217) B157217
theorem B104823 : Blo 103782 104823 := bstep (se 1 (by rfl) ⟨78617, by rfl⟩ : syracuseStep 104823 = 157235) B157235
theorem B104843 : Blo 103782 104843 := bstep (se 1 (by rfl) ⟨78632, by rfl⟩ : syracuseStep 104843 = 157265) B157265
theorem B104855 : Blo 103782 104855 := bstep (se 1 (by rfl) ⟨78641, by rfl⟩ : syracuseStep 104855 = 157283) B157283
theorem B104875 : Blo 103782 104875 := bstep (se 1 (by rfl) ⟨78656, by rfl⟩ : syracuseStep 104875 = 157313) B157313
theorem B1743281 : Blo 103782 1743281 := bstep (se 2 (by rfl) ⟨653730, by rfl⟩ : syracuseStep 1743281 = 1307461) B1307461
theorem B104887 : Blo 103782 104887 := bstep (se 1 (by rfl) ⟨78665, by rfl⟩ : syracuseStep 104887 = 157331) B157331
theorem B235979 : Blo 103782 235979 := bstep (se 1 (by rfl) ⟨176984, by rfl⟩ : syracuseStep 235979 = 353969) B353969
theorem B104907 : Blo 103782 104907 := bstep (se 1 (by rfl) ⟨78680, by rfl⟩ : syracuseStep 104907 = 157361) B157361
theorem B104919 : Blo 103782 104919 := bstep (se 1 (by rfl) ⟨78689, by rfl⟩ : syracuseStep 104919 = 157379) B157379
theorem B104939 : Blo 103782 104939 := bstep (se 1 (by rfl) ⟨78704, by rfl⟩ : syracuseStep 104939 = 157409) B157409
theorem B104951 : Blo 103782 104951 := bstep (se 1 (by rfl) ⟨78713, by rfl⟩ : syracuseStep 104951 = 157427) B157427
theorem B236033 : Blo 103782 236033 := bstep (se 2 (by rfl) ⟨88512, by rfl⟩ : syracuseStep 236033 = 177025) B177025
theorem B104971 : Blo 103782 104971 := bstep (se 1 (by rfl) ⟨78728, by rfl⟩ : syracuseStep 104971 = 157457) B157457
theorem B104983 : Blo 103782 104983 := bstep (se 1 (by rfl) ⟨78737, by rfl⟩ : syracuseStep 104983 = 157475) B157475
theorem B105003 : Blo 103782 105003 := bstep (se 1 (by rfl) ⟨78752, by rfl⟩ : syracuseStep 105003 = 157505) B157505
theorem B399917 : Blo 103782 399917 := bstep (se 3 (by rfl) ⟨74984, by rfl⟩ : syracuseStep 399917 = 149969) B149969
theorem B105015 : Blo 103782 105015 := bstep (se 1 (by rfl) ⟨78761, by rfl⟩ : syracuseStep 105015 = 157523) B157523
theorem B465473 : Blo 103782 465473 := bstep (se 2 (by rfl) ⟨174552, by rfl⟩ : syracuseStep 465473 = 349105) B349105
theorem B105035 : Blo 103782 105035 := bstep (se 1 (by rfl) ⟨78776, by rfl⟩ : syracuseStep 105035 = 157553) B157553
theorem B105047 : Blo 103782 105047 := bstep (se 1 (by rfl) ⟨78785, by rfl⟩ : syracuseStep 105047 = 157571) B157571
theorem B105067 : Blo 103782 105067 := bstep (se 1 (by rfl) ⟨78800, by rfl⟩ : syracuseStep 105067 = 157601) B157601
theorem B105079 : Blo 103782 105079 := bstep (se 1 (by rfl) ⟨78809, by rfl⟩ : syracuseStep 105079 = 157619) B157619
theorem B105099 : Blo 103782 105099 := bstep (se 1 (by rfl) ⟨78824, by rfl⟩ : syracuseStep 105099 = 157649) B157649
theorem B105111 : Blo 103782 105111 := bstep (se 1 (by rfl) ⟨78833, by rfl⟩ : syracuseStep 105111 = 157667) B157667
theorem B105131 : Blo 103782 105131 := bstep (se 1 (by rfl) ⟨78848, by rfl⟩ : syracuseStep 105131 = 157697) B157697
theorem B105143 : Blo 103782 105143 := bstep (se 1 (by rfl) ⟨78857, by rfl⟩ : syracuseStep 105143 = 157715) B157715
theorem B105163 : Blo 103782 105163 := bstep (se 1 (by rfl) ⟨78872, by rfl⟩ : syracuseStep 105163 = 157745) B157745
theorem B203467 : Blo 103782 203467 := bstep (se 1 (by rfl) ⟨152600, by rfl⟩ : syracuseStep 203467 = 305201) B305201
theorem B105175 : Blo 103782 105175 := bstep (se 1 (by rfl) ⟨78881, by rfl⟩ : syracuseStep 105175 = 157763) B157763
theorem B236249 : Blo 103782 236249 := bstep (se 2 (by rfl) ⟨88593, by rfl⟩ : syracuseStep 236249 = 177187) B177187
theorem B105195 : Blo 103782 105195 := bstep (se 1 (by rfl) ⟨78896, by rfl⟩ : syracuseStep 105195 = 157793) B157793
theorem B105207 : Blo 103782 105207 := bstep (se 1 (by rfl) ⟨78905, by rfl⟩ : syracuseStep 105207 = 157811) B157811
theorem B105227 : Blo 103782 105227 := bstep (se 1 (by rfl) ⟨78920, by rfl⟩ : syracuseStep 105227 = 157841) B157841
theorem B105239 : Blo 103782 105239 := bstep (se 1 (by rfl) ⟨78929, by rfl⟩ : syracuseStep 105239 = 157859) B157859
theorem B203543 : Blo 103782 203543 := bstep (se 1 (by rfl) ⟨152657, by rfl⟩ : syracuseStep 203543 = 305315) B305315
theorem B105259 : Blo 103782 105259 := bstep (se 1 (by rfl) ⟨78944, by rfl⟩ : syracuseStep 105259 = 157889) B157889
theorem B236339 : Blo 103782 236339 := bstep (se 1 (by rfl) ⟨177254, by rfl⟩ : syracuseStep 236339 = 354509) B354509
theorem B105271 : Blo 103782 105271 := bstep (se 1 (by rfl) ⟨78953, by rfl⟩ : syracuseStep 105271 = 157907) B157907
theorem B105291 : Blo 103782 105291 := bstep (se 1 (by rfl) ⟨78968, by rfl⟩ : syracuseStep 105291 = 157937) B157937
theorem B236375 : Blo 103782 236375 := bstep (se 1 (by rfl) ⟨177281, by rfl⟩ : syracuseStep 236375 = 354563) B354563
theorem B105303 : Blo 103782 105303 := bstep (se 1 (by rfl) ⟨78977, by rfl⟩ : syracuseStep 105303 = 157955) B157955
theorem B891749 : Blo 103782 891749 := bstep (se 4 (by rfl) ⟨83601, by rfl⟩ : syracuseStep 891749 = 167203) B167203
theorem B105323 : Blo 103782 105323 := bstep (se 1 (by rfl) ⟨78992, by rfl⟩ : syracuseStep 105323 = 157985) B157985
theorem B105335 : Blo 103782 105335 := bstep (se 1 (by rfl) ⟨79001, by rfl⟩ : syracuseStep 105335 = 158003) B158003
theorem B105355 : Blo 103782 105355 := bstep (se 1 (by rfl) ⟨79016, by rfl⟩ : syracuseStep 105355 = 158033) B158033
theorem B105367 : Blo 103782 105367 := bstep (se 1 (by rfl) ⟨79025, by rfl⟩ : syracuseStep 105367 = 158051) B158051
theorem B105387 : Blo 103782 105387 := bstep (se 1 (by rfl) ⟨79040, by rfl⟩ : syracuseStep 105387 = 158081) B158081
theorem B596915 : Blo 103782 596915 := bstep (se 1 (by rfl) ⟨447686, by rfl⟩ : syracuseStep 596915 = 895373) B895373
theorem B105399 : Blo 103782 105399 := bstep (se 1 (by rfl) ⟨79049, by rfl⟩ : syracuseStep 105399 = 158099) B158099
theorem B105419 : Blo 103782 105419 := bstep (se 1 (by rfl) ⟨79064, by rfl⟩ : syracuseStep 105419 = 158129) B158129
theorem B105431 : Blo 103782 105431 := bstep (se 1 (by rfl) ⟨79073, by rfl⟩ : syracuseStep 105431 = 158147) B158147
theorem B564185 : Blo 103782 564185 := bstep (se 2 (by rfl) ⟨211569, by rfl⟩ : syracuseStep 564185 = 423139) B423139
theorem B105451 : Blo 103782 105451 := bstep (se 1 (by rfl) ⟨79088, by rfl⟩ : syracuseStep 105451 = 158177) B158177
theorem B105463 : Blo 103782 105463 := bstep (se 1 (by rfl) ⟨79097, by rfl⟩ : syracuseStep 105463 = 158195) B158195
theorem B236555 : Blo 103782 236555 := bstep (se 1 (by rfl) ⟨177416, by rfl⟩ : syracuseStep 236555 = 354833) B354833
theorem B105483 : Blo 103782 105483 := bstep (se 1 (by rfl) ⟨79112, by rfl⟩ : syracuseStep 105483 = 158225) B158225
theorem B105495 : Blo 103782 105495 := bstep (se 1 (by rfl) ⟨79121, by rfl⟩ : syracuseStep 105495 = 158243) B158243
theorem B105515 : Blo 103782 105515 := bstep (se 1 (by rfl) ⟨79136, by rfl⟩ : syracuseStep 105515 = 158273) B158273
theorem B105527 : Blo 103782 105527 := bstep (se 1 (by rfl) ⟨79145, by rfl⟩ : syracuseStep 105527 = 158291) B158291
theorem B531521 : Blo 103782 531521 := bstep (se 2 (by rfl) ⟨199320, by rfl⟩ : syracuseStep 531521 = 398641) B398641
theorem B236609 : Blo 103782 236609 := bstep (se 2 (by rfl) ⟨88728, by rfl⟩ : syracuseStep 236609 = 177457) B177457
theorem B105547 : Blo 103782 105547 := bstep (se 1 (by rfl) ⟨79160, by rfl⟩ : syracuseStep 105547 = 158321) B158321
theorem B105559 : Blo 103782 105559 := bstep (se 1 (by rfl) ⟨79169, by rfl⟩ : syracuseStep 105559 = 158339) B158339
theorem B105579 : Blo 103782 105579 := bstep (se 1 (by rfl) ⟨79184, by rfl⟩ : syracuseStep 105579 = 158369) B158369
theorem B105591 : Blo 103782 105591 := bstep (se 1 (by rfl) ⟨79193, by rfl⟩ : syracuseStep 105591 = 158387) B158387
theorem B105611 : Blo 103782 105611 := bstep (se 1 (by rfl) ⟨79208, by rfl⟩ : syracuseStep 105611 = 158417) B158417
theorem B302231 : Blo 103782 302231 := bstep (se 1 (by rfl) ⟨226673, by rfl⟩ : syracuseStep 302231 = 453347) B453347
theorem B105623 : Blo 103782 105623 := bstep (se 1 (by rfl) ⟨79217, by rfl⟩ : syracuseStep 105623 = 158435) B158435
theorem B105643 : Blo 103782 105643 := bstep (se 1 (by rfl) ⟨79232, by rfl⟩ : syracuseStep 105643 = 158465) B158465
theorem B105655 : Blo 103782 105655 := bstep (se 1 (by rfl) ⟨79241, by rfl⟩ : syracuseStep 105655 = 158483) B158483
theorem B105675 : Blo 103782 105675 := bstep (se 1 (by rfl) ⟨79256, by rfl⟩ : syracuseStep 105675 = 158513) B158513
theorem B105687 : Blo 103782 105687 := bstep (se 1 (by rfl) ⟨79265, by rfl⟩ : syracuseStep 105687 = 158531) B158531
theorem B105707 : Blo 103782 105707 := bstep (se 1 (by rfl) ⟨79280, by rfl⟩ : syracuseStep 105707 = 158561) B158561
theorem B105719 : Blo 103782 105719 := bstep (se 1 (by rfl) ⟨79289, by rfl⟩ : syracuseStep 105719 = 158579) B158579
theorem B105739 : Blo 103782 105739 := bstep (se 1 (by rfl) ⟨79304, by rfl⟩ : syracuseStep 105739 = 158609) B158609
theorem B105751 : Blo 103782 105751 := bstep (se 1 (by rfl) ⟨79313, by rfl⟩ : syracuseStep 105751 = 158627) B158627
theorem B236825 : Blo 103782 236825 := bstep (se 2 (by rfl) ⟨88809, by rfl⟩ : syracuseStep 236825 = 177619) B177619
theorem B105771 : Blo 103782 105771 := bstep (se 1 (by rfl) ⟨79328, by rfl⟩ : syracuseStep 105771 = 158657) B158657
theorem B105783 : Blo 103782 105783 := bstep (se 1 (by rfl) ⟨79337, by rfl⟩ : syracuseStep 105783 = 158675) B158675
theorem B105803 : Blo 103782 105803 := bstep (se 1 (by rfl) ⟨79352, by rfl⟩ : syracuseStep 105803 = 158705) B158705
theorem B105815 : Blo 103782 105815 := bstep (se 1 (by rfl) ⟨79361, by rfl⟩ : syracuseStep 105815 = 158723) B158723
theorem B105835 : Blo 103782 105835 := bstep (se 1 (by rfl) ⟨79376, by rfl⟩ : syracuseStep 105835 = 158753) B158753
theorem B236915 : Blo 103782 236915 := bstep (se 1 (by rfl) ⟨177686, by rfl⟩ : syracuseStep 236915 = 355373) B355373
theorem B105847 : Blo 103782 105847 := bstep (se 1 (by rfl) ⟨79385, by rfl⟩ : syracuseStep 105847 = 158771) B158771
theorem B105867 : Blo 103782 105867 := bstep (se 1 (by rfl) ⟨79400, by rfl⟩ : syracuseStep 105867 = 158801) B158801
theorem B236951 : Blo 103782 236951 := bstep (se 1 (by rfl) ⟨177713, by rfl⟩ : syracuseStep 236951 = 355427) B355427
theorem B105879 : Blo 103782 105879 := bstep (se 1 (by rfl) ⟨79409, by rfl⟩ : syracuseStep 105879 = 158819) B158819
theorem B105899 : Blo 103782 105899 := bstep (se 1 (by rfl) ⟨79424, by rfl⟩ : syracuseStep 105899 = 158849) B158849
theorem B204211 : Blo 103782 204211 := bstep (se 1 (by rfl) ⟨153158, by rfl⟩ : syracuseStep 204211 = 306317) B306317
theorem B105911 : Blo 103782 105911 := bstep (se 1 (by rfl) ⟨79433, by rfl⟩ : syracuseStep 105911 = 158867) B158867
theorem B105931 : Blo 103782 105931 := bstep (se 1 (by rfl) ⟨79448, by rfl⟩ : syracuseStep 105931 = 158897) B158897
theorem B105943 : Blo 103782 105943 := bstep (se 1 (by rfl) ⟨79457, by rfl⟩ : syracuseStep 105943 = 158915) B158915
theorem B105963 : Blo 103782 105963 := bstep (se 1 (by rfl) ⟨79472, by rfl⟩ : syracuseStep 105963 = 158945) B158945
theorem B105975 : Blo 103782 105975 := bstep (se 1 (by rfl) ⟨79481, by rfl⟩ : syracuseStep 105975 = 158963) B158963
theorem B105995 : Blo 103782 105995 := bstep (se 1 (by rfl) ⟨79496, by rfl⟩ : syracuseStep 105995 = 158993) B158993
theorem B106007 : Blo 103782 106007 := bstep (se 1 (by rfl) ⟨79505, by rfl⟩ : syracuseStep 106007 = 159011) B159011
theorem B106027 : Blo 103782 106027 := bstep (se 1 (by rfl) ⟨79520, by rfl⟩ : syracuseStep 106027 = 159041) B159041
theorem B106039 : Blo 103782 106039 := bstep (se 1 (by rfl) ⟨79529, by rfl⟩ : syracuseStep 106039 = 159059) B159059
theorem B237131 : Blo 103782 237131 := bstep (se 1 (by rfl) ⟨177848, by rfl⟩ : syracuseStep 237131 = 355697) B355697
theorem B106059 : Blo 103782 106059 := bstep (se 1 (by rfl) ⟨79544, by rfl⟩ : syracuseStep 106059 = 159089) B159089
theorem B106071 : Blo 103782 106071 := bstep (se 1 (by rfl) ⟨79553, by rfl⟩ : syracuseStep 106071 = 159107) B159107
theorem B106091 : Blo 103782 106091 := bstep (se 1 (by rfl) ⟨79568, by rfl⟩ : syracuseStep 106091 = 159137) B159137
theorem B106103 : Blo 103782 106103 := bstep (se 1 (by rfl) ⟨79577, by rfl⟩ : syracuseStep 106103 = 159155) B159155
theorem B237185 : Blo 103782 237185 := bstep (se 2 (by rfl) ⟨88944, by rfl⟩ : syracuseStep 237185 = 177889) B177889
theorem B106123 : Blo 103782 106123 := bstep (se 1 (by rfl) ⟨79592, by rfl⟩ : syracuseStep 106123 = 159185) B159185
theorem B106135 : Blo 103782 106135 := bstep (se 1 (by rfl) ⟨79601, by rfl⟩ : syracuseStep 106135 = 159203) B159203
theorem B204439 : Blo 103782 204439 := bstep (se 1 (by rfl) ⟨153329, by rfl⟩ : syracuseStep 204439 = 306659) B306659
theorem B106155 : Blo 103782 106155 := bstep (se 1 (by rfl) ⟨79616, by rfl⟩ : syracuseStep 106155 = 159233) B159233
theorem B106167 : Blo 103782 106167 := bstep (se 1 (by rfl) ⟨79625, by rfl⟩ : syracuseStep 106167 = 159251) B159251
theorem B106187 : Blo 103782 106187 := bstep (se 1 (by rfl) ⟨79640, by rfl⟩ : syracuseStep 106187 = 159281) B159281
theorem B106199 : Blo 103782 106199 := bstep (se 1 (by rfl) ⟨79649, by rfl⟩ : syracuseStep 106199 = 159299) B159299
theorem B106219 : Blo 103782 106219 := bstep (se 1 (by rfl) ⟨79664, by rfl⟩ : syracuseStep 106219 = 159329) B159329
theorem B106231 : Blo 103782 106231 := bstep (se 1 (by rfl) ⟨79673, by rfl⟩ : syracuseStep 106231 = 159347) B159347
theorem B204545 : Blo 103782 204545 := bstep (se 2 (by rfl) ⟨76704, by rfl⟩ : syracuseStep 204545 = 153409) B153409
theorem B106251 : Blo 103782 106251 := bstep (se 1 (by rfl) ⟨79688, by rfl⟩ : syracuseStep 106251 = 159377) B159377
theorem B106263 : Blo 103782 106263 := bstep (se 1 (by rfl) ⟨79697, by rfl⟩ : syracuseStep 106263 = 159395) B159395
theorem B106283 : Blo 103782 106283 := bstep (se 1 (by rfl) ⟨79712, by rfl⟩ : syracuseStep 106283 = 159425) B159425
theorem B106295 : Blo 103782 106295 := bstep (se 1 (by rfl) ⟨79721, by rfl⟩ : syracuseStep 106295 = 159443) B159443
theorem B106315 : Blo 103782 106315 := bstep (se 1 (by rfl) ⟨79736, by rfl⟩ : syracuseStep 106315 = 159473) B159473
theorem B270155 : Blo 103782 270155 := bstep (se 1 (by rfl) ⟨202616, by rfl⟩ : syracuseStep 270155 = 405233) B405233
theorem B106327 : Blo 103782 106327 := bstep (se 1 (by rfl) ⟨79745, by rfl⟩ : syracuseStep 106327 = 159491) B159491
theorem B237401 : Blo 103782 237401 := bstep (se 2 (by rfl) ⟨89025, by rfl⟩ : syracuseStep 237401 = 178051) B178051
theorem B2039651 : Blo 103782 2039651 := bstep (se 1 (by rfl) ⟨1529738, by rfl⟩ : syracuseStep 2039651 = 3059477) B3059477
theorem B106347 : Blo 103782 106347 := bstep (se 1 (by rfl) ⟨79760, by rfl⟩ : syracuseStep 106347 = 159521) B159521
theorem B106359 : Blo 103782 106359 := bstep (se 1 (by rfl) ⟨79769, by rfl⟩ : syracuseStep 106359 = 159539) B159539
theorem B106379 : Blo 103782 106379 := bstep (se 1 (by rfl) ⟨79784, by rfl⟩ : syracuseStep 106379 = 159569) B159569
theorem B106391 : Blo 103782 106391 := bstep (se 1 (by rfl) ⟨79793, by rfl⟩ : syracuseStep 106391 = 159587) B159587
theorem B106411 : Blo 103782 106411 := bstep (se 1 (by rfl) ⟨79808, by rfl⟩ : syracuseStep 106411 = 159617) B159617
theorem B237491 : Blo 103782 237491 := bstep (se 1 (by rfl) ⟨178118, by rfl⟩ : syracuseStep 237491 = 356237) B356237
theorem B106423 : Blo 103782 106423 := bstep (se 1 (by rfl) ⟨79817, by rfl⟩ : syracuseStep 106423 = 159635) B159635
theorem B401345 : Blo 103782 401345 := bstep (se 2 (by rfl) ⟨150504, by rfl⟩ : syracuseStep 401345 = 301009) B301009
theorem B106443 : Blo 103782 106443 := bstep (se 1 (by rfl) ⟨79832, by rfl⟩ : syracuseStep 106443 = 159665) B159665
theorem B237527 : Blo 103782 237527 := bstep (se 1 (by rfl) ⟨178145, by rfl⟩ : syracuseStep 237527 = 356291) B356291
theorem B106455 : Blo 103782 106455 := bstep (se 1 (by rfl) ⟨79841, by rfl⟩ : syracuseStep 106455 = 159683) B159683
theorem B106475 : Blo 103782 106475 := bstep (se 1 (by rfl) ⟨79856, by rfl⟩ : syracuseStep 106475 = 159713) B159713
theorem B106487 : Blo 103782 106487 := bstep (se 1 (by rfl) ⟨79865, by rfl⟩ : syracuseStep 106487 = 159731) B159731
theorem B106507 : Blo 103782 106507 := bstep (se 1 (by rfl) ⟨79880, by rfl⟩ : syracuseStep 106507 = 159761) B159761
theorem B106519 : Blo 103782 106519 := bstep (se 1 (by rfl) ⟨79889, by rfl⟩ : syracuseStep 106519 = 159779) B159779
theorem B106539 : Blo 103782 106539 := bstep (se 1 (by rfl) ⟨79904, by rfl⟩ : syracuseStep 106539 = 159809) B159809
theorem B106551 : Blo 103782 106551 := bstep (se 1 (by rfl) ⟨79913, by rfl⟩ : syracuseStep 106551 = 159827) B159827
theorem B106571 : Blo 103782 106571 := bstep (se 1 (by rfl) ⟨79928, by rfl⟩ : syracuseStep 106571 = 159857) B159857
theorem B106583 : Blo 103782 106583 := bstep (se 1 (by rfl) ⟨79937, by rfl⟩ : syracuseStep 106583 = 159875) B159875
theorem B106603 : Blo 103782 106603 := bstep (se 1 (by rfl) ⟨79952, by rfl⟩ : syracuseStep 106603 = 159905) B159905
theorem B106615 : Blo 103782 106615 := bstep (se 1 (by rfl) ⟨79961, by rfl⟩ : syracuseStep 106615 = 159923) B159923
theorem B761987 : Blo 103782 761987 := bstep (se 1 (by rfl) ⟨571490, by rfl⟩ : syracuseStep 761987 = 1142981) B1142981
theorem B237707 : Blo 103782 237707 := bstep (se 1 (by rfl) ⟨178280, by rfl⟩ : syracuseStep 237707 = 356561) B356561
theorem B106635 : Blo 103782 106635 := bstep (se 1 (by rfl) ⟨79976, by rfl⟩ : syracuseStep 106635 = 159953) B159953
theorem B106647 : Blo 103782 106647 := bstep (se 1 (by rfl) ⟨79985, by rfl⟩ : syracuseStep 106647 = 159971) B159971
theorem B106667 : Blo 103782 106667 := bstep (se 1 (by rfl) ⟨80000, by rfl⟩ : syracuseStep 106667 = 160001) B160001
theorem B106679 : Blo 103782 106679 := bstep (se 1 (by rfl) ⟨80009, by rfl⟩ : syracuseStep 106679 = 160019) B160019
theorem B237761 : Blo 103782 237761 := bstep (se 2 (by rfl) ⟨89160, by rfl⟩ : syracuseStep 237761 = 178321) B178321
theorem B106699 : Blo 103782 106699 := bstep (se 1 (by rfl) ⟨80024, by rfl⟩ : syracuseStep 106699 = 160049) B160049
theorem B106711 : Blo 103782 106711 := bstep (se 1 (by rfl) ⟨80033, by rfl⟩ : syracuseStep 106711 = 160067) B160067
theorem B106731 : Blo 103782 106731 := bstep (se 1 (by rfl) ⟨80048, by rfl⟩ : syracuseStep 106731 = 160097) B160097
theorem B106743 : Blo 103782 106743 := bstep (se 1 (by rfl) ⟨80057, by rfl⟩ : syracuseStep 106743 = 160115) B160115
theorem B106763 : Blo 103782 106763 := bstep (se 1 (by rfl) ⟨80072, by rfl⟩ : syracuseStep 106763 = 160145) B160145
theorem B106775 : Blo 103782 106775 := bstep (se 1 (by rfl) ⟨80081, by rfl⟩ : syracuseStep 106775 = 160163) B160163
theorem B106795 : Blo 103782 106795 := bstep (se 1 (by rfl) ⟨80096, by rfl⟩ : syracuseStep 106795 = 160193) B160193
theorem B106807 : Blo 103782 106807 := bstep (se 1 (by rfl) ⟨80105, by rfl⟩ : syracuseStep 106807 = 160211) B160211
theorem B106827 : Blo 103782 106827 := bstep (se 1 (by rfl) ⟨80120, by rfl⟩ : syracuseStep 106827 = 160241) B160241
theorem B106839 : Blo 103782 106839 := bstep (se 1 (by rfl) ⟨80129, by rfl⟩ : syracuseStep 106839 = 160259) B160259
theorem B598373 : Blo 103782 598373 := bstep (se 4 (by rfl) ⟨56097, by rfl⟩ : syracuseStep 598373 = 112195) B112195
theorem B106859 : Blo 103782 106859 := bstep (se 1 (by rfl) ⟨80144, by rfl⟩ : syracuseStep 106859 = 160289) B160289
theorem B106871 : Blo 103782 106871 := bstep (se 1 (by rfl) ⟨80153, by rfl⟩ : syracuseStep 106871 = 160307) B160307
theorem B106891 : Blo 103782 106891 := bstep (se 1 (by rfl) ⟨80168, by rfl⟩ : syracuseStep 106891 = 160337) B160337
theorem B106903 : Blo 103782 106903 := bstep (se 1 (by rfl) ⟨80177, by rfl⟩ : syracuseStep 106903 = 160355) B160355
theorem B237977 : Blo 103782 237977 := bstep (se 2 (by rfl) ⟨89241, by rfl⟩ : syracuseStep 237977 = 178483) B178483
theorem B106923 : Blo 103782 106923 := bstep (se 1 (by rfl) ⟨80192, by rfl⟩ : syracuseStep 106923 = 160385) B160385
theorem B106935 : Blo 103782 106935 := bstep (se 1 (by rfl) ⟨80201, by rfl⟩ : syracuseStep 106935 = 160403) B160403
theorem B106955 : Blo 103782 106955 := bstep (se 1 (by rfl) ⟨80216, by rfl⟩ : syracuseStep 106955 = 160433) B160433
theorem B893389 : Blo 103782 893389 := bstep (se 3 (by rfl) ⟨167510, by rfl⟩ : syracuseStep 893389 = 335021) B335021
theorem B106967 : Blo 103782 106967 := bstep (se 1 (by rfl) ⟨80225, by rfl⟩ : syracuseStep 106967 = 160451) B160451
theorem B106987 : Blo 103782 106987 := bstep (se 1 (by rfl) ⟨80240, by rfl⟩ : syracuseStep 106987 = 160481) B160481
theorem B238067 : Blo 103782 238067 := bstep (se 1 (by rfl) ⟨178550, by rfl⟩ : syracuseStep 238067 = 357101) B357101
theorem B106999 : Blo 103782 106999 := bstep (se 1 (by rfl) ⟨80249, by rfl⟩ : syracuseStep 106999 = 160499) B160499
theorem B107019 : Blo 103782 107019 := bstep (se 1 (by rfl) ⟨80264, by rfl⟩ : syracuseStep 107019 = 160529) B160529
theorem B238103 : Blo 103782 238103 := bstep (se 1 (by rfl) ⟨178577, by rfl⟩ : syracuseStep 238103 = 357155) B357155
theorem B107031 : Blo 103782 107031 := bstep (se 1 (by rfl) ⟨80273, by rfl⟩ : syracuseStep 107031 = 160547) B160547
theorem B107051 : Blo 103782 107051 := bstep (se 1 (by rfl) ⟨80288, by rfl⟩ : syracuseStep 107051 = 160577) B160577
theorem B107063 : Blo 103782 107063 := bstep (se 1 (by rfl) ⟨80297, by rfl⟩ : syracuseStep 107063 = 160595) B160595
theorem B107083 : Blo 103782 107083 := bstep (se 1 (by rfl) ⟨80312, by rfl⟩ : syracuseStep 107083 = 160625) B160625
theorem B107095 : Blo 103782 107095 := bstep (se 1 (by rfl) ⟨80321, by rfl⟩ : syracuseStep 107095 = 160643) B160643
theorem B172631 : Blo 103782 172631 := bstep (se 1 (by rfl) ⟨129473, by rfl⟩ : syracuseStep 172631 = 258947) B258947
theorem B303709 : Blo 103782 303709 := bstep (se 3 (by rfl) ⟨56945, by rfl⟩ : syracuseStep 303709 = 113891) B113891
theorem B107115 : Blo 103782 107115 := bstep (se 1 (by rfl) ⟨80336, by rfl⟩ : syracuseStep 107115 = 160673) B160673
theorem B107127 : Blo 103782 107127 := bstep (se 1 (by rfl) ⟨80345, by rfl⟩ : syracuseStep 107127 = 160691) B160691
theorem B107147 : Blo 103782 107147 := bstep (se 1 (by rfl) ⟨80360, by rfl⟩ : syracuseStep 107147 = 160721) B160721
theorem B107159 : Blo 103782 107159 := bstep (se 1 (by rfl) ⟨80369, by rfl⟩ : syracuseStep 107159 = 160739) B160739
theorem B107179 : Blo 103782 107179 := bstep (se 1 (by rfl) ⟨80384, by rfl⟩ : syracuseStep 107179 = 160769) B160769
theorem B107191 : Blo 103782 107191 := bstep (se 1 (by rfl) ⟨80393, by rfl⟩ : syracuseStep 107191 = 160787) B160787
theorem B238283 : Blo 103782 238283 := bstep (se 1 (by rfl) ⟨178712, by rfl⟩ : syracuseStep 238283 = 357425) B357425
theorem B107211 : Blo 103782 107211 := bstep (se 1 (by rfl) ⟨80408, by rfl⟩ : syracuseStep 107211 = 160817) B160817
theorem B107223 : Blo 103782 107223 := bstep (se 1 (by rfl) ⟨80417, by rfl⟩ : syracuseStep 107223 = 160835) B160835
theorem B107243 : Blo 103782 107243 := bstep (se 1 (by rfl) ⟨80432, by rfl⟩ : syracuseStep 107243 = 160865) B160865
theorem B107255 : Blo 103782 107255 := bstep (se 1 (by rfl) ⟨80441, by rfl⟩ : syracuseStep 107255 = 160883) B160883
theorem B238337 : Blo 103782 238337 := bstep (se 2 (by rfl) ⟨89376, by rfl⟩ : syracuseStep 238337 = 178753) B178753
theorem B107275 : Blo 103782 107275 := bstep (se 1 (by rfl) ⟨80456, by rfl⟩ : syracuseStep 107275 = 160913) B160913
theorem B271127 : Blo 103782 271127 := bstep (se 1 (by rfl) ⟨203345, by rfl⟩ : syracuseStep 271127 = 406691) B406691
theorem B107287 : Blo 103782 107287 := bstep (se 1 (by rfl) ⟨80465, by rfl⟩ : syracuseStep 107287 = 160931) B160931
theorem B107307 : Blo 103782 107307 := bstep (se 1 (by rfl) ⟨80480, by rfl⟩ : syracuseStep 107307 = 160961) B160961
theorem B107319 : Blo 103782 107319 := bstep (se 1 (by rfl) ⟨80489, by rfl⟩ : syracuseStep 107319 = 160979) B160979
theorem B107339 : Blo 103782 107339 := bstep (se 1 (by rfl) ⟨80504, by rfl⟩ : syracuseStep 107339 = 161009) B161009
theorem B107351 : Blo 103782 107351 := bstep (se 1 (by rfl) ⟨80513, by rfl⟩ : syracuseStep 107351 = 161027) B161027
theorem B500573 : Blo 103782 500573 := bstep (se 3 (by rfl) ⟨93857, by rfl⟩ : syracuseStep 500573 = 187715) B187715
theorem B107371 : Blo 103782 107371 := bstep (se 1 (by rfl) ⟨80528, by rfl⟩ : syracuseStep 107371 = 161057) B161057
theorem B107383 : Blo 103782 107383 := bstep (se 1 (by rfl) ⟨80537, by rfl⟩ : syracuseStep 107383 = 161075) B161075
theorem B107403 : Blo 103782 107403 := bstep (se 1 (by rfl) ⟨80552, by rfl⟩ : syracuseStep 107403 = 161105) B161105
theorem B336791 : Blo 103782 336791 := bstep (se 1 (by rfl) ⟨252593, by rfl⟩ : syracuseStep 336791 = 505187) B505187
theorem B107415 : Blo 103782 107415 := bstep (se 1 (by rfl) ⟨80561, by rfl⟩ : syracuseStep 107415 = 161123) B161123
theorem B107435 : Blo 103782 107435 := bstep (se 1 (by rfl) ⟨80576, by rfl⟩ : syracuseStep 107435 = 161153) B161153
theorem B107447 : Blo 103782 107447 := bstep (se 1 (by rfl) ⟨80585, by rfl⟩ : syracuseStep 107447 = 161171) B161171
theorem B107467 : Blo 103782 107467 := bstep (se 1 (by rfl) ⟨80600, by rfl⟩ : syracuseStep 107467 = 161201) B161201
theorem B107479 : Blo 103782 107479 := bstep (se 1 (by rfl) ⟨80609, by rfl⟩ : syracuseStep 107479 = 161219) B161219
theorem B533465 : Blo 103782 533465 := bstep (se 2 (by rfl) ⟨200049, by rfl⟩ : syracuseStep 533465 = 400099) B400099
theorem B238553 : Blo 103782 238553 := bstep (se 2 (by rfl) ⟨89457, by rfl⟩ : syracuseStep 238553 = 178915) B178915
theorem B107499 : Blo 103782 107499 := bstep (se 1 (by rfl) ⟨80624, by rfl⟩ : syracuseStep 107499 = 161249) B161249
theorem B107511 : Blo 103782 107511 := bstep (se 1 (by rfl) ⟨80633, by rfl⟩ : syracuseStep 107511 = 161267) B161267
theorem B107531 : Blo 103782 107531 := bstep (se 1 (by rfl) ⟨80648, by rfl⟩ : syracuseStep 107531 = 161297) B161297
theorem B336919 : Blo 103782 336919 := bstep (se 1 (by rfl) ⟨252689, by rfl⟩ : syracuseStep 336919 = 505379) B505379
theorem B107543 : Blo 103782 107543 := bstep (se 1 (by rfl) ⟨80657, by rfl⟩ : syracuseStep 107543 = 161315) B161315
theorem B107563 : Blo 103782 107563 := bstep (se 1 (by rfl) ⟨80672, by rfl⟩ : syracuseStep 107563 = 161345) B161345
theorem B238643 : Blo 103782 238643 := bstep (se 1 (by rfl) ⟨178982, by rfl⟩ : syracuseStep 238643 = 357965) B357965
theorem B107575 : Blo 103782 107575 := bstep (se 1 (by rfl) ⟨80681, by rfl⟩ : syracuseStep 107575 = 161363) B161363
theorem B107595 : Blo 103782 107595 := bstep (se 1 (by rfl) ⟨80696, by rfl⟩ : syracuseStep 107595 = 161393) B161393
theorem B238679 : Blo 103782 238679 := bstep (se 1 (by rfl) ⟨179009, by rfl⟩ : syracuseStep 238679 = 358019) B358019
theorem B107607 : Blo 103782 107607 := bstep (se 1 (by rfl) ⟨80705, by rfl⟩ : syracuseStep 107607 = 161411) B161411
theorem B107627 : Blo 103782 107627 := bstep (se 1 (by rfl) ⟨80720, by rfl⟩ : syracuseStep 107627 = 161441) B161441
theorem B107639 : Blo 103782 107639 := bstep (se 1 (by rfl) ⟨80729, by rfl⟩ : syracuseStep 107639 = 161459) B161459
theorem B107659 : Blo 103782 107659 := bstep (se 1 (by rfl) ⟨80744, by rfl⟩ : syracuseStep 107659 = 161489) B161489
theorem B107671 : Blo 103782 107671 := bstep (se 1 (by rfl) ⟨80753, by rfl⟩ : syracuseStep 107671 = 161507) B161507
theorem B107691 : Blo 103782 107691 := bstep (se 1 (by rfl) ⟨80768, by rfl⟩ : syracuseStep 107691 = 161537) B161537
theorem B107703 : Blo 103782 107703 := bstep (se 1 (by rfl) ⟨80777, by rfl⟩ : syracuseStep 107703 = 161555) B161555
theorem B107723 : Blo 103782 107723 := bstep (se 1 (by rfl) ⟨80792, by rfl⟩ : syracuseStep 107723 = 161585) B161585
theorem B1156301 : Blo 103782 1156301 := bstep (se 3 (by rfl) ⟨216806, by rfl⟩ : syracuseStep 1156301 = 433613) B433613
theorem B107735 : Blo 103782 107735 := bstep (se 1 (by rfl) ⟨80801, by rfl⟩ : syracuseStep 107735 = 161603) B161603
theorem B107755 : Blo 103782 107755 := bstep (se 1 (by rfl) ⟨80816, by rfl⟩ : syracuseStep 107755 = 161633) B161633
theorem B107767 : Blo 103782 107767 := bstep (se 1 (by rfl) ⟨80825, by rfl⟩ : syracuseStep 107767 = 161651) B161651
theorem B238859 : Blo 103782 238859 := bstep (se 1 (by rfl) ⟨179144, by rfl⟩ : syracuseStep 238859 = 358289) B358289
theorem B337175 : Blo 103782 337175 := bstep (se 1 (by rfl) ⟨252881, by rfl⟩ : syracuseStep 337175 = 505763) B505763
theorem B238913 : Blo 103782 238913 := bstep (se 2 (by rfl) ⟨89592, by rfl⟩ : syracuseStep 238913 = 179185) B179185
theorem B402833 : Blo 103782 402833 := bstep (se 2 (by rfl) ⟨151062, by rfl⟩ : syracuseStep 402833 = 302125) B302125
theorem B206233 : Blo 103782 206233 := bstep (se 2 (by rfl) ⟨77337, by rfl⟩ : syracuseStep 206233 = 154675) B154675
theorem B271795 : Blo 103782 271795 := bstep (se 1 (by rfl) ⟨203846, by rfl⟩ : syracuseStep 271795 = 407693) B407693
theorem B108043 : Blo 103782 108043 := bstep (se 1 (by rfl) ⟨81032, by rfl⟩ : syracuseStep 108043 = 162065) B162065
theorem B402961 : Blo 103782 402961 := bstep (se 2 (by rfl) ⟨151110, by rfl⟩ : syracuseStep 402961 = 302221) B302221
theorem B173591 : Blo 103782 173591 := bstep (se 1 (by rfl) ⟨130193, by rfl⟩ : syracuseStep 173591 = 260387) B260387
theorem B239129 : Blo 103782 239129 := bstep (se 2 (by rfl) ⟨89673, by rfl⟩ : syracuseStep 239129 = 179347) B179347
theorem B271937 : Blo 103782 271937 := bstep (se 2 (by rfl) ⟨101976, by rfl⟩ : syracuseStep 271937 = 203953) B203953
theorem B239219 : Blo 103782 239219 := bstep (se 1 (by rfl) ⟨179414, by rfl⟩ : syracuseStep 239219 = 358829) B358829
theorem B239255 : Blo 103782 239255 := bstep (se 1 (by rfl) ⟨179441, by rfl⟩ : syracuseStep 239255 = 358883) B358883
theorem B894725 : Blo 103782 894725 := bstep (se 4 (by rfl) ⟨83880, by rfl⟩ : syracuseStep 894725 = 167761) B167761
theorem B534347 : Blo 103782 534347 := bstep (se 1 (by rfl) ⟨400760, by rfl⟩ : syracuseStep 534347 = 801521) B801521
theorem B239435 : Blo 103782 239435 := bstep (se 1 (by rfl) ⟨179576, by rfl⟩ : syracuseStep 239435 = 359153) B359153
theorem B403289 : Blo 103782 403289 := bstep (se 2 (by rfl) ⟨151233, by rfl⟩ : syracuseStep 403289 = 302467) B302467
theorem B304985 : Blo 103782 304985 := bstep (se 2 (by rfl) ⟨114369, by rfl⟩ : syracuseStep 304985 = 228739) B228739
theorem B239489 : Blo 103782 239489 := bstep (se 2 (by rfl) ⟨89808, by rfl⟩ : syracuseStep 239489 = 179617) B179617
theorem B665495 : Blo 103782 665495 := bstep (se 1 (by rfl) ⟨499121, by rfl⟩ : syracuseStep 665495 = 998243) B998243
theorem B2009123 : Blo 103782 2009123 := bstep (se 1 (by rfl) ⟨1506842, by rfl⟩ : syracuseStep 2009123 = 3013685) B3013685
theorem B403501 : Blo 103782 403501 := bstep (se 3 (by rfl) ⟨75656, by rfl⟩ : syracuseStep 403501 = 151313) B151313
theorem B108631 : Blo 103782 108631 := bstep (se 1 (by rfl) ⟨81473, by rfl⟩ : syracuseStep 108631 = 162947) B162947
theorem B239705 : Blo 103782 239705 := bstep (se 2 (by rfl) ⟨89889, by rfl⟩ : syracuseStep 239705 = 179779) B179779
theorem B239795 : Blo 103782 239795 := bstep (se 1 (by rfl) ⟨179846, by rfl⟩ : syracuseStep 239795 = 359693) B359693
theorem B239831 : Blo 103782 239831 := bstep (se 1 (by rfl) ⟨179873, by rfl⟩ : syracuseStep 239831 = 359747) B359747
theorem B1059077 : Blo 103782 1059077 := bstep (se 4 (by rfl) ⟨99288, by rfl⟩ : syracuseStep 1059077 = 198577) B198577
theorem B469271 : Blo 103782 469271 := bstep (se 1 (by rfl) ⟨351953, by rfl⟩ : syracuseStep 469271 = 703907) B703907
theorem B272663 : Blo 103782 272663 := bstep (se 1 (by rfl) ⟨204497, by rfl⟩ : syracuseStep 272663 = 408995) B408995
theorem B338251 : Blo 103782 338251 := bstep (se 1 (by rfl) ⟨253688, by rfl⟩ : syracuseStep 338251 = 507377) B507377
theorem B403805 : Blo 103782 403805 := bstep (se 3 (by rfl) ⟨75713, by rfl⟩ : syracuseStep 403805 = 151427) B151427
theorem B240011 : Blo 103782 240011 := bstep (se 1 (by rfl) ⟨180008, by rfl⟩ : syracuseStep 240011 = 360017) B360017
theorem B2337173 : Blo 103782 2337173 := bstep (se 6 (by rfl) ⟨54777, by rfl⟩ : syracuseStep 2337173 = 109555) B109555
theorem B240065 : Blo 103782 240065 := bstep (se 2 (by rfl) ⟨90024, by rfl⟩ : syracuseStep 240065 = 180049) B180049
theorem B338393 : Blo 103782 338393 := bstep (se 2 (by rfl) ⟨126897, by rfl⟩ : syracuseStep 338393 = 253795) B253795
theorem B272857 : Blo 103782 272857 := bstep (se 2 (by rfl) ⟨102321, by rfl⟩ : syracuseStep 272857 = 204643) B204643
theorem B141835 : Blo 103782 141835 := bstep (se 1 (by rfl) ⟨106376, by rfl⟩ : syracuseStep 141835 = 212753) B212753
theorem B1878563 : Blo 103782 1878563 := bstep (se 1 (by rfl) ⟨1408922, by rfl⟩ : syracuseStep 1878563 = 2817845) B2817845
theorem B535085 : Blo 103782 535085 := bstep (se 3 (by rfl) ⟨100328, by rfl⟩ : syracuseStep 535085 = 200657) B200657
theorem B338507 : Blo 103782 338507 := bstep (se 1 (by rfl) ⟨253880, by rfl⟩ : syracuseStep 338507 = 507761) B507761
theorem B1223261 : Blo 103782 1223261 := bstep (se 3 (by rfl) ⟨229361, by rfl⟩ : syracuseStep 1223261 = 458723) B458723
theorem B240281 : Blo 103782 240281 := bstep (se 2 (by rfl) ⟨90105, by rfl⟩ : syracuseStep 240281 = 180211) B180211
theorem B240371 : Blo 103782 240371 := bstep (se 1 (by rfl) ⟨180278, by rfl⟩ : syracuseStep 240371 = 360557) B360557
theorem B404227 : Blo 103782 404227 := bstep (se 1 (by rfl) ⟨303170, by rfl⟩ : syracuseStep 404227 = 606341) B606341
theorem B240407 : Blo 103782 240407 := bstep (se 1 (by rfl) ⟨180305, by rfl⟩ : syracuseStep 240407 = 360611) B360611
theorem B338867 : Blo 103782 338867 := bstep (se 1 (by rfl) ⟨254150, by rfl⟩ : syracuseStep 338867 = 508301) B508301
theorem B240587 : Blo 103782 240587 := bstep (se 1 (by rfl) ⟨180440, by rfl⟩ : syracuseStep 240587 = 360881) B360881
theorem B240641 : Blo 103782 240641 := bstep (se 2 (by rfl) ⟨90240, by rfl⟩ : syracuseStep 240641 = 180481) B180481
theorem B175243 : Blo 103782 175243 := bstep (se 1 (by rfl) ⟨131432, by rfl⟩ : syracuseStep 175243 = 262865) B262865
theorem B240857 : Blo 103782 240857 := bstep (se 2 (by rfl) ⟨90321, by rfl⟩ : syracuseStep 240857 = 180643) B180643
theorem B109847 : Blo 103782 109847 := bstep (se 1 (by rfl) ⟨82385, by rfl⟩ : syracuseStep 109847 = 164771) B164771
theorem B175385 : Blo 103782 175385 := bstep (se 2 (by rfl) ⟨65769, by rfl⟩ : syracuseStep 175385 = 131539) B131539
theorem B240947 : Blo 103782 240947 := bstep (se 1 (by rfl) ⟨180710, by rfl⟩ : syracuseStep 240947 = 361421) B361421
theorem B240983 : Blo 103782 240983 := bstep (se 1 (by rfl) ⟨180737, by rfl⟩ : syracuseStep 240983 = 361475) B361475
theorem B175513 : Blo 103782 175513 := bstep (se 2 (by rfl) ⟨65817, by rfl⟩ : syracuseStep 175513 = 131635) B131635
theorem B1027505 : Blo 103782 1027505 := bstep (se 2 (by rfl) ⟨385314, by rfl⟩ : syracuseStep 1027505 = 770629) B770629
theorem B306625 : Blo 103782 306625 := bstep (se 2 (by rfl) ⟨114984, by rfl⟩ : syracuseStep 306625 = 229969) B229969
theorem B241163 : Blo 103782 241163 := bstep (se 1 (by rfl) ⟨180872, by rfl⟩ : syracuseStep 241163 = 361745) B361745
theorem B241217 : Blo 103782 241217 := bstep (se 2 (by rfl) ⟨90456, by rfl⟩ : syracuseStep 241217 = 180913) B180913
theorem B339635 : Blo 103782 339635 := bstep (se 1 (by rfl) ⟨254726, by rfl⟩ : syracuseStep 339635 = 509453) B509453
theorem B831181 : Blo 103782 831181 := bstep (se 3 (by rfl) ⟨155846, by rfl⟩ : syracuseStep 831181 = 311693) B311693
theorem B241433 : Blo 103782 241433 := bstep (se 2 (by rfl) ⟨90537, by rfl⟩ : syracuseStep 241433 = 181075) B181075
theorem B241523 : Blo 103782 241523 := bstep (se 1 (by rfl) ⟨181142, by rfl⟩ : syracuseStep 241523 = 362285) B362285
theorem B241559 : Blo 103782 241559 := bstep (se 1 (by rfl) ⟨181169, by rfl⟩ : syracuseStep 241559 = 362339) B362339
theorem B176087 : Blo 103782 176087 := bstep (se 1 (by rfl) ⟨132065, by rfl⟩ : syracuseStep 176087 = 264131) B264131
theorem B1814489 : Blo 103782 1814489 := bstep (se 2 (by rfl) ⟨680433, by rfl⟩ : syracuseStep 1814489 = 1360867) B1360867
theorem B340033 : Blo 103782 340033 := bstep (se 2 (by rfl) ⟨127512, by rfl⟩ : syracuseStep 340033 = 255025) B255025
theorem B241739 : Blo 103782 241739 := bstep (se 1 (by rfl) ⟨181304, by rfl⟩ : syracuseStep 241739 = 362609) B362609
theorem B176215 : Blo 103782 176215 := bstep (se 1 (by rfl) ⟨132161, by rfl⟩ : syracuseStep 176215 = 264323) B264323
theorem B241793 : Blo 103782 241793 := bstep (se 2 (by rfl) ⟨90672, by rfl⟩ : syracuseStep 241793 = 181345) B181345
theorem B340147 : Blo 103782 340147 := bstep (se 1 (by rfl) ⟨255110, by rfl⟩ : syracuseStep 340147 = 510221) B510221
theorem B242009 : Blo 103782 242009 := bstep (se 2 (by rfl) ⟨90753, by rfl⟩ : syracuseStep 242009 = 181507) B181507
theorem B242099 : Blo 103782 242099 := bstep (se 1 (by rfl) ⟨181574, by rfl⟩ : syracuseStep 242099 = 363149) B363149
theorem B242135 : Blo 103782 242135 := bstep (se 1 (by rfl) ⟨181601, by rfl⟩ : syracuseStep 242135 = 363203) B363203
theorem B242315 : Blo 103782 242315 := bstep (se 1 (by rfl) ⟨181736, by rfl⟩ : syracuseStep 242315 = 363473) B363473
theorem B242369 : Blo 103782 242369 := bstep (se 2 (by rfl) ⟨90888, by rfl⟩ : syracuseStep 242369 = 181777) B181777
theorem B176843 : Blo 103782 176843 := bstep (se 1 (by rfl) ⟨132632, by rfl⟩ : syracuseStep 176843 = 265265) B265265
theorem B2994893 : Blo 103782 2994893 := bstep (se 3 (by rfl) ⟨561542, by rfl⟩ : syracuseStep 2994893 = 1123085) B1123085
theorem B176971 : Blo 103782 176971 := bstep (se 1 (by rfl) ⟨132728, by rfl⟩ : syracuseStep 176971 = 265457) B265457
theorem B406403 : Blo 103782 406403 := bstep (se 1 (by rfl) ⟨304802, by rfl⟩ : syracuseStep 406403 = 609605) B609605
theorem B406417 : Blo 103782 406417 := bstep (se 2 (by rfl) ⟨152406, by rfl⟩ : syracuseStep 406417 = 304813) B304813
theorem B177113 : Blo 103782 177113 := bstep (se 2 (by rfl) ⟨66417, by rfl⟩ : syracuseStep 177113 = 132835) B132835
theorem B177241 : Blo 103782 177241 := bstep (se 2 (by rfl) ⟨66465, by rfl⟩ : syracuseStep 177241 = 132931) B132931
theorem B406721 : Blo 103782 406721 := bstep (se 2 (by rfl) ⟨152520, by rfl⟩ : syracuseStep 406721 = 305041) B305041
theorem B111947 : Blo 103782 111947 := bstep (se 1 (by rfl) ⟨83960, by rfl⟩ : syracuseStep 111947 = 167921) B167921
theorem B1291697 : Blo 103782 1291697 := bstep (se 2 (by rfl) ⟨484386, by rfl⟩ : syracuseStep 1291697 = 968773) B968773
theorem B1553843 : Blo 103782 1553843 := bstep (se 1 (by rfl) ⟨1165382, by rfl⟩ : syracuseStep 1553843 = 2330765) B2330765
theorem B1029667 : Blo 103782 1029667 := bstep (se 1 (by rfl) ⟨772250, by rfl⟩ : syracuseStep 1029667 = 1544501) B1544501
theorem B243251 : Blo 103782 243251 := bstep (se 1 (by rfl) ⟨182438, by rfl⟩ : syracuseStep 243251 = 364877) B364877
theorem B341597 : Blo 103782 341597 := bstep (se 3 (by rfl) ⟨64049, by rfl⟩ : syracuseStep 341597 = 128099) B128099
theorem B177815 : Blo 103782 177815 := bstep (se 1 (by rfl) ⟨133361, by rfl⟩ : syracuseStep 177815 = 266723) B266723
theorem B177943 : Blo 103782 177943 := bstep (se 1 (by rfl) ⟨133457, by rfl⟩ : syracuseStep 177943 = 266915) B266915
theorem B210775 : Blo 103782 210775 := bstep (se 1 (by rfl) ⟨158081, by rfl⟩ : syracuseStep 210775 = 316163) B316163
theorem B407389 : Blo 103782 407389 := bstep (se 3 (by rfl) ⟨76385, by rfl⟩ : syracuseStep 407389 = 152771) B152771
theorem B604205 : Blo 103782 604205 := bstep (se 3 (by rfl) ⟨113288, by rfl⟩ : syracuseStep 604205 = 226577) B226577
theorem B211033 : Blo 103782 211033 := bstep (se 2 (by rfl) ⟨79137, by rfl⟩ : syracuseStep 211033 = 158275) B158275
theorem B1620209 : Blo 103782 1620209 := bstep (se 2 (by rfl) ⟨607578, by rfl⟩ : syracuseStep 1620209 = 1215157) B1215157
theorem B538973 : Blo 103782 538973 := bstep (se 3 (by rfl) ⟨101057, by rfl⟩ : syracuseStep 538973 = 202115) B202115
theorem B178571 : Blo 103782 178571 := bstep (se 1 (by rfl) ⟨133928, by rfl⟩ : syracuseStep 178571 = 267857) B267857
theorem B440749 : Blo 103782 440749 := bstep (se 3 (by rfl) ⟨82640, by rfl⟩ : syracuseStep 440749 = 165281) B165281
theorem B178699 : Blo 103782 178699 := bstep (se 1 (by rfl) ⟨134024, by rfl⟩ : syracuseStep 178699 = 268049) B268049
theorem B670301 : Blo 103782 670301 := bstep (se 3 (by rfl) ⟨125681, by rfl⟩ : syracuseStep 670301 = 251363) B251363
theorem B178841 : Blo 103782 178841 := bstep (se 2 (by rfl) ⟨67065, by rfl⟩ : syracuseStep 178841 = 134131) B134131
theorem B178969 : Blo 103782 178969 := bstep (se 2 (by rfl) ⟨67113, by rfl⟩ : syracuseStep 178969 = 134227) B134227
theorem B113707 : Blo 103782 113707 := bstep (se 1 (by rfl) ⟨85280, by rfl⟩ : syracuseStep 113707 = 170561) B170561
theorem B408665 : Blo 103782 408665 := bstep (se 2 (by rfl) ⟨153249, by rfl⟩ : syracuseStep 408665 = 306499) B306499
theorem B113783 : Blo 103782 113783 := bstep (se 1 (by rfl) ⟨85337, by rfl⟩ : syracuseStep 113783 = 170675) B170675
theorem B179543 : Blo 103782 179543 := bstep (se 1 (by rfl) ⟨134657, by rfl⟩ : syracuseStep 179543 = 269315) B269315
theorem B769459 : Blo 103782 769459 := bstep (se 1 (by rfl) ⟨577094, by rfl⟩ : syracuseStep 769459 = 1154189) B1154189
theorem B179671 : Blo 103782 179671 := bstep (se 1 (by rfl) ⟨134753, by rfl⟩ : syracuseStep 179671 = 269507) B269507
theorem B376541 : Blo 103782 376541 := bstep (se 3 (by rfl) ⟨70601, by rfl⟩ : syracuseStep 376541 = 141203) B141203
theorem B180299 : Blo 103782 180299 := bstep (se 1 (by rfl) ⟨135224, by rfl⟩ : syracuseStep 180299 = 270449) B270449
theorem B180427 : Blo 103782 180427 := bstep (se 1 (by rfl) ⟨135320, by rfl⟩ : syracuseStep 180427 = 270641) B270641
theorem B180569 : Blo 103782 180569 := bstep (se 2 (by rfl) ⟨67713, by rfl⟩ : syracuseStep 180569 = 135427) B135427
theorem B541079 : Blo 103782 541079 := bstep (se 1 (by rfl) ⟨405809, by rfl⟩ : syracuseStep 541079 = 811619) B811619
theorem B180697 : Blo 103782 180697 := bstep (se 2 (by rfl) ⟨67761, by rfl⟩ : syracuseStep 180697 = 135523) B135523
theorem B508717 : Blo 103782 508717 := bstep (se 3 (by rfl) ⟨95384, by rfl⟩ : syracuseStep 508717 = 190769) B190769
theorem B1197017 : Blo 103782 1197017 := bstep (se 2 (by rfl) ⟨448881, by rfl⟩ : syracuseStep 1197017 = 897763) B897763
theorem B181271 : Blo 103782 181271 := bstep (se 1 (by rfl) ⟨135953, by rfl⟩ : syracuseStep 181271 = 271907) B271907
theorem B181399 : Blo 103782 181399 := bstep (se 1 (by rfl) ⟨136049, by rfl⟩ : syracuseStep 181399 = 272099) B272099
theorem B935441 : Blo 103782 935441 := bstep (se 2 (by rfl) ⟨350790, by rfl⟩ : syracuseStep 935441 = 701581) B701581
theorem B214553 : Blo 103782 214553 := bstep (se 2 (by rfl) ⟨80457, by rfl⟩ : syracuseStep 214553 = 160915) B160915
theorem B771677 : Blo 103782 771677 := bstep (se 3 (by rfl) ⟨144689, by rfl⟩ : syracuseStep 771677 = 289379) B289379
theorem B607895 : Blo 103782 607895 := bstep (se 1 (by rfl) ⟨455921, by rfl⟩ : syracuseStep 607895 = 911843) B911843
theorem B575383 : Blo 103782 575383 := bstep (se 1 (by rfl) ⟨431537, by rfl⟩ : syracuseStep 575383 = 863075) B863075
theorem B116779 : Blo 103782 116779 := bstep (se 1 (by rfl) ⟨87584, by rfl⟩ : syracuseStep 116779 = 175169) B175169
theorem B1624157 : Blo 103782 1624157 := bstep (se 3 (by rfl) ⟨304529, by rfl⟩ : syracuseStep 1624157 = 609059) B609059
theorem B116887 : Blo 103782 116887 := bstep (se 1 (by rfl) ⟨87665, by rfl⟩ : syracuseStep 116887 = 175331) B175331
theorem B117067 : Blo 103782 117067 := bstep (se 1 (by rfl) ⟨87800, by rfl⟩ : syracuseStep 117067 = 175601) B175601
theorem B444851 : Blo 103782 444851 := bstep (se 1 (by rfl) ⟨333638, by rfl⟩ : syracuseStep 444851 = 667277) B667277
theorem B117175 : Blo 103782 117175 := bstep (se 1 (by rfl) ⟨87881, by rfl⟩ : syracuseStep 117175 = 175763) B175763
theorem B117355 : Blo 103782 117355 := bstep (se 1 (by rfl) ⟨88016, by rfl⟩ : syracuseStep 117355 = 176033) B176033
theorem B150169 : Blo 103782 150169 := bstep (se 2 (by rfl) ⟨56313, by rfl⟩ : syracuseStep 150169 = 112627) B112627
theorem B215705 : Blo 103782 215705 := bstep (se 2 (by rfl) ⟨80889, by rfl⟩ : syracuseStep 215705 = 161779) B161779
theorem B182987 : Blo 103782 182987 := bstep (se 1 (by rfl) ⟨137240, by rfl⟩ : syracuseStep 182987 = 274481) B274481
theorem B117463 : Blo 103782 117463 := bstep (se 1 (by rfl) ⟨88097, by rfl⟩ : syracuseStep 117463 = 176195) B176195
theorem B117643 : Blo 103782 117643 := bstep (se 1 (by rfl) ⟨88232, by rfl⟩ : syracuseStep 117643 = 176465) B176465
theorem B117751 : Blo 103782 117751 := bstep (se 1 (by rfl) ⟨88313, by rfl⟩ : syracuseStep 117751 = 176627) B176627
theorem B117931 : Blo 103782 117931 := bstep (se 1 (by rfl) ⟨88448, by rfl⟩ : syracuseStep 117931 = 176897) B176897
theorem B118039 : Blo 103782 118039 := bstep (se 1 (by rfl) ⟨88529, by rfl⟩ : syracuseStep 118039 = 177059) B177059
theorem B118219 : Blo 103782 118219 := bstep (se 1 (by rfl) ⟨88664, by rfl⟩ : syracuseStep 118219 = 177329) B177329
theorem B675373 : Blo 103782 675373 := bstep (se 3 (by rfl) ⟨126632, by rfl⟩ : syracuseStep 675373 = 253265) B253265
theorem B118327 : Blo 103782 118327 := bstep (se 1 (by rfl) ⟨88745, by rfl⟩ : syracuseStep 118327 = 177491) B177491
theorem B118507 : Blo 103782 118507 := bstep (se 1 (by rfl) ⟨88880, by rfl⟩ : syracuseStep 118507 = 177761) B177761
theorem B118615 : Blo 103782 118615 := bstep (se 1 (by rfl) ⟨88961, by rfl⟩ : syracuseStep 118615 = 177923) B177923
theorem B347993 : Blo 103782 347993 := bstep (se 2 (by rfl) ⟨130497, by rfl⟩ : syracuseStep 347993 = 260995) B260995
theorem B544643 : Blo 103782 544643 := bstep (se 1 (by rfl) ⟨408482, by rfl⟩ : syracuseStep 544643 = 816965) B816965
theorem B511895 : Blo 103782 511895 := bstep (se 1 (by rfl) ⟨383921, by rfl⟩ : syracuseStep 511895 = 767843) B767843
theorem B577459 : Blo 103782 577459 := bstep (se 1 (by rfl) ⟨433094, by rfl⟩ : syracuseStep 577459 = 866189) B866189
theorem B118795 : Blo 103782 118795 := bstep (se 1 (by rfl) ⟨89096, by rfl⟩ : syracuseStep 118795 = 178193) B178193
theorem B151627 : Blo 103782 151627 := bstep (se 1 (by rfl) ⟨113720, by rfl⟩ : syracuseStep 151627 = 227441) B227441
theorem B118903 : Blo 103782 118903 := bstep (se 1 (by rfl) ⟨89177, by rfl⟩ : syracuseStep 118903 = 178355) B178355
theorem B119083 : Blo 103782 119083 := bstep (se 1 (by rfl) ⟨89312, by rfl⟩ : syracuseStep 119083 = 178625) B178625
theorem B119191 : Blo 103782 119191 := bstep (se 1 (by rfl) ⟨89393, by rfl⟩ : syracuseStep 119191 = 178787) B178787
theorem B119371 : Blo 103782 119371 := bstep (se 1 (by rfl) ⟨89528, by rfl⟩ : syracuseStep 119371 = 179057) B179057
theorem B119479 : Blo 103782 119479 := bstep (se 1 (by rfl) ⟨89609, by rfl⟩ : syracuseStep 119479 = 179219) B179219
theorem B119659 : Blo 103782 119659 := bstep (se 1 (by rfl) ⟨89744, by rfl⟩ : syracuseStep 119659 = 179489) B179489
theorem B119767 : Blo 103782 119767 := bstep (se 1 (by rfl) ⟨89825, by rfl⟩ : syracuseStep 119767 = 179651) B179651
theorem B316381 : Blo 103782 316381 := bstep (se 3 (by rfl) ⟨59321, by rfl⟩ : syracuseStep 316381 = 118643) B118643
theorem B381917 : Blo 103782 381917 := bstep (se 3 (by rfl) ⟨71609, by rfl⟩ : syracuseStep 381917 = 143219) B143219
theorem B218123 : Blo 103782 218123 := bstep (se 1 (by rfl) ⟨163592, by rfl⟩ : syracuseStep 218123 = 327185) B327185
theorem B119947 : Blo 103782 119947 := bstep (se 1 (by rfl) ⟨89960, by rfl⟩ : syracuseStep 119947 = 179921) B179921
theorem B611479 : Blo 103782 611479 := bstep (se 1 (by rfl) ⟨458609, by rfl⟩ : syracuseStep 611479 = 917219) B917219
theorem B120055 : Blo 103782 120055 := bstep (se 1 (by rfl) ⟨90041, by rfl⟩ : syracuseStep 120055 = 180083) B180083
theorem B152857 : Blo 103782 152857 := bstep (se 2 (by rfl) ⟨57321, by rfl⟩ : syracuseStep 152857 = 114643) B114643
theorem B120235 : Blo 103782 120235 := bstep (se 1 (by rfl) ⟨90176, by rfl⟩ : syracuseStep 120235 = 180353) B180353
theorem B120343 : Blo 103782 120343 := bstep (se 1 (by rfl) ⟨90257, by rfl⟩ : syracuseStep 120343 = 180515) B180515
theorem B448051 : Blo 103782 448051 := bstep (se 1 (by rfl) ⟨336038, by rfl⟩ : syracuseStep 448051 = 672077) B672077
theorem B120523 : Blo 103782 120523 := bstep (se 1 (by rfl) ⟨90392, by rfl⟩ : syracuseStep 120523 = 180785) B180785
theorem B120631 : Blo 103782 120631 := bstep (se 1 (by rfl) ⟨90473, by rfl⟩ : syracuseStep 120631 = 180947) B180947
theorem B841603 : Blo 103782 841603 := bstep (se 1 (by rfl) ⟨631202, by rfl⟩ : syracuseStep 841603 = 1262405) B1262405
theorem B120811 : Blo 103782 120811 := bstep (se 1 (by rfl) ⟨90608, by rfl⟩ : syracuseStep 120811 = 181217) B181217
theorem B120919 : Blo 103782 120919 := bstep (se 1 (by rfl) ⟨90689, by rfl⟩ : syracuseStep 120919 = 181379) B181379
theorem B350297 : Blo 103782 350297 := bstep (se 2 (by rfl) ⟨131361, by rfl⟩ : syracuseStep 350297 = 262723) B262723
theorem B2676887 : Blo 103782 2676887 := bstep (se 1 (by rfl) ⟨2007665, by rfl⟩ : syracuseStep 2676887 = 4015331) B4015331
theorem B907469 : Blo 103782 907469 := bstep (se 3 (by rfl) ⟨170150, by rfl⟩ : syracuseStep 907469 = 340301) B340301
theorem B121099 : Blo 103782 121099 := bstep (se 1 (by rfl) ⟨90824, by rfl⟩ : syracuseStep 121099 = 181649) B181649
theorem B121207 : Blo 103782 121207 := bstep (se 1 (by rfl) ⟨90905, by rfl⟩ : syracuseStep 121207 = 181811) B181811
theorem B1989137 : Blo 103782 1989137 := bstep (se 2 (by rfl) ⟨745926, by rfl⟩ : syracuseStep 1989137 = 1491853) B1491853
theorem B449155 : Blo 103782 449155 := bstep (se 1 (by rfl) ⟨336866, by rfl⟩ : syracuseStep 449155 = 673733) B673733
theorem B350999 : Blo 103782 350999 := bstep (se 1 (by rfl) ⟨263249, by rfl⟩ : syracuseStep 350999 = 526499) B526499
theorem B187211 : Blo 103782 187211 := bstep (se 1 (by rfl) ⟨140408, by rfl⟩ : syracuseStep 187211 = 280817) B280817
theorem B285529 : Blo 103782 285529 := bstep (se 2 (by rfl) ⟨107073, by rfl⟩ : syracuseStep 285529 = 214147) B214147
theorem B613271 : Blo 103782 613271 := bstep (se 1 (by rfl) ⟨459953, by rfl⟩ : syracuseStep 613271 = 919907) B919907
theorem B810161 : Blo 103782 810161 := bstep (se 2 (by rfl) ⟨303810, by rfl⟩ : syracuseStep 810161 = 607621) B607621
theorem B351539 : Blo 103782 351539 := bstep (se 1 (by rfl) ⟨263654, by rfl⟩ : syracuseStep 351539 = 527309) B527309
theorem B351809 : Blo 103782 351809 := bstep (se 2 (by rfl) ⟨131928, by rfl⟩ : syracuseStep 351809 = 263857) B263857
theorem B810647 : Blo 103782 810647 := bstep (se 1 (by rfl) ⟨607985, by rfl⟩ : syracuseStep 810647 = 1215971) B1215971
theorem B155723 : Blo 103782 155723 := bstep (se 1 (by rfl) ⟨116792, by rfl⟩ : syracuseStep 155723 = 233585) B233585
theorem B155735 : Blo 103782 155735 := bstep (se 1 (by rfl) ⟨116801, by rfl⟩ : syracuseStep 155735 = 233603) B233603
theorem B352349 : Blo 103782 352349 := bstep (se 3 (by rfl) ⟨66065, by rfl⟩ : syracuseStep 352349 = 132131) B132131
theorem B155801 : Blo 103782 155801 := bstep (se 2 (by rfl) ⟨58425, by rfl⟩ : syracuseStep 155801 = 116851) B116851
theorem B286913 : Blo 103782 286913 := bstep (se 2 (by rfl) ⟨107592, by rfl⟩ : syracuseStep 286913 = 215185) B215185
theorem B155915 : Blo 103782 155915 := bstep (se 1 (by rfl) ⟨116936, by rfl⟩ : syracuseStep 155915 = 233873) B233873
theorem B155927 : Blo 103782 155927 := bstep (se 1 (by rfl) ⟨116945, by rfl⟩ : syracuseStep 155927 = 233891) B233891
theorem B155993 : Blo 103782 155993 := bstep (se 2 (by rfl) ⟨58497, by rfl⟩ : syracuseStep 155993 = 116995) B116995
theorem B450967 : Blo 103782 450967 := bstep (se 1 (by rfl) ⟨338225, by rfl⟩ : syracuseStep 450967 = 676451) B676451
theorem B156107 : Blo 103782 156107 := bstep (se 1 (by rfl) ⟨117080, by rfl⟩ : syracuseStep 156107 = 234161) B234161
theorem B254411 : Blo 103782 254411 := bstep (se 1 (by rfl) ⟨190808, by rfl⟩ : syracuseStep 254411 = 381617) B381617
theorem B156119 : Blo 103782 156119 := bstep (se 1 (by rfl) ⟨117089, by rfl⟩ : syracuseStep 156119 = 234179) B234179
theorem B221707 : Blo 103782 221707 := bstep (se 1 (by rfl) ⟨166280, by rfl⟩ : syracuseStep 221707 = 332561) B332561
theorem B156185 : Blo 103782 156185 := bstep (se 2 (by rfl) ⟨58569, by rfl⟩ : syracuseStep 156185 = 117139) B117139
theorem B156299 : Blo 103782 156299 := bstep (se 1 (by rfl) ⟨117224, by rfl⟩ : syracuseStep 156299 = 234449) B234449
theorem B156311 : Blo 103782 156311 := bstep (se 1 (by rfl) ⟨117233, by rfl⟩ : syracuseStep 156311 = 234467) B234467
theorem B156377 : Blo 103782 156377 := bstep (se 2 (by rfl) ⟨58641, by rfl⟩ : syracuseStep 156377 = 117283) B117283
theorem B1008449 : Blo 103782 1008449 := bstep (se 2 (by rfl) ⟨378168, by rfl⟩ : syracuseStep 1008449 = 756337) B756337
theorem B156491 : Blo 103782 156491 := bstep (se 1 (by rfl) ⟨117368, by rfl⟩ : syracuseStep 156491 = 234737) B234737
theorem B156503 : Blo 103782 156503 := bstep (se 1 (by rfl) ⟨117377, by rfl⟩ : syracuseStep 156503 = 234755) B234755
theorem B222041 : Blo 103782 222041 := bstep (se 2 (by rfl) ⟨83265, by rfl⟩ : syracuseStep 222041 = 166531) B166531
theorem B320345 : Blo 103782 320345 := bstep (se 2 (by rfl) ⟨120129, by rfl⟩ : syracuseStep 320345 = 240259) B240259
theorem B156569 : Blo 103782 156569 := bstep (se 2 (by rfl) ⟨58713, by rfl⟩ : syracuseStep 156569 = 117427) B117427
theorem B156683 : Blo 103782 156683 := bstep (se 1 (by rfl) ⟨117512, by rfl⟩ : syracuseStep 156683 = 235025) B235025
theorem B451601 : Blo 103782 451601 := bstep (se 2 (by rfl) ⟨169350, by rfl⟩ : syracuseStep 451601 = 338701) B338701
theorem B156695 : Blo 103782 156695 := bstep (se 1 (by rfl) ⟨117521, by rfl⟩ : syracuseStep 156695 = 235043) B235043
theorem B156761 : Blo 103782 156761 := bstep (se 2 (by rfl) ⟨58785, by rfl⟩ : syracuseStep 156761 = 117571) B117571
theorem B156875 : Blo 103782 156875 := bstep (se 1 (by rfl) ⟨117656, by rfl⟩ : syracuseStep 156875 = 235313) B235313
theorem B353483 : Blo 103782 353483 := bstep (se 1 (by rfl) ⟨265112, by rfl⟩ : syracuseStep 353483 = 530225) B530225
theorem B156887 : Blo 103782 156887 := bstep (se 1 (by rfl) ⟨117665, by rfl⟩ : syracuseStep 156887 = 235331) B235331
theorem B189719 : Blo 103782 189719 := bstep (se 1 (by rfl) ⟨142289, by rfl⟩ : syracuseStep 189719 = 284579) B284579
theorem B156953 : Blo 103782 156953 := bstep (se 2 (by rfl) ⟨58857, by rfl⟩ : syracuseStep 156953 = 117715) B117715
theorem B157067 : Blo 103782 157067 := bstep (se 1 (by rfl) ⟨117800, by rfl⟩ : syracuseStep 157067 = 235601) B235601
theorem B157079 : Blo 103782 157079 := bstep (se 1 (by rfl) ⟨117809, by rfl⟩ : syracuseStep 157079 = 235619) B235619
theorem B157145 : Blo 103782 157145 := bstep (se 2 (by rfl) ⟨58929, by rfl⟩ : syracuseStep 157145 = 117859) B117859
theorem B353753 : Blo 103782 353753 := bstep (se 2 (by rfl) ⟨132657, by rfl⟩ : syracuseStep 353753 = 265315) B265315
theorem B157259 : Blo 103782 157259 := bstep (se 1 (by rfl) ⟨117944, by rfl⟩ : syracuseStep 157259 = 235889) B235889
theorem B157271 : Blo 103782 157271 := bstep (se 1 (by rfl) ⟨117953, by rfl⟩ : syracuseStep 157271 = 235907) B235907
theorem B157337 : Blo 103782 157337 := bstep (se 2 (by rfl) ⟨59001, by rfl⟩ : syracuseStep 157337 = 118003) B118003
theorem B452299 : Blo 103782 452299 := bstep (se 1 (by rfl) ⟨339224, by rfl⟩ : syracuseStep 452299 = 678449) B678449
theorem B386819 : Blo 103782 386819 := bstep (se 1 (by rfl) ⟨290114, by rfl⟩ : syracuseStep 386819 = 580229) B580229
theorem B157451 : Blo 103782 157451 := bstep (se 1 (by rfl) ⟨118088, by rfl⟩ : syracuseStep 157451 = 236177) B236177
theorem B157463 : Blo 103782 157463 := bstep (se 1 (by rfl) ⟨118097, by rfl⟩ : syracuseStep 157463 = 236195) B236195
theorem B157529 : Blo 103782 157529 := bstep (se 2 (by rfl) ⟨59073, by rfl⟩ : syracuseStep 157529 = 118147) B118147
theorem B157643 : Blo 103782 157643 := bstep (se 1 (by rfl) ⟨118232, by rfl⟩ : syracuseStep 157643 = 236465) B236465
theorem B157655 : Blo 103782 157655 := bstep (se 1 (by rfl) ⟨118241, by rfl⟩ : syracuseStep 157655 = 236483) B236483
theorem B452573 : Blo 103782 452573 := bstep (se 3 (by rfl) ⟨84857, by rfl⟩ : syracuseStep 452573 = 169715) B169715
theorem B157721 : Blo 103782 157721 := bstep (se 2 (by rfl) ⟨59145, by rfl⟩ : syracuseStep 157721 = 118291) B118291
theorem B157835 : Blo 103782 157835 := bstep (se 1 (by rfl) ⟨118376, by rfl⟩ : syracuseStep 157835 = 236753) B236753
theorem B354455 : Blo 103782 354455 := bstep (se 1 (by rfl) ⟨265841, by rfl⟩ : syracuseStep 354455 = 531683) B531683
theorem B157847 : Blo 103782 157847 := bstep (se 1 (by rfl) ⟨118385, by rfl⟩ : syracuseStep 157847 = 236771) B236771
theorem B3106997 : Blo 103782 3106997 := bstep (se 5 (by rfl) ⟨145640, by rfl⟩ : syracuseStep 3106997 = 291281) B291281
theorem B157913 : Blo 103782 157913 := bstep (se 2 (by rfl) ⟨59217, by rfl⟩ : syracuseStep 157913 = 118435) B118435
theorem B452915 : Blo 103782 452915 := bstep (se 1 (by rfl) ⟨339686, by rfl⟩ : syracuseStep 452915 = 679373) B679373
theorem B223553 : Blo 103782 223553 := bstep (se 2 (by rfl) ⟨83832, by rfl⟩ : syracuseStep 223553 = 167665) B167665
theorem B158027 : Blo 103782 158027 := bstep (se 1 (by rfl) ⟨118520, by rfl⟩ : syracuseStep 158027 = 237041) B237041
theorem B158039 : Blo 103782 158039 := bstep (se 1 (by rfl) ⟨118529, by rfl⟩ : syracuseStep 158039 = 237059) B237059
theorem B551261 : Blo 103782 551261 := bstep (se 3 (by rfl) ⟨103361, by rfl⟩ : syracuseStep 551261 = 206723) B206723
theorem B158105 : Blo 103782 158105 := bstep (se 2 (by rfl) ⟨59289, by rfl⟩ : syracuseStep 158105 = 118579) B118579
theorem B158219 : Blo 103782 158219 := bstep (se 1 (by rfl) ⟨118664, by rfl⟩ : syracuseStep 158219 = 237329) B237329
theorem B158231 : Blo 103782 158231 := bstep (se 1 (by rfl) ⟨118673, by rfl⟩ : syracuseStep 158231 = 237347) B237347
theorem B158297 : Blo 103782 158297 := bstep (se 2 (by rfl) ⟨59361, by rfl⟩ : syracuseStep 158297 = 118723) B118723
theorem B354995 : Blo 103782 354995 := bstep (se 1 (by rfl) ⟨266246, by rfl⟩ : syracuseStep 354995 = 532493) B532493
theorem B158411 : Blo 103782 158411 := bstep (se 1 (by rfl) ⟨118808, by rfl⟩ : syracuseStep 158411 = 237617) B237617
theorem B158423 : Blo 103782 158423 := bstep (se 1 (by rfl) ⟨118817, by rfl⟩ : syracuseStep 158423 = 237635) B237635
theorem B158489 : Blo 103782 158489 := bstep (se 2 (by rfl) ⟨59433, by rfl⟩ : syracuseStep 158489 = 118867) B118867
theorem B1469249 : Blo 103782 1469249 := bstep (se 2 (by rfl) ⟨550968, by rfl⟩ : syracuseStep 1469249 = 1101937) B1101937
theorem B912221 : Blo 103782 912221 := bstep (se 3 (by rfl) ⟨171041, by rfl⟩ : syracuseStep 912221 = 342083) B342083
theorem B387971 : Blo 103782 387971 := bstep (se 1 (by rfl) ⟨290978, by rfl⟩ : syracuseStep 387971 = 581957) B581957
theorem B158603 : Blo 103782 158603 := bstep (se 1 (by rfl) ⟨118952, by rfl⟩ : syracuseStep 158603 = 237905) B237905
theorem B158615 : Blo 103782 158615 := bstep (se 1 (by rfl) ⟨118961, by rfl⟩ : syracuseStep 158615 = 237923) B237923
theorem B355265 : Blo 103782 355265 := bstep (se 2 (by rfl) ⟨133224, by rfl⟩ : syracuseStep 355265 = 266449) B266449
theorem B158681 : Blo 103782 158681 := bstep (se 2 (by rfl) ⟨59505, by rfl⟩ : syracuseStep 158681 = 119011) B119011
theorem B125975 : Blo 103782 125975 := bstep (se 1 (by rfl) ⟨94481, by rfl⟩ : syracuseStep 125975 = 188963) B188963
theorem B158795 : Blo 103782 158795 := bstep (se 1 (by rfl) ⟨119096, by rfl⟩ : syracuseStep 158795 = 238193) B238193
theorem B158807 : Blo 103782 158807 := bstep (se 1 (by rfl) ⟨119105, by rfl⟩ : syracuseStep 158807 = 238211) B238211
theorem B224407 : Blo 103782 224407 := bstep (se 1 (by rfl) ⟨168305, by rfl⟩ : syracuseStep 224407 = 336611) B336611
theorem B158873 : Blo 103782 158873 := bstep (se 2 (by rfl) ⟨59577, by rfl⟩ : syracuseStep 158873 = 119155) B119155
theorem B158987 : Blo 103782 158987 := bstep (se 1 (by rfl) ⟨119240, by rfl⟩ : syracuseStep 158987 = 238481) B238481
theorem B158999 : Blo 103782 158999 := bstep (se 1 (by rfl) ⟨119249, by rfl⟩ : syracuseStep 158999 = 238499) B238499
theorem B159065 : Blo 103782 159065 := bstep (se 2 (by rfl) ⟨59649, by rfl⟩ : syracuseStep 159065 = 119299) B119299
theorem B290137 : Blo 103782 290137 := bstep (se 2 (by rfl) ⟨108801, by rfl⟩ : syracuseStep 290137 = 217603) B217603
theorem B159127 : Blo 103782 159127 := bstep (se 1 (by rfl) ⟨119345, by rfl⟩ : syracuseStep 159127 = 238691) B238691
theorem B159179 : Blo 103782 159179 := bstep (se 1 (by rfl) ⟨119384, by rfl⟩ : syracuseStep 159179 = 238769) B238769
theorem B159191 : Blo 103782 159191 := bstep (se 1 (by rfl) ⟨119393, by rfl⟩ : syracuseStep 159191 = 238787) B238787
theorem B650713 : Blo 103782 650713 := bstep (se 2 (by rfl) ⟨244017, by rfl⟩ : syracuseStep 650713 = 488035) B488035
theorem B355805 : Blo 103782 355805 := bstep (se 3 (by rfl) ⟨66713, by rfl⟩ : syracuseStep 355805 = 133427) B133427
theorem B159257 : Blo 103782 159257 := bstep (se 2 (by rfl) ⟨59721, by rfl⟩ : syracuseStep 159257 = 119443) B119443
theorem B159371 : Blo 103782 159371 := bstep (se 1 (by rfl) ⟨119528, by rfl⟩ : syracuseStep 159371 = 239057) B239057
theorem B159383 : Blo 103782 159383 := bstep (se 1 (by rfl) ⟨119537, by rfl⟩ : syracuseStep 159383 = 239075) B239075
theorem B159449 : Blo 103782 159449 := bstep (se 2 (by rfl) ⟨59793, by rfl⟩ : syracuseStep 159449 = 119587) B119587
theorem B159563 : Blo 103782 159563 := bstep (se 1 (by rfl) ⟨119672, by rfl⟩ : syracuseStep 159563 = 239345) B239345
theorem B159575 : Blo 103782 159575 := bstep (se 1 (by rfl) ⟨119681, by rfl⟩ : syracuseStep 159575 = 239363) B239363
theorem B159641 : Blo 103782 159641 := bstep (se 2 (by rfl) ⟨59865, by rfl⟩ : syracuseStep 159641 = 119731) B119731
theorem B225227 : Blo 103782 225227 := bstep (se 1 (by rfl) ⟨168920, by rfl⟩ : syracuseStep 225227 = 337841) B337841
theorem B159755 : Blo 103782 159755 := bstep (se 1 (by rfl) ⟨119816, by rfl⟩ : syracuseStep 159755 = 239633) B239633
theorem B159767 : Blo 103782 159767 := bstep (se 1 (by rfl) ⟨119825, by rfl⟩ : syracuseStep 159767 = 239651) B239651
theorem B127051 : Blo 103782 127051 := bstep (se 1 (by rfl) ⟨95288, by rfl⟩ : syracuseStep 127051 = 190577) B190577
theorem B192601 : Blo 103782 192601 := bstep (se 2 (by rfl) ⟨72225, by rfl⟩ : syracuseStep 192601 = 144451) B144451
theorem B159833 : Blo 103782 159833 := bstep (se 2 (by rfl) ⟨59937, by rfl⟩ : syracuseStep 159833 = 119875) B119875
theorem B159947 : Blo 103782 159947 := bstep (se 1 (by rfl) ⟨119960, by rfl⟩ : syracuseStep 159947 = 239921) B239921
theorem B159959 : Blo 103782 159959 := bstep (se 1 (by rfl) ⟨119969, by rfl⟩ : syracuseStep 159959 = 239939) B239939
theorem B160025 : Blo 103782 160025 := bstep (se 2 (by rfl) ⟨60009, by rfl⟩ : syracuseStep 160025 = 120019) B120019
theorem B160139 : Blo 103782 160139 := bstep (se 1 (by rfl) ⟨120104, by rfl⟩ : syracuseStep 160139 = 240209) B240209
theorem B160151 : Blo 103782 160151 := bstep (se 1 (by rfl) ⟨120113, by rfl⟩ : syracuseStep 160151 = 240227) B240227
theorem B160217 : Blo 103782 160217 := bstep (se 2 (by rfl) ⟨60081, by rfl⟩ : syracuseStep 160217 = 120163) B120163
theorem B356939 : Blo 103782 356939 := bstep (se 1 (by rfl) ⟨267704, by rfl⟩ : syracuseStep 356939 = 535409) B535409
theorem B160331 : Blo 103782 160331 := bstep (se 1 (by rfl) ⟨120248, by rfl⟩ : syracuseStep 160331 = 240497) B240497
theorem B160343 : Blo 103782 160343 := bstep (se 1 (by rfl) ⟨120257, by rfl⟩ : syracuseStep 160343 = 240515) B240515
theorem B2716253 : Blo 103782 2716253 := bstep (se 3 (by rfl) ⟨509297, by rfl⟩ : syracuseStep 2716253 = 1018595) B1018595
theorem B160409 : Blo 103782 160409 := bstep (se 2 (by rfl) ⟨60153, by rfl⟩ : syracuseStep 160409 = 120307) B120307
theorem B455341 : Blo 103782 455341 := bstep (se 3 (by rfl) ⟨85376, by rfl⟩ : syracuseStep 455341 = 170753) B170753
theorem B160523 : Blo 103782 160523 := bstep (se 1 (by rfl) ⟨120392, by rfl⟩ : syracuseStep 160523 = 240785) B240785
theorem B160535 : Blo 103782 160535 := bstep (se 1 (by rfl) ⟨120401, by rfl⟩ : syracuseStep 160535 = 240803) B240803
theorem B357209 : Blo 103782 357209 := bstep (se 2 (by rfl) ⟨133953, by rfl⟩ : syracuseStep 357209 = 267907) B267907
theorem B160601 : Blo 103782 160601 := bstep (se 2 (by rfl) ⟨60225, by rfl⟩ : syracuseStep 160601 = 120451) B120451
theorem B3240805 : Blo 103782 3240805 := bstep (se 4 (by rfl) ⟨303825, by rfl⟩ : syracuseStep 3240805 = 607651) B607651
theorem B357313 : Blo 103782 357313 := bstep (se 2 (by rfl) ⟨133992, by rfl⟩ : syracuseStep 357313 = 267985) B267985
theorem B160715 : Blo 103782 160715 := bstep (se 1 (by rfl) ⟨120536, by rfl⟩ : syracuseStep 160715 = 241073) B241073
theorem B160727 : Blo 103782 160727 := bstep (se 1 (by rfl) ⟨120545, by rfl⟩ : syracuseStep 160727 = 241091) B241091
theorem B914449 : Blo 103782 914449 := bstep (se 2 (by rfl) ⟨342918, by rfl⟩ : syracuseStep 914449 = 685837) B685837
theorem B160793 : Blo 103782 160793 := bstep (se 2 (by rfl) ⟨60297, by rfl⟩ : syracuseStep 160793 = 120595) B120595
theorem B160907 : Blo 103782 160907 := bstep (se 1 (by rfl) ⟨120680, by rfl⟩ : syracuseStep 160907 = 241361) B241361
theorem B160919 : Blo 103782 160919 := bstep (se 1 (by rfl) ⟨120689, by rfl⟩ : syracuseStep 160919 = 241379) B241379
theorem B160985 : Blo 103782 160985 := bstep (se 2 (by rfl) ⟨60369, by rfl⟩ : syracuseStep 160985 = 120739) B120739
theorem B161099 : Blo 103782 161099 := bstep (se 1 (by rfl) ⟨120824, by rfl⟩ : syracuseStep 161099 = 241649) B241649
theorem B161111 : Blo 103782 161111 := bstep (se 1 (by rfl) ⟨120833, by rfl⟩ : syracuseStep 161111 = 241667) B241667
theorem B193943 : Blo 103782 193943 := bstep (se 1 (by rfl) ⟨145457, by rfl⟩ : syracuseStep 193943 = 290915) B290915
theorem B161177 : Blo 103782 161177 := bstep (se 2 (by rfl) ⟨60441, by rfl⟩ : syracuseStep 161177 = 120883) B120883
theorem B1570265 : Blo 103782 1570265 := bstep (se 2 (by rfl) ⟨588849, by rfl⟩ : syracuseStep 1570265 = 1177699) B1177699
theorem B161291 : Blo 103782 161291 := bstep (se 1 (by rfl) ⟨120968, by rfl⟩ : syracuseStep 161291 = 241937) B241937
theorem B357911 : Blo 103782 357911 := bstep (se 1 (by rfl) ⟨268433, by rfl⟩ : syracuseStep 357911 = 536867) B536867
theorem B488983 : Blo 103782 488983 := bstep (se 1 (by rfl) ⟨366737, by rfl⟩ : syracuseStep 488983 = 733475) B733475
theorem B161303 : Blo 103782 161303 := bstep (se 1 (by rfl) ⟨120977, by rfl⟩ : syracuseStep 161303 = 241955) B241955
theorem B161369 : Blo 103782 161369 := bstep (se 2 (by rfl) ⟨60513, by rfl⟩ : syracuseStep 161369 = 121027) B121027
theorem B161483 : Blo 103782 161483 := bstep (se 1 (by rfl) ⟨121112, by rfl⟩ : syracuseStep 161483 = 242225) B242225
theorem B161495 : Blo 103782 161495 := bstep (se 1 (by rfl) ⟨121121, by rfl⟩ : syracuseStep 161495 = 242243) B242243
theorem B161561 : Blo 103782 161561 := bstep (se 2 (by rfl) ⟨60585, by rfl⟩ : syracuseStep 161561 = 121171) B121171
theorem B423755 : Blo 103782 423755 := bstep (se 1 (by rfl) ⟨317816, by rfl⟩ : syracuseStep 423755 = 635633) B635633
theorem B358451 : Blo 103782 358451 := bstep (se 1 (by rfl) ⟨268838, by rfl⟩ : syracuseStep 358451 = 537677) B537677
theorem B227585 : Blo 103782 227585 := bstep (se 2 (by rfl) ⟨85344, by rfl⟩ : syracuseStep 227585 = 170689) B170689
theorem B358721 : Blo 103782 358721 := bstep (se 2 (by rfl) ⟨134520, by rfl⟩ : syracuseStep 358721 = 269041) B269041
theorem B1374529 : Blo 103782 1374529 := bstep (se 2 (by rfl) ⟨515448, by rfl⟩ : syracuseStep 1374529 = 1030897) B1030897
theorem B227927 : Blo 103782 227927 := bstep (se 1 (by rfl) ⟨170945, by rfl⟩ : syracuseStep 227927 = 341891) B341891
theorem B817937 : Blo 103782 817937 := bstep (se 2 (by rfl) ⟨306726, by rfl⟩ : syracuseStep 817937 = 613453) B613453
theorem B359261 : Blo 103782 359261 := bstep (se 3 (by rfl) ⟨67361, by rfl⟩ : syracuseStep 359261 = 134723) B134723
theorem B457751 : Blo 103782 457751 := bstep (se 1 (by rfl) ⟨343313, by rfl⟩ : syracuseStep 457751 = 686627) B686627
theorem B293977 : Blo 103782 293977 := bstep (se 2 (by rfl) ⟨110241, by rfl⟩ : syracuseStep 293977 = 220483) B220483
theorem B228491 : Blo 103782 228491 := bstep (se 1 (by rfl) ⟨171368, by rfl⟩ : syracuseStep 228491 = 342737) B342737
theorem B1211597 : Blo 103782 1211597 := bstep (se 3 (by rfl) ⟨227174, by rfl⟩ : syracuseStep 1211597 = 454349) B454349
theorem B425309 : Blo 103782 425309 := bstep (se 3 (by rfl) ⟨79745, by rfl⟩ : syracuseStep 425309 = 159491) B159491
theorem B229081 : Blo 103782 229081 := bstep (se 2 (by rfl) ⟨85905, by rfl⟩ : syracuseStep 229081 = 171811) B171811
theorem B360395 : Blo 103782 360395 := bstep (se 1 (by rfl) ⟨270296, by rfl⟩ : syracuseStep 360395 = 540593) B540593
theorem B360719 : Blo 103782 360719 := bstep (se 1 (by rfl) ⟨270539, by rfl⟩ : syracuseStep 360719 = 541079) B541079
theorem B2031965 : Blo 103782 2031965 := bstep (se 3 (by rfl) ⟨380993, by rfl⟩ : syracuseStep 2031965 = 761987) B761987
theorem B360989 : Blo 103782 360989 := bstep (se 3 (by rfl) ⟨67685, by rfl⟩ : syracuseStep 360989 = 135371) B135371
theorem B197255 : Blo 103782 197255 := bstep (se 1 (by rfl) ⟨147941, by rfl⟩ : syracuseStep 197255 = 295883) B295883
theorem B263027 : Blo 103782 263027 := bstep (se 1 (by rfl) ⟨197270, by rfl⟩ : syracuseStep 263027 = 394541) B394541
theorem B131959 : Blo 103782 131959 := bstep (se 1 (by rfl) ⟨98969, by rfl⟩ : syracuseStep 131959 = 197939) B197939
theorem B263047 : Blo 103782 263047 := bstep (se 1 (by rfl) ⟨197285, by rfl⟩ : syracuseStep 263047 = 394571) B394571
theorem B623627 : Blo 103782 623627 := bstep (se 1 (by rfl) ⟨467720, by rfl⟩ : syracuseStep 623627 = 935441) B935441
theorem B263321 : Blo 103782 263321 := bstep (se 2 (by rfl) ⟨98745, by rfl⟩ : syracuseStep 263321 = 197491) B197491
theorem B132283 : Blo 103782 132283 := bstep (se 1 (by rfl) ⟨99212, by rfl⟩ : syracuseStep 132283 = 198425) B198425
theorem B263483 : Blo 103782 263483 := bstep (se 1 (by rfl) ⟨197612, by rfl⟩ : syracuseStep 263483 = 395225) B395225
theorem B1082771 : Blo 103782 1082771 := bstep (se 1 (by rfl) ⟨812078, by rfl⟩ : syracuseStep 1082771 = 1624157) B1624157
theorem B3016115 : Blo 103782 3016115 := bstep (se 1 (by rfl) ⟨2262086, by rfl⟩ : syracuseStep 3016115 = 4524173) B4524173
theorem B263695 : Blo 103782 263695 := bstep (se 1 (by rfl) ⟨197771, by rfl⟩ : syracuseStep 263695 = 395543) B395543
theorem B460349 : Blo 103782 460349 := bstep (se 3 (by rfl) ⟨86315, by rfl⟩ : syracuseStep 460349 = 172631) B172631
theorem B7603789 : Blo 103782 7603789 := bstep (se 3 (by rfl) ⟨1425710, by rfl⟩ : syracuseStep 7603789 = 2851421) B2851421
theorem B296567 : Blo 103782 296567 := bstep (se 1 (by rfl) ⟨222425, by rfl⟩ : syracuseStep 296567 = 444851) B444851
theorem B132779 : Blo 103782 132779 := bstep (se 1 (by rfl) ⟨99584, by rfl⟩ : syracuseStep 132779 = 199169) B199169
theorem B263969 : Blo 103782 263969 := bstep (se 2 (by rfl) ⟨98988, by rfl⟩ : syracuseStep 263969 = 197977) B197977
theorem B362393 : Blo 103782 362393 := bstep (se 2 (by rfl) ⟨135897, by rfl⟩ : syracuseStep 362393 = 271795) B271795
theorem B1837079 : Blo 103782 1837079 := bstep (se 1 (by rfl) ⟨1377809, by rfl⟩ : syracuseStep 1837079 = 2755619) B2755619
theorem B133255 : Blo 103782 133255 := bstep (se 1 (by rfl) ⟨99941, by rfl⟩ : syracuseStep 133255 = 199883) B199883
theorem B592109 : Blo 103782 592109 := bstep (se 3 (by rfl) ⟨111020, by rfl⟩ : syracuseStep 592109 = 222041) B222041
theorem B231995 : Blo 103782 231995 := bstep (se 1 (by rfl) ⟨173996, by rfl⟩ : syracuseStep 231995 = 347993) B347993
theorem B363095 : Blo 103782 363095 := bstep (se 1 (by rfl) ⟨272321, by rfl⟩ : syracuseStep 363095 = 544643) B544643
theorem B133751 : Blo 103782 133751 := bstep (se 1 (by rfl) ⟨100313, by rfl⟩ : syracuseStep 133751 = 200627) B200627
theorem B1182437 : Blo 103782 1182437 := bstep (se 4 (by rfl) ⟨110853, by rfl⟩ : syracuseStep 1182437 = 221707) B221707
theorem B264971 : Blo 103782 264971 := bstep (se 1 (by rfl) ⟨198728, by rfl⟩ : syracuseStep 264971 = 397457) B397457
theorem B789263 : Blo 103782 789263 := bstep (se 1 (by rfl) ⟨591947, by rfl⟩ : syracuseStep 789263 = 1183895) B1183895
theorem B133903 : Blo 103782 133903 := bstep (se 1 (by rfl) ⟨100427, by rfl⟩ : syracuseStep 133903 = 200855) B200855
theorem B134075 : Blo 103782 134075 := bstep (se 1 (by rfl) ⟨100556, by rfl⟩ : syracuseStep 134075 = 201113) B201113
theorem B199739 : Blo 103782 199739 := bstep (se 1 (by rfl) ⟨149804, by rfl⟩ : syracuseStep 199739 = 299609) B299609
theorem B363581 : Blo 103782 363581 := bstep (se 3 (by rfl) ⟨68171, by rfl⟩ : syracuseStep 363581 = 136343) B136343
theorem B1510487 : Blo 103782 1510487 := bstep (se 1 (by rfl) ⟨1132865, by rfl⟩ : syracuseStep 1510487 = 2265731) B2265731
theorem B363809 : Blo 103782 363809 := bstep (se 2 (by rfl) ⟨136428, by rfl⟩ : syracuseStep 363809 = 272857) B272857
theorem B265619 : Blo 103782 265619 := bstep (se 1 (by rfl) ⟨199214, by rfl⟩ : syracuseStep 265619 = 398429) B398429
theorem B396697 : Blo 103782 396697 := bstep (se 2 (by rfl) ⟨148761, by rfl⟩ : syracuseStep 396697 = 297523) B297523
theorem B200225 : Blo 103782 200225 := bstep (se 2 (by rfl) ⟨75084, by rfl⟩ : syracuseStep 200225 = 150169) B150169
theorem B265913 : Blo 103782 265913 := bstep (se 2 (by rfl) ⟨99717, by rfl⟩ : syracuseStep 265913 = 199435) B199435
theorem B397001 : Blo 103782 397001 := bstep (se 2 (by rfl) ⟨148875, by rfl⟩ : syracuseStep 397001 = 297751) B297751
theorem B135047 : Blo 103782 135047 := bstep (se 1 (by rfl) ⟨101285, by rfl⟩ : syracuseStep 135047 = 202571) B202571
theorem B528281 : Blo 103782 528281 := bstep (se 2 (by rfl) ⟨198105, by rfl⟩ : syracuseStep 528281 = 396211) B396211
theorem B233531 : Blo 103782 233531 := bstep (se 1 (by rfl) ⟨175148, by rfl⟩ : syracuseStep 233531 = 350297) B350297
theorem B233657 : Blo 103782 233657 := bstep (se 2 (by rfl) ⟨87621, by rfl⟩ : syracuseStep 233657 = 175243) B175243
theorem B299209 : Blo 103782 299209 := bstep (se 2 (by rfl) ⟨112203, by rfl⟩ : syracuseStep 299209 = 224407) B224407
theorem B266611 : Blo 103782 266611 := bstep (se 1 (by rfl) ⟨199958, by rfl⟩ : syracuseStep 266611 = 399917) B399917
theorem B266753 : Blo 103782 266753 := bstep (se 2 (by rfl) ⟨100032, by rfl⟩ : syracuseStep 266753 = 200065) B200065
theorem B233999 : Blo 103782 233999 := bstep (se 1 (by rfl) ⟨175499, by rfl⟩ : syracuseStep 233999 = 350999) B350999
theorem B135695 : Blo 103782 135695 := bstep (se 1 (by rfl) ⟨101771, by rfl⟩ : syracuseStep 135695 = 203543) B203543
theorem B234017 : Blo 103782 234017 := bstep (se 2 (by rfl) ⟨87756, by rfl⟩ : syracuseStep 234017 = 175513) B175513
theorem B594499 : Blo 103782 594499 := bstep (se 1 (by rfl) ⟨445874, by rfl⟩ : syracuseStep 594499 = 891749) B891749
theorem B397943 : Blo 103782 397943 := bstep (se 1 (by rfl) ⟨298457, by rfl⟩ : syracuseStep 397943 = 596915) B596915
theorem B234359 : Blo 103782 234359 := bstep (se 1 (by rfl) ⟨175769, by rfl⟩ : syracuseStep 234359 = 351539) B351539
theorem B267209 : Blo 103782 267209 := bstep (se 2 (by rfl) ⟨100203, by rfl⟩ : syracuseStep 267209 = 200407) B200407
theorem B234539 : Blo 103782 234539 := bstep (se 1 (by rfl) ⟨175904, by rfl⟩ : syracuseStep 234539 = 351809) B351809
theorem B267563 : Blo 103782 267563 := bstep (se 1 (by rfl) ⟨200672, by rfl⟩ : syracuseStep 267563 = 401345) B401345
theorem B103815 : Blo 103782 103815 := bstep (se 1 (by rfl) ⟨77861, by rfl⟩ : syracuseStep 103815 = 155723) B155723
theorem B103823 : Blo 103782 103823 := bstep (se 1 (by rfl) ⟨77867, by rfl⟩ : syracuseStep 103823 = 155735) B155735
theorem B234899 : Blo 103782 234899 := bstep (se 1 (by rfl) ⟨176174, by rfl⟩ : syracuseStep 234899 = 352349) B352349
theorem B202169 : Blo 103782 202169 := bstep (se 2 (by rfl) ⟨75813, by rfl⟩ : syracuseStep 202169 = 151627) B151627
theorem B103867 : Blo 103782 103867 := bstep (se 1 (by rfl) ⟨77900, by rfl⟩ : syracuseStep 103867 = 155801) B155801
theorem B234953 : Blo 103782 234953 := bstep (se 2 (by rfl) ⟨88107, by rfl⟩ : syracuseStep 234953 = 176215) B176215
theorem B103943 : Blo 103782 103943 := bstep (se 1 (by rfl) ⟨77957, by rfl⟩ : syracuseStep 103943 = 155915) B155915
theorem B103951 : Blo 103782 103951 := bstep (se 1 (by rfl) ⟨77963, by rfl⟩ : syracuseStep 103951 = 155927) B155927
theorem B103995 : Blo 103782 103995 := bstep (se 1 (by rfl) ⟨77996, by rfl⟩ : syracuseStep 103995 = 155993) B155993
theorem B398915 : Blo 103782 398915 := bstep (se 1 (by rfl) ⟨299186, by rfl⟩ : syracuseStep 398915 = 598373) B598373
theorem B104071 : Blo 103782 104071 := bstep (se 1 (by rfl) ⟨78053, by rfl⟩ : syracuseStep 104071 = 156107) B156107
theorem B169607 : Blo 103782 169607 := bstep (se 1 (by rfl) ⟨127205, by rfl⟩ : syracuseStep 169607 = 254411) B254411
theorem B104079 : Blo 103782 104079 := bstep (se 1 (by rfl) ⟨78059, by rfl⟩ : syracuseStep 104079 = 156119) B156119
theorem B104123 : Blo 103782 104123 := bstep (se 1 (by rfl) ⟨78092, by rfl⟩ : syracuseStep 104123 = 156185) B156185
theorem B104199 : Blo 103782 104199 := bstep (se 1 (by rfl) ⟨78149, by rfl⟩ : syracuseStep 104199 = 156299) B156299
theorem B104207 : Blo 103782 104207 := bstep (se 1 (by rfl) ⟨78155, by rfl⟩ : syracuseStep 104207 = 156311) B156311
theorem B104251 : Blo 103782 104251 := bstep (se 1 (by rfl) ⟨78188, by rfl⟩ : syracuseStep 104251 = 156377) B156377
theorem B104327 : Blo 103782 104327 := bstep (se 1 (by rfl) ⟨78245, by rfl⟩ : syracuseStep 104327 = 156491) B156491
theorem B104335 : Blo 103782 104335 := bstep (se 1 (by rfl) ⟨78251, by rfl⟩ : syracuseStep 104335 = 156503) B156503
theorem B333715 : Blo 103782 333715 := bstep (se 1 (by rfl) ⟨250286, by rfl⟩ : syracuseStep 333715 = 500573) B500573
theorem B104379 : Blo 103782 104379 := bstep (se 1 (by rfl) ⟨78284, by rfl⟩ : syracuseStep 104379 = 156569) B156569
theorem B104455 : Blo 103782 104455 := bstep (se 1 (by rfl) ⟨78341, by rfl⟩ : syracuseStep 104455 = 156683) B156683
theorem B301067 : Blo 103782 301067 := bstep (se 1 (by rfl) ⟨225800, by rfl⟩ : syracuseStep 301067 = 451601) B451601
theorem B104463 : Blo 103782 104463 := bstep (se 1 (by rfl) ⟨78347, by rfl⟩ : syracuseStep 104463 = 156695) B156695
theorem B104507 : Blo 103782 104507 := bstep (se 1 (by rfl) ⟨78380, by rfl⟩ : syracuseStep 104507 = 156761) B156761
theorem B1251389 : Blo 103782 1251389 := bstep (se 3 (by rfl) ⟨234635, by rfl⟩ : syracuseStep 1251389 = 469271) B469271
theorem B104583 : Blo 103782 104583 := bstep (se 1 (by rfl) ⟨78437, by rfl⟩ : syracuseStep 104583 = 156875) B156875
theorem B235655 : Blo 103782 235655 := bstep (se 1 (by rfl) ⟨176741, by rfl⟩ : syracuseStep 235655 = 353483) B353483
theorem B104591 : Blo 103782 104591 := bstep (se 1 (by rfl) ⟨78443, by rfl⟩ : syracuseStep 104591 = 156887) B156887
theorem B104635 : Blo 103782 104635 := bstep (se 1 (by rfl) ⟨78476, by rfl⟩ : syracuseStep 104635 = 156953) B156953
theorem B104711 : Blo 103782 104711 := bstep (se 1 (by rfl) ⟨78533, by rfl⟩ : syracuseStep 104711 = 157067) B157067
theorem B268555 : Blo 103782 268555 := bstep (se 1 (by rfl) ⟨201416, by rfl⟩ : syracuseStep 268555 = 402833) B402833
theorem B104719 : Blo 103782 104719 := bstep (se 1 (by rfl) ⟨78539, by rfl⟩ : syracuseStep 104719 = 157079) B157079
theorem B104763 : Blo 103782 104763 := bstep (se 1 (by rfl) ⟨78572, by rfl⟩ : syracuseStep 104763 = 157145) B157145
theorem B235835 : Blo 103782 235835 := bstep (se 1 (by rfl) ⟨176876, by rfl⟩ : syracuseStep 235835 = 353753) B353753
theorem B104839 : Blo 103782 104839 := bstep (se 1 (by rfl) ⟨78629, by rfl⟩ : syracuseStep 104839 = 157259) B157259
theorem B104847 : Blo 103782 104847 := bstep (se 1 (by rfl) ⟨78635, by rfl⟩ : syracuseStep 104847 = 157271) B157271
theorem B268697 : Blo 103782 268697 := bstep (se 2 (by rfl) ⟨100761, by rfl⟩ : syracuseStep 268697 = 201523) B201523
theorem B530873 : Blo 103782 530873 := bstep (se 2 (by rfl) ⟨199077, by rfl⟩ : syracuseStep 530873 = 398155) B398155
theorem B235961 : Blo 103782 235961 := bstep (se 2 (by rfl) ⟨88485, by rfl⟩ : syracuseStep 235961 = 176971) B176971
theorem B104891 : Blo 103782 104891 := bstep (se 1 (by rfl) ⟨78668, by rfl⟩ : syracuseStep 104891 = 157337) B157337
theorem B596483 : Blo 103782 596483 := bstep (se 1 (by rfl) ⟨447362, by rfl⟩ : syracuseStep 596483 = 894725) B894725
theorem B104967 : Blo 103782 104967 := bstep (se 1 (by rfl) ⟨78725, by rfl⟩ : syracuseStep 104967 = 157451) B157451
theorem B104975 : Blo 103782 104975 := bstep (se 1 (by rfl) ⟨78731, by rfl⟩ : syracuseStep 104975 = 157463) B157463
theorem B105019 : Blo 103782 105019 := bstep (se 1 (by rfl) ⟨78764, by rfl⟩ : syracuseStep 105019 = 157529) B157529
theorem B268859 : Blo 103782 268859 := bstep (se 1 (by rfl) ⟨201644, by rfl⟩ : syracuseStep 268859 = 403289) B403289
theorem B203323 : Blo 103782 203323 := bstep (se 1 (by rfl) ⟨152492, by rfl⟩ : syracuseStep 203323 = 304985) B304985
theorem B105095 : Blo 103782 105095 := bstep (se 1 (by rfl) ⟨78821, by rfl⟩ : syracuseStep 105095 = 157643) B157643
theorem B105103 : Blo 103782 105103 := bstep (se 1 (by rfl) ⟨78827, by rfl⟩ : syracuseStep 105103 = 157655) B157655
theorem B301715 : Blo 103782 301715 := bstep (se 1 (by rfl) ⟨226286, by rfl⟩ : syracuseStep 301715 = 452573) B452573
theorem B105147 : Blo 103782 105147 := bstep (se 1 (by rfl) ⟨78860, by rfl⟩ : syracuseStep 105147 = 157721) B157721
theorem B1219265 : Blo 103782 1219265 := bstep (se 2 (by rfl) ⟨457224, by rfl⟩ : syracuseStep 1219265 = 914449) B914449
theorem B105223 : Blo 103782 105223 := bstep (se 1 (by rfl) ⟨78917, by rfl⟩ : syracuseStep 105223 = 157835) B157835
theorem B236303 : Blo 103782 236303 := bstep (se 1 (by rfl) ⟨177227, by rfl⟩ : syracuseStep 236303 = 354455) B354455
theorem B105231 : Blo 103782 105231 := bstep (se 1 (by rfl) ⟨78923, by rfl⟩ : syracuseStep 105231 = 157847) B157847
theorem B236321 : Blo 103782 236321 := bstep (se 2 (by rfl) ⟨88620, by rfl⟩ : syracuseStep 236321 = 177241) B177241
theorem B2071331 : Blo 103782 2071331 := bstep (se 1 (by rfl) ⟨1553498, by rfl⟩ : syracuseStep 2071331 = 3106997) B3106997
theorem B105275 : Blo 103782 105275 := bstep (se 1 (by rfl) ⟨78956, by rfl⟩ : syracuseStep 105275 = 157913) B157913
theorem B301943 : Blo 103782 301943 := bstep (se 1 (by rfl) ⟨226457, by rfl⟩ : syracuseStep 301943 = 452915) B452915
theorem B105351 : Blo 103782 105351 := bstep (se 1 (by rfl) ⟨79013, by rfl⟩ : syracuseStep 105351 = 158027) B158027
theorem B105359 : Blo 103782 105359 := bstep (se 1 (by rfl) ⟨79019, by rfl⟩ : syracuseStep 105359 = 158039) B158039
theorem B269203 : Blo 103782 269203 := bstep (se 1 (by rfl) ⟨201902, by rfl⟩ : syracuseStep 269203 = 403805) B403805
theorem B367507 : Blo 103782 367507 := bstep (se 1 (by rfl) ⟨275630, by rfl⟩ : syracuseStep 367507 = 551261) B551261
theorem B105403 : Blo 103782 105403 := bstep (se 1 (by rfl) ⟨79052, by rfl⟩ : syracuseStep 105403 = 158105) B158105
theorem B105479 : Blo 103782 105479 := bstep (se 1 (by rfl) ⟨79109, by rfl⟩ : syracuseStep 105479 = 158219) B158219
theorem B105487 : Blo 103782 105487 := bstep (se 1 (by rfl) ⟨79115, by rfl⟩ : syracuseStep 105487 = 158231) B158231
theorem B269345 : Blo 103782 269345 := bstep (se 2 (by rfl) ⟨101004, by rfl⟩ : syracuseStep 269345 = 202009) B202009
theorem B203809 : Blo 103782 203809 := bstep (se 2 (by rfl) ⟨76428, by rfl⟩ : syracuseStep 203809 = 152857) B152857
theorem B105531 : Blo 103782 105531 := bstep (se 1 (by rfl) ⟨79148, by rfl⟩ : syracuseStep 105531 = 158297) B158297
theorem B236663 : Blo 103782 236663 := bstep (se 1 (by rfl) ⟨177497, by rfl⟩ : syracuseStep 236663 = 354995) B354995
theorem B105607 : Blo 103782 105607 := bstep (se 1 (by rfl) ⟨79205, by rfl⟩ : syracuseStep 105607 = 158411) B158411
theorem B105615 : Blo 103782 105615 := bstep (se 1 (by rfl) ⟨79211, by rfl⟩ : syracuseStep 105615 = 158423) B158423
theorem B105659 : Blo 103782 105659 := bstep (se 1 (by rfl) ⟨79244, by rfl⟩ : syracuseStep 105659 = 158489) B158489
theorem B400585 : Blo 103782 400585 := bstep (se 2 (by rfl) ⟨150219, by rfl⟩ : syracuseStep 400585 = 300439) B300439
theorem B105735 : Blo 103782 105735 := bstep (se 1 (by rfl) ⟨79301, by rfl⟩ : syracuseStep 105735 = 158603) B158603
theorem B105743 : Blo 103782 105743 := bstep (se 1 (by rfl) ⟨79307, by rfl⟩ : syracuseStep 105743 = 158615) B158615
theorem B236843 : Blo 103782 236843 := bstep (se 1 (by rfl) ⟨177632, by rfl⟩ : syracuseStep 236843 = 355265) B355265
theorem B105787 : Blo 103782 105787 := bstep (se 1 (by rfl) ⟨79340, by rfl⟩ : syracuseStep 105787 = 158681) B158681
theorem B105863 : Blo 103782 105863 := bstep (se 1 (by rfl) ⟨79397, by rfl⟩ : syracuseStep 105863 = 158795) B158795
theorem B105871 : Blo 103782 105871 := bstep (se 1 (by rfl) ⟨79403, by rfl⟩ : syracuseStep 105871 = 158807) B158807
theorem B597401 : Blo 103782 597401 := bstep (se 2 (by rfl) ⟨224025, by rfl⟩ : syracuseStep 597401 = 448051) B448051
theorem B105915 : Blo 103782 105915 := bstep (se 1 (by rfl) ⟨79436, by rfl⟩ : syracuseStep 105915 = 158873) B158873
theorem B105991 : Blo 103782 105991 := bstep (se 1 (by rfl) ⟨79493, by rfl⟩ : syracuseStep 105991 = 158987) B158987
theorem B105999 : Blo 103782 105999 := bstep (se 1 (by rfl) ⟨79499, by rfl⟩ : syracuseStep 105999 = 158999) B158999
theorem B499229 : Blo 103782 499229 := bstep (se 3 (by rfl) ⟨93605, by rfl⟩ : syracuseStep 499229 = 187211) B187211
theorem B106043 : Blo 103782 106043 := bstep (se 1 (by rfl) ⟨79532, by rfl⟩ : syracuseStep 106043 = 159065) B159065
theorem B106119 : Blo 103782 106119 := bstep (se 1 (by rfl) ⟨79589, by rfl⟩ : syracuseStep 106119 = 159179) B159179
theorem B106127 : Blo 103782 106127 := bstep (se 1 (by rfl) ⟨79595, by rfl⟩ : syracuseStep 106127 = 159191) B159191
theorem B237203 : Blo 103782 237203 := bstep (se 1 (by rfl) ⟨177902, by rfl⟩ : syracuseStep 237203 = 355805) B355805
theorem B106171 : Blo 103782 106171 := bstep (se 1 (by rfl) ⟨79628, by rfl⟩ : syracuseStep 106171 = 159257) B159257
theorem B532169 : Blo 103782 532169 := bstep (se 2 (by rfl) ⟨199563, by rfl⟩ : syracuseStep 532169 = 399127) B399127
theorem B237257 : Blo 103782 237257 := bstep (se 2 (by rfl) ⟨88971, by rfl⟩ : syracuseStep 237257 = 177943) B177943
theorem B106247 : Blo 103782 106247 := bstep (se 1 (by rfl) ⟨79685, by rfl⟩ : syracuseStep 106247 = 159371) B159371
theorem B106255 : Blo 103782 106255 := bstep (se 1 (by rfl) ⟨79691, by rfl⟩ : syracuseStep 106255 = 159383) B159383
theorem B106299 : Blo 103782 106299 := bstep (se 1 (by rfl) ⟨79724, by rfl⟩ : syracuseStep 106299 = 159449) B159449
theorem B1122137 : Blo 103782 1122137 := bstep (se 2 (by rfl) ⟨420801, by rfl⟩ : syracuseStep 1122137 = 841603) B841603
theorem B106375 : Blo 103782 106375 := bstep (se 1 (by rfl) ⟨79781, by rfl⟩ : syracuseStep 106375 = 159563) B159563
theorem B106383 : Blo 103782 106383 := bstep (se 1 (by rfl) ⟨79787, by rfl⟩ : syracuseStep 106383 = 159575) B159575
theorem B106427 : Blo 103782 106427 := bstep (se 1 (by rfl) ⟨79820, by rfl⟩ : syracuseStep 106427 = 159641) B159641
theorem B270337 : Blo 103782 270337 := bstep (se 2 (by rfl) ⟨101376, by rfl⟩ : syracuseStep 270337 = 202753) B202753
theorem B106503 : Blo 103782 106503 := bstep (se 1 (by rfl) ⟨79877, by rfl⟩ : syracuseStep 106503 = 159755) B159755
theorem B106511 : Blo 103782 106511 := bstep (se 1 (by rfl) ⟨79883, by rfl⟩ : syracuseStep 106511 = 159767) B159767
theorem B106555 : Blo 103782 106555 := bstep (se 1 (by rfl) ⟨79916, by rfl⟩ : syracuseStep 106555 = 159833) B159833
theorem B335933 : Blo 103782 335933 := bstep (se 3 (by rfl) ⟨62987, by rfl⟩ : syracuseStep 335933 = 125975) B125975
theorem B106631 : Blo 103782 106631 := bstep (se 1 (by rfl) ⟨79973, by rfl⟩ : syracuseStep 106631 = 159947) B159947
theorem B106639 : Blo 103782 106639 := bstep (se 1 (by rfl) ⟨79979, by rfl⟩ : syracuseStep 106639 = 159959) B159959
theorem B106683 : Blo 103782 106683 := bstep (se 1 (by rfl) ⟨80012, by rfl⟩ : syracuseStep 106683 = 160025) B160025
theorem B106759 : Blo 103782 106759 := bstep (se 1 (by rfl) ⟨80069, by rfl⟩ : syracuseStep 106759 = 160139) B160139
theorem B106767 : Blo 103782 106767 := bstep (se 1 (by rfl) ⟨80075, by rfl⟩ : syracuseStep 106767 = 160151) B160151
theorem B106811 : Blo 103782 106811 := bstep (se 1 (by rfl) ⟨80108, by rfl⟩ : syracuseStep 106811 = 160217) B160217
theorem B303421 : Blo 103782 303421 := bstep (se 3 (by rfl) ⟨56891, by rfl⟩ : syracuseStep 303421 = 113783) B113783
theorem B237959 : Blo 103782 237959 := bstep (se 1 (by rfl) ⟨178469, by rfl⟩ : syracuseStep 237959 = 356939) B356939
theorem B106887 : Blo 103782 106887 := bstep (se 1 (by rfl) ⟨80165, by rfl⟩ : syracuseStep 106887 = 160331) B160331
theorem B106895 : Blo 103782 106895 := bstep (se 1 (by rfl) ⟨80171, by rfl⟩ : syracuseStep 106895 = 160343) B160343
theorem B1810835 : Blo 103782 1810835 := bstep (se 1 (by rfl) ⟨1358126, by rfl⟩ : syracuseStep 1810835 = 2716253) B2716253
theorem B106939 : Blo 103782 106939 := bstep (se 1 (by rfl) ⟨80204, by rfl⟩ : syracuseStep 106939 = 160409) B160409
theorem B107015 : Blo 103782 107015 := bstep (se 1 (by rfl) ⟨80261, by rfl⟩ : syracuseStep 107015 = 160523) B160523
theorem B107023 : Blo 103782 107023 := bstep (se 1 (by rfl) ⟨80267, by rfl⟩ : syracuseStep 107023 = 160535) B160535
theorem B238139 : Blo 103782 238139 := bstep (se 1 (by rfl) ⟨178604, by rfl⟩ : syracuseStep 238139 = 357209) B357209
theorem B107067 : Blo 103782 107067 := bstep (se 1 (by rfl) ⟨80300, by rfl⟩ : syracuseStep 107067 = 160601) B160601
theorem B270935 : Blo 103782 270935 := bstep (se 1 (by rfl) ⟨203201, by rfl⟩ : syracuseStep 270935 = 406403) B406403
theorem B107143 : Blo 103782 107143 := bstep (se 1 (by rfl) ⟨80357, by rfl⟩ : syracuseStep 107143 = 160715) B160715
theorem B107151 : Blo 103782 107151 := bstep (se 1 (by rfl) ⟨80363, by rfl⟩ : syracuseStep 107151 = 160727) B160727
theorem B238265 : Blo 103782 238265 := bstep (se 2 (by rfl) ⟨89349, by rfl⟩ : syracuseStep 238265 = 178699) B178699
theorem B107195 : Blo 103782 107195 := bstep (se 1 (by rfl) ⟨80396, by rfl⟩ : syracuseStep 107195 = 160793) B160793
theorem B107271 : Blo 103782 107271 := bstep (se 1 (by rfl) ⟨80453, by rfl⟩ : syracuseStep 107271 = 160907) B160907
theorem B107279 : Blo 103782 107279 := bstep (se 1 (by rfl) ⟨80459, by rfl⟩ : syracuseStep 107279 = 160919) B160919
theorem B271147 : Blo 103782 271147 := bstep (se 1 (by rfl) ⟨203360, by rfl⟩ : syracuseStep 271147 = 406721) B406721
theorem B107323 : Blo 103782 107323 := bstep (se 1 (by rfl) ⟨80492, by rfl⟩ : syracuseStep 107323 = 160985) B160985
theorem B598873 : Blo 103782 598873 := bstep (se 2 (by rfl) ⟨224577, by rfl⟩ : syracuseStep 598873 = 449155) B449155
theorem B107399 : Blo 103782 107399 := bstep (se 1 (by rfl) ⟨80549, by rfl⟩ : syracuseStep 107399 = 161099) B161099
theorem B107407 : Blo 103782 107407 := bstep (se 1 (by rfl) ⟨80555, by rfl⟩ : syracuseStep 107407 = 161111) B161111
theorem B271289 : Blo 103782 271289 := bstep (se 2 (by rfl) ⟨101733, by rfl⟩ : syracuseStep 271289 = 203467) B203467
theorem B107451 : Blo 103782 107451 := bstep (se 1 (by rfl) ⟨80588, by rfl⟩ : syracuseStep 107451 = 161177) B161177
theorem B861131 : Blo 103782 861131 := bstep (se 1 (by rfl) ⟨645848, by rfl⟩ : syracuseStep 861131 = 1291697) B1291697
theorem B107527 : Blo 103782 107527 := bstep (se 1 (by rfl) ⟨80645, by rfl⟩ : syracuseStep 107527 = 161291) B161291
theorem B238607 : Blo 103782 238607 := bstep (se 1 (by rfl) ⟨178955, by rfl⟩ : syracuseStep 238607 = 357911) B357911
theorem B107535 : Blo 103782 107535 := bstep (se 1 (by rfl) ⟨80651, by rfl⟩ : syracuseStep 107535 = 161303) B161303
theorem B238625 : Blo 103782 238625 := bstep (se 2 (by rfl) ⟨89484, by rfl⟩ : syracuseStep 238625 = 178969) B178969
theorem B107579 : Blo 103782 107579 := bstep (se 1 (by rfl) ⟨80684, by rfl⟩ : syracuseStep 107579 = 161369) B161369
theorem B107655 : Blo 103782 107655 := bstep (se 1 (by rfl) ⟨80741, by rfl⟩ : syracuseStep 107655 = 161483) B161483
theorem B107663 : Blo 103782 107663 := bstep (se 1 (by rfl) ⟨80747, by rfl⟩ : syracuseStep 107663 = 161495) B161495
theorem B107707 : Blo 103782 107707 := bstep (se 1 (by rfl) ⟨80780, by rfl⟩ : syracuseStep 107707 = 161561) B161561
theorem B402803 : Blo 103782 402803 := bstep (se 1 (by rfl) ⟨302102, by rfl⟩ : syracuseStep 402803 = 604205) B604205
theorem B238967 : Blo 103782 238967 := bstep (se 1 (by rfl) ⟨179225, by rfl⟩ : syracuseStep 238967 = 358451) B358451
theorem B239147 : Blo 103782 239147 := bstep (se 1 (by rfl) ⟨179360, by rfl⟩ : syracuseStep 239147 = 358721) B358721
theorem B239507 : Blo 103782 239507 := bstep (se 1 (by rfl) ⟨179630, by rfl⟩ : syracuseStep 239507 = 359261) B359261
theorem B1025945 : Blo 103782 1025945 := bstep (se 2 (by rfl) ⟨384729, by rfl⟩ : syracuseStep 1025945 = 769459) B769459
theorem B272281 : Blo 103782 272281 := bstep (se 2 (by rfl) ⟨102105, by rfl⟩ : syracuseStep 272281 = 204211) B204211
theorem B239561 : Blo 103782 239561 := bstep (se 2 (by rfl) ⟨89835, by rfl⟩ : syracuseStep 239561 = 179671) B179671
theorem B305167 : Blo 103782 305167 := bstep (se 1 (by rfl) ⟨228875, by rfl⟩ : syracuseStep 305167 = 457751) B457751
theorem B272443 : Blo 103782 272443 := bstep (se 1 (by rfl) ⟨204332, by rfl⟩ : syracuseStep 272443 = 408665) B408665
theorem B272585 : Blo 103782 272585 := bstep (se 2 (by rfl) ⟨102219, by rfl⟩ : syracuseStep 272585 = 204439) B204439
theorem B305441 : Blo 103782 305441 := bstep (se 2 (by rfl) ⟨114540, by rfl⟩ : syracuseStep 305441 = 229081) B229081
theorem B600605 : Blo 103782 600605 := bstep (se 3 (by rfl) ⟨112613, by rfl⟩ : syracuseStep 600605 = 225227) B225227
theorem B240263 : Blo 103782 240263 := bstep (se 1 (by rfl) ⟨180197, by rfl⟩ : syracuseStep 240263 = 360395) B360395
theorem B240443 : Blo 103782 240443 := bstep (se 1 (by rfl) ⟨180332, by rfl⟩ : syracuseStep 240443 = 360665) B360665
theorem B240569 : Blo 103782 240569 := bstep (se 2 (by rfl) ⟨90213, by rfl⟩ : syracuseStep 240569 = 180427) B180427
theorem B175223 : Blo 103782 175223 := bstep (se 1 (by rfl) ⟨131417, by rfl⟩ : syracuseStep 175223 = 262835) B262835
theorem B2141315 : Blo 103782 2141315 := bstep (se 1 (by rfl) ⟨1605986, by rfl⟩ : syracuseStep 2141315 = 3211973) B3211973
theorem B765101 : Blo 103782 765101 := bstep (se 3 (by rfl) ⟨143456, by rfl⟩ : syracuseStep 765101 = 286913) B286913
theorem B601289 : Blo 103782 601289 := bstep (se 2 (by rfl) ⟨225483, by rfl⟩ : syracuseStep 601289 = 450967) B450967
theorem B306443 : Blo 103782 306443 := bstep (se 1 (by rfl) ⟨229832, by rfl⟩ : syracuseStep 306443 = 459665) B459665
theorem B240911 : Blo 103782 240911 := bstep (se 1 (by rfl) ⟨180683, by rfl⟩ : syracuseStep 240911 = 361367) B361367
theorem B1191185 : Blo 103782 1191185 := bstep (se 2 (by rfl) ⟨446694, by rfl⟩ : syracuseStep 1191185 = 893389) B893389
theorem B240929 : Blo 103782 240929 := bstep (se 2 (by rfl) ⟨90348, by rfl⟩ : syracuseStep 240929 = 180697) B180697
theorem B798011 : Blo 103782 798011 := bstep (se 1 (by rfl) ⟨598508, by rfl⟩ : syracuseStep 798011 = 1197017) B1197017
theorem B568723 : Blo 103782 568723 := bstep (se 1 (by rfl) ⟨426542, by rfl⟩ : syracuseStep 568723 = 853085) B853085
theorem B404945 : Blo 103782 404945 := bstep (se 2 (by rfl) ⟨151854, by rfl⟩ : syracuseStep 404945 = 303709) B303709
theorem B175675 : Blo 103782 175675 := bstep (se 1 (by rfl) ⟨131756, by rfl⟩ : syracuseStep 175675 = 263513) B263513
theorem B241271 : Blo 103782 241271 := bstep (se 1 (by rfl) ⟨180953, by rfl⟩ : syracuseStep 241271 = 361907) B361907
theorem B306841 : Blo 103782 306841 := bstep (se 2 (by rfl) ⟨115065, by rfl⟩ : syracuseStep 306841 = 230131) B230131
theorem B143035 : Blo 103782 143035 := bstep (se 1 (by rfl) ⟨107276, by rfl⟩ : syracuseStep 143035 = 214553) B214553
theorem B175817 : Blo 103782 175817 := bstep (se 2 (by rfl) ⟨65931, by rfl⟩ : syracuseStep 175817 = 131863) B131863
theorem B405263 : Blo 103782 405263 := bstep (se 1 (by rfl) ⟨303947, by rfl⟩ : syracuseStep 405263 = 607895) B607895
theorem B241451 : Blo 103782 241451 := bstep (se 1 (by rfl) ⟨181088, by rfl⟩ : syracuseStep 241451 = 362177) B362177
theorem B241811 : Blo 103782 241811 := bstep (se 1 (by rfl) ⟨181358, by rfl⟩ : syracuseStep 241811 = 362717) B362717
theorem B241865 : Blo 103782 241865 := bstep (se 2 (by rfl) ⟨90699, by rfl⟩ : syracuseStep 241865 = 181399) B181399
theorem B176519 : Blo 103782 176519 := bstep (se 1 (by rfl) ⟨132389, by rfl⟩ : syracuseStep 176519 = 264779) B264779
theorem B143803 : Blo 103782 143803 := bstep (se 1 (by rfl) ⟨107852, by rfl⟩ : syracuseStep 143803 = 215705) B215705
theorem B307727 : Blo 103782 307727 := bstep (se 1 (by rfl) ⟨230795, by rfl⟩ : syracuseStep 307727 = 461591) B461591
theorem B537281 : Blo 103782 537281 := bstep (se 2 (by rfl) ⟨201480, by rfl⟩ : syracuseStep 537281 = 402961) B402961
theorem B111503 : Blo 103782 111503 := bstep (se 1 (by rfl) ⟨83627, by rfl⟩ : syracuseStep 111503 = 167255) B167255
theorem B603065 : Blo 103782 603065 := bstep (se 2 (by rfl) ⟨226149, by rfl⟩ : syracuseStep 603065 = 452299) B452299
theorem B177167 : Blo 103782 177167 := bstep (se 1 (by rfl) ⟨132875, by rfl⟩ : syracuseStep 177167 = 265751) B265751
theorem B767177 : Blo 103782 767177 := bstep (se 2 (by rfl) ⟨287691, by rfl⟩ : syracuseStep 767177 = 575383) B575383
theorem B341263 : Blo 103782 341263 := bstep (se 1 (by rfl) ⟨255947, by rfl⟩ : syracuseStep 341263 = 511895) B511895
theorem B538001 : Blo 103782 538001 := bstep (se 2 (by rfl) ⟨201750, by rfl⟩ : syracuseStep 538001 = 403501) B403501
theorem B144841 : Blo 103782 144841 := bstep (se 2 (by rfl) ⟨54315, by rfl⟩ : syracuseStep 144841 = 108631) B108631
theorem B177707 : Blo 103782 177707 := bstep (se 1 (by rfl) ⟨133280, by rfl⟩ : syracuseStep 177707 = 266561) B266561
theorem B178105 : Blo 103782 178105 := bstep (se 2 (by rfl) ⟨66789, by rfl⟩ : syracuseStep 178105 = 133579) B133579
theorem B145415 : Blo 103782 145415 := bstep (se 1 (by rfl) ⟨109061, by rfl⟩ : syracuseStep 145415 = 218123) B218123
theorem B112699 : Blo 103782 112699 := bstep (se 1 (by rfl) ⟨84524, by rfl⟩ : syracuseStep 112699 = 169049) B169049
theorem B1194101 : Blo 103782 1194101 := bstep (se 5 (by rfl) ⟨55973, by rfl⟩ : syracuseStep 1194101 = 111947) B111947
theorem B538969 : Blo 103782 538969 := bstep (se 2 (by rfl) ⟨202113, by rfl⟩ : syracuseStep 538969 = 404227) B404227
theorem B4143581 : Blo 103782 4143581 := bstep (se 3 (by rfl) ⟨776921, by rfl⟩ : syracuseStep 4143581 = 1553843) B1553843
theorem B178807 : Blo 103782 178807 := bstep (se 1 (by rfl) ⟨134105, by rfl⟩ : syracuseStep 178807 = 268211) B268211
theorem B1784591 : Blo 103782 1784591 := bstep (se 1 (by rfl) ⟨1338443, by rfl⟩ : syracuseStep 1784591 = 2676887) B2676887
theorem B604979 : Blo 103782 604979 := bstep (se 1 (by rfl) ⟨453734, by rfl⟩ : syracuseStep 604979 = 907469) B907469
theorem B179003 : Blo 103782 179003 := bstep (se 1 (by rfl) ⟨134252, by rfl⟩ : syracuseStep 179003 = 268505) B268505
theorem B1227635 : Blo 103782 1227635 := bstep (se 1 (by rfl) ⟨920726, by rfl⟩ : syracuseStep 1227635 = 1841453) B1841453
theorem B1162187 : Blo 103782 1162187 := bstep (se 1 (by rfl) ⟨871640, by rfl⟩ : syracuseStep 1162187 = 1743281) B1743281
theorem B310315 : Blo 103782 310315 := bstep (se 1 (by rfl) ⟨232736, by rfl⟩ : syracuseStep 310315 = 465473) B465473
theorem B179401 : Blo 103782 179401 := bstep (se 2 (by rfl) ⟨67275, by rfl⟩ : syracuseStep 179401 = 134551) B134551
theorem B408833 : Blo 103782 408833 := bstep (se 2 (by rfl) ⟨153312, by rfl⟩ : syracuseStep 408833 = 306625) B306625
theorem B408847 : Blo 103782 408847 := bstep (se 1 (by rfl) ⟨306635, by rfl⟩ : syracuseStep 408847 = 613271) B613271
theorem B867617 : Blo 103782 867617 := bstep (se 2 (by rfl) ⟨325356, by rfl⟩ : syracuseStep 867617 = 650713) B650713
theorem B376123 : Blo 103782 376123 := bstep (se 1 (by rfl) ⟨282092, by rfl⟩ : syracuseStep 376123 = 564185) B564185
theorem B900497 : Blo 103782 900497 := bstep (se 2 (by rfl) ⟨337686, by rfl⟩ : syracuseStep 900497 = 675373) B675373
theorem B540107 : Blo 103782 540107 := bstep (se 1 (by rfl) ⟨405080, by rfl⟩ : syracuseStep 540107 = 810161) B810161
theorem B540431 : Blo 103782 540431 := bstep (se 1 (by rfl) ⟨405323, by rfl⟩ : syracuseStep 540431 = 810647) B810647
theorem B180103 : Blo 103782 180103 := bstep (se 1 (by rfl) ⟨135077, by rfl⟩ : syracuseStep 180103 = 270155) B270155
theorem B1359767 : Blo 103782 1359767 := bstep (se 1 (by rfl) ⟨1019825, by rfl⟩ : syracuseStep 1359767 = 2039651) B2039651
theorem B769945 : Blo 103782 769945 := bstep (se 2 (by rfl) ⟨288729, by rfl⟩ : syracuseStep 769945 = 577459) B577459
theorem B606437 : Blo 103782 606437 := bstep (se 4 (by rfl) ⟨56853, by rfl⟩ : syracuseStep 606437 = 113707) B113707
theorem B967133 : Blo 103782 967133 := bstep (se 3 (by rfl) ⟨181337, by rfl⟩ : syracuseStep 967133 = 362675) B362675
theorem B180751 : Blo 103782 180751 := bstep (se 1 (by rfl) ⟨135563, by rfl⟩ : syracuseStep 180751 = 271127) B271127
theorem B803357 : Blo 103782 803357 := bstep (se 3 (by rfl) ⟨150629, by rfl⟩ : syracuseStep 803357 = 301259) B301259
theorem B672299 : Blo 103782 672299 := bstep (se 1 (by rfl) ⟨504224, by rfl⟩ : syracuseStep 672299 = 1008449) B1008449
theorem B213563 : Blo 103782 213563 := bstep (se 1 (by rfl) ⟨160172, by rfl⟩ : syracuseStep 213563 = 320345) B320345
theorem B3261221 : Blo 103782 3261221 := bstep (se 4 (by rfl) ⟨305739, by rfl⟩ : syracuseStep 3261221 = 611479) B611479
theorem B770867 : Blo 103782 770867 := bstep (se 1 (by rfl) ⟨578150, by rfl⟩ : syracuseStep 770867 = 1156301) B1156301
theorem B607121 : Blo 103782 607121 := bstep (se 2 (by rfl) ⟨227670, by rfl⟩ : syracuseStep 607121 = 455341) B455341
theorem B115727 : Blo 103782 115727 := bstep (se 1 (by rfl) ⟨86795, by rfl⟩ : syracuseStep 115727 = 173591) B173591
theorem B181291 : Blo 103782 181291 := bstep (se 1 (by rfl) ⟨135968, by rfl⟩ : syracuseStep 181291 = 271937) B271937
theorem B181433 : Blo 103782 181433 := bstep (se 2 (by rfl) ⟨68037, by rfl⟩ : syracuseStep 181433 = 136075) B136075
theorem B541889 : Blo 103782 541889 := bstep (se 2 (by rfl) ⟨203208, by rfl⟩ : syracuseStep 541889 = 406417) B406417
theorem B476417 : Blo 103782 476417 := bstep (se 2 (by rfl) ⟨178656, by rfl⟩ : syracuseStep 476417 = 357313) B357313
theorem B443663 : Blo 103782 443663 := bstep (se 1 (by rfl) ⟨332747, by rfl⟩ : syracuseStep 443663 = 665495) B665495
theorem B1230173 : Blo 103782 1230173 := bstep (se 3 (by rfl) ⟨230657, by rfl⟩ : syracuseStep 1230173 = 461315) B461315
theorem B706051 : Blo 103782 706051 := bstep (se 1 (by rfl) ⟨529538, by rfl⟩ : syracuseStep 706051 = 1059077) B1059077
theorem B181775 : Blo 103782 181775 := bstep (se 1 (by rfl) ⟨136331, by rfl⟩ : syracuseStep 181775 = 272663) B272663
theorem B149035 : Blo 103782 149035 := bstep (se 1 (by rfl) ⟨111776, by rfl⟩ : syracuseStep 149035 = 223553) B223553
theorem B1558115 : Blo 103782 1558115 := bstep (se 1 (by rfl) ⟨1168586, by rfl⟩ : syracuseStep 1558115 = 2337173) B2337173
theorem B608147 : Blo 103782 608147 := bstep (se 1 (by rfl) ⟨456110, by rfl⟩ : syracuseStep 608147 = 912221) B912221
theorem B1099909 : Blo 103782 1099909 := bstep (se 4 (by rfl) ⟨103116, by rfl⟩ : syracuseStep 1099909 = 206233) B206233
theorem B116923 : Blo 103782 116923 := bstep (se 1 (by rfl) ⟨87692, by rfl⟩ : syracuseStep 116923 = 175385) B175385
theorem B281033 : Blo 103782 281033 := bstep (se 2 (by rfl) ⟨105387, by rfl⟩ : syracuseStep 281033 = 210775) B210775
theorem B543185 : Blo 103782 543185 := bstep (se 2 (by rfl) ⟨203694, by rfl⟩ : syracuseStep 543185 = 407389) B407389
theorem B117391 : Blo 103782 117391 := bstep (se 1 (by rfl) ⟨88043, by rfl⟩ : syracuseStep 117391 = 176087) B176087
theorem B1231553 : Blo 103782 1231553 := bstep (se 2 (by rfl) ⟨461832, by rfl⟩ : syracuseStep 1231553 = 923665) B923665
theorem B576229 : Blo 103782 576229 := bstep (se 4 (by rfl) ⟨54021, by rfl⟩ : syracuseStep 576229 = 108043) B108043
theorem B281377 : Blo 103782 281377 := bstep (se 2 (by rfl) ⟨105516, by rfl⟩ : syracuseStep 281377 = 211033) B211033
theorem B805949 : Blo 103782 805949 := bstep (se 3 (by rfl) ⟨151115, by rfl⟩ : syracuseStep 805949 = 302231) B302231
theorem B117895 : Blo 103782 117895 := bstep (se 1 (by rfl) ⟨88421, by rfl⟩ : syracuseStep 117895 = 176843) B176843
theorem B118075 : Blo 103782 118075 := bstep (se 1 (by rfl) ⟨88556, by rfl⟩ : syracuseStep 118075 = 177113) B177113
theorem B1134157 : Blo 103782 1134157 := bstep (se 3 (by rfl) ⟨212654, by rfl⟩ : syracuseStep 1134157 = 425309) B425309
theorem B118543 : Blo 103782 118543 := bstep (se 1 (by rfl) ⟨88907, by rfl⟩ : syracuseStep 118543 = 177815) B177815
theorem B380705 : Blo 103782 380705 := bstep (se 2 (by rfl) ⟨142764, by rfl⟩ : syracuseStep 380705 = 285529) B285529
theorem B282503 : Blo 103782 282503 := bstep (se 1 (by rfl) ⟨211877, by rfl⟩ : syracuseStep 282503 = 423755) B423755
theorem B151723 : Blo 103782 151723 := bstep (se 1 (by rfl) ⟨113792, by rfl⟩ : syracuseStep 151723 = 227585) B227585
theorem B119047 : Blo 103782 119047 := bstep (se 1 (by rfl) ⟨89285, by rfl⟩ : syracuseStep 119047 = 178571) B178571
theorem B151951 : Blo 103782 151951 := bstep (se 1 (by rfl) ⟨113963, by rfl⟩ : syracuseStep 151951 = 227927) B227927
theorem B446867 : Blo 103782 446867 := bstep (se 1 (by rfl) ⟨335150, by rfl⟩ : syracuseStep 446867 = 670301) B670301
theorem B119227 : Blo 103782 119227 := bstep (se 1 (by rfl) ⟨89420, by rfl⟩ : syracuseStep 119227 = 178841) B178841
theorem B545291 : Blo 103782 545291 := bstep (se 1 (by rfl) ⟨408968, by rfl⟩ : syracuseStep 545291 = 817937) B817937
theorem B545453 : Blo 103782 545453 := bstep (se 3 (by rfl) ⟨102272, by rfl⟩ : syracuseStep 545453 = 204545) B204545
theorem B152327 : Blo 103782 152327 := bstep (se 1 (by rfl) ⟨114245, by rfl⟩ : syracuseStep 152327 = 228491) B228491
theorem B807731 : Blo 103782 807731 := bstep (se 1 (by rfl) ⟨605798, by rfl⟩ : syracuseStep 807731 = 1211597) B1211597
theorem B119695 : Blo 103782 119695 := bstep (se 1 (by rfl) ⟨89771, by rfl⟩ : syracuseStep 119695 = 179543) B179543
theorem B251027 : Blo 103782 251027 := bstep (se 1 (by rfl) ⟨188270, by rfl⟩ : syracuseStep 251027 = 376541) B376541
theorem B120199 : Blo 103782 120199 := bstep (se 1 (by rfl) ⟨90149, by rfl⟩ : syracuseStep 120199 = 180299) B180299
theorem B120379 : Blo 103782 120379 := bstep (se 1 (by rfl) ⟨90284, by rfl⟩ : syracuseStep 120379 = 180569) B180569
theorem B677605 : Blo 103782 677605 := bstep (se 4 (by rfl) ⟨63525, by rfl⟩ : syracuseStep 677605 = 127051) B127051
theorem B284687 : Blo 103782 284687 := bstep (se 1 (by rfl) ⟨213515, by rfl⟩ : syracuseStep 284687 = 427031) B427031
theorem B120847 : Blo 103782 120847 := bstep (se 1 (by rfl) ⟨90635, by rfl⟩ : syracuseStep 120847 = 181271) B181271
theorem B448541 : Blo 103782 448541 := bstep (se 3 (by rfl) ⟨84101, by rfl⟩ : syracuseStep 448541 = 168203) B168203
theorem B678289 : Blo 103782 678289 := bstep (se 2 (by rfl) ⟨254358, by rfl⟩ : syracuseStep 678289 = 508717) B508717
theorem B514451 : Blo 103782 514451 := bstep (se 1 (by rfl) ⟨385838, by rfl⟩ : syracuseStep 514451 = 771677) B771677
theorem B481879 : Blo 103782 481879 := bstep (se 1 (by rfl) ⟨361409, by rfl⟩ : syracuseStep 481879 = 722819) B722819
theorem B449225 : Blo 103782 449225 := bstep (se 2 (by rfl) ⟨168459, by rfl⟩ : syracuseStep 449225 = 336919) B336919
theorem B351161 : Blo 103782 351161 := bstep (se 2 (by rfl) ⟨131685, by rfl⟩ : syracuseStep 351161 = 263371) B263371
theorem B121991 : Blo 103782 121991 := bstep (se 1 (by rfl) ⟨91493, by rfl⟩ : syracuseStep 121991 = 182987) B182987
theorem B1793339 : Blo 103782 1793339 := bstep (se 1 (by rfl) ⟨1345004, by rfl⟩ : syracuseStep 1793339 = 2690009) B2690009
theorem B351755 : Blo 103782 351755 := bstep (se 1 (by rfl) ⟨263816, by rfl⟩ : syracuseStep 351755 = 527633) B527633
theorem B351863 : Blo 103782 351863 := bstep (se 1 (by rfl) ⟨263897, by rfl⟩ : syracuseStep 351863 = 527795) B527795
theorem B155705 : Blo 103782 155705 := bstep (se 2 (by rfl) ⟨58389, by rfl⟩ : syracuseStep 155705 = 116779) B116779
theorem B155783 : Blo 103782 155783 := bstep (se 1 (by rfl) ⟨116837, by rfl⟩ : syracuseStep 155783 = 233675) B233675
theorem B155819 : Blo 103782 155819 := bstep (se 1 (by rfl) ⟨116864, by rfl⟩ : syracuseStep 155819 = 233729) B233729
theorem B155849 : Blo 103782 155849 := bstep (se 2 (by rfl) ⟨58443, by rfl⟩ : syracuseStep 155849 = 116887) B116887
theorem B352457 : Blo 103782 352457 := bstep (se 2 (by rfl) ⟨132171, by rfl⟩ : syracuseStep 352457 = 264343) B264343
theorem B155963 : Blo 103782 155963 := bstep (se 1 (by rfl) ⟨116972, by rfl⟩ : syracuseStep 155963 = 233945) B233945
theorem B156023 : Blo 103782 156023 := bstep (se 1 (by rfl) ⟨117017, by rfl⟩ : syracuseStep 156023 = 234035) B234035
theorem B156047 : Blo 103782 156047 := bstep (se 1 (by rfl) ⟨117035, by rfl⟩ : syracuseStep 156047 = 234071) B234071
theorem B156089 : Blo 103782 156089 := bstep (se 2 (by rfl) ⟨58533, by rfl⟩ : syracuseStep 156089 = 117067) B117067
theorem B451001 : Blo 103782 451001 := bstep (se 2 (by rfl) ⟨169125, by rfl⟩ : syracuseStep 451001 = 338251) B338251
theorem B156167 : Blo 103782 156167 := bstep (se 1 (by rfl) ⟨117125, by rfl⟩ : syracuseStep 156167 = 234251) B234251
theorem B156203 : Blo 103782 156203 := bstep (se 1 (by rfl) ⟨117152, by rfl⟩ : syracuseStep 156203 = 234305) B234305
theorem B156233 : Blo 103782 156233 := bstep (se 2 (by rfl) ⟨58587, by rfl⟩ : syracuseStep 156233 = 117175) B117175
theorem B287347 : Blo 103782 287347 := bstep (se 1 (by rfl) ⟨215510, by rfl⟩ : syracuseStep 287347 = 431021) B431021
theorem B254611 : Blo 103782 254611 := bstep (se 1 (by rfl) ⟨190958, by rfl⟩ : syracuseStep 254611 = 381917) B381917
theorem B189113 : Blo 103782 189113 := bstep (se 2 (by rfl) ⟨70917, by rfl⟩ : syracuseStep 189113 = 141835) B141835
theorem B156347 : Blo 103782 156347 := bstep (se 1 (by rfl) ⟨117260, by rfl⟩ : syracuseStep 156347 = 234521) B234521
theorem B156407 : Blo 103782 156407 := bstep (se 1 (by rfl) ⟨117305, by rfl⟩ : syracuseStep 156407 = 234611) B234611
theorem B156431 : Blo 103782 156431 := bstep (se 1 (by rfl) ⟨117323, by rfl⟩ : syracuseStep 156431 = 234647) B234647
theorem B156473 : Blo 103782 156473 := bstep (se 2 (by rfl) ⟨58677, by rfl⟩ : syracuseStep 156473 = 117355) B117355
theorem B156551 : Blo 103782 156551 := bstep (se 1 (by rfl) ⟨117413, by rfl⟩ : syracuseStep 156551 = 234827) B234827
theorem B353159 : Blo 103782 353159 := bstep (se 1 (by rfl) ⟨264869, by rfl⟩ : syracuseStep 353159 = 529739) B529739
theorem B156587 : Blo 103782 156587 := bstep (se 1 (by rfl) ⟨117440, by rfl⟩ : syracuseStep 156587 = 234881) B234881
theorem B156617 : Blo 103782 156617 := bstep (se 2 (by rfl) ⟨58731, by rfl⟩ : syracuseStep 156617 = 117463) B117463
theorem B156731 : Blo 103782 156731 := bstep (se 1 (by rfl) ⟨117548, by rfl⟩ : syracuseStep 156731 = 235097) B235097
theorem B156791 : Blo 103782 156791 := bstep (se 1 (by rfl) ⟨117593, by rfl⟩ : syracuseStep 156791 = 235187) B235187
theorem B156815 : Blo 103782 156815 := bstep (se 1 (by rfl) ⟨117611, by rfl⟩ : syracuseStep 156815 = 235223) B235223
theorem B156857 : Blo 103782 156857 := bstep (se 2 (by rfl) ⟨58821, by rfl⟩ : syracuseStep 156857 = 117643) B117643
theorem B353537 : Blo 103782 353537 := bstep (se 2 (by rfl) ⟨132576, by rfl⟩ : syracuseStep 353537 = 265153) B265153
theorem B156935 : Blo 103782 156935 := bstep (se 1 (by rfl) ⟨117701, by rfl⟩ : syracuseStep 156935 = 235403) B235403
theorem B156971 : Blo 103782 156971 := bstep (se 1 (by rfl) ⟨117728, by rfl⟩ : syracuseStep 156971 = 235457) B235457
theorem B157001 : Blo 103782 157001 := bstep (se 2 (by rfl) ⟨58875, by rfl⟩ : syracuseStep 157001 = 117751) B117751
theorem B157115 : Blo 103782 157115 := bstep (se 1 (by rfl) ⟨117836, by rfl⟩ : syracuseStep 157115 = 235673) B235673
theorem B157175 : Blo 103782 157175 := bstep (se 1 (by rfl) ⟨117881, by rfl⟩ : syracuseStep 157175 = 235763) B235763
theorem B157199 : Blo 103782 157199 := bstep (se 1 (by rfl) ⟨117899, by rfl⟩ : syracuseStep 157199 = 235799) B235799
theorem B157241 : Blo 103782 157241 := bstep (se 2 (by rfl) ⟨58965, by rfl⟩ : syracuseStep 157241 = 117931) B117931
theorem B157319 : Blo 103782 157319 := bstep (se 1 (by rfl) ⟨117989, by rfl⟩ : syracuseStep 157319 = 235979) B235979
theorem B157355 : Blo 103782 157355 := bstep (se 1 (by rfl) ⟨118016, by rfl⟩ : syracuseStep 157355 = 236033) B236033
theorem B157385 : Blo 103782 157385 := bstep (se 2 (by rfl) ⟨59019, by rfl⟩ : syracuseStep 157385 = 118039) B118039
theorem B386849 : Blo 103782 386849 := bstep (se 2 (by rfl) ⟨145068, by rfl⟩ : syracuseStep 386849 = 290137) B290137
theorem B157499 : Blo 103782 157499 := bstep (se 1 (by rfl) ⟨118124, by rfl⟩ : syracuseStep 157499 = 236249) B236249
theorem B157559 : Blo 103782 157559 := bstep (se 1 (by rfl) ⟨118169, by rfl⟩ : syracuseStep 157559 = 236339) B236339
theorem B157583 : Blo 103782 157583 := bstep (se 1 (by rfl) ⟨118187, by rfl⟩ : syracuseStep 157583 = 236375) B236375
theorem B157625 : Blo 103782 157625 := bstep (se 2 (by rfl) ⟨59109, by rfl⟩ : syracuseStep 157625 = 118219) B118219
theorem B223177 : Blo 103782 223177 := bstep (se 2 (by rfl) ⟨83691, by rfl⟩ : syracuseStep 223177 = 167383) B167383
theorem B157703 : Blo 103782 157703 := bstep (se 1 (by rfl) ⟨118277, by rfl⟩ : syracuseStep 157703 = 236555) B236555
theorem B354347 : Blo 103782 354347 := bstep (se 1 (by rfl) ⟨265760, by rfl⟩ : syracuseStep 354347 = 531521) B531521
theorem B157739 : Blo 103782 157739 := bstep (se 1 (by rfl) ⟨118304, by rfl⟩ : syracuseStep 157739 = 236609) B236609
theorem B157769 : Blo 103782 157769 := bstep (se 2 (by rfl) ⟨59163, by rfl⟩ : syracuseStep 157769 = 118327) B118327
theorem B157883 : Blo 103782 157883 := bstep (se 1 (by rfl) ⟨118412, by rfl⟩ : syracuseStep 157883 = 236825) B236825
theorem B157943 : Blo 103782 157943 := bstep (se 1 (by rfl) ⟨118457, by rfl⟩ : syracuseStep 157943 = 236915) B236915
theorem B157967 : Blo 103782 157967 := bstep (se 1 (by rfl) ⟨118475, by rfl⟩ : syracuseStep 157967 = 236951) B236951
theorem B1108241 : Blo 103782 1108241 := bstep (se 2 (by rfl) ⟨415590, by rfl⟩ : syracuseStep 1108241 = 831181) B831181
theorem B158009 : Blo 103782 158009 := bstep (se 2 (by rfl) ⟨59253, by rfl⟩ : syracuseStep 158009 = 118507) B118507
theorem B158087 : Blo 103782 158087 := bstep (se 1 (by rfl) ⟨118565, by rfl⟩ : syracuseStep 158087 = 237131) B237131
theorem B158123 : Blo 103782 158123 := bstep (se 1 (by rfl) ⟨118592, by rfl⟩ : syracuseStep 158123 = 237185) B237185
theorem B616889 : Blo 103782 616889 := bstep (se 2 (by rfl) ⟨231333, by rfl⟩ : syracuseStep 616889 = 462667) B462667
theorem B158153 : Blo 103782 158153 := bstep (se 2 (by rfl) ⟨59307, by rfl⟩ : syracuseStep 158153 = 118615) B118615
theorem B158267 : Blo 103782 158267 := bstep (se 1 (by rfl) ⟨118700, by rfl⟩ : syracuseStep 158267 = 237401) B237401
theorem B158327 : Blo 103782 158327 := bstep (se 1 (by rfl) ⟨118745, by rfl⟩ : syracuseStep 158327 = 237491) B237491
theorem B158351 : Blo 103782 158351 := bstep (se 1 (by rfl) ⟨118763, by rfl⟩ : syracuseStep 158351 = 237527) B237527
theorem B158393 : Blo 103782 158393 := bstep (se 2 (by rfl) ⟨59397, by rfl⟩ : syracuseStep 158393 = 118795) B118795
theorem B453377 : Blo 103782 453377 := bstep (se 2 (by rfl) ⟨170016, by rfl⟩ : syracuseStep 453377 = 340033) B340033
theorem B158471 : Blo 103782 158471 := bstep (se 1 (by rfl) ⟨118853, by rfl⟩ : syracuseStep 158471 = 237707) B237707
theorem B256801 : Blo 103782 256801 := bstep (se 2 (by rfl) ⟨96300, by rfl⟩ : syracuseStep 256801 = 192601) B192601
theorem B158507 : Blo 103782 158507 := bstep (se 1 (by rfl) ⟨118880, by rfl⟩ : syracuseStep 158507 = 237761) B237761
theorem B158537 : Blo 103782 158537 := bstep (se 2 (by rfl) ⟨59451, by rfl⟩ : syracuseStep 158537 = 118903) B118903
theorem B453529 : Blo 103782 453529 := bstep (se 2 (by rfl) ⟨170073, by rfl⟩ : syracuseStep 453529 = 340147) B340147
theorem B158651 : Blo 103782 158651 := bstep (se 1 (by rfl) ⟨118988, by rfl⟩ : syracuseStep 158651 = 237977) B237977
theorem B158711 : Blo 103782 158711 := bstep (se 1 (by rfl) ⟨119033, by rfl⟩ : syracuseStep 158711 = 238067) B238067
theorem B158735 : Blo 103782 158735 := bstep (se 1 (by rfl) ⟨119051, by rfl⟩ : syracuseStep 158735 = 238103) B238103
theorem B158777 : Blo 103782 158777 := bstep (se 2 (by rfl) ⟨59541, by rfl⟩ : syracuseStep 158777 = 119083) B119083
theorem B158855 : Blo 103782 158855 := bstep (se 1 (by rfl) ⟨119141, by rfl⟩ : syracuseStep 158855 = 238283) B238283
theorem B158891 : Blo 103782 158891 := bstep (se 1 (by rfl) ⟨119168, by rfl⟩ : syracuseStep 158891 = 238337) B238337
theorem B158921 : Blo 103782 158921 := bstep (se 2 (by rfl) ⟨59595, by rfl⟩ : syracuseStep 158921 = 119191) B119191
theorem B224527 : Blo 103782 224527 := bstep (se 1 (by rfl) ⟨168395, by rfl⟩ : syracuseStep 224527 = 336791) B336791
theorem B355643 : Blo 103782 355643 := bstep (se 1 (by rfl) ⟨266732, by rfl⟩ : syracuseStep 355643 = 533465) B533465
theorem B159035 : Blo 103782 159035 := bstep (se 1 (by rfl) ⟨119276, by rfl⟩ : syracuseStep 159035 = 238553) B238553
theorem B159095 : Blo 103782 159095 := bstep (se 1 (by rfl) ⟨119321, by rfl⟩ : syracuseStep 159095 = 238643) B238643
theorem B159119 : Blo 103782 159119 := bstep (se 1 (by rfl) ⟨119339, by rfl⟩ : syracuseStep 159119 = 238679) B238679
theorem B159161 : Blo 103782 159161 := bstep (se 2 (by rfl) ⟨59685, by rfl⟩ : syracuseStep 159161 = 119371) B119371
theorem B159239 : Blo 103782 159239 := bstep (se 1 (by rfl) ⟨119429, by rfl⟩ : syracuseStep 159239 = 238859) B238859
theorem B224783 : Blo 103782 224783 := bstep (se 1 (by rfl) ⟨168587, by rfl⟩ : syracuseStep 224783 = 337175) B337175
theorem B126479 : Blo 103782 126479 := bstep (se 1 (by rfl) ⟨94859, by rfl⟩ : syracuseStep 126479 = 189719) B189719
theorem B159275 : Blo 103782 159275 := bstep (se 1 (by rfl) ⟨119456, by rfl⟩ : syracuseStep 159275 = 238913) B238913
theorem B159305 : Blo 103782 159305 := bstep (se 2 (by rfl) ⟨59739, by rfl⟩ : syracuseStep 159305 = 119479) B119479
theorem B159419 : Blo 103782 159419 := bstep (se 1 (by rfl) ⟨119564, by rfl⟩ : syracuseStep 159419 = 239129) B239129
theorem B421613 : Blo 103782 421613 := bstep (se 3 (by rfl) ⟨79052, by rfl⟩ : syracuseStep 421613 = 158105) B158105
theorem B159479 : Blo 103782 159479 := bstep (se 1 (by rfl) ⟨119609, by rfl⟩ : syracuseStep 159479 = 239219) B239219
theorem B159503 : Blo 103782 159503 := bstep (se 1 (by rfl) ⟨119627, by rfl⟩ : syracuseStep 159503 = 239255) B239255
theorem B356129 : Blo 103782 356129 := bstep (se 2 (by rfl) ⟨133548, by rfl⟩ : syracuseStep 356129 = 267097) B267097
theorem B4321073 : Blo 103782 4321073 := bstep (se 2 (by rfl) ⟨1620402, by rfl⟩ : syracuseStep 4321073 = 3240805) B3240805
theorem B159545 : Blo 103782 159545 := bstep (se 2 (by rfl) ⟨59829, by rfl⟩ : syracuseStep 159545 = 119659) B119659
theorem B257879 : Blo 103782 257879 := bstep (se 1 (by rfl) ⟨193409, by rfl⟩ : syracuseStep 257879 = 386819) B386819
theorem B356231 : Blo 103782 356231 := bstep (se 1 (by rfl) ⟨267173, by rfl⟩ : syracuseStep 356231 = 534347) B534347
theorem B159623 : Blo 103782 159623 := bstep (se 1 (by rfl) ⟨119717, by rfl⟩ : syracuseStep 159623 = 239435) B239435
theorem B159659 : Blo 103782 159659 := bstep (se 1 (by rfl) ⟨119744, by rfl⟩ : syracuseStep 159659 = 239489) B239489
theorem B159689 : Blo 103782 159689 := bstep (se 2 (by rfl) ⟨59883, by rfl⟩ : syracuseStep 159689 = 119767) B119767
theorem B421841 : Blo 103782 421841 := bstep (se 2 (by rfl) ⟨158190, by rfl⟩ : syracuseStep 421841 = 316381) B316381
theorem B1339415 : Blo 103782 1339415 := bstep (se 1 (by rfl) ⟨1004561, by rfl⟩ : syracuseStep 1339415 = 2009123) B2009123
theorem B5304365 : Blo 103782 5304365 := bstep (se 3 (by rfl) ⟨994568, by rfl⟩ : syracuseStep 5304365 = 1989137) B1989137
theorem B159803 : Blo 103782 159803 := bstep (se 1 (by rfl) ⟨119852, by rfl⟩ : syracuseStep 159803 = 239705) B239705
theorem B5009501 : Blo 103782 5009501 := bstep (se 3 (by rfl) ⟨939281, by rfl⟩ : syracuseStep 5009501 = 1878563) B1878563
theorem B159863 : Blo 103782 159863 := bstep (se 1 (by rfl) ⟨119897, by rfl⟩ : syracuseStep 159863 = 239795) B239795
theorem B159887 : Blo 103782 159887 := bstep (se 1 (by rfl) ⟨119915, by rfl⟩ : syracuseStep 159887 = 239831) B239831
theorem B159929 : Blo 103782 159929 := bstep (se 2 (by rfl) ⟨59973, by rfl⟩ : syracuseStep 159929 = 119947) B119947
theorem B160007 : Blo 103782 160007 := bstep (se 1 (by rfl) ⟨120005, by rfl⟩ : syracuseStep 160007 = 240011) B240011
theorem B160043 : Blo 103782 160043 := bstep (se 1 (by rfl) ⟨120032, by rfl⟩ : syracuseStep 160043 = 240065) B240065
theorem B225595 : Blo 103782 225595 := bstep (se 1 (by rfl) ⟨169196, by rfl⟩ : syracuseStep 225595 = 338393) B338393
theorem B160073 : Blo 103782 160073 := bstep (se 2 (by rfl) ⟨60027, by rfl⟩ : syracuseStep 160073 = 120055) B120055
theorem B356723 : Blo 103782 356723 := bstep (se 1 (by rfl) ⟨267542, by rfl⟩ : syracuseStep 356723 = 535085) B535085
theorem B225671 : Blo 103782 225671 := bstep (se 1 (by rfl) ⟨169253, by rfl⟩ : syracuseStep 225671 = 338507) B338507
theorem B815507 : Blo 103782 815507 := bstep (se 1 (by rfl) ⟨611630, by rfl⟩ : syracuseStep 815507 = 1223261) B1223261
theorem B160187 : Blo 103782 160187 := bstep (se 1 (by rfl) ⟨120140, by rfl⟩ : syracuseStep 160187 = 240281) B240281
theorem B160247 : Blo 103782 160247 := bstep (se 1 (by rfl) ⟨120185, by rfl⟩ : syracuseStep 160247 = 240371) B240371
theorem B160271 : Blo 103782 160271 := bstep (se 1 (by rfl) ⟨120203, by rfl⟩ : syracuseStep 160271 = 240407) B240407
theorem B979499 : Blo 103782 979499 := bstep (se 1 (by rfl) ⟨734624, by rfl⟩ : syracuseStep 979499 = 1469249) B1469249
theorem B160313 : Blo 103782 160313 := bstep (se 2 (by rfl) ⟨60117, by rfl⟩ : syracuseStep 160313 = 120235) B120235
theorem B258647 : Blo 103782 258647 := bstep (se 1 (by rfl) ⟨193985, by rfl⟩ : syracuseStep 258647 = 387971) B387971
theorem B225911 : Blo 103782 225911 := bstep (se 1 (by rfl) ⟨169433, by rfl⟩ : syracuseStep 225911 = 338867) B338867
theorem B160391 : Blo 103782 160391 := bstep (se 1 (by rfl) ⟨120293, by rfl⟩ : syracuseStep 160391 = 240587) B240587
theorem B160427 : Blo 103782 160427 := bstep (se 1 (by rfl) ⟨120320, by rfl⟩ : syracuseStep 160427 = 240641) B240641
theorem B160457 : Blo 103782 160457 := bstep (se 2 (by rfl) ⟨60171, by rfl⟩ : syracuseStep 160457 = 120343) B120343
theorem B651977 : Blo 103782 651977 := bstep (se 2 (by rfl) ⟨244491, by rfl⟩ : syracuseStep 651977 = 488983) B488983
theorem B1372889 : Blo 103782 1372889 := bstep (se 2 (by rfl) ⟨514833, by rfl⟩ : syracuseStep 1372889 = 1029667) B1029667
theorem B226081 : Blo 103782 226081 := bstep (se 2 (by rfl) ⟨84780, by rfl⟩ : syracuseStep 226081 = 169561) B169561
theorem B848677 : Blo 103782 848677 := bstep (se 4 (by rfl) ⟨79563, by rfl⟩ : syracuseStep 848677 = 159127) B159127
theorem B160571 : Blo 103782 160571 := bstep (se 1 (by rfl) ⟨120428, by rfl⟩ : syracuseStep 160571 = 240857) B240857
theorem B160631 : Blo 103782 160631 := bstep (se 1 (by rfl) ⟨120473, by rfl⟩ : syracuseStep 160631 = 240947) B240947
theorem B160655 : Blo 103782 160655 := bstep (se 1 (by rfl) ⟨120491, by rfl⟩ : syracuseStep 160655 = 240983) B240983
theorem B160697 : Blo 103782 160697 := bstep (se 2 (by rfl) ⟨60261, by rfl⟩ : syracuseStep 160697 = 120523) B120523
theorem B685003 : Blo 103782 685003 := bstep (se 1 (by rfl) ⟨513752, by rfl⟩ : syracuseStep 685003 = 1027505) B1027505
theorem B160775 : Blo 103782 160775 := bstep (se 1 (by rfl) ⟨120581, by rfl⟩ : syracuseStep 160775 = 241163) B241163
theorem B160811 : Blo 103782 160811 := bstep (se 1 (by rfl) ⟨120608, by rfl⟩ : syracuseStep 160811 = 241217) B241217
theorem B160841 : Blo 103782 160841 := bstep (se 2 (by rfl) ⟨60315, by rfl⟩ : syracuseStep 160841 = 120631) B120631
theorem B226423 : Blo 103782 226423 := bstep (se 1 (by rfl) ⟨169817, by rfl⟩ : syracuseStep 226423 = 339635) B339635
theorem B160955 : Blo 103782 160955 := bstep (se 1 (by rfl) ⟨120716, by rfl⟩ : syracuseStep 160955 = 241433) B241433
theorem B161015 : Blo 103782 161015 := bstep (se 1 (by rfl) ⟨120761, by rfl⟩ : syracuseStep 161015 = 241523) B241523
theorem B161039 : Blo 103782 161039 := bstep (se 1 (by rfl) ⟨120779, by rfl⟩ : syracuseStep 161039 = 241559) B241559
theorem B161081 : Blo 103782 161081 := bstep (se 2 (by rfl) ⟨60405, by rfl⟩ : syracuseStep 161081 = 120811) B120811
theorem B1209659 : Blo 103782 1209659 := bstep (se 1 (by rfl) ⟨907244, by rfl⟩ : syracuseStep 1209659 = 1814489) B1814489
theorem B161159 : Blo 103782 161159 := bstep (se 1 (by rfl) ⟨120869, by rfl⟩ : syracuseStep 161159 = 241739) B241739
theorem B161195 : Blo 103782 161195 := bstep (se 1 (by rfl) ⟨120896, by rfl⟩ : syracuseStep 161195 = 241793) B241793
theorem B161225 : Blo 103782 161225 := bstep (se 2 (by rfl) ⟨60459, by rfl⟩ : syracuseStep 161225 = 120919) B120919
theorem B161339 : Blo 103782 161339 := bstep (se 1 (by rfl) ⟨121004, by rfl⟩ : syracuseStep 161339 = 242009) B242009
theorem B161399 : Blo 103782 161399 := bstep (se 1 (by rfl) ⟨121049, by rfl⟩ : syracuseStep 161399 = 242099) B242099
theorem B161423 : Blo 103782 161423 := bstep (se 1 (by rfl) ⟨121067, by rfl⟩ : syracuseStep 161423 = 242135) B242135
theorem B161465 : Blo 103782 161465 := bstep (se 2 (by rfl) ⟨60549, by rfl⟩ : syracuseStep 161465 = 121099) B121099
theorem B358145 : Blo 103782 358145 := bstep (se 2 (by rfl) ⟨134304, by rfl⟩ : syracuseStep 358145 = 268609) B268609
theorem B1832705 : Blo 103782 1832705 := bstep (se 2 (by rfl) ⟨687264, by rfl⟩ : syracuseStep 1832705 = 1374529) B1374529
theorem B161543 : Blo 103782 161543 := bstep (se 1 (by rfl) ⟨121157, by rfl⟩ : syracuseStep 161543 = 242315) B242315
theorem B161579 : Blo 103782 161579 := bstep (se 1 (by rfl) ⟨121184, by rfl⟩ : syracuseStep 161579 = 242369) B242369
theorem B1996595 : Blo 103782 1996595 := bstep (se 1 (by rfl) ⟨1497446, by rfl⟩ : syracuseStep 1996595 = 2994893) B2994893
theorem B161609 : Blo 103782 161609 := bstep (se 2 (by rfl) ⟨60603, by rfl⟩ : syracuseStep 161609 = 121207) B121207
theorem B587665 : Blo 103782 587665 := bstep (se 2 (by rfl) ⟨220374, by rfl⟩ : syracuseStep 587665 = 440749) B440749
theorem B292925 : Blo 103782 292925 := bstep (se 3 (by rfl) ⟨54923, by rfl⟩ : syracuseStep 292925 = 109847) B109847
theorem B129295 : Blo 103782 129295 := bstep (se 1 (by rfl) ⟨96971, by rfl⟩ : syracuseStep 129295 = 193943) B193943
theorem B1046843 : Blo 103782 1046843 := bstep (se 1 (by rfl) ⟨785132, by rfl⟩ : syracuseStep 1046843 = 1570265) B1570265
theorem B162167 : Blo 103782 162167 := bstep (se 1 (by rfl) ⟨121625, by rfl⟩ : syracuseStep 162167 = 243251) B243251
theorem B227731 : Blo 103782 227731 := bstep (se 1 (by rfl) ⟨170798, by rfl⟩ : syracuseStep 227731 = 341597) B341597
theorem B391969 : Blo 103782 391969 := bstep (se 2 (by rfl) ⟨146988, by rfl⟩ : syracuseStep 391969 = 293977) B293977
theorem B1080139 : Blo 103782 1080139 := bstep (se 1 (by rfl) ⟨810104, by rfl⟩ : syracuseStep 1080139 = 1620209) B1620209
theorem B359315 : Blo 103782 359315 := bstep (se 1 (by rfl) ⟨269486, by rfl⟩ : syracuseStep 359315 = 538973) B538973
theorem B360449 : Blo 103782 360449 := bstep (se 2 (by rfl) ⟨135168, by rfl⟩ : syracuseStep 360449 = 270337) B270337
theorem B361259 : Blo 103782 361259 := bstep (se 1 (by rfl) ⟨270944, by rfl⟩ : syracuseStep 361259 = 541889) B541889
theorem B295775 : Blo 103782 295775 := bstep (se 1 (by rfl) ⟨221831, by rfl⟩ : syracuseStep 295775 = 443663) B443663
theorem B820115 : Blo 103782 820115 := bstep (se 1 (by rfl) ⟨615086, by rfl⟩ : syracuseStep 820115 = 1230173) B1230173
theorem B721847 : Blo 103782 721847 := bstep (se 1 (by rfl) ⟨541385, by rfl⟩ : syracuseStep 721847 = 1082771) B1082771
theorem B361529 : Blo 103782 361529 := bstep (se 2 (by rfl) ⟨135573, by rfl⟩ : syracuseStep 361529 = 271147) B271147
theorem B197711 : Blo 103782 197711 := bstep (se 1 (by rfl) ⟨148283, by rfl⟩ : syracuseStep 197711 = 296567) B296567
theorem B361853 : Blo 103782 361853 := bstep (se 3 (by rfl) ⟨67847, by rfl⟩ : syracuseStep 361853 = 135695) B135695
theorem B689573 : Blo 103782 689573 := bstep (se 4 (by rfl) ⟨64647, by rfl⟩ : syracuseStep 689573 = 129295) B129295
theorem B394739 : Blo 103782 394739 := bstep (se 1 (by rfl) ⟨296054, by rfl⟩ : syracuseStep 394739 = 592109) B592109
theorem B689725 : Blo 103782 689725 := bstep (se 3 (by rfl) ⟨129323, by rfl⟩ : syracuseStep 689725 = 258647) B258647
theorem B362123 : Blo 103782 362123 := bstep (se 1 (by rfl) ⟨271592, by rfl⟩ : syracuseStep 362123 = 543185) B543185
theorem B526013 : Blo 103782 526013 := bstep (se 3 (by rfl) ⟨98627, by rfl⟩ : syracuseStep 526013 = 197255) B197255
theorem B821035 : Blo 103782 821035 := bstep (se 1 (by rfl) ⟨615776, by rfl⟩ : syracuseStep 821035 = 1231553) B1231553
theorem B788291 : Blo 103782 788291 := bstep (se 1 (by rfl) ⟨591218, by rfl⟩ : syracuseStep 788291 = 1182437) B1182437
theorem B526175 : Blo 103782 526175 := bstep (se 1 (by rfl) ⟨394631, by rfl⟩ : syracuseStep 526175 = 789263) B789263
theorem B133159 : Blo 103782 133159 := bstep (se 1 (by rfl) ⟨99869, by rfl⟩ : syracuseStep 133159 = 199739) B199739
theorem B198713 : Blo 103782 198713 := bstep (se 2 (by rfl) ⟨74517, by rfl⟩ : syracuseStep 198713 = 149035) B149035
theorem B133483 : Blo 103782 133483 := bstep (se 1 (by rfl) ⟨100112, by rfl⟩ : syracuseStep 133483 = 200225) B200225
theorem B297341 : Blo 103782 297341 := bstep (se 3 (by rfl) ⟨55751, by rfl⟩ : syracuseStep 297341 = 111503) B111503
theorem B264667 : Blo 103782 264667 := bstep (se 1 (by rfl) ⟨198500, by rfl⟩ : syracuseStep 264667 = 397001) B397001
theorem B2296349 : Blo 103782 2296349 := bstep (se 3 (by rfl) ⟨430565, by rfl⟩ : syracuseStep 2296349 = 861131) B861131
theorem B363041 : Blo 103782 363041 := bstep (se 2 (by rfl) ⟨136140, by rfl⟩ : syracuseStep 363041 = 272281) B272281
theorem B297569 : Blo 103782 297569 := bstep (se 2 (by rfl) ⟨111588, by rfl⟩ : syracuseStep 297569 = 223177) B223177
theorem B363257 : Blo 103782 363257 := bstep (se 2 (by rfl) ⟨136221, by rfl⟩ : syracuseStep 363257 = 272443) B272443
theorem B297911 : Blo 103782 297911 := bstep (se 1 (by rfl) ⟨223433, by rfl⟩ : syracuseStep 297911 = 446867) B446867
theorem B363527 : Blo 103782 363527 := bstep (se 1 (by rfl) ⟨272645, by rfl⟩ : syracuseStep 363527 = 545291) B545291
theorem B265295 : Blo 103782 265295 := bstep (se 1 (by rfl) ⟨198971, by rfl⟩ : syracuseStep 265295 = 397943) B397943
theorem B363635 : Blo 103782 363635 := bstep (se 1 (by rfl) ⟨272726, by rfl⟩ : syracuseStep 363635 = 545453) B545453
theorem B167351 : Blo 103782 167351 := bstep (se 1 (by rfl) ⟨125513, by rfl⟩ : syracuseStep 167351 = 251027) B251027
theorem B134779 : Blo 103782 134779 := bstep (se 1 (by rfl) ⟨101084, by rfl⟩ : syracuseStep 134779 = 202169) B202169
theorem B265943 : Blo 103782 265943 := bstep (se 1 (by rfl) ⟨199457, by rfl⟩ : syracuseStep 265943 = 398915) B398915
theorem B200711 : Blo 103782 200711 := bstep (se 1 (by rfl) ⟨150533, by rfl⟩ : syracuseStep 200711 = 301067) B301067
theorem B299027 : Blo 103782 299027 := bstep (se 1 (by rfl) ⟨224270, by rfl⟩ : syracuseStep 299027 = 448541) B448541
theorem B397655 : Blo 103782 397655 := bstep (se 1 (by rfl) ⟨298241, by rfl⟩ : syracuseStep 397655 = 596483) B596483
theorem B299369 : Blo 103782 299369 := bstep (se 2 (by rfl) ⟨112263, by rfl⟩ : syracuseStep 299369 = 224527) B224527
theorem B201143 : Blo 103782 201143 := bstep (se 1 (by rfl) ⟨150857, by rfl⟩ : syracuseStep 201143 = 301715) B301715
theorem B299483 : Blo 103782 299483 := bstep (se 1 (by rfl) ⟨224612, by rfl⟩ : syracuseStep 299483 = 449225) B449225
theorem B1380887 : Blo 103782 1380887 := bstep (se 1 (by rfl) ⟨1035665, by rfl⟩ : syracuseStep 1380887 = 2071331) B2071331
theorem B758297 : Blo 103782 758297 := bstep (se 2 (by rfl) ⟨284361, by rfl⟩ : syracuseStep 758297 = 568723) B568723
theorem B528929 : Blo 103782 528929 := bstep (se 2 (by rfl) ⟨198348, by rfl⟩ : syracuseStep 528929 = 396697) B396697
theorem B201295 : Blo 103782 201295 := bstep (se 1 (by rfl) ⟨150971, by rfl⟩ : syracuseStep 201295 = 301943) B301943
theorem B234107 : Blo 103782 234107 := bstep (se 1 (by rfl) ⟨175580, by rfl⟩ : syracuseStep 234107 = 351161) B351161
theorem B234233 : Blo 103782 234233 := bstep (se 2 (by rfl) ⟨87837, by rfl⟩ : syracuseStep 234233 = 175675) B175675
theorem B1512209 : Blo 103782 1512209 := bstep (se 2 (by rfl) ⟨567078, by rfl⟩ : syracuseStep 1512209 = 1134157) B1134157
theorem B398267 : Blo 103782 398267 := bstep (se 1 (by rfl) ⟨298700, by rfl⟩ : syracuseStep 398267 = 597401) B597401
theorem B234503 : Blo 103782 234503 := bstep (se 1 (by rfl) ⟨175877, by rfl⟩ : syracuseStep 234503 = 351755) B351755
theorem B332819 : Blo 103782 332819 := bstep (se 1 (by rfl) ⟨249614, by rfl⟩ : syracuseStep 332819 = 499229) B499229
theorem B234575 : Blo 103782 234575 := bstep (se 1 (by rfl) ⟨175931, by rfl⟩ : syracuseStep 234575 = 351863) B351863
theorem B103803 : Blo 103782 103803 := bstep (se 1 (by rfl) ⟨77852, by rfl⟩ : syracuseStep 103803 = 155705) B155705
theorem B103855 : Blo 103782 103855 := bstep (se 1 (by rfl) ⟨77891, by rfl⟩ : syracuseStep 103855 = 155783) B155783
theorem B103879 : Blo 103782 103879 := bstep (se 1 (by rfl) ⟨77909, by rfl⟩ : syracuseStep 103879 = 155819) B155819
theorem B103899 : Blo 103782 103899 := bstep (se 1 (by rfl) ⟨77924, by rfl⟩ : syracuseStep 103899 = 155849) B155849
theorem B234971 : Blo 103782 234971 := bstep (se 1 (by rfl) ⟨176228, by rfl⟩ : syracuseStep 234971 = 352457) B352457
theorem B103975 : Blo 103782 103975 := bstep (se 1 (by rfl) ⟨77981, by rfl⟩ : syracuseStep 103975 = 155963) B155963
theorem B104015 : Blo 103782 104015 := bstep (se 1 (by rfl) ⟨78011, by rfl⟩ : syracuseStep 104015 = 156023) B156023
theorem B104031 : Blo 103782 104031 := bstep (se 1 (by rfl) ⟨78023, by rfl⟩ : syracuseStep 104031 = 156047) B156047
theorem B398945 : Blo 103782 398945 := bstep (se 2 (by rfl) ⟨149604, by rfl⟩ : syracuseStep 398945 = 299209) B299209
theorem B104059 : Blo 103782 104059 := bstep (se 1 (by rfl) ⟨78044, by rfl⟩ : syracuseStep 104059 = 156089) B156089
theorem B300667 : Blo 103782 300667 := bstep (se 1 (by rfl) ⟨225500, by rfl⟩ : syracuseStep 300667 = 451001) B451001
theorem B104111 : Blo 103782 104111 := bstep (se 1 (by rfl) ⟨78083, by rfl⟩ : syracuseStep 104111 = 156167) B156167
theorem B104135 : Blo 103782 104135 := bstep (se 1 (by rfl) ⟨78101, by rfl⟩ : syracuseStep 104135 = 156203) B156203
theorem B104155 : Blo 103782 104155 := bstep (se 1 (by rfl) ⟨78116, by rfl⟩ : syracuseStep 104155 = 156233) B156233
theorem B300793 : Blo 103782 300793 := bstep (se 2 (by rfl) ⟨112797, by rfl⟩ : syracuseStep 300793 = 225595) B225595
theorem B104231 : Blo 103782 104231 := bstep (se 1 (by rfl) ⟨78173, by rfl⟩ : syracuseStep 104231 = 156347) B156347
theorem B104271 : Blo 103782 104271 := bstep (se 1 (by rfl) ⟨78203, by rfl⟩ : syracuseStep 104271 = 156407) B156407
theorem B104287 : Blo 103782 104287 := bstep (se 1 (by rfl) ⟨78215, by rfl⟩ : syracuseStep 104287 = 156431) B156431
theorem B202601 : Blo 103782 202601 := bstep (se 2 (by rfl) ⟨75975, by rfl⟩ : syracuseStep 202601 = 151951) B151951
theorem B104315 : Blo 103782 104315 := bstep (se 1 (by rfl) ⟨78236, by rfl⟩ : syracuseStep 104315 = 156473) B156473
theorem B104367 : Blo 103782 104367 := bstep (se 1 (by rfl) ⟨78275, by rfl⟩ : syracuseStep 104367 = 156551) B156551
theorem B235439 : Blo 103782 235439 := bstep (se 1 (by rfl) ⟨176579, by rfl⟩ : syracuseStep 235439 = 353159) B353159
theorem B104391 : Blo 103782 104391 := bstep (se 1 (by rfl) ⟨78293, by rfl⟩ : syracuseStep 104391 = 156587) B156587
theorem B104411 : Blo 103782 104411 := bstep (se 1 (by rfl) ⟨78308, by rfl⟩ : syracuseStep 104411 = 156617) B156617
theorem B104487 : Blo 103782 104487 := bstep (se 1 (by rfl) ⟨78365, by rfl⟩ : syracuseStep 104487 = 156731) B156731
theorem B104527 : Blo 103782 104527 := bstep (se 1 (by rfl) ⟨78395, by rfl⟩ : syracuseStep 104527 = 156791) B156791
theorem B792665 : Blo 103782 792665 := bstep (se 2 (by rfl) ⟨297249, by rfl⟩ : syracuseStep 792665 = 594499) B594499
theorem B104543 : Blo 103782 104543 := bstep (se 1 (by rfl) ⟨78407, by rfl⟩ : syracuseStep 104543 = 156815) B156815
theorem B104571 : Blo 103782 104571 := bstep (se 1 (by rfl) ⟨78428, by rfl⟩ : syracuseStep 104571 = 156857) B156857
theorem B235691 : Blo 103782 235691 := bstep (se 1 (by rfl) ⟨176768, by rfl⟩ : syracuseStep 235691 = 353537) B353537
theorem B104623 : Blo 103782 104623 := bstep (se 1 (by rfl) ⟨78467, by rfl⟩ : syracuseStep 104623 = 156935) B156935
theorem B104647 : Blo 103782 104647 := bstep (se 1 (by rfl) ⟨78485, by rfl⟩ : syracuseStep 104647 = 156971) B156971
theorem B104667 : Blo 103782 104667 := bstep (se 1 (by rfl) ⟨78500, by rfl⟩ : syracuseStep 104667 = 157001) B157001
theorem B268535 : Blo 103782 268535 := bstep (se 1 (by rfl) ⟨201401, by rfl⟩ : syracuseStep 268535 = 402803) B402803
theorem B104743 : Blo 103782 104743 := bstep (se 1 (by rfl) ⟨78557, by rfl⟩ : syracuseStep 104743 = 157115) B157115
theorem B104783 : Blo 103782 104783 := bstep (se 1 (by rfl) ⟨78587, by rfl⟩ : syracuseStep 104783 = 157175) B157175
theorem B104799 : Blo 103782 104799 := bstep (se 1 (by rfl) ⟨78599, by rfl⟩ : syracuseStep 104799 = 157199) B157199
theorem B104827 : Blo 103782 104827 := bstep (se 1 (by rfl) ⟨78620, by rfl⟩ : syracuseStep 104827 = 157241) B157241
theorem B104879 : Blo 103782 104879 := bstep (se 1 (by rfl) ⟨78659, by rfl⟩ : syracuseStep 104879 = 157319) B157319
theorem B104903 : Blo 103782 104903 := bstep (se 1 (by rfl) ⟨78677, by rfl⟩ : syracuseStep 104903 = 157355) B157355
theorem B104923 : Blo 103782 104923 := bstep (se 1 (by rfl) ⟨78692, by rfl⟩ : syracuseStep 104923 = 157385) B157385
theorem B104999 : Blo 103782 104999 := bstep (se 1 (by rfl) ⟨78749, by rfl⟩ : syracuseStep 104999 = 157499) B157499
theorem B105039 : Blo 103782 105039 := bstep (se 1 (by rfl) ⟨78779, by rfl⟩ : syracuseStep 105039 = 157559) B157559
theorem B105055 : Blo 103782 105055 := bstep (se 1 (by rfl) ⟨78791, by rfl⟩ : syracuseStep 105055 = 157583) B157583
theorem B105083 : Blo 103782 105083 := bstep (se 1 (by rfl) ⟨78812, by rfl⟩ : syracuseStep 105083 = 157625) B157625
theorem B105135 : Blo 103782 105135 := bstep (se 1 (by rfl) ⟨78851, by rfl⟩ : syracuseStep 105135 = 157703) B157703
theorem B236231 : Blo 103782 236231 := bstep (se 1 (by rfl) ⟨177173, by rfl⟩ : syracuseStep 236231 = 354347) B354347
theorem B105159 : Blo 103782 105159 := bstep (se 1 (by rfl) ⟨78869, by rfl⟩ : syracuseStep 105159 = 157739) B157739
theorem B105179 : Blo 103782 105179 := bstep (se 1 (by rfl) ⟨78884, by rfl⟩ : syracuseStep 105179 = 157769) B157769
theorem B105255 : Blo 103782 105255 := bstep (se 1 (by rfl) ⟨78941, by rfl⟩ : syracuseStep 105255 = 157883) B157883
theorem B301897 : Blo 103782 301897 := bstep (se 2 (by rfl) ⟨113211, by rfl⟩ : syracuseStep 301897 = 226423) B226423
theorem B105295 : Blo 103782 105295 := bstep (se 1 (by rfl) ⟨78971, by rfl⟩ : syracuseStep 105295 = 157943) B157943
theorem B105311 : Blo 103782 105311 := bstep (se 1 (by rfl) ⟨78983, by rfl⟩ : syracuseStep 105311 = 157967) B157967
theorem B203627 : Blo 103782 203627 := bstep (se 1 (by rfl) ⟨152720, by rfl⟩ : syracuseStep 203627 = 305441) B305441
theorem B105339 : Blo 103782 105339 := bstep (se 1 (by rfl) ⟨79004, by rfl⟩ : syracuseStep 105339 = 158009) B158009
theorem B105391 : Blo 103782 105391 := bstep (se 1 (by rfl) ⟨79043, by rfl⟩ : syracuseStep 105391 = 158087) B158087
theorem B105415 : Blo 103782 105415 := bstep (se 1 (by rfl) ⟨79061, by rfl⟩ : syracuseStep 105415 = 158123) B158123
theorem B105435 : Blo 103782 105435 := bstep (se 1 (by rfl) ⟨79076, by rfl⟩ : syracuseStep 105435 = 158153) B158153
theorem B400403 : Blo 103782 400403 := bstep (se 1 (by rfl) ⟨300302, by rfl⟩ : syracuseStep 400403 = 600605) B600605
theorem B105511 : Blo 103782 105511 := bstep (se 1 (by rfl) ⟨79133, by rfl⟩ : syracuseStep 105511 = 158267) B158267
theorem B105551 : Blo 103782 105551 := bstep (se 1 (by rfl) ⟨79163, by rfl⟩ : syracuseStep 105551 = 158327) B158327
theorem B105567 : Blo 103782 105567 := bstep (se 1 (by rfl) ⟨79175, by rfl⟩ : syracuseStep 105567 = 158351) B158351
theorem B105595 : Blo 103782 105595 := bstep (se 1 (by rfl) ⟨79196, by rfl⟩ : syracuseStep 105595 = 158393) B158393
theorem B302251 : Blo 103782 302251 := bstep (se 1 (by rfl) ⟨226688, by rfl⟩ : syracuseStep 302251 = 453377) B453377
theorem B105647 : Blo 103782 105647 := bstep (se 1 (by rfl) ⟨79235, by rfl⟩ : syracuseStep 105647 = 158471) B158471
theorem B105671 : Blo 103782 105671 := bstep (se 1 (by rfl) ⟨79253, by rfl⟩ : syracuseStep 105671 = 158507) B158507
theorem B105691 : Blo 103782 105691 := bstep (se 1 (by rfl) ⟨79268, by rfl⟩ : syracuseStep 105691 = 158537) B158537
theorem B105767 : Blo 103782 105767 := bstep (se 1 (by rfl) ⟨79325, by rfl⟩ : syracuseStep 105767 = 158651) B158651
theorem B105807 : Blo 103782 105807 := bstep (se 1 (by rfl) ⟨79355, by rfl⟩ : syracuseStep 105807 = 158711) B158711
theorem B105823 : Blo 103782 105823 := bstep (se 1 (by rfl) ⟨79367, by rfl⟩ : syracuseStep 105823 = 158735) B158735
theorem B105851 : Blo 103782 105851 := bstep (se 1 (by rfl) ⟨79388, by rfl⟩ : syracuseStep 105851 = 158777) B158777
theorem B105903 : Blo 103782 105903 := bstep (se 1 (by rfl) ⟨79427, by rfl⟩ : syracuseStep 105903 = 158855) B158855
theorem B105927 : Blo 103782 105927 := bstep (se 1 (by rfl) ⟨79445, by rfl⟩ : syracuseStep 105927 = 158891) B158891
theorem B400859 : Blo 103782 400859 := bstep (se 1 (by rfl) ⟨300644, by rfl⟩ : syracuseStep 400859 = 601289) B601289
theorem B105947 : Blo 103782 105947 := bstep (se 1 (by rfl) ⟨79460, by rfl⟩ : syracuseStep 105947 = 158921) B158921
theorem B204295 : Blo 103782 204295 := bstep (se 1 (by rfl) ⟨153221, by rfl⟩ : syracuseStep 204295 = 306443) B306443
theorem B794123 : Blo 103782 794123 := bstep (se 1 (by rfl) ⟨595592, by rfl⟩ : syracuseStep 794123 = 1191185) B1191185
theorem B532007 : Blo 103782 532007 := bstep (se 1 (by rfl) ⟨399005, by rfl⟩ : syracuseStep 532007 = 798011) B798011
theorem B237095 : Blo 103782 237095 := bstep (se 1 (by rfl) ⟨177821, by rfl⟩ : syracuseStep 237095 = 355643) B355643
theorem B106023 : Blo 103782 106023 := bstep (se 1 (by rfl) ⟨79517, by rfl⟩ : syracuseStep 106023 = 159035) B159035
theorem B106063 : Blo 103782 106063 := bstep (se 1 (by rfl) ⟨79547, by rfl⟩ : syracuseStep 106063 = 159095) B159095
theorem B106079 : Blo 103782 106079 := bstep (se 1 (by rfl) ⟨79559, by rfl⟩ : syracuseStep 106079 = 159119) B159119
theorem B106107 : Blo 103782 106107 := bstep (se 1 (by rfl) ⟨79580, by rfl⟩ : syracuseStep 106107 = 159161) B159161
theorem B269963 : Blo 103782 269963 := bstep (se 1 (by rfl) ⟨202472, by rfl⟩ : syracuseStep 269963 = 404945) B404945
theorem B106159 : Blo 103782 106159 := bstep (se 1 (by rfl) ⟨79619, by rfl⟩ : syracuseStep 106159 = 159239) B159239
theorem B106183 : Blo 103782 106183 := bstep (se 1 (by rfl) ⟨79637, by rfl⟩ : syracuseStep 106183 = 159275) B159275
theorem B106203 : Blo 103782 106203 := bstep (se 1 (by rfl) ⟨79652, by rfl⟩ : syracuseStep 106203 = 159305) B159305
theorem B106279 : Blo 103782 106279 := bstep (se 1 (by rfl) ⟨79709, by rfl⟩ : syracuseStep 106279 = 159419) B159419
theorem B106319 : Blo 103782 106319 := bstep (se 1 (by rfl) ⟨79739, by rfl⟩ : syracuseStep 106319 = 159479) B159479
theorem B106335 : Blo 103782 106335 := bstep (se 1 (by rfl) ⟨79751, by rfl⟩ : syracuseStep 106335 = 159503) B159503
theorem B270175 : Blo 103782 270175 := bstep (se 1 (by rfl) ⟨202631, by rfl⟩ : syracuseStep 270175 = 405263) B405263
theorem B237419 : Blo 103782 237419 := bstep (se 1 (by rfl) ⟨178064, by rfl⟩ : syracuseStep 237419 = 356129) B356129
theorem B106363 : Blo 103782 106363 := bstep (se 1 (by rfl) ⟨79772, by rfl⟩ : syracuseStep 106363 = 159545) B159545
theorem B171919 : Blo 103782 171919 := bstep (se 1 (by rfl) ⟨128939, by rfl⟩ : syracuseStep 171919 = 257879) B257879
theorem B237473 : Blo 103782 237473 := bstep (se 2 (by rfl) ⟨89052, by rfl⟩ : syracuseStep 237473 = 178105) B178105
theorem B237487 : Blo 103782 237487 := bstep (se 1 (by rfl) ⟨178115, by rfl⟩ : syracuseStep 237487 = 356231) B356231
theorem B106415 : Blo 103782 106415 := bstep (se 1 (by rfl) ⟨79811, by rfl⟩ : syracuseStep 106415 = 159623) B159623
theorem B106439 : Blo 103782 106439 := bstep (se 1 (by rfl) ⟨79829, by rfl⟩ : syracuseStep 106439 = 159659) B159659
theorem B106459 : Blo 103782 106459 := bstep (se 1 (by rfl) ⟨79844, by rfl⟩ : syracuseStep 106459 = 159689) B159689
theorem B892943 : Blo 103782 892943 := bstep (se 1 (by rfl) ⟨669707, by rfl⟩ : syracuseStep 892943 = 1339415) B1339415
theorem B106535 : Blo 103782 106535 := bstep (se 1 (by rfl) ⟨79901, by rfl⟩ : syracuseStep 106535 = 159803) B159803
theorem B106575 : Blo 103782 106575 := bstep (se 1 (by rfl) ⟨79931, by rfl⟩ : syracuseStep 106575 = 159863) B159863
theorem B106591 : Blo 103782 106591 := bstep (se 1 (by rfl) ⟨79943, by rfl⟩ : syracuseStep 106591 = 159887) B159887
theorem B106619 : Blo 103782 106619 := bstep (se 1 (by rfl) ⟨79964, by rfl⟩ : syracuseStep 106619 = 159929) B159929
theorem B106671 : Blo 103782 106671 := bstep (se 1 (by rfl) ⟨80003, by rfl⟩ : syracuseStep 106671 = 160007) B160007
theorem B106695 : Blo 103782 106695 := bstep (se 1 (by rfl) ⟨80021, by rfl⟩ : syracuseStep 106695 = 160043) B160043
theorem B106715 : Blo 103782 106715 := bstep (se 1 (by rfl) ⟨80036, by rfl⟩ : syracuseStep 106715 = 160073) B160073
theorem B237815 : Blo 103782 237815 := bstep (se 1 (by rfl) ⟨178361, by rfl⟩ : syracuseStep 237815 = 356723) B356723
theorem B106791 : Blo 103782 106791 := bstep (se 1 (by rfl) ⟨80093, by rfl⟩ : syracuseStep 106791 = 160187) B160187
theorem B106831 : Blo 103782 106831 := bstep (se 1 (by rfl) ⟨80123, by rfl⟩ : syracuseStep 106831 = 160247) B160247
theorem B205151 : Blo 103782 205151 := bstep (se 1 (by rfl) ⟨153863, by rfl⟩ : syracuseStep 205151 = 307727) B307727
theorem B106847 : Blo 103782 106847 := bstep (se 1 (by rfl) ⟨80135, by rfl⟩ : syracuseStep 106847 = 160271) B160271
theorem B106875 : Blo 103782 106875 := bstep (se 1 (by rfl) ⟨80156, by rfl⟩ : syracuseStep 106875 = 160313) B160313
theorem B106927 : Blo 103782 106927 := bstep (se 1 (by rfl) ⟨80195, by rfl⟩ : syracuseStep 106927 = 160391) B160391
theorem B106951 : Blo 103782 106951 := bstep (se 1 (by rfl) ⟨80213, by rfl⟩ : syracuseStep 106951 = 160427) B160427
theorem B106971 : Blo 103782 106971 := bstep (se 1 (by rfl) ⟨80228, by rfl⟩ : syracuseStep 106971 = 160457) B160457
theorem B434651 : Blo 103782 434651 := bstep (se 1 (by rfl) ⟨325988, by rfl⟩ : syracuseStep 434651 = 651977) B651977
theorem B303641 : Blo 103782 303641 := bstep (se 2 (by rfl) ⟨113865, by rfl⟩ : syracuseStep 303641 = 227731) B227731
theorem B107047 : Blo 103782 107047 := bstep (se 1 (by rfl) ⟨80285, by rfl⟩ : syracuseStep 107047 = 160571) B160571
theorem B107087 : Blo 103782 107087 := bstep (se 1 (by rfl) ⟨80315, by rfl⟩ : syracuseStep 107087 = 160631) B160631
theorem B107103 : Blo 103782 107103 := bstep (se 1 (by rfl) ⟨80327, by rfl⟩ : syracuseStep 107103 = 160655) B160655
theorem B402043 : Blo 103782 402043 := bstep (se 1 (by rfl) ⟨301532, by rfl⟩ : syracuseStep 402043 = 603065) B603065
theorem B107131 : Blo 103782 107131 := bstep (se 1 (by rfl) ⟨80348, by rfl⟩ : syracuseStep 107131 = 160697) B160697
theorem B107183 : Blo 103782 107183 := bstep (se 1 (by rfl) ⟨80387, by rfl⟩ : syracuseStep 107183 = 160775) B160775
theorem B107207 : Blo 103782 107207 := bstep (se 1 (by rfl) ⟨80405, by rfl⟩ : syracuseStep 107207 = 160811) B160811
theorem B107227 : Blo 103782 107227 := bstep (se 1 (by rfl) ⟨80420, by rfl⟩ : syracuseStep 107227 = 160841) B160841
theorem B271097 : Blo 103782 271097 := bstep (se 2 (by rfl) ⟨101661, by rfl⟩ : syracuseStep 271097 = 203323) B203323
theorem B107303 : Blo 103782 107303 := bstep (se 1 (by rfl) ⟨80477, by rfl⟩ : syracuseStep 107303 = 160955) B160955
theorem B238409 : Blo 103782 238409 := bstep (se 2 (by rfl) ⟨89403, by rfl⟩ : syracuseStep 238409 = 178807) B178807
theorem B107343 : Blo 103782 107343 := bstep (se 1 (by rfl) ⟨80507, by rfl⟩ : syracuseStep 107343 = 161015) B161015
theorem B107359 : Blo 103782 107359 := bstep (se 1 (by rfl) ⟨80519, by rfl⟩ : syracuseStep 107359 = 161039) B161039
theorem B107387 : Blo 103782 107387 := bstep (se 1 (by rfl) ⟨80540, by rfl⟩ : syracuseStep 107387 = 161081) B161081
theorem B107439 : Blo 103782 107439 := bstep (se 1 (by rfl) ⟨80579, by rfl⟩ : syracuseStep 107439 = 161159) B161159
theorem B107463 : Blo 103782 107463 := bstep (se 1 (by rfl) ⟨80597, by rfl⟩ : syracuseStep 107463 = 161195) B161195
theorem B107483 : Blo 103782 107483 := bstep (se 1 (by rfl) ⟨80612, by rfl⟩ : syracuseStep 107483 = 161225) B161225
theorem B762853 : Blo 103782 762853 := bstep (se 4 (by rfl) ⟨71517, by rfl⟩ : syracuseStep 762853 = 143035) B143035
theorem B107559 : Blo 103782 107559 := bstep (se 1 (by rfl) ⟨80669, by rfl⟩ : syracuseStep 107559 = 161339) B161339
theorem B107599 : Blo 103782 107599 := bstep (se 1 (by rfl) ⟨80699, by rfl⟩ : syracuseStep 107599 = 161399) B161399
theorem B107615 : Blo 103782 107615 := bstep (se 1 (by rfl) ⟨80711, by rfl⟩ : syracuseStep 107615 = 161423) B161423
theorem B107643 : Blo 103782 107643 := bstep (se 1 (by rfl) ⟨80732, by rfl⟩ : syracuseStep 107643 = 161465) B161465
theorem B238763 : Blo 103782 238763 := bstep (se 1 (by rfl) ⟨179072, by rfl⟩ : syracuseStep 238763 = 358145) B358145
theorem B1221803 : Blo 103782 1221803 := bstep (se 1 (by rfl) ⟨916352, by rfl⟩ : syracuseStep 1221803 = 1832705) B1832705
theorem B107695 : Blo 103782 107695 := bstep (se 1 (by rfl) ⟨80771, by rfl⟩ : syracuseStep 107695 = 161543) B161543
theorem B107719 : Blo 103782 107719 := bstep (se 1 (by rfl) ⟨80789, by rfl⟩ : syracuseStep 107719 = 161579) B161579
theorem B107739 : Blo 103782 107739 := bstep (se 1 (by rfl) ⟨80804, by rfl⟩ : syracuseStep 107739 = 161609) B161609
theorem B337277 : Blo 103782 337277 := bstep (se 3 (by rfl) ⟨63239, by rfl⟩ : syracuseStep 337277 = 126479) B126479
theorem B271745 : Blo 103782 271745 := bstep (se 2 (by rfl) ⟨101904, by rfl⟩ : syracuseStep 271745 = 203809) B203809
theorem B796067 : Blo 103782 796067 := bstep (se 1 (by rfl) ⟨597050, by rfl⟩ : syracuseStep 796067 = 1194101) B1194101
theorem B697895 : Blo 103782 697895 := bstep (se 1 (by rfl) ⟨523421, by rfl⟩ : syracuseStep 697895 = 1046843) B1046843
theorem B534113 : Blo 103782 534113 := bstep (se 2 (by rfl) ⟨200292, by rfl⟩ : syracuseStep 534113 = 400585) B400585
theorem B239201 : Blo 103782 239201 := bstep (se 2 (by rfl) ⟨89700, by rfl⟩ : syracuseStep 239201 = 179401) B179401
theorem B2762387 : Blo 103782 2762387 := bstep (se 1 (by rfl) ⟨2071790, by rfl⟩ : syracuseStep 2762387 = 4143581) B4143581
theorem B501497 : Blo 103782 501497 := bstep (se 2 (by rfl) ⟨188061, by rfl⟩ : syracuseStep 501497 = 376123) B376123
theorem B1189727 : Blo 103782 1189727 := bstep (se 1 (by rfl) ⟨892295, by rfl⟩ : syracuseStep 1189727 = 1784591) B1784591
theorem B403319 : Blo 103782 403319 := bstep (se 1 (by rfl) ⟨302489, by rfl⟩ : syracuseStep 403319 = 604979) B604979
theorem B239543 : Blo 103782 239543 := bstep (se 1 (by rfl) ⟨179657, by rfl⟩ : syracuseStep 239543 = 359315) B359315
theorem B272555 : Blo 103782 272555 := bstep (se 1 (by rfl) ⟨204416, by rfl⟩ : syracuseStep 272555 = 408833) B408833
theorem B600331 : Blo 103782 600331 := bstep (se 1 (by rfl) ⟨450248, by rfl⟩ : syracuseStep 600331 = 900497) B900497
theorem B240137 : Blo 103782 240137 := bstep (se 2 (by rfl) ⟨90051, by rfl⟩ : syracuseStep 240137 = 180103) B180103
theorem B1026593 : Blo 103782 1026593 := bstep (se 2 (by rfl) ⟨384972, by rfl⟩ : syracuseStep 1026593 = 769945) B769945
theorem B404291 : Blo 103782 404291 := bstep (se 1 (by rfl) ⟨303218, by rfl⟩ : syracuseStep 404291 = 606437) B606437
theorem B240479 : Blo 103782 240479 := bstep (se 1 (by rfl) ⟨180359, by rfl⟩ : syracuseStep 240479 = 360719) B360719
theorem B1354643 : Blo 103782 1354643 := bstep (se 1 (by rfl) ⟨1015982, by rfl⟩ : syracuseStep 1354643 = 2031965) B2031965
theorem B535571 : Blo 103782 535571 := bstep (se 1 (by rfl) ⟨401678, by rfl⟩ : syracuseStep 535571 = 803357) B803357
theorem B240659 : Blo 103782 240659 := bstep (se 1 (by rfl) ⟨180494, by rfl⟩ : syracuseStep 240659 = 360989) B360989
theorem B404561 : Blo 103782 404561 := bstep (se 2 (by rfl) ⟨151710, by rfl⟩ : syracuseStep 404561 = 303421) B303421
theorem B2174147 : Blo 103782 2174147 := bstep (se 1 (by rfl) ⟨1630610, by rfl⟩ : syracuseStep 2174147 = 3261221) B3261221
theorem B175351 : Blo 103782 175351 := bstep (se 1 (by rfl) ⟨131513, by rfl⟩ : syracuseStep 175351 = 263027) B263027
theorem B404747 : Blo 103782 404747 := bstep (se 1 (by rfl) ⟨303560, by rfl⟩ : syracuseStep 404747 = 607121) B607121
theorem B241001 : Blo 103782 241001 := bstep (se 2 (by rfl) ⟨90375, by rfl⟩ : syracuseStep 241001 = 180751) B180751
theorem B175547 : Blo 103782 175547 := bstep (se 1 (by rfl) ⟨131660, by rfl⟩ : syracuseStep 175547 = 263321) B263321
theorem B339481 : Blo 103782 339481 := bstep (se 2 (by rfl) ⟨127305, by rfl⟩ : syracuseStep 339481 = 254611) B254611
theorem B175655 : Blo 103782 175655 := bstep (se 1 (by rfl) ⟨131741, by rfl⟩ : syracuseStep 175655 = 263483) B263483
theorem B2010743 : Blo 103782 2010743 := bstep (se 1 (by rfl) ⟨1508057, by rfl⟩ : syracuseStep 2010743 = 3016115) B3016115
theorem B601789 : Blo 103782 601789 := bstep (se 3 (by rfl) ⟨112835, by rfl⟩ : syracuseStep 601789 = 225671) B225671
theorem B306899 : Blo 103782 306899 := bstep (se 1 (by rfl) ⟨230174, by rfl⟩ : syracuseStep 306899 = 460349) B460349
theorem B798497 : Blo 103782 798497 := bstep (se 2 (by rfl) ⟨299436, by rfl⟩ : syracuseStep 798497 = 598873) B598873
theorem B175945 : Blo 103782 175945 := bstep (se 2 (by rfl) ⟨65979, by rfl⟩ : syracuseStep 175945 = 131959) B131959
theorem B175979 : Blo 103782 175979 := bstep (se 1 (by rfl) ⟨131984, by rfl⟩ : syracuseStep 175979 = 263969) B263969
theorem B405431 : Blo 103782 405431 := bstep (se 1 (by rfl) ⟨304073, by rfl⟩ : syracuseStep 405431 = 608147) B608147
theorem B241595 : Blo 103782 241595 := bstep (se 1 (by rfl) ⟨181196, by rfl⟩ : syracuseStep 241595 = 362393) B362393
theorem B1224719 : Blo 103782 1224719 := bstep (se 1 (by rfl) ⟨918539, by rfl⟩ : syracuseStep 1224719 = 1837079) B1837079
theorem B241721 : Blo 103782 241721 := bstep (se 2 (by rfl) ⟨90645, by rfl⟩ : syracuseStep 241721 = 181291) B181291
theorem B569501 : Blo 103782 569501 := bstep (se 3 (by rfl) ⟨106781, by rfl⟩ : syracuseStep 569501 = 213563) B213563
theorem B176377 : Blo 103782 176377 := bstep (se 2 (by rfl) ⟨66141, by rfl⟩ : syracuseStep 176377 = 132283) B132283
theorem B242063 : Blo 103782 242063 := bstep (se 1 (by rfl) ⟨181547, by rfl⟩ : syracuseStep 242063 = 363095) B363095
theorem B504301 : Blo 103782 504301 := bstep (se 3 (by rfl) ⟨94556, by rfl⟩ : syracuseStep 504301 = 189113) B189113
theorem B176647 : Blo 103782 176647 := bstep (se 1 (by rfl) ⟨132485, by rfl⟩ : syracuseStep 176647 = 264971) B264971
theorem B406205 : Blo 103782 406205 := bstep (se 3 (by rfl) ⟨76163, by rfl⟩ : syracuseStep 406205 = 152327) B152327
theorem B537299 : Blo 103782 537299 := bstep (se 1 (by rfl) ⟨402974, by rfl⟩ : syracuseStep 537299 = 805949) B805949
theorem B242387 : Blo 103782 242387 := bstep (se 1 (by rfl) ⟨181790, by rfl⟩ : syracuseStep 242387 = 363581) B363581
theorem B10138385 : Blo 103782 10138385 := bstep (se 2 (by rfl) ⟨3801894, by rfl⟩ : syracuseStep 10138385 = 7603789) B7603789
theorem B177079 : Blo 103782 177079 := bstep (se 1 (by rfl) ⟨132809, by rfl⟩ : syracuseStep 177079 = 265619) B265619
theorem B177275 : Blo 103782 177275 := bstep (se 1 (by rfl) ⟨132956, by rfl⟩ : syracuseStep 177275 = 265913) B265913
theorem B406889 : Blo 103782 406889 := bstep (se 2 (by rfl) ⟨152583, by rfl⟩ : syracuseStep 406889 = 305167) B305167
theorem B308605 : Blo 103782 308605 := bstep (se 3 (by rfl) ⟨57863, by rfl⟩ : syracuseStep 308605 = 115727) B115727
theorem B177673 : Blo 103782 177673 := bstep (se 2 (by rfl) ⟨66627, by rfl⟩ : syracuseStep 177673 = 133255) B133255
theorem B177835 : Blo 103782 177835 := bstep (se 1 (by rfl) ⟨133376, by rfl⟩ : syracuseStep 177835 = 266753) B266753
theorem B538487 : Blo 103782 538487 := bstep (se 1 (by rfl) ⟨403865, by rfl⟩ : syracuseStep 538487 = 807731) B807731
theorem B178139 : Blo 103782 178139 := bstep (se 1 (by rfl) ⟨133604, by rfl⟩ : syracuseStep 178139 = 267209) B267209
theorem B3225757 : Blo 103782 3225757 := bstep (se 3 (by rfl) ⟨604829, by rfl⟩ : syracuseStep 3225757 = 1209659) B1209659
theorem B178375 : Blo 103782 178375 := bstep (se 1 (by rfl) ⟨133781, by rfl⟩ : syracuseStep 178375 = 267563) B267563
theorem B768305 : Blo 103782 768305 := bstep (se 2 (by rfl) ⟨288114, by rfl⟩ : syracuseStep 768305 = 576229) B576229
theorem B178537 : Blo 103782 178537 := bstep (se 2 (by rfl) ⟨66951, by rfl⟩ : syracuseStep 178537 = 133903) B133903
theorem B342401 : Blo 103782 342401 := bstep (se 2 (by rfl) ⟨128400, by rfl⟩ : syracuseStep 342401 = 256801) B256801
theorem B113071 : Blo 103782 113071 := bstep (se 1 (by rfl) ⟨84803, by rfl⟩ : syracuseStep 113071 = 169607) B169607
theorem B604705 : Blo 103782 604705 := bstep (se 2 (by rfl) ⟨226764, by rfl⟩ : syracuseStep 604705 = 453529) B453529
theorem B342967 : Blo 103782 342967 := bstep (se 1 (by rfl) ⟨257225, by rfl⟩ : syracuseStep 342967 = 514451) B514451
theorem B179131 : Blo 103782 179131 := bstep (se 1 (by rfl) ⟨134348, by rfl⟩ : syracuseStep 179131 = 268697) B268697
theorem B179239 : Blo 103782 179239 := bstep (se 1 (by rfl) ⟨134429, by rfl⟩ : syracuseStep 179239 = 268859) B268859
theorem B179563 : Blo 103782 179563 := bstep (se 1 (by rfl) ⟨134672, by rfl⟩ : syracuseStep 179563 = 269345) B269345
theorem B409121 : Blo 103782 409121 := bstep (se 2 (by rfl) ⟨153420, by rfl⟩ : syracuseStep 409121 = 306841) B306841
theorem B1195559 : Blo 103782 1195559 := bstep (se 1 (by rfl) ⟨896669, by rfl⟩ : syracuseStep 1195559 = 1793339) B1793339
theorem B180623 : Blo 103782 180623 := bstep (se 1 (by rfl) ⟨135467, by rfl⟩ : syracuseStep 180623 = 270935) B270935
theorem B180859 : Blo 103782 180859 := bstep (se 1 (by rfl) ⟨135644, by rfl⟩ : syracuseStep 180859 = 271289) B271289
theorem B1131569 : Blo 103782 1131569 := bstep (se 2 (by rfl) ⟨424338, by rfl⟩ : syracuseStep 1131569 = 848677) B848677
theorem B181723 : Blo 103782 181723 := bstep (se 1 (by rfl) ⟨136292, by rfl⟩ : syracuseStep 181723 = 272585) B272585
theorem B738827 : Blo 103782 738827 := bstep (se 1 (by rfl) ⟨554120, by rfl⟩ : syracuseStep 738827 = 1108241) B1108241
theorem B411259 : Blo 103782 411259 := bstep (se 1 (by rfl) ⟨308444, by rfl⟩ : syracuseStep 411259 = 616889) B616889
theorem B116815 : Blo 103782 116815 := bstep (se 1 (by rfl) ⟨87611, by rfl⟩ : syracuseStep 116815 = 175223) B175223
theorem B1427543 : Blo 103782 1427543 := bstep (se 1 (by rfl) ⟨1070657, by rfl⟩ : syracuseStep 1427543 = 2141315) B2141315
theorem B510067 : Blo 103782 510067 := bstep (se 1 (by rfl) ⟨382550, by rfl⟩ : syracuseStep 510067 = 765101) B765101
theorem B903473 : Blo 103782 903473 := bstep (se 2 (by rfl) ⟨338802, by rfl⟩ : syracuseStep 903473 = 677605) B677605
theorem B149855 : Blo 103782 149855 := bstep (se 1 (by rfl) ⟨112391, by rfl⟩ : syracuseStep 149855 = 224783) B224783
theorem B117211 : Blo 103782 117211 := bstep (se 1 (by rfl) ⟨87908, by rfl⟩ : syracuseStep 117211 = 175817) B175817
theorem B281075 : Blo 103782 281075 := bstep (se 1 (by rfl) ⟨210806, by rfl⟩ : syracuseStep 281075 = 421613) B421613
theorem B444953 : Blo 103782 444953 := bstep (se 2 (by rfl) ⟨166857, by rfl⟩ : syracuseStep 444953 = 333715) B333715
theorem B281227 : Blo 103782 281227 := bstep (se 1 (by rfl) ⟨210920, by rfl⟩ : syracuseStep 281227 = 421841) B421841
theorem B150265 : Blo 103782 150265 := bstep (se 2 (by rfl) ⟨56349, by rfl⟩ : syracuseStep 150265 = 112699) B112699
theorem B117679 : Blo 103782 117679 := bstep (se 1 (by rfl) ⟨88259, by rfl⟩ : syracuseStep 117679 = 176519) B176519
theorem B543671 : Blo 103782 543671 := bstep (se 1 (by rfl) ⟨407753, by rfl⟩ : syracuseStep 543671 = 815507) B815507
theorem B150607 : Blo 103782 150607 := bstep (se 1 (by rfl) ⟨112955, by rfl⟩ : syracuseStep 150607 = 225911) B225911
theorem B904385 : Blo 103782 904385 := bstep (se 2 (by rfl) ⟨339144, by rfl⟩ : syracuseStep 904385 = 678289) B678289
theorem B118111 : Blo 103782 118111 := bstep (se 1 (by rfl) ⟨88583, by rfl⟩ : syracuseStep 118111 = 177167) B177167
theorem B970157 : Blo 103782 970157 := bstep (se 3 (by rfl) ⟨181904, by rfl⟩ : syracuseStep 970157 = 363809) B363809
theorem B642505 : Blo 103782 642505 := bstep (se 2 (by rfl) ⟨240939, by rfl⟩ : syracuseStep 642505 = 481879) B481879
theorem B511451 : Blo 103782 511451 := bstep (se 1 (by rfl) ⟨383588, by rfl⟩ : syracuseStep 511451 = 767177) B767177
theorem B118471 : Blo 103782 118471 := bstep (se 1 (by rfl) ⟨88853, by rfl⟩ : syracuseStep 118471 = 177707) B177707
theorem B1331063 : Blo 103782 1331063 := bstep (se 1 (by rfl) ⟨998297, by rfl⟩ : syracuseStep 1331063 = 1996595) B1996595
theorem B413753 : Blo 103782 413753 := bstep (se 2 (by rfl) ⟨155157, by rfl⟩ : syracuseStep 413753 = 310315) B310315
theorem B545129 : Blo 103782 545129 := bstep (se 2 (by rfl) ⟨204423, by rfl⟩ : syracuseStep 545129 = 408847) B408847
theorem B119335 : Blo 103782 119335 := bstep (se 1 (by rfl) ⟨89501, by rfl⟩ : syracuseStep 119335 = 179003) B179003
theorem B774791 : Blo 103782 774791 := bstep (se 1 (by rfl) ⟨581093, by rfl⟩ : syracuseStep 774791 = 1162187) B1162187
theorem B3134213 : Blo 103782 3134213 := bstep (se 4 (by rfl) ⟨293832, by rfl⟩ : syracuseStep 3134213 = 587665) B587665
theorem B578411 : Blo 103782 578411 := bstep (se 1 (by rfl) ⟨433808, by rfl⟩ : syracuseStep 578411 = 867617) B867617
theorem B906511 : Blo 103782 906511 := bstep (se 1 (by rfl) ⟨679883, by rfl⟩ : syracuseStep 906511 = 1359767) B1359767
theorem B644755 : Blo 103782 644755 := bstep (se 1 (by rfl) ⟨483566, by rfl⟩ : syracuseStep 644755 = 967133) B967133
theorem B448199 : Blo 103782 448199 := bstep (se 1 (by rfl) ⟨336149, by rfl⟩ : syracuseStep 448199 = 672299) B672299
theorem B513911 : Blo 103782 513911 := bstep (se 1 (by rfl) ⟨385433, by rfl⟩ : syracuseStep 513911 = 770867) B770867
theorem B415751 : Blo 103782 415751 := bstep (se 1 (by rfl) ⟨311813, by rfl⟩ : syracuseStep 415751 = 623627) B623627
theorem B120955 : Blo 103782 120955 := bstep (se 1 (by rfl) ⟨90716, by rfl⟩ : syracuseStep 120955 = 181433) B181433
theorem B383129 : Blo 103782 383129 := bstep (se 2 (by rfl) ⟨143673, by rfl⟩ : syracuseStep 383129 = 287347) B287347
theorem B317611 : Blo 103782 317611 := bstep (se 1 (by rfl) ⟨238208, by rfl⟩ : syracuseStep 317611 = 476417) B476417
theorem B809189 : Blo 103782 809189 := bstep (se 4 (by rfl) ⟨75861, by rfl⟩ : syracuseStep 809189 = 151723) B151723
theorem B1038743 : Blo 103782 1038743 := bstep (se 1 (by rfl) ⟨779057, by rfl⟩ : syracuseStep 1038743 = 1558115) B1558115
theorem B350729 : Blo 103782 350729 := bstep (se 2 (by rfl) ⟨131523, by rfl⟩ : syracuseStep 350729 = 263047) B263047
theorem B2611997 : Blo 103782 2611997 := bstep (se 3 (by rfl) ⟨489749, by rfl⟩ : syracuseStep 2611997 = 979499) B979499
theorem B187355 : Blo 103782 187355 := bstep (se 1 (by rfl) ⟨140516, by rfl⟩ : syracuseStep 187355 = 281033) B281033
theorem B941401 : Blo 103782 941401 := bstep (se 2 (by rfl) ⟨353025, by rfl⟩ : syracuseStep 941401 = 706051) B706051
theorem B351593 : Blo 103782 351593 := bstep (se 2 (by rfl) ⟨131847, by rfl⟩ : syracuseStep 351593 = 263695) B263695
theorem B1006991 : Blo 103782 1006991 := bstep (se 1 (by rfl) ⟨755243, by rfl⟩ : syracuseStep 1006991 = 1510487) B1510487
theorem B188335 : Blo 103782 188335 := bstep (se 1 (by rfl) ⟨141251, by rfl⟩ : syracuseStep 188335 = 282503) B282503
theorem B352187 : Blo 103782 352187 := bstep (se 1 (by rfl) ⟨264140, by rfl⟩ : syracuseStep 352187 = 528281) B528281
theorem B155687 : Blo 103782 155687 := bstep (se 1 (by rfl) ⟨116765, by rfl⟩ : syracuseStep 155687 = 233531) B233531
theorem B155771 : Blo 103782 155771 := bstep (se 1 (by rfl) ⟨116828, by rfl⟩ : syracuseStep 155771 = 233657) B233657
theorem B1466545 : Blo 103782 1466545 := bstep (se 2 (by rfl) ⟨549954, by rfl⟩ : syracuseStep 1466545 = 1099909) B1099909
theorem B155897 : Blo 103782 155897 := bstep (se 2 (by rfl) ⟨58461, by rfl⟩ : syracuseStep 155897 = 116923) B116923
theorem B155999 : Blo 103782 155999 := bstep (se 1 (by rfl) ⟨116999, by rfl⟩ : syracuseStep 155999 = 233999) B233999
theorem B156011 : Blo 103782 156011 := bstep (se 1 (by rfl) ⟨117008, by rfl⟩ : syracuseStep 156011 = 234017) B234017
theorem B156239 : Blo 103782 156239 := bstep (se 1 (by rfl) ⟨117179, by rfl⟩ : syracuseStep 156239 = 234359) B234359
theorem B156359 : Blo 103782 156359 := bstep (se 1 (by rfl) ⟨117269, by rfl⟩ : syracuseStep 156359 = 234539) B234539
theorem B156521 : Blo 103782 156521 := bstep (se 2 (by rfl) ⟨58695, by rfl⟩ : syracuseStep 156521 = 117391) B117391
theorem B156599 : Blo 103782 156599 := bstep (se 1 (by rfl) ⟨117449, by rfl⟩ : syracuseStep 156599 = 234899) B234899
theorem B156635 : Blo 103782 156635 := bstep (se 1 (by rfl) ⟨117476, by rfl⟩ : syracuseStep 156635 = 234953) B234953
theorem B1729781 : Blo 103782 1729781 := bstep (se 5 (by rfl) ⟨81083, by rfl⟩ : syracuseStep 1729781 = 162167) B162167
theorem B189791 : Blo 103782 189791 := bstep (se 1 (by rfl) ⟨142343, by rfl⟩ : syracuseStep 189791 = 284687) B284687
theorem B484733 : Blo 103782 484733 := bstep (se 3 (by rfl) ⟨90887, by rfl⟩ : syracuseStep 484733 = 181775) B181775
theorem B157103 : Blo 103782 157103 := bstep (se 1 (by rfl) ⟨117827, by rfl⟩ : syracuseStep 157103 = 235655) B235655
theorem B1500677 : Blo 103782 1500677 := bstep (se 4 (by rfl) ⟨140688, by rfl⟩ : syracuseStep 1500677 = 281377) B281377
theorem B1205765 : Blo 103782 1205765 := bstep (se 4 (by rfl) ⟨113040, by rfl⟩ : syracuseStep 1205765 = 226081) B226081
theorem B157193 : Blo 103782 157193 := bstep (se 2 (by rfl) ⟨58947, by rfl⟩ : syracuseStep 157193 = 117895) B117895
theorem B157223 : Blo 103782 157223 := bstep (se 1 (by rfl) ⟨117917, by rfl⟩ : syracuseStep 157223 = 235835) B235835
theorem B353915 : Blo 103782 353915 := bstep (se 1 (by rfl) ⟨265436, by rfl⟩ : syracuseStep 353915 = 530873) B530873
theorem B157307 : Blo 103782 157307 := bstep (se 1 (by rfl) ⟨117980, by rfl⟩ : syracuseStep 157307 = 235961) B235961
theorem B157433 : Blo 103782 157433 := bstep (se 2 (by rfl) ⟨59037, by rfl⟩ : syracuseStep 157433 = 118075) B118075
theorem B354077 : Blo 103782 354077 := bstep (se 3 (by rfl) ⟨66389, by rfl⟩ : syracuseStep 354077 = 132779) B132779
theorem B812843 : Blo 103782 812843 := bstep (se 1 (by rfl) ⟨609632, by rfl⟩ : syracuseStep 812843 = 1219265) B1219265
theorem B157535 : Blo 103782 157535 := bstep (se 1 (by rfl) ⟨118151, by rfl⟩ : syracuseStep 157535 = 236303) B236303
theorem B157547 : Blo 103782 157547 := bstep (se 1 (by rfl) ⟨118160, by rfl⟩ : syracuseStep 157547 = 236321) B236321
theorem B157775 : Blo 103782 157775 := bstep (se 1 (by rfl) ⟨118331, by rfl⟩ : syracuseStep 157775 = 236663) B236663
theorem B157895 : Blo 103782 157895 := bstep (se 1 (by rfl) ⟨118421, by rfl⟩ : syracuseStep 157895 = 236843) B236843
theorem B158057 : Blo 103782 158057 := bstep (se 2 (by rfl) ⟨59271, by rfl⟩ : syracuseStep 158057 = 118543) B118543
theorem B158135 : Blo 103782 158135 := bstep (se 1 (by rfl) ⟨118601, by rfl⟩ : syracuseStep 158135 = 237203) B237203
theorem B354779 : Blo 103782 354779 := bstep (se 1 (by rfl) ⟨266084, by rfl⟩ : syracuseStep 354779 = 532169) B532169
theorem B158171 : Blo 103782 158171 := bstep (se 1 (by rfl) ⟨118628, by rfl⟩ : syracuseStep 158171 = 237257) B237257
theorem B748091 : Blo 103782 748091 := bstep (se 1 (by rfl) ⟨561068, by rfl⟩ : syracuseStep 748091 = 1122137) B1122137
theorem B387773 : Blo 103782 387773 := bstep (se 3 (by rfl) ⟨72707, by rfl⟩ : syracuseStep 387773 = 145415) B145415
theorem B223955 : Blo 103782 223955 := bstep (se 1 (by rfl) ⟨167966, by rfl⟩ : syracuseStep 223955 = 335933) B335933
theorem B3337037 : Blo 103782 3337037 := bstep (se 3 (by rfl) ⟨625694, by rfl⟩ : syracuseStep 3337037 = 1251389) B1251389
theorem B158639 : Blo 103782 158639 := bstep (se 1 (by rfl) ⟨118979, by rfl⟩ : syracuseStep 158639 = 237959) B237959
theorem B1207223 : Blo 103782 1207223 := bstep (se 1 (by rfl) ⟨905417, by rfl⟩ : syracuseStep 1207223 = 1810835) B1810835
theorem B158729 : Blo 103782 158729 := bstep (se 2 (by rfl) ⟨59523, by rfl⟩ : syracuseStep 158729 = 119047) B119047
theorem B158759 : Blo 103782 158759 := bstep (se 1 (by rfl) ⟨119069, by rfl⟩ : syracuseStep 158759 = 238139) B238139
theorem B158843 : Blo 103782 158843 := bstep (se 1 (by rfl) ⟨119132, by rfl⟩ : syracuseStep 158843 = 238265) B238265
theorem B355481 : Blo 103782 355481 := bstep (se 2 (by rfl) ⟨133305, by rfl⟩ : syracuseStep 355481 = 266611) B266611
theorem B158969 : Blo 103782 158969 := bstep (se 2 (by rfl) ⟨59613, by rfl⟩ : syracuseStep 158969 = 119227) B119227
theorem B191737 : Blo 103782 191737 := bstep (se 2 (by rfl) ⟨71901, by rfl⟩ : syracuseStep 191737 = 143803) B143803
theorem B159071 : Blo 103782 159071 := bstep (se 1 (by rfl) ⟨119303, by rfl⟩ : syracuseStep 159071 = 238607) B238607
theorem B159083 : Blo 103782 159083 := bstep (se 1 (by rfl) ⟨119312, by rfl⟩ : syracuseStep 159083 = 238625) B238625
theorem B159311 : Blo 103782 159311 := bstep (se 1 (by rfl) ⟨119483, by rfl⟩ : syracuseStep 159311 = 238967) B238967
theorem B58453589 : Blo 103782 58453589 := bstep (se 8 (by rfl) ⟨342501, by rfl⟩ : syracuseStep 58453589 = 685003) B685003
theorem B159431 : Blo 103782 159431 := bstep (se 1 (by rfl) ⟨119573, by rfl⟩ : syracuseStep 159431 = 239147) B239147
theorem B159593 : Blo 103782 159593 := bstep (se 2 (by rfl) ⟨59847, by rfl⟩ : syracuseStep 159593 = 119695) B119695
theorem B257899 : Blo 103782 257899 := bstep (se 1 (by rfl) ⟨193424, by rfl⟩ : syracuseStep 257899 = 386849) B386849
theorem B159671 : Blo 103782 159671 := bstep (se 1 (by rfl) ⟨119753, by rfl⟩ : syracuseStep 159671 = 239507) B239507
theorem B683963 : Blo 103782 683963 := bstep (se 1 (by rfl) ⟨512972, by rfl⟩ : syracuseStep 683963 = 1025945) B1025945
theorem B159707 : Blo 103782 159707 := bstep (se 1 (by rfl) ⟨119780, by rfl⟩ : syracuseStep 159707 = 239561) B239561
theorem B618653 : Blo 103782 618653 := bstep (se 3 (by rfl) ⟨115997, by rfl⟩ : syracuseStep 618653 = 231995) B231995
theorem B356669 : Blo 103782 356669 := bstep (se 3 (by rfl) ⟨66875, by rfl⟩ : syracuseStep 356669 = 133751) B133751
theorem B455017 : Blo 103782 455017 := bstep (se 2 (by rfl) ⟨170631, by rfl⟩ : syracuseStep 455017 = 341263) B341263
theorem B160175 : Blo 103782 160175 := bstep (se 1 (by rfl) ⟨120131, by rfl⟩ : syracuseStep 160175 = 240263) B240263
theorem B160265 : Blo 103782 160265 := bstep (se 2 (by rfl) ⟨60099, by rfl⟩ : syracuseStep 160265 = 120199) B120199
theorem B160295 : Blo 103782 160295 := bstep (se 1 (by rfl) ⟨120221, by rfl⟩ : syracuseStep 160295 = 240443) B240443
theorem B193121 : Blo 103782 193121 := bstep (se 2 (by rfl) ⟨72420, by rfl⟩ : syracuseStep 193121 = 144841) B144841
theorem B160379 : Blo 103782 160379 := bstep (se 1 (by rfl) ⟨120284, by rfl⟩ : syracuseStep 160379 = 240569) B240569
theorem B160505 : Blo 103782 160505 := bstep (se 2 (by rfl) ⟨60189, by rfl⟩ : syracuseStep 160505 = 120379) B120379
theorem B160607 : Blo 103782 160607 := bstep (se 1 (by rfl) ⟨120455, by rfl⟩ : syracuseStep 160607 = 240911) B240911
theorem B160619 : Blo 103782 160619 := bstep (se 1 (by rfl) ⟨120464, by rfl⟩ : syracuseStep 160619 = 240929) B240929
theorem B160847 : Blo 103782 160847 := bstep (se 1 (by rfl) ⟨120635, by rfl⟩ : syracuseStep 160847 = 241271) B241271
theorem B357533 : Blo 103782 357533 := bstep (se 3 (by rfl) ⟨67037, by rfl⟩ : syracuseStep 357533 = 134075) B134075
theorem B160967 : Blo 103782 160967 := bstep (se 1 (by rfl) ⟨120725, by rfl⟩ : syracuseStep 160967 = 241451) B241451
theorem B2880715 : Blo 103782 2880715 := bstep (se 1 (by rfl) ⟨2160536, by rfl⟩ : syracuseStep 2880715 = 4321073) B4321073
theorem B161129 : Blo 103782 161129 := bstep (se 2 (by rfl) ⟨60423, by rfl⟩ : syracuseStep 161129 = 120847) B120847
theorem B3536243 : Blo 103782 3536243 := bstep (se 1 (by rfl) ⟨2652182, by rfl⟩ : syracuseStep 3536243 = 5304365) B5304365
theorem B3339667 : Blo 103782 3339667 := bstep (se 1 (by rfl) ⟨2504750, by rfl⟩ : syracuseStep 3339667 = 5009501) B5009501
theorem B161207 : Blo 103782 161207 := bstep (se 1 (by rfl) ⟨120905, by rfl⟩ : syracuseStep 161207 = 241811) B241811
theorem B161243 : Blo 103782 161243 := bstep (se 1 (by rfl) ⟨120932, by rfl⟩ : syracuseStep 161243 = 241865) B241865
theorem B358073 : Blo 103782 358073 := bstep (se 2 (by rfl) ⟨134277, by rfl⟩ : syracuseStep 358073 = 268555) B268555
theorem B325309 : Blo 103782 325309 := bstep (se 3 (by rfl) ⟨60995, by rfl⟩ : syracuseStep 325309 = 121991) B121991
theorem B718625 : Blo 103782 718625 := bstep (se 2 (by rfl) ⟨269484, by rfl⟩ : syracuseStep 718625 = 538969) B538969
theorem B358187 : Blo 103782 358187 := bstep (se 1 (by rfl) ⟨268640, by rfl⟩ : syracuseStep 358187 = 537281) B537281
theorem B915259 : Blo 103782 915259 := bstep (se 1 (by rfl) ⟨686444, by rfl⟩ : syracuseStep 915259 = 1372889) B1372889
theorem B358667 : Blo 103782 358667 := bstep (se 1 (by rfl) ⟨269000, by rfl⟩ : syracuseStep 358667 = 538001) B538001
theorem B522625 : Blo 103782 522625 := bstep (se 2 (by rfl) ⟨195984, by rfl⟩ : syracuseStep 522625 = 391969) B391969
theorem B1440185 : Blo 103782 1440185 := bstep (se 2 (by rfl) ⟨540069, by rfl⟩ : syracuseStep 1440185 = 1080139) B1080139
theorem B358937 : Blo 103782 358937 := bstep (se 2 (by rfl) ⟨134601, by rfl⟩ : syracuseStep 358937 = 269203) B269203
theorem B490009 : Blo 103782 490009 := bstep (se 2 (by rfl) ⟨183753, by rfl⟩ : syracuseStep 490009 = 367507) B367507
theorem B195283 : Blo 103782 195283 := bstep (se 1 (by rfl) ⟨146462, by rfl⟩ : syracuseStep 195283 = 292925) B292925
theorem B818423 : Blo 103782 818423 := bstep (se 1 (by rfl) ⟨613817, by rfl⟩ : syracuseStep 818423 = 1227635) B1227635
theorem B1015213 : Blo 103782 1015213 := bstep (se 3 (by rfl) ⟨190352, by rfl⟩ : syracuseStep 1015213 = 380705) B380705
theorem B360071 : Blo 103782 360071 := bstep (se 1 (by rfl) ⟨270053, by rfl⟩ : syracuseStep 360071 = 540107) B540107
theorem B360125 : Blo 103782 360125 := bstep (se 3 (by rfl) ⟨67523, by rfl⟩ : syracuseStep 360125 = 135047) B135047
theorem B360287 : Blo 103782 360287 := bstep (se 1 (by rfl) ⟨270215, by rfl⟩ : syracuseStep 360287 = 540431) B540431
theorem B197183 : Blo 103782 197183 := bstep (se 1 (by rfl) ⟨147887, by rfl⟩ : syracuseStep 197183 = 295775) B295775
theorem B754379 : Blo 103782 754379 := bstep (se 1 (by rfl) ⟨565784, by rfl⟩ : syracuseStep 754379 = 1131569) B1131569
theorem B131807 : Blo 103782 131807 := bstep (se 1 (by rfl) ⟨98855, by rfl⟩ : syracuseStep 131807 = 197711) B197711
theorem B459715 : Blo 103782 459715 := bstep (se 1 (by rfl) ⟨344786, by rfl⟩ : syracuseStep 459715 = 689573) B689573
theorem B263159 : Blo 103782 263159 := bstep (se 1 (by rfl) ⟨197369, by rfl⟩ : syracuseStep 263159 = 394739) B394739
theorem B492551 : Blo 103782 492551 := bstep (se 1 (by rfl) ⟨369413, by rfl⟩ : syracuseStep 492551 = 738827) B738827
theorem B525527 : Blo 103782 525527 := bstep (se 1 (by rfl) ⟨394145, by rfl⟩ : syracuseStep 525527 = 788291) B788291
theorem B1017137 : Blo 103782 1017137 := bstep (se 2 (by rfl) ⟨381426, by rfl⟩ : syracuseStep 1017137 = 762853) B762853
theorem B951695 : Blo 103782 951695 := bstep (se 1 (by rfl) ⟨713771, by rfl⟩ : syracuseStep 951695 = 1427543) B1427543
theorem B198227 : Blo 103782 198227 := bstep (se 1 (by rfl) ⟨148670, by rfl⟩ : syracuseStep 198227 = 297341) B297341
theorem B296635 : Blo 103782 296635 := bstep (se 1 (by rfl) ⟨222476, by rfl⟩ : syracuseStep 296635 = 444953) B444953
theorem B198379 : Blo 103782 198379 := bstep (se 1 (by rfl) ⟨148784, by rfl⟩ : syracuseStep 198379 = 297569) B297569
theorem B198607 : Blo 103782 198607 := bstep (se 1 (by rfl) ⟨148955, by rfl⟩ : syracuseStep 198607 = 297911) B297911
theorem B362447 : Blo 103782 362447 := bstep (se 1 (by rfl) ⟨271835, by rfl⟩ : syracuseStep 362447 = 543671) B543671
theorem B919633 : Blo 103782 919633 := bstep (se 2 (by rfl) ⟨344862, by rfl⟩ : syracuseStep 919633 = 689725) B689725
theorem B887375 : Blo 103782 887375 := bstep (se 1 (by rfl) ⟨665531, by rfl⟩ : syracuseStep 887375 = 1331063) B1331063
theorem B133807 : Blo 103782 133807 := bstep (se 1 (by rfl) ⟨100355, by rfl⟩ : syracuseStep 133807 = 200711) B200711
theorem B199351 : Blo 103782 199351 := bstep (se 1 (by rfl) ⟨149513, by rfl⟩ : syracuseStep 199351 = 299027) B299027
theorem B265103 : Blo 103782 265103 := bstep (se 1 (by rfl) ⟨198827, by rfl⟩ : syracuseStep 265103 = 397655) B397655
theorem B199579 : Blo 103782 199579 := bstep (se 1 (by rfl) ⟨149684, by rfl⟩ : syracuseStep 199579 = 299369) B299369
theorem B363419 : Blo 103782 363419 := bstep (se 1 (by rfl) ⟨272564, by rfl⟩ : syracuseStep 363419 = 545129) B545129
theorem B199655 : Blo 103782 199655 := bstep (se 1 (by rfl) ⟨149741, by rfl⟩ : syracuseStep 199655 = 299483) B299483
theorem B920591 : Blo 103782 920591 := bstep (se 1 (by rfl) ⟨690443, by rfl⟩ : syracuseStep 920591 = 1380887) B1380887
theorem B265511 : Blo 103782 265511 := bstep (se 1 (by rfl) ⟨199133, by rfl⟩ : syracuseStep 265511 = 398267) B398267
theorem B265963 : Blo 103782 265963 := bstep (se 1 (by rfl) ⟨199472, by rfl⟩ : syracuseStep 265963 = 398945) B398945
theorem B298799 : Blo 103782 298799 := bstep (se 1 (by rfl) ⟨224099, by rfl⟩ : syracuseStep 298799 = 448199) B448199
theorem B528443 : Blo 103782 528443 := bstep (se 1 (by rfl) ⟨396332, by rfl⟩ : syracuseStep 528443 = 792665) B792665
theorem B200809 : Blo 103782 200809 := bstep (se 2 (by rfl) ⟨75303, by rfl⟩ : syracuseStep 200809 = 150607) B150607
theorem B692495 : Blo 103782 692495 := bstep (se 1 (by rfl) ⟨519371, by rfl⟩ : syracuseStep 692495 = 1038743) B1038743
theorem B233801 : Blo 103782 233801 := bstep (se 2 (by rfl) ⟨87675, by rfl⟩ : syracuseStep 233801 = 175351) B175351
theorem B233819 : Blo 103782 233819 := bstep (se 1 (by rfl) ⟨175364, by rfl⟩ : syracuseStep 233819 = 350729) B350729
theorem B1741331 : Blo 103782 1741331 := bstep (se 1 (by rfl) ⟨1305998, by rfl⟩ : syracuseStep 1741331 = 2611997) B2611997
theorem B135751 : Blo 103782 135751 := bstep (se 1 (by rfl) ⟨101813, by rfl⟩ : syracuseStep 135751 = 203627) B203627
theorem B856673 : Blo 103782 856673 := bstep (se 2 (by rfl) ⟨321252, by rfl⟩ : syracuseStep 856673 = 642505) B642505
theorem B266935 : Blo 103782 266935 := bstep (se 1 (by rfl) ⟨200201, by rfl⟩ : syracuseStep 266935 = 400403) B400403
theorem B955165 : Blo 103782 955165 := bstep (se 3 (by rfl) ⟨179093, by rfl⟩ : syracuseStep 955165 = 358187) B358187
theorem B234395 : Blo 103782 234395 := bstep (se 1 (by rfl) ⟨175796, by rfl⟩ : syracuseStep 234395 = 351593) B351593
theorem B267239 : Blo 103782 267239 := bstep (se 1 (by rfl) ⟨200429, by rfl⟩ : syracuseStep 267239 = 400859) B400859
theorem B529415 : Blo 103782 529415 := bstep (se 1 (by rfl) ⟨397061, by rfl⟩ : syracuseStep 529415 = 794123) B794123
theorem B234593 : Blo 103782 234593 := bstep (se 2 (by rfl) ⟨87972, by rfl⟩ : syracuseStep 234593 = 175945) B175945
theorem B234791 : Blo 103782 234791 := bstep (se 1 (by rfl) ⟨176093, by rfl⟩ : syracuseStep 234791 = 352187) B352187
theorem B595295 : Blo 103782 595295 := bstep (se 1 (by rfl) ⟨446471, by rfl⟩ : syracuseStep 595295 = 892943) B892943
theorem B103791 : Blo 103782 103791 := bstep (se 1 (by rfl) ⟨77843, by rfl⟩ : syracuseStep 103791 = 155687) B155687
theorem B103847 : Blo 103782 103847 := bstep (se 1 (by rfl) ⟨77885, by rfl⟩ : syracuseStep 103847 = 155771) B155771
theorem B529901 : Blo 103782 529901 := bstep (se 3 (by rfl) ⟨99356, by rfl⟩ : syracuseStep 529901 = 198713) B198713
theorem B103931 : Blo 103782 103931 := bstep (se 1 (by rfl) ⟨77948, by rfl⟩ : syracuseStep 103931 = 155897) B155897
theorem B103999 : Blo 103782 103999 := bstep (se 1 (by rfl) ⟨77999, by rfl⟩ : syracuseStep 103999 = 155999) B155999
theorem B104007 : Blo 103782 104007 := bstep (se 1 (by rfl) ⟨78005, by rfl⟩ : syracuseStep 104007 = 156011) B156011
theorem B235169 : Blo 103782 235169 := bstep (se 2 (by rfl) ⟨88188, by rfl⟩ : syracuseStep 235169 = 176377) B176377
theorem B202427 : Blo 103782 202427 := bstep (se 1 (by rfl) ⟨151820, by rfl⟩ : syracuseStep 202427 = 303641) B303641
theorem B104159 : Blo 103782 104159 := bstep (se 1 (by rfl) ⟨78119, by rfl⟩ : syracuseStep 104159 = 156239) B156239
theorem B104239 : Blo 103782 104239 := bstep (se 1 (by rfl) ⟨78179, by rfl⟩ : syracuseStep 104239 = 156359) B156359
theorem B104347 : Blo 103782 104347 := bstep (se 1 (by rfl) ⟨78260, by rfl⟩ : syracuseStep 104347 = 156521) B156521
theorem B104399 : Blo 103782 104399 := bstep (se 1 (by rfl) ⟨78299, by rfl⟩ : syracuseStep 104399 = 156599) B156599
theorem B104423 : Blo 103782 104423 := bstep (se 1 (by rfl) ⟨78317, by rfl⟩ : syracuseStep 104423 = 156635) B156635
theorem B235529 : Blo 103782 235529 := bstep (se 2 (by rfl) ⟨88323, by rfl⟩ : syracuseStep 235529 = 176647) B176647
theorem B268393 : Blo 103782 268393 := bstep (se 2 (by rfl) ⟨100647, by rfl⟩ : syracuseStep 268393 = 201295) B201295
theorem B1153187 : Blo 103782 1153187 := bstep (se 1 (by rfl) ⟨864890, by rfl⟩ : syracuseStep 1153187 = 1729781) B1729781
theorem B399613 : Blo 103782 399613 := bstep (se 3 (by rfl) ⟨74927, by rfl⟩ : syracuseStep 399613 = 149855) B149855
theorem B530711 : Blo 103782 530711 := bstep (se 1 (by rfl) ⟨398033, by rfl⟩ : syracuseStep 530711 = 796067) B796067
theorem B104735 : Blo 103782 104735 := bstep (se 1 (by rfl) ⟨78551, by rfl⟩ : syracuseStep 104735 = 157103) B157103
theorem B104795 : Blo 103782 104795 := bstep (se 1 (by rfl) ⟨78596, by rfl⟩ : syracuseStep 104795 = 157193) B157193
theorem B104815 : Blo 103782 104815 := bstep (se 1 (by rfl) ⟨78611, by rfl⟩ : syracuseStep 104815 = 157223) B157223
theorem B465263 : Blo 103782 465263 := bstep (se 1 (by rfl) ⟨348947, by rfl⟩ : syracuseStep 465263 = 697895) B697895
theorem B235943 : Blo 103782 235943 := bstep (se 1 (by rfl) ⟨176957, by rfl⟩ : syracuseStep 235943 = 353915) B353915
theorem B104871 : Blo 103782 104871 := bstep (se 1 (by rfl) ⟨78653, by rfl⟩ : syracuseStep 104871 = 157307) B157307
theorem B1841591 : Blo 103782 1841591 := bstep (se 1 (by rfl) ⟨1381193, by rfl⟩ : syracuseStep 1841591 = 2762387) B2762387
theorem B3840493 : Blo 103782 3840493 := bstep (se 3 (by rfl) ⟨720092, by rfl⟩ : syracuseStep 3840493 = 1440185) B1440185
theorem B334331 : Blo 103782 334331 := bstep (se 1 (by rfl) ⟨250748, by rfl⟩ : syracuseStep 334331 = 501497) B501497
theorem B104955 : Blo 103782 104955 := bstep (se 1 (by rfl) ⟨78716, by rfl⟩ : syracuseStep 104955 = 157433) B157433
theorem B236051 : Blo 103782 236051 := bstep (se 1 (by rfl) ⟨177038, by rfl⟩ : syracuseStep 236051 = 354077) B354077
theorem B793151 : Blo 103782 793151 := bstep (se 1 (by rfl) ⟨594863, by rfl⟩ : syracuseStep 793151 = 1189727) B1189727
theorem B105023 : Blo 103782 105023 := bstep (se 1 (by rfl) ⟨78767, by rfl⟩ : syracuseStep 105023 = 157535) B157535
theorem B105031 : Blo 103782 105031 := bstep (se 1 (by rfl) ⟨78773, by rfl⟩ : syracuseStep 105031 = 157547) B157547
theorem B236105 : Blo 103782 236105 := bstep (se 2 (by rfl) ⟨88539, by rfl⟩ : syracuseStep 236105 = 177079) B177079
theorem B268879 : Blo 103782 268879 := bstep (se 1 (by rfl) ⟨201659, by rfl⟩ : syracuseStep 268879 = 403319) B403319
theorem B105183 : Blo 103782 105183 := bstep (se 1 (by rfl) ⟨78887, by rfl⟩ : syracuseStep 105183 = 157775) B157775
theorem B105263 : Blo 103782 105263 := bstep (se 1 (by rfl) ⟨78947, by rfl⟩ : syracuseStep 105263 = 157895) B157895
theorem B105371 : Blo 103782 105371 := bstep (se 1 (by rfl) ⟨79028, by rfl⟩ : syracuseStep 105371 = 158057) B158057
theorem B3840953 : Blo 103782 3840953 := bstep (se 2 (by rfl) ⟨1440357, by rfl⟩ : syracuseStep 3840953 = 2880715) B2880715
theorem B105423 : Blo 103782 105423 := bstep (se 1 (by rfl) ⟨79067, by rfl⟩ : syracuseStep 105423 = 158135) B158135
theorem B236519 : Blo 103782 236519 := bstep (se 1 (by rfl) ⟨177389, by rfl⟩ : syracuseStep 236519 = 354779) B354779
theorem B105447 : Blo 103782 105447 := bstep (se 1 (by rfl) ⟨79085, by rfl⟩ : syracuseStep 105447 = 158171) B158171
theorem B498727 : Blo 103782 498727 := bstep (se 1 (by rfl) ⟨374045, by rfl⟩ : syracuseStep 498727 = 748091) B748091
theorem B5020805 : Blo 103782 5020805 := bstep (se 4 (by rfl) ⟨470700, by rfl⟩ : syracuseStep 5020805 = 941401) B941401
theorem B269527 : Blo 103782 269527 := bstep (se 1 (by rfl) ⟨202145, by rfl⟩ : syracuseStep 269527 = 404291) B404291
theorem B105759 : Blo 103782 105759 := bstep (se 1 (by rfl) ⟨79319, by rfl⟩ : syracuseStep 105759 = 158639) B158639
theorem B105819 : Blo 103782 105819 := bstep (se 1 (by rfl) ⟨79364, by rfl⟩ : syracuseStep 105819 = 158729) B158729
theorem B236897 : Blo 103782 236897 := bstep (se 2 (by rfl) ⟨88836, by rfl⟩ : syracuseStep 236897 = 177673) B177673
theorem B105839 : Blo 103782 105839 := bstep (se 1 (by rfl) ⟨79379, by rfl⟩ : syracuseStep 105839 = 158759) B158759
theorem B105895 : Blo 103782 105895 := bstep (se 1 (by rfl) ⟨79421, by rfl⟩ : syracuseStep 105895 = 158843) B158843
theorem B236987 : Blo 103782 236987 := bstep (se 1 (by rfl) ⟨177740, by rfl⟩ : syracuseStep 236987 = 355481) B355481
theorem B1449431 : Blo 103782 1449431 := bstep (se 1 (by rfl) ⟨1087073, by rfl⟩ : syracuseStep 1449431 = 2174147) B2174147
theorem B400889 : Blo 103782 400889 := bstep (se 2 (by rfl) ⟨150333, by rfl⟩ : syracuseStep 400889 = 300667) B300667
theorem B105979 : Blo 103782 105979 := bstep (se 1 (by rfl) ⟨79484, by rfl⟩ : syracuseStep 105979 = 158969) B158969
theorem B269831 : Blo 103782 269831 := bstep (se 1 (by rfl) ⟨202373, by rfl⟩ : syracuseStep 269831 = 404747) B404747
theorem B859673 : Blo 103782 859673 := bstep (se 2 (by rfl) ⟨322377, by rfl⟩ : syracuseStep 859673 = 644755) B644755
theorem B237113 : Blo 103782 237113 := bstep (se 2 (by rfl) ⟨88917, by rfl⟩ : syracuseStep 237113 = 177835) B177835
theorem B106047 : Blo 103782 106047 := bstep (se 1 (by rfl) ⟨79535, by rfl⟩ : syracuseStep 106047 = 159071) B159071
theorem B106055 : Blo 103782 106055 := bstep (se 1 (by rfl) ⟨79541, by rfl⟩ : syracuseStep 106055 = 159083) B159083
theorem B433745 : Blo 103782 433745 := bstep (se 2 (by rfl) ⟨162654, by rfl⟩ : syracuseStep 433745 = 325309) B325309
theorem B401057 : Blo 103782 401057 := bstep (se 2 (by rfl) ⟨150396, by rfl⟩ : syracuseStep 401057 = 300793) B300793
theorem B106207 : Blo 103782 106207 := bstep (se 1 (by rfl) ⟨79655, by rfl⟩ : syracuseStep 106207 = 159311) B159311
theorem B38969059 : Blo 103782 38969059 := bstep (se 1 (by rfl) ⟨29226794, by rfl⟩ : syracuseStep 38969059 = 58453589) B58453589
theorem B1220345 : Blo 103782 1220345 := bstep (se 2 (by rfl) ⟨457629, by rfl⟩ : syracuseStep 1220345 = 915259) B915259
theorem B106287 : Blo 103782 106287 := bstep (se 1 (by rfl) ⟨79715, by rfl⟩ : syracuseStep 106287 = 159431) B159431
theorem B204599 : Blo 103782 204599 := bstep (se 1 (by rfl) ⟨153449, by rfl⟩ : syracuseStep 204599 = 306899) B306899
theorem B532331 : Blo 103782 532331 := bstep (se 1 (by rfl) ⟨399248, by rfl⟩ : syracuseStep 532331 = 798497) B798497
theorem B106395 : Blo 103782 106395 := bstep (se 1 (by rfl) ⟨79796, by rfl⟩ : syracuseStep 106395 = 159593) B159593
theorem B106447 : Blo 103782 106447 := bstep (se 1 (by rfl) ⟨79835, by rfl⟩ : syracuseStep 106447 = 159671) B159671
theorem B270287 : Blo 103782 270287 := bstep (se 1 (by rfl) ⟨202715, by rfl⟩ : syracuseStep 270287 = 405431) B405431
theorem B106471 : Blo 103782 106471 := bstep (se 1 (by rfl) ⟨79853, by rfl⟩ : syracuseStep 106471 = 159707) B159707
theorem B4301009 : Blo 103782 4301009 := bstep (se 2 (by rfl) ⟨1612878, by rfl⟩ : syracuseStep 4301009 = 3225757) B3225757
theorem B237779 : Blo 103782 237779 := bstep (se 1 (by rfl) ⟨178334, by rfl⟩ : syracuseStep 237779 = 356669) B356669
theorem B237833 : Blo 103782 237833 := bstep (se 2 (by rfl) ⟨89187, by rfl⟩ : syracuseStep 237833 = 178375) B178375
theorem B106783 : Blo 103782 106783 := bstep (se 1 (by rfl) ⟨80087, by rfl⟩ : syracuseStep 106783 = 160175) B160175
theorem B106843 : Blo 103782 106843 := bstep (se 1 (by rfl) ⟨80132, by rfl⟩ : syracuseStep 106843 = 160265) B160265
theorem B106863 : Blo 103782 106863 := bstep (se 1 (by rfl) ⟨80147, by rfl⟩ : syracuseStep 106863 = 160295) B160295
theorem B106919 : Blo 103782 106919 := bstep (se 1 (by rfl) ⟨80189, by rfl⟩ : syracuseStep 106919 = 160379) B160379
theorem B270803 : Blo 103782 270803 := bstep (se 1 (by rfl) ⟨203102, by rfl⟩ : syracuseStep 270803 = 406205) B406205
theorem B238049 : Blo 103782 238049 := bstep (se 2 (by rfl) ⟨89268, by rfl⟩ : syracuseStep 238049 = 178537) B178537
theorem B107003 : Blo 103782 107003 := bstep (se 1 (by rfl) ⟨80252, by rfl⟩ : syracuseStep 107003 = 160505) B160505
theorem B696833 : Blo 103782 696833 := bstep (se 2 (by rfl) ⟨261312, by rfl⟩ : syracuseStep 696833 = 522625) B522625
theorem B6758923 : Blo 103782 6758923 := bstep (se 1 (by rfl) ⟨5069192, by rfl⟩ : syracuseStep 6758923 = 10138385) B10138385
theorem B107071 : Blo 103782 107071 := bstep (se 1 (by rfl) ⟨80303, by rfl⟩ : syracuseStep 107071 = 160607) B160607
theorem B107079 : Blo 103782 107079 := bstep (se 1 (by rfl) ⟨80309, by rfl⟩ : syracuseStep 107079 = 160619) B160619
theorem B107231 : Blo 103782 107231 := bstep (se 1 (by rfl) ⟨80423, by rfl⟩ : syracuseStep 107231 = 160847) B160847
theorem B238355 : Blo 103782 238355 := bstep (se 1 (by rfl) ⟨178766, by rfl⟩ : syracuseStep 238355 = 357533) B357533
theorem B107311 : Blo 103782 107311 := bstep (se 1 (by rfl) ⟨80483, by rfl⟩ : syracuseStep 107311 = 160967) B160967
theorem B271259 : Blo 103782 271259 := bstep (se 1 (by rfl) ⟨203444, by rfl⟩ : syracuseStep 271259 = 406889) B406889
theorem B107419 : Blo 103782 107419 := bstep (se 1 (by rfl) ⟨80564, by rfl⟩ : syracuseStep 107419 = 161129) B161129
theorem B107471 : Blo 103782 107471 := bstep (se 1 (by rfl) ⟨80603, by rfl⟩ : syracuseStep 107471 = 161207) B161207
theorem B107495 : Blo 103782 107495 := bstep (se 1 (by rfl) ⟨80621, by rfl⟩ : syracuseStep 107495 = 161243) B161243
theorem B402529 : Blo 103782 402529 := bstep (se 2 (by rfl) ⟨150948, by rfl⟩ : syracuseStep 402529 = 301897) B301897
theorem B238715 : Blo 103782 238715 := bstep (se 1 (by rfl) ⟨179036, by rfl⟩ : syracuseStep 238715 = 358073) B358073
theorem B238841 : Blo 103782 238841 := bstep (se 2 (by rfl) ⟨89565, by rfl⟩ : syracuseStep 238841 = 179131) B179131
theorem B238985 : Blo 103782 238985 := bstep (se 2 (by rfl) ⟨89619, by rfl⟩ : syracuseStep 238985 = 179239) B179239
theorem B239111 : Blo 103782 239111 := bstep (se 1 (by rfl) ⟨179333, by rfl⟩ : syracuseStep 239111 = 358667) B358667
theorem B403001 : Blo 103782 403001 := bstep (se 2 (by rfl) ⟨151125, by rfl⟩ : syracuseStep 403001 = 302251) B302251
theorem B239291 : Blo 103782 239291 := bstep (se 1 (by rfl) ⟨179468, by rfl⟩ : syracuseStep 239291 = 358937) B358937
theorem B239417 : Blo 103782 239417 := bstep (se 2 (by rfl) ⟨89781, by rfl⟩ : syracuseStep 239417 = 179563) B179563
theorem B1353617 : Blo 103782 1353617 := bstep (se 2 (by rfl) ⟨507606, by rfl⟩ : syracuseStep 1353617 = 1015213) B1015213
theorem B272393 : Blo 103782 272393 := bstep (se 2 (by rfl) ⟨102147, by rfl⟩ : syracuseStep 272393 = 204295) B204295
theorem B272747 : Blo 103782 272747 := bstep (se 1 (by rfl) ⟨204560, by rfl⟩ : syracuseStep 272747 = 409121) B409121
theorem B797039 : Blo 103782 797039 := bstep (se 1 (by rfl) ⟨597779, by rfl⟩ : syracuseStep 797039 = 1195559) B1195559
theorem B240047 : Blo 103782 240047 := bstep (se 1 (by rfl) ⟨180035, by rfl⟩ : syracuseStep 240047 = 360071) B360071
theorem B240083 : Blo 103782 240083 := bstep (se 1 (by rfl) ⟨180062, by rfl⟩ : syracuseStep 240083 = 360125) B360125
theorem B240191 : Blo 103782 240191 := bstep (se 1 (by rfl) ⟨180143, by rfl⟩ : syracuseStep 240191 = 360287) B360287
theorem B240299 : Blo 103782 240299 := bstep (se 1 (by rfl) ⟨180224, by rfl⟩ : syracuseStep 240299 = 360449) B360449
theorem B240839 : Blo 103782 240839 := bstep (se 1 (by rfl) ⟨180629, by rfl⟩ : syracuseStep 240839 = 361259) B361259
theorem B241019 : Blo 103782 241019 := bstep (se 1 (by rfl) ⟨180764, by rfl⟩ : syracuseStep 241019 = 361529) B361529
theorem B536057 : Blo 103782 536057 := bstep (se 2 (by rfl) ⟨201021, by rfl⟩ : syracuseStep 536057 = 402043) B402043
theorem B241145 : Blo 103782 241145 := bstep (se 2 (by rfl) ⟨90429, by rfl⟩ : syracuseStep 241145 = 180859) B180859
theorem B241235 : Blo 103782 241235 := bstep (se 1 (by rfl) ⟨180926, by rfl⟩ : syracuseStep 241235 = 361853) B361853
theorem B241415 : Blo 103782 241415 := bstep (se 1 (by rfl) ⟨181061, by rfl⟩ : syracuseStep 241415 = 362123) B362123
theorem B536381 : Blo 103782 536381 := bstep (se 3 (by rfl) ⟨100571, by rfl⟩ : syracuseStep 536381 = 201143) B201143
theorem B1159069 : Blo 103782 1159069 := bstep (se 3 (by rfl) ⟨217325, by rfl⟩ : syracuseStep 1159069 = 434651) B434651
theorem B602315 : Blo 103782 602315 := bstep (se 1 (by rfl) ⟨451736, by rfl⟩ : syracuseStep 602315 = 903473) B903473
theorem B242027 : Blo 103782 242027 := bstep (se 1 (by rfl) ⟨181520, by rfl⟩ : syracuseStep 242027 = 363041) B363041
theorem B242171 : Blo 103782 242171 := bstep (se 1 (by rfl) ⟨181628, by rfl⟩ : syracuseStep 242171 = 363257) B363257
theorem B242297 : Blo 103782 242297 := bstep (se 2 (by rfl) ⟨90861, by rfl⟩ : syracuseStep 242297 = 181723) B181723
theorem B242351 : Blo 103782 242351 := bstep (se 1 (by rfl) ⟨181763, by rfl⟩ : syracuseStep 242351 = 363527) B363527
theorem B176863 : Blo 103782 176863 := bstep (se 1 (by rfl) ⟨132647, by rfl⟩ : syracuseStep 176863 = 265295) B265295
theorem B242423 : Blo 103782 242423 := bstep (se 1 (by rfl) ⟨181817, by rfl⟩ : syracuseStep 242423 = 363635) B363635
theorem B340967 : Blo 103782 340967 := bstep (se 1 (by rfl) ⟨255725, by rfl⟩ : syracuseStep 340967 = 511451) B511451
theorem B177295 : Blo 103782 177295 := bstep (se 1 (by rfl) ⟨132971, by rfl⟩ : syracuseStep 177295 = 265943) B265943
theorem B177545 : Blo 103782 177545 := bstep (se 2 (by rfl) ⟨66579, by rfl⟩ : syracuseStep 177545 = 133159) B133159
theorem B800441 : Blo 103782 800441 := bstep (se 2 (by rfl) ⟨300165, by rfl⟩ : syracuseStep 800441 = 600331) B600331
theorem B505531 : Blo 103782 505531 := bstep (se 1 (by rfl) ⟨379148, by rfl⟩ : syracuseStep 505531 = 758297) B758297
theorem B177977 : Blo 103782 177977 := bstep (se 2 (by rfl) ⟨66741, by rfl⟩ : syracuseStep 177977 = 133483) B133483
theorem B374969 : Blo 103782 374969 := bstep (se 2 (by rfl) ⟨140613, by rfl⟩ : syracuseStep 374969 = 281227) B281227
theorem B801413 : Blo 103782 801413 := bstep (se 4 (by rfl) ⟨75132, by rfl⟩ : syracuseStep 801413 = 150265) B150265
theorem B539459 : Blo 103782 539459 := bstep (se 1 (by rfl) ⟨404594, by rfl⟩ : syracuseStep 539459 = 809189) B809189
theorem B179023 : Blo 103782 179023 := bstep (se 1 (by rfl) ⟨134267, by rfl⟩ : syracuseStep 179023 = 268535) B268535
theorem B179705 : Blo 103782 179705 := bstep (se 2 (by rfl) ⟨67389, by rfl⟩ : syracuseStep 179705 = 134779) B134779
theorem B802385 : Blo 103782 802385 := bstep (se 2 (by rfl) ⟨300894, by rfl⟩ : syracuseStep 802385 = 601789) B601789
theorem B671327 : Blo 103782 671327 := bstep (se 1 (by rfl) ⟨503495, by rfl⟩ : syracuseStep 671327 = 1006991) B1006991
theorem B540269 : Blo 103782 540269 := bstep (se 3 (by rfl) ⟨101300, by rfl⟩ : syracuseStep 540269 = 202601) B202601
theorem B179975 : Blo 103782 179975 := bstep (se 1 (by rfl) ⟨134981, by rfl⟩ : syracuseStep 179975 = 269963) B269963
theorem B343865 : Blo 103782 343865 := bstep (se 2 (by rfl) ⟨128949, by rfl⟩ : syracuseStep 343865 = 257899) B257899
theorem B606689 : Blo 103782 606689 := bstep (se 2 (by rfl) ⟨227508, by rfl⟩ : syracuseStep 606689 = 455017) B455017
theorem B180731 : Blo 103782 180731 := bstep (se 1 (by rfl) ⟨135548, by rfl⟩ : syracuseStep 180731 = 271097) B271097
theorem B672401 : Blo 103782 672401 := bstep (se 2 (by rfl) ⟨252150, by rfl⟩ : syracuseStep 672401 = 504301) B504301
theorem B181163 : Blo 103782 181163 := bstep (se 1 (by rfl) ⟨135872, by rfl⟩ : syracuseStep 181163 = 271745) B271745
theorem B1000451 : Blo 103782 1000451 := bstep (se 1 (by rfl) ⟨750338, by rfl⟩ : syracuseStep 1000451 = 1500677) B1500677
theorem B803843 : Blo 103782 803843 := bstep (se 1 (by rfl) ⟨602882, by rfl⟩ : syracuseStep 803843 = 1205765) B1205765
theorem B541895 : Blo 103782 541895 := bstep (se 1 (by rfl) ⟨406421, by rfl⟩ : syracuseStep 541895 = 812843) B812843
theorem B181703 : Blo 103782 181703 := bstep (se 1 (by rfl) ⟨136277, by rfl⟩ : syracuseStep 181703 = 272555) B272555
theorem B149303 : Blo 103782 149303 := bstep (se 1 (by rfl) ⟨111977, by rfl⟩ : syracuseStep 149303 = 223955) B223955
theorem B411473 : Blo 103782 411473 := bstep (se 2 (by rfl) ⟨154302, by rfl⟩ : syracuseStep 411473 = 308605) B308605
theorem B903095 : Blo 103782 903095 := bstep (se 1 (by rfl) ⟨677321, by rfl⟩ : syracuseStep 903095 = 1354643) B1354643
theorem B804815 : Blo 103782 804815 := bstep (se 1 (by rfl) ⟨603611, by rfl⟩ : syracuseStep 804815 = 1207223) B1207223
theorem B117031 : Blo 103782 117031 := bstep (se 1 (by rfl) ⟨87773, by rfl⟩ : syracuseStep 117031 = 175547) B175547
theorem B117103 : Blo 103782 117103 := bstep (se 1 (by rfl) ⟨87827, by rfl⟩ : syracuseStep 117103 = 175655) B175655
theorem B117319 : Blo 103782 117319 := bstep (se 1 (by rfl) ⟨87989, by rfl⟩ : syracuseStep 117319 = 175979) B175979
theorem B412435 : Blo 103782 412435 := bstep (se 1 (by rfl) ⟨309326, by rfl⟩ : syracuseStep 412435 = 618653) B618653
theorem B379667 : Blo 103782 379667 := bstep (se 1 (by rfl) ⟨284750, by rfl⟩ : syracuseStep 379667 = 569501) B569501
theorem B2411693 : Blo 103782 2411693 := bstep (se 3 (by rfl) ⟨452192, by rfl⟩ : syracuseStep 2411693 = 904385) B904385
theorem B150761 : Blo 103782 150761 := bstep (se 2 (by rfl) ⟨56535, by rfl⟩ : syracuseStep 150761 = 113071) B113071
theorem B806273 : Blo 103782 806273 := bstep (se 2 (by rfl) ⟨302352, by rfl⟩ : syracuseStep 806273 = 604705) B604705
theorem B118183 : Blo 103782 118183 := bstep (se 1 (by rfl) ⟨88637, by rfl⟩ : syracuseStep 118183 = 177275) B177275
theorem B446269 : Blo 103782 446269 := bstep (se 3 (by rfl) ⟨83675, by rfl⟩ : syracuseStep 446269 = 167351) B167351
theorem B479083 : Blo 103782 479083 := bstep (se 1 (by rfl) ⟨359312, by rfl⟩ : syracuseStep 479083 = 718625) B718625
theorem B118759 : Blo 103782 118759 := bstep (se 1 (by rfl) ⟨89069, by rfl⟩ : syracuseStep 118759 = 178139) B178139
theorem B512203 : Blo 103782 512203 := bstep (se 1 (by rfl) ⟨384152, by rfl⟩ : syracuseStep 512203 = 768305) B768305
theorem B4378853 : Blo 103782 4378853 := bstep (se 4 (by rfl) ⟨410517, by rfl⟩ : syracuseStep 4378853 = 821035) B821035
theorem B545615 : Blo 103782 545615 := bstep (se 1 (by rfl) ⟨409211, by rfl⟩ : syracuseStep 545615 = 818423) B818423
theorem B316649 : Blo 103782 316649 := bstep (se 2 (by rfl) ⟨118743, by rfl⟩ : syracuseStep 316649 = 237487) B237487
theorem B251113 : Blo 103782 251113 := bstep (se 2 (by rfl) ⟨94167, by rfl⟩ : syracuseStep 251113 = 188335) B188335
theorem B1103341 : Blo 103782 1103341 := bstep (se 3 (by rfl) ⟨206876, by rfl⟩ : syracuseStep 1103341 = 413753) B413753
theorem B1955393 : Blo 103782 1955393 := bstep (se 2 (by rfl) ⟨733272, by rfl⟩ : syracuseStep 1955393 = 1466545) B1466545
theorem B120415 : Blo 103782 120415 := bstep (se 1 (by rfl) ⟨90311, by rfl⟩ : syracuseStep 120415 = 180623) B180623
theorem B546743 : Blo 103782 546743 := bstep (se 1 (by rfl) ⟨410057, by rfl⟩ : syracuseStep 546743 = 820115) B820115
theorem B481231 : Blo 103782 481231 := bstep (se 1 (by rfl) ⟨360923, by rfl⟩ : syracuseStep 481231 = 721847) B721847
theorem B547069 : Blo 103782 547069 := bstep (se 3 (by rfl) ⟨102575, by rfl⟩ : syracuseStep 547069 = 205151) B205151
theorem B350675 : Blo 103782 350675 := bstep (se 1 (by rfl) ⟨263006, by rfl⟩ : syracuseStep 350675 = 526013) B526013
theorem B350783 : Blo 103782 350783 := bstep (se 1 (by rfl) ⟨263087, by rfl⟩ : syracuseStep 350783 = 526175) B526175
theorem B1530899 : Blo 103782 1530899 := bstep (se 1 (by rfl) ⟨1148174, by rfl⟩ : syracuseStep 1530899 = 2296349) B2296349
theorem B548345 : Blo 103782 548345 := bstep (se 2 (by rfl) ⟨205629, by rfl⟩ : syracuseStep 548345 = 411259) B411259
theorem B155753 : Blo 103782 155753 := bstep (se 2 (by rfl) ⟨58407, by rfl⟩ : syracuseStep 155753 = 116815) B116815
theorem B680089 : Blo 103782 680089 := bstep (se 2 (by rfl) ⟨255033, by rfl⟩ : syracuseStep 680089 = 510067) B510067
theorem B352619 : Blo 103782 352619 := bstep (se 1 (by rfl) ⟨264464, by rfl⟩ : syracuseStep 352619 = 528929) B528929
theorem B156071 : Blo 103782 156071 := bstep (se 1 (by rfl) ⟨117053, by rfl⟩ : syracuseStep 156071 = 234107) B234107
theorem B516527 : Blo 103782 516527 := bstep (se 1 (by rfl) ⟨387395, by rfl⟩ : syracuseStep 516527 = 774791) B774791
theorem B156155 : Blo 103782 156155 := bstep (se 1 (by rfl) ⟨117116, by rfl⟩ : syracuseStep 156155 = 234233) B234233
theorem B2089475 : Blo 103782 2089475 := bstep (se 1 (by rfl) ⟨1567106, by rfl⟩ : syracuseStep 2089475 = 3134213) B3134213
theorem B1008139 : Blo 103782 1008139 := bstep (se 1 (by rfl) ⟨756104, by rfl⟩ : syracuseStep 1008139 = 1512209) B1512209
theorem B385607 : Blo 103782 385607 := bstep (se 1 (by rfl) ⟨289205, by rfl⟩ : syracuseStep 385607 = 578411) B578411
theorem B156281 : Blo 103782 156281 := bstep (se 2 (by rfl) ⟨58605, by rfl⟩ : syracuseStep 156281 = 117211) B117211
theorem B352889 : Blo 103782 352889 := bstep (se 2 (by rfl) ⟨132333, by rfl⟩ : syracuseStep 352889 = 264667) B264667
theorem B156335 : Blo 103782 156335 := bstep (se 1 (by rfl) ⟨117251, by rfl⟩ : syracuseStep 156335 = 234503) B234503
theorem B221879 : Blo 103782 221879 := bstep (se 1 (by rfl) ⟨166409, by rfl⟩ : syracuseStep 221879 = 332819) B332819
theorem B156383 : Blo 103782 156383 := bstep (se 1 (by rfl) ⟨117287, by rfl⟩ : syracuseStep 156383 = 234575) B234575
theorem B156647 : Blo 103782 156647 := bstep (se 1 (by rfl) ⟨117485, by rfl⟩ : syracuseStep 156647 = 234971) B234971
theorem B156905 : Blo 103782 156905 := bstep (se 2 (by rfl) ⟨58839, by rfl⟩ : syracuseStep 156905 = 117679) B117679
theorem B156959 : Blo 103782 156959 := bstep (se 1 (by rfl) ⟨117719, by rfl⟩ : syracuseStep 156959 = 235439) B235439
theorem B255419 : Blo 103782 255419 := bstep (se 1 (by rfl) ⟨191564, by rfl⟩ : syracuseStep 255419 = 383129) B383129
theorem B157127 : Blo 103782 157127 := bstep (se 1 (by rfl) ⟨117845, by rfl⟩ : syracuseStep 157127 = 235691) B235691
theorem B255649 : Blo 103782 255649 := bstep (se 2 (by rfl) ⟨95868, by rfl⟩ : syracuseStep 255649 = 191737) B191737
theorem B157481 : Blo 103782 157481 := bstep (se 2 (by rfl) ⟨59055, by rfl⟩ : syracuseStep 157481 = 118111) B118111
theorem B157487 : Blo 103782 157487 := bstep (se 1 (by rfl) ⟨118115, by rfl⟩ : syracuseStep 157487 = 236231) B236231
theorem B124903 : Blo 103782 124903 := bstep (se 1 (by rfl) ⟨93677, by rfl⟩ : syracuseStep 124903 = 187355) B187355
theorem B452641 : Blo 103782 452641 := bstep (se 2 (by rfl) ⟨169740, by rfl⟩ : syracuseStep 452641 = 339481) B339481
theorem B157961 : Blo 103782 157961 := bstep (se 2 (by rfl) ⟨59235, by rfl⟩ : syracuseStep 157961 = 118471) B118471
theorem B1370429 : Blo 103782 1370429 := bstep (se 3 (by rfl) ⟨256955, by rfl⟩ : syracuseStep 1370429 = 513911) B513911
theorem B354671 : Blo 103782 354671 := bstep (se 1 (by rfl) ⟨266003, by rfl⟩ : syracuseStep 354671 = 532007) B532007
theorem B158063 : Blo 103782 158063 := bstep (se 1 (by rfl) ⟨118547, by rfl⟩ : syracuseStep 158063 = 237095) B237095
theorem B158279 : Blo 103782 158279 := bstep (se 1 (by rfl) ⟨118709, by rfl⟩ : syracuseStep 158279 = 237419) B237419
theorem B158315 : Blo 103782 158315 := bstep (se 1 (by rfl) ⟨118736, by rfl⟩ : syracuseStep 158315 = 237473) B237473
theorem B1108669 : Blo 103782 1108669 := bstep (se 3 (by rfl) ⟨207875, by rfl⟩ : syracuseStep 1108669 = 415751) B415751
theorem B158543 : Blo 103782 158543 := bstep (se 1 (by rfl) ⟨118907, by rfl⟩ : syracuseStep 158543 = 237815) B237815
theorem B158939 : Blo 103782 158939 := bstep (se 1 (by rfl) ⟨119204, by rfl⟩ : syracuseStep 158939 = 238409) B238409
theorem B159113 : Blo 103782 159113 := bstep (se 2 (by rfl) ⟨59667, by rfl⟩ : syracuseStep 159113 = 119335) B119335
theorem B159175 : Blo 103782 159175 := bstep (se 1 (by rfl) ⟨119381, by rfl⟩ : syracuseStep 159175 = 238763) B238763
theorem B814535 : Blo 103782 814535 := bstep (se 1 (by rfl) ⟨610901, by rfl⟩ : syracuseStep 814535 = 1221803) B1221803
theorem B126527 : Blo 103782 126527 := bstep (se 1 (by rfl) ⟨94895, by rfl⟩ : syracuseStep 126527 = 189791) B189791
theorem B224851 : Blo 103782 224851 := bstep (se 1 (by rfl) ⟨168638, by rfl⟩ : syracuseStep 224851 = 337277) B337277
theorem B323155 : Blo 103782 323155 := bstep (se 1 (by rfl) ⟨242366, by rfl⟩ : syracuseStep 323155 = 484733) B484733
theorem B913069 : Blo 103782 913069 := bstep (se 3 (by rfl) ⟨171200, by rfl⟩ : syracuseStep 913069 = 342401) B342401
theorem B356075 : Blo 103782 356075 := bstep (se 1 (by rfl) ⟨267056, by rfl⟩ : syracuseStep 356075 = 534113) B534113
theorem B159467 : Blo 103782 159467 := bstep (se 1 (by rfl) ⟨119600, by rfl⟩ : syracuseStep 159467 = 239201) B239201
theorem B159695 : Blo 103782 159695 := bstep (se 1 (by rfl) ⟨119771, by rfl⟩ : syracuseStep 159695 = 239543) B239543
theorem B749533 : Blo 103782 749533 := bstep (se 3 (by rfl) ⟨140537, by rfl⟩ : syracuseStep 749533 = 281075) B281075
theorem B160091 : Blo 103782 160091 := bstep (se 1 (by rfl) ⟨120068, by rfl⟩ : syracuseStep 160091 = 240137) B240137
theorem B1208681 : Blo 103782 1208681 := bstep (se 2 (by rfl) ⟨453255, by rfl⟩ : syracuseStep 1208681 = 906511) B906511
theorem B684395 : Blo 103782 684395 := bstep (se 1 (by rfl) ⟨513296, by rfl⟩ : syracuseStep 684395 = 1026593) B1026593
theorem B258515 : Blo 103782 258515 := bstep (se 1 (by rfl) ⟨193886, by rfl⟩ : syracuseStep 258515 = 387773) B387773
theorem B4452889 : Blo 103782 4452889 := bstep (se 2 (by rfl) ⟨1669833, by rfl⟩ : syracuseStep 4452889 = 3339667) B3339667
theorem B2224691 : Blo 103782 2224691 := bstep (se 1 (by rfl) ⟨1668518, by rfl⟩ : syracuseStep 2224691 = 3337037) B3337037
theorem B160319 : Blo 103782 160319 := bstep (se 1 (by rfl) ⟨120239, by rfl⟩ : syracuseStep 160319 = 240479) B240479
theorem B357047 : Blo 103782 357047 := bstep (se 1 (by rfl) ⟨267785, by rfl⟩ : syracuseStep 357047 = 535571) B535571
theorem B160439 : Blo 103782 160439 := bstep (se 1 (by rfl) ⟨120329, by rfl⟩ : syracuseStep 160439 = 240659) B240659
theorem B160667 : Blo 103782 160667 := bstep (se 1 (by rfl) ⟨120500, by rfl⟩ : syracuseStep 160667 = 241001) B241001
theorem B1340495 : Blo 103782 1340495 := bstep (se 1 (by rfl) ⟨1005371, by rfl⟩ : syracuseStep 1340495 = 2010743) B2010743
theorem B455975 : Blo 103782 455975 := bstep (se 1 (by rfl) ⟨341981, by rfl⟩ : syracuseStep 455975 = 683963) B683963
theorem B161063 : Blo 103782 161063 := bstep (se 1 (by rfl) ⟨120797, by rfl⟩ : syracuseStep 161063 = 241595) B241595
theorem B816479 : Blo 103782 816479 := bstep (se 1 (by rfl) ⟨612359, by rfl⟩ : syracuseStep 816479 = 1224719) B1224719
theorem B161147 : Blo 103782 161147 := bstep (se 1 (by rfl) ⟨120860, by rfl⟩ : syracuseStep 161147 = 241721) B241721
theorem B161273 : Blo 103782 161273 := bstep (se 2 (by rfl) ⟨60477, by rfl⟩ : syracuseStep 161273 = 120955) B120955
theorem B1078829 : Blo 103782 1078829 := bstep (se 3 (by rfl) ⟨202280, by rfl⟩ : syracuseStep 1078829 = 404561) B404561
theorem B423481 : Blo 103782 423481 := bstep (se 2 (by rfl) ⟨158805, by rfl⟩ : syracuseStep 423481 = 317611) B317611
theorem B161375 : Blo 103782 161375 := bstep (se 1 (by rfl) ⟨121031, by rfl⟩ : syracuseStep 161375 = 242063) B242063
theorem B128747 : Blo 103782 128747 := bstep (se 1 (by rfl) ⟨96560, by rfl⟩ : syracuseStep 128747 = 193121) B193121
theorem B358199 : Blo 103782 358199 := bstep (se 1 (by rfl) ⟨268649, by rfl⟩ : syracuseStep 358199 = 537299) B537299
theorem B161591 : Blo 103782 161591 := bstep (se 1 (by rfl) ⟨121193, by rfl⟩ : syracuseStep 161591 = 242387) B242387
theorem B423917 : Blo 103782 423917 := bstep (se 3 (by rfl) ⟨79484, by rfl⟩ : syracuseStep 423917 = 158969) B158969
theorem B653345 : Blo 103782 653345 := bstep (se 2 (by rfl) ⟨245004, by rfl⟩ : syracuseStep 653345 = 490009) B490009
theorem B2357495 : Blo 103782 2357495 := bstep (se 1 (by rfl) ⟨1768121, by rfl⟩ : syracuseStep 2357495 = 3536243) B3536243
theorem B260377 : Blo 103782 260377 := bstep (se 2 (by rfl) ⟨97641, by rfl⟩ : syracuseStep 260377 = 195283) B195283
theorem B2587085 : Blo 103782 2587085 := bstep (se 3 (by rfl) ⟨485078, by rfl⟩ : syracuseStep 2587085 = 970157) B970157
theorem B457289 : Blo 103782 457289 := bstep (se 2 (by rfl) ⟨171483, by rfl⟩ : syracuseStep 457289 = 342967) B342967
theorem B358991 : Blo 103782 358991 := bstep (se 1 (by rfl) ⟨269243, by rfl⟩ : syracuseStep 358991 = 538487) B538487
theorem B360233 : Blo 103782 360233 := bstep (se 2 (by rfl) ⟨135087, by rfl⟩ : syracuseStep 360233 = 270175) B270175
theorem B229225 : Blo 103782 229225 := bstep (se 2 (by rfl) ⟨85959, by rfl⟩ : syracuseStep 229225 = 171919) B171919
theorem B131455 : Blo 103782 131455 := bstep (se 1 (by rfl) ⟨98591, by rfl⟩ : syracuseStep 131455 = 197183) B197183
theorem B328367 : Blo 103782 328367 := bstep (se 1 (by rfl) ⟨246275, by rfl⟩ : syracuseStep 328367 = 492551) B492551
theorem B1344185 : Blo 103782 1344185 := bstep (se 2 (by rfl) ⟨504069, by rfl⟩ : syracuseStep 1344185 = 1008139) B1008139
theorem B9011897 : Blo 103782 9011897 := bstep (se 2 (by rfl) ⟨3379461, by rfl⟩ : syracuseStep 9011897 = 6758923) B6758923
theorem B591583 : Blo 103782 591583 := bstep (se 1 (by rfl) ⟨443687, by rfl⟩ : syracuseStep 591583 = 887375) B887375
theorem B133103 : Blo 103782 133103 := bstep (se 1 (by rfl) ⟨99827, by rfl⟩ : syracuseStep 133103 = 199655) B199655
theorem B1607795 : Blo 103782 1607795 := bstep (se 1 (by rfl) ⟨1205846, by rfl⟩ : syracuseStep 1607795 = 2411693) B2411693
theorem B395513 : Blo 103782 395513 := bstep (se 2 (by rfl) ⟨148317, by rfl⟩ : syracuseStep 395513 = 296635) B296635
theorem B264505 : Blo 103782 264505 := bstep (se 2 (by rfl) ⟨99189, by rfl⟩ : syracuseStep 264505 = 198379) B198379
theorem B199199 : Blo 103782 199199 := bstep (se 1 (by rfl) ⟨149399, by rfl⟩ : syracuseStep 199199 = 298799) B298799
theorem B264809 : Blo 103782 264809 := bstep (se 2 (by rfl) ⟨99303, by rfl⟩ : syracuseStep 264809 = 198607) B198607
theorem B166537 : Blo 103782 166537 := bstep (se 2 (by rfl) ⟨62451, by rfl⟩ : syracuseStep 166537 = 124903) B124903
theorem B2919235 : Blo 103782 2919235 := bstep (se 1 (by rfl) ⟨2189426, by rfl⟩ : syracuseStep 2919235 = 4378853) B4378853
theorem B461663 : Blo 103782 461663 := bstep (se 1 (by rfl) ⟨346247, by rfl⟩ : syracuseStep 461663 = 692495) B692495
theorem B1445053 : Blo 103782 1445053 := bstep (se 3 (by rfl) ⟨270947, by rfl⟩ : syracuseStep 1445053 = 541895) B541895
theorem B363743 : Blo 103782 363743 := bstep (se 1 (by rfl) ⟨272807, by rfl⟩ : syracuseStep 363743 = 545615) B545615
theorem B396863 : Blo 103782 396863 := bstep (se 1 (by rfl) ⟨297647, by rfl⟩ : syracuseStep 396863 = 595295) B595295
theorem B265801 : Blo 103782 265801 := bstep (se 2 (by rfl) ⟨99675, by rfl⟩ : syracuseStep 265801 = 199351) B199351
theorem B1478225 : Blo 103782 1478225 := bstep (se 2 (by rfl) ⟨554334, by rfl⟩ : syracuseStep 1478225 = 1108669) B1108669
theorem B134951 : Blo 103782 134951 := bstep (se 1 (by rfl) ⟨101213, by rfl⟩ : syracuseStep 134951 = 202427) B202427
theorem B266105 : Blo 103782 266105 := bstep (se 2 (by rfl) ⟨99789, by rfl⟩ : syracuseStep 266105 = 199579) B199579
theorem B364495 : Blo 103782 364495 := bstep (se 1 (by rfl) ⟨273371, by rfl⟩ : syracuseStep 364495 = 546743) B546743
theorem B2199653 : Blo 103782 2199653 := bstep (se 4 (by rfl) ⟨206217, by rfl⟩ : syracuseStep 2199653 = 412435) B412435
theorem B528605 : Blo 103782 528605 := bstep (se 3 (by rfl) ⟨99113, by rfl⟩ : syracuseStep 528605 = 198227) B198227
theorem B233783 : Blo 103782 233783 := bstep (se 1 (by rfl) ⟨175337, by rfl⟩ : syracuseStep 233783 = 350675) B350675
theorem B233855 : Blo 103782 233855 := bstep (se 1 (by rfl) ⟨175391, by rfl⟩ : syracuseStep 233855 = 350783) B350783
theorem B528767 : Blo 103782 528767 := bstep (se 1 (by rfl) ⟨396575, by rfl⟩ : syracuseStep 528767 = 793151) B793151
theorem B1020599 : Blo 103782 1020599 := bstep (se 1 (by rfl) ⟨765449, by rfl⟩ : syracuseStep 1020599 = 1530899) B1530899
theorem B3347203 : Blo 103782 3347203 := bstep (se 1 (by rfl) ⟨2510402, by rfl⟩ : syracuseStep 3347203 = 5020805) B5020805
theorem B299801 : Blo 103782 299801 := bstep (se 2 (by rfl) ⟨112425, by rfl⟩ : syracuseStep 299801 = 224851) B224851
theorem B398141 : Blo 103782 398141 := bstep (se 3 (by rfl) ⟨74651, by rfl⟩ : syracuseStep 398141 = 149303) B149303
theorem B1217425 : Blo 103782 1217425 := bstep (se 2 (by rfl) ⟨456534, by rfl⟩ : syracuseStep 1217425 = 913069) B913069
theorem B267259 : Blo 103782 267259 := bstep (se 1 (by rfl) ⟨200444, by rfl⟩ : syracuseStep 267259 = 400889) B400889
theorem B365563 : Blo 103782 365563 := bstep (se 1 (by rfl) ⟨274172, by rfl⟩ : syracuseStep 365563 = 548345) B548345
theorem B595025 : Blo 103782 595025 := bstep (se 2 (by rfl) ⟨223134, by rfl⟩ : syracuseStep 595025 = 446269) B446269
theorem B267371 : Blo 103782 267371 := bstep (se 1 (by rfl) ⟨200528, by rfl⟩ : syracuseStep 267371 = 401057) B401057
theorem B136399 : Blo 103782 136399 := bstep (se 1 (by rfl) ⟨102299, by rfl⟩ : syracuseStep 136399 = 204599) B204599
theorem B1545425 : Blo 103782 1545425 := bstep (se 2 (by rfl) ⟨579534, by rfl⟩ : syracuseStep 1545425 = 1159069) B1159069
theorem B103835 : Blo 103782 103835 := bstep (se 1 (by rfl) ⟨77876, by rfl⟩ : syracuseStep 103835 = 155753) B155753
theorem B267745 : Blo 103782 267745 := bstep (se 2 (by rfl) ⟨100404, by rfl⟩ : syracuseStep 267745 = 200809) B200809
theorem B235079 : Blo 103782 235079 := bstep (se 1 (by rfl) ⟨176309, by rfl⟩ : syracuseStep 235079 = 352619) B352619
theorem B104047 : Blo 103782 104047 := bstep (se 1 (by rfl) ⟨78035, by rfl⟩ : syracuseStep 104047 = 156071) B156071
theorem B104103 : Blo 103782 104103 := bstep (se 1 (by rfl) ⟨78077, by rfl⟩ : syracuseStep 104103 = 156155) B156155
theorem B464555 : Blo 103782 464555 := bstep (se 1 (by rfl) ⟨348416, by rfl⟩ : syracuseStep 464555 = 696833) B696833
theorem B104187 : Blo 103782 104187 := bstep (se 1 (by rfl) ⟨78140, by rfl⟩ : syracuseStep 104187 = 156281) B156281
theorem B235259 : Blo 103782 235259 := bstep (se 1 (by rfl) ⟨176444, by rfl⟩ : syracuseStep 235259 = 352889) B352889
theorem B104223 : Blo 103782 104223 := bstep (se 1 (by rfl) ⟨78167, by rfl⟩ : syracuseStep 104223 = 156335) B156335
theorem B104255 : Blo 103782 104255 := bstep (se 1 (by rfl) ⟨78191, by rfl⟩ : syracuseStep 104255 = 156383) B156383
theorem B104431 : Blo 103782 104431 := bstep (se 1 (by rfl) ⟨78323, by rfl⟩ : syracuseStep 104431 = 156647) B156647
theorem B1349621 : Blo 103782 1349621 := bstep (se 5 (by rfl) ⟨63263, by rfl⟩ : syracuseStep 1349621 = 126527) B126527
theorem B5937185 : Blo 103782 5937185 := bstep (se 2 (by rfl) ⟨2226444, by rfl⟩ : syracuseStep 5937185 = 4452889) B4452889
theorem B104603 : Blo 103782 104603 := bstep (se 1 (by rfl) ⟨78452, by rfl⟩ : syracuseStep 104603 = 156905) B156905
theorem B104639 : Blo 103782 104639 := bstep (se 1 (by rfl) ⟨78479, by rfl⟩ : syracuseStep 104639 = 156959) B156959
theorem B170279 : Blo 103782 170279 := bstep (se 1 (by rfl) ⟨127709, by rfl⟩ : syracuseStep 170279 = 255419) B255419
theorem B235817 : Blo 103782 235817 := bstep (se 2 (by rfl) ⟨88431, by rfl⟩ : syracuseStep 235817 = 176863) B176863
theorem B104751 : Blo 103782 104751 := bstep (se 1 (by rfl) ⟨78563, by rfl⟩ : syracuseStep 104751 = 157127) B157127
theorem B268667 : Blo 103782 268667 := bstep (se 1 (by rfl) ⟨201500, by rfl⟩ : syracuseStep 268667 = 403001) B403001
theorem B104987 : Blo 103782 104987 := bstep (se 1 (by rfl) ⟨78740, by rfl⟩ : syracuseStep 104987 = 157481) B157481
theorem B104991 : Blo 103782 104991 := bstep (se 1 (by rfl) ⟨78743, by rfl⟩ : syracuseStep 104991 = 157487) B157487
theorem B105307 : Blo 103782 105307 := bstep (se 1 (by rfl) ⟨78980, by rfl⟩ : syracuseStep 105307 = 157961) B157961
theorem B236393 : Blo 103782 236393 := bstep (se 2 (by rfl) ⟨88647, by rfl⟩ : syracuseStep 236393 = 177295) B177295
theorem B531359 : Blo 103782 531359 := bstep (se 1 (by rfl) ⟨398519, by rfl⟩ : syracuseStep 531359 = 797039) B797039
theorem B236447 : Blo 103782 236447 := bstep (se 1 (by rfl) ⟨177335, by rfl⟩ : syracuseStep 236447 = 354671) B354671
theorem B105375 : Blo 103782 105375 := bstep (se 1 (by rfl) ⟨79031, by rfl⟩ : syracuseStep 105375 = 158063) B158063
theorem B334817 : Blo 103782 334817 := bstep (se 2 (by rfl) ⟨125556, by rfl⟩ : syracuseStep 334817 = 251113) B251113
theorem B105519 : Blo 103782 105519 := bstep (se 1 (by rfl) ⟨79139, by rfl⟩ : syracuseStep 105519 = 158279) B158279
theorem B105543 : Blo 103782 105543 := bstep (se 1 (by rfl) ⟨79157, by rfl⟩ : syracuseStep 105543 = 158315) B158315
theorem B105695 : Blo 103782 105695 := bstep (se 1 (by rfl) ⟨79271, by rfl⟩ : syracuseStep 105695 = 158543) B158543
theorem B564641 : Blo 103782 564641 := bstep (se 2 (by rfl) ⟨211740, by rfl⟩ : syracuseStep 564641 = 423481) B423481
theorem B105959 : Blo 103782 105959 := bstep (se 1 (by rfl) ⟨79469, by rfl⟩ : syracuseStep 105959 = 158939) B158939
theorem B106075 : Blo 103782 106075 := bstep (se 1 (by rfl) ⟨79556, by rfl⟩ : syracuseStep 106075 = 159113) B159113
theorem B237383 : Blo 103782 237383 := bstep (se 1 (by rfl) ⟨178037, by rfl⟩ : syracuseStep 237383 = 356075) B356075
theorem B106311 : Blo 103782 106311 := bstep (se 1 (by rfl) ⟨79733, by rfl⟩ : syracuseStep 106311 = 159467) B159467
theorem B106463 : Blo 103782 106463 := bstep (se 1 (by rfl) ⟨79847, by rfl⟩ : syracuseStep 106463 = 159695) B159695
theorem B401543 : Blo 103782 401543 := bstep (se 1 (by rfl) ⟨301157, by rfl⟩ : syracuseStep 401543 = 602315) B602315
theorem B106727 : Blo 103782 106727 := bstep (se 1 (by rfl) ⟨80045, by rfl⟩ : syracuseStep 106727 = 160091) B160091
theorem B172343 : Blo 103782 172343 := bstep (se 1 (by rfl) ⟨129257, by rfl⟩ : syracuseStep 172343 = 258515) B258515
theorem B532817 : Blo 103782 532817 := bstep (se 2 (by rfl) ⟨199806, by rfl⟩ : syracuseStep 532817 = 399613) B399613
theorem B729425 : Blo 103782 729425 := bstep (se 2 (by rfl) ⟨273534, by rfl⟩ : syracuseStep 729425 = 547069) B547069
theorem B1483127 : Blo 103782 1483127 := bstep (se 1 (by rfl) ⟨1112345, by rfl⟩ : syracuseStep 1483127 = 2224691) B2224691
theorem B106879 : Blo 103782 106879 := bstep (se 1 (by rfl) ⟨80159, by rfl⟩ : syracuseStep 106879 = 160319) B160319
theorem B238031 : Blo 103782 238031 := bstep (se 1 (by rfl) ⟨178523, by rfl⟩ : syracuseStep 238031 = 357047) B357047
theorem B106959 : Blo 103782 106959 := bstep (se 1 (by rfl) ⟨80219, by rfl⟩ : syracuseStep 106959 = 160439) B160439
theorem B107111 : Blo 103782 107111 := bstep (se 1 (by rfl) ⟨80333, by rfl⟩ : syracuseStep 107111 = 160667) B160667
theorem B402029 : Blo 103782 402029 := bstep (se 3 (by rfl) ⟨75380, by rfl⟩ : syracuseStep 402029 = 150761) B150761
theorem B5120657 : Blo 103782 5120657 := bstep (se 2 (by rfl) ⟨1920246, by rfl⟩ : syracuseStep 5120657 = 3840493) B3840493
theorem B893663 : Blo 103782 893663 := bstep (se 1 (by rfl) ⟨670247, by rfl⟩ : syracuseStep 893663 = 1340495) B1340495
theorem B303983 : Blo 103782 303983 := bstep (se 1 (by rfl) ⟨227987, by rfl⟩ : syracuseStep 303983 = 455975) B455975
theorem B107375 : Blo 103782 107375 := bstep (se 1 (by rfl) ⟨80531, by rfl⟩ : syracuseStep 107375 = 161063) B161063
theorem B107431 : Blo 103782 107431 := bstep (se 1 (by rfl) ⟨80573, by rfl⟩ : syracuseStep 107431 = 161147) B161147
theorem B107515 : Blo 103782 107515 := bstep (se 1 (by rfl) ⟨80636, by rfl⟩ : syracuseStep 107515 = 161273) B161273
theorem B107583 : Blo 103782 107583 := bstep (se 1 (by rfl) ⟨80687, by rfl⟩ : syracuseStep 107583 = 161375) B161375
theorem B238697 : Blo 103782 238697 := bstep (se 2 (by rfl) ⟨89511, by rfl⟩ : syracuseStep 238697 = 179023) B179023
theorem B533627 : Blo 103782 533627 := bstep (se 1 (by rfl) ⟨400220, by rfl⟩ : syracuseStep 533627 = 800441) B800441
theorem B238799 : Blo 103782 238799 := bstep (se 1 (by rfl) ⟨179099, by rfl⟩ : syracuseStep 238799 = 358199) B358199
theorem B107727 : Blo 103782 107727 := bstep (se 1 (by rfl) ⟨80795, by rfl⟩ : syracuseStep 107727 = 161591) B161591
theorem B435563 : Blo 103782 435563 := bstep (se 1 (by rfl) ⟨326672, by rfl⟩ : syracuseStep 435563 = 653345) B653345
theorem B664969 : Blo 103782 664969 := bstep (se 2 (by rfl) ⟨249363, by rfl⟩ : syracuseStep 664969 = 498727) B498727
theorem B304859 : Blo 103782 304859 := bstep (se 1 (by rfl) ⟨228644, by rfl⟩ : syracuseStep 304859 = 457289) B457289
theorem B239327 : Blo 103782 239327 := bstep (se 1 (by rfl) ⟨179495, by rfl⟩ : syracuseStep 239327 = 358991) B358991
theorem B534275 : Blo 103782 534275 := bstep (se 1 (by rfl) ⟨400706, by rfl⟩ : syracuseStep 534275 = 801413) B801413
theorem B534923 : Blo 103782 534923 := bstep (se 1 (by rfl) ⟨401192, by rfl⟩ : syracuseStep 534923 = 802385) B802385
theorem B305633 : Blo 103782 305633 := bstep (se 2 (by rfl) ⟨114612, by rfl⟩ : syracuseStep 305633 = 229225) B229225
theorem B240155 : Blo 103782 240155 := bstep (se 1 (by rfl) ⟨180116, by rfl⟩ : syracuseStep 240155 = 360233) B360233
theorem B404459 : Blo 103782 404459 := bstep (se 1 (by rfl) ⟨303344, by rfl⟩ : syracuseStep 404459 = 606689) B606689
theorem B502919 : Blo 103782 502919 := bstep (se 1 (by rfl) ⟨377189, by rfl⟩ : syracuseStep 502919 = 754379) B754379
theorem B175439 : Blo 103782 175439 := bstep (se 1 (by rfl) ⟨131579, by rfl⟩ : syracuseStep 175439 = 263159) B263159
theorem B666967 : Blo 103782 666967 := bstep (se 1 (by rfl) ⟨500225, by rfl⟩ : syracuseStep 666967 = 1000451) B1000451
theorem B535895 : Blo 103782 535895 := bstep (se 1 (by rfl) ⟨401921, by rfl⟩ : syracuseStep 535895 = 803843) B803843
theorem B634463 : Blo 103782 634463 := bstep (se 1 (by rfl) ⟨475847, by rfl⟩ : syracuseStep 634463 = 951695) B951695
theorem B274315 : Blo 103782 274315 := bstep (se 1 (by rfl) ⟨205736, by rfl⟩ : syracuseStep 274315 = 411473) B411473
theorem B602063 : Blo 103782 602063 := bstep (se 1 (by rfl) ⟨451547, by rfl⟩ : syracuseStep 602063 = 903095) B903095
theorem B536543 : Blo 103782 536543 := bstep (se 1 (by rfl) ⟨402407, by rfl⟩ : syracuseStep 536543 = 804815) B804815
theorem B241631 : Blo 103782 241631 := bstep (se 1 (by rfl) ⟨181223, by rfl⟩ : syracuseStep 241631 = 362447) B362447
theorem B536705 : Blo 103782 536705 := bstep (se 2 (by rfl) ⟨201264, by rfl⟩ : syracuseStep 536705 = 402529) B402529
theorem B1388677 : Blo 103782 1388677 := bstep (se 4 (by rfl) ⟨130188, by rfl⟩ : syracuseStep 1388677 = 260377) B260377
theorem B1028285 : Blo 103782 1028285 := bstep (se 3 (by rfl) ⟨192803, by rfl⟩ : syracuseStep 1028285 = 385607) B385607
theorem B176735 : Blo 103782 176735 := bstep (se 1 (by rfl) ⟨132551, by rfl⟩ : syracuseStep 176735 = 265103) B265103
theorem B242279 : Blo 103782 242279 := bstep (se 1 (by rfl) ⟨181709, by rfl⟩ : syracuseStep 242279 = 363419) B363419
theorem B177007 : Blo 103782 177007 := bstep (se 1 (by rfl) ⟨132755, by rfl⟩ : syracuseStep 177007 = 265511) B265511
theorem B340865 : Blo 103782 340865 := bstep (se 2 (by rfl) ⟨127824, by rfl⟩ : syracuseStep 340865 = 255649) B255649
theorem B537515 : Blo 103782 537515 := bstep (se 1 (by rfl) ⟨403136, by rfl⟩ : syracuseStep 537515 = 806273) B806273
theorem B603521 : Blo 103782 603521 := bstep (se 2 (by rfl) ⟨226320, by rfl⟩ : syracuseStep 603521 = 452641) B452641
theorem B1226177 : Blo 103782 1226177 := bstep (se 2 (by rfl) ⟨459816, by rfl⟩ : syracuseStep 1226177 = 919633) B919633
theorem B1160887 : Blo 103782 1160887 := bstep (se 1 (by rfl) ⟨870665, by rfl⟩ : syracuseStep 1160887 = 1741331) B1741331
theorem B571115 : Blo 103782 571115 := bstep (se 1 (by rfl) ⟨428336, by rfl⟩ : syracuseStep 571115 = 856673) B856673
theorem B178159 : Blo 103782 178159 := bstep (se 1 (by rfl) ⟨133619, by rfl⟩ : syracuseStep 178159 = 267239) B267239
theorem B211099 : Blo 103782 211099 := bstep (se 1 (by rfl) ⟨158324, by rfl⟩ : syracuseStep 211099 = 316649) B316649
theorem B178409 : Blo 103782 178409 := bstep (se 2 (by rfl) ⟨66903, by rfl⟩ : syracuseStep 178409 = 133807) B133807
theorem B768791 : Blo 103782 768791 := bstep (se 1 (by rfl) ⟨576593, by rfl⟩ : syracuseStep 768791 = 1153187) B1153187
theorem B310175 : Blo 103782 310175 := bstep (se 1 (by rfl) ⟨232631, by rfl⟩ : syracuseStep 310175 = 465263) B465263
theorem B1227727 : Blo 103782 1227727 := bstep (se 1 (by rfl) ⟨920795, by rfl⟩ : syracuseStep 1227727 = 1841591) B1841591
theorem B343325 : Blo 103782 343325 := bstep (se 3 (by rfl) ⟨64373, by rfl⟩ : syracuseStep 343325 = 128747) B128747
theorem B966287 : Blo 103782 966287 := bstep (se 1 (by rfl) ⟨724715, by rfl⟩ : syracuseStep 966287 = 1449431) B1449431
theorem B179887 : Blo 103782 179887 := bstep (se 1 (by rfl) ⟨134915, by rfl⟩ : syracuseStep 179887 = 269831) B269831
theorem B573115 : Blo 103782 573115 := bstep (se 1 (by rfl) ⟨429836, by rfl⟩ : syracuseStep 573115 = 859673) B859673
theorem B638777 : Blo 103782 638777 := bstep (se 2 (by rfl) ⟨239541, by rfl⟩ : syracuseStep 638777 = 479083) B479083
theorem B999377 : Blo 103782 999377 := bstep (se 2 (by rfl) ⟨374766, by rfl⟩ : syracuseStep 999377 = 749533) B749533
theorem B180191 : Blo 103782 180191 := bstep (se 1 (by rfl) ⟨135143, by rfl⟩ : syracuseStep 180191 = 270287) B270287
theorem B2867339 : Blo 103782 2867339 := bstep (se 1 (by rfl) ⟨2150504, by rfl⟩ : syracuseStep 2867339 = 4301009) B4301009
theorem B344351 : Blo 103782 344351 := bstep (se 1 (by rfl) ⟨258263, by rfl⟩ : syracuseStep 344351 = 516527) B516527
theorem B180535 : Blo 103782 180535 := bstep (se 1 (by rfl) ⟨135401, by rfl⟩ : syracuseStep 180535 = 270803) B270803
theorem B1392983 : Blo 103782 1392983 := bstep (se 1 (by rfl) ⟨1044737, by rfl⟩ : syracuseStep 1392983 = 2089475) B2089475
theorem B147919 : Blo 103782 147919 := bstep (se 1 (by rfl) ⟨110939, by rfl⟩ : syracuseStep 147919 = 221879) B221879
theorem B180839 : Blo 103782 180839 := bstep (se 1 (by rfl) ⟨135629, by rfl⟩ : syracuseStep 180839 = 271259) B271259
theorem B181001 : Blo 103782 181001 := bstep (se 2 (by rfl) ⟨67875, by rfl⟩ : syracuseStep 181001 = 135751) B135751
theorem B902411 : Blo 103782 902411 := bstep (se 1 (by rfl) ⟨676808, by rfl⟩ : syracuseStep 902411 = 1353617) B1353617
theorem B181595 : Blo 103782 181595 := bstep (se 1 (by rfl) ⟨136196, by rfl⟩ : syracuseStep 181595 = 272393) B272393
theorem B181831 : Blo 103782 181831 := bstep (se 1 (by rfl) ⟨136373, by rfl⟩ : syracuseStep 181831 = 272747) B272747
theorem B674041 : Blo 103782 674041 := bstep (se 2 (by rfl) ⟨252765, by rfl⟩ : syracuseStep 674041 = 505531) B505531
theorem B543023 : Blo 103782 543023 := bstep (se 1 (by rfl) ⟨407267, by rfl⟩ : syracuseStep 543023 = 814535) B814535
theorem B10242541 : Blo 103782 10242541 := bstep (se 3 (by rfl) ⟨1920476, by rfl⟩ : syracuseStep 10242541 = 3840953) B3840953
theorem B641641 : Blo 103782 641641 := bstep (se 2 (by rfl) ⟨240615, by rfl⟩ : syracuseStep 641641 = 481231) B481231
theorem B805787 : Blo 103782 805787 := bstep (se 1 (by rfl) ⟨604340, by rfl⟩ : syracuseStep 805787 = 1208681) B1208681
theorem B1723493 : Blo 103782 1723493 := bstep (se 4 (by rfl) ⟨161577, by rfl⟩ : syracuseStep 1723493 = 323155) B323155
theorem B544319 : Blo 103782 544319 := bstep (se 1 (by rfl) ⟨408239, by rfl⟩ : syracuseStep 544319 = 816479) B816479
theorem B118363 : Blo 103782 118363 := bstep (se 1 (by rfl) ⟨88772, by rfl⟩ : syracuseStep 118363 = 177545) B177545
theorem B118651 : Blo 103782 118651 := bstep (se 1 (by rfl) ⟨88988, by rfl⟩ : syracuseStep 118651 = 177977) B177977
theorem B282611 : Blo 103782 282611 := bstep (se 1 (by rfl) ⟨211958, by rfl⟩ : syracuseStep 282611 = 423917) B423917
theorem B249979 : Blo 103782 249979 := bstep (se 1 (by rfl) ⟨187484, by rfl⟩ : syracuseStep 249979 = 374969) B374969
theorem B1724723 : Blo 103782 1724723 := bstep (se 1 (by rfl) ⟨1293542, by rfl⟩ : syracuseStep 1724723 = 2587085) B2587085
theorem B479933 : Blo 103782 479933 := bstep (se 3 (by rfl) ⟨89987, by rfl⟩ : syracuseStep 479933 = 179975) B179975
theorem B51958745 : Blo 103782 51958745 := bstep (se 2 (by rfl) ⟨19484529, by rfl⟩ : syracuseStep 51958745 = 38969059) B38969059
theorem B119803 : Blo 103782 119803 := bstep (se 1 (by rfl) ⟨89852, by rfl⟩ : syracuseStep 119803 = 179705) B179705
theorem B447551 : Blo 103782 447551 := bstep (se 1 (by rfl) ⟨335663, by rfl⟩ : syracuseStep 447551 = 671327) B671327
theorem B119983 : Blo 103782 119983 := bstep (se 1 (by rfl) ⟨89987, by rfl⟩ : syracuseStep 119983 = 179975) B179975
theorem B906785 : Blo 103782 906785 := bstep (se 2 (by rfl) ⟨340044, by rfl⟩ : syracuseStep 906785 = 680089) B680089
theorem B120487 : Blo 103782 120487 := bstep (se 1 (by rfl) ⟨90365, by rfl⟩ : syracuseStep 120487 = 180731) B180731
theorem B448267 : Blo 103782 448267 := bstep (se 1 (by rfl) ⟨336200, by rfl⟩ : syracuseStep 448267 = 672401) B672401
theorem B120775 : Blo 103782 120775 := bstep (se 1 (by rfl) ⟨90581, by rfl⟩ : syracuseStep 120775 = 181163) B181163
theorem B350351 : Blo 103782 350351 := bstep (se 1 (by rfl) ⟨262763, by rfl⟩ : syracuseStep 350351 = 525527) B525527
theorem B678091 : Blo 103782 678091 := bstep (se 1 (by rfl) ⟨508568, by rfl⟩ : syracuseStep 678091 = 1017137) B1017137
theorem B121135 : Blo 103782 121135 := bstep (se 1 (by rfl) ⟨90851, by rfl⟩ : syracuseStep 121135 = 181703) B181703
theorem B612953 : Blo 103782 612953 := bstep (se 2 (by rfl) ⟨229857, by rfl⟩ : syracuseStep 612953 = 459715) B459715
theorem B351485 : Blo 103782 351485 := bstep (se 3 (by rfl) ⟨65903, by rfl⟩ : syracuseStep 351485 = 131807) B131807
theorem B613727 : Blo 103782 613727 := bstep (se 1 (by rfl) ⟨460295, by rfl⟩ : syracuseStep 613727 = 920591) B920591
theorem B909245 : Blo 103782 909245 := bstep (se 3 (by rfl) ⟨170483, by rfl⟩ : syracuseStep 909245 = 340967) B340967
theorem B352295 : Blo 103782 352295 := bstep (se 1 (by rfl) ⟨264221, by rfl⟩ : syracuseStep 352295 = 528443) B528443
theorem B155867 : Blo 103782 155867 := bstep (se 1 (by rfl) ⟨116900, by rfl⟩ : syracuseStep 155867 = 233801) B233801
theorem B155879 : Blo 103782 155879 := bstep (se 1 (by rfl) ⟨116909, by rfl⟩ : syracuseStep 155879 = 233819) B233819
theorem B156041 : Blo 103782 156041 := bstep (se 2 (by rfl) ⟨58515, by rfl⟩ : syracuseStep 156041 = 117031) B117031
theorem B156137 : Blo 103782 156137 := bstep (se 2 (by rfl) ⟨58551, by rfl⟩ : syracuseStep 156137 = 117103) B117103
theorem B156263 : Blo 103782 156263 := bstep (se 1 (by rfl) ⟨117197, by rfl⟩ : syracuseStep 156263 = 234395) B234395
theorem B352943 : Blo 103782 352943 := bstep (se 1 (by rfl) ⟨264707, by rfl⟩ : syracuseStep 352943 = 529415) B529415
theorem B156395 : Blo 103782 156395 := bstep (se 1 (by rfl) ⟨117296, by rfl⟩ : syracuseStep 156395 = 234593) B234593
theorem B156425 : Blo 103782 156425 := bstep (se 2 (by rfl) ⟨58659, by rfl⟩ : syracuseStep 156425 = 117319) B117319
theorem B156527 : Blo 103782 156527 := bstep (se 1 (by rfl) ⟨117395, by rfl⟩ : syracuseStep 156527 = 234791) B234791
theorem B353267 : Blo 103782 353267 := bstep (se 1 (by rfl) ⟨264950, by rfl⟩ : syracuseStep 353267 = 529901) B529901
theorem B1303595 : Blo 103782 1303595 := bstep (se 1 (by rfl) ⟨977696, by rfl⟩ : syracuseStep 1303595 = 1955393) B1955393
theorem B156779 : Blo 103782 156779 := bstep (se 1 (by rfl) ⟨117584, by rfl⟩ : syracuseStep 156779 = 235169) B235169
theorem B157019 : Blo 103782 157019 := bstep (se 1 (by rfl) ⟨117764, by rfl⟩ : syracuseStep 157019 = 235529) B235529
theorem B353807 : Blo 103782 353807 := bstep (se 1 (by rfl) ⟨265355, by rfl⟩ : syracuseStep 353807 = 530711) B530711
theorem B157295 : Blo 103782 157295 := bstep (se 1 (by rfl) ⟨117971, by rfl⟩ : syracuseStep 157295 = 235943) B235943
theorem B222887 : Blo 103782 222887 := bstep (se 1 (by rfl) ⟨167165, by rfl⟩ : syracuseStep 222887 = 334331) B334331
theorem B157367 : Blo 103782 157367 := bstep (se 1 (by rfl) ⟨118025, by rfl⟩ : syracuseStep 157367 = 236051) B236051
theorem B157403 : Blo 103782 157403 := bstep (se 1 (by rfl) ⟨118052, by rfl⟩ : syracuseStep 157403 = 236105) B236105
theorem B157577 : Blo 103782 157577 := bstep (se 2 (by rfl) ⟨59091, by rfl⟩ : syracuseStep 157577 = 118183) B118183
theorem B157679 : Blo 103782 157679 := bstep (se 1 (by rfl) ⟨118259, by rfl⟩ : syracuseStep 157679 = 236519) B236519
theorem B157931 : Blo 103782 157931 := bstep (se 1 (by rfl) ⟨118448, by rfl⟩ : syracuseStep 157931 = 236897) B236897
theorem B157991 : Blo 103782 157991 := bstep (se 1 (by rfl) ⟨118493, by rfl⟩ : syracuseStep 157991 = 236987) B236987
theorem B354617 : Blo 103782 354617 := bstep (se 2 (by rfl) ⟨132981, by rfl⟩ : syracuseStep 354617 = 265963) B265963
theorem B158075 : Blo 103782 158075 := bstep (se 1 (by rfl) ⟨118556, by rfl⟩ : syracuseStep 158075 = 237113) B237113
theorem B289163 : Blo 103782 289163 := bstep (se 1 (by rfl) ⟨216872, by rfl⟩ : syracuseStep 289163 = 433745) B433745
theorem B813563 : Blo 103782 813563 := bstep (se 1 (by rfl) ⟨610172, by rfl⟩ : syracuseStep 813563 = 1220345) B1220345
theorem B354887 : Blo 103782 354887 := bstep (se 1 (by rfl) ⟨266165, by rfl⟩ : syracuseStep 354887 = 532331) B532331
theorem B158345 : Blo 103782 158345 := bstep (se 2 (by rfl) ⟨59379, by rfl⟩ : syracuseStep 158345 = 118759) B118759
theorem B158519 : Blo 103782 158519 := bstep (se 1 (by rfl) ⟨118889, by rfl⟩ : syracuseStep 158519 = 237779) B237779
theorem B158555 : Blo 103782 158555 := bstep (se 1 (by rfl) ⟨118916, by rfl⟩ : syracuseStep 158555 = 237833) B237833
theorem B682937 : Blo 103782 682937 := bstep (se 2 (by rfl) ⟨256101, by rfl⟩ : syracuseStep 682937 = 512203) B512203
theorem B158699 : Blo 103782 158699 := bstep (se 1 (by rfl) ⟨119024, by rfl⟩ : syracuseStep 158699 = 238049) B238049
theorem B158903 : Blo 103782 158903 := bstep (se 1 (by rfl) ⟨119177, by rfl⟩ : syracuseStep 158903 = 238355) B238355
theorem B159143 : Blo 103782 159143 := bstep (se 1 (by rfl) ⟨119357, by rfl⟩ : syracuseStep 159143 = 238715) B238715
theorem B159227 : Blo 103782 159227 := bstep (se 1 (by rfl) ⟨119420, by rfl⟩ : syracuseStep 159227 = 238841) B238841
theorem B355913 : Blo 103782 355913 := bstep (se 2 (by rfl) ⟨133467, by rfl⟩ : syracuseStep 355913 = 266935) B266935
theorem B159323 : Blo 103782 159323 := bstep (se 1 (by rfl) ⟨119492, by rfl⟩ : syracuseStep 159323 = 238985) B238985
theorem B159407 : Blo 103782 159407 := bstep (se 1 (by rfl) ⟨119555, by rfl⟩ : syracuseStep 159407 = 239111) B239111
theorem B1273553 : Blo 103782 1273553 := bstep (se 2 (by rfl) ⟨477582, by rfl⟩ : syracuseStep 1273553 = 955165) B955165
theorem B159527 : Blo 103782 159527 := bstep (se 1 (by rfl) ⟨119645, by rfl⟩ : syracuseStep 159527 = 239291) B239291
theorem B159611 : Blo 103782 159611 := bstep (se 1 (by rfl) ⟨119708, by rfl⟩ : syracuseStep 159611 = 239417) B239417
theorem B913619 : Blo 103782 913619 := bstep (se 1 (by rfl) ⟨685214, by rfl⟩ : syracuseStep 913619 = 1370429) B1370429
theorem B160031 : Blo 103782 160031 := bstep (se 1 (by rfl) ⟨120023, by rfl⟩ : syracuseStep 160031 = 240047) B240047
theorem B160055 : Blo 103782 160055 := bstep (se 1 (by rfl) ⟨120041, by rfl⟩ : syracuseStep 160055 = 240083) B240083
theorem B160127 : Blo 103782 160127 := bstep (se 1 (by rfl) ⟨120095, by rfl⟩ : syracuseStep 160127 = 240191) B240191
theorem B160199 : Blo 103782 160199 := bstep (se 1 (by rfl) ⟨120149, by rfl⟩ : syracuseStep 160199 = 240299) B240299
theorem B1471121 : Blo 103782 1471121 := bstep (se 2 (by rfl) ⟨551670, by rfl⟩ : syracuseStep 1471121 = 1103341) B1103341
theorem B1012445 : Blo 103782 1012445 := bstep (se 3 (by rfl) ⟨189833, by rfl⟩ : syracuseStep 1012445 = 379667) B379667
theorem B160553 : Blo 103782 160553 := bstep (se 2 (by rfl) ⟨60207, by rfl⟩ : syracuseStep 160553 = 120415) B120415
theorem B160559 : Blo 103782 160559 := bstep (se 1 (by rfl) ⟨120419, by rfl⟩ : syracuseStep 160559 = 240839) B240839
theorem B160679 : Blo 103782 160679 := bstep (se 1 (by rfl) ⟨120509, by rfl⟩ : syracuseStep 160679 = 241019) B241019
theorem B357371 : Blo 103782 357371 := bstep (se 1 (by rfl) ⟨268028, by rfl⟩ : syracuseStep 357371 = 536057) B536057
theorem B160763 : Blo 103782 160763 := bstep (se 1 (by rfl) ⟨120572, by rfl⟩ : syracuseStep 160763 = 241145) B241145
theorem B848933 : Blo 103782 848933 := bstep (se 4 (by rfl) ⟨79587, by rfl⟩ : syracuseStep 848933 = 159175) B159175
theorem B160823 : Blo 103782 160823 := bstep (se 1 (by rfl) ⟨120617, by rfl⟩ : syracuseStep 160823 = 241235) B241235
theorem B160943 : Blo 103782 160943 := bstep (se 1 (by rfl) ⟨120707, by rfl⟩ : syracuseStep 160943 = 241415) B241415
theorem B357587 : Blo 103782 357587 := bstep (se 1 (by rfl) ⟨268190, by rfl⟩ : syracuseStep 357587 = 536381) B536381
theorem B357857 : Blo 103782 357857 := bstep (se 2 (by rfl) ⟨134196, by rfl⟩ : syracuseStep 357857 = 268393) B268393
theorem B456263 : Blo 103782 456263 := bstep (se 1 (by rfl) ⟨342197, by rfl⟩ : syracuseStep 456263 = 684395) B684395
theorem B161351 : Blo 103782 161351 := bstep (se 1 (by rfl) ⟨121013, by rfl⟩ : syracuseStep 161351 = 242027) B242027
theorem B161447 : Blo 103782 161447 := bstep (se 1 (by rfl) ⟨121085, by rfl⟩ : syracuseStep 161447 = 242171) B242171
theorem B161531 : Blo 103782 161531 := bstep (se 1 (by rfl) ⟨121148, by rfl⟩ : syracuseStep 161531 = 242297) B242297
theorem B161567 : Blo 103782 161567 := bstep (se 1 (by rfl) ⟨121175, by rfl⟩ : syracuseStep 161567 = 242351) B242351
theorem B161615 : Blo 103782 161615 := bstep (se 1 (by rfl) ⟨121211, by rfl⟩ : syracuseStep 161615 = 242423) B242423
theorem B358505 : Blo 103782 358505 := bstep (se 2 (by rfl) ⟨134439, by rfl⟩ : syracuseStep 358505 = 268879) B268879
theorem B719219 : Blo 103782 719219 := bstep (se 1 (by rfl) ⟨539414, by rfl⟩ : syracuseStep 719219 = 1078829) B1078829
theorem B1571663 : Blo 103782 1571663 := bstep (se 1 (by rfl) ⟨1178747, by rfl⟩ : syracuseStep 1571663 = 2357495) B2357495
theorem B359369 : Blo 103782 359369 := bstep (se 2 (by rfl) ⟨134763, by rfl⟩ : syracuseStep 359369 = 269527) B269527
theorem B359639 : Blo 103782 359639 := bstep (se 1 (by rfl) ⟨269729, by rfl⟩ : syracuseStep 359639 = 539459) B539459
theorem B360179 : Blo 103782 360179 := bstep (se 1 (by rfl) ⟨270134, by rfl⟩ : syracuseStep 360179 = 540269) B540269
theorem B229243 : Blo 103782 229243 := bstep (se 1 (by rfl) ⟨171932, by rfl⟩ : syracuseStep 229243 = 343865) B343865
theorem B229567 : Blo 103782 229567 := bstep (se 1 (by rfl) ⟨172175, by rfl⟩ : syracuseStep 229567 = 344351) B344351
theorem B197225 : Blo 103782 197225 := bstep (se 2 (by rfl) ⟨73959, by rfl⟩ : syracuseStep 197225 = 147919) B147919
theorem B263675 : Blo 103782 263675 := bstep (se 1 (by rfl) ⟨197756, by rfl⟩ : syracuseStep 263675 = 395513) B395513
theorem B362015 : Blo 103782 362015 := bstep (se 1 (by rfl) ⟨271511, by rfl⟩ : syracuseStep 362015 = 543023) B543023
theorem B886625 : Blo 103782 886625 := bstep (se 2 (by rfl) ⟨332484, by rfl⟩ : syracuseStep 886625 = 664969) B664969
theorem B1148995 : Blo 103782 1148995 := bstep (se 1 (by rfl) ⟨861746, by rfl⟩ : syracuseStep 1148995 = 1723493) B1723493
theorem B788777 : Blo 103782 788777 := bstep (se 2 (by rfl) ⟨295791, by rfl⟩ : syracuseStep 788777 = 591583) B591583
theorem B264575 : Blo 103782 264575 := bstep (se 1 (by rfl) ⟨198431, by rfl⟩ : syracuseStep 264575 = 396863) B396863
theorem B362879 : Blo 103782 362879 := bstep (se 1 (by rfl) ⟨272159, by rfl⟩ : syracuseStep 362879 = 544319) B544319
theorem B985483 : Blo 103782 985483 := bstep (se 1 (by rfl) ⟨739112, by rfl⟩ : syracuseStep 985483 = 1478225) B1478225
theorem B1149815 : Blo 103782 1149815 := bstep (se 1 (by rfl) ⟨862361, by rfl⟩ : syracuseStep 1149815 = 1724723) B1724723
theorem B265427 : Blo 103782 265427 := bstep (se 1 (by rfl) ⟨199070, by rfl⟩ : syracuseStep 265427 = 398141) B398141
theorem B34639163 : Blo 103782 34639163 := bstep (se 1 (by rfl) ⟨25979372, by rfl⟩ : syracuseStep 34639163 = 51958745) B51958745
theorem B298367 : Blo 103782 298367 := bstep (se 1 (by rfl) ⟨223775, by rfl⟩ : syracuseStep 298367 = 447551) B447551
theorem B396683 : Blo 103782 396683 := bstep (se 1 (by rfl) ⟨297512, by rfl⟩ : syracuseStep 396683 = 595025) B595025
theorem B855521 : Blo 103782 855521 := bstep (se 2 (by rfl) ⟨320820, by rfl⟩ : syracuseStep 855521 = 641641) B641641
theorem B233567 : Blo 103782 233567 := bstep (se 1 (by rfl) ⟨175175, by rfl⟩ : syracuseStep 233567 = 350351) B350351
theorem B889289 : Blo 103782 889289 := bstep (se 2 (by rfl) ⟨333483, by rfl⟩ : syracuseStep 889289 = 666967) B666967
theorem B234323 : Blo 103782 234323 := bstep (se 1 (by rfl) ⟨175742, by rfl⟩ : syracuseStep 234323 = 351485) B351485
theorem B365753 : Blo 103782 365753 := bstep (se 2 (by rfl) ⟨137157, by rfl⟩ : syracuseStep 365753 = 274315) B274315
theorem B234863 : Blo 103782 234863 := bstep (se 1 (by rfl) ⟨176147, by rfl⟩ : syracuseStep 234863 = 352295) B352295
theorem B15832493 : Blo 103782 15832493 := bstep (se 3 (by rfl) ⟨2968592, by rfl⟩ : syracuseStep 15832493 = 5937185) B5937185
theorem B267695 : Blo 103782 267695 := bstep (se 1 (by rfl) ⟨200771, by rfl⟩ : syracuseStep 267695 = 401543) B401543
theorem B103911 : Blo 103782 103911 := bstep (se 1 (by rfl) ⟨77933, by rfl⟩ : syracuseStep 103911 = 155867) B155867
theorem B103919 : Blo 103782 103919 := bstep (se 1 (by rfl) ⟨77939, by rfl⟩ : syracuseStep 103919 = 155879) B155879
theorem B333305 : Blo 103782 333305 := bstep (se 2 (by rfl) ⟨124989, by rfl⟩ : syracuseStep 333305 = 249979) B249979
theorem B988751 : Blo 103782 988751 := bstep (se 1 (by rfl) ⟨741563, by rfl⟩ : syracuseStep 988751 = 1483127) B1483127
theorem B104027 : Blo 103782 104027 := bstep (se 1 (by rfl) ⟨78020, by rfl⟩ : syracuseStep 104027 = 156041) B156041
theorem B104091 : Blo 103782 104091 := bstep (se 1 (by rfl) ⟨78068, by rfl⟩ : syracuseStep 104091 = 156137) B156137
theorem B104175 : Blo 103782 104175 := bstep (se 1 (by rfl) ⟨78131, by rfl⟩ : syracuseStep 104175 = 156263) B156263
theorem B268019 : Blo 103782 268019 := bstep (se 1 (by rfl) ⟨201014, by rfl⟩ : syracuseStep 268019 = 402029) B402029
theorem B3413771 : Blo 103782 3413771 := bstep (se 1 (by rfl) ⟨2560328, by rfl⟩ : syracuseStep 3413771 = 5120657) B5120657
theorem B235295 : Blo 103782 235295 := bstep (se 1 (by rfl) ⟨176471, by rfl⟩ : syracuseStep 235295 = 352943) B352943
theorem B595775 : Blo 103782 595775 := bstep (se 1 (by rfl) ⟨446831, by rfl⟩ : syracuseStep 595775 = 893663) B893663
theorem B104263 : Blo 103782 104263 := bstep (se 1 (by rfl) ⟨78197, by rfl⟩ : syracuseStep 104263 = 156395) B156395
theorem B104283 : Blo 103782 104283 := bstep (se 1 (by rfl) ⟨78212, by rfl⟩ : syracuseStep 104283 = 156425) B156425
theorem B104351 : Blo 103782 104351 := bstep (se 1 (by rfl) ⟨78263, by rfl⟩ : syracuseStep 104351 = 156527) B156527
theorem B202655 : Blo 103782 202655 := bstep (se 1 (by rfl) ⟨151991, by rfl⟩ : syracuseStep 202655 = 303983) B303983
theorem B235511 : Blo 103782 235511 := bstep (se 1 (by rfl) ⟨176633, by rfl⟩ : syracuseStep 235511 = 353267) B353267
theorem B104519 : Blo 103782 104519 := bstep (se 1 (by rfl) ⟨78389, by rfl⟩ : syracuseStep 104519 = 156779) B156779
theorem B104679 : Blo 103782 104679 := bstep (se 1 (by rfl) ⟨78509, by rfl⟩ : syracuseStep 104679 = 157019) B157019
theorem B4462937 : Blo 103782 4462937 := bstep (se 2 (by rfl) ⟨1673601, by rfl⟩ : syracuseStep 4462937 = 3347203) B3347203
theorem B235871 : Blo 103782 235871 := bstep (se 1 (by rfl) ⟨176903, by rfl⟩ : syracuseStep 235871 = 353807) B353807
theorem B104863 : Blo 103782 104863 := bstep (se 1 (by rfl) ⟨78647, by rfl⟩ : syracuseStep 104863 = 157295) B157295
theorem B104911 : Blo 103782 104911 := bstep (se 1 (by rfl) ⟨78683, by rfl⟩ : syracuseStep 104911 = 157367) B157367
theorem B203239 : Blo 103782 203239 := bstep (se 1 (by rfl) ⟨152429, by rfl⟩ : syracuseStep 203239 = 304859) B304859
theorem B104935 : Blo 103782 104935 := bstep (se 1 (by rfl) ⟨78701, by rfl⟩ : syracuseStep 104935 = 157403) B157403
theorem B236009 : Blo 103782 236009 := bstep (se 2 (by rfl) ⟨88503, by rfl⟩ : syracuseStep 236009 = 177007) B177007
theorem B105051 : Blo 103782 105051 := bstep (se 1 (by rfl) ⟨78788, by rfl⟩ : syracuseStep 105051 = 157577) B157577
theorem B105119 : Blo 103782 105119 := bstep (se 1 (by rfl) ⟨78839, by rfl⟩ : syracuseStep 105119 = 157679) B157679
theorem B531197 : Blo 103782 531197 := bstep (se 3 (by rfl) ⟨99599, by rfl⟩ : syracuseStep 531197 = 199199) B199199
theorem B105287 : Blo 103782 105287 := bstep (se 1 (by rfl) ⟨78965, by rfl⟩ : syracuseStep 105287 = 157931) B157931
theorem B105327 : Blo 103782 105327 := bstep (se 1 (by rfl) ⟨78995, by rfl⟩ : syracuseStep 105327 = 157991) B157991
theorem B236411 : Blo 103782 236411 := bstep (se 1 (by rfl) ⟨177308, by rfl⟩ : syracuseStep 236411 = 354617) B354617
theorem B105383 : Blo 103782 105383 := bstep (se 1 (by rfl) ⟨79037, by rfl⟩ : syracuseStep 105383 = 158075) B158075
theorem B236591 : Blo 103782 236591 := bstep (se 1 (by rfl) ⟨177443, by rfl⟩ : syracuseStep 236591 = 354887) B354887
theorem B105563 : Blo 103782 105563 := bstep (se 1 (by rfl) ⟨79172, by rfl⟩ : syracuseStep 105563 = 158345) B158345
theorem B105679 : Blo 103782 105679 := bstep (se 1 (by rfl) ⟨79259, by rfl⟩ : syracuseStep 105679 = 158519) B158519
theorem B105703 : Blo 103782 105703 := bstep (se 1 (by rfl) ⟨79277, by rfl⟩ : syracuseStep 105703 = 158555) B158555
theorem B105799 : Blo 103782 105799 := bstep (se 1 (by rfl) ⟨79349, by rfl⟩ : syracuseStep 105799 = 158699) B158699
theorem B269639 : Blo 103782 269639 := bstep (se 1 (by rfl) ⟨202229, by rfl⟩ : syracuseStep 269639 = 404459) B404459
theorem B335279 : Blo 103782 335279 := bstep (se 1 (by rfl) ⟨251459, by rfl⟩ : syracuseStep 335279 = 502919) B502919
theorem B105935 : Blo 103782 105935 := bstep (se 1 (by rfl) ⟨79451, by rfl⟩ : syracuseStep 105935 = 158903) B158903
theorem B1547849 : Blo 103782 1547849 := bstep (se 2 (by rfl) ⟨580443, by rfl⟩ : syracuseStep 1547849 = 1160887) B1160887
theorem B106095 : Blo 103782 106095 := bstep (se 1 (by rfl) ⟨79571, by rfl⟩ : syracuseStep 106095 = 159143) B159143
theorem B106151 : Blo 103782 106151 := bstep (se 1 (by rfl) ⟨79613, by rfl⟩ : syracuseStep 106151 = 159227) B159227
theorem B597689 : Blo 103782 597689 := bstep (se 2 (by rfl) ⟨224133, by rfl⟩ : syracuseStep 597689 = 448267) B448267
theorem B237275 : Blo 103782 237275 := bstep (se 1 (by rfl) ⟨177956, by rfl⟩ : syracuseStep 237275 = 355913) B355913
theorem B106215 : Blo 103782 106215 := bstep (se 1 (by rfl) ⟨79661, by rfl⟩ : syracuseStep 106215 = 159323) B159323
theorem B106271 : Blo 103782 106271 := bstep (se 1 (by rfl) ⟨79703, by rfl⟩ : syracuseStep 106271 = 159407) B159407
theorem B106351 : Blo 103782 106351 := bstep (se 1 (by rfl) ⟨79763, by rfl⟩ : syracuseStep 106351 = 159527) B159527
theorem B106407 : Blo 103782 106407 := bstep (se 1 (by rfl) ⟨79805, by rfl⟩ : syracuseStep 106407 = 159611) B159611
theorem B401375 : Blo 103782 401375 := bstep (se 1 (by rfl) ⟨301031, by rfl⟩ : syracuseStep 401375 = 602063) B602063
theorem B237545 : Blo 103782 237545 := bstep (se 2 (by rfl) ⟨89079, by rfl⟩ : syracuseStep 237545 = 178159) B178159
theorem B106687 : Blo 103782 106687 := bstep (se 1 (by rfl) ⟨80015, by rfl⟩ : syracuseStep 106687 = 160031) B160031
theorem B106703 : Blo 103782 106703 := bstep (se 1 (by rfl) ⟨80027, by rfl⟩ : syracuseStep 106703 = 160055) B160055
theorem B106751 : Blo 103782 106751 := bstep (se 1 (by rfl) ⟨80063, by rfl⟩ : syracuseStep 106751 = 160127) B160127
theorem B106799 : Blo 103782 106799 := bstep (se 1 (by rfl) ⟨80099, by rfl⟩ : syracuseStep 106799 = 160199) B160199
theorem B107035 : Blo 103782 107035 := bstep (se 1 (by rfl) ⟨80276, by rfl⟩ : syracuseStep 107035 = 160553) B160553
theorem B107039 : Blo 103782 107039 := bstep (se 1 (by rfl) ⟨80279, by rfl⟩ : syracuseStep 107039 = 160559) B160559
theorem B107119 : Blo 103782 107119 := bstep (se 1 (by rfl) ⟨80339, by rfl⟩ : syracuseStep 107119 = 160679) B160679
theorem B238247 : Blo 103782 238247 := bstep (se 1 (by rfl) ⟨178685, by rfl⟩ : syracuseStep 238247 = 357371) B357371
theorem B107175 : Blo 103782 107175 := bstep (se 1 (by rfl) ⟨80381, by rfl⟩ : syracuseStep 107175 = 160763) B160763
theorem B565955 : Blo 103782 565955 := bstep (se 1 (by rfl) ⟨424466, by rfl⟩ : syracuseStep 565955 = 848933) B848933
theorem B107215 : Blo 103782 107215 := bstep (se 1 (by rfl) ⟨80411, by rfl⟩ : syracuseStep 107215 = 160823) B160823
theorem B107295 : Blo 103782 107295 := bstep (se 1 (by rfl) ⟨80471, by rfl⟩ : syracuseStep 107295 = 160943) B160943
theorem B238391 : Blo 103782 238391 := bstep (se 1 (by rfl) ⟨178793, by rfl⟩ : syracuseStep 238391 = 357587) B357587
theorem B402347 : Blo 103782 402347 := bstep (se 1 (by rfl) ⟨301760, by rfl⟩ : syracuseStep 402347 = 603521) B603521
theorem B238571 : Blo 103782 238571 := bstep (se 1 (by rfl) ⟨178928, by rfl⟩ : syracuseStep 238571 = 357857) B357857
theorem B304175 : Blo 103782 304175 := bstep (se 1 (by rfl) ⟨228131, by rfl⟩ : syracuseStep 304175 = 456263) B456263
theorem B107567 : Blo 103782 107567 := bstep (se 1 (by rfl) ⟨80675, by rfl⟩ : syracuseStep 107567 = 161351) B161351
theorem B107631 : Blo 103782 107631 := bstep (se 1 (by rfl) ⟨80723, by rfl⟩ : syracuseStep 107631 = 161447) B161447
theorem B107687 : Blo 103782 107687 := bstep (se 1 (by rfl) ⟨80765, by rfl⟩ : syracuseStep 107687 = 161531) B161531
theorem B107711 : Blo 103782 107711 := bstep (se 1 (by rfl) ⟨80783, by rfl⟩ : syracuseStep 107711 = 161567) B161567
theorem B107743 : Blo 103782 107743 := bstep (se 1 (by rfl) ⟨80807, by rfl⟩ : syracuseStep 107743 = 161615) B161615
theorem B239003 : Blo 103782 239003 := bstep (se 1 (by rfl) ⟨179252, by rfl⟩ : syracuseStep 239003 = 358505) B358505
theorem B206783 : Blo 103782 206783 := bstep (se 1 (by rfl) ⟨155087, by rfl⟩ : syracuseStep 206783 = 310175) B310175
theorem B239579 : Blo 103782 239579 := bstep (se 1 (by rfl) ⟨179684, by rfl⟩ : syracuseStep 239579 = 359369) B359369
theorem B239759 : Blo 103782 239759 := bstep (se 1 (by rfl) ⟨179819, by rfl⟩ : syracuseStep 239759 = 359639) B359639
theorem B239849 : Blo 103782 239849 := bstep (se 2 (by rfl) ⟨89943, by rfl⟩ : syracuseStep 239849 = 179887) B179887
theorem B764153 : Blo 103782 764153 := bstep (se 2 (by rfl) ⟨286557, by rfl⟩ : syracuseStep 764153 = 573115) B573115
theorem B240119 : Blo 103782 240119 := bstep (se 1 (by rfl) ⟨180089, by rfl⟩ : syracuseStep 240119 = 360179) B360179
theorem B305657 : Blo 103782 305657 := bstep (se 2 (by rfl) ⟨114621, by rfl⟩ : syracuseStep 305657 = 229243) B229243
theorem B666251 : Blo 103782 666251 := bstep (se 1 (by rfl) ⟨499688, by rfl⟩ : syracuseStep 666251 = 999377) B999377
theorem B1911559 : Blo 103782 1911559 := bstep (se 1 (by rfl) ⟨1433669, by rfl⟩ : syracuseStep 1911559 = 2867339) B2867339
theorem B928655 : Blo 103782 928655 := bstep (se 1 (by rfl) ⟨696491, by rfl⟩ : syracuseStep 928655 = 1392983) B1392983
theorem B240713 : Blo 103782 240713 := bstep (se 2 (by rfl) ⟨90267, by rfl⟩ : syracuseStep 240713 = 180535) B180535
theorem B896123 : Blo 103782 896123 := bstep (se 1 (by rfl) ⟨672092, by rfl⟩ : syracuseStep 896123 = 1344185) B1344185
theorem B6007931 : Blo 103782 6007931 := bstep (se 1 (by rfl) ⟨4505948, by rfl⟩ : syracuseStep 6007931 = 9011897) B9011897
theorem B175273 : Blo 103782 175273 := bstep (se 2 (by rfl) ⟨65727, by rfl⟩ : syracuseStep 175273 = 131455) B131455
theorem B601607 : Blo 103782 601607 := bstep (se 1 (by rfl) ⟨451205, by rfl⟩ : syracuseStep 601607 = 902411) B902411
theorem B1945133 : Blo 103782 1945133 := bstep (se 3 (by rfl) ⟨364712, by rfl⟩ : syracuseStep 1945133 = 729425) B729425
theorem B176539 : Blo 103782 176539 := bstep (se 1 (by rfl) ⟨132404, by rfl⟩ : syracuseStep 176539 = 264809) B264809
theorem B307775 : Blo 103782 307775 := bstep (se 1 (by rfl) ⟨230831, by rfl⟩ : syracuseStep 307775 = 461663) B461663
theorem B537191 : Blo 103782 537191 := bstep (se 1 (by rfl) ⟨402893, by rfl⟩ : syracuseStep 537191 = 805787) B805787
theorem B799469 : Blo 103782 799469 := bstep (se 3 (by rfl) ⟨149900, by rfl⟩ : syracuseStep 799469 = 299801) B299801
theorem B242441 : Blo 103782 242441 := bstep (se 2 (by rfl) ⟨90915, by rfl⟩ : syracuseStep 242441 = 181831) B181831
theorem B242495 : Blo 103782 242495 := bstep (se 1 (by rfl) ⟨181871, by rfl⟩ : syracuseStep 242495 = 363743) B363743
theorem B177403 : Blo 103782 177403 := bstep (se 1 (by rfl) ⟨133052, by rfl⟩ : syracuseStep 177403 = 266105) B266105
theorem B898721 : Blo 103782 898721 := bstep (se 2 (by rfl) ⟨337020, by rfl⟩ : syracuseStep 898721 = 674041) B674041
theorem B636797 : Blo 103782 636797 := bstep (se 3 (by rfl) ⟨119399, by rfl⟩ : syracuseStep 636797 = 238799) B238799
theorem B178247 : Blo 103782 178247 := bstep (se 1 (by rfl) ⟨133685, by rfl⟩ : syracuseStep 178247 = 267371) B267371
theorem B1030283 : Blo 103782 1030283 := bstep (se 1 (by rfl) ⟨772712, by rfl⟩ : syracuseStep 1030283 = 1545425) B1545425
theorem B604523 : Blo 103782 604523 := bstep (se 1 (by rfl) ⟨453392, by rfl⟩ : syracuseStep 604523 = 906785) B906785
theorem B899747 : Blo 103782 899747 := bstep (se 1 (by rfl) ⟨674810, by rfl⟩ : syracuseStep 899747 = 1349621) B1349621
theorem B113519 : Blo 103782 113519 := bstep (se 1 (by rfl) ⟨85139, by rfl⟩ : syracuseStep 113519 = 170279) B170279
theorem B179111 : Blo 103782 179111 := bstep (se 1 (by rfl) ⟨134333, by rfl⟩ : syracuseStep 179111 = 268667) B268667
theorem B408635 : Blo 103782 408635 := bstep (se 1 (by rfl) ⟨306476, by rfl⟩ : syracuseStep 408635 = 612953) B612953
theorem B409151 : Blo 103782 409151 := bstep (se 1 (by rfl) ⟨306863, by rfl⟩ : syracuseStep 409151 = 613727) B613727
theorem B376427 : Blo 103782 376427 := bstep (se 1 (by rfl) ⟨282320, by rfl⟩ : syracuseStep 376427 = 564641) B564641
theorem B606163 : Blo 103782 606163 := bstep (se 1 (by rfl) ⟨454622, by rfl⟩ : syracuseStep 606163 = 909245) B909245
theorem B1851569 : Blo 103782 1851569 := bstep (se 2 (by rfl) ⟨694338, by rfl⟩ : syracuseStep 1851569 = 1388677) B1388677
theorem B114895 : Blo 103782 114895 := bstep (se 1 (by rfl) ⟨86171, by rfl⟩ : syracuseStep 114895 = 172343) B172343
theorem B869063 : Blo 103782 869063 := bstep (se 1 (by rfl) ⟨651797, by rfl⟩ : syracuseStep 869063 = 1303595) B1303595
theorem B1917917 : Blo 103782 1917917 := bstep (se 3 (by rfl) ⟨359609, by rfl⟩ : syracuseStep 1917917 = 719219) B719219
theorem B148591 : Blo 103782 148591 := bstep (se 1 (by rfl) ⟨111443, by rfl⟩ : syracuseStep 148591 = 222887) B222887
theorem B1623233 : Blo 103782 1623233 := bstep (se 2 (by rfl) ⟨608712, by rfl⟩ : syracuseStep 1623233 = 1217425) B1217425
theorem B181865 : Blo 103782 181865 := bstep (se 2 (by rfl) ⟨68199, by rfl⟩ : syracuseStep 181865 = 136399) B136399
theorem B542375 : Blo 103782 542375 := bstep (se 1 (by rfl) ⟨406781, by rfl⟩ : syracuseStep 542375 = 813563) B813563
theorem B2050109 : Blo 103782 2050109 := bstep (se 3 (by rfl) ⟨384395, by rfl⟩ : syracuseStep 2050109 = 768791) B768791
theorem B116959 : Blo 103782 116959 := bstep (se 1 (by rfl) ⟨87719, by rfl⟩ : syracuseStep 116959 = 175439) B175439
theorem B609079 : Blo 103782 609079 := bstep (se 1 (by rfl) ⟨456809, by rfl⟩ : syracuseStep 609079 = 913619) B913619
theorem B281465 : Blo 103782 281465 := bstep (se 2 (by rfl) ⟨105549, by rfl⟩ : syracuseStep 281465 = 211099) B211099
theorem B904121 : Blo 103782 904121 := bstep (se 2 (by rfl) ⟨339045, by rfl⟩ : syracuseStep 904121 = 678091) B678091
theorem B117823 : Blo 103782 117823 := bstep (se 1 (by rfl) ⟨88367, by rfl⟩ : syracuseStep 117823 = 176735) B176735
theorem B674963 : Blo 103782 674963 := bstep (se 1 (by rfl) ⟨506222, by rfl⟩ : syracuseStep 674963 = 1012445) B1012445
theorem B380743 : Blo 103782 380743 := bstep (se 1 (by rfl) ⟨285557, by rfl⟩ : syracuseStep 380743 = 571115) B571115
theorem B118939 : Blo 103782 118939 := bstep (se 1 (by rfl) ⟨89204, by rfl⟩ : syracuseStep 118939 = 178409) B178409
theorem B2576765 : Blo 103782 2576765 := bstep (se 3 (by rfl) ⟨483143, by rfl⟩ : syracuseStep 2576765 = 966287) B966287
theorem B120127 : Blo 103782 120127 := bstep (se 1 (by rfl) ⟨90095, by rfl⟩ : syracuseStep 120127 = 180191) B180191
theorem B120559 : Blo 103782 120559 := bstep (se 1 (by rfl) ⟨90419, by rfl⟩ : syracuseStep 120559 = 180839) B180839
theorem B218911 : Blo 103782 218911 := bstep (se 1 (by rfl) ⟨164183, by rfl⟩ : syracuseStep 218911 = 328367) B328367
theorem B120667 : Blo 103782 120667 := bstep (se 1 (by rfl) ⟨90500, by rfl⟩ : syracuseStep 120667 = 181001) B181001
theorem B121063 : Blo 103782 121063 := bstep (se 1 (by rfl) ⟨90797, by rfl⟩ : syracuseStep 121063 = 181595) B181595
theorem B1071863 : Blo 103782 1071863 := bstep (se 1 (by rfl) ⟨803897, by rfl⟩ : syracuseStep 1071863 = 1607795) B1607795
theorem B188407 : Blo 103782 188407 := bstep (se 1 (by rfl) ⟨141305, by rfl⟩ : syracuseStep 188407 = 282611) B282611
theorem B1466435 : Blo 103782 1466435 := bstep (se 1 (by rfl) ⟨1099826, by rfl⟩ : syracuseStep 1466435 = 2199653) B2199653
theorem B352403 : Blo 103782 352403 := bstep (se 1 (by rfl) ⟨264302, by rfl⟩ : syracuseStep 352403 = 528605) B528605
theorem B155855 : Blo 103782 155855 := bstep (se 1 (by rfl) ⟨116891, by rfl⟩ : syracuseStep 155855 = 233783) B233783
theorem B155903 : Blo 103782 155903 := bstep (se 1 (by rfl) ⟨116927, by rfl⟩ : syracuseStep 155903 = 233855) B233855
theorem B352511 : Blo 103782 352511 := bstep (se 1 (by rfl) ⟨264383, by rfl⟩ : syracuseStep 352511 = 528767) B528767
theorem B352673 : Blo 103782 352673 := bstep (se 2 (by rfl) ⟨132252, by rfl⟩ : syracuseStep 352673 = 264505) B264505
theorem B680399 : Blo 103782 680399 := bstep (se 1 (by rfl) ⟨510299, by rfl⟩ : syracuseStep 680399 = 1020599) B1020599
theorem B319955 : Blo 103782 319955 := bstep (se 1 (by rfl) ⟨239966, by rfl⟩ : syracuseStep 319955 = 479933) B479933
theorem B13656721 : Blo 103782 13656721 := bstep (se 2 (by rfl) ⟨5121270, by rfl⟩ : syracuseStep 13656721 = 10242541) B10242541
theorem B222049 : Blo 103782 222049 := bstep (se 2 (by rfl) ⟨83268, by rfl⟩ : syracuseStep 222049 = 166537) B166537
theorem B156719 : Blo 103782 156719 := bstep (se 1 (by rfl) ⟨117539, by rfl⟩ : syracuseStep 156719 = 235079) B235079
theorem B3892313 : Blo 103782 3892313 := bstep (se 2 (by rfl) ⟨1459617, by rfl⟩ : syracuseStep 3892313 = 2919235) B2919235
theorem B156839 : Blo 103782 156839 := bstep (se 1 (by rfl) ⟨117629, by rfl⟩ : syracuseStep 156839 = 235259) B235259
theorem B157211 : Blo 103782 157211 := bstep (se 1 (by rfl) ⟨117908, by rfl⟩ : syracuseStep 157211 = 235817) B235817
theorem B1926737 : Blo 103782 1926737 := bstep (se 2 (by rfl) ⟨722526, by rfl⟩ : syracuseStep 1926737 = 1445053) B1445053
theorem B1238813 : Blo 103782 1238813 := bstep (se 3 (by rfl) ⟨232277, by rfl⟩ : syracuseStep 1238813 = 464555) B464555
theorem B157595 : Blo 103782 157595 := bstep (se 1 (by rfl) ⟨118196, by rfl⟩ : syracuseStep 157595 = 236393) B236393
theorem B354239 : Blo 103782 354239 := bstep (se 1 (by rfl) ⟨265679, by rfl⟩ : syracuseStep 354239 = 531359) B531359
theorem B157631 : Blo 103782 157631 := bstep (se 1 (by rfl) ⟨118223, by rfl⟩ : syracuseStep 157631 = 236447) B236447
theorem B223211 : Blo 103782 223211 := bstep (se 1 (by rfl) ⟨167408, by rfl⟩ : syracuseStep 223211 = 334817) B334817
theorem B354401 : Blo 103782 354401 := bstep (se 2 (by rfl) ⟨132900, by rfl⟩ : syracuseStep 354401 = 265801) B265801
theorem B157817 : Blo 103782 157817 := bstep (se 2 (by rfl) ⟨59181, by rfl⟩ : syracuseStep 157817 = 118363) B118363
theorem B6547877 : Blo 103782 6547877 := bstep (se 4 (by rfl) ⟨613863, by rfl⟩ : syracuseStep 6547877 = 1227727) B1227727
theorem B158201 : Blo 103782 158201 := bstep (se 2 (by rfl) ⟨59325, by rfl⟩ : syracuseStep 158201 = 118651) B118651
theorem B158255 : Blo 103782 158255 := bstep (se 1 (by rfl) ⟨118691, by rfl⟩ : syracuseStep 158255 = 237383) B237383
theorem B485993 : Blo 103782 485993 := bstep (se 2 (by rfl) ⟨182247, by rfl⟩ : syracuseStep 485993 = 364495) B364495
theorem B354941 : Blo 103782 354941 := bstep (se 3 (by rfl) ⟨66551, by rfl⟩ : syracuseStep 354941 = 133103) B133103
theorem B355211 : Blo 103782 355211 := bstep (se 1 (by rfl) ⟨266408, by rfl⟩ : syracuseStep 355211 = 532817) B532817
theorem B158687 : Blo 103782 158687 := bstep (se 1 (by rfl) ⟨119015, by rfl⟩ : syracuseStep 158687 = 238031) B238031
theorem B159131 : Blo 103782 159131 := bstep (se 1 (by rfl) ⟨119348, by rfl⟩ : syracuseStep 159131 = 238697) B238697
theorem B355751 : Blo 103782 355751 := bstep (se 1 (by rfl) ⟨266813, by rfl⟩ : syracuseStep 355751 = 533627) B533627
theorem B290375 : Blo 103782 290375 := bstep (se 1 (by rfl) ⟨217781, by rfl⟩ : syracuseStep 290375 = 435563) B435563
theorem B159551 : Blo 103782 159551 := bstep (se 1 (by rfl) ⟨119663, by rfl⟩ : syracuseStep 159551 = 239327) B239327
theorem B356183 : Blo 103782 356183 := bstep (se 1 (by rfl) ⟨267137, by rfl⟩ : syracuseStep 356183 = 534275) B534275
theorem B815021 : Blo 103782 815021 := bstep (se 3 (by rfl) ⟨152816, by rfl⟩ : syracuseStep 815021 = 305633) B305633
theorem B356345 : Blo 103782 356345 := bstep (se 2 (by rfl) ⟨133629, by rfl⟩ : syracuseStep 356345 = 267259) B267259
theorem B159737 : Blo 103782 159737 := bstep (se 2 (by rfl) ⟨59901, by rfl⟩ : syracuseStep 159737 = 119803) B119803
theorem B487417 : Blo 103782 487417 := bstep (se 2 (by rfl) ⟨182781, by rfl⟩ : syracuseStep 487417 = 365563) B365563
theorem B159977 : Blo 103782 159977 := bstep (se 2 (by rfl) ⟨59991, by rfl⟩ : syracuseStep 159977 = 119983) B119983
theorem B356615 : Blo 103782 356615 := bstep (se 1 (by rfl) ⟨267461, by rfl⟩ : syracuseStep 356615 = 534923) B534923
theorem B192775 : Blo 103782 192775 := bstep (se 1 (by rfl) ⟨144581, by rfl⟩ : syracuseStep 192775 = 289163) B289163
theorem B160103 : Blo 103782 160103 := bstep (se 1 (by rfl) ⟨120077, by rfl⟩ : syracuseStep 160103 = 240155) B240155
theorem B455291 : Blo 103782 455291 := bstep (se 1 (by rfl) ⟨341468, by rfl⟩ : syracuseStep 455291 = 682937) B682937
theorem B356993 : Blo 103782 356993 := bstep (se 2 (by rfl) ⟨133872, by rfl⟩ : syracuseStep 356993 = 267745) B267745
theorem B160649 : Blo 103782 160649 := bstep (se 2 (by rfl) ⟨60243, by rfl⟩ : syracuseStep 160649 = 120487) B120487
theorem B357263 : Blo 103782 357263 := bstep (se 1 (by rfl) ⟨267947, by rfl⟩ : syracuseStep 357263 = 535895) B535895
theorem B422975 : Blo 103782 422975 := bstep (se 1 (by rfl) ⟨317231, by rfl⟩ : syracuseStep 422975 = 634463) B634463
theorem B849035 : Blo 103782 849035 := bstep (se 1 (by rfl) ⟨636776, by rfl⟩ : syracuseStep 849035 = 1273553) B1273553
theorem B161033 : Blo 103782 161033 := bstep (se 2 (by rfl) ⟨60387, by rfl⟩ : syracuseStep 161033 = 120775) B120775
theorem B357695 : Blo 103782 357695 := bstep (se 1 (by rfl) ⟨268271, by rfl⟩ : syracuseStep 357695 = 536543) B536543
theorem B161087 : Blo 103782 161087 := bstep (se 1 (by rfl) ⟨120815, by rfl⟩ : syracuseStep 161087 = 241631) B241631
theorem B357803 : Blo 103782 357803 := bstep (se 1 (by rfl) ⟨268352, by rfl⟩ : syracuseStep 357803 = 536705) B536705
theorem B685523 : Blo 103782 685523 := bstep (se 1 (by rfl) ⟨514142, by rfl⟩ : syracuseStep 685523 = 1028285) B1028285
theorem B161513 : Blo 103782 161513 := bstep (se 2 (by rfl) ⟨60567, by rfl⟩ : syracuseStep 161513 = 121135) B121135
theorem B161519 : Blo 103782 161519 := bstep (se 1 (by rfl) ⟨121139, by rfl⟩ : syracuseStep 161519 = 242279) B242279
theorem B980747 : Blo 103782 980747 := bstep (se 1 (by rfl) ⟨735560, by rfl⟩ : syracuseStep 980747 = 1471121) B1471121
theorem B227243 : Blo 103782 227243 := bstep (se 1 (by rfl) ⟨170432, by rfl⟩ : syracuseStep 227243 = 340865) B340865
theorem B358343 : Blo 103782 358343 := bstep (se 1 (by rfl) ⟨268757, by rfl⟩ : syracuseStep 358343 = 537515) B537515
theorem B915533 : Blo 103782 915533 := bstep (se 3 (by rfl) ⟨171662, by rfl⟩ : syracuseStep 915533 = 343325) B343325
theorem B817451 : Blo 103782 817451 := bstep (se 1 (by rfl) ⟨613088, by rfl⟩ : syracuseStep 817451 = 1226177) B1226177
theorem B1047775 : Blo 103782 1047775 := bstep (se 1 (by rfl) ⟨785831, by rfl⟩ : syracuseStep 1047775 = 1571663) B1571663
theorem B359869 : Blo 103782 359869 := bstep (se 3 (by rfl) ⟨67475, by rfl⟩ : syracuseStep 359869 = 134951) B134951
theorem B1703405 : Blo 103782 1703405 := bstep (se 3 (by rfl) ⟨319388, by rfl⟩ : syracuseStep 1703405 = 638777) B638777
theorem B131483 : Blo 103782 131483 := bstep (se 1 (by rfl) ⟨98612, by rfl⟩ : syracuseStep 131483 = 197225) B197225
theorem B1278611 : Blo 103782 1278611 := bstep (se 1 (by rfl) ⟨958958, by rfl⟩ : syracuseStep 1278611 = 1917917) B1917917
theorem B1082155 : Blo 103782 1082155 := bstep (se 1 (by rfl) ⟨811616, by rfl⟩ : syracuseStep 1082155 = 1623233) B1623233
theorem B361583 : Blo 103782 361583 := bstep (se 1 (by rfl) ⟨271187, by rfl⟩ : syracuseStep 361583 = 542375) B542375
theorem B296065 : Blo 103782 296065 := bstep (se 2 (by rfl) ⟨111024, by rfl⟩ : syracuseStep 296065 = 222049) B222049
theorem B853213 : Blo 103782 853213 := bstep (se 3 (by rfl) ⟨159977, by rfl⟩ : syracuseStep 853213 = 319955) B319955
theorem B591083 : Blo 103782 591083 := bstep (se 1 (by rfl) ⟨443312, by rfl⟩ : syracuseStep 591083 = 886625) B886625
theorem B198121 : Blo 103782 198121 := bstep (se 2 (by rfl) ⟨74295, by rfl⟩ : syracuseStep 198121 = 148591) B148591
theorem B525851 : Blo 103782 525851 := bstep (se 1 (by rfl) ⟨394388, by rfl⟩ : syracuseStep 525851 = 788777) B788777
theorem B198911 : Blo 103782 198911 := bstep (se 1 (by rfl) ⟨149183, by rfl⟩ : syracuseStep 198911 = 298367) B298367
theorem B264455 : Blo 103782 264455 := bstep (se 1 (by rfl) ⟨198341, by rfl⟩ : syracuseStep 264455 = 396683) B396683
theorem B1083941 : Blo 103782 1083941 := bstep (se 4 (by rfl) ⟨101619, by rfl⟩ : syracuseStep 1083941 = 203239) B203239
theorem B592859 : Blo 103782 592859 := bstep (se 1 (by rfl) ⟨444644, by rfl⟩ : syracuseStep 592859 = 889289) B889289
theorem B1313977 : Blo 103782 1313977 := bstep (se 2 (by rfl) ⟨492741, by rfl⟩ : syracuseStep 1313977 = 985483) B985483
theorem B10554995 : Blo 103782 10554995 := bstep (se 1 (by rfl) ⟨7916246, by rfl⟩ : syracuseStep 10554995 = 15832493) B15832493
theorem B659167 : Blo 103782 659167 := bstep (se 1 (by rfl) ⟨494375, by rfl⟩ : syracuseStep 659167 = 988751) B988751
theorem B397183 : Blo 103782 397183 := bstep (se 1 (by rfl) ⟨297887, by rfl⟩ : syracuseStep 397183 = 595775) B595775
theorem B135103 : Blo 103782 135103 := bstep (se 1 (by rfl) ⟨101327, by rfl⟩ : syracuseStep 135103 = 202655) B202655
theorem B398459 : Blo 103782 398459 := bstep (se 1 (by rfl) ⟨298844, by rfl⟩ : syracuseStep 398459 = 597689) B597689
theorem B267583 : Blo 103782 267583 := bstep (se 1 (by rfl) ⟨200687, by rfl⟩ : syracuseStep 267583 = 401375) B401375
theorem B234935 : Blo 103782 234935 := bstep (se 1 (by rfl) ⟨176201, by rfl⟩ : syracuseStep 234935 = 352403) B352403
theorem B103903 : Blo 103782 103903 := bstep (se 1 (by rfl) ⟨77927, by rfl⟩ : syracuseStep 103903 = 155855) B155855
theorem B103935 : Blo 103782 103935 := bstep (se 1 (by rfl) ⟨77951, by rfl⟩ : syracuseStep 103935 = 155903) B155903
theorem B235007 : Blo 103782 235007 := bstep (se 1 (by rfl) ⟨176255, by rfl⟩ : syracuseStep 235007 = 352511) B352511
theorem B235115 : Blo 103782 235115 := bstep (se 1 (by rfl) ⟨176336, by rfl⟩ : syracuseStep 235115 = 352673) B352673
theorem B235385 : Blo 103782 235385 := bstep (se 2 (by rfl) ⟨88269, by rfl⟩ : syracuseStep 235385 = 176539) B176539
theorem B268231 : Blo 103782 268231 := bstep (se 1 (by rfl) ⟨201173, by rfl⟩ : syracuseStep 268231 = 402347) B402347
theorem B104479 : Blo 103782 104479 := bstep (se 1 (by rfl) ⟨78359, by rfl⟩ : syracuseStep 104479 = 156719) B156719
theorem B2594875 : Blo 103782 2594875 := bstep (se 1 (by rfl) ⟨1946156, by rfl⟩ : syracuseStep 2594875 = 3892313) B3892313
theorem B104559 : Blo 103782 104559 := bstep (se 1 (by rfl) ⟨78419, by rfl⟩ : syracuseStep 104559 = 156839) B156839
theorem B104807 : Blo 103782 104807 := bstep (se 1 (by rfl) ⟨78605, by rfl⟩ : syracuseStep 104807 = 157211) B157211
theorem B1284491 : Blo 103782 1284491 := bstep (se 1 (by rfl) ⟨963368, by rfl⟩ : syracuseStep 1284491 = 1926737) B1926737
theorem B825875 : Blo 103782 825875 := bstep (se 1 (by rfl) ⟨619406, by rfl⟩ : syracuseStep 825875 = 1238813) B1238813
theorem B105063 : Blo 103782 105063 := bstep (se 1 (by rfl) ⟨78797, by rfl⟩ : syracuseStep 105063 = 157595) B157595
theorem B236159 : Blo 103782 236159 := bstep (se 1 (by rfl) ⟨177119, by rfl⟩ : syracuseStep 236159 = 354239) B354239
theorem B105087 : Blo 103782 105087 := bstep (se 1 (by rfl) ⟨78815, by rfl⟩ : syracuseStep 105087 = 157631) B157631
theorem B137855 : Blo 103782 137855 := bstep (se 1 (by rfl) ⟨103391, by rfl⟩ : syracuseStep 137855 = 206783) B206783
theorem B236267 : Blo 103782 236267 := bstep (se 1 (by rfl) ⟨177200, by rfl⟩ : syracuseStep 236267 = 354401) B354401
theorem B105211 : Blo 103782 105211 := bstep (se 1 (by rfl) ⟨78908, by rfl⟩ : syracuseStep 105211 = 157817) B157817
theorem B4365251 : Blo 103782 4365251 := bstep (se 1 (by rfl) ⟨3273938, by rfl⟩ : syracuseStep 4365251 = 6547877) B6547877
theorem B236537 : Blo 103782 236537 := bstep (se 2 (by rfl) ⟨88701, by rfl⟩ : syracuseStep 236537 = 177403) B177403
theorem B105467 : Blo 103782 105467 := bstep (se 1 (by rfl) ⟨79100, by rfl⟩ : syracuseStep 105467 = 158201) B158201
theorem B203771 : Blo 103782 203771 := bstep (se 1 (by rfl) ⟨152828, by rfl⟩ : syracuseStep 203771 = 305657) B305657
theorem B105503 : Blo 103782 105503 := bstep (se 1 (by rfl) ⟨79127, by rfl⟩ : syracuseStep 105503 = 158255) B158255
theorem B236627 : Blo 103782 236627 := bstep (se 1 (by rfl) ⟨177470, by rfl⟩ : syracuseStep 236627 = 354941) B354941
theorem B236807 : Blo 103782 236807 := bstep (se 1 (by rfl) ⟨177605, by rfl⟩ : syracuseStep 236807 = 355211) B355211
theorem B105791 : Blo 103782 105791 := bstep (se 1 (by rfl) ⟨79343, by rfl⟩ : syracuseStep 105791 = 158687) B158687
theorem B597415 : Blo 103782 597415 := bstep (se 1 (by rfl) ⟨448061, by rfl⟩ : syracuseStep 597415 = 896123) B896123
theorem B4005287 : Blo 103782 4005287 := bstep (se 1 (by rfl) ⟨3003965, by rfl⟩ : syracuseStep 4005287 = 6007931) B6007931
theorem B106087 : Blo 103782 106087 := bstep (se 1 (by rfl) ⟨79565, by rfl⟩ : syracuseStep 106087 = 159131) B159131
theorem B237167 : Blo 103782 237167 := bstep (se 1 (by rfl) ⟨177875, by rfl⟩ : syracuseStep 237167 = 355751) B355751
theorem B302717 : Blo 103782 302717 := bstep (se 3 (by rfl) ⟨56759, by rfl⟩ : syracuseStep 302717 = 113519) B113519
theorem B401071 : Blo 103782 401071 := bstep (se 1 (by rfl) ⟨300803, by rfl⟩ : syracuseStep 401071 = 601607) B601607
theorem B106367 : Blo 103782 106367 := bstep (se 1 (by rfl) ⟨79775, by rfl⟩ : syracuseStep 106367 = 159551) B159551
theorem B237455 : Blo 103782 237455 := bstep (se 1 (by rfl) ⟨178091, by rfl⟩ : syracuseStep 237455 = 356183) B356183
theorem B106491 : Blo 103782 106491 := bstep (se 1 (by rfl) ⟨79868, by rfl⟩ : syracuseStep 106491 = 159737) B159737
theorem B237563 : Blo 103782 237563 := bstep (se 1 (by rfl) ⟨178172, by rfl⟩ : syracuseStep 237563 = 356345) B356345
theorem B106651 : Blo 103782 106651 := bstep (se 1 (by rfl) ⟨79988, by rfl⟩ : syracuseStep 106651 = 159977) B159977
theorem B237743 : Blo 103782 237743 := bstep (se 1 (by rfl) ⟨178307, by rfl⟩ : syracuseStep 237743 = 356615) B356615
theorem B106735 : Blo 103782 106735 := bstep (se 1 (by rfl) ⟨80051, by rfl⟩ : syracuseStep 106735 = 160103) B160103
theorem B205183 : Blo 103782 205183 := bstep (se 1 (by rfl) ⟨153887, by rfl⟩ : syracuseStep 205183 = 307775) B307775
theorem B303527 : Blo 103782 303527 := bstep (se 1 (by rfl) ⟨227645, by rfl⟩ : syracuseStep 303527 = 455291) B455291
theorem B237995 : Blo 103782 237995 := bstep (se 1 (by rfl) ⟨178496, by rfl⟩ : syracuseStep 237995 = 356993) B356993
theorem B532979 : Blo 103782 532979 := bstep (se 1 (by rfl) ⟨399734, by rfl⟩ : syracuseStep 532979 = 799469) B799469
theorem B107099 : Blo 103782 107099 := bstep (se 1 (by rfl) ⟨80324, by rfl⟩ : syracuseStep 107099 = 160649) B160649
theorem B238175 : Blo 103782 238175 := bstep (se 1 (by rfl) ⟨178631, by rfl⟩ : syracuseStep 238175 = 357263) B357263
theorem B270985 : Blo 103782 270985 := bstep (se 2 (by rfl) ⟨101619, by rfl⟩ : syracuseStep 270985 = 203239) B203239
theorem B566023 : Blo 103782 566023 := bstep (se 1 (by rfl) ⟨424517, by rfl⟩ : syracuseStep 566023 = 849035) B849035
theorem B107355 : Blo 103782 107355 := bstep (se 1 (by rfl) ⟨80516, by rfl⟩ : syracuseStep 107355 = 161033) B161033
theorem B238463 : Blo 103782 238463 := bstep (se 1 (by rfl) ⟨178847, by rfl⟩ : syracuseStep 238463 = 357695) B357695
theorem B107391 : Blo 103782 107391 := bstep (se 1 (by rfl) ⟨80543, by rfl⟩ : syracuseStep 107391 = 161087) B161087
theorem B238535 : Blo 103782 238535 := bstep (se 1 (by rfl) ⟨178901, by rfl⟩ : syracuseStep 238535 = 357803) B357803
theorem B599147 : Blo 103782 599147 := bstep (se 1 (by rfl) ⟨449360, by rfl⟩ : syracuseStep 599147 = 898721) B898721
theorem B107675 : Blo 103782 107675 := bstep (se 1 (by rfl) ⟨80756, by rfl⟩ : syracuseStep 107675 = 161513) B161513
theorem B107679 : Blo 103782 107679 := bstep (se 1 (by rfl) ⟨80759, by rfl⟩ : syracuseStep 107679 = 161519) B161519
theorem B238895 : Blo 103782 238895 := bstep (se 1 (by rfl) ⟨179171, by rfl⟩ : syracuseStep 238895 = 358343) B358343
theorem B403015 : Blo 103782 403015 := bstep (se 1 (by rfl) ⟨302261, by rfl⟩ : syracuseStep 403015 = 604523) B604523
theorem B599831 : Blo 103782 599831 := bstep (se 1 (by rfl) ⟨449873, by rfl⟩ : syracuseStep 599831 = 899747) B899747
theorem B272423 : Blo 103782 272423 := bstep (se 1 (by rfl) ⟨204317, by rfl⟩ : syracuseStep 272423 = 408635) B408635
theorem B272767 : Blo 103782 272767 := bstep (se 1 (by rfl) ⟨204575, by rfl⟩ : syracuseStep 272767 = 409151) B409151
theorem B3910493 : Blo 103782 3910493 := bstep (se 3 (by rfl) ⟨733217, by rfl⟩ : syracuseStep 3910493 = 1466435) B1466435
theorem B306089 : Blo 103782 306089 := bstep (se 2 (by rfl) ⟨114783, by rfl⟩ : syracuseStep 306089 = 229567) B229567
theorem B175783 : Blo 103782 175783 := bstep (se 1 (by rfl) ⟨131837, by rfl⟩ : syracuseStep 175783 = 263675) B263675
theorem B241343 : Blo 103782 241343 := bstep (se 1 (by rfl) ⟨181007, by rfl⟩ : syracuseStep 241343 = 362015) B362015
theorem B176383 : Blo 103782 176383 := bstep (se 1 (by rfl) ⟨132287, by rfl⟩ : syracuseStep 176383 = 264575) B264575
theorem B241919 : Blo 103782 241919 := bstep (se 1 (by rfl) ⟨181439, by rfl⟩ : syracuseStep 241919 = 362879) B362879
theorem B602747 : Blo 103782 602747 := bstep (se 1 (by rfl) ⟨452060, by rfl⟩ : syracuseStep 602747 = 904121) B904121
theorem B176951 : Blo 103782 176951 := bstep (se 1 (by rfl) ⟨132713, by rfl⟩ : syracuseStep 176951 = 265427) B265427
theorem B570347 : Blo 103782 570347 := bstep (se 1 (by rfl) ⟨427760, by rfl⟩ : syracuseStep 570347 = 855521) B855521
theorem B1717843 : Blo 103782 1717843 := bstep (se 1 (by rfl) ⟨1288382, by rfl⟩ : syracuseStep 1717843 = 2576765) B2576765
theorem B178463 : Blo 103782 178463 := bstep (se 1 (by rfl) ⟨133847, by rfl⟩ : syracuseStep 178463 = 267695) B267695
theorem B178679 : Blo 103782 178679 := bstep (se 1 (by rfl) ⟨134009, by rfl⟩ : syracuseStep 178679 = 268019) B268019
theorem B2275847 : Blo 103782 2275847 := bstep (se 1 (by rfl) ⟨1706885, by rfl⟩ : syracuseStep 2275847 = 3413771) B3413771
theorem B179759 : Blo 103782 179759 := bstep (se 1 (by rfl) ⟨134819, by rfl⟩ : syracuseStep 179759 = 269639) B269639
theorem B1031899 : Blo 103782 1031899 := bstep (se 1 (by rfl) ⟨773924, by rfl⟩ : syracuseStep 1031899 = 1547849) B1547849
theorem B605981 : Blo 103782 605981 := bstep (se 3 (by rfl) ⟨113621, by rfl⟩ : syracuseStep 605981 = 227243) B227243
theorem B377303 : Blo 103782 377303 := bstep (se 1 (by rfl) ⟨282977, by rfl⟩ : syracuseStep 377303 = 565955) B565955
theorem B934789 : Blo 103782 934789 := bstep (se 4 (by rfl) ⟨87636, by rfl⟩ : syracuseStep 934789 = 175273) B175273
theorem B148807 : Blo 103782 148807 := bstep (se 1 (by rfl) ⟨111605, by rfl⟩ : syracuseStep 148807 = 223211) B223211
theorem B509435 : Blo 103782 509435 := bstep (se 1 (by rfl) ⟨382076, by rfl⟩ : syracuseStep 509435 = 764153) B764153
theorem B444167 : Blo 103782 444167 := bstep (se 1 (by rfl) ⟨333125, by rfl⟩ : syracuseStep 444167 = 666251) B666251
theorem B3066173 : Blo 103782 3066173 := bstep (se 3 (by rfl) ⟨574907, by rfl⟩ : syracuseStep 3066173 = 1149815) B1149815
theorem B1296755 : Blo 103782 1296755 := bstep (se 1 (by rfl) ⟨972566, by rfl⟩ : syracuseStep 1296755 = 1945133) B1945133
theorem B543347 : Blo 103782 543347 := bstep (se 1 (by rfl) ⟨407510, by rfl⟩ : syracuseStep 543347 = 815021) B815021
theorem B281983 : Blo 103782 281983 := bstep (se 1 (by rfl) ⟨211487, by rfl⟩ : syracuseStep 281983 = 422975) B422975
theorem B118831 : Blo 103782 118831 := bstep (se 1 (by rfl) ⟨89123, by rfl⟩ : syracuseStep 118831 = 178247) B178247
theorem B610355 : Blo 103782 610355 := bstep (se 1 (by rfl) ⟨457766, by rfl⟩ : syracuseStep 610355 = 915533) B915533
theorem B544967 : Blo 103782 544967 := bstep (se 1 (by rfl) ⟨408725, by rfl⟩ : syracuseStep 544967 = 817451) B817451
theorem B1397033 : Blo 103782 1397033 := bstep (se 2 (by rfl) ⟨523887, by rfl⟩ : syracuseStep 1397033 = 1047775) B1047775
theorem B479825 : Blo 103782 479825 := bstep (se 2 (by rfl) ⟨179934, by rfl⟩ : syracuseStep 479825 = 359869) B359869
theorem B119407 : Blo 103782 119407 := bstep (se 1 (by rfl) ⟨89555, by rfl⟩ : syracuseStep 119407 = 179111) B179111
theorem B1135603 : Blo 103782 1135603 := bstep (se 1 (by rfl) ⟨851702, by rfl⟩ : syracuseStep 1135603 = 1703405) B1703405
theorem B250951 : Blo 103782 250951 := bstep (se 1 (by rfl) ⟨188213, by rfl⟩ : syracuseStep 250951 = 376427) B376427
theorem B808217 : Blo 103782 808217 := bstep (se 2 (by rfl) ⟨303081, by rfl⟩ : syracuseStep 808217 = 606163) B606163
theorem B251209 : Blo 103782 251209 := bstep (se 2 (by rfl) ⟨94203, by rfl⟩ : syracuseStep 251209 = 188407) B188407
theorem B1234379 : Blo 103782 1234379 := bstep (se 1 (by rfl) ⟨925784, by rfl⟩ : syracuseStep 1234379 = 1851569) B1851569
theorem B153193 : Blo 103782 153193 := bstep (se 2 (by rfl) ⟨57447, by rfl⟩ : syracuseStep 153193 = 114895) B114895
theorem B18208961 : Blo 103782 18208961 := bstep (se 2 (by rfl) ⟨6828360, by rfl⟩ : syracuseStep 18208961 = 13656721) B13656721
theorem B121243 : Blo 103782 121243 := bstep (se 1 (by rfl) ⟨90932, by rfl⟩ : syracuseStep 121243 = 181865) B181865
theorem B1366739 : Blo 103782 1366739 := bstep (se 1 (by rfl) ⟨1025054, by rfl⟩ : syracuseStep 1366739 = 2050109) B2050109
theorem B2317501 : Blo 103782 2317501 := bstep (se 3 (by rfl) ⟨434531, by rfl⟩ : syracuseStep 2317501 = 869063) B869063
theorem B187643 : Blo 103782 187643 := bstep (se 1 (by rfl) ⟨140732, by rfl⟩ : syracuseStep 187643 = 281465) B281465
theorem B449975 : Blo 103782 449975 := bstep (se 1 (by rfl) ⟨337481, by rfl⟩ : syracuseStep 449975 = 674963) B674963
theorem B23092775 : Blo 103782 23092775 := bstep (se 1 (by rfl) ⟨17319581, by rfl⟩ : syracuseStep 23092775 = 34639163) B34639163
theorem B155711 : Blo 103782 155711 := bstep (se 1 (by rfl) ⟨116783, by rfl⟩ : syracuseStep 155711 = 233567) B233567
theorem B1531993 : Blo 103782 1531993 := bstep (se 2 (by rfl) ⟨574497, by rfl⟩ : syracuseStep 1531993 = 1148995) B1148995
theorem B811133 : Blo 103782 811133 := bstep (se 3 (by rfl) ⟨152087, by rfl⟩ : syracuseStep 811133 = 304175) B304175
theorem B155945 : Blo 103782 155945 := bstep (se 2 (by rfl) ⟨58479, by rfl⟩ : syracuseStep 155945 = 116959) B116959
theorem B287165 : Blo 103782 287165 := bstep (se 3 (by rfl) ⟨53843, by rfl⟩ : syracuseStep 287165 = 107687) B107687
theorem B975341 : Blo 103782 975341 := bstep (se 3 (by rfl) ⟨182876, by rfl⟩ : syracuseStep 975341 = 365753) B365753
theorem B156215 : Blo 103782 156215 := bstep (se 1 (by rfl) ⟨117161, by rfl⟩ : syracuseStep 156215 = 234323) B234323
theorem B156575 : Blo 103782 156575 := bstep (se 1 (by rfl) ⟨117431, by rfl⟩ : syracuseStep 156575 = 234863) B234863
theorem B222203 : Blo 103782 222203 := bstep (se 1 (by rfl) ⟨166652, by rfl⟩ : syracuseStep 222203 = 333305) B333305
theorem B2548745 : Blo 103782 2548745 := bstep (se 2 (by rfl) ⟨955779, by rfl⟩ : syracuseStep 2548745 = 1911559) B1911559
theorem B812105 : Blo 103782 812105 := bstep (se 2 (by rfl) ⟨304539, by rfl⟩ : syracuseStep 812105 = 609079) B609079
theorem B156863 : Blo 103782 156863 := bstep (se 1 (by rfl) ⟨117647, by rfl⟩ : syracuseStep 156863 = 235295) B235295
theorem B157007 : Blo 103782 157007 := bstep (se 1 (by rfl) ⟨117755, by rfl⟩ : syracuseStep 157007 = 235511) B235511
theorem B157097 : Blo 103782 157097 := bstep (se 2 (by rfl) ⟨58911, by rfl⟩ : syracuseStep 157097 = 117823) B117823
theorem B2975291 : Blo 103782 2975291 := bstep (se 1 (by rfl) ⟨2231468, by rfl⟩ : syracuseStep 2975291 = 4462937) B4462937
theorem B157247 : Blo 103782 157247 := bstep (se 1 (by rfl) ⟨117935, by rfl⟩ : syracuseStep 157247 = 235871) B235871
theorem B157339 : Blo 103782 157339 := bstep (se 1 (by rfl) ⟨118004, by rfl⟩ : syracuseStep 157339 = 236009) B236009
theorem B714575 : Blo 103782 714575 := bstep (se 1 (by rfl) ⟨535931, by rfl⟩ : syracuseStep 714575 = 1071863) B1071863
theorem B354131 : Blo 103782 354131 := bstep (se 1 (by rfl) ⟨265598, by rfl⟩ : syracuseStep 354131 = 531197) B531197
theorem B157607 : Blo 103782 157607 := bstep (se 1 (by rfl) ⟨118205, by rfl⟩ : syracuseStep 157607 = 236411) B236411
theorem B157727 : Blo 103782 157727 := bstep (se 1 (by rfl) ⟨118295, by rfl⟩ : syracuseStep 157727 = 236591) B236591
theorem B223519 : Blo 103782 223519 := bstep (se 1 (by rfl) ⟨167639, by rfl⟩ : syracuseStep 223519 = 335279) B335279
theorem B158183 : Blo 103782 158183 := bstep (se 1 (by rfl) ⟨118637, by rfl⟩ : syracuseStep 158183 = 237275) B237275
theorem B158363 : Blo 103782 158363 := bstep (se 1 (by rfl) ⟨118772, by rfl⟩ : syracuseStep 158363 = 237545) B237545
theorem B649889 : Blo 103782 649889 := bstep (se 2 (by rfl) ⟨243708, by rfl⟩ : syracuseStep 649889 = 487417) B487417
theorem B158585 : Blo 103782 158585 := bstep (se 2 (by rfl) ⟨59469, by rfl⟩ : syracuseStep 158585 = 118939) B118939
theorem B453599 : Blo 103782 453599 := bstep (se 1 (by rfl) ⟨340199, by rfl⟩ : syracuseStep 453599 = 680399) B680399
theorem B257033 : Blo 103782 257033 := bstep (se 2 (by rfl) ⟨96387, by rfl⟩ : syracuseStep 257033 = 192775) B192775
theorem B158831 : Blo 103782 158831 := bstep (se 1 (by rfl) ⟨119123, by rfl⟩ : syracuseStep 158831 = 238247) B238247
theorem B158927 : Blo 103782 158927 := bstep (se 1 (by rfl) ⟨119195, by rfl⟩ : syracuseStep 158927 = 238391) B238391
theorem B159047 : Blo 103782 159047 := bstep (se 1 (by rfl) ⟨119285, by rfl⟩ : syracuseStep 159047 = 238571) B238571
theorem B159335 : Blo 103782 159335 := bstep (se 1 (by rfl) ⟨119501, by rfl⟩ : syracuseStep 159335 = 239003) B239003
theorem B159719 : Blo 103782 159719 := bstep (se 1 (by rfl) ⟨119789, by rfl⟩ : syracuseStep 159719 = 239579) B239579
theorem B159839 : Blo 103782 159839 := bstep (se 1 (by rfl) ⟨119879, by rfl⟩ : syracuseStep 159839 = 239759) B239759
theorem B159899 : Blo 103782 159899 := bstep (se 1 (by rfl) ⟨119924, by rfl⟩ : syracuseStep 159899 = 239849) B239849
theorem B160079 : Blo 103782 160079 := bstep (se 1 (by rfl) ⟨120059, by rfl⟩ : syracuseStep 160079 = 240119) B240119
theorem B323995 : Blo 103782 323995 := bstep (se 1 (by rfl) ⟨242996, by rfl⟩ : syracuseStep 323995 = 485993) B485993
theorem B160169 : Blo 103782 160169 := bstep (se 2 (by rfl) ⟨60063, by rfl⟩ : syracuseStep 160169 = 120127) B120127
theorem B619103 : Blo 103782 619103 := bstep (se 1 (by rfl) ⟨464327, by rfl⟩ : syracuseStep 619103 = 928655) B928655
theorem B160475 : Blo 103782 160475 := bstep (se 1 (by rfl) ⟨120356, by rfl⟩ : syracuseStep 160475 = 240713) B240713
theorem B160745 : Blo 103782 160745 := bstep (se 2 (by rfl) ⟨60279, by rfl⟩ : syracuseStep 160745 = 120559) B120559
theorem B291881 : Blo 103782 291881 := bstep (se 2 (by rfl) ⟨109455, by rfl⟩ : syracuseStep 291881 = 218911) B218911
theorem B193583 : Blo 103782 193583 := bstep (se 1 (by rfl) ⟨145187, by rfl⟩ : syracuseStep 193583 = 290375) B290375
theorem B160889 : Blo 103782 160889 := bstep (se 2 (by rfl) ⟨60333, by rfl⟩ : syracuseStep 160889 = 120667) B120667
theorem B161417 : Blo 103782 161417 := bstep (se 2 (by rfl) ⟨60531, by rfl⟩ : syracuseStep 161417 = 121063) B121063
theorem B358127 : Blo 103782 358127 := bstep (se 1 (by rfl) ⟨268595, by rfl⟩ : syracuseStep 358127 = 537191) B537191
theorem B161627 : Blo 103782 161627 := bstep (se 1 (by rfl) ⟨121220, by rfl⟩ : syracuseStep 161627 = 242441) B242441
theorem B161663 : Blo 103782 161663 := bstep (se 1 (by rfl) ⟨121247, by rfl⟩ : syracuseStep 161663 = 242495) B242495
theorem B457015 : Blo 103782 457015 := bstep (se 1 (by rfl) ⟨342761, by rfl⟩ : syracuseStep 457015 = 685523) B685523
theorem B653831 : Blo 103782 653831 := bstep (se 1 (by rfl) ⟨490373, by rfl⟩ : syracuseStep 653831 = 980747) B980747
theorem B424531 : Blo 103782 424531 := bstep (se 1 (by rfl) ⟨318398, by rfl⟩ : syracuseStep 424531 = 636797) B636797
theorem B686855 : Blo 103782 686855 := bstep (se 1 (by rfl) ⟨515141, by rfl⟩ : syracuseStep 686855 = 1030283) B1030283
theorem B2030629 : Blo 103782 2030629 := bstep (se 4 (by rfl) ⟨190371, by rfl⟩ : syracuseStep 2030629 = 380743) B380743
theorem B852407 : Blo 103782 852407 := bstep (se 1 (by rfl) ⟨639305, by rfl⟩ : syracuseStep 852407 = 1278611) B1278611
theorem B394055 : Blo 103782 394055 := bstep (se 1 (by rfl) ⟨295541, by rfl⟩ : syracuseStep 394055 = 591083) B591083
theorem B361313 : Blo 103782 361313 := bstep (se 2 (by rfl) ⟨135492, by rfl⟩ : syracuseStep 361313 = 270985) B270985
theorem B754697 : Blo 103782 754697 := bstep (se 2 (by rfl) ⟨283011, by rfl⟩ : syracuseStep 754697 = 566023) B566023
theorem B1442873 : Blo 103782 1442873 := bstep (se 2 (by rfl) ⟨541077, by rfl⟩ : syracuseStep 1442873 = 1082155) B1082155
theorem B296111 : Blo 103782 296111 := bstep (se 1 (by rfl) ⟨222083, by rfl⟩ : syracuseStep 296111 = 444167) B444167
theorem B1246385 : Blo 103782 1246385 := bstep (se 2 (by rfl) ⟨467394, by rfl⟩ : syracuseStep 1246385 = 934789) B934789
theorem B132607 : Blo 103782 132607 := bstep (se 1 (by rfl) ⟨99455, by rfl⟩ : syracuseStep 132607 = 198911) B198911
theorem B394753 : Blo 103782 394753 := bstep (se 2 (by rfl) ⟨148032, by rfl⟩ : syracuseStep 394753 = 296065) B296065
theorem B722627 : Blo 103782 722627 := bstep (se 1 (by rfl) ⟨541970, by rfl⟩ : syracuseStep 722627 = 1083941) B1083941
theorem B362231 : Blo 103782 362231 := bstep (se 1 (by rfl) ⟨271673, by rfl⟩ : syracuseStep 362231 = 543347) B543347
theorem B264161 : Blo 103782 264161 := bstep (se 2 (by rfl) ⟨99060, by rfl⟩ : syracuseStep 264161 = 198121) B198121
theorem B395239 : Blo 103782 395239 := bstep (se 1 (by rfl) ⟨296429, by rfl⟩ : syracuseStep 395239 = 592859) B592859
theorem B592541 : Blo 103782 592541 := bstep (se 3 (by rfl) ⟨111101, by rfl⟩ : syracuseStep 592541 = 222203) B222203
theorem B363311 : Blo 103782 363311 := bstep (se 1 (by rfl) ⟨272483, by rfl⟩ : syracuseStep 363311 = 544967) B544967
theorem B298025 : Blo 103782 298025 := bstep (se 2 (by rfl) ⟨111759, by rfl⟩ : syracuseStep 298025 = 223519) B223519
theorem B363689 : Blo 103782 363689 := bstep (se 2 (by rfl) ⟨136383, by rfl⟩ : syracuseStep 363689 = 272767) B272767
theorem B265639 : Blo 103782 265639 := bstep (se 1 (by rfl) ⟨199229, by rfl⟩ : syracuseStep 265639 = 398459) B398459
theorem B856327 : Blo 103782 856327 := bstep (se 1 (by rfl) ⟨642245, by rfl⟩ : syracuseStep 856327 = 1284491) B1284491
theorem B135847 : Blo 103782 135847 := bstep (se 1 (by rfl) ⟨101885, by rfl⟩ : syracuseStep 135847 = 203771) B203771
theorem B234377 : Blo 103782 234377 := bstep (se 2 (by rfl) ⟨87891, by rfl⟩ : syracuseStep 234377 = 175783) B175783
theorem B529577 : Blo 103782 529577 := bstep (se 2 (by rfl) ⟨198591, by rfl⟩ : syracuseStep 529577 = 397183) B397183
theorem B103807 : Blo 103782 103807 := bstep (se 1 (by rfl) ⟨77855, by rfl⟩ : syracuseStep 103807 = 155711) B155711
theorem B103963 : Blo 103782 103963 := bstep (se 1 (by rfl) ⟨77972, by rfl⟩ : syracuseStep 103963 = 155945) B155945
theorem B202351 : Blo 103782 202351 := bstep (se 1 (by rfl) ⟨151763, by rfl⟩ : syracuseStep 202351 = 303527) B303527
theorem B104143 : Blo 103782 104143 := bstep (se 1 (by rfl) ⟨78107, by rfl⟩ : syracuseStep 104143 = 156215) B156215
theorem B431993 : Blo 103782 431993 := bstep (se 2 (by rfl) ⟨161997, by rfl⟩ : syracuseStep 431993 = 323995) B323995
theorem B104383 : Blo 103782 104383 := bstep (se 1 (by rfl) ⟨78287, by rfl⟩ : syracuseStep 104383 = 156575) B156575
theorem B399431 : Blo 103782 399431 := bstep (se 1 (by rfl) ⟨299573, by rfl⟩ : syracuseStep 399431 = 599147) B599147
theorem B104575 : Blo 103782 104575 := bstep (se 1 (by rfl) ⟨78431, by rfl⟩ : syracuseStep 104575 = 156863) B156863
theorem B104671 : Blo 103782 104671 := bstep (se 1 (by rfl) ⟨78503, by rfl⟩ : syracuseStep 104671 = 157007) B157007
theorem B104731 : Blo 103782 104731 := bstep (se 1 (by rfl) ⟨78548, by rfl⟩ : syracuseStep 104731 = 157097) B157097
theorem B104831 : Blo 103782 104831 := bstep (se 1 (by rfl) ⟨78623, by rfl⟩ : syracuseStep 104831 = 157247) B157247
theorem B399887 : Blo 103782 399887 := bstep (se 1 (by rfl) ⟨299915, by rfl⟩ : syracuseStep 399887 = 599831) B599831
theorem B236087 : Blo 103782 236087 := bstep (se 1 (by rfl) ⟨177065, by rfl⟩ : syracuseStep 236087 = 354131) B354131
theorem B105071 : Blo 103782 105071 := bstep (se 1 (by rfl) ⟨78803, by rfl⟩ : syracuseStep 105071 = 157607) B157607
theorem B1514137 : Blo 103782 1514137 := bstep (se 2 (by rfl) ⟨567801, by rfl⟩ : syracuseStep 1514137 = 1135603) B1135603
theorem B105151 : Blo 103782 105151 := bstep (se 1 (by rfl) ⟨78863, by rfl⟩ : syracuseStep 105151 = 157727) B157727
theorem B334601 : Blo 103782 334601 := bstep (se 2 (by rfl) ⟨125475, by rfl⟩ : syracuseStep 334601 = 250951) B250951
theorem B105455 : Blo 103782 105455 := bstep (se 1 (by rfl) ⟨79091, by rfl⟩ : syracuseStep 105455 = 158183) B158183
theorem B367613 : Blo 103782 367613 := bstep (se 3 (by rfl) ⟨68927, by rfl⟩ : syracuseStep 367613 = 137855) B137855
theorem B793637 : Blo 103782 793637 := bstep (se 4 (by rfl) ⟨74403, by rfl⟩ : syracuseStep 793637 = 148807) B148807
theorem B334945 : Blo 103782 334945 := bstep (se 2 (by rfl) ⟨125604, by rfl⟩ : syracuseStep 334945 = 251209) B251209
theorem B105575 : Blo 103782 105575 := bstep (se 1 (by rfl) ⟨79181, by rfl⟩ : syracuseStep 105575 = 158363) B158363
theorem B433259 : Blo 103782 433259 := bstep (se 1 (by rfl) ⟨324944, by rfl⟩ : syracuseStep 433259 = 649889) B649889
theorem B105723 : Blo 103782 105723 := bstep (se 1 (by rfl) ⟨79292, by rfl⟩ : syracuseStep 105723 = 158585) B158585
theorem B204059 : Blo 103782 204059 := bstep (se 1 (by rfl) ⟨153044, by rfl⟩ : syracuseStep 204059 = 306089) B306089
theorem B302399 : Blo 103782 302399 := bstep (se 1 (by rfl) ⟨226799, by rfl⟩ : syracuseStep 302399 = 453599) B453599
theorem B105887 : Blo 103782 105887 := bstep (se 1 (by rfl) ⟨79415, by rfl⟩ : syracuseStep 105887 = 158831) B158831
theorem B105951 : Blo 103782 105951 := bstep (se 1 (by rfl) ⟨79463, by rfl⟩ : syracuseStep 105951 = 158927) B158927
theorem B204257 : Blo 103782 204257 := bstep (se 2 (by rfl) ⟨76596, by rfl⟩ : syracuseStep 204257 = 153193) B153193
theorem B106031 : Blo 103782 106031 := bstep (se 1 (by rfl) ⟨79523, by rfl⟩ : syracuseStep 106031 = 159047) B159047
theorem B106223 : Blo 103782 106223 := bstep (se 1 (by rfl) ⟨79667, by rfl⟩ : syracuseStep 106223 = 159335) B159335
theorem B106479 : Blo 103782 106479 := bstep (se 1 (by rfl) ⟨79859, by rfl⟩ : syracuseStep 106479 = 159719) B159719
theorem B106559 : Blo 103782 106559 := bstep (se 1 (by rfl) ⟨79919, by rfl⟩ : syracuseStep 106559 = 159839) B159839
theorem B106599 : Blo 103782 106599 := bstep (se 1 (by rfl) ⟨79949, by rfl⟩ : syracuseStep 106599 = 159899) B159899
theorem B106719 : Blo 103782 106719 := bstep (se 1 (by rfl) ⟨80039, by rfl⟩ : syracuseStep 106719 = 160079) B160079
theorem B106779 : Blo 103782 106779 := bstep (se 1 (by rfl) ⟨80084, by rfl⟩ : syracuseStep 106779 = 160169) B160169
theorem B401831 : Blo 103782 401831 := bstep (se 1 (by rfl) ⟨301373, by rfl⟩ : syracuseStep 401831 = 602747) B602747
theorem B106983 : Blo 103782 106983 := bstep (se 1 (by rfl) ⟨80237, by rfl⟩ : syracuseStep 106983 = 160475) B160475
theorem B107163 : Blo 103782 107163 := bstep (se 1 (by rfl) ⟨80372, by rfl⟩ : syracuseStep 107163 = 160745) B160745
theorem B107259 : Blo 103782 107259 := bstep (se 1 (by rfl) ⟨80444, by rfl⟩ : syracuseStep 107259 = 160889) B160889
theorem B566041 : Blo 103782 566041 := bstep (se 2 (by rfl) ⟨212265, by rfl⟩ : syracuseStep 566041 = 424531) B424531
theorem B107611 : Blo 103782 107611 := bstep (se 1 (by rfl) ⟨80708, by rfl⟩ : syracuseStep 107611 = 161417) B161417
theorem B238751 : Blo 103782 238751 := bstep (se 1 (by rfl) ⟨179063, by rfl⟩ : syracuseStep 238751 = 358127) B358127
theorem B3515557 : Blo 103782 3515557 := bstep (se 4 (by rfl) ⟨329583, by rfl⟩ : syracuseStep 3515557 = 659167) B659167
theorem B107751 : Blo 103782 107751 := bstep (se 1 (by rfl) ⟨80813, by rfl⟩ : syracuseStep 107751 = 161627) B161627
theorem B107775 : Blo 103782 107775 := bstep (se 1 (by rfl) ⟨80831, by rfl⟩ : syracuseStep 107775 = 161663) B161663
theorem B3090001 : Blo 103782 3090001 := bstep (se 2 (by rfl) ⟨1158750, by rfl⟩ : syracuseStep 3090001 = 2317501) B2317501
theorem B1517231 : Blo 103782 1517231 := bstep (se 1 (by rfl) ⟨1137923, by rfl⟩ : syracuseStep 1517231 = 2275847) B2275847
theorem B435887 : Blo 103782 435887 := bstep (se 1 (by rfl) ⟨326915, by rfl⟩ : syracuseStep 435887 = 653831) B653831
theorem B796553 : Blo 103782 796553 := bstep (se 2 (by rfl) ⟨298707, by rfl⟩ : syracuseStep 796553 = 597415) B597415
theorem B534761 : Blo 103782 534761 := bstep (se 2 (by rfl) ⟨200535, by rfl⟩ : syracuseStep 534761 = 401071) B401071
theorem B403987 : Blo 103782 403987 := bstep (se 1 (by rfl) ⟨302990, by rfl⟩ : syracuseStep 403987 = 605981) B605981
theorem B2042657 : Blo 103782 2042657 := bstep (se 2 (by rfl) ⟨765996, by rfl⟩ : syracuseStep 2042657 = 1531993) B1531993
theorem B273577 : Blo 103782 273577 := bstep (se 2 (by rfl) ⟨102591, by rfl⟩ : syracuseStep 273577 = 205183) B205183
theorem B241055 : Blo 103782 241055 := bstep (se 1 (by rfl) ⟨180791, by rfl⟩ : syracuseStep 241055 = 361583) B361583
theorem B339623 : Blo 103782 339623 := bstep (se 1 (by rfl) ⟨254717, by rfl⟩ : syracuseStep 339623 = 509435) B509435
theorem B176303 : Blo 103782 176303 := bstep (se 1 (by rfl) ⟨132227, by rfl⟩ : syracuseStep 176303 = 264455) B264455
theorem B2044115 : Blo 103782 2044115 := bstep (se 1 (by rfl) ⟨1533086, by rfl⟩ : syracuseStep 2044115 = 3066173) B3066173
theorem B864503 : Blo 103782 864503 := bstep (se 1 (by rfl) ⟨648377, by rfl⟩ : syracuseStep 864503 = 1296755) B1296755
theorem B1650941 : Blo 103782 1650941 := bstep (se 3 (by rfl) ⟨309551, by rfl⟩ : syracuseStep 1650941 = 619103) B619103
theorem B537353 : Blo 103782 537353 := bstep (se 2 (by rfl) ⟨201507, by rfl⟩ : syracuseStep 537353 = 403015) B403015
theorem B209785 : Blo 103782 209785 := bstep (se 2 (by rfl) ⟨78669, by rfl⟩ : syracuseStep 209785 = 157339) B157339
theorem B406903 : Blo 103782 406903 := bstep (se 1 (by rfl) ⟨305177, by rfl⟩ : syracuseStep 406903 = 610355) B610355
theorem B931355 : Blo 103782 931355 := bstep (se 1 (by rfl) ⟨698516, by rfl⟩ : syracuseStep 931355 = 1397033) B1397033
theorem B538811 : Blo 103782 538811 := bstep (se 1 (by rfl) ⟨404108, by rfl⟩ : syracuseStep 538811 = 808217) B808217
theorem B3291677 : Blo 103782 3291677 := bstep (se 3 (by rfl) ⟨617189, by rfl⟩ : syracuseStep 3291677 = 1234379) B1234379
theorem B12139307 : Blo 103782 12139307 := bstep (se 1 (by rfl) ⟨9104480, by rfl⟩ : syracuseStep 12139307 = 18208961) B18208961
theorem B1751969 : Blo 103782 1751969 := bstep (se 2 (by rfl) ⟨656988, by rfl⟩ : syracuseStep 1751969 = 1313977) B1313977
theorem B375977 : Blo 103782 375977 := bstep (se 2 (by rfl) ⟨140991, by rfl⟩ : syracuseStep 375977 = 281983) B281983
theorem B2670191 : Blo 103782 2670191 := bstep (se 1 (by rfl) ⟨2002643, by rfl⟩ : syracuseStep 2670191 = 4005287) B4005287
theorem B180137 : Blo 103782 180137 := bstep (se 2 (by rfl) ⟨67551, by rfl⟩ : syracuseStep 180137 = 135103) B135103
theorem B540755 : Blo 103782 540755 := bstep (se 1 (by rfl) ⟨405566, by rfl⟩ : syracuseStep 540755 = 811133) B811133
theorem B541403 : Blo 103782 541403 := bstep (se 1 (by rfl) ⟨406052, by rfl⟩ : syracuseStep 541403 = 812105) B812105
theorem B1983527 : Blo 103782 1983527 := bstep (se 1 (by rfl) ⟨1487645, by rfl⟩ : syracuseStep 1983527 = 2975291) B2975291
theorem B476383 : Blo 103782 476383 := bstep (se 1 (by rfl) ⟨357287, by rfl⟩ : syracuseStep 476383 = 714575) B714575
theorem B181615 : Blo 103782 181615 := bstep (se 1 (by rfl) ⟨136211, by rfl⟩ : syracuseStep 181615 = 272423) B272423
theorem B2606995 : Blo 103782 2606995 := bstep (se 1 (by rfl) ⟨1955246, by rfl⟩ : syracuseStep 2606995 = 3910493) B3910493
theorem B3459833 : Blo 103782 3459833 := bstep (se 2 (by rfl) ⟨1297437, by rfl⟩ : syracuseStep 3459833 = 2594875) B2594875
theorem B609353 : Blo 103782 609353 := bstep (se 2 (by rfl) ⟨228507, by rfl⟩ : syracuseStep 609353 = 457015) B457015
theorem B117967 : Blo 103782 117967 := bstep (se 1 (by rfl) ⟨88475, by rfl⟩ : syracuseStep 117967 = 176951) B176951
theorem B380231 : Blo 103782 380231 := bstep (se 1 (by rfl) ⟨285173, by rfl⟩ : syracuseStep 380231 = 570347) B570347
theorem B1199933 : Blo 103782 1199933 := bstep (se 3 (by rfl) ⟨224987, by rfl⟩ : syracuseStep 1199933 = 449975) B449975
theorem B2707505 : Blo 103782 2707505 := bstep (se 2 (by rfl) ⟨1015314, by rfl⟩ : syracuseStep 2707505 = 2030629) B2030629
theorem B118975 : Blo 103782 118975 := bstep (se 1 (by rfl) ⟨89231, by rfl⟩ : syracuseStep 118975 = 178463) B178463
theorem B807245 : Blo 103782 807245 := bstep (se 3 (by rfl) ⟨151358, by rfl⟩ : syracuseStep 807245 = 302717) B302717
theorem B119119 : Blo 103782 119119 := bstep (se 1 (by rfl) ⟨89339, by rfl⟩ : syracuseStep 119119 = 178679) B178679
theorem B119839 : Blo 103782 119839 := bstep (se 1 (by rfl) ⟨89879, by rfl⟩ : syracuseStep 119839 = 179759) B179759
theorem B350567 : Blo 103782 350567 := bstep (se 1 (by rfl) ⟨262925, by rfl⟩ : syracuseStep 350567 = 525851) B525851
theorem B350621 : Blo 103782 350621 := bstep (se 3 (by rfl) ⟨65741, by rfl⟩ : syracuseStep 350621 = 131483) B131483
theorem B1006141 : Blo 103782 1006141 := bstep (se 3 (by rfl) ⟨188651, by rfl⟩ : syracuseStep 1006141 = 377303) B377303
theorem B940709 : Blo 103782 940709 := bstep (se 4 (by rfl) ⟨88191, by rfl⟩ : syracuseStep 940709 = 176383) B176383
theorem B1137617 : Blo 103782 1137617 := bstep (se 2 (by rfl) ⟨426606, by rfl⟩ : syracuseStep 1137617 = 853213) B853213
theorem B778349 : Blo 103782 778349 := bstep (se 3 (by rfl) ⟨145940, by rfl⟩ : syracuseStep 778349 = 291881) B291881
theorem B319883 : Blo 103782 319883 := bstep (se 1 (by rfl) ⟨239912, by rfl⟩ : syracuseStep 319883 = 479825) B479825
theorem B156623 : Blo 103782 156623 := bstep (se 1 (by rfl) ⟨117467, by rfl⟩ : syracuseStep 156623 = 234935) B234935
theorem B156671 : Blo 103782 156671 := bstep (se 1 (by rfl) ⟨117503, by rfl⟩ : syracuseStep 156671 = 235007) B235007
theorem B156743 : Blo 103782 156743 := bstep (se 1 (by rfl) ⟨117557, by rfl⟩ : syracuseStep 156743 = 235115) B235115
theorem B156923 : Blo 103782 156923 := bstep (se 1 (by rfl) ⟨117692, by rfl⟩ : syracuseStep 156923 = 235385) B235385
theorem B550583 : Blo 103782 550583 := bstep (se 1 (by rfl) ⟨412937, by rfl⟩ : syracuseStep 550583 = 825875) B825875
theorem B157439 : Blo 103782 157439 := bstep (se 1 (by rfl) ⟨118079, by rfl⟩ : syracuseStep 157439 = 236159) B236159
theorem B911159 : Blo 103782 911159 := bstep (se 1 (by rfl) ⟨683369, by rfl⟩ : syracuseStep 911159 = 1366739) B1366739
theorem B157511 : Blo 103782 157511 := bstep (se 1 (by rfl) ⟨118133, by rfl⟩ : syracuseStep 157511 = 236267) B236267
theorem B2910167 : Blo 103782 2910167 := bstep (se 1 (by rfl) ⟨2182625, by rfl⟩ : syracuseStep 2910167 = 4365251) B4365251
theorem B157691 : Blo 103782 157691 := bstep (se 1 (by rfl) ⟨118268, by rfl⟩ : syracuseStep 157691 = 236537) B236537
theorem B157751 : Blo 103782 157751 := bstep (se 1 (by rfl) ⟨118313, by rfl⟩ : syracuseStep 157751 = 236627) B236627
theorem B125095 : Blo 103782 125095 := bstep (se 1 (by rfl) ⟨93821, by rfl⟩ : syracuseStep 125095 = 187643) B187643
theorem B157871 : Blo 103782 157871 := bstep (se 1 (by rfl) ⟨118403, by rfl⟩ : syracuseStep 157871 = 236807) B236807
theorem B15395183 : Blo 103782 15395183 := bstep (se 1 (by rfl) ⟨11546387, by rfl⟩ : syracuseStep 15395183 = 23092775) B23092775
theorem B158111 : Blo 103782 158111 := bstep (se 1 (by rfl) ⟨118583, by rfl⟩ : syracuseStep 158111 = 237167) B237167
theorem B158303 : Blo 103782 158303 := bstep (se 1 (by rfl) ⟨118727, by rfl⟩ : syracuseStep 158303 = 237455) B237455
theorem B158375 : Blo 103782 158375 := bstep (se 1 (by rfl) ⟨118781, by rfl⟩ : syracuseStep 158375 = 237563) B237563
theorem B158441 : Blo 103782 158441 := bstep (se 2 (by rfl) ⟨59415, by rfl⟩ : syracuseStep 158441 = 118831) B118831
theorem B158495 : Blo 103782 158495 := bstep (se 1 (by rfl) ⟨118871, by rfl⟩ : syracuseStep 158495 = 237743) B237743
theorem B158663 : Blo 103782 158663 := bstep (se 1 (by rfl) ⟨118997, by rfl⟩ : syracuseStep 158663 = 237995) B237995
theorem B191443 : Blo 103782 191443 := bstep (se 1 (by rfl) ⟨143582, by rfl⟩ : syracuseStep 191443 = 287165) B287165
theorem B650227 : Blo 103782 650227 := bstep (se 1 (by rfl) ⟨487670, by rfl⟩ : syracuseStep 650227 = 975341) B975341
theorem B355319 : Blo 103782 355319 := bstep (se 1 (by rfl) ⟨266489, by rfl⟩ : syracuseStep 355319 = 532979) B532979
theorem B158783 : Blo 103782 158783 := bstep (se 1 (by rfl) ⟨119087, by rfl⟩ : syracuseStep 158783 = 238175) B238175
theorem B158975 : Blo 103782 158975 := bstep (se 1 (by rfl) ⟨119231, by rfl⟩ : syracuseStep 158975 = 238463) B238463
theorem B159023 : Blo 103782 159023 := bstep (se 1 (by rfl) ⟨119267, by rfl⟩ : syracuseStep 159023 = 238535) B238535
theorem B1699163 : Blo 103782 1699163 := bstep (se 1 (by rfl) ⟨1274372, by rfl⟩ : syracuseStep 1699163 = 2548745) B2548745
theorem B159209 : Blo 103782 159209 := bstep (se 2 (by rfl) ⟨59703, by rfl⟩ : syracuseStep 159209 = 119407) B119407
theorem B159263 : Blo 103782 159263 := bstep (se 1 (by rfl) ⟨119447, by rfl⟩ : syracuseStep 159263 = 238895) B238895
theorem B356777 : Blo 103782 356777 := bstep (se 2 (by rfl) ⟨133791, by rfl⟩ : syracuseStep 356777 = 267583) B267583
theorem B2290457 : Blo 103782 2290457 := bstep (se 2 (by rfl) ⟨858921, by rfl⟩ : syracuseStep 2290457 = 1717843) B1717843
theorem B160895 : Blo 103782 160895 := bstep (se 1 (by rfl) ⟨120671, by rfl⟩ : syracuseStep 160895 = 241343) B241343
theorem B357641 : Blo 103782 357641 := bstep (se 2 (by rfl) ⟨134115, by rfl⟩ : syracuseStep 357641 = 268231) B268231
theorem B685421 : Blo 103782 685421 := bstep (se 3 (by rfl) ⟨128516, by rfl⟩ : syracuseStep 685421 = 257033) B257033
theorem B161279 : Blo 103782 161279 := bstep (se 1 (by rfl) ⟨120959, by rfl⟩ : syracuseStep 161279 = 241919) B241919
theorem B161657 : Blo 103782 161657 := bstep (se 2 (by rfl) ⟨60621, by rfl⟩ : syracuseStep 161657 = 121243) B121243
theorem B129055 : Blo 103782 129055 := bstep (se 1 (by rfl) ⟨96791, by rfl⟩ : syracuseStep 129055 = 193583) B193583
theorem B28146653 : Blo 103782 28146653 := bstep (se 3 (by rfl) ⟨5277497, by rfl⟩ : syracuseStep 28146653 = 10554995) B10554995
theorem B457903 : Blo 103782 457903 := bstep (se 1 (by rfl) ⟨343427, by rfl⟩ : syracuseStep 457903 = 686855) B686855
theorem B1375865 : Blo 103782 1375865 := bstep (se 2 (by rfl) ⟨515949, by rfl⟩ : syracuseStep 1375865 = 1031899) B1031899
theorem B360503 : Blo 103782 360503 := bstep (se 1 (by rfl) ⟨270377, by rfl⟩ : syracuseStep 360503 = 540755) B540755
theorem B360935 : Blo 103782 360935 := bstep (se 1 (by rfl) ⟨270701, by rfl⟩ : syracuseStep 360935 = 541403) B541403
theorem B262703 : Blo 103782 262703 := bstep (se 1 (by rfl) ⟨197027, by rfl⟩ : syracuseStep 262703 = 394055) B394055
theorem B197407 : Blo 103782 197407 := bstep (se 1 (by rfl) ⟨148055, by rfl⟩ : syracuseStep 197407 = 296111) B296111
theorem B853021 : Blo 103782 853021 := bstep (se 3 (by rfl) ⟨159941, by rfl⟩ : syracuseStep 853021 = 319883) B319883
theorem B754721 : Blo 103782 754721 := bstep (se 2 (by rfl) ⟨283020, by rfl⟩ : syracuseStep 754721 = 566041) B566041
theorem B4687409 : Blo 103782 4687409 := bstep (se 2 (by rfl) ⟨1757778, by rfl⟩ : syracuseStep 4687409 = 3515557) B3515557
theorem B395027 : Blo 103782 395027 := bstep (se 1 (by rfl) ⟨296270, by rfl⟩ : syracuseStep 395027 = 592541) B592541
theorem B526337 : Blo 103782 526337 := bstep (se 2 (by rfl) ⟨197376, by rfl⟩ : syracuseStep 526337 = 394753) B394753
theorem B198683 : Blo 103782 198683 := bstep (se 1 (by rfl) ⟨149012, by rfl⟩ : syracuseStep 198683 = 298025) B298025
theorem B3475993 : Blo 103782 3475993 := bstep (se 2 (by rfl) ⟨1303497, by rfl⟩ : syracuseStep 3475993 = 2606995) B2606995
theorem B526985 : Blo 103782 526985 := bstep (se 2 (by rfl) ⟨197619, by rfl⟩ : syracuseStep 526985 = 395239) B395239
theorem B1805003 : Blo 103782 1805003 := bstep (se 1 (by rfl) ⟨1353752, by rfl⟩ : syracuseStep 1805003 = 2707505) B2707505
theorem B166793 : Blo 103782 166793 := bstep (se 2 (by rfl) ⟨62547, by rfl⟩ : syracuseStep 166793 = 125095) B125095
theorem B266287 : Blo 103782 266287 := bstep (se 1 (by rfl) ⟨199715, by rfl⟩ : syracuseStep 266287 = 399431) B399431
theorem B364769 : Blo 103782 364769 := bstep (se 2 (by rfl) ⟨136788, by rfl⟩ : syracuseStep 364769 = 273577) B273577
theorem B233711 : Blo 103782 233711 := bstep (se 1 (by rfl) ⟨175283, by rfl⟩ : syracuseStep 233711 = 350567) B350567
theorem B233747 : Blo 103782 233747 := bstep (se 1 (by rfl) ⟨175310, by rfl⟩ : syracuseStep 233747 = 350621) B350621
theorem B266591 : Blo 103782 266591 := bstep (se 1 (by rfl) ⟨199943, by rfl⟩ : syracuseStep 266591 = 399887) B399887
theorem B627139 : Blo 103782 627139 := bstep (se 1 (by rfl) ⟨470354, by rfl⟩ : syracuseStep 627139 = 940709) B940709
theorem B758411 : Blo 103782 758411 := bstep (se 1 (by rfl) ⟨568808, by rfl⟩ : syracuseStep 758411 = 1137617) B1137617
theorem B529091 : Blo 103782 529091 := bstep (se 1 (by rfl) ⟨396818, by rfl⟩ : syracuseStep 529091 = 793637) B793637
theorem B201599 : Blo 103782 201599 := bstep (se 1 (by rfl) ⟨151199, by rfl⟩ : syracuseStep 201599 = 302399) B302399
theorem B136171 : Blo 103782 136171 := bstep (se 1 (by rfl) ⟨102128, by rfl⟩ : syracuseStep 136171 = 204257) B204257
theorem B1151981 : Blo 103782 1151981 := bstep (se 3 (by rfl) ⟨215996, by rfl⟩ : syracuseStep 1151981 = 431993) B431993
theorem B267887 : Blo 103782 267887 := bstep (se 1 (by rfl) ⟨200915, by rfl⟩ : syracuseStep 267887 = 401831) B401831
theorem B104415 : Blo 103782 104415 := bstep (se 1 (by rfl) ⟨78311, by rfl⟩ : syracuseStep 104415 = 156623) B156623
theorem B104447 : Blo 103782 104447 := bstep (se 1 (by rfl) ⟨78335, by rfl⟩ : syracuseStep 104447 = 156671) B156671
theorem B104495 : Blo 103782 104495 := bstep (se 1 (by rfl) ⟨78371, by rfl⟩ : syracuseStep 104495 = 156743) B156743
theorem B104615 : Blo 103782 104615 := bstep (se 1 (by rfl) ⟨78461, by rfl⟩ : syracuseStep 104615 = 156923) B156923
theorem B367055 : Blo 103782 367055 := bstep (se 1 (by rfl) ⟨275291, by rfl⟩ : syracuseStep 367055 = 550583) B550583
theorem B104959 : Blo 103782 104959 := bstep (se 1 (by rfl) ⟨78719, by rfl⟩ : syracuseStep 104959 = 157439) B157439
theorem B105007 : Blo 103782 105007 := bstep (se 1 (by rfl) ⟨78755, by rfl⟩ : syracuseStep 105007 = 157511) B157511
theorem B531035 : Blo 103782 531035 := bstep (se 1 (by rfl) ⟨398276, by rfl⟩ : syracuseStep 531035 = 796553) B796553
theorem B1940111 : Blo 103782 1940111 := bstep (se 1 (by rfl) ⟨1455083, by rfl⟩ : syracuseStep 1940111 = 2910167) B2910167
theorem B105127 : Blo 103782 105127 := bstep (se 1 (by rfl) ⟨78845, by rfl⟩ : syracuseStep 105127 = 157691) B157691
theorem B105167 : Blo 103782 105167 := bstep (se 1 (by rfl) ⟨78875, by rfl⟩ : syracuseStep 105167 = 157751) B157751
theorem B105247 : Blo 103782 105247 := bstep (se 1 (by rfl) ⟨78935, by rfl⟩ : syracuseStep 105247 = 157871) B157871
theorem B10263455 : Blo 103782 10263455 := bstep (se 1 (by rfl) ⟨7697591, by rfl⟩ : syracuseStep 10263455 = 15395183) B15395183
theorem B105407 : Blo 103782 105407 := bstep (se 1 (by rfl) ⟨79055, by rfl⟩ : syracuseStep 105407 = 158111) B158111
theorem B105535 : Blo 103782 105535 := bstep (se 1 (by rfl) ⟨79151, by rfl⟩ : syracuseStep 105535 = 158303) B158303
theorem B105583 : Blo 103782 105583 := bstep (se 1 (by rfl) ⟨79187, by rfl⟩ : syracuseStep 105583 = 158375) B158375
theorem B105627 : Blo 103782 105627 := bstep (se 1 (by rfl) ⟨79220, by rfl⟩ : syracuseStep 105627 = 158441) B158441
theorem B105663 : Blo 103782 105663 := bstep (se 1 (by rfl) ⟨79247, by rfl⟩ : syracuseStep 105663 = 158495) B158495
theorem B105775 : Blo 103782 105775 := bstep (se 1 (by rfl) ⟨79331, by rfl⟩ : syracuseStep 105775 = 158663) B158663
theorem B236879 : Blo 103782 236879 := bstep (se 1 (by rfl) ⟨177659, by rfl⟩ : syracuseStep 236879 = 355319) B355319
theorem B105855 : Blo 103782 105855 := bstep (se 1 (by rfl) ⟨79391, by rfl⟩ : syracuseStep 105855 = 158783) B158783
theorem B269801 : Blo 103782 269801 := bstep (se 2 (by rfl) ⟨101175, by rfl⟩ : syracuseStep 269801 = 202351) B202351
theorem B105983 : Blo 103782 105983 := bstep (se 1 (by rfl) ⟨79487, by rfl⟩ : syracuseStep 105983 = 158975) B158975
theorem B106015 : Blo 103782 106015 := bstep (se 1 (by rfl) ⟨79511, by rfl⟩ : syracuseStep 106015 = 159023) B159023
theorem B106139 : Blo 103782 106139 := bstep (se 1 (by rfl) ⟨79604, by rfl⟩ : syracuseStep 106139 = 159209) B159209
theorem B106175 : Blo 103782 106175 := bstep (se 1 (by rfl) ⟨79631, by rfl⟩ : syracuseStep 106175 = 159263) B159263
theorem B172073 : Blo 103782 172073 := bstep (se 2 (by rfl) ⟨64527, by rfl⟩ : syracuseStep 172073 = 129055) B129055
theorem B237851 : Blo 103782 237851 := bstep (se 1 (by rfl) ⟨178388, by rfl⟩ : syracuseStep 237851 = 356777) B356777
theorem B107263 : Blo 103782 107263 := bstep (se 1 (by rfl) ⟨80447, by rfl⟩ : syracuseStep 107263 = 160895) B160895
theorem B238427 : Blo 103782 238427 := bstep (se 1 (by rfl) ⟨178820, by rfl⟩ : syracuseStep 238427 = 357641) B357641
theorem B107519 : Blo 103782 107519 := bstep (se 1 (by rfl) ⟨80639, by rfl⟩ : syracuseStep 107519 = 161279) B161279
theorem B107771 : Blo 103782 107771 := bstep (se 1 (by rfl) ⟨80828, by rfl⟩ : syracuseStep 107771 = 161657) B161657
theorem B1780127 : Blo 103782 1780127 := bstep (se 1 (by rfl) ⟨1335095, by rfl⟩ : syracuseStep 1780127 = 2670191) B2670191
theorem B2075597 : Blo 103782 2075597 := bstep (se 3 (by rfl) ⟨389174, by rfl⟩ : syracuseStep 2075597 = 778349) B778349
theorem B568271 : Blo 103782 568271 := bstep (se 1 (by rfl) ⟨426203, by rfl⟩ : syracuseStep 568271 = 852407) B852407
theorem B240875 : Blo 103782 240875 := bstep (se 1 (by rfl) ⟨180656, by rfl⟩ : syracuseStep 240875 = 361313) B361313
theorem B503131 : Blo 103782 503131 := bstep (se 1 (by rfl) ⟨377348, by rfl⟩ : syracuseStep 503131 = 754697) B754697
theorem B1322351 : Blo 103782 1322351 := bstep (se 1 (by rfl) ⟨991763, by rfl⟩ : syracuseStep 1322351 = 1983527) B1983527
theorem B961915 : Blo 103782 961915 := bstep (se 1 (by rfl) ⟨721436, by rfl⟩ : syracuseStep 961915 = 1442873) B1442873
theorem B241487 : Blo 103782 241487 := bstep (se 1 (by rfl) ⟨181115, by rfl⟩ : syracuseStep 241487 = 362231) B362231
theorem B176107 : Blo 103782 176107 := bstep (se 1 (by rfl) ⟨132080, by rfl⟩ : syracuseStep 176107 = 264161) B264161
theorem B635177 : Blo 103782 635177 := bstep (se 2 (by rfl) ⟨238191, by rfl⟩ : syracuseStep 635177 = 476383) B476383
theorem B242153 : Blo 103782 242153 := bstep (se 2 (by rfl) ⟨90807, by rfl⟩ : syracuseStep 242153 = 181615) B181615
theorem B2306555 : Blo 103782 2306555 := bstep (se 1 (by rfl) ⟨1729916, by rfl⟩ : syracuseStep 2306555 = 3459833) B3459833
theorem B242207 : Blo 103782 242207 := bstep (se 1 (by rfl) ⟨181655, by rfl⟩ : syracuseStep 242207 = 363311) B363311
theorem B176809 : Blo 103782 176809 := bstep (se 2 (by rfl) ⟨66303, by rfl⟩ : syracuseStep 176809 = 132607) B132607
theorem B406235 : Blo 103782 406235 := bstep (se 1 (by rfl) ⟨304676, by rfl⟩ : syracuseStep 406235 = 609353) B609353
theorem B242459 : Blo 103782 242459 := bstep (se 1 (by rfl) ⟨181844, by rfl⟩ : syracuseStep 242459 = 363689) B363689
theorem B799955 : Blo 103782 799955 := bstep (se 1 (by rfl) ⟨599966, by rfl⟩ : syracuseStep 799955 = 1199933) B1199933
theorem B538163 : Blo 103782 538163 := bstep (se 1 (by rfl) ⟨403622, by rfl⟩ : syracuseStep 538163 = 807245) B807245
theorem B3323693 : Blo 103782 3323693 := bstep (se 3 (by rfl) ⟨623192, by rfl⟩ : syracuseStep 3323693 = 1246385) B1246385
theorem B538649 : Blo 103782 538649 := bstep (se 2 (by rfl) ⟨201993, by rfl⟩ : syracuseStep 538649 = 403987) B403987
theorem B866969 : Blo 103782 866969 := bstep (se 2 (by rfl) ⟨325113, by rfl⟩ : syracuseStep 866969 = 650227) B650227
theorem B245075 : Blo 103782 245075 := bstep (se 1 (by rfl) ⟨183806, by rfl⟩ : syracuseStep 245075 = 367613) B367613
theorem B181129 : Blo 103782 181129 := bstep (se 2 (by rfl) ⟨67923, by rfl⟩ : syracuseStep 181129 = 135847) B135847
theorem B279713 : Blo 103782 279713 := bstep (se 2 (by rfl) ⟨104892, by rfl⟩ : syracuseStep 279713 = 209785) B209785
theorem B607439 : Blo 103782 607439 := bstep (se 1 (by rfl) ⟨455579, by rfl⟩ : syracuseStep 607439 = 911159) B911159
theorem B542537 : Blo 103782 542537 := bstep (se 2 (by rfl) ⟨203451, by rfl⟩ : syracuseStep 542537 = 406903) B406903
theorem B1361771 : Blo 103782 1361771 := bstep (se 1 (by rfl) ⟨1021328, by rfl⟩ : syracuseStep 1361771 = 2042657) B2042657
theorem B1132775 : Blo 103782 1132775 := bstep (se 1 (by rfl) ⟨849581, by rfl⟩ : syracuseStep 1132775 = 1699163) B1699163
theorem B117535 : Blo 103782 117535 := bstep (se 1 (by rfl) ⟨88151, by rfl⟩ : syracuseStep 117535 = 176303) B176303
theorem B1362743 : Blo 103782 1362743 := bstep (se 1 (by rfl) ⟨1022057, by rfl⟩ : syracuseStep 1362743 = 2044115) B2044115
theorem B576335 : Blo 103782 576335 := bstep (se 1 (by rfl) ⟨432251, by rfl⟩ : syracuseStep 576335 = 864503) B864503
theorem B1100627 : Blo 103782 1100627 := bstep (se 1 (by rfl) ⟨825470, by rfl⟩ : syracuseStep 1100627 = 1650941) B1650941
theorem B1526971 : Blo 103782 1526971 := bstep (se 1 (by rfl) ⟨1145228, by rfl⟩ : syracuseStep 1526971 = 2290457) B2290457
theorem B544157 : Blo 103782 544157 := bstep (se 3 (by rfl) ⟨102029, by rfl⟩ : syracuseStep 544157 = 204059) B204059
theorem B2018849 : Blo 103782 2018849 := bstep (se 2 (by rfl) ⟨757068, by rfl⟩ : syracuseStep 2018849 = 1514137) B1514137
theorem B446593 : Blo 103782 446593 := bstep (se 2 (by rfl) ⟨167472, by rfl⟩ : syracuseStep 446593 = 334945) B334945
theorem B610537 : Blo 103782 610537 := bstep (se 2 (by rfl) ⟨228951, by rfl⟩ : syracuseStep 610537 = 457903) B457903
theorem B1167979 : Blo 103782 1167979 := bstep (se 1 (by rfl) ⟨875984, by rfl⟩ : syracuseStep 1167979 = 1751969) B1751969
theorem B18764435 : Blo 103782 18764435 := bstep (se 1 (by rfl) ⟨14073326, by rfl⟩ : syracuseStep 18764435 = 28146653) B28146653
theorem B250651 : Blo 103782 250651 := bstep (se 1 (by rfl) ⟨187988, by rfl⟩ : syracuseStep 250651 = 375977) B375977
theorem B120091 : Blo 103782 120091 := bstep (se 1 (by rfl) ⟨90068, by rfl⟩ : syracuseStep 120091 = 180137) B180137
theorem B481751 : Blo 103782 481751 := bstep (se 1 (by rfl) ⟨361313, by rfl⟩ : syracuseStep 481751 = 722627) B722627
theorem B4120001 : Blo 103782 4120001 := bstep (se 2 (by rfl) ⟨1545000, by rfl⟩ : syracuseStep 4120001 = 3090001) B3090001
theorem B253487 : Blo 103782 253487 := bstep (se 1 (by rfl) ⟨190115, by rfl⟩ : syracuseStep 253487 = 380231) B380231
theorem B156251 : Blo 103782 156251 := bstep (se 1 (by rfl) ⟨117188, by rfl⟩ : syracuseStep 156251 = 234377) B234377
theorem B353051 : Blo 103782 353051 := bstep (se 1 (by rfl) ⟨264788, by rfl⟩ : syracuseStep 353051 = 529577) B529577
theorem B255257 : Blo 103782 255257 := bstep (se 2 (by rfl) ⟨95721, by rfl⟩ : syracuseStep 255257 = 191443) B191443
theorem B157289 : Blo 103782 157289 := bstep (se 2 (by rfl) ⟨58983, by rfl⟩ : syracuseStep 157289 = 117967) B117967
theorem B157391 : Blo 103782 157391 := bstep (se 1 (by rfl) ⟨118043, by rfl⟩ : syracuseStep 157391 = 236087) B236087
theorem B223067 : Blo 103782 223067 := bstep (se 1 (by rfl) ⟨167300, by rfl⟩ : syracuseStep 223067 = 334601) B334601
theorem B354185 : Blo 103782 354185 := bstep (se 2 (by rfl) ⟨132819, by rfl⟩ : syracuseStep 354185 = 265639) B265639
theorem B288839 : Blo 103782 288839 := bstep (se 1 (by rfl) ⟨216629, by rfl⟩ : syracuseStep 288839 = 433259) B433259
theorem B158633 : Blo 103782 158633 := bstep (se 2 (by rfl) ⟨59487, by rfl⟩ : syracuseStep 158633 = 118975) B118975
theorem B1141769 : Blo 103782 1141769 := bstep (se 2 (by rfl) ⟨428163, by rfl⟩ : syracuseStep 1141769 = 856327) B856327
theorem B158825 : Blo 103782 158825 := bstep (se 2 (by rfl) ⟨59559, by rfl⟩ : syracuseStep 158825 = 119119) B119119
theorem B159167 : Blo 103782 159167 := bstep (se 1 (by rfl) ⟨119375, by rfl⟩ : syracuseStep 159167 = 238751) B238751
theorem B1011487 : Blo 103782 1011487 := bstep (se 1 (by rfl) ⟨758615, by rfl⟩ : syracuseStep 1011487 = 1517231) B1517231
theorem B290591 : Blo 103782 290591 := bstep (se 1 (by rfl) ⟨217943, by rfl⟩ : syracuseStep 290591 = 435887) B435887
theorem B159785 : Blo 103782 159785 := bstep (se 2 (by rfl) ⟨59919, by rfl⟩ : syracuseStep 159785 = 119839) B119839
theorem B356507 : Blo 103782 356507 := bstep (se 1 (by rfl) ⟨267380, by rfl⟩ : syracuseStep 356507 = 534761) B534761
theorem B160703 : Blo 103782 160703 := bstep (se 1 (by rfl) ⟨120527, by rfl⟩ : syracuseStep 160703 = 241055) B241055
theorem B226415 : Blo 103782 226415 := bstep (se 1 (by rfl) ⟨169811, by rfl⟩ : syracuseStep 226415 = 339623) B339623
theorem B358235 : Blo 103782 358235 := bstep (se 1 (by rfl) ⟨268676, by rfl⟩ : syracuseStep 358235 = 537353) B537353
theorem B1341521 : Blo 103782 1341521 := bstep (se 2 (by rfl) ⟨503070, by rfl⟩ : syracuseStep 1341521 = 1006141) B1006141
theorem B456947 : Blo 103782 456947 := bstep (se 1 (by rfl) ⟨342710, by rfl⟩ : syracuseStep 456947 = 685421) B685421
theorem B620903 : Blo 103782 620903 := bstep (se 1 (by rfl) ⟨465677, by rfl⟩ : syracuseStep 620903 = 931355) B931355
theorem B359207 : Blo 103782 359207 := bstep (se 1 (by rfl) ⟨269405, by rfl⟩ : syracuseStep 359207 = 538811) B538811
theorem B2194451 : Blo 103782 2194451 := bstep (se 1 (by rfl) ⟨1645838, by rfl⟩ : syracuseStep 2194451 = 3291677) B3291677
theorem B8092871 : Blo 103782 8092871 := bstep (se 1 (by rfl) ⟨6069653, by rfl⟩ : syracuseStep 8092871 = 12139307) B12139307
theorem B917243 : Blo 103782 917243 := bstep (se 1 (by rfl) ⟨687932, by rfl⟩ : syracuseStep 917243 = 1375865) B1375865
theorem B263209 : Blo 103782 263209 := bstep (se 2 (by rfl) ⟨98703, by rfl⟩ : syracuseStep 263209 = 197407) B197407
theorem B263351 : Blo 103782 263351 := bstep (se 1 (by rfl) ⟨197513, by rfl⟩ : syracuseStep 263351 = 395027) B395027
theorem B361691 : Blo 103782 361691 := bstep (se 1 (by rfl) ⟨271268, by rfl⟩ : syracuseStep 361691 = 542537) B542537
theorem B132455 : Blo 103782 132455 := bstep (se 1 (by rfl) ⟨99341, by rfl⟩ : syracuseStep 132455 = 198683) B198683
theorem B755183 : Blo 103782 755183 := bstep (se 1 (by rfl) ⟨566387, by rfl⟩ : syracuseStep 755183 = 1132775) B1132775
theorem B362771 : Blo 103782 362771 := bstep (se 1 (by rfl) ⟨272078, by rfl⟩ : syracuseStep 362771 = 544157) B544157
theorem B134399 : Blo 103782 134399 := bstep (se 1 (by rfl) ⟨100799, by rfl⟩ : syracuseStep 134399 = 201599) B201599
theorem B2035961 : Blo 103782 2035961 := bstep (se 2 (by rfl) ⟨763485, by rfl⟩ : syracuseStep 2035961 = 1526971) B1526971
theorem B1282553 : Blo 103782 1282553 := bstep (se 2 (by rfl) ⟨480957, by rfl⟩ : syracuseStep 1282553 = 961915) B961915
theorem B1348649 : Blo 103782 1348649 := bstep (se 2 (by rfl) ⟨505743, by rfl⟩ : syracuseStep 1348649 = 1011487) B1011487
theorem B234809 : Blo 103782 234809 := bstep (se 2 (by rfl) ⟨88053, by rfl⟩ : syracuseStep 234809 = 176107) B176107
theorem B595457 : Blo 103782 595457 := bstep (se 2 (by rfl) ⟨223296, by rfl⟩ : syracuseStep 595457 = 446593) B446593
theorem B104167 : Blo 103782 104167 := bstep (se 1 (by rfl) ⟨78125, by rfl⟩ : syracuseStep 104167 = 156251) B156251
theorem B235367 : Blo 103782 235367 := bstep (se 1 (by rfl) ⟨176525, by rfl⟩ : syracuseStep 235367 = 353051) B353051
theorem B170171 : Blo 103782 170171 := bstep (se 1 (by rfl) ⟨127628, by rfl⟩ : syracuseStep 170171 = 255257) B255257
theorem B235745 : Blo 103782 235745 := bstep (se 2 (by rfl) ⟨88404, by rfl⟩ : syracuseStep 235745 = 176809) B176809
theorem B334201 : Blo 103782 334201 := bstep (se 2 (by rfl) ⟨125325, by rfl⟩ : syracuseStep 334201 = 250651) B250651
theorem B104859 : Blo 103782 104859 := bstep (se 1 (by rfl) ⟨78644, by rfl⟩ : syracuseStep 104859 = 157289) B157289
theorem B104927 : Blo 103782 104927 := bstep (se 1 (by rfl) ⟨78695, by rfl⟩ : syracuseStep 104927 = 157391) B157391
theorem B236123 : Blo 103782 236123 := bstep (se 1 (by rfl) ⟨177092, by rfl⟩ : syracuseStep 236123 = 354185) B354185
theorem B1186751 : Blo 103782 1186751 := bstep (se 1 (by rfl) ⟨890063, by rfl⟩ : syracuseStep 1186751 = 1780127) B1780127
theorem B105755 : Blo 103782 105755 := bstep (se 1 (by rfl) ⟨79316, by rfl⟩ : syracuseStep 105755 = 158633) B158633
theorem B1383731 : Blo 103782 1383731 := bstep (se 1 (by rfl) ⟨1037798, by rfl⟩ : syracuseStep 1383731 = 2075597) B2075597
theorem B761179 : Blo 103782 761179 := bstep (se 1 (by rfl) ⟨570884, by rfl⟩ : syracuseStep 761179 = 1141769) B1141769
theorem B105883 : Blo 103782 105883 := bstep (se 1 (by rfl) ⟨79412, by rfl⟩ : syracuseStep 105883 = 158825) B158825
theorem B106111 : Blo 103782 106111 := bstep (se 1 (by rfl) ⟨79583, by rfl⟩ : syracuseStep 106111 = 159167) B159167
theorem B106523 : Blo 103782 106523 := bstep (se 1 (by rfl) ⟨79892, by rfl⟩ : syracuseStep 106523 = 159785) B159785
theorem B237671 : Blo 103782 237671 := bstep (se 1 (by rfl) ⟨178253, by rfl⟩ : syracuseStep 237671 = 356507) B356507
theorem B270823 : Blo 103782 270823 := bstep (se 1 (by rfl) ⟨203117, by rfl⟩ : syracuseStep 270823 = 406235) B406235
theorem B107135 : Blo 103782 107135 := bstep (se 1 (by rfl) ⟨80351, by rfl⟩ : syracuseStep 107135 = 160703) B160703
theorem B533303 : Blo 103782 533303 := bstep (se 1 (by rfl) ⟨399977, by rfl⟩ : syracuseStep 533303 = 799955) B799955
theorem B238823 : Blo 103782 238823 := bstep (se 1 (by rfl) ⟨179117, by rfl⟩ : syracuseStep 238823 = 358235) B358235
theorem B894347 : Blo 103782 894347 := bstep (se 1 (by rfl) ⟨670760, by rfl⟩ : syracuseStep 894347 = 1341521) B1341521
theorem B5383597 : Blo 103782 5383597 := bstep (se 3 (by rfl) ⟨1009424, by rfl⟩ : syracuseStep 5383597 = 2018849) B2018849
theorem B304631 : Blo 103782 304631 := bstep (se 1 (by rfl) ⟨228473, by rfl⟩ : syracuseStep 304631 = 456947) B456947
theorem B239471 : Blo 103782 239471 := bstep (se 1 (by rfl) ⟨179603, by rfl⟩ : syracuseStep 239471 = 359207) B359207
theorem B240335 : Blo 103782 240335 := bstep (se 1 (by rfl) ⟨180251, by rfl⟩ : syracuseStep 240335 = 360503) B360503
theorem B240623 : Blo 103782 240623 := bstep (se 1 (by rfl) ⟨180467, by rfl⟩ : syracuseStep 240623 = 360935) B360935
theorem B175135 : Blo 103782 175135 := bstep (se 1 (by rfl) ⟨131351, by rfl⟩ : syracuseStep 175135 = 262703) B262703
theorem B503147 : Blo 103782 503147 := bstep (se 1 (by rfl) ⟨377360, by rfl⟩ : syracuseStep 503147 = 754721) B754721
theorem B404959 : Blo 103782 404959 := bstep (se 1 (by rfl) ⟨303719, by rfl⟩ : syracuseStep 404959 = 607439) B607439
theorem B3124939 : Blo 103782 3124939 := bstep (se 1 (by rfl) ⟨2343704, by rfl⟩ : syracuseStep 3124939 = 4687409) B4687409
theorem B241505 : Blo 103782 241505 := bstep (se 2 (by rfl) ⟨90564, by rfl⟩ : syracuseStep 241505 = 181129) B181129
theorem B733751 : Blo 103782 733751 := bstep (se 1 (by rfl) ⟨550313, by rfl⟩ : syracuseStep 733751 = 1100627) B1100627
theorem B243179 : Blo 103782 243179 := bstep (se 1 (by rfl) ⟨182384, by rfl⟩ : syracuseStep 243179 = 364769) B364769
theorem B177727 : Blo 103782 177727 := bstep (se 1 (by rfl) ⟨133295, by rfl⟩ : syracuseStep 177727 = 266591) B266591
theorem B603773 : Blo 103782 603773 := bstep (se 3 (by rfl) ⟨113207, by rfl⟩ : syracuseStep 603773 = 226415) B226415
theorem B505607 : Blo 103782 505607 := bstep (se 1 (by rfl) ⟨379205, by rfl⟩ : syracuseStep 505607 = 758411) B758411
theorem B767987 : Blo 103782 767987 := bstep (se 1 (by rfl) ⟨575990, by rfl⟩ : syracuseStep 767987 = 1151981) B1151981
theorem B4634657 : Blo 103782 4634657 := bstep (se 2 (by rfl) ⟨1737996, by rfl⟩ : syracuseStep 4634657 = 3475993) B3475993
theorem B178591 : Blo 103782 178591 := bstep (se 1 (by rfl) ⟨133943, by rfl⟩ : syracuseStep 178591 = 267887) B267887
theorem B244703 : Blo 103782 244703 := bstep (se 1 (by rfl) ⟨183527, by rfl⟩ : syracuseStep 244703 = 367055) B367055
theorem B1293407 : Blo 103782 1293407 := bstep (se 1 (by rfl) ⟨970055, by rfl⟩ : syracuseStep 1293407 = 1940111) B1940111
theorem B670841 : Blo 103782 670841 := bstep (se 2 (by rfl) ⟨251565, by rfl⟩ : syracuseStep 670841 = 503131) B503131
theorem B179867 : Blo 103782 179867 := bstep (se 1 (by rfl) ⟨134900, by rfl⟩ : syracuseStep 179867 = 269801) B269801
theorem B114715 : Blo 103782 114715 := bstep (se 1 (by rfl) ⟨86036, by rfl⟩ : syracuseStep 114715 = 172073) B172073
theorem B836185 : Blo 103782 836185 := bstep (se 2 (by rfl) ⟨313569, by rfl⟩ : syracuseStep 836185 = 627139) B627139
theorem B1557305 : Blo 103782 1557305 := bstep (se 2 (by rfl) ⟨583989, by rfl⟩ : syracuseStep 1557305 = 1167979) B1167979
theorem B1655741 : Blo 103782 1655741 := bstep (se 3 (by rfl) ⟨310451, by rfl⟩ : syracuseStep 1655741 = 620903) B620903
theorem B148711 : Blo 103782 148711 := bstep (se 1 (by rfl) ⟨111533, by rfl⟩ : syracuseStep 148711 = 223067) B223067
theorem B181561 : Blo 103782 181561 := bstep (se 2 (by rfl) ⟨68085, by rfl⟩ : syracuseStep 181561 = 136171) B136171
theorem B378847 : Blo 103782 378847 := bstep (se 1 (by rfl) ⟨284135, by rfl⟩ : syracuseStep 378847 = 568271) B568271
theorem B444781 : Blo 103782 444781 := bstep (se 3 (by rfl) ⟨83396, by rfl⟩ : syracuseStep 444781 = 166793) B166793
theorem B2215795 : Blo 103782 2215795 := bstep (se 1 (by rfl) ⟨1661846, by rfl⟩ : syracuseStep 2215795 = 3323693) B3323693
theorem B675965 : Blo 103782 675965 := bstep (se 3 (by rfl) ⟨126743, by rfl⟩ : syracuseStep 675965 = 253487) B253487
theorem B577979 : Blo 103782 577979 := bstep (se 1 (by rfl) ⟨433484, by rfl⟩ : syracuseStep 577979 = 866969) B866969
theorem B1462967 : Blo 103782 1462967 := bstep (se 1 (by rfl) ⟨1097225, by rfl⟩ : syracuseStep 1462967 = 2194451) B2194451
theorem B5395247 : Blo 103782 5395247 := bstep (se 1 (by rfl) ⟨4046435, by rfl⟩ : syracuseStep 5395247 = 8092871) B8092871
theorem B611495 : Blo 103782 611495 := bstep (se 1 (by rfl) ⟨458621, by rfl⟩ : syracuseStep 611495 = 917243) B917243
theorem B186475 : Blo 103782 186475 := bstep (se 1 (by rfl) ⟨139856, by rfl⟩ : syracuseStep 186475 = 279713) B279713
theorem B907847 : Blo 103782 907847 := bstep (se 1 (by rfl) ⟨680885, by rfl⟩ : syracuseStep 907847 = 1361771) B1361771
theorem B350891 : Blo 103782 350891 := bstep (se 1 (by rfl) ⟨263168, by rfl⟩ : syracuseStep 350891 = 526337) B526337
theorem B1137361 : Blo 103782 1137361 := bstep (se 2 (by rfl) ⟨426510, by rfl⟩ : syracuseStep 1137361 = 853021) B853021
theorem B351323 : Blo 103782 351323 := bstep (se 1 (by rfl) ⟨263492, by rfl⟩ : syracuseStep 351323 = 526985) B526985
theorem B1203335 : Blo 103782 1203335 := bstep (se 1 (by rfl) ⟨902501, by rfl⟩ : syracuseStep 1203335 = 1805003) B1805003
theorem B908495 : Blo 103782 908495 := bstep (se 1 (by rfl) ⟨681371, by rfl⟩ : syracuseStep 908495 = 1362743) B1362743
theorem B155807 : Blo 103782 155807 := bstep (se 1 (by rfl) ⟨116855, by rfl⟩ : syracuseStep 155807 = 233711) B233711
theorem B155831 : Blo 103782 155831 := bstep (se 1 (by rfl) ⟨116873, by rfl⟩ : syracuseStep 155831 = 233747) B233747
theorem B12509623 : Blo 103782 12509623 := bstep (se 1 (by rfl) ⟨9382217, by rfl⟩ : syracuseStep 12509623 = 18764435) B18764435
theorem B352727 : Blo 103782 352727 := bstep (se 1 (by rfl) ⟨264545, by rfl⟩ : syracuseStep 352727 = 529091) B529091
theorem B2614133 : Blo 103782 2614133 := bstep (se 5 (by rfl) ⟨122537, by rfl⟩ : syracuseStep 2614133 = 245075) B245075
theorem B156713 : Blo 103782 156713 := bstep (se 2 (by rfl) ⟨58767, by rfl⟩ : syracuseStep 156713 = 117535) B117535
theorem B321167 : Blo 103782 321167 := bstep (se 1 (by rfl) ⟨240875, by rfl⟩ : syracuseStep 321167 = 481751) B481751
theorem B354023 : Blo 103782 354023 := bstep (se 1 (by rfl) ⟨265517, by rfl⟩ : syracuseStep 354023 = 531035) B531035
theorem B6842303 : Blo 103782 6842303 := bstep (se 1 (by rfl) ⟨5131727, by rfl⟩ : syracuseStep 6842303 = 10263455) B10263455
theorem B157919 : Blo 103782 157919 := bstep (se 1 (by rfl) ⟨118439, by rfl⟩ : syracuseStep 157919 = 236879) B236879
theorem B2746667 : Blo 103782 2746667 := bstep (se 1 (by rfl) ⟨2060000, by rfl⟩ : syracuseStep 2746667 = 4120001) B4120001
theorem B355049 : Blo 103782 355049 := bstep (se 2 (by rfl) ⟨133143, by rfl⟩ : syracuseStep 355049 = 266287) B266287
theorem B158567 : Blo 103782 158567 := bstep (se 1 (by rfl) ⟨118925, by rfl⟩ : syracuseStep 158567 = 237851) B237851
theorem B814049 : Blo 103782 814049 := bstep (se 2 (by rfl) ⟨305268, by rfl⟩ : syracuseStep 814049 = 610537) B610537
theorem B158951 : Blo 103782 158951 := bstep (se 1 (by rfl) ⟨119213, by rfl⟩ : syracuseStep 158951 = 238427) B238427
theorem B192559 : Blo 103782 192559 := bstep (se 1 (by rfl) ⟨144419, by rfl⟩ : syracuseStep 192559 = 288839) B288839
theorem B160121 : Blo 103782 160121 := bstep (se 2 (by rfl) ⟨60045, by rfl⟩ : syracuseStep 160121 = 120091) B120091
theorem B160583 : Blo 103782 160583 := bstep (se 1 (by rfl) ⟨120437, by rfl⟩ : syracuseStep 160583 = 240875) B240875
theorem B1536893 : Blo 103782 1536893 := bstep (se 3 (by rfl) ⟨288167, by rfl⟩ : syracuseStep 1536893 = 576335) B576335
theorem B881567 : Blo 103782 881567 := bstep (se 1 (by rfl) ⟨661175, by rfl⟩ : syracuseStep 881567 = 1322351) B1322351
theorem B193727 : Blo 103782 193727 := bstep (se 1 (by rfl) ⟨145295, by rfl⟩ : syracuseStep 193727 = 290591) B290591
theorem B160991 : Blo 103782 160991 := bstep (se 1 (by rfl) ⟨120743, by rfl⟩ : syracuseStep 160991 = 241487) B241487
theorem B423451 : Blo 103782 423451 := bstep (se 1 (by rfl) ⟨317588, by rfl⟩ : syracuseStep 423451 = 635177) B635177
theorem B161435 : Blo 103782 161435 := bstep (se 1 (by rfl) ⟨121076, by rfl⟩ : syracuseStep 161435 = 242153) B242153
theorem B1537703 : Blo 103782 1537703 := bstep (se 1 (by rfl) ⟨1153277, by rfl⟩ : syracuseStep 1537703 = 2306555) B2306555
theorem B161471 : Blo 103782 161471 := bstep (se 1 (by rfl) ⟨121103, by rfl⟩ : syracuseStep 161471 = 242207) B242207
theorem B161639 : Blo 103782 161639 := bstep (se 1 (by rfl) ⟨121229, by rfl⟩ : syracuseStep 161639 = 242459) B242459
theorem B358775 : Blo 103782 358775 := bstep (se 1 (by rfl) ⟨269081, by rfl⟩ : syracuseStep 358775 = 538163) B538163
theorem B359099 : Blo 103782 359099 := bstep (se 1 (by rfl) ⟨269324, by rfl⟩ : syracuseStep 359099 = 538649) B538649
theorem B361097 : Blo 103782 361097 := bstep (se 2 (by rfl) ⟨135411, by rfl⟩ : syracuseStep 361097 = 270823) B270823
theorem B1114913 : Blo 103782 1114913 := bstep (se 2 (by rfl) ⟨418092, by rfl⟩ : syracuseStep 1114913 = 836185) B836185
theorem B198281 : Blo 103782 198281 := bstep (se 2 (by rfl) ⟨74355, by rfl⟩ : syracuseStep 198281 = 148711) B148711
theorem B7178129 : Blo 103782 7178129 := bstep (se 2 (by rfl) ⟨2691798, by rfl⟩ : syracuseStep 7178129 = 5383597) B5383597
theorem B66717989 : Blo 103782 66717989 := bstep (se 4 (by rfl) ⟨6254811, by rfl⟩ : syracuseStep 66717989 = 12509623) B12509623
theorem B855035 : Blo 103782 855035 := bstep (se 1 (by rfl) ⟨641276, by rfl⟩ : syracuseStep 855035 = 1282553) B1282553
theorem B593041 : Blo 103782 593041 := bstep (se 2 (by rfl) ⟨222390, by rfl⟩ : syracuseStep 593041 = 444781) B444781
theorem B396971 : Blo 103782 396971 := bstep (se 1 (by rfl) ⟨297728, by rfl⟩ : syracuseStep 396971 = 595457) B595457
theorem B233513 : Blo 103782 233513 := bstep (se 2 (by rfl) ⟨87567, by rfl⟩ : syracuseStep 233513 = 175135) B175135
theorem B233927 : Blo 103782 233927 := bstep (se 1 (by rfl) ⟨175445, by rfl⟩ : syracuseStep 233927 = 350891) B350891
theorem B791167 : Blo 103782 791167 := bstep (se 1 (by rfl) ⟨593375, by rfl⟩ : syracuseStep 791167 = 1186751) B1186751
theorem B1348285 : Blo 103782 1348285 := bstep (se 3 (by rfl) ⟨252803, by rfl⟩ : syracuseStep 1348285 = 505607) B505607
theorem B234215 : Blo 103782 234215 := bstep (se 1 (by rfl) ⟨175661, by rfl⟩ : syracuseStep 234215 = 351323) B351323
theorem B922487 : Blo 103782 922487 := bstep (se 1 (by rfl) ⟨691865, by rfl⟩ : syracuseStep 922487 = 1383731) B1383731
theorem B4166585 : Blo 103782 4166585 := bstep (se 2 (by rfl) ⟨1562469, by rfl⟩ : syracuseStep 4166585 = 3124939) B3124939
theorem B2954393 : Blo 103782 2954393 := bstep (se 2 (by rfl) ⟨1107897, by rfl⟩ : syracuseStep 2954393 = 2215795) B2215795
theorem B103871 : Blo 103782 103871 := bstep (se 1 (by rfl) ⟨77903, by rfl⟩ : syracuseStep 103871 = 155807) B155807
theorem B103887 : Blo 103782 103887 := bstep (se 1 (by rfl) ⟨77915, by rfl⟩ : syracuseStep 103887 = 155831) B155831
theorem B235151 : Blo 103782 235151 := bstep (se 1 (by rfl) ⟨176363, by rfl⟩ : syracuseStep 235151 = 352727) B352727
theorem B1742755 : Blo 103782 1742755 := bstep (se 1 (by rfl) ⟨1307066, by rfl⟩ : syracuseStep 1742755 = 2614133) B2614133
theorem B104475 : Blo 103782 104475 := bstep (se 1 (by rfl) ⟨78356, by rfl⟩ : syracuseStep 104475 = 156713) B156713
theorem B596231 : Blo 103782 596231 := bstep (se 1 (by rfl) ⟨447173, by rfl⟩ : syracuseStep 596231 = 894347) B894347
theorem B203087 : Blo 103782 203087 := bstep (se 1 (by rfl) ⟨152315, by rfl⟩ : syracuseStep 203087 = 304631) B304631
theorem B236015 : Blo 103782 236015 := bstep (se 1 (by rfl) ⟨177011, by rfl⟩ : syracuseStep 236015 = 354023) B354023
theorem B4561535 : Blo 103782 4561535 := bstep (se 1 (by rfl) ⟨3421151, by rfl⟩ : syracuseStep 4561535 = 6842303) B6842303
theorem B105279 : Blo 103782 105279 := bstep (se 1 (by rfl) ⟨78959, by rfl⟩ : syracuseStep 105279 = 157919) B157919
theorem B236699 : Blo 103782 236699 := bstep (se 1 (by rfl) ⟨177524, by rfl⟩ : syracuseStep 236699 = 355049) B355049
theorem B105711 : Blo 103782 105711 := bstep (se 1 (by rfl) ⟨79283, by rfl⟩ : syracuseStep 105711 = 158567) B158567
theorem B236969 : Blo 103782 236969 := bstep (se 2 (by rfl) ⟨88863, by rfl⟩ : syracuseStep 236969 = 177727) B177727
theorem B105967 : Blo 103782 105967 := bstep (se 1 (by rfl) ⟨79475, by rfl⟩ : syracuseStep 105967 = 158951) B158951
theorem B335431 : Blo 103782 335431 := bstep (se 1 (by rfl) ⟨251573, by rfl⟩ : syracuseStep 335431 = 503147) B503147
theorem B106747 : Blo 103782 106747 := bstep (se 1 (by rfl) ⟨80060, by rfl⟩ : syracuseStep 106747 = 160121) B160121
theorem B238121 : Blo 103782 238121 := bstep (se 2 (by rfl) ⟨89295, by rfl⟩ : syracuseStep 238121 = 178591) B178591
theorem B107055 : Blo 103782 107055 := bstep (se 1 (by rfl) ⟨80291, by rfl⟩ : syracuseStep 107055 = 160583) B160583
theorem B1024595 : Blo 103782 1024595 := bstep (se 1 (by rfl) ⟨768446, by rfl⟩ : syracuseStep 1024595 = 1536893) B1536893
theorem B107327 : Blo 103782 107327 := bstep (se 1 (by rfl) ⟨80495, by rfl⟩ : syracuseStep 107327 = 160991) B160991
theorem B1516481 : Blo 103782 1516481 := bstep (se 2 (by rfl) ⟨568680, by rfl⟩ : syracuseStep 1516481 = 1137361) B1137361
theorem B402515 : Blo 103782 402515 := bstep (se 1 (by rfl) ⟨301886, by rfl⟩ : syracuseStep 402515 = 603773) B603773
theorem B107623 : Blo 103782 107623 := bstep (se 1 (by rfl) ⟨80717, by rfl⟩ : syracuseStep 107623 = 161435) B161435
theorem B1025135 : Blo 103782 1025135 := bstep (se 1 (by rfl) ⟨768851, by rfl⟩ : syracuseStep 1025135 = 1537703) B1537703
theorem B107647 : Blo 103782 107647 := bstep (se 1 (by rfl) ⟨80735, by rfl⟩ : syracuseStep 107647 = 161471) B161471
theorem B107759 : Blo 103782 107759 := bstep (se 1 (by rfl) ⟨80819, by rfl⟩ : syracuseStep 107759 = 161639) B161639
theorem B3089771 : Blo 103782 3089771 := bstep (se 1 (by rfl) ⟨2317328, by rfl⟩ : syracuseStep 3089771 = 4634657) B4634657
theorem B239183 : Blo 103782 239183 := bstep (se 1 (by rfl) ⟨179387, by rfl⟩ : syracuseStep 239183 = 358775) B358775
theorem B239399 : Blo 103782 239399 := bstep (se 1 (by rfl) ⟨179549, by rfl⟩ : syracuseStep 239399 = 359099) B359099
theorem B862271 : Blo 103782 862271 := bstep (se 1 (by rfl) ⟨646703, by rfl⟩ : syracuseStep 862271 = 1293407) B1293407
theorem B175567 : Blo 103782 175567 := bstep (se 1 (by rfl) ⟨131675, by rfl⟩ : syracuseStep 175567 = 263351) B263351
theorem B241127 : Blo 103782 241127 := bstep (se 1 (by rfl) ⟨180845, by rfl⟩ : syracuseStep 241127 = 361691) B361691
theorem B503455 : Blo 103782 503455 := bstep (se 1 (by rfl) ⟨377591, by rfl⟩ : syracuseStep 503455 = 755183) B755183
theorem B241847 : Blo 103782 241847 := bstep (se 1 (by rfl) ⟨181385, by rfl⟩ : syracuseStep 241847 = 362771) B362771
theorem B242081 : Blo 103782 242081 := bstep (se 2 (by rfl) ⟨90780, by rfl⟩ : syracuseStep 242081 = 181561) B181561
theorem B505129 : Blo 103782 505129 := bstep (se 2 (by rfl) ⟨189423, by rfl⟩ : syracuseStep 505129 = 378847) B378847
theorem B1357307 : Blo 103782 1357307 := bstep (se 1 (by rfl) ⟨1017980, by rfl⟩ : syracuseStep 1357307 = 2035961) B2035961
theorem B899099 : Blo 103782 899099 := bstep (se 1 (by rfl) ⟨674324, by rfl⟩ : syracuseStep 899099 = 1348649) B1348649
theorem B407663 : Blo 103782 407663 := bstep (se 1 (by rfl) ⟨305747, by rfl⟩ : syracuseStep 407663 = 611495) B611495
theorem B113447 : Blo 103782 113447 := bstep (se 1 (by rfl) ⟨85085, by rfl⟩ : syracuseStep 113447 = 170171) B170171
theorem B605231 : Blo 103782 605231 := bstep (se 1 (by rfl) ⟨453923, by rfl⟩ : syracuseStep 605231 = 907847) B907847
theorem B539945 : Blo 103782 539945 := bstep (se 2 (by rfl) ⟨202479, by rfl⟩ : syracuseStep 539945 = 404959) B404959
theorem B802223 : Blo 103782 802223 := bstep (se 1 (by rfl) ⟨601667, by rfl⟩ : syracuseStep 802223 = 1203335) B1203335
theorem B605663 : Blo 103782 605663 := bstep (se 1 (by rfl) ⟨454247, by rfl⟩ : syracuseStep 605663 = 908495) B908495
theorem B7324445 : Blo 103782 7324445 := bstep (se 3 (by rfl) ⟨1373333, by rfl⟩ : syracuseStep 7324445 = 2746667) B2746667
theorem B214111 : Blo 103782 214111 := bstep (se 1 (by rfl) ⟨160583, by rfl⟩ : syracuseStep 214111 = 321167) B321167
theorem B542699 : Blo 103782 542699 := bstep (se 1 (by rfl) ⟨407024, by rfl⟩ : syracuseStep 542699 = 814049) B814049
theorem B248633 : Blo 103782 248633 := bstep (se 2 (by rfl) ⟨93237, by rfl⟩ : syracuseStep 248633 = 186475) B186475
theorem B445601 : Blo 103782 445601 := bstep (se 2 (by rfl) ⟨167100, by rfl⟩ : syracuseStep 445601 = 334201) B334201
theorem B511991 : Blo 103782 511991 := bstep (se 1 (by rfl) ⟨383993, by rfl⟩ : syracuseStep 511991 = 767987) B767987
theorem B447227 : Blo 103782 447227 := bstep (se 1 (by rfl) ⟨335420, by rfl⟩ : syracuseStep 447227 = 670841) B670841
theorem B119911 : Blo 103782 119911 := bstep (se 1 (by rfl) ⟨89933, by rfl⟩ : syracuseStep 119911 = 179867) B179867
theorem B611813 : Blo 103782 611813 := bstep (se 4 (by rfl) ⟨57357, by rfl⟩ : syracuseStep 611813 = 114715) B114715
theorem B1038203 : Blo 103782 1038203 := bstep (se 1 (by rfl) ⟨778652, by rfl⟩ : syracuseStep 1038203 = 1557305) B1557305
theorem B1103827 : Blo 103782 1103827 := bstep (se 1 (by rfl) ⟨827870, by rfl⟩ : syracuseStep 1103827 = 1655741) B1655741
theorem B350945 : Blo 103782 350945 := bstep (se 2 (by rfl) ⟨131604, by rfl⟩ : syracuseStep 350945 = 263209) B263209
theorem B450643 : Blo 103782 450643 := bstep (se 1 (by rfl) ⟨337982, by rfl⟩ : syracuseStep 450643 = 675965) B675965
theorem B385319 : Blo 103782 385319 := bstep (se 1 (by rfl) ⟨288989, by rfl⟩ : syracuseStep 385319 = 577979) B577979
theorem B975311 : Blo 103782 975311 := bstep (se 1 (by rfl) ⟨731483, by rfl⟩ : syracuseStep 975311 = 1462967) B1462967
theorem B3596831 : Blo 103782 3596831 := bstep (se 1 (by rfl) ⟨2697623, by rfl⟩ : syracuseStep 3596831 = 5395247) B5395247
theorem B156539 : Blo 103782 156539 := bstep (se 1 (by rfl) ⟨117404, by rfl⟩ : syracuseStep 156539 = 234809) B234809
theorem B353213 : Blo 103782 353213 := bstep (se 3 (by rfl) ⟨66227, by rfl⟩ : syracuseStep 353213 = 132455) B132455
theorem B156911 : Blo 103782 156911 := bstep (se 1 (by rfl) ⟨117683, by rfl⟩ : syracuseStep 156911 = 235367) B235367
theorem B157163 : Blo 103782 157163 := bstep (se 1 (by rfl) ⟨117872, by rfl⟩ : syracuseStep 157163 = 235745) B235745
theorem B157415 : Blo 103782 157415 := bstep (se 1 (by rfl) ⟨118061, by rfl⟩ : syracuseStep 157415 = 236123) B236123
theorem B256745 : Blo 103782 256745 := bstep (se 2 (by rfl) ⟨96279, by rfl⟩ : syracuseStep 256745 = 192559) B192559
theorem B158447 : Blo 103782 158447 := bstep (se 1 (by rfl) ⟨118835, by rfl⟩ : syracuseStep 158447 = 237671) B237671
theorem B355535 : Blo 103782 355535 := bstep (se 1 (by rfl) ⟨266651, by rfl⟩ : syracuseStep 355535 = 533303) B533303
theorem B159215 : Blo 103782 159215 := bstep (se 1 (by rfl) ⟨119411, by rfl⟩ : syracuseStep 159215 = 238823) B238823
theorem B159647 : Blo 103782 159647 := bstep (se 1 (by rfl) ⟨119735, by rfl⟩ : syracuseStep 159647 = 239471) B239471
theorem B160223 : Blo 103782 160223 := bstep (se 1 (by rfl) ⟨120167, by rfl⟩ : syracuseStep 160223 = 240335) B240335
theorem B160415 : Blo 103782 160415 := bstep (se 1 (by rfl) ⟨120311, by rfl⟩ : syracuseStep 160415 = 240623) B240623
theorem B161003 : Blo 103782 161003 := bstep (se 1 (by rfl) ⟨120752, by rfl⟩ : syracuseStep 161003 = 241505) B241505
theorem B2258405 : Blo 103782 2258405 := bstep (se 4 (by rfl) ⟨211725, by rfl⟩ : syracuseStep 2258405 = 423451) B423451
theorem B489167 : Blo 103782 489167 := bstep (se 1 (by rfl) ⟨366875, by rfl⟩ : syracuseStep 489167 = 733751) B733751
theorem B587711 : Blo 103782 587711 := bstep (se 1 (by rfl) ⟨440783, by rfl⟩ : syracuseStep 587711 = 881567) B881567
theorem B358397 : Blo 103782 358397 := bstep (se 3 (by rfl) ⟨67199, by rfl⟩ : syracuseStep 358397 = 134399) B134399
theorem B129151 : Blo 103782 129151 := bstep (se 1 (by rfl) ⟨96863, by rfl⟩ : syracuseStep 129151 = 193727) B193727
theorem B162119 : Blo 103782 162119 := bstep (se 1 (by rfl) ⟨121589, by rfl⟩ : syracuseStep 162119 = 243179) B243179
theorem B1014905 : Blo 103782 1014905 := bstep (se 2 (by rfl) ⟨380589, by rfl⟩ : syracuseStep 1014905 = 761179) B761179
theorem B163135 : Blo 103782 163135 := bstep (se 1 (by rfl) ⟨122351, by rfl⟩ : syracuseStep 163135 = 244703) B244703
theorem B4882963 : Blo 103782 4882963 := bstep (se 1 (by rfl) ⟨3662222, by rfl⟩ : syracuseStep 4882963 = 7324445) B7324445
theorem B132187 : Blo 103782 132187 := bstep (se 1 (by rfl) ⟨99140, by rfl⟩ : syracuseStep 132187 = 198281) B198281
theorem B4785419 : Blo 103782 4785419 := bstep (se 1 (by rfl) ⟨3589064, by rfl⟩ : syracuseStep 4785419 = 7178129) B7178129
theorem B361799 : Blo 103782 361799 := bstep (se 1 (by rfl) ⟨271349, by rfl⟩ : syracuseStep 361799 = 542699) B542699
theorem B165755 : Blo 103782 165755 := bstep (se 1 (by rfl) ⟨124316, by rfl⟩ : syracuseStep 165755 = 248633) B248633
theorem B2459965 : Blo 103782 2459965 := bstep (se 3 (by rfl) ⟨461243, by rfl⟩ : syracuseStep 2459965 = 922487) B922487
theorem B264647 : Blo 103782 264647 := bstep (se 1 (by rfl) ⟨198485, by rfl⟩ : syracuseStep 264647 = 396971) B396971
theorem B298151 : Blo 103782 298151 := bstep (se 1 (by rfl) ⟨223613, by rfl⟩ : syracuseStep 298151 = 447227) B447227
theorem B1969595 : Blo 103782 1969595 := bstep (se 1 (by rfl) ⟨1477196, by rfl⟩ : syracuseStep 1969595 = 2954393) B2954393
theorem B692135 : Blo 103782 692135 := bstep (se 1 (by rfl) ⟨519101, by rfl⟩ : syracuseStep 692135 = 1038203) B1038203
theorem B397487 : Blo 103782 397487 := bstep (se 1 (by rfl) ⟨298115, by rfl⟩ : syracuseStep 397487 = 596231) B596231
theorem B790721 : Blo 103782 790721 := bstep (se 2 (by rfl) ⟨296520, by rfl⟩ : syracuseStep 790721 = 593041) B593041
theorem B233963 : Blo 103782 233963 := bstep (se 1 (by rfl) ⟨175472, by rfl⟩ : syracuseStep 233963 = 350945) B350945
theorem B234089 : Blo 103782 234089 := bstep (se 2 (by rfl) ⟨87783, by rfl⟩ : syracuseStep 234089 = 175567) B175567
theorem B2397887 : Blo 103782 2397887 := bstep (se 1 (by rfl) ⟨1798415, by rfl⟩ : syracuseStep 2397887 = 3596831) B3596831
theorem B104359 : Blo 103782 104359 := bstep (se 1 (by rfl) ⟨78269, by rfl⟩ : syracuseStep 104359 = 156539) B156539
theorem B235475 : Blo 103782 235475 := bstep (se 1 (by rfl) ⟨176606, by rfl⟩ : syracuseStep 235475 = 353213) B353213
theorem B268343 : Blo 103782 268343 := bstep (se 1 (by rfl) ⟨201257, by rfl⟩ : syracuseStep 268343 = 402515) B402515
theorem B104607 : Blo 103782 104607 := bstep (se 1 (by rfl) ⟨78455, by rfl⟩ : syracuseStep 104607 = 156911) B156911
theorem B1054889 : Blo 103782 1054889 := bstep (se 2 (by rfl) ⟨395583, by rfl⟩ : syracuseStep 1054889 = 791167) B791167
theorem B432317 : Blo 103782 432317 := bstep (se 3 (by rfl) ⟨81059, by rfl⟩ : syracuseStep 432317 = 162119) B162119
theorem B104775 : Blo 103782 104775 := bstep (se 1 (by rfl) ⟨78581, by rfl⟩ : syracuseStep 104775 = 157163) B157163
theorem B104943 : Blo 103782 104943 := bstep (se 1 (by rfl) ⟨78707, by rfl⟩ : syracuseStep 104943 = 157415) B157415
theorem B171163 : Blo 103782 171163 := bstep (se 1 (by rfl) ⟨128372, by rfl⟩ : syracuseStep 171163 = 256745) B256745
theorem B105631 : Blo 103782 105631 := bstep (se 1 (by rfl) ⟨79223, by rfl⟩ : syracuseStep 105631 = 158447) B158447
theorem B302525 : Blo 103782 302525 := bstep (se 3 (by rfl) ⟨56723, by rfl⟩ : syracuseStep 302525 = 113447) B113447
theorem B237023 : Blo 103782 237023 := bstep (se 1 (by rfl) ⟨177767, by rfl⟩ : syracuseStep 237023 = 355535) B355535
theorem B106143 : Blo 103782 106143 := bstep (se 1 (by rfl) ⟨79607, by rfl⟩ : syracuseStep 106143 = 159215) B159215
theorem B565157 : Blo 103782 565157 := bstep (se 4 (by rfl) ⟨52983, by rfl⟩ : syracuseStep 565157 = 105967) B105967
theorem B106431 : Blo 103782 106431 := bstep (se 1 (by rfl) ⟨79823, by rfl⟩ : syracuseStep 106431 = 159647) B159647
theorem B172201 : Blo 103782 172201 := bstep (se 2 (by rfl) ⟨64575, by rfl⟩ : syracuseStep 172201 = 129151) B129151
theorem B106815 : Blo 103782 106815 := bstep (se 1 (by rfl) ⟨80111, by rfl⟩ : syracuseStep 106815 = 160223) B160223
theorem B1188269 : Blo 103782 1188269 := bstep (se 3 (by rfl) ⟨222800, by rfl⟩ : syracuseStep 1188269 = 445601) B445601
theorem B106943 : Blo 103782 106943 := bstep (se 1 (by rfl) ⟨80207, by rfl⟩ : syracuseStep 106943 = 160415) B160415
theorem B107335 : Blo 103782 107335 := bstep (se 1 (by rfl) ⟨80501, by rfl⟩ : syracuseStep 107335 = 161003) B161003
theorem B238931 : Blo 103782 238931 := bstep (se 1 (by rfl) ⟨179198, by rfl⟩ : syracuseStep 238931 = 358397) B358397
theorem B599399 : Blo 103782 599399 := bstep (se 1 (by rfl) ⟨449549, by rfl⟩ : syracuseStep 599399 = 899099) B899099
theorem B271775 : Blo 103782 271775 := bstep (se 1 (by rfl) ⟨203831, by rfl⟩ : syracuseStep 271775 = 407663) B407663
theorem B403487 : Blo 103782 403487 := bstep (se 1 (by rfl) ⟨302615, by rfl⟩ : syracuseStep 403487 = 605231) B605231
theorem B534815 : Blo 103782 534815 := bstep (se 1 (by rfl) ⟨401111, by rfl⟩ : syracuseStep 534815 = 802223) B802223
theorem B403775 : Blo 103782 403775 := bstep (se 1 (by rfl) ⟨302831, by rfl⟩ : syracuseStep 403775 = 605663) B605663
theorem B600857 : Blo 103782 600857 := bstep (se 2 (by rfl) ⟨225321, by rfl⟩ : syracuseStep 600857 = 450643) B450643
theorem B240731 : Blo 103782 240731 := bstep (se 1 (by rfl) ⟨180548, by rfl⟩ : syracuseStep 240731 = 361097) B361097
theorem B44478659 : Blo 103782 44478659 := bstep (se 1 (by rfl) ⟨33358994, by rfl⟩ : syracuseStep 44478659 = 66717989) B66717989
theorem B570023 : Blo 103782 570023 := bstep (se 1 (by rfl) ⟨427517, by rfl⟩ : syracuseStep 570023 = 855035) B855035
theorem B341327 : Blo 103782 341327 := bstep (se 1 (by rfl) ⟨255995, by rfl⟩ : syracuseStep 341327 = 511991) B511991
theorem B407875 : Blo 103782 407875 := bstep (se 1 (by rfl) ⟨305906, by rfl⟩ : syracuseStep 407875 = 611813) B611813
theorem B671273 : Blo 103782 671273 := bstep (se 2 (by rfl) ⟨251727, by rfl⟩ : syracuseStep 671273 = 503455) B503455
theorem B541565 : Blo 103782 541565 := bstep (se 3 (by rfl) ⟨101543, by rfl⟩ : syracuseStep 541565 = 203087) B203087
theorem B574847 : Blo 103782 574847 := bstep (se 1 (by rfl) ⟨431135, by rfl⟩ : syracuseStep 574847 = 862271) B862271
theorem B673505 : Blo 103782 673505 := bstep (se 2 (by rfl) ⟨252564, by rfl⟩ : syracuseStep 673505 = 505129) B505129
theorem B1788965 : Blo 103782 1788965 := bstep (se 4 (by rfl) ⟨167715, by rfl⟩ : syracuseStep 1788965 = 335431) B335431
theorem B904871 : Blo 103782 904871 := bstep (se 1 (by rfl) ⟨678653, by rfl⟩ : syracuseStep 904871 = 1357307) B1357307
theorem B217513 : Blo 103782 217513 := bstep (se 2 (by rfl) ⟨81567, by rfl⟩ : syracuseStep 217513 = 163135) B163135
theorem B676603 : Blo 103782 676603 := bstep (se 1 (by rfl) ⟨507452, by rfl⟩ : syracuseStep 676603 = 1014905) B1014905
theorem B743275 : Blo 103782 743275 := bstep (se 1 (by rfl) ⟨557456, by rfl⟩ : syracuseStep 743275 = 1114913) B1114913
theorem B285481 : Blo 103782 285481 := bstep (se 2 (by rfl) ⟨107055, by rfl⟩ : syracuseStep 285481 = 214111) B214111
theorem B155675 : Blo 103782 155675 := bstep (se 1 (by rfl) ⟨116756, by rfl⟩ : syracuseStep 155675 = 233513) B233513
theorem B155951 : Blo 103782 155951 := bstep (se 1 (by rfl) ⟨116963, by rfl⟩ : syracuseStep 155951 = 233927) B233927
theorem B156143 : Blo 103782 156143 := bstep (se 1 (by rfl) ⟨117107, by rfl⟩ : syracuseStep 156143 = 234215) B234215
theorem B2777723 : Blo 103782 2777723 := bstep (se 1 (by rfl) ⟨2083292, by rfl⟩ : syracuseStep 2777723 = 4166585) B4166585
theorem B156767 : Blo 103782 156767 := bstep (se 1 (by rfl) ⟨117575, by rfl⟩ : syracuseStep 156767 = 235151) B235151
theorem B157343 : Blo 103782 157343 := bstep (se 1 (by rfl) ⟨118007, by rfl⟩ : syracuseStep 157343 = 236015) B236015
theorem B3041023 : Blo 103782 3041023 := bstep (se 1 (by rfl) ⟨2280767, by rfl⟩ : syracuseStep 3041023 = 4561535) B4561535
theorem B157799 : Blo 103782 157799 := bstep (se 1 (by rfl) ⟨118349, by rfl⟩ : syracuseStep 157799 = 236699) B236699
theorem B157979 : Blo 103782 157979 := bstep (se 1 (by rfl) ⟨118484, by rfl⟩ : syracuseStep 157979 = 236969) B236969
theorem B256879 : Blo 103782 256879 := bstep (se 1 (by rfl) ⟨192659, by rfl⟩ : syracuseStep 256879 = 385319) B385319
theorem B650207 : Blo 103782 650207 := bstep (se 1 (by rfl) ⟨487655, by rfl⟩ : syracuseStep 650207 = 975311) B975311
theorem B158747 : Blo 103782 158747 := bstep (se 1 (by rfl) ⟨119060, by rfl⟩ : syracuseStep 158747 = 238121) B238121
theorem B683063 : Blo 103782 683063 := bstep (se 1 (by rfl) ⟨512297, by rfl⟩ : syracuseStep 683063 = 1024595) B1024595
theorem B1010987 : Blo 103782 1010987 := bstep (se 1 (by rfl) ⟨758240, by rfl⟩ : syracuseStep 1010987 = 1516481) B1516481
theorem B683423 : Blo 103782 683423 := bstep (se 1 (by rfl) ⟨512567, by rfl⟩ : syracuseStep 683423 = 1025135) B1025135
theorem B2059847 : Blo 103782 2059847 := bstep (se 1 (by rfl) ⟨1544885, by rfl⟩ : syracuseStep 2059847 = 3089771) B3089771
theorem B1797713 : Blo 103782 1797713 := bstep (se 2 (by rfl) ⟨674142, by rfl⟩ : syracuseStep 1797713 = 1348285) B1348285
theorem B159455 : Blo 103782 159455 := bstep (se 1 (by rfl) ⟨119591, by rfl⟩ : syracuseStep 159455 = 239183) B239183
theorem B159599 : Blo 103782 159599 := bstep (se 1 (by rfl) ⟨119699, by rfl⟩ : syracuseStep 159599 = 239399) B239399
theorem B159881 : Blo 103782 159881 := bstep (se 2 (by rfl) ⟨59955, by rfl⟩ : syracuseStep 159881 = 119911) B119911
theorem B160751 : Blo 103782 160751 := bstep (se 1 (by rfl) ⟨120563, by rfl⟩ : syracuseStep 160751 = 241127) B241127
theorem B2323673 : Blo 103782 2323673 := bstep (se 2 (by rfl) ⟨871377, by rfl⟩ : syracuseStep 2323673 = 1742755) B1742755
theorem B1471769 : Blo 103782 1471769 := bstep (se 2 (by rfl) ⟨551913, by rfl⟩ : syracuseStep 1471769 = 1103827) B1103827
theorem B161231 : Blo 103782 161231 := bstep (se 1 (by rfl) ⟨120923, by rfl⟩ : syracuseStep 161231 = 241847) B241847
theorem B161387 : Blo 103782 161387 := bstep (se 1 (by rfl) ⟨121040, by rfl⟩ : syracuseStep 161387 = 242081) B242081
theorem B1505603 : Blo 103782 1505603 := bstep (se 1 (by rfl) ⟨1129202, by rfl⟩ : syracuseStep 1505603 = 2258405) B2258405
theorem B326111 : Blo 103782 326111 := bstep (se 1 (by rfl) ⟨244583, by rfl⟩ : syracuseStep 326111 = 489167) B489167
theorem B391807 : Blo 103782 391807 := bstep (se 1 (by rfl) ⟨293855, by rfl⟩ : syracuseStep 391807 = 587711) B587711
theorem B359963 : Blo 103782 359963 := bstep (se 1 (by rfl) ⟨269972, by rfl⟩ : syracuseStep 359963 = 539945) B539945
theorem B229601 : Blo 103782 229601 := bstep (se 2 (by rfl) ⟨86100, by rfl⟩ : syracuseStep 229601 = 172201) B172201
theorem B361043 : Blo 103782 361043 := bstep (se 1 (by rfl) ⟨270782, by rfl⟩ : syracuseStep 361043 = 541565) B541565
theorem B198767 : Blo 103782 198767 := bstep (se 1 (by rfl) ⟨149075, by rfl⟩ : syracuseStep 198767 = 298151) B298151
theorem B1313063 : Blo 103782 1313063 := bstep (se 1 (by rfl) ⟨984797, by rfl⟩ : syracuseStep 1313063 = 1969595) B1969595
theorem B461423 : Blo 103782 461423 := bstep (se 1 (by rfl) ⟨346067, by rfl⟩ : syracuseStep 461423 = 692135) B692135
theorem B264991 : Blo 103782 264991 := bstep (se 1 (by rfl) ⟨198743, by rfl⟩ : syracuseStep 264991 = 397487) B397487
theorem B527147 : Blo 103782 527147 := bstep (se 1 (by rfl) ⟨395360, by rfl⟩ : syracuseStep 527147 = 790721) B790721
theorem B3279953 : Blo 103782 3279953 := bstep (se 2 (by rfl) ⟨1229982, by rfl⟩ : syracuseStep 3279953 = 2459965) B2459965
theorem B201683 : Blo 103782 201683 := bstep (se 1 (by rfl) ⟨151262, by rfl⟩ : syracuseStep 201683 = 302525) B302525
theorem B103783 : Blo 103782 103783 := bstep (se 1 (by rfl) ⟨77837, by rfl⟩ : syracuseStep 103783 = 155675) B155675
theorem B103967 : Blo 103782 103967 := bstep (se 1 (by rfl) ⟨77975, by rfl⟩ : syracuseStep 103967 = 155951) B155951
theorem B792179 : Blo 103782 792179 := bstep (se 1 (by rfl) ⟨594134, by rfl⟩ : syracuseStep 792179 = 1188269) B1188269
theorem B104095 : Blo 103782 104095 := bstep (se 1 (by rfl) ⟨78071, by rfl⟩ : syracuseStep 104095 = 156143) B156143
theorem B104511 : Blo 103782 104511 := bstep (se 1 (by rfl) ⟨78383, by rfl⟩ : syracuseStep 104511 = 156767) B156767
theorem B399599 : Blo 103782 399599 := bstep (se 1 (by rfl) ⟨299699, by rfl⟩ : syracuseStep 399599 = 599399) B599399
theorem B104895 : Blo 103782 104895 := bstep (se 1 (by rfl) ⟨78671, by rfl⟩ : syracuseStep 104895 = 157343) B157343
theorem B268991 : Blo 103782 268991 := bstep (se 1 (by rfl) ⟨201743, by rfl⟩ : syracuseStep 268991 = 403487) B403487
theorem B105199 : Blo 103782 105199 := bstep (se 1 (by rfl) ⟨78899, by rfl⟩ : syracuseStep 105199 = 157799) B157799
theorem B105319 : Blo 103782 105319 := bstep (se 1 (by rfl) ⟨78989, by rfl⟩ : syracuseStep 105319 = 157979) B157979
theorem B269183 : Blo 103782 269183 := bstep (se 1 (by rfl) ⟨201887, by rfl⟩ : syracuseStep 269183 = 403775) B403775
theorem B400571 : Blo 103782 400571 := bstep (se 1 (by rfl) ⟨300428, by rfl⟩ : syracuseStep 400571 = 600857) B600857
theorem B433471 : Blo 103782 433471 := bstep (se 1 (by rfl) ⟨325103, by rfl⟩ : syracuseStep 433471 = 650207) B650207
theorem B105831 : Blo 103782 105831 := bstep (se 1 (by rfl) ⟨79373, by rfl⟩ : syracuseStep 105831 = 158747) B158747
theorem B991033 : Blo 103782 991033 := bstep (se 2 (by rfl) ⟨371637, by rfl⟩ : syracuseStep 991033 = 743275) B743275
theorem B106303 : Blo 103782 106303 := bstep (se 1 (by rfl) ⟨79727, by rfl⟩ : syracuseStep 106303 = 159455) B159455
theorem B106399 : Blo 103782 106399 := bstep (se 1 (by rfl) ⟨79799, by rfl⟩ : syracuseStep 106399 = 159599) B159599
theorem B106587 : Blo 103782 106587 := bstep (se 1 (by rfl) ⟨79940, by rfl⟩ : syracuseStep 106587 = 159881) B159881
theorem B107167 : Blo 103782 107167 := bstep (se 1 (by rfl) ⟨80375, by rfl⟩ : syracuseStep 107167 = 160751) B160751
theorem B1549115 : Blo 103782 1549115 := bstep (se 1 (by rfl) ⟨1161836, by rfl⟩ : syracuseStep 1549115 = 2323673) B2323673
theorem B107487 : Blo 103782 107487 := bstep (se 1 (by rfl) ⟨80615, by rfl⟩ : syracuseStep 107487 = 161231) B161231
theorem B107591 : Blo 103782 107591 := bstep (se 1 (by rfl) ⟨80693, by rfl⟩ : syracuseStep 107591 = 161387) B161387
theorem B239975 : Blo 103782 239975 := bstep (se 1 (by rfl) ⟨179981, by rfl⟩ : syracuseStep 239975 = 359963) B359963
theorem B3190279 : Blo 103782 3190279 := bstep (se 1 (by rfl) ⟨2392709, by rfl⟩ : syracuseStep 3190279 = 4785419) B4785419
theorem B241199 : Blo 103782 241199 := bstep (se 1 (by rfl) ⟨180899, by rfl⟩ : syracuseStep 241199 = 361799) B361799
theorem B176249 : Blo 103782 176249 := bstep (se 2 (by rfl) ⟨66093, by rfl⟩ : syracuseStep 176249 = 132187) B132187
theorem B176431 : Blo 103782 176431 := bstep (se 1 (by rfl) ⟨132323, by rfl⟩ : syracuseStep 176431 = 264647) B264647
theorem B1192643 : Blo 103782 1192643 := bstep (se 1 (by rfl) ⟨894482, by rfl⟩ : syracuseStep 1192643 = 1788965) B1788965
theorem B603247 : Blo 103782 603247 := bstep (se 1 (by rfl) ⟨452435, by rfl⟩ : syracuseStep 603247 = 904871) B904871
theorem B342505 : Blo 103782 342505 := bstep (se 2 (by rfl) ⟨128439, by rfl⟩ : syracuseStep 342505 = 256879) B256879
theorem B178895 : Blo 103782 178895 := bstep (se 1 (by rfl) ⟨134171, by rfl⟩ : syracuseStep 178895 = 268343) B268343
theorem B703259 : Blo 103782 703259 := bstep (se 1 (by rfl) ⟨527444, by rfl⟩ : syracuseStep 703259 = 1054889) B1054889
theorem B442013 : Blo 103782 442013 := bstep (se 3 (by rfl) ⟨82877, by rfl⟩ : syracuseStep 442013 = 165755) B165755
theorem B1851815 : Blo 103782 1851815 := bstep (se 1 (by rfl) ⟨1388861, by rfl⟩ : syracuseStep 1851815 = 2777723) B2777723
theorem B181183 : Blo 103782 181183 := bstep (se 1 (by rfl) ⟨135887, by rfl⟩ : syracuseStep 181183 = 271775) B271775
theorem B902137 : Blo 103782 902137 := bstep (se 2 (by rfl) ⟨338301, by rfl⟩ : syracuseStep 902137 = 676603) B676603
theorem B869629 : Blo 103782 869629 := bstep (se 3 (by rfl) ⟨163055, by rfl⟩ : syracuseStep 869629 = 326111) B326111
theorem B673991 : Blo 103782 673991 := bstep (se 1 (by rfl) ⟨505493, by rfl⟩ : syracuseStep 673991 = 1010987) B1010987
theorem B1198475 : Blo 103782 1198475 := bstep (se 1 (by rfl) ⟨898856, by rfl⟩ : syracuseStep 1198475 = 1797713) B1797713
theorem B543833 : Blo 103782 543833 := bstep (se 2 (by rfl) ⟨203937, by rfl⟩ : syracuseStep 543833 = 407875) B407875
theorem B380015 : Blo 103782 380015 := bstep (se 1 (by rfl) ⟨285011, by rfl⟩ : syracuseStep 380015 = 570023) B570023
theorem B380641 : Blo 103782 380641 := bstep (se 2 (by rfl) ⟨142740, by rfl⟩ : syracuseStep 380641 = 285481) B285481
theorem B1003735 : Blo 103782 1003735 := bstep (se 1 (by rfl) ⟨752801, by rfl⟩ : syracuseStep 1003735 = 1505603) B1505603
theorem B447515 : Blo 103782 447515 := bstep (se 1 (by rfl) ⟨335636, by rfl⟩ : syracuseStep 447515 = 671273) B671273
theorem B6510617 : Blo 103782 6510617 := bstep (se 2 (by rfl) ⟨2441481, by rfl⟩ : syracuseStep 6510617 = 4882963) B4882963
theorem B383231 : Blo 103782 383231 := bstep (se 1 (by rfl) ⟨287423, by rfl⟩ : syracuseStep 383231 = 574847) B574847
theorem B449003 : Blo 103782 449003 := bstep (se 1 (by rfl) ⟨336752, by rfl⟩ : syracuseStep 449003 = 673505) B673505
theorem B4054697 : Blo 103782 4054697 := bstep (se 2 (by rfl) ⟨1520511, by rfl⟩ : syracuseStep 4054697 = 3041023) B3041023
theorem B155975 : Blo 103782 155975 := bstep (se 1 (by rfl) ⟨116981, by rfl⟩ : syracuseStep 155975 = 233963) B233963
theorem B156059 : Blo 103782 156059 := bstep (se 1 (by rfl) ⟨117044, by rfl⟩ : syracuseStep 156059 = 234089) B234089
theorem B1598591 : Blo 103782 1598591 := bstep (se 1 (by rfl) ⟨1198943, by rfl⟩ : syracuseStep 1598591 = 2397887) B2397887
theorem B156983 : Blo 103782 156983 := bstep (se 1 (by rfl) ⟨117737, by rfl⟩ : syracuseStep 156983 = 235475) B235475
theorem B288211 : Blo 103782 288211 := bstep (se 1 (by rfl) ⟨216158, by rfl⟩ : syracuseStep 288211 = 432317) B432317
theorem B158015 : Blo 103782 158015 := bstep (se 1 (by rfl) ⟨118511, by rfl⟩ : syracuseStep 158015 = 237023) B237023
theorem B290017 : Blo 103782 290017 := bstep (se 2 (by rfl) ⟨108756, by rfl⟩ : syracuseStep 290017 = 217513) B217513
theorem B912869 : Blo 103782 912869 := bstep (se 4 (by rfl) ⟨85581, by rfl⟩ : syracuseStep 912869 = 171163) B171163
theorem B159287 : Blo 103782 159287 := bstep (se 1 (by rfl) ⟨119465, by rfl⟩ : syracuseStep 159287 = 238931) B238931
theorem B356543 : Blo 103782 356543 := bstep (se 1 (by rfl) ⟨267407, by rfl⟩ : syracuseStep 356543 = 534815) B534815
theorem B455375 : Blo 103782 455375 := bstep (se 1 (by rfl) ⟨341531, by rfl⟩ : syracuseStep 455375 = 683063) B683063
theorem B160487 : Blo 103782 160487 := bstep (se 1 (by rfl) ⟨120365, by rfl⟩ : syracuseStep 160487 = 240731) B240731
theorem B455615 : Blo 103782 455615 := bstep (se 1 (by rfl) ⟨341711, by rfl⟩ : syracuseStep 455615 = 683423) B683423
theorem B1373231 : Blo 103782 1373231 := bstep (se 1 (by rfl) ⟨1029923, by rfl⟩ : syracuseStep 1373231 = 2059847) B2059847
theorem B29652439 : Blo 103782 29652439 := bstep (se 1 (by rfl) ⟨22239329, by rfl⟩ : syracuseStep 29652439 = 44478659) B44478659
theorem B522409 : Blo 103782 522409 := bstep (se 2 (by rfl) ⟨195903, by rfl⟩ : syracuseStep 522409 = 391807) B391807
theorem B981179 : Blo 103782 981179 := bstep (se 1 (by rfl) ⟨735884, by rfl⟩ : syracuseStep 981179 = 1471769) B1471769
theorem B227551 : Blo 103782 227551 := bstep (se 1 (by rfl) ⟨170663, by rfl⟩ : syracuseStep 227551 = 341327) B341327
theorem B1507085 : Blo 103782 1507085 := bstep (se 3 (by rfl) ⟨282578, by rfl⟩ : syracuseStep 1507085 = 565157) B565157
theorem B132511 : Blo 103782 132511 := bstep (se 1 (by rfl) ⟨99383, by rfl⟩ : syracuseStep 132511 = 198767) B198767
theorem B3803125 : Blo 103782 3803125 := bstep (se 5 (by rfl) ⟨178271, by rfl⟩ : syracuseStep 3803125 = 356543) B356543
theorem B362555 : Blo 103782 362555 := bstep (se 1 (by rfl) ⟨271916, by rfl⟩ : syracuseStep 362555 = 543833) B543833
theorem B134455 : Blo 103782 134455 := bstep (se 1 (by rfl) ⟨100841, by rfl⟩ : syracuseStep 134455 = 201683) B201683
theorem B298343 : Blo 103782 298343 := bstep (se 1 (by rfl) ⟨223757, by rfl⟩ : syracuseStep 298343 = 447515) B447515
theorem B528119 : Blo 103782 528119 := bstep (se 1 (by rfl) ⟨396089, by rfl⟩ : syracuseStep 528119 = 792179) B792179
theorem B266399 : Blo 103782 266399 := bstep (se 1 (by rfl) ⟨199799, by rfl⟩ : syracuseStep 266399 = 399599) B399599
theorem B299335 : Blo 103782 299335 := bstep (se 1 (by rfl) ⟨224501, by rfl⟩ : syracuseStep 299335 = 449003) B449003
theorem B267047 : Blo 103782 267047 := bstep (se 1 (by rfl) ⟨200285, by rfl⟩ : syracuseStep 267047 = 400571) B400571
theorem B103983 : Blo 103782 103983 := bstep (se 1 (by rfl) ⟨77987, by rfl⟩ : syracuseStep 103983 = 155975) B155975
theorem B104039 : Blo 103782 104039 := bstep (se 1 (by rfl) ⟨78029, by rfl⟩ : syracuseStep 104039 = 156059) B156059
theorem B235241 : Blo 103782 235241 := bstep (se 2 (by rfl) ⟨88215, by rfl⟩ : syracuseStep 235241 = 176431) B176431
theorem B104655 : Blo 103782 104655 := bstep (se 1 (by rfl) ⟨78491, by rfl⟩ : syracuseStep 104655 = 156983) B156983
theorem B21142037 : Blo 103782 21142037 := bstep (se 6 (by rfl) ⟨495516, by rfl⟩ : syracuseStep 21142037 = 991033) B991033
theorem B105343 : Blo 103782 105343 := bstep (se 1 (by rfl) ⟨79007, by rfl⟩ : syracuseStep 105343 = 158015) B158015
theorem B106191 : Blo 103782 106191 := bstep (se 1 (by rfl) ⟨79643, by rfl⟩ : syracuseStep 106191 = 159287) B159287
theorem B696545 : Blo 103782 696545 := bstep (se 2 (by rfl) ⟨261204, by rfl⟩ : syracuseStep 696545 = 522409) B522409
theorem B303401 : Blo 103782 303401 := bstep (se 2 (by rfl) ⟨113775, by rfl⟩ : syracuseStep 303401 = 227551) B227551
theorem B795095 : Blo 103782 795095 := bstep (se 1 (by rfl) ⟨596321, by rfl⟩ : syracuseStep 795095 = 1192643) B1192643
theorem B303583 : Blo 103782 303583 := bstep (se 1 (by rfl) ⟨227687, by rfl⟩ : syracuseStep 303583 = 455375) B455375
theorem B106991 : Blo 103782 106991 := bstep (se 1 (by rfl) ⟨80243, by rfl⟩ : syracuseStep 106991 = 160487) B160487
theorem B303743 : Blo 103782 303743 := bstep (se 1 (by rfl) ⟨227807, by rfl⟩ : syracuseStep 303743 = 455615) B455615
theorem B468839 : Blo 103782 468839 := bstep (se 1 (by rfl) ⟨351629, by rfl⟩ : syracuseStep 468839 = 703259) B703259
theorem B240695 : Blo 103782 240695 := bstep (se 1 (by rfl) ⟨180521, by rfl⟩ : syracuseStep 240695 = 361043) B361043
theorem B5353253 : Blo 103782 5353253 := bstep (se 4 (by rfl) ⟨501867, by rfl⟩ : syracuseStep 5353253 = 1003735) B1003735
theorem B241577 : Blo 103782 241577 := bstep (se 2 (by rfl) ⟨90591, by rfl⟩ : syracuseStep 241577 = 181183) B181183
theorem B798983 : Blo 103782 798983 := bstep (se 1 (by rfl) ⟨599237, by rfl⟩ : syracuseStep 798983 = 1198475) B1198475
theorem B1159505 : Blo 103782 1159505 := bstep (se 2 (by rfl) ⟨434814, by rfl⟩ : syracuseStep 1159505 = 869629) B869629
theorem B4340411 : Blo 103782 4340411 := bstep (se 1 (by rfl) ⟨3255308, by rfl⟩ : syracuseStep 4340411 = 6510617) B6510617
theorem B179327 : Blo 103782 179327 := bstep (se 1 (by rfl) ⟨134495, by rfl⟩ : syracuseStep 179327 = 268991) B268991
theorem B179455 : Blo 103782 179455 := bstep (se 1 (by rfl) ⟨134591, by rfl⟩ : syracuseStep 179455 = 269183) B269183
theorem B507521 : Blo 103782 507521 := bstep (se 2 (by rfl) ⟨190320, by rfl⟩ : syracuseStep 507521 = 380641) B380641
theorem B2703131 : Blo 103782 2703131 := bstep (se 1 (by rfl) ⟨2027348, by rfl⟩ : syracuseStep 2703131 = 4054697) B4054697
theorem B1032743 : Blo 103782 1032743 := bstep (se 1 (by rfl) ⟨774557, by rfl⟩ : syracuseStep 1032743 = 1549115) B1549115
theorem B1065727 : Blo 103782 1065727 := bstep (se 1 (by rfl) ⟨799295, by rfl⟩ : syracuseStep 1065727 = 1598591) B1598591
theorem B804329 : Blo 103782 804329 := bstep (se 2 (by rfl) ⟨301623, by rfl⟩ : syracuseStep 804329 = 603247) B603247
theorem B1230461 : Blo 103782 1230461 := bstep (se 3 (by rfl) ⟨230711, by rfl⟩ : syracuseStep 1230461 = 461423) B461423
theorem B39536585 : Blo 103782 39536585 := bstep (se 2 (by rfl) ⟨14826219, by rfl⟩ : syracuseStep 39536585 = 29652439) B29652439
theorem B608579 : Blo 103782 608579 := bstep (se 1 (by rfl) ⟨456434, by rfl⟩ : syracuseStep 608579 = 912869) B912869
theorem B117499 : Blo 103782 117499 := bstep (se 1 (by rfl) ⟨88124, by rfl⟩ : syracuseStep 117499 = 176249) B176249
theorem B577961 : Blo 103782 577961 := bstep (se 2 (by rfl) ⟨216735, by rfl⟩ : syracuseStep 577961 = 433471) B433471
theorem B119263 : Blo 103782 119263 := bstep (se 1 (by rfl) ⟨89447, by rfl⟩ : syracuseStep 119263 = 178895) B178895
theorem B1004723 : Blo 103782 1004723 := bstep (se 1 (by rfl) ⟨753542, by rfl⟩ : syracuseStep 1004723 = 1507085) B1507085
theorem B1234543 : Blo 103782 1234543 := bstep (se 1 (by rfl) ⟨925907, by rfl⟩ : syracuseStep 1234543 = 1851815) B1851815
theorem B612269 : Blo 103782 612269 := bstep (se 3 (by rfl) ⟨114800, by rfl⟩ : syracuseStep 612269 = 229601) B229601
theorem B1202849 : Blo 103782 1202849 := bstep (se 2 (by rfl) ⟨451068, by rfl⟩ : syracuseStep 1202849 = 902137) B902137
theorem B449327 : Blo 103782 449327 := bstep (se 1 (by rfl) ⟨336995, by rfl⟩ : syracuseStep 449327 = 673991) B673991
theorem B875375 : Blo 103782 875375 := bstep (se 1 (by rfl) ⟨656531, by rfl⟩ : syracuseStep 875375 = 1313063) B1313063
theorem B351431 : Blo 103782 351431 := bstep (se 1 (by rfl) ⟨263573, by rfl⟩ : syracuseStep 351431 = 527147) B527147
theorem B384281 : Blo 103782 384281 := bstep (se 2 (by rfl) ⟨144105, by rfl⟩ : syracuseStep 384281 = 288211) B288211
theorem B2186635 : Blo 103782 2186635 := bstep (se 1 (by rfl) ⟨1639976, by rfl⟩ : syracuseStep 2186635 = 3279953) B3279953
theorem B253343 : Blo 103782 253343 := bstep (se 1 (by rfl) ⟨190007, by rfl⟩ : syracuseStep 253343 = 380015) B380015
theorem B3661949 : Blo 103782 3661949 := bstep (se 3 (by rfl) ⟨686615, by rfl⟩ : syracuseStep 3661949 = 1373231) B1373231
theorem B353321 : Blo 103782 353321 := bstep (se 2 (by rfl) ⟨132495, by rfl⟩ : syracuseStep 353321 = 264991) B264991
theorem B255487 : Blo 103782 255487 := bstep (se 1 (by rfl) ⟨191615, by rfl⟩ : syracuseStep 255487 = 383231) B383231
theorem B386689 : Blo 103782 386689 := bstep (se 2 (by rfl) ⟨145008, by rfl⟩ : syracuseStep 386689 = 290017) B290017
theorem B4253705 : Blo 103782 4253705 := bstep (se 2 (by rfl) ⟨1595139, by rfl⟩ : syracuseStep 4253705 = 3190279) B3190279
theorem B159983 : Blo 103782 159983 := bstep (se 1 (by rfl) ⟨119987, by rfl⟩ : syracuseStep 159983 = 239975) B239975
theorem B4714805 : Blo 103782 4714805 := bstep (se 5 (by rfl) ⟨221006, by rfl⟩ : syracuseStep 4714805 = 442013) B442013
theorem B160799 : Blo 103782 160799 := bstep (se 1 (by rfl) ⟨120599, by rfl⟩ : syracuseStep 160799 = 241199) B241199
theorem B456673 : Blo 103782 456673 := bstep (se 2 (by rfl) ⟨171252, by rfl⟩ : syracuseStep 456673 = 342505) B342505
theorem B654119 : Blo 103782 654119 := bstep (se 1 (by rfl) ⟨490589, by rfl⟩ : syracuseStep 654119 = 981179) B981179
theorem B9765197 : Blo 103782 9765197 := bstep (se 3 (by rfl) ⟨1830974, by rfl⟩ : syracuseStep 9765197 = 3661949) B3661949
theorem B688495 : Blo 103782 688495 := bstep (se 1 (by rfl) ⟨516371, by rfl⟩ : syracuseStep 688495 = 1032743) B1032743
theorem B820307 : Blo 103782 820307 := bstep (se 1 (by rfl) ⟨615230, by rfl⟩ : syracuseStep 820307 = 1230461) B1230461
theorem B14094691 : Blo 103782 14094691 := bstep (se 1 (by rfl) ⟨10571018, by rfl⟩ : syracuseStep 14094691 = 21142037) B21142037
theorem B299551 : Blo 103782 299551 := bstep (se 1 (by rfl) ⟨224663, by rfl⟩ : syracuseStep 299551 = 449327) B449327
theorem B234287 : Blo 103782 234287 := bstep (se 1 (by rfl) ⟨175715, by rfl⟩ : syracuseStep 234287 = 351431) B351431
theorem B168895 : Blo 103782 168895 := bstep (se 1 (by rfl) ⟨126671, by rfl⟩ : syracuseStep 168895 = 253343) B253343
theorem B464363 : Blo 103782 464363 := bstep (se 1 (by rfl) ⟨348272, by rfl⟩ : syracuseStep 464363 = 696545) B696545
theorem B202267 : Blo 103782 202267 := bstep (se 1 (by rfl) ⟨151700, by rfl⟩ : syracuseStep 202267 = 303401) B303401
theorem B530063 : Blo 103782 530063 := bstep (se 1 (by rfl) ⟨397547, by rfl⟩ : syracuseStep 530063 = 795095) B795095
theorem B202495 : Blo 103782 202495 := bstep (se 1 (by rfl) ⟨151871, by rfl⟩ : syracuseStep 202495 = 303743) B303743
theorem B399113 : Blo 103782 399113 := bstep (se 2 (by rfl) ⟨149667, by rfl⟩ : syracuseStep 399113 = 299335) B299335
theorem B235547 : Blo 103782 235547 := bstep (se 1 (by rfl) ⟨176660, by rfl⟩ : syracuseStep 235547 = 353321) B353321
theorem B1646057 : Blo 103782 1646057 := bstep (se 2 (by rfl) ⟨617271, by rfl⟩ : syracuseStep 1646057 = 1234543) B1234543
theorem B106655 : Blo 103782 106655 := bstep (se 1 (by rfl) ⟨79991, by rfl⟩ : syracuseStep 106655 = 159983) B159983
theorem B532655 : Blo 103782 532655 := bstep (se 1 (by rfl) ⟨399491, by rfl⟩ : syracuseStep 532655 = 798983) B798983
theorem B107199 : Blo 103782 107199 := bstep (se 1 (by rfl) ⟨80399, by rfl⟩ : syracuseStep 107199 = 160799) B160799
theorem B795581 : Blo 103782 795581 := bstep (se 3 (by rfl) ⟨149171, by rfl⟩ : syracuseStep 795581 = 298343) B298343
theorem B239273 : Blo 103782 239273 := bstep (se 2 (by rfl) ⟨89727, by rfl⟩ : syracuseStep 239273 = 179455) B179455
theorem B2893607 : Blo 103782 2893607 := bstep (se 1 (by rfl) ⟨2170205, by rfl⟩ : syracuseStep 2893607 = 4340411) B4340411
theorem B436079 : Blo 103782 436079 := bstep (se 1 (by rfl) ⟨327059, by rfl⟩ : syracuseStep 436079 = 654119) B654119
theorem B338347 : Blo 103782 338347 := bstep (se 1 (by rfl) ⟨253760, by rfl⟩ : syracuseStep 338347 = 507521) B507521
theorem B404777 : Blo 103782 404777 := bstep (se 2 (by rfl) ⟨151791, by rfl⟩ : syracuseStep 404777 = 303583) B303583
theorem B536219 : Blo 103782 536219 := bstep (se 1 (by rfl) ⟨402164, by rfl⟩ : syracuseStep 536219 = 804329) B804329
theorem B26357723 : Blo 103782 26357723 := bstep (se 1 (by rfl) ⟨19768292, by rfl⟩ : syracuseStep 26357723 = 39536585) B39536585
theorem B241703 : Blo 103782 241703 := bstep (se 1 (by rfl) ⟨181277, by rfl⟩ : syracuseStep 241703 = 362555) B362555
theorem B405719 : Blo 103782 405719 := bstep (se 1 (by rfl) ⟨304289, by rfl⟩ : syracuseStep 405719 = 608579) B608579
theorem B176681 : Blo 103782 176681 := bstep (se 2 (by rfl) ⟨66255, by rfl⟩ : syracuseStep 176681 = 132511) B132511
theorem B340649 : Blo 103782 340649 := bstep (se 2 (by rfl) ⟨127743, by rfl⟩ : syracuseStep 340649 = 255487) B255487
theorem B177599 : Blo 103782 177599 := bstep (se 1 (by rfl) ⟨133199, by rfl⟩ : syracuseStep 177599 = 266399) B266399
theorem B178031 : Blo 103782 178031 := bstep (se 1 (by rfl) ⟨133523, by rfl⟩ : syracuseStep 178031 = 267047) B267047
theorem B669815 : Blo 103782 669815 := bstep (se 1 (by rfl) ⟨502361, by rfl⟩ : syracuseStep 669815 = 1004723) B1004723
theorem B408179 : Blo 103782 408179 := bstep (se 1 (by rfl) ⟨306134, by rfl⟩ : syracuseStep 408179 = 612269) B612269
theorem B5683877 : Blo 103782 5683877 := bstep (se 4 (by rfl) ⟨532863, by rfl⟩ : syracuseStep 5683877 = 1065727) B1065727
theorem B179273 : Blo 103782 179273 := bstep (se 2 (by rfl) ⟨67227, by rfl⟩ : syracuseStep 179273 = 134455) B134455
theorem B801899 : Blo 103782 801899 := bstep (se 1 (by rfl) ⟨601424, by rfl⟩ : syracuseStep 801899 = 1202849) B1202849
theorem B312559 : Blo 103782 312559 := bstep (se 1 (by rfl) ⟨234419, by rfl⟩ : syracuseStep 312559 = 468839) B468839
theorem B2835803 : Blo 103782 2835803 := bstep (se 1 (by rfl) ⟨2126852, by rfl⟩ : syracuseStep 2835803 = 4253705) B4253705
theorem B608897 : Blo 103782 608897 := bstep (se 2 (by rfl) ⟨228336, by rfl⟩ : syracuseStep 608897 = 456673) B456673
theorem B773003 : Blo 103782 773003 := bstep (se 1 (by rfl) ⟨579752, by rfl⟩ : syracuseStep 773003 = 1159505) B1159505
theorem B119551 : Blo 103782 119551 := bstep (se 1 (by rfl) ⟨89663, by rfl⟩ : syracuseStep 119551 = 179327) B179327
theorem B12572813 : Blo 103782 12572813 := bstep (se 3 (by rfl) ⟨2357402, by rfl⟩ : syracuseStep 12572813 = 4714805) B4714805
theorem B515585 : Blo 103782 515585 := bstep (se 2 (by rfl) ⟨193344, by rfl⟩ : syracuseStep 515585 = 386689) B386689
theorem B352079 : Blo 103782 352079 := bstep (se 1 (by rfl) ⟨264059, by rfl⟩ : syracuseStep 352079 = 528119) B528119
theorem B5070833 : Blo 103782 5070833 := bstep (se 2 (by rfl) ⟨1901562, by rfl⟩ : syracuseStep 5070833 = 3803125) B3803125
theorem B385307 : Blo 103782 385307 := bstep (se 1 (by rfl) ⟨288980, by rfl⟩ : syracuseStep 385307 = 577961) B577961
theorem B156665 : Blo 103782 156665 := bstep (se 2 (by rfl) ⟨58749, by rfl⟩ : syracuseStep 156665 = 117499) B117499
theorem B156827 : Blo 103782 156827 := bstep (se 1 (by rfl) ⟨117620, by rfl⟩ : syracuseStep 156827 = 235241) B235241
theorem B583583 : Blo 103782 583583 := bstep (se 1 (by rfl) ⟨437687, by rfl⟩ : syracuseStep 583583 = 875375) B875375
theorem B256187 : Blo 103782 256187 := bstep (se 1 (by rfl) ⟨192140, by rfl⟩ : syracuseStep 256187 = 384281) B384281
theorem B159017 : Blo 103782 159017 := bstep (se 2 (by rfl) ⟨59631, by rfl⟩ : syracuseStep 159017 = 119263) B119263
theorem B160463 : Blo 103782 160463 := bstep (se 1 (by rfl) ⟨120347, by rfl⟩ : syracuseStep 160463 = 240695) B240695
theorem B3568835 : Blo 103782 3568835 := bstep (se 1 (by rfl) ⟨2676626, by rfl⟩ : syracuseStep 3568835 = 5353253) B5353253
theorem B161051 : Blo 103782 161051 := bstep (se 1 (by rfl) ⟨120788, by rfl⟩ : syracuseStep 161051 = 241577) B241577
theorem B2915513 : Blo 103782 2915513 := bstep (se 2 (by rfl) ⟨1093317, by rfl⟩ : syracuseStep 2915513 = 2186635) B2186635
theorem B1802087 : Blo 103782 1802087 := bstep (se 1 (by rfl) ⟨1351565, by rfl⟩ : syracuseStep 1802087 = 2703131) B2703131
theorem B917993 : Blo 103782 917993 := bstep (se 2 (by rfl) ⟨344247, by rfl⟩ : syracuseStep 917993 = 688495) B688495
theorem B75171685 : Blo 103782 75171685 := bstep (se 4 (by rfl) ⟨7047345, by rfl⟩ : syracuseStep 75171685 = 14094691) B14094691
theorem B266075 : Blo 103782 266075 := bstep (se 1 (by rfl) ⟨199556, by rfl⟩ : syracuseStep 266075 = 399113) B399113
theorem B234719 : Blo 103782 234719 := bstep (se 1 (by rfl) ⟨176039, by rfl⟩ : syracuseStep 234719 = 352079) B352079
theorem B3380555 : Blo 103782 3380555 := bstep (se 1 (by rfl) ⟨2535416, by rfl⟩ : syracuseStep 3380555 = 5070833) B5070833
theorem B530387 : Blo 103782 530387 := bstep (se 1 (by rfl) ⟨397790, by rfl⟩ : syracuseStep 530387 = 795581) B795581
theorem B104443 : Blo 103782 104443 := bstep (se 1 (by rfl) ⟨78332, by rfl⟩ : syracuseStep 104443 = 156665) B156665
theorem B399401 : Blo 103782 399401 := bstep (se 2 (by rfl) ⟨149775, by rfl⟩ : syracuseStep 399401 = 299551) B299551
theorem B104551 : Blo 103782 104551 := bstep (se 1 (by rfl) ⟨78413, by rfl⟩ : syracuseStep 104551 = 156827) B156827
theorem B170791 : Blo 103782 170791 := bstep (se 1 (by rfl) ⟨128093, by rfl⟩ : syracuseStep 170791 = 256187) B256187
theorem B269689 : Blo 103782 269689 := bstep (se 2 (by rfl) ⟨101133, by rfl⟩ : syracuseStep 269689 = 202267) B202267
theorem B106011 : Blo 103782 106011 := bstep (se 1 (by rfl) ⟨79508, by rfl⟩ : syracuseStep 106011 = 159017) B159017
theorem B269851 : Blo 103782 269851 := bstep (se 1 (by rfl) ⟨202388, by rfl⟩ : syracuseStep 269851 = 404777) B404777
theorem B269993 : Blo 103782 269993 := bstep (se 2 (by rfl) ⟨101247, by rfl⟩ : syracuseStep 269993 = 202495) B202495
theorem B17571815 : Blo 103782 17571815 := bstep (se 1 (by rfl) ⟨13178861, by rfl⟩ : syracuseStep 17571815 = 26357723) B26357723
theorem B270479 : Blo 103782 270479 := bstep (se 1 (by rfl) ⟨202859, by rfl⟩ : syracuseStep 270479 = 405719) B405719
theorem B106975 : Blo 103782 106975 := bstep (se 1 (by rfl) ⟨80231, by rfl⟩ : syracuseStep 106975 = 160463) B160463
theorem B107367 : Blo 103782 107367 := bstep (se 1 (by rfl) ⟨80525, by rfl⟩ : syracuseStep 107367 = 161051) B161051
theorem B272119 : Blo 103782 272119 := bstep (se 1 (by rfl) ⟨204089, by rfl⟩ : syracuseStep 272119 = 408179) B408179
theorem B534599 : Blo 103782 534599 := bstep (se 1 (by rfl) ⟨400949, by rfl⟩ : syracuseStep 534599 = 801899) B801899
theorem B1943675 : Blo 103782 1943675 := bstep (se 1 (by rfl) ⟨1457756, by rfl⟩ : syracuseStep 1943675 = 2915513) B2915513
theorem B405931 : Blo 103782 405931 := bstep (se 1 (by rfl) ⟨304448, by rfl⟩ : syracuseStep 405931 = 608897) B608897
theorem B309575 : Blo 103782 309575 := bstep (se 1 (by rfl) ⟨232181, by rfl⟩ : syracuseStep 309575 = 464363) B464363
theorem B1097371 : Blo 103782 1097371 := bstep (se 1 (by rfl) ⟨823028, by rfl⟩ : syracuseStep 1097371 = 1646057) B1646057
theorem B1556221 : Blo 103782 1556221 := bstep (se 3 (by rfl) ⟨291791, by rfl⟩ : syracuseStep 1556221 = 583583) B583583
theorem B117787 : Blo 103782 117787 := bstep (se 1 (by rfl) ⟨88340, by rfl⟩ : syracuseStep 117787 = 176681) B176681
theorem B2379223 : Blo 103782 2379223 := bstep (se 1 (by rfl) ⟨1784417, by rfl⟩ : syracuseStep 2379223 = 3568835) B3568835
theorem B118399 : Blo 103782 118399 := bstep (se 1 (by rfl) ⟨88799, by rfl⟩ : syracuseStep 118399 = 177599) B177599
theorem B118687 : Blo 103782 118687 := bstep (se 1 (by rfl) ⟨89015, by rfl⟩ : syracuseStep 118687 = 178031) B178031
theorem B446543 : Blo 103782 446543 := bstep (se 1 (by rfl) ⟨334907, by rfl⟩ : syracuseStep 446543 = 669815) B669815
theorem B3789251 : Blo 103782 3789251 := bstep (se 1 (by rfl) ⟨2841938, by rfl⟩ : syracuseStep 3789251 = 5683877) B5683877
theorem B119515 : Blo 103782 119515 := bstep (se 1 (by rfl) ⟨89636, by rfl⟩ : syracuseStep 119515 = 179273) B179273
theorem B1201391 : Blo 103782 1201391 := bstep (se 1 (by rfl) ⟨901043, by rfl⟩ : syracuseStep 1201391 = 1802087) B1802087
theorem B6510131 : Blo 103782 6510131 := bstep (se 1 (by rfl) ⟨4882598, by rfl⟩ : syracuseStep 6510131 = 9765197) B9765197
theorem B546871 : Blo 103782 546871 := bstep (se 1 (by rfl) ⟨410153, by rfl⟩ : syracuseStep 546871 = 820307) B820307
theorem B1890535 : Blo 103782 1890535 := bstep (se 1 (by rfl) ⟨1417901, by rfl⟩ : syracuseStep 1890535 = 2835803) B2835803
theorem B515335 : Blo 103782 515335 := bstep (se 1 (by rfl) ⟨386501, by rfl⟩ : syracuseStep 515335 = 773003) B773003
theorem B156191 : Blo 103782 156191 := bstep (se 1 (by rfl) ⟨117143, by rfl⟩ : syracuseStep 156191 = 234287) B234287
theorem B451129 : Blo 103782 451129 := bstep (se 2 (by rfl) ⟨169173, by rfl⟩ : syracuseStep 451129 = 338347) B338347
theorem B353375 : Blo 103782 353375 := bstep (se 1 (by rfl) ⟨265031, by rfl⟩ : syracuseStep 353375 = 530063) B530063
theorem B157031 : Blo 103782 157031 := bstep (se 1 (by rfl) ⟨117773, by rfl⟩ : syracuseStep 157031 = 235547) B235547
theorem B8381875 : Blo 103782 8381875 := bstep (se 1 (by rfl) ⟨6286406, by rfl⟩ : syracuseStep 8381875 = 12572813) B12572813
theorem B355103 : Blo 103782 355103 := bstep (se 1 (by rfl) ⟨266327, by rfl⟩ : syracuseStep 355103 = 532655) B532655
theorem B256871 : Blo 103782 256871 := bstep (se 1 (by rfl) ⟨192653, by rfl⟩ : syracuseStep 256871 = 385307) B385307
theorem B159401 : Blo 103782 159401 := bstep (se 2 (by rfl) ⟨59775, by rfl⟩ : syracuseStep 159401 = 119551) B119551
theorem B159515 : Blo 103782 159515 := bstep (se 1 (by rfl) ⟨119636, by rfl⟩ : syracuseStep 159515 = 239273) B239273
theorem B1929071 : Blo 103782 1929071 := bstep (se 1 (by rfl) ⟨1446803, by rfl⟩ : syracuseStep 1929071 = 2893607) B2893607
theorem B290719 : Blo 103782 290719 := bstep (se 1 (by rfl) ⟨218039, by rfl⟩ : syracuseStep 290719 = 436079) B436079
theorem B1666981 : Blo 103782 1666981 := bstep (se 4 (by rfl) ⟨156279, by rfl⟩ : syracuseStep 1666981 = 312559) B312559
theorem B225193 : Blo 103782 225193 := bstep (se 2 (by rfl) ⟨84447, by rfl⟩ : syracuseStep 225193 = 168895) B168895
theorem B357479 : Blo 103782 357479 := bstep (se 1 (by rfl) ⟨268109, by rfl⟩ : syracuseStep 357479 = 536219) B536219
theorem B161135 : Blo 103782 161135 := bstep (se 1 (by rfl) ⟨120851, by rfl⟩ : syracuseStep 161135 = 241703) B241703
theorem B227099 : Blo 103782 227099 := bstep (se 1 (by rfl) ⟨170324, by rfl⟩ : syracuseStep 227099 = 340649) B340649
theorem B1374893 : Blo 103782 1374893 := bstep (se 3 (by rfl) ⟨257792, by rfl⟩ : syracuseStep 1374893 = 515585) B515585
theorem B11175833 : Blo 103782 11175833 := bstep (se 2 (by rfl) ⟨4190937, by rfl⟩ : syracuseStep 11175833 = 8381875) B8381875
theorem B362825 : Blo 103782 362825 := bstep (se 2 (by rfl) ⟨136059, by rfl⟩ : syracuseStep 362825 = 272119) B272119
theorem B297695 : Blo 103782 297695 := bstep (se 1 (by rfl) ⟨223271, by rfl⟩ : syracuseStep 297695 = 446543) B446543
theorem B2526167 : Blo 103782 2526167 := bstep (se 1 (by rfl) ⟨1894625, by rfl⟩ : syracuseStep 2526167 = 3789251) B3789251
theorem B266267 : Blo 103782 266267 := bstep (se 1 (by rfl) ⟨199700, by rfl⟩ : syracuseStep 266267 = 399401) B399401
theorem B300257 : Blo 103782 300257 := bstep (se 2 (by rfl) ⟨112596, by rfl⟩ : syracuseStep 300257 = 225193) B225193
theorem B104127 : Blo 103782 104127 := bstep (se 1 (by rfl) ⟨78095, by rfl⟩ : syracuseStep 104127 = 156191) B156191
theorem B235583 : Blo 103782 235583 := bstep (se 1 (by rfl) ⟨176687, by rfl⟩ : syracuseStep 235583 = 353375) B353375
theorem B104687 : Blo 103782 104687 := bstep (se 1 (by rfl) ⟨78515, by rfl⟩ : syracuseStep 104687 = 157031) B157031
theorem B236735 : Blo 103782 236735 := bstep (se 1 (by rfl) ⟨177551, by rfl⟩ : syracuseStep 236735 = 355103) B355103
theorem B171247 : Blo 103782 171247 := bstep (se 1 (by rfl) ⟨128435, by rfl⟩ : syracuseStep 171247 = 256871) B256871
theorem B106267 : Blo 103782 106267 := bstep (se 1 (by rfl) ⟨79700, by rfl⟩ : syracuseStep 106267 = 159401) B159401
theorem B106343 : Blo 103782 106343 := bstep (se 1 (by rfl) ⟨79757, by rfl⟩ : syracuseStep 106343 = 159515) B159515
theorem B1286047 : Blo 103782 1286047 := bstep (se 1 (by rfl) ⟨964535, by rfl⟩ : syracuseStep 1286047 = 1929071) B1929071
theorem B729161 : Blo 103782 729161 := bstep (se 2 (by rfl) ⟨273435, by rfl⟩ : syracuseStep 729161 = 546871) B546871
theorem B238319 : Blo 103782 238319 := bstep (se 1 (by rfl) ⟨178739, by rfl⟩ : syracuseStep 238319 = 357479) B357479
theorem B107423 : Blo 103782 107423 := bstep (se 1 (by rfl) ⟨80567, by rfl⟩ : syracuseStep 107423 = 161135) B161135
theorem B206383 : Blo 103782 206383 := bstep (se 1 (by rfl) ⟨154787, by rfl⟩ : syracuseStep 206383 = 309575) B309575
theorem B1550501 : Blo 103782 1550501 := bstep (se 4 (by rfl) ⟨145359, by rfl⟩ : syracuseStep 1550501 = 290719) B290719
theorem B8890565 : Blo 103782 8890565 := bstep (se 4 (by rfl) ⟨833490, by rfl⟩ : syracuseStep 8890565 = 1666981) B1666981
theorem B2074961 : Blo 103782 2074961 := bstep (se 2 (by rfl) ⟨778110, by rfl⟩ : syracuseStep 2074961 = 1556221) B1556221
theorem B601505 : Blo 103782 601505 := bstep (se 2 (by rfl) ⟨225564, by rfl⟩ : syracuseStep 601505 = 451129) B451129
theorem B177383 : Blo 103782 177383 := bstep (se 1 (by rfl) ⟨133037, by rfl⟩ : syracuseStep 177383 = 266075) B266075
theorem B800927 : Blo 103782 800927 := bstep (se 1 (by rfl) ⟨600695, by rfl⟩ : syracuseStep 800927 = 1201391) B1201391
theorem B4340087 : Blo 103782 4340087 := bstep (se 1 (by rfl) ⟨3255065, by rfl⟩ : syracuseStep 4340087 = 6510131) B6510131
theorem B179995 : Blo 103782 179995 := bstep (se 1 (by rfl) ⟨134996, by rfl⟩ : syracuseStep 179995 = 269993) B269993
theorem B11714543 : Blo 103782 11714543 := bstep (se 1 (by rfl) ⟨8785907, by rfl⟩ : syracuseStep 11714543 = 17571815) B17571815
theorem B180319 : Blo 103782 180319 := bstep (se 1 (by rfl) ⟨135239, by rfl⟩ : syracuseStep 180319 = 270479) B270479
theorem B541241 : Blo 103782 541241 := bstep (se 2 (by rfl) ⟨202965, by rfl⟩ : syracuseStep 541241 = 405931) B405931
theorem B1295783 : Blo 103782 1295783 := bstep (se 1 (by rfl) ⟨971837, by rfl⟩ : syracuseStep 1295783 = 1943675) B1943675
theorem B5852645 : Blo 103782 5852645 := bstep (se 4 (by rfl) ⟨548685, by rfl⟩ : syracuseStep 5852645 = 1097371) B1097371
theorem B151399 : Blo 103782 151399 := bstep (se 1 (by rfl) ⟨113549, by rfl⟩ : syracuseStep 151399 = 227099) B227099
theorem B611995 : Blo 103782 611995 := bstep (se 1 (by rfl) ⟨458996, by rfl⟩ : syracuseStep 611995 = 917993) B917993
theorem B100228913 : Blo 103782 100228913 := bstep (se 2 (by rfl) ⟨37585842, by rfl⟩ : syracuseStep 100228913 = 75171685) B75171685
theorem B156479 : Blo 103782 156479 := bstep (se 1 (by rfl) ⟨117359, by rfl⟩ : syracuseStep 156479 = 234719) B234719
theorem B2253703 : Blo 103782 2253703 := bstep (se 1 (by rfl) ⟨1690277, by rfl⟩ : syracuseStep 2253703 = 3380555) B3380555
theorem B353591 : Blo 103782 353591 := bstep (se 1 (by rfl) ⟨265193, by rfl⟩ : syracuseStep 353591 = 530387) B530387
theorem B157049 : Blo 103782 157049 := bstep (se 2 (by rfl) ⟨58893, by rfl⟩ : syracuseStep 157049 = 117787) B117787
theorem B910885 : Blo 103782 910885 := bstep (se 4 (by rfl) ⟨85395, by rfl⟩ : syracuseStep 910885 = 170791) B170791
theorem B3172297 : Blo 103782 3172297 := bstep (se 2 (by rfl) ⟨1189611, by rfl⟩ : syracuseStep 3172297 = 2379223) B2379223
theorem B157865 : Blo 103782 157865 := bstep (se 2 (by rfl) ⟨59199, by rfl⟩ : syracuseStep 157865 = 118399) B118399
theorem B158249 : Blo 103782 158249 := bstep (se 2 (by rfl) ⟨59343, by rfl⟩ : syracuseStep 158249 = 118687) B118687
theorem B159353 : Blo 103782 159353 := bstep (se 2 (by rfl) ⟨59757, by rfl⟩ : syracuseStep 159353 = 119515) B119515
theorem B356399 : Blo 103782 356399 := bstep (se 1 (by rfl) ⟨267299, by rfl⟩ : syracuseStep 356399 = 534599) B534599
theorem B2520713 : Blo 103782 2520713 := bstep (se 2 (by rfl) ⟨945267, by rfl⟩ : syracuseStep 2520713 = 1890535) B1890535
theorem B687113 : Blo 103782 687113 := bstep (se 2 (by rfl) ⟨257667, by rfl⟩ : syracuseStep 687113 = 515335) B515335
theorem B916595 : Blo 103782 916595 := bstep (se 1 (by rfl) ⟨687446, by rfl⟩ : syracuseStep 916595 = 1374893) B1374893
theorem B359585 : Blo 103782 359585 := bstep (se 2 (by rfl) ⟨134844, by rfl⟩ : syracuseStep 359585 = 269689) B269689
theorem B359801 : Blo 103782 359801 := bstep (se 2 (by rfl) ⟨134925, by rfl⟩ : syracuseStep 359801 = 269851) B269851
theorem B360827 : Blo 103782 360827 := bstep (se 1 (by rfl) ⟨270620, by rfl⟩ : syracuseStep 360827 = 541241) B541241
theorem B198463 : Blo 103782 198463 := bstep (se 1 (by rfl) ⟨148847, by rfl⟩ : syracuseStep 198463 = 297695) B297695
theorem B1214513 : Blo 103782 1214513 := bstep (se 2 (by rfl) ⟨455442, by rfl⟩ : syracuseStep 1214513 = 910885) B910885
theorem B3901763 : Blo 103782 3901763 := bstep (se 1 (by rfl) ⟨2926322, by rfl⟩ : syracuseStep 3901763 = 5852645) B5852645
theorem B4229729 : Blo 103782 4229729 := bstep (se 2 (by rfl) ⟨1586148, by rfl⟩ : syracuseStep 4229729 = 3172297) B3172297
theorem B200171 : Blo 103782 200171 := bstep (se 1 (by rfl) ⟨150128, by rfl⟩ : syracuseStep 200171 = 300257) B300257
theorem B201865 : Blo 103782 201865 := bstep (se 2 (by rfl) ⟨75699, by rfl⟩ : syracuseStep 201865 = 151399) B151399
theorem B66819275 : Blo 103782 66819275 := bstep (se 1 (by rfl) ⟨50114456, by rfl⟩ : syracuseStep 66819275 = 100228913) B100228913
theorem B104319 : Blo 103782 104319 := bstep (se 1 (by rfl) ⟨78239, by rfl⟩ : syracuseStep 104319 = 156479) B156479
theorem B235727 : Blo 103782 235727 := bstep (se 1 (by rfl) ⟨176795, by rfl⟩ : syracuseStep 235727 = 353591) B353591
theorem B104699 : Blo 103782 104699 := bstep (se 1 (by rfl) ⟨78524, by rfl⟩ : syracuseStep 104699 = 157049) B157049
theorem B105243 : Blo 103782 105243 := bstep (se 1 (by rfl) ⟨78932, by rfl⟩ : syracuseStep 105243 = 157865) B157865
theorem B1383307 : Blo 103782 1383307 := bstep (se 1 (by rfl) ⟨1037480, by rfl⟩ : syracuseStep 1383307 = 2074961) B2074961
theorem B105499 : Blo 103782 105499 := bstep (se 1 (by rfl) ⟨79124, by rfl⟩ : syracuseStep 105499 = 158249) B158249
theorem B401003 : Blo 103782 401003 := bstep (se 1 (by rfl) ⟨300752, by rfl⟩ : syracuseStep 401003 = 601505) B601505
theorem B106235 : Blo 103782 106235 := bstep (se 1 (by rfl) ⟨79676, by rfl⟩ : syracuseStep 106235 = 159353) B159353
theorem B237599 : Blo 103782 237599 := bstep (se 1 (by rfl) ⟨178199, by rfl⟩ : syracuseStep 237599 = 356399) B356399
theorem B1680475 : Blo 103782 1680475 := bstep (se 1 (by rfl) ⟨1260356, by rfl⟩ : syracuseStep 1680475 = 2520713) B2520713
theorem B533951 : Blo 103782 533951 := bstep (se 1 (by rfl) ⟨400463, by rfl⟩ : syracuseStep 533951 = 800927) B800927
theorem B2893391 : Blo 103782 2893391 := bstep (se 1 (by rfl) ⟨2170043, by rfl⟩ : syracuseStep 2893391 = 4340087) B4340087
theorem B239723 : Blo 103782 239723 := bstep (se 1 (by rfl) ⟨179792, by rfl⟩ : syracuseStep 239723 = 359585) B359585
theorem B239867 : Blo 103782 239867 := bstep (se 1 (by rfl) ⟨179900, by rfl⟩ : syracuseStep 239867 = 359801) B359801
theorem B239993 : Blo 103782 239993 := bstep (se 2 (by rfl) ⟨89997, by rfl⟩ : syracuseStep 239993 = 179995) B179995
theorem B1714729 : Blo 103782 1714729 := bstep (se 2 (by rfl) ⟨643023, by rfl⟩ : syracuseStep 1714729 = 1286047) B1286047
theorem B7809695 : Blo 103782 7809695 := bstep (se 1 (by rfl) ⟨5857271, by rfl⟩ : syracuseStep 7809695 = 11714543) B11714543
theorem B240425 : Blo 103782 240425 := bstep (se 2 (by rfl) ⟨90159, by rfl⟩ : syracuseStep 240425 = 180319) B180319
theorem B863855 : Blo 103782 863855 := bstep (se 1 (by rfl) ⟨647891, by rfl⟩ : syracuseStep 863855 = 1295783) B1295783
theorem B7450555 : Blo 103782 7450555 := bstep (se 1 (by rfl) ⟨5587916, by rfl⟩ : syracuseStep 7450555 = 11175833) B11175833
theorem B241883 : Blo 103782 241883 := bstep (se 1 (by rfl) ⟨181412, by rfl⟩ : syracuseStep 241883 = 362825) B362825
theorem B1684111 : Blo 103782 1684111 := bstep (se 1 (by rfl) ⟨1263083, by rfl⟩ : syracuseStep 1684111 = 2526167) B2526167
theorem B275177 : Blo 103782 275177 := bstep (se 2 (by rfl) ⟨103191, by rfl⟩ : syracuseStep 275177 = 206383) B206383
theorem B177511 : Blo 103782 177511 := bstep (se 1 (by rfl) ⟨133133, by rfl⟩ : syracuseStep 177511 = 266267) B266267
theorem B23708173 : Blo 103782 23708173 := bstep (se 3 (by rfl) ⟨4445282, by rfl⟩ : syracuseStep 23708173 = 8890565) B8890565
theorem B1033667 : Blo 103782 1033667 := bstep (se 1 (by rfl) ⟨775250, by rfl⟩ : syracuseStep 1033667 = 1550501) B1550501
theorem B118255 : Blo 103782 118255 := bstep (se 1 (by rfl) ⟨88691, by rfl⟩ : syracuseStep 118255 = 177383) B177383
theorem B611063 : Blo 103782 611063 := bstep (se 1 (by rfl) ⟨458297, by rfl⟩ : syracuseStep 611063 = 916595) B916595
theorem B3004937 : Blo 103782 3004937 := bstep (se 2 (by rfl) ⟨1126851, by rfl⟩ : syracuseStep 3004937 = 2253703) B2253703
theorem B157055 : Blo 103782 157055 := bstep (se 1 (by rfl) ⟨117791, by rfl⟩ : syracuseStep 157055 = 235583) B235583
theorem B157823 : Blo 103782 157823 := bstep (se 1 (by rfl) ⟨118367, by rfl⟩ : syracuseStep 157823 = 236735) B236735
theorem B486107 : Blo 103782 486107 := bstep (se 1 (by rfl) ⟨364580, by rfl⟩ : syracuseStep 486107 = 729161) B729161
theorem B158879 : Blo 103782 158879 := bstep (se 1 (by rfl) ⟨119159, by rfl⟩ : syracuseStep 158879 = 238319) B238319
theorem B815993 : Blo 103782 815993 := bstep (se 2 (by rfl) ⟨305997, by rfl⟩ : syracuseStep 815993 = 611995) B611995
theorem B228329 : Blo 103782 228329 := bstep (se 2 (by rfl) ⟨85623, by rfl⟩ : syracuseStep 228329 = 171247) B171247
theorem B458075 : Blo 103782 458075 := bstep (se 1 (by rfl) ⟨343556, by rfl⟩ : syracuseStep 458075 = 687113) B687113
theorem B689111 : Blo 103782 689111 := bstep (se 1 (by rfl) ⟨516833, by rfl⟩ : syracuseStep 689111 = 1033667) B1033667
theorem B2819819 : Blo 103782 2819819 := bstep (se 1 (by rfl) ⟨2114864, by rfl⟩ : syracuseStep 2819819 = 4229729) B4229729
theorem B264617 : Blo 103782 264617 := bstep (se 2 (by rfl) ⟨99231, by rfl⟩ : syracuseStep 264617 = 198463) B198463
theorem B2003291 : Blo 103782 2003291 := bstep (se 1 (by rfl) ⟨1502468, by rfl⟩ : syracuseStep 2003291 = 3004937) B3004937
theorem B7377637 : Blo 103782 7377637 := bstep (se 4 (by rfl) ⟨691653, by rfl⟩ : syracuseStep 7377637 = 1383307) B1383307
theorem B267335 : Blo 103782 267335 := bstep (se 1 (by rfl) ⟨200501, by rfl⟩ : syracuseStep 267335 = 401003) B401003
theorem B9934073 : Blo 103782 9934073 := bstep (se 2 (by rfl) ⟨3725277, by rfl⟩ : syracuseStep 9934073 = 7450555) B7450555
theorem B104703 : Blo 103782 104703 := bstep (se 1 (by rfl) ⟨78527, by rfl⟩ : syracuseStep 104703 = 157055) B157055
theorem B105215 : Blo 103782 105215 := bstep (se 1 (by rfl) ⟨78911, by rfl⟩ : syracuseStep 105215 = 157823) B157823
theorem B269153 : Blo 103782 269153 := bstep (se 2 (by rfl) ⟨100932, by rfl⟩ : syracuseStep 269153 = 201865) B201865
theorem B236681 : Blo 103782 236681 := bstep (se 2 (by rfl) ⟨88755, by rfl⟩ : syracuseStep 236681 = 177511) B177511
theorem B105919 : Blo 103782 105919 := bstep (se 1 (by rfl) ⟨79439, by rfl⟩ : syracuseStep 105919 = 158879) B158879
theorem B533789 : Blo 103782 533789 := bstep (se 3 (by rfl) ⟨100085, by rfl⟩ : syracuseStep 533789 = 200171) B200171
theorem B305383 : Blo 103782 305383 := bstep (se 1 (by rfl) ⟨229037, by rfl⟩ : syracuseStep 305383 = 458075) B458075
theorem B240551 : Blo 103782 240551 := bstep (se 1 (by rfl) ⟨180413, by rfl⟩ : syracuseStep 240551 = 360827) B360827
theorem B2240633 : Blo 103782 2240633 := bstep (se 2 (by rfl) ⟨840237, by rfl⟩ : syracuseStep 2240633 = 1680475) B1680475
theorem B2601175 : Blo 103782 2601175 := bstep (se 1 (by rfl) ⟨1950881, by rfl⟩ : syracuseStep 2601175 = 3901763) B3901763
theorem B733805 : Blo 103782 733805 := bstep (se 3 (by rfl) ⟨137588, by rfl⟩ : syracuseStep 733805 = 275177) B275177
theorem B407375 : Blo 103782 407375 := bstep (se 1 (by rfl) ⟨305531, by rfl⟩ : syracuseStep 407375 = 611063) B611063
theorem B44546183 : Blo 103782 44546183 := bstep (se 1 (by rfl) ⟨33409637, by rfl⟩ : syracuseStep 44546183 = 66819275) B66819275
theorem B2245481 : Blo 103782 2245481 := bstep (se 2 (by rfl) ⟨842055, by rfl⟩ : syracuseStep 2245481 = 1684111) B1684111
theorem B575903 : Blo 103782 575903 := bstep (se 1 (by rfl) ⟨431927, by rfl⟩ : syracuseStep 575903 = 863855) B863855
theorem B543995 : Blo 103782 543995 := bstep (se 1 (by rfl) ⟨407996, by rfl⟩ : syracuseStep 543995 = 815993) B815993
theorem B152219 : Blo 103782 152219 := bstep (se 1 (by rfl) ⟨114164, by rfl⟩ : syracuseStep 152219 = 228329) B228329
theorem B31610897 : Blo 103782 31610897 := bstep (se 2 (by rfl) ⟨11854086, by rfl⟩ : syracuseStep 31610897 = 23708173) B23708173
theorem B809675 : Blo 103782 809675 := bstep (se 1 (by rfl) ⟨607256, by rfl⟩ : syracuseStep 809675 = 1214513) B1214513
theorem B2286305 : Blo 103782 2286305 := bstep (se 2 (by rfl) ⟨857364, by rfl⟩ : syracuseStep 2286305 = 1714729) B1714729
theorem B157151 : Blo 103782 157151 := bstep (se 1 (by rfl) ⟨117863, by rfl⟩ : syracuseStep 157151 = 235727) B235727
theorem B157673 : Blo 103782 157673 := bstep (se 2 (by rfl) ⟨59127, by rfl⟩ : syracuseStep 157673 = 118255) B118255
theorem B158399 : Blo 103782 158399 := bstep (se 1 (by rfl) ⟨118799, by rfl⟩ : syracuseStep 158399 = 237599) B237599
theorem B355967 : Blo 103782 355967 := bstep (se 1 (by rfl) ⟨266975, by rfl⟩ : syracuseStep 355967 = 533951) B533951
theorem B1928927 : Blo 103782 1928927 := bstep (se 1 (by rfl) ⟨1446695, by rfl⟩ : syracuseStep 1928927 = 2893391) B2893391
theorem B159815 : Blo 103782 159815 := bstep (se 1 (by rfl) ⟨119861, by rfl⟩ : syracuseStep 159815 = 239723) B239723
theorem B159911 : Blo 103782 159911 := bstep (se 1 (by rfl) ⟨119933, by rfl⟩ : syracuseStep 159911 = 239867) B239867
theorem B159995 : Blo 103782 159995 := bstep (se 1 (by rfl) ⟨119996, by rfl⟩ : syracuseStep 159995 = 239993) B239993
theorem B5206463 : Blo 103782 5206463 := bstep (se 1 (by rfl) ⟨3904847, by rfl⟩ : syracuseStep 5206463 = 7809695) B7809695
theorem B324071 : Blo 103782 324071 := bstep (se 1 (by rfl) ⟨243053, by rfl⟩ : syracuseStep 324071 = 486107) B486107
theorem B160283 : Blo 103782 160283 := bstep (se 1 (by rfl) ⟨120212, by rfl⟩ : syracuseStep 160283 = 240425) B240425
theorem B161255 : Blo 103782 161255 := bstep (se 1 (by rfl) ⟨120941, by rfl⟩ : syracuseStep 161255 = 241883) B241883
theorem B459407 : Blo 103782 459407 := bstep (se 1 (by rfl) ⟨344555, by rfl⟩ : syracuseStep 459407 = 689111) B689111
theorem B362663 : Blo 103782 362663 := bstep (se 1 (by rfl) ⟨271997, by rfl⟩ : syracuseStep 362663 = 543995) B543995
theorem B6622715 : Blo 103782 6622715 := bstep (se 1 (by rfl) ⟨4967036, by rfl⟩ : syracuseStep 6622715 = 9934073) B9934073
theorem B21073931 : Blo 103782 21073931 := bstep (se 1 (by rfl) ⟨15805448, by rfl⟩ : syracuseStep 21073931 = 31610897) B31610897
theorem B9836849 : Blo 103782 9836849 := bstep (se 2 (by rfl) ⟨3688818, by rfl⟩ : syracuseStep 9836849 = 7377637) B7377637
theorem B104767 : Blo 103782 104767 := bstep (se 1 (by rfl) ⟨78575, by rfl⟩ : syracuseStep 104767 = 157151) B157151
theorem B105115 : Blo 103782 105115 := bstep (se 1 (by rfl) ⟨78836, by rfl⟩ : syracuseStep 105115 = 157673) B157673
theorem B105599 : Blo 103782 105599 := bstep (se 1 (by rfl) ⟨79199, by rfl⟩ : syracuseStep 105599 = 158399) B158399
theorem B237311 : Blo 103782 237311 := bstep (se 1 (by rfl) ⟨177983, by rfl⟩ : syracuseStep 237311 = 355967) B355967
theorem B1285951 : Blo 103782 1285951 := bstep (se 1 (by rfl) ⟨964463, by rfl⟩ : syracuseStep 1285951 = 1928927) B1928927
theorem B106543 : Blo 103782 106543 := bstep (se 1 (by rfl) ⟨79907, by rfl⟩ : syracuseStep 106543 = 159815) B159815
theorem B106607 : Blo 103782 106607 := bstep (se 1 (by rfl) ⟨79955, by rfl⟩ : syracuseStep 106607 = 159911) B159911
theorem B106663 : Blo 103782 106663 := bstep (se 1 (by rfl) ⟨79997, by rfl⟩ : syracuseStep 106663 = 159995) B159995
theorem B106855 : Blo 103782 106855 := bstep (se 1 (by rfl) ⟨80141, by rfl⟩ : syracuseStep 106855 = 160283) B160283
theorem B107503 : Blo 103782 107503 := bstep (se 1 (by rfl) ⟨80627, by rfl⟩ : syracuseStep 107503 = 161255) B161255
theorem B271583 : Blo 103782 271583 := bstep (se 1 (by rfl) ⟨203687, by rfl⟩ : syracuseStep 271583 = 407375) B407375
theorem B29697455 : Blo 103782 29697455 := bstep (se 1 (by rfl) ⟨22273091, by rfl⟩ : syracuseStep 29697455 = 44546183) B44546183
theorem B5975021 : Blo 103782 5975021 := bstep (se 3 (by rfl) ⟨1120316, by rfl⟩ : syracuseStep 5975021 = 2240633) B2240633
theorem B176411 : Blo 103782 176411 := bstep (se 1 (by rfl) ⟨132308, by rfl⟩ : syracuseStep 176411 = 264617) B264617
theorem B405917 : Blo 103782 405917 := bstep (se 3 (by rfl) ⟨76109, by rfl⟩ : syracuseStep 405917 = 152219) B152219
theorem B407177 : Blo 103782 407177 := bstep (se 2 (by rfl) ⟨152691, by rfl⟩ : syracuseStep 407177 = 305383) B305383
theorem B178223 : Blo 103782 178223 := bstep (se 1 (by rfl) ⟨133667, by rfl⟩ : syracuseStep 178223 = 267335) B267335
theorem B539783 : Blo 103782 539783 := bstep (se 1 (by rfl) ⟨404837, by rfl⟩ : syracuseStep 539783 = 809675) B809675
theorem B179435 : Blo 103782 179435 := bstep (se 1 (by rfl) ⟨134576, by rfl⟩ : syracuseStep 179435 = 269153) B269153
theorem B7519517 : Blo 103782 7519517 := bstep (se 3 (by rfl) ⟨1409909, by rfl⟩ : syracuseStep 7519517 = 2819819) B2819819
theorem B1524203 : Blo 103782 1524203 := bstep (se 1 (by rfl) ⟨1143152, by rfl⟩ : syracuseStep 1524203 = 2286305) B2286305
theorem B216047 : Blo 103782 216047 := bstep (se 1 (by rfl) ⟨162035, by rfl⟩ : syracuseStep 216047 = 324071) B324071
theorem B1496987 : Blo 103782 1496987 := bstep (se 1 (by rfl) ⟨1122740, by rfl⟩ : syracuseStep 1496987 = 2245481) B2245481
theorem B383935 : Blo 103782 383935 := bstep (se 1 (by rfl) ⟨287951, by rfl⟩ : syracuseStep 383935 = 575903) B575903
theorem B1335527 : Blo 103782 1335527 := bstep (se 1 (by rfl) ⟨1001645, by rfl⟩ : syracuseStep 1335527 = 2003291) B2003291
theorem B157787 : Blo 103782 157787 := bstep (se 1 (by rfl) ⟨118340, by rfl⟩ : syracuseStep 157787 = 236681) B236681
theorem B3468233 : Blo 103782 3468233 := bstep (se 2 (by rfl) ⟨1300587, by rfl⟩ : syracuseStep 3468233 = 2601175) B2601175
theorem B355859 : Blo 103782 355859 := bstep (se 1 (by rfl) ⟨266894, by rfl⟩ : syracuseStep 355859 = 533789) B533789
theorem B160367 : Blo 103782 160367 := bstep (se 1 (by rfl) ⟨120275, by rfl⟩ : syracuseStep 160367 = 240551) B240551
theorem B3470975 : Blo 103782 3470975 := bstep (se 1 (by rfl) ⟨2603231, by rfl⟩ : syracuseStep 3470975 = 5206463) B5206463
theorem B489203 : Blo 103782 489203 := bstep (se 1 (by rfl) ⟨366902, by rfl⟩ : syracuseStep 489203 = 733805) B733805
theorem B1016135 : Blo 103782 1016135 := bstep (se 1 (by rfl) ⟨762101, by rfl⟩ : syracuseStep 1016135 = 1524203) B1524203
theorem B1901045 : Blo 103782 1901045 := bstep (se 5 (by rfl) ⟨89111, by rfl⟩ : syracuseStep 1901045 = 178223) B178223
theorem B890351 : Blo 103782 890351 := bstep (se 1 (by rfl) ⟨667763, by rfl⟩ : syracuseStep 890351 = 1335527) B1335527
theorem B105191 : Blo 103782 105191 := bstep (se 1 (by rfl) ⟨78893, by rfl⟩ : syracuseStep 105191 = 157787) B157787
theorem B237239 : Blo 103782 237239 := bstep (se 1 (by rfl) ⟨177929, by rfl⟩ : syracuseStep 237239 = 355859) B355859
theorem B270611 : Blo 103782 270611 := bstep (se 1 (by rfl) ⟨202958, by rfl⟩ : syracuseStep 270611 = 405917) B405917
theorem B106911 : Blo 103782 106911 := bstep (se 1 (by rfl) ⟨80183, by rfl⟩ : syracuseStep 106911 = 160367) B160367
theorem B271451 : Blo 103782 271451 := bstep (se 1 (by rfl) ⟨203588, by rfl⟩ : syracuseStep 271451 = 407177) B407177
theorem B1714601 : Blo 103782 1714601 := bstep (se 2 (by rfl) ⟨642975, by rfl⟩ : syracuseStep 1714601 = 1285951) B1285951
theorem B306271 : Blo 103782 306271 := bstep (se 1 (by rfl) ⟨229703, by rfl⟩ : syracuseStep 306271 = 459407) B459407
theorem B241775 : Blo 103782 241775 := bstep (se 1 (by rfl) ⟨181331, by rfl⟩ : syracuseStep 241775 = 362663) B362663
theorem B144031 : Blo 103782 144031 := bstep (se 1 (by rfl) ⟨108023, by rfl⟩ : syracuseStep 144031 = 216047) B216047
theorem B997991 : Blo 103782 997991 := bstep (se 1 (by rfl) ⟨748493, by rfl⟩ : syracuseStep 997991 = 1496987) B1496987
theorem B26231597 : Blo 103782 26231597 := bstep (se 3 (by rfl) ⟨4918424, by rfl⟩ : syracuseStep 26231597 = 9836849) B9836849
theorem B181055 : Blo 103782 181055 := bstep (se 1 (by rfl) ⟨135791, by rfl⟩ : syracuseStep 181055 = 271583) B271583
theorem B2312155 : Blo 103782 2312155 := bstep (se 1 (by rfl) ⟨1734116, by rfl⟩ : syracuseStep 2312155 = 3468233) B3468233
theorem B3983347 : Blo 103782 3983347 := bstep (se 1 (by rfl) ⟨2987510, by rfl⟩ : syracuseStep 3983347 = 5975021) B5975021
theorem B117607 : Blo 103782 117607 := bstep (se 1 (by rfl) ⟨88205, by rfl⟩ : syracuseStep 117607 = 176411) B176411
theorem B2313983 : Blo 103782 2313983 := bstep (se 1 (by rfl) ⟨1735487, by rfl⟩ : syracuseStep 2313983 = 3470975) B3470975
theorem B511913 : Blo 103782 511913 := bstep (se 2 (by rfl) ⟨191967, by rfl⟩ : syracuseStep 511913 = 383935) B383935
theorem B119623 : Blo 103782 119623 := bstep (se 1 (by rfl) ⟨89717, by rfl⟩ : syracuseStep 119623 = 179435) B179435
theorem B4415143 : Blo 103782 4415143 := bstep (se 1 (by rfl) ⟨3311357, by rfl⟩ : syracuseStep 4415143 = 6622715) B6622715
theorem B14049287 : Blo 103782 14049287 := bstep (se 1 (by rfl) ⟨10536965, by rfl⟩ : syracuseStep 14049287 = 21073931) B21073931
theorem B79193213 : Blo 103782 79193213 := bstep (se 3 (by rfl) ⟨14848727, by rfl⟩ : syracuseStep 79193213 = 29697455) B29697455
theorem B158207 : Blo 103782 158207 := bstep (se 1 (by rfl) ⟨118655, by rfl⟩ : syracuseStep 158207 = 237311) B237311
theorem B326135 : Blo 103782 326135 := bstep (se 1 (by rfl) ⟨244601, by rfl⟩ : syracuseStep 326135 = 489203) B489203
theorem B359855 : Blo 103782 359855 := bstep (se 1 (by rfl) ⟨269891, by rfl⟩ : syracuseStep 359855 = 539783) B539783
theorem B5013011 : Blo 103782 5013011 := bstep (se 1 (by rfl) ⟨3759758, by rfl⟩ : syracuseStep 5013011 = 7519517) B7519517
theorem B1542655 : Blo 103782 1542655 := bstep (se 1 (by rfl) ⟨1156991, by rfl⟩ : syracuseStep 1542655 = 2313983) B2313983
theorem B3082873 : Blo 103782 3082873 := bstep (se 2 (by rfl) ⟨1156077, by rfl⟩ : syracuseStep 3082873 = 2312155) B2312155
theorem B5311129 : Blo 103782 5311129 := bstep (se 2 (by rfl) ⟨1991673, by rfl⟩ : syracuseStep 5311129 = 3983347) B3983347
theorem B593567 : Blo 103782 593567 := bstep (se 1 (by rfl) ⟨445175, by rfl⟩ : syracuseStep 593567 = 890351) B890351
theorem B52795475 : Blo 103782 52795475 := bstep (se 1 (by rfl) ⟨39596606, by rfl⟩ : syracuseStep 52795475 = 79193213) B79193213
theorem B105471 : Blo 103782 105471 := bstep (se 1 (by rfl) ⟨79103, by rfl⟩ : syracuseStep 105471 = 158207) B158207
theorem B665327 : Blo 103782 665327 := bstep (se 1 (by rfl) ⟨498995, by rfl⟩ : syracuseStep 665327 = 997991) B997991
theorem B239903 : Blo 103782 239903 := bstep (se 1 (by rfl) ⟨179927, by rfl⟩ : syracuseStep 239903 = 359855) B359855
theorem B341275 : Blo 103782 341275 := bstep (se 1 (by rfl) ⟨255956, by rfl⟩ : syracuseStep 341275 = 511913) B511913
theorem B408361 : Blo 103782 408361 := bstep (se 2 (by rfl) ⟨153135, by rfl⟩ : syracuseStep 408361 = 306271) B306271
theorem B180407 : Blo 103782 180407 := bstep (se 1 (by rfl) ⟨135305, by rfl⟩ : syracuseStep 180407 = 270611) B270611
theorem B180967 : Blo 103782 180967 := bstep (se 1 (by rfl) ⟨135725, by rfl⟩ : syracuseStep 180967 = 271451) B271451
theorem B217423 : Blo 103782 217423 := bstep (se 1 (by rfl) ⟨163067, by rfl⟩ : syracuseStep 217423 = 326135) B326135
theorem B5886857 : Blo 103782 5886857 := bstep (se 2 (by rfl) ⟨2207571, by rfl⟩ : syracuseStep 5886857 = 4415143) B4415143
theorem B677423 : Blo 103782 677423 := bstep (se 1 (by rfl) ⟨508067, by rfl⟩ : syracuseStep 677423 = 1016135) B1016135
theorem B1267363 : Blo 103782 1267363 := bstep (se 1 (by rfl) ⟨950522, by rfl⟩ : syracuseStep 1267363 = 1901045) B1901045
theorem B17487731 : Blo 103782 17487731 := bstep (se 1 (by rfl) ⟨13115798, by rfl⟩ : syracuseStep 17487731 = 26231597) B26231597
theorem B120703 : Blo 103782 120703 := bstep (se 1 (by rfl) ⟨90527, by rfl⟩ : syracuseStep 120703 = 181055) B181055
theorem B156809 : Blo 103782 156809 := bstep (se 2 (by rfl) ⟨58803, by rfl⟩ : syracuseStep 156809 = 117607) B117607
theorem B158159 : Blo 103782 158159 := bstep (se 1 (by rfl) ⟨118619, by rfl⟩ : syracuseStep 158159 = 237239) B237239
theorem B9366191 : Blo 103782 9366191 := bstep (se 1 (by rfl) ⟨7024643, by rfl⟩ : syracuseStep 9366191 = 14049287) B14049287
theorem B192041 : Blo 103782 192041 := bstep (se 2 (by rfl) ⟨72015, by rfl⟩ : syracuseStep 192041 = 144031) B144031
theorem B159497 : Blo 103782 159497 := bstep (se 2 (by rfl) ⟨59811, by rfl⟩ : syracuseStep 159497 = 119623) B119623
theorem B1143067 : Blo 103782 1143067 := bstep (se 1 (by rfl) ⟨857300, by rfl⟩ : syracuseStep 1143067 = 1714601) B1714601
theorem B161183 : Blo 103782 161183 := bstep (se 1 (by rfl) ⟨120887, by rfl⟩ : syracuseStep 161183 = 241775) B241775
theorem B3342007 : Blo 103782 3342007 := bstep (se 1 (by rfl) ⟨2506505, by rfl⟩ : syracuseStep 3342007 = 5013011) B5013011
theorem B395711 : Blo 103782 395711 := bstep (se 1 (by rfl) ⟨296783, by rfl⟩ : syracuseStep 395711 = 593567) B593567
theorem B7081505 : Blo 103782 7081505 := bstep (se 2 (by rfl) ⟨2655564, by rfl⟩ : syracuseStep 7081505 = 5311129) B5311129
theorem B35196983 : Blo 103782 35196983 := bstep (se 1 (by rfl) ⟨26397737, by rfl⟩ : syracuseStep 35196983 = 52795475) B52795475
theorem B1806461 : Blo 103782 1806461 := bstep (se 3 (by rfl) ⟨338711, by rfl⟩ : syracuseStep 1806461 = 677423) B677423
theorem B104539 : Blo 103782 104539 := bstep (se 1 (by rfl) ⟨78404, by rfl⟩ : syracuseStep 104539 = 156809) B156809
theorem B105439 : Blo 103782 105439 := bstep (se 1 (by rfl) ⟨79079, by rfl⟩ : syracuseStep 105439 = 158159) B158159
theorem B106331 : Blo 103782 106331 := bstep (se 1 (by rfl) ⟨79748, by rfl⟩ : syracuseStep 106331 = 159497) B159497
theorem B107455 : Blo 103782 107455 := bstep (se 1 (by rfl) ⟨80591, by rfl⟩ : syracuseStep 107455 = 161183) B161183
theorem B241289 : Blo 103782 241289 := bstep (se 2 (by rfl) ⟨90483, by rfl⟩ : syracuseStep 241289 = 180967) B180967
theorem B1159589 : Blo 103782 1159589 := bstep (se 4 (by rfl) ⟨108711, by rfl⟩ : syracuseStep 1159589 = 217423) B217423
theorem B4110497 : Blo 103782 4110497 := bstep (se 2 (by rfl) ⟨1541436, by rfl⟩ : syracuseStep 4110497 = 3082873) B3082873
theorem B1524089 : Blo 103782 1524089 := bstep (se 2 (by rfl) ⟨571533, by rfl⟩ : syracuseStep 1524089 = 1143067) B1143067
theorem B443551 : Blo 103782 443551 := bstep (se 1 (by rfl) ⟨332663, by rfl⟩ : syracuseStep 443551 = 665327) B665327
theorem B6244127 : Blo 103782 6244127 := bstep (se 1 (by rfl) ⟨4683095, by rfl⟩ : syracuseStep 6244127 = 9366191) B9366191
theorem B1689817 : Blo 103782 1689817 := bstep (se 2 (by rfl) ⟨633681, by rfl⟩ : syracuseStep 1689817 = 1267363) B1267363
theorem B544481 : Blo 103782 544481 := bstep (se 2 (by rfl) ⟨204180, by rfl⟩ : syracuseStep 544481 = 408361) B408361
theorem B120271 : Blo 103782 120271 := bstep (se 1 (by rfl) ⟨90203, by rfl⟩ : syracuseStep 120271 = 180407) B180407
theorem B3924571 : Blo 103782 3924571 := bstep (se 1 (by rfl) ⟨2943428, by rfl⟩ : syracuseStep 3924571 = 5886857) B5886857
theorem B2056873 : Blo 103782 2056873 := bstep (se 2 (by rfl) ⟨771327, by rfl⟩ : syracuseStep 2056873 = 1542655) B1542655
theorem B11658487 : Blo 103782 11658487 := bstep (se 1 (by rfl) ⟨8743865, by rfl⟩ : syracuseStep 11658487 = 17487731) B17487731
theorem B159935 : Blo 103782 159935 := bstep (se 1 (by rfl) ⟨119951, by rfl⟩ : syracuseStep 159935 = 239903) B239903
theorem B455033 : Blo 103782 455033 := bstep (se 2 (by rfl) ⟨170637, by rfl⟩ : syracuseStep 455033 = 341275) B341275
theorem B128027 : Blo 103782 128027 := bstep (se 1 (by rfl) ⟨96020, by rfl⟩ : syracuseStep 128027 = 192041) B192041
theorem B160937 : Blo 103782 160937 := bstep (se 2 (by rfl) ⟨60351, by rfl⟩ : syracuseStep 160937 = 120703) B120703
theorem B4456009 : Blo 103782 4456009 := bstep (se 2 (by rfl) ⟨1671003, by rfl⟩ : syracuseStep 4456009 = 3342007) B3342007
theorem B1016059 : Blo 103782 1016059 := bstep (se 1 (by rfl) ⟨762044, by rfl⟩ : syracuseStep 1016059 = 1524089) B1524089
theorem B4162751 : Blo 103782 4162751 := bstep (se 1 (by rfl) ⟨3122063, by rfl⟩ : syracuseStep 4162751 = 6244127) B6244127
theorem B591401 : Blo 103782 591401 := bstep (se 2 (by rfl) ⟨221775, by rfl⟩ : syracuseStep 591401 = 443551) B443551
theorem B263807 : Blo 103782 263807 := bstep (se 1 (by rfl) ⟨197855, by rfl⟩ : syracuseStep 263807 = 395711) B395711
theorem B4721003 : Blo 103782 4721003 := bstep (se 1 (by rfl) ⟨3540752, by rfl⟩ : syracuseStep 4721003 = 7081505) B7081505
theorem B362987 : Blo 103782 362987 := bstep (se 1 (by rfl) ⟨272240, by rfl⟩ : syracuseStep 362987 = 544481) B544481
theorem B23464655 : Blo 103782 23464655 := bstep (se 1 (by rfl) ⟨17598491, by rfl⟩ : syracuseStep 23464655 = 35196983) B35196983
theorem B106623 : Blo 103782 106623 := bstep (se 1 (by rfl) ⟨79967, by rfl⟩ : syracuseStep 106623 = 159935) B159935
theorem B303355 : Blo 103782 303355 := bstep (se 1 (by rfl) ⟨227516, by rfl⟩ : syracuseStep 303355 = 455033) B455033
theorem B107291 : Blo 103782 107291 := bstep (se 1 (by rfl) ⟨80468, by rfl⟩ : syracuseStep 107291 = 160937) B160937
theorem B5941345 : Blo 103782 5941345 := bstep (se 2 (by rfl) ⟨2228004, by rfl⟩ : syracuseStep 5941345 = 4456009) B4456009
theorem B15544649 : Blo 103782 15544649 := bstep (se 2 (by rfl) ⟨5829243, by rfl⟩ : syracuseStep 15544649 = 11658487) B11658487
theorem B341405 : Blo 103782 341405 := bstep (se 3 (by rfl) ⟨64013, by rfl⟩ : syracuseStep 341405 = 128027) B128027
theorem B773059 : Blo 103782 773059 := bstep (se 1 (by rfl) ⟨579794, by rfl⟩ : syracuseStep 773059 = 1159589) B1159589
theorem B2740331 : Blo 103782 2740331 := bstep (se 1 (by rfl) ⟨2055248, by rfl⟩ : syracuseStep 2740331 = 4110497) B4110497
theorem B5232761 : Blo 103782 5232761 := bstep (se 2 (by rfl) ⟨1962285, by rfl⟩ : syracuseStep 5232761 = 3924571) B3924571
theorem B2742497 : Blo 103782 2742497 := bstep (se 2 (by rfl) ⟨1028436, by rfl⟩ : syracuseStep 2742497 = 2056873) B2056873
theorem B1204307 : Blo 103782 1204307 := bstep (se 1 (by rfl) ⟨903230, by rfl⟩ : syracuseStep 1204307 = 1806461) B1806461
theorem B2253089 : Blo 103782 2253089 := bstep (se 2 (by rfl) ⟨844908, by rfl⟩ : syracuseStep 2253089 = 1689817) B1689817
theorem B160361 : Blo 103782 160361 := bstep (se 2 (by rfl) ⟨60135, by rfl⟩ : syracuseStep 160361 = 120271) B120271
theorem B160859 : Blo 103782 160859 := bstep (se 1 (by rfl) ⟨120644, by rfl⟩ : syracuseStep 160859 = 241289) B241289
theorem B394267 : Blo 103782 394267 := bstep (se 1 (by rfl) ⟨295700, by rfl⟩ : syracuseStep 394267 = 591401) B591401
theorem B3147335 : Blo 103782 3147335 := bstep (se 1 (by rfl) ⟨2360501, by rfl⟩ : syracuseStep 3147335 = 4721003) B4721003
theorem B10363099 : Blo 103782 10363099 := bstep (se 1 (by rfl) ⟨7772324, by rfl⟩ : syracuseStep 10363099 = 15544649) B15544649
theorem B106907 : Blo 103782 106907 := bstep (se 1 (by rfl) ⟨80180, by rfl⟩ : syracuseStep 106907 = 160361) B160361
theorem B107239 : Blo 103782 107239 := bstep (se 1 (by rfl) ⟨80429, by rfl⟩ : syracuseStep 107239 = 160859) B160859
theorem B1354745 : Blo 103782 1354745 := bstep (se 2 (by rfl) ⟨508029, by rfl⟩ : syracuseStep 1354745 = 1016059) B1016059
theorem B404473 : Blo 103782 404473 := bstep (se 2 (by rfl) ⟨151677, by rfl⟩ : syracuseStep 404473 = 303355) B303355
theorem B175871 : Blo 103782 175871 := bstep (se 1 (by rfl) ⟨131903, by rfl⟩ : syracuseStep 175871 = 263807) B263807
theorem B241991 : Blo 103782 241991 := bstep (se 1 (by rfl) ⟨181493, by rfl⟩ : syracuseStep 241991 = 362987) B362987
theorem B15643103 : Blo 103782 15643103 := bstep (se 1 (by rfl) ⟨11732327, by rfl⟩ : syracuseStep 15643103 = 23464655) B23464655
theorem B1030745 : Blo 103782 1030745 := bstep (se 2 (by rfl) ⟨386529, by rfl⟩ : syracuseStep 1030745 = 773059) B773059
theorem B3488507 : Blo 103782 3488507 := bstep (se 1 (by rfl) ⟨2616380, by rfl⟩ : syracuseStep 3488507 = 5232761) B5232761
theorem B802871 : Blo 103782 802871 := bstep (se 1 (by rfl) ⟨602153, by rfl⟩ : syracuseStep 802871 = 1204307) B1204307
theorem B2775167 : Blo 103782 2775167 := bstep (se 1 (by rfl) ⟨2081375, by rfl⟩ : syracuseStep 2775167 = 4162751) B4162751
theorem B1826887 : Blo 103782 1826887 := bstep (se 1 (by rfl) ⟨1370165, by rfl⟩ : syracuseStep 1826887 = 2740331) B2740331
theorem B7921793 : Blo 103782 7921793 := bstep (se 2 (by rfl) ⟨2970672, by rfl⟩ : syracuseStep 7921793 = 5941345) B5941345
theorem B1828331 : Blo 103782 1828331 := bstep (se 1 (by rfl) ⟨1371248, by rfl⟩ : syracuseStep 1828331 = 2742497) B2742497
theorem B1502059 : Blo 103782 1502059 := bstep (se 1 (by rfl) ⟨1126544, by rfl⟩ : syracuseStep 1502059 = 2253089) B2253089
theorem B227603 : Blo 103782 227603 := bstep (se 1 (by rfl) ⟨170702, by rfl⟩ : syracuseStep 227603 = 341405) B341405
theorem B2098223 : Blo 103782 2098223 := bstep (se 1 (by rfl) ⟨1573667, by rfl⟩ : syracuseStep 2098223 = 3147335) B3147335
theorem B41714941 : Blo 103782 41714941 := bstep (se 3 (by rfl) ⟨7821551, by rfl⟩ : syracuseStep 41714941 = 15643103) B15643103
theorem B525689 : Blo 103782 525689 := bstep (se 2 (by rfl) ⟨197133, by rfl⟩ : syracuseStep 525689 = 394267) B394267
theorem B2002745 : Blo 103782 2002745 := bstep (se 2 (by rfl) ⟨751029, by rfl⟩ : syracuseStep 2002745 = 1502059) B1502059
theorem B5281195 : Blo 103782 5281195 := bstep (se 1 (by rfl) ⟨3960896, by rfl⟩ : syracuseStep 5281195 = 7921793) B7921793
theorem B1218887 : Blo 103782 1218887 := bstep (se 1 (by rfl) ⟨914165, by rfl⟩ : syracuseStep 1218887 = 1828331) B1828331
theorem B535247 : Blo 103782 535247 := bstep (se 1 (by rfl) ⟨401435, by rfl⟩ : syracuseStep 535247 = 802871) B802871
theorem B2435849 : Blo 103782 2435849 := bstep (se 2 (by rfl) ⟨913443, by rfl⟩ : syracuseStep 2435849 = 1826887) B1826887
theorem B539297 : Blo 103782 539297 := bstep (se 2 (by rfl) ⟨202236, by rfl⟩ : syracuseStep 539297 = 404473) B404473
theorem B1850111 : Blo 103782 1850111 := bstep (se 1 (by rfl) ⟨1387583, by rfl⟩ : syracuseStep 1850111 = 2775167) B2775167
theorem B903163 : Blo 103782 903163 := bstep (se 1 (by rfl) ⟨677372, by rfl⟩ : syracuseStep 903163 = 1354745) B1354745
theorem B117247 : Blo 103782 117247 := bstep (se 1 (by rfl) ⟨87935, by rfl⟩ : syracuseStep 117247 = 175871) B175871
theorem B151735 : Blo 103782 151735 := bstep (se 1 (by rfl) ⟨113801, by rfl⟩ : syracuseStep 151735 = 227603) B227603
theorem B13817465 : Blo 103782 13817465 := bstep (se 2 (by rfl) ⟨5181549, by rfl⟩ : syracuseStep 13817465 = 10363099) B10363099
theorem B161327 : Blo 103782 161327 := bstep (se 1 (by rfl) ⟨120995, by rfl⟩ : syracuseStep 161327 = 241991) B241991
theorem B687163 : Blo 103782 687163 := bstep (se 1 (by rfl) ⟨515372, by rfl⟩ : syracuseStep 687163 = 1030745) B1030745
theorem B2325671 : Blo 103782 2325671 := bstep (se 1 (by rfl) ⟨1744253, by rfl⟩ : syracuseStep 2325671 = 3488507) B3488507
theorem B9211643 : Blo 103782 9211643 := bstep (se 1 (by rfl) ⟨6908732, by rfl⟩ : syracuseStep 9211643 = 13817465) B13817465
theorem B202313 : Blo 103782 202313 := bstep (se 2 (by rfl) ⟨75867, by rfl⟩ : syracuseStep 202313 = 151735) B151735
theorem B107551 : Blo 103782 107551 := bstep (se 1 (by rfl) ⟨80663, by rfl⟩ : syracuseStep 107551 = 161327) B161327
theorem B1550447 : Blo 103782 1550447 := bstep (se 1 (by rfl) ⟨1162835, by rfl⟩ : syracuseStep 1550447 = 2325671) B2325671
theorem B55619921 : Blo 103782 55619921 := bstep (se 2 (by rfl) ⟨20857470, by rfl⟩ : syracuseStep 55619921 = 41714941) B41714941
theorem B1623899 : Blo 103782 1623899 := bstep (se 1 (by rfl) ⟨1217924, by rfl⟩ : syracuseStep 1623899 = 2435849) B2435849
theorem B1233407 : Blo 103782 1233407 := bstep (se 1 (by rfl) ⟨925055, by rfl⟩ : syracuseStep 1233407 = 1850111) B1850111
theorem B1398815 : Blo 103782 1398815 := bstep (se 1 (by rfl) ⟨1049111, by rfl⟩ : syracuseStep 1398815 = 2098223) B2098223
theorem B350459 : Blo 103782 350459 := bstep (se 1 (by rfl) ⟨262844, by rfl⟩ : syracuseStep 350459 = 525689) B525689
theorem B1335163 : Blo 103782 1335163 := bstep (se 1 (by rfl) ⟨1001372, by rfl⟩ : syracuseStep 1335163 = 2002745) B2002745
theorem B1204217 : Blo 103782 1204217 := bstep (se 2 (by rfl) ⟨451581, by rfl⟩ : syracuseStep 1204217 = 903163) B903163
theorem B156329 : Blo 103782 156329 := bstep (se 2 (by rfl) ⟨58623, by rfl⟩ : syracuseStep 156329 = 117247) B117247
theorem B812591 : Blo 103782 812591 := bstep (se 1 (by rfl) ⟨609443, by rfl⟩ : syracuseStep 812591 = 1218887) B1218887
theorem B356831 : Blo 103782 356831 := bstep (se 1 (by rfl) ⟨267623, by rfl⟩ : syracuseStep 356831 = 535247) B535247
theorem B7041593 : Blo 103782 7041593 := bstep (se 2 (by rfl) ⟨2640597, by rfl⟩ : syracuseStep 7041593 = 5281195) B5281195
theorem B916217 : Blo 103782 916217 := bstep (se 2 (by rfl) ⟨343581, by rfl⟩ : syracuseStep 916217 = 687163) B687163
theorem B359531 : Blo 103782 359531 := bstep (se 1 (by rfl) ⟨269648, by rfl⟩ : syracuseStep 359531 = 539297) B539297
theorem B822271 : Blo 103782 822271 := bstep (se 1 (by rfl) ⟨616703, by rfl⟩ : syracuseStep 822271 = 1233407) B1233407
theorem B134875 : Blo 103782 134875 := bstep (se 1 (by rfl) ⟨101156, by rfl⟩ : syracuseStep 134875 = 202313) B202313
theorem B233639 : Blo 103782 233639 := bstep (se 1 (by rfl) ⟨175229, by rfl⟩ : syracuseStep 233639 = 350459) B350459
theorem B4330397 : Blo 103782 4330397 := bstep (se 3 (by rfl) ⟨811949, by rfl⟩ : syracuseStep 4330397 = 1623899) B1623899
theorem B104219 : Blo 103782 104219 := bstep (se 1 (by rfl) ⟨78164, by rfl⟩ : syracuseStep 104219 = 156329) B156329
theorem B237887 : Blo 103782 237887 := bstep (se 1 (by rfl) ⟨178415, by rfl⟩ : syracuseStep 237887 = 356831) B356831
theorem B4694395 : Blo 103782 4694395 := bstep (se 1 (by rfl) ⟨3520796, by rfl⟩ : syracuseStep 4694395 = 7041593) B7041593
theorem B239687 : Blo 103782 239687 := bstep (se 1 (by rfl) ⟨179765, by rfl⟩ : syracuseStep 239687 = 359531) B359531
theorem B1780217 : Blo 103782 1780217 := bstep (se 2 (by rfl) ⟨667581, by rfl⟩ : syracuseStep 1780217 = 1335163) B1335163
theorem B6141095 : Blo 103782 6141095 := bstep (se 1 (by rfl) ⟨4605821, by rfl⟩ : syracuseStep 6141095 = 9211643) B9211643
theorem B932543 : Blo 103782 932543 := bstep (se 1 (by rfl) ⟨699407, by rfl⟩ : syracuseStep 932543 = 1398815) B1398815
theorem B802811 : Blo 103782 802811 := bstep (se 1 (by rfl) ⟨602108, by rfl⟩ : syracuseStep 802811 = 1204217) B1204217
theorem B541727 : Blo 103782 541727 := bstep (se 1 (by rfl) ⟨406295, by rfl⟩ : syracuseStep 541727 = 812591) B812591
theorem B1033631 : Blo 103782 1033631 := bstep (se 1 (by rfl) ⟨775223, by rfl⟩ : syracuseStep 1033631 = 1550447) B1550447
theorem B37079947 : Blo 103782 37079947 := bstep (se 1 (by rfl) ⟨27809960, by rfl⟩ : syracuseStep 37079947 = 55619921) B55619921
theorem B610811 : Blo 103782 610811 := bstep (se 1 (by rfl) ⟨458108, by rfl⟩ : syracuseStep 610811 = 916217) B916217
theorem B6259193 : Blo 103782 6259193 := bstep (se 2 (by rfl) ⟨2347197, by rfl⟩ : syracuseStep 6259193 = 4694395) B4694395
theorem B361151 : Blo 103782 361151 := bstep (se 1 (by rfl) ⟨270863, by rfl⟩ : syracuseStep 361151 = 541727) B541727
theorem B689087 : Blo 103782 689087 := bstep (se 1 (by rfl) ⟨516815, by rfl⟩ : syracuseStep 689087 = 1033631) B1033631
theorem B2886931 : Blo 103782 2886931 := bstep (se 1 (by rfl) ⟨2165198, by rfl⟩ : syracuseStep 2886931 = 4330397) B4330397
theorem B197759717 : Blo 103782 197759717 := bstep (se 4 (by rfl) ⟨18539973, by rfl⟩ : syracuseStep 197759717 = 37079947) B37079947
theorem B1186811 : Blo 103782 1186811 := bstep (se 1 (by rfl) ⟨890108, by rfl⟩ : syracuseStep 1186811 = 1780217) B1780217
theorem B535207 : Blo 103782 535207 := bstep (se 1 (by rfl) ⟨401405, by rfl⟩ : syracuseStep 535207 = 802811) B802811
theorem B407207 : Blo 103782 407207 := bstep (se 1 (by rfl) ⟨305405, by rfl⟩ : syracuseStep 407207 = 610811) B610811
theorem B1096361 : Blo 103782 1096361 := bstep (se 2 (by rfl) ⟨411135, by rfl⟩ : syracuseStep 1096361 = 822271) B822271
theorem B179833 : Blo 103782 179833 := bstep (se 2 (by rfl) ⟨67437, by rfl⟩ : syracuseStep 179833 = 134875) B134875
theorem B155759 : Blo 103782 155759 := bstep (se 1 (by rfl) ⟨116819, by rfl⟩ : syracuseStep 155759 = 233639) B233639
theorem B158591 : Blo 103782 158591 := bstep (se 1 (by rfl) ⟨118943, by rfl⟩ : syracuseStep 158591 = 237887) B237887
theorem B159791 : Blo 103782 159791 := bstep (se 1 (by rfl) ⟨119843, by rfl⟩ : syracuseStep 159791 = 239687) B239687
theorem B4094063 : Blo 103782 4094063 := bstep (se 1 (by rfl) ⟨3070547, by rfl⟩ : syracuseStep 4094063 = 6141095) B6141095
theorem B621695 : Blo 103782 621695 := bstep (se 1 (by rfl) ⟨466271, by rfl⟩ : syracuseStep 621695 = 932543) B932543
theorem B459391 : Blo 103782 459391 := bstep (se 1 (by rfl) ⟨344543, by rfl⟩ : syracuseStep 459391 = 689087) B689087
theorem B791207 : Blo 103782 791207 := bstep (se 1 (by rfl) ⟨593405, by rfl⟩ : syracuseStep 791207 = 1186811) B1186811
theorem B103839 : Blo 103782 103839 := bstep (se 1 (by rfl) ⟨77879, by rfl⟩ : syracuseStep 103839 = 155759) B155759
theorem B105727 : Blo 103782 105727 := bstep (se 1 (by rfl) ⟨79295, by rfl⟩ : syracuseStep 105727 = 158591) B158591
theorem B106527 : Blo 103782 106527 := bstep (se 1 (by rfl) ⟨79895, by rfl⟩ : syracuseStep 106527 = 159791) B159791
theorem B271471 : Blo 103782 271471 := bstep (se 1 (by rfl) ⟨203603, by rfl⟩ : syracuseStep 271471 = 407207) B407207
theorem B2729375 : Blo 103782 2729375 := bstep (se 1 (by rfl) ⟨2047031, by rfl⟩ : syracuseStep 2729375 = 4094063) B4094063
theorem B730907 : Blo 103782 730907 := bstep (se 1 (by rfl) ⟨548180, by rfl⟩ : syracuseStep 730907 = 1096361) B1096361
theorem B239777 : Blo 103782 239777 := bstep (se 2 (by rfl) ⟨89916, by rfl⟩ : syracuseStep 239777 = 179833) B179833
theorem B4172795 : Blo 103782 4172795 := bstep (se 1 (by rfl) ⟨3129596, by rfl⟩ : syracuseStep 4172795 = 6259193) B6259193
theorem B240767 : Blo 103782 240767 := bstep (se 1 (by rfl) ⟨180575, by rfl⟩ : syracuseStep 240767 = 361151) B361151
theorem B131839811 : Blo 103782 131839811 := bstep (se 1 (by rfl) ⟨98879858, by rfl⟩ : syracuseStep 131839811 = 197759717) B197759717
theorem B3849241 : Blo 103782 3849241 := bstep (se 2 (by rfl) ⟨1443465, by rfl⟩ : syracuseStep 3849241 = 2886931) B2886931
theorem B414463 : Blo 103782 414463 := bstep (se 1 (by rfl) ⟨310847, by rfl⟩ : syracuseStep 414463 = 621695) B621695
theorem B713609 : Blo 103782 713609 := bstep (se 2 (by rfl) ⟨267603, by rfl⟩ : syracuseStep 713609 = 535207) B535207
theorem B361961 : Blo 103782 361961 := bstep (se 2 (by rfl) ⟨135735, by rfl⟩ : syracuseStep 361961 = 271471) B271471
theorem B527471 : Blo 103782 527471 := bstep (se 1 (by rfl) ⟨395603, by rfl⟩ : syracuseStep 527471 = 791207) B791207
theorem B87893207 : Blo 103782 87893207 := bstep (se 1 (by rfl) ⟨65919905, by rfl⟩ : syracuseStep 87893207 = 131839811) B131839811
theorem B475739 : Blo 103782 475739 := bstep (se 1 (by rfl) ⟨356804, by rfl⟩ : syracuseStep 475739 = 713609) B713609
theorem B1819583 : Blo 103782 1819583 := bstep (se 1 (by rfl) ⟨1364687, by rfl⟩ : syracuseStep 1819583 = 2729375) B2729375
theorem B5132321 : Blo 103782 5132321 := bstep (se 2 (by rfl) ⟨1924620, by rfl⟩ : syracuseStep 5132321 = 3849241) B3849241
theorem B612521 : Blo 103782 612521 := bstep (se 2 (by rfl) ⟨229695, by rfl⟩ : syracuseStep 612521 = 459391) B459391
theorem B552617 : Blo 103782 552617 := bstep (se 2 (by rfl) ⟨207231, by rfl⟩ : syracuseStep 552617 = 414463) B414463
theorem B487271 : Blo 103782 487271 := bstep (se 1 (by rfl) ⟨365453, by rfl⟩ : syracuseStep 487271 = 730907) B730907
theorem B159851 : Blo 103782 159851 := bstep (se 1 (by rfl) ⟨119888, by rfl⟩ : syracuseStep 159851 = 239777) B239777
theorem B2781863 : Blo 103782 2781863 := bstep (se 1 (by rfl) ⟨2086397, by rfl⟩ : syracuseStep 2781863 = 4172795) B4172795
theorem B160511 : Blo 103782 160511 := bstep (se 1 (by rfl) ⟨120383, by rfl⟩ : syracuseStep 160511 = 240767) B240767
theorem B1213055 : Blo 103782 1213055 := bstep (se 1 (by rfl) ⟨909791, by rfl⟩ : syracuseStep 1213055 = 1819583) B1819583
theorem B58595471 : Blo 103782 58595471 := bstep (se 1 (by rfl) ⟨43946603, by rfl⟩ : syracuseStep 58595471 = 87893207) B87893207
theorem B368411 : Blo 103782 368411 := bstep (se 1 (by rfl) ⟨276308, by rfl⟩ : syracuseStep 368411 = 552617) B552617
theorem B106567 : Blo 103782 106567 := bstep (se 1 (by rfl) ⟨79925, by rfl⟩ : syracuseStep 106567 = 159851) B159851
theorem B107007 : Blo 103782 107007 := bstep (se 1 (by rfl) ⟨80255, by rfl⟩ : syracuseStep 107007 = 160511) B160511
theorem B241307 : Blo 103782 241307 := bstep (se 1 (by rfl) ⟨180980, by rfl⟩ : syracuseStep 241307 = 361961) B361961
theorem B3421547 : Blo 103782 3421547 := bstep (se 1 (by rfl) ⟨2566160, by rfl⟩ : syracuseStep 3421547 = 5132321) B5132321
theorem B408347 : Blo 103782 408347 := bstep (se 1 (by rfl) ⟨306260, by rfl⟩ : syracuseStep 408347 = 612521) B612521
theorem B1854575 : Blo 103782 1854575 := bstep (se 1 (by rfl) ⟨1390931, by rfl⟩ : syracuseStep 1854575 = 2781863) B2781863
theorem B317159 : Blo 103782 317159 := bstep (se 1 (by rfl) ⟨237869, by rfl⟩ : syracuseStep 317159 = 475739) B475739
theorem B351647 : Blo 103782 351647 := bstep (se 1 (by rfl) ⟨263735, by rfl⟩ : syracuseStep 351647 = 527471) B527471
theorem B324847 : Blo 103782 324847 := bstep (se 1 (by rfl) ⟨243635, by rfl⟩ : syracuseStep 324847 = 487271) B487271
theorem B39063647 : Blo 103782 39063647 := bstep (se 1 (by rfl) ⟨29297735, by rfl⟩ : syracuseStep 39063647 = 58595471) B58595471
theorem B234431 : Blo 103782 234431 := bstep (se 1 (by rfl) ⟨175823, by rfl⟩ : syracuseStep 234431 = 351647) B351647
theorem B433129 : Blo 103782 433129 := bstep (se 2 (by rfl) ⟨162423, by rfl⟩ : syracuseStep 433129 = 324847) B324847
theorem B272231 : Blo 103782 272231 := bstep (se 1 (by rfl) ⟨204173, by rfl⟩ : syracuseStep 272231 = 408347) B408347
theorem B211439 : Blo 103782 211439 := bstep (se 1 (by rfl) ⟨158579, by rfl⟩ : syracuseStep 211439 = 317159) B317159
theorem B2281031 : Blo 103782 2281031 := bstep (se 1 (by rfl) ⟨1710773, by rfl⟩ : syracuseStep 2281031 = 3421547) B3421547
theorem B808703 : Blo 103782 808703 := bstep (se 1 (by rfl) ⟨606527, by rfl⟩ : syracuseStep 808703 = 1213055) B1213055
theorem B1236383 : Blo 103782 1236383 := bstep (se 1 (by rfl) ⟨927287, by rfl⟩ : syracuseStep 1236383 = 1854575) B1854575
theorem B160871 : Blo 103782 160871 := bstep (se 1 (by rfl) ⟨120653, by rfl⟩ : syracuseStep 160871 = 241307) B241307
theorem B3929717 : Blo 103782 3929717 := bstep (se 5 (by rfl) ⟨184205, by rfl⟩ : syracuseStep 3929717 = 368411) B368411
theorem B824255 : Blo 103782 824255 := bstep (se 1 (by rfl) ⟨618191, by rfl⟩ : syracuseStep 824255 = 1236383) B1236383
theorem B107247 : Blo 103782 107247 := bstep (se 1 (by rfl) ⟨80435, by rfl⟩ : syracuseStep 107247 = 160871) B160871
theorem B140959 : Blo 103782 140959 := bstep (se 1 (by rfl) ⟨105719, by rfl⟩ : syracuseStep 140959 = 211439) B211439
theorem B1520687 : Blo 103782 1520687 := bstep (se 1 (by rfl) ⟨1140515, by rfl⟩ : syracuseStep 1520687 = 2281031) B2281031
theorem B539135 : Blo 103782 539135 := bstep (se 1 (by rfl) ⟨404351, by rfl⟩ : syracuseStep 539135 = 808703) B808703
theorem B181487 : Blo 103782 181487 := bstep (se 1 (by rfl) ⟨136115, by rfl⟩ : syracuseStep 181487 = 272231) B272231
theorem B577505 : Blo 103782 577505 := bstep (se 2 (by rfl) ⟨216564, by rfl⟩ : syracuseStep 577505 = 433129) B433129
theorem B26042431 : Blo 103782 26042431 := bstep (se 1 (by rfl) ⟨19531823, by rfl⟩ : syracuseStep 26042431 = 39063647) B39063647
theorem B156287 : Blo 103782 156287 := bstep (se 1 (by rfl) ⟨117215, by rfl⟩ : syracuseStep 156287 = 234431) B234431
theorem B2619811 : Blo 103782 2619811 := bstep (se 1 (by rfl) ⟨1964858, by rfl⟩ : syracuseStep 2619811 = 3929717) B3929717
theorem B104191 : Blo 103782 104191 := bstep (se 1 (by rfl) ⟨78143, by rfl⟩ : syracuseStep 104191 = 156287) B156287
theorem B3493081 : Blo 103782 3493081 := bstep (se 2 (by rfl) ⟨1309905, by rfl⟩ : syracuseStep 3493081 = 2619811) B2619811
theorem B34723241 : Blo 103782 34723241 := bstep (se 2 (by rfl) ⟨13021215, by rfl⟩ : syracuseStep 34723241 = 26042431) B26042431
theorem B120991 : Blo 103782 120991 := bstep (se 1 (by rfl) ⟨90743, by rfl⟩ : syracuseStep 120991 = 181487) B181487
theorem B385003 : Blo 103782 385003 := bstep (se 1 (by rfl) ⟨288752, by rfl⟩ : syracuseStep 385003 = 577505) B577505
theorem B549503 : Blo 103782 549503 := bstep (se 1 (by rfl) ⟨412127, by rfl⟩ : syracuseStep 549503 = 824255) B824255
theorem B1013791 : Blo 103782 1013791 := bstep (se 1 (by rfl) ⟨760343, by rfl⟩ : syracuseStep 1013791 = 1520687) B1520687
theorem B751781 : Blo 103782 751781 := bstep (se 4 (by rfl) ⟨70479, by rfl⟩ : syracuseStep 751781 = 140959) B140959
theorem B359423 : Blo 103782 359423 := bstep (se 1 (by rfl) ⟨269567, by rfl⟩ : syracuseStep 359423 = 539135) B539135
theorem B4657441 : Blo 103782 4657441 := bstep (se 2 (by rfl) ⟨1746540, by rfl⟩ : syracuseStep 4657441 = 3493081) B3493081
theorem B366335 : Blo 103782 366335 := bstep (se 1 (by rfl) ⟨274751, by rfl⟩ : syracuseStep 366335 = 549503) B549503
theorem B2004749 : Blo 103782 2004749 := bstep (se 3 (by rfl) ⟨375890, by rfl⟩ : syracuseStep 2004749 = 751781) B751781
theorem B1351721 : Blo 103782 1351721 := bstep (se 2 (by rfl) ⟨506895, by rfl⟩ : syracuseStep 1351721 = 1013791) B1013791
theorem B239615 : Blo 103782 239615 := bstep (se 1 (by rfl) ⟨179711, by rfl⟩ : syracuseStep 239615 = 359423) B359423
theorem B23148827 : Blo 103782 23148827 := bstep (se 1 (by rfl) ⟨17361620, by rfl⟩ : syracuseStep 23148827 = 34723241) B34723241
theorem B513337 : Blo 103782 513337 := bstep (se 2 (by rfl) ⟨192501, by rfl⟩ : syracuseStep 513337 = 385003) B385003
theorem B161321 : Blo 103782 161321 := bstep (se 2 (by rfl) ⟨60495, by rfl⟩ : syracuseStep 161321 = 120991) B120991
theorem B107547 : Blo 103782 107547 := bstep (se 1 (by rfl) ⟨80660, by rfl⟩ : syracuseStep 107547 = 161321) B161321
theorem B244223 : Blo 103782 244223 := bstep (se 1 (by rfl) ⟨183167, by rfl⟩ : syracuseStep 244223 = 366335) B366335
theorem B901147 : Blo 103782 901147 := bstep (se 1 (by rfl) ⟨675860, by rfl⟩ : syracuseStep 901147 = 1351721) B1351721
theorem B6209921 : Blo 103782 6209921 := bstep (se 2 (by rfl) ⟨2328720, by rfl⟩ : syracuseStep 6209921 = 4657441) B4657441
theorem B1336499 : Blo 103782 1336499 := bstep (se 1 (by rfl) ⟨1002374, by rfl⟩ : syracuseStep 1336499 = 2004749) B2004749
theorem B159743 : Blo 103782 159743 := bstep (se 1 (by rfl) ⟨119807, by rfl⟩ : syracuseStep 159743 = 239615) B239615
theorem B684449 : Blo 103782 684449 := bstep (se 2 (by rfl) ⟨256668, by rfl⟩ : syracuseStep 684449 = 513337) B513337
theorem B15432551 : Blo 103782 15432551 := bstep (se 1 (by rfl) ⟨11574413, by rfl⟩ : syracuseStep 15432551 = 23148827) B23148827
theorem B890999 : Blo 103782 890999 := bstep (se 1 (by rfl) ⟨668249, by rfl⟩ : syracuseStep 890999 = 1336499) B1336499
theorem B106495 : Blo 103782 106495 := bstep (se 1 (by rfl) ⟨79871, by rfl⟩ : syracuseStep 106495 = 159743) B159743
theorem B4139947 : Blo 103782 4139947 := bstep (se 1 (by rfl) ⟨3104960, by rfl⟩ : syracuseStep 4139947 = 6209921) B6209921
theorem B1201529 : Blo 103782 1201529 := bstep (se 2 (by rfl) ⟨450573, by rfl⟩ : syracuseStep 1201529 = 901147) B901147
theorem B456299 : Blo 103782 456299 := bstep (se 1 (by rfl) ⟨342224, by rfl⟩ : syracuseStep 456299 = 684449) B684449
theorem B162815 : Blo 103782 162815 := bstep (se 1 (by rfl) ⟨122111, by rfl⟩ : syracuseStep 162815 = 244223) B244223
theorem B10288367 : Blo 103782 10288367 := bstep (se 1 (by rfl) ⟨7716275, by rfl⟩ : syracuseStep 10288367 = 15432551) B15432551
theorem B593999 : Blo 103782 593999 := bstep (se 1 (by rfl) ⟨445499, by rfl⟩ : syracuseStep 593999 = 890999) B890999
theorem B434173 : Blo 103782 434173 := bstep (se 3 (by rfl) ⟨81407, by rfl⟩ : syracuseStep 434173 = 162815) B162815
theorem B304199 : Blo 103782 304199 := bstep (se 1 (by rfl) ⟨228149, by rfl⟩ : syracuseStep 304199 = 456299) B456299
theorem B6858911 : Blo 103782 6858911 := bstep (se 1 (by rfl) ⟨5144183, by rfl⟩ : syracuseStep 6858911 = 10288367) B10288367
theorem B801019 : Blo 103782 801019 := bstep (se 1 (by rfl) ⟨600764, by rfl⟩ : syracuseStep 801019 = 1201529) B1201529
theorem B5519929 : Blo 103782 5519929 := bstep (se 2 (by rfl) ⟨2069973, by rfl⟩ : syracuseStep 5519929 = 4139947) B4139947
theorem B395999 : Blo 103782 395999 := bstep (se 1 (by rfl) ⟨296999, by rfl⟩ : syracuseStep 395999 = 593999) B593999
theorem B202799 : Blo 103782 202799 := bstep (se 1 (by rfl) ⟨152099, by rfl⟩ : syracuseStep 202799 = 304199) B304199
theorem B4272101 : Blo 103782 4272101 := bstep (se 4 (by rfl) ⟨400509, by rfl⟩ : syracuseStep 4272101 = 801019) B801019
theorem B4572607 : Blo 103782 4572607 := bstep (se 1 (by rfl) ⟨3429455, by rfl⟩ : syracuseStep 4572607 = 6858911) B6858911
theorem B7359905 : Blo 103782 7359905 := bstep (se 2 (by rfl) ⟨2759964, by rfl⟩ : syracuseStep 7359905 = 5519929) B5519929
theorem B578897 : Blo 103782 578897 := bstep (se 2 (by rfl) ⟨217086, by rfl⟩ : syracuseStep 578897 = 434173) B434173
theorem B263999 : Blo 103782 263999 := bstep (se 1 (by rfl) ⟨197999, by rfl⟩ : syracuseStep 263999 = 395999) B395999
theorem B6096809 : Blo 103782 6096809 := bstep (se 2 (by rfl) ⟨2286303, by rfl⟩ : syracuseStep 6096809 = 4572607) B4572607
theorem B135199 : Blo 103782 135199 := bstep (se 1 (by rfl) ⟨101399, by rfl⟩ : syracuseStep 135199 = 202799) B202799
theorem B4906603 : Blo 103782 4906603 := bstep (se 1 (by rfl) ⟨3679952, by rfl⟩ : syracuseStep 4906603 = 7359905) B7359905
theorem B385931 : Blo 103782 385931 := bstep (se 1 (by rfl) ⟨289448, by rfl⟩ : syracuseStep 385931 = 578897) B578897
theorem B2848067 : Blo 103782 2848067 := bstep (se 1 (by rfl) ⟨2136050, by rfl⟩ : syracuseStep 2848067 = 4272101) B4272101
theorem B16258157 : Blo 103782 16258157 := bstep (se 3 (by rfl) ⟨3048404, by rfl⟩ : syracuseStep 16258157 = 6096809) B6096809
theorem B175999 : Blo 103782 175999 := bstep (se 1 (by rfl) ⟨131999, by rfl⟩ : syracuseStep 175999 = 263999) B263999
theorem B180265 : Blo 103782 180265 := bstep (se 2 (by rfl) ⟨67599, by rfl⟩ : syracuseStep 180265 = 135199) B135199
theorem B6542137 : Blo 103782 6542137 := bstep (se 2 (by rfl) ⟨2453301, by rfl⟩ : syracuseStep 6542137 = 4906603) B4906603
theorem B257287 : Blo 103782 257287 := bstep (se 1 (by rfl) ⟨192965, by rfl⟩ : syracuseStep 257287 = 385931) B385931
theorem B1898711 : Blo 103782 1898711 := bstep (se 1 (by rfl) ⟨1424033, by rfl⟩ : syracuseStep 1898711 = 2848067) B2848067
theorem B21955157 : Blo 103782 21955157 := bstep (se 8 (by rfl) ⟨128643, by rfl⟩ : syracuseStep 21955157 = 257287) B257287
theorem B234665 : Blo 103782 234665 := bstep (se 2 (by rfl) ⟨87999, by rfl⟩ : syracuseStep 234665 = 175999) B175999
theorem B240353 : Blo 103782 240353 := bstep (se 2 (by rfl) ⟨90132, by rfl⟩ : syracuseStep 240353 = 180265) B180265
theorem B1265807 : Blo 103782 1265807 := bstep (se 1 (by rfl) ⟨949355, by rfl⟩ : syracuseStep 1265807 = 1898711) B1898711
theorem B10838771 : Blo 103782 10838771 := bstep (se 1 (by rfl) ⟨8129078, by rfl⟩ : syracuseStep 10838771 = 16258157) B16258157
theorem B34891397 : Blo 103782 34891397 := bstep (se 4 (by rfl) ⟨3271068, by rfl⟩ : syracuseStep 34891397 = 6542137) B6542137
theorem B7225847 : Blo 103782 7225847 := bstep (se 1 (by rfl) ⟨5419385, by rfl⟩ : syracuseStep 7225847 = 10838771) B10838771
theorem B14636771 : Blo 103782 14636771 := bstep (se 1 (by rfl) ⟨10977578, by rfl⟩ : syracuseStep 14636771 = 21955157) B21955157
theorem B843871 : Blo 103782 843871 := bstep (se 1 (by rfl) ⟨632903, by rfl⟩ : syracuseStep 843871 = 1265807) B1265807
theorem B156443 : Blo 103782 156443 := bstep (se 1 (by rfl) ⟨117332, by rfl⟩ : syracuseStep 156443 = 234665) B234665
theorem B23260931 : Blo 103782 23260931 := bstep (se 1 (by rfl) ⟨17445698, by rfl⟩ : syracuseStep 23260931 = 34891397) B34891397
theorem B160235 : Blo 103782 160235 := bstep (se 1 (by rfl) ⟨120176, by rfl⟩ : syracuseStep 160235 = 240353) B240353
theorem B4817231 : Blo 103782 4817231 := bstep (se 1 (by rfl) ⟨3612923, by rfl⟩ : syracuseStep 4817231 = 7225847) B7225847
theorem B104295 : Blo 103782 104295 := bstep (se 1 (by rfl) ⟨78221, by rfl⟩ : syracuseStep 104295 = 156443) B156443
theorem B15507287 : Blo 103782 15507287 := bstep (se 1 (by rfl) ⟨11630465, by rfl⟩ : syracuseStep 15507287 = 23260931) B23260931
theorem B106823 : Blo 103782 106823 := bstep (se 1 (by rfl) ⟨80117, by rfl⟩ : syracuseStep 106823 = 160235) B160235
theorem B1125161 : Blo 103782 1125161 := bstep (se 2 (by rfl) ⟨421935, by rfl⟩ : syracuseStep 1125161 = 843871) B843871
theorem B9757847 : Blo 103782 9757847 := bstep (se 1 (by rfl) ⟨7318385, by rfl⟩ : syracuseStep 9757847 = 14636771) B14636771
theorem B3211487 : Blo 103782 3211487 := bstep (se 1 (by rfl) ⟨2408615, by rfl⟩ : syracuseStep 3211487 = 4817231) B4817231
theorem B10338191 : Blo 103782 10338191 := bstep (se 1 (by rfl) ⟨7753643, by rfl⟩ : syracuseStep 10338191 = 15507287) B15507287
theorem B6505231 : Blo 103782 6505231 := bstep (se 1 (by rfl) ⟨4878923, by rfl⟩ : syracuseStep 6505231 = 9757847) B9757847
theorem B750107 : Blo 103782 750107 := bstep (se 1 (by rfl) ⟨562580, by rfl⟩ : syracuseStep 750107 = 1125161) B1125161
theorem B2000285 : Blo 103782 2000285 := bstep (se 3 (by rfl) ⟨375053, by rfl⟩ : syracuseStep 2000285 = 750107) B750107
theorem B6892127 : Blo 103782 6892127 := bstep (se 1 (by rfl) ⟨5169095, by rfl⟩ : syracuseStep 6892127 = 10338191) B10338191
theorem B2140991 : Blo 103782 2140991 := bstep (se 1 (by rfl) ⟨1605743, by rfl⟩ : syracuseStep 2140991 = 3211487) B3211487
theorem B8673641 : Blo 103782 8673641 := bstep (se 2 (by rfl) ⟨3252615, by rfl⟩ : syracuseStep 8673641 = 6505231) B6505231
theorem B4594751 : Blo 103782 4594751 := bstep (se 1 (by rfl) ⟨3446063, by rfl⟩ : syracuseStep 4594751 = 6892127) B6892127
theorem B5782427 : Blo 103782 5782427 := bstep (se 1 (by rfl) ⟨4336820, by rfl⟩ : syracuseStep 5782427 = 8673641) B8673641
theorem B1427327 : Blo 103782 1427327 := bstep (se 1 (by rfl) ⟨1070495, by rfl⟩ : syracuseStep 1427327 = 2140991) B2140991
theorem B1333523 : Blo 103782 1333523 := bstep (se 1 (by rfl) ⟨1000142, by rfl⟩ : syracuseStep 1333523 = 2000285) B2000285
theorem B951551 : Blo 103782 951551 := bstep (se 1 (by rfl) ⟨713663, by rfl⟩ : syracuseStep 951551 = 1427327) B1427327
theorem B889015 : Blo 103782 889015 := bstep (se 1 (by rfl) ⟨666761, by rfl⟩ : syracuseStep 889015 = 1333523) B1333523
theorem B3063167 : Blo 103782 3063167 := bstep (se 1 (by rfl) ⟨2297375, by rfl⟩ : syracuseStep 3063167 = 4594751) B4594751
theorem B3854951 : Blo 103782 3854951 := bstep (se 1 (by rfl) ⟨2891213, by rfl⟩ : syracuseStep 3854951 = 5782427) B5782427
theorem B1185353 : Blo 103782 1185353 := bstep (se 2 (by rfl) ⟨444507, by rfl⟩ : syracuseStep 1185353 = 889015) B889015
theorem B2042111 : Blo 103782 2042111 := bstep (se 1 (by rfl) ⟨1531583, by rfl⟩ : syracuseStep 2042111 = 3063167) B3063167
theorem B634367 : Blo 103782 634367 := bstep (se 1 (by rfl) ⟨475775, by rfl⟩ : syracuseStep 634367 = 951551) B951551
theorem B2569967 : Blo 103782 2569967 := bstep (se 1 (by rfl) ⟨1927475, by rfl⟩ : syracuseStep 2569967 = 3854951) B3854951
theorem B790235 : Blo 103782 790235 := bstep (se 1 (by rfl) ⟨592676, by rfl⟩ : syracuseStep 790235 = 1185353) B1185353
theorem B1713311 : Blo 103782 1713311 := bstep (se 1 (by rfl) ⟨1284983, by rfl⟩ : syracuseStep 1713311 = 2569967) B2569967
theorem B1361407 : Blo 103782 1361407 := bstep (se 1 (by rfl) ⟨1021055, by rfl⟩ : syracuseStep 1361407 = 2042111) B2042111
theorem B422911 : Blo 103782 422911 := bstep (se 1 (by rfl) ⟨317183, by rfl⟩ : syracuseStep 422911 = 634367) B634367
theorem B526823 : Blo 103782 526823 := bstep (se 1 (by rfl) ⟨395117, by rfl⟩ : syracuseStep 526823 = 790235) B790235
theorem B563881 : Blo 103782 563881 := bstep (se 2 (by rfl) ⟨211455, by rfl⟩ : syracuseStep 563881 = 422911) B422911
theorem B1815209 : Blo 103782 1815209 := bstep (se 2 (by rfl) ⟨680703, by rfl⟩ : syracuseStep 1815209 = 1361407) B1361407
theorem B1142207 : Blo 103782 1142207 := bstep (se 1 (by rfl) ⟨856655, by rfl⟩ : syracuseStep 1142207 = 1713311) B1713311
theorem B761471 : Blo 103782 761471 := bstep (se 1 (by rfl) ⟨571103, by rfl⟩ : syracuseStep 761471 = 1142207) B1142207
theorem B351215 : Blo 103782 351215 := bstep (se 1 (by rfl) ⟨263411, by rfl⟩ : syracuseStep 351215 = 526823) B526823
theorem B1210139 : Blo 103782 1210139 := bstep (se 1 (by rfl) ⟨907604, by rfl⟩ : syracuseStep 1210139 = 1815209) B1815209
theorem B751841 : Blo 103782 751841 := bstep (se 2 (by rfl) ⟨281940, by rfl⟩ : syracuseStep 751841 = 563881) B563881
theorem B234143 : Blo 103782 234143 := bstep (se 1 (by rfl) ⟨175607, by rfl⟩ : syracuseStep 234143 = 351215) B351215
theorem B501227 : Blo 103782 501227 := bstep (se 1 (by rfl) ⟨375920, by rfl⟩ : syracuseStep 501227 = 751841) B751841
theorem B507647 : Blo 103782 507647 := bstep (se 1 (by rfl) ⟨380735, by rfl⟩ : syracuseStep 507647 = 761471) B761471
theorem B806759 : Blo 103782 806759 := bstep (se 1 (by rfl) ⟨605069, by rfl⟩ : syracuseStep 806759 = 1210139) B1210139
theorem B334151 : Blo 103782 334151 := bstep (se 1 (by rfl) ⟨250613, by rfl⟩ : syracuseStep 334151 = 501227) B501227
theorem B338431 : Blo 103782 338431 := bstep (se 1 (by rfl) ⟨253823, by rfl⟩ : syracuseStep 338431 = 507647) B507647
theorem B537839 : Blo 103782 537839 := bstep (se 1 (by rfl) ⟨403379, by rfl⟩ : syracuseStep 537839 = 806759) B806759
theorem B156095 : Blo 103782 156095 := bstep (se 1 (by rfl) ⟨117071, by rfl⟩ : syracuseStep 156095 = 234143) B234143
theorem B104063 : Blo 103782 104063 := bstep (se 1 (by rfl) ⟨78047, by rfl⟩ : syracuseStep 104063 = 156095) B156095
theorem B451241 : Blo 103782 451241 := bstep (se 2 (by rfl) ⟨169215, by rfl⟩ : syracuseStep 451241 = 338431) B338431
theorem B222767 : Blo 103782 222767 := bstep (se 1 (by rfl) ⟨167075, by rfl⟩ : syracuseStep 222767 = 334151) B334151
theorem B358559 : Blo 103782 358559 := bstep (se 1 (by rfl) ⟨268919, by rfl⟩ : syracuseStep 358559 = 537839) B537839
theorem B300827 : Blo 103782 300827 := bstep (se 1 (by rfl) ⟨225620, by rfl⟩ : syracuseStep 300827 = 451241) B451241
theorem B239039 : Blo 103782 239039 := bstep (se 1 (by rfl) ⟨179279, by rfl⟩ : syracuseStep 239039 = 358559) B358559
theorem B148511 : Blo 103782 148511 := bstep (se 1 (by rfl) ⟨111383, by rfl⟩ : syracuseStep 148511 = 222767) B222767
theorem B396029 : Blo 103782 396029 := bstep (se 3 (by rfl) ⟨74255, by rfl⟩ : syracuseStep 396029 = 148511) B148511
theorem B200551 : Blo 103782 200551 := bstep (se 1 (by rfl) ⟨150413, by rfl⟩ : syracuseStep 200551 = 300827) B300827
theorem B159359 : Blo 103782 159359 := bstep (se 1 (by rfl) ⟨119519, by rfl⟩ : syracuseStep 159359 = 239039) B239039
theorem B264019 : Blo 103782 264019 := bstep (se 1 (by rfl) ⟨198014, by rfl⟩ : syracuseStep 264019 = 396029) B396029
theorem B267401 : Blo 103782 267401 := bstep (se 2 (by rfl) ⟨100275, by rfl⟩ : syracuseStep 267401 = 200551) B200551
theorem B106239 : Blo 103782 106239 := bstep (se 1 (by rfl) ⟨79679, by rfl⟩ : syracuseStep 106239 = 159359) B159359
theorem B178267 : Blo 103782 178267 := bstep (se 1 (by rfl) ⟨133700, by rfl⟩ : syracuseStep 178267 = 267401) B267401
theorem B352025 : Blo 103782 352025 := bstep (se 2 (by rfl) ⟨132009, by rfl⟩ : syracuseStep 352025 = 264019) B264019
theorem B234683 : Blo 103782 234683 := bstep (se 1 (by rfl) ⟨176012, by rfl⟩ : syracuseStep 234683 = 352025) B352025
theorem B237689 : Blo 103782 237689 := bstep (se 2 (by rfl) ⟨89133, by rfl⟩ : syracuseStep 237689 = 178267) B178267
theorem B156455 : Blo 103782 156455 := bstep (se 1 (by rfl) ⟨117341, by rfl⟩ : syracuseStep 156455 = 234683) B234683
theorem B158459 : Blo 103782 158459 := bstep (se 1 (by rfl) ⟨118844, by rfl⟩ : syracuseStep 158459 = 237689) B237689
theorem B104303 : Blo 103782 104303 := bstep (se 1 (by rfl) ⟨78227, by rfl⟩ : syracuseStep 104303 = 156455) B156455
theorem B105639 : Blo 103782 105639 := bstep (se 1 (by rfl) ⟨79229, by rfl⟩ : syracuseStep 105639 = 158459) B158459

theorem C0 (j : ℕ) (h1 : 25945 ≤ j) (h2 : j ≤ 26644) : Blo 103782 (4 * j + 3) := by
  interval_cases j
  · exact B103783
  · exact B103787
  · exact B103791
  · exact B103795
  · exact B103799
  · exact B103803
  · exact B103807
  · exact B103811
  · exact B103815
  · exact B103819
  · exact B103823
  · exact B103827
  · exact B103831
  · exact B103835
  · exact B103839
  · exact B103843
  · exact B103847
  · exact B103851
  · exact B103855
  · exact B103859
  · exact B103863
  · exact B103867
  · exact B103871
  · exact B103875
  · exact B103879
  · exact B103883
  · exact B103887
  · exact B103891
  · exact B103895
  · exact B103899
  · exact B103903
  · exact B103907
  · exact B103911
  · exact B103915
  · exact B103919
  · exact B103923
  · exact B103927
  · exact B103931
  · exact B103935
  · exact B103939
  · exact B103943
  · exact B103947
  · exact B103951
  · exact B103955
  · exact B103959
  · exact B103963
  · exact B103967
  · exact B103971
  · exact B103975
  · exact B103979
  · exact B103983
  · exact B103987
  · exact B103991
  · exact B103995
  · exact B103999
  · exact B104003
  · exact B104007
  · exact B104011
  · exact B104015
  · exact B104019
  · exact B104023
  · exact B104027
  · exact B104031
  · exact B104035
  · exact B104039
  · exact B104043
  · exact B104047
  · exact B104051
  · exact B104055
  · exact B104059
  · exact B104063
  · exact B104067
  · exact B104071
  · exact B104075
  · exact B104079
  · exact B104083
  · exact B104087
  · exact B104091
  · exact B104095
  · exact B104099
  · exact B104103
  · exact B104107
  · exact B104111
  · exact B104115
  · exact B104119
  · exact B104123
  · exact B104127
  · exact B104131
  · exact B104135
  · exact B104139
  · exact B104143
  · exact B104147
  · exact B104151
  · exact B104155
  · exact B104159
  · exact B104163
  · exact B104167
  · exact B104171
  · exact B104175
  · exact B104179
  · exact B104183
  · exact B104187
  · exact B104191
  · exact B104195
  · exact B104199
  · exact B104203
  · exact B104207
  · exact B104211
  · exact B104215
  · exact B104219
  · exact B104223
  · exact B104227
  · exact B104231
  · exact B104235
  · exact B104239
  · exact B104243
  · exact B104247
  · exact B104251
  · exact B104255
  · exact B104259
  · exact B104263
  · exact B104267
  · exact B104271
  · exact B104275
  · exact B104279
  · exact B104283
  · exact B104287
  · exact B104291
  · exact B104295
  · exact B104299
  · exact B104303
  · exact B104307
  · exact B104311
  · exact B104315
  · exact B104319
  · exact B104323
  · exact B104327
  · exact B104331
  · exact B104335
  · exact B104339
  · exact B104343
  · exact B104347
  · exact B104351
  · exact B104355
  · exact B104359
  · exact B104363
  · exact B104367
  · exact B104371
  · exact B104375
  · exact B104379
  · exact B104383
  · exact B104387
  · exact B104391
  · exact B104395
  · exact B104399
  · exact B104403
  · exact B104407
  · exact B104411
  · exact B104415
  · exact B104419
  · exact B104423
  · exact B104427
  · exact B104431
  · exact B104435
  · exact B104439
  · exact B104443
  · exact B104447
  · exact B104451
  · exact B104455
  · exact B104459
  · exact B104463
  · exact B104467
  · exact B104471
  · exact B104475
  · exact B104479
  · exact B104483
  · exact B104487
  · exact B104491
  · exact B104495
  · exact B104499
  · exact B104503
  · exact B104507
  · exact B104511
  · exact B104515
  · exact B104519
  · exact B104523
  · exact B104527
  · exact B104531
  · exact B104535
  · exact B104539
  · exact B104543
  · exact B104547
  · exact B104551
  · exact B104555
  · exact B104559
  · exact B104563
  · exact B104567
  · exact B104571
  · exact B104575
  · exact B104579
  · exact B104583
  · exact B104587
  · exact B104591
  · exact B104595
  · exact B104599
  · exact B104603
  · exact B104607
  · exact B104611
  · exact B104615
  · exact B104619
  · exact B104623
  · exact B104627
  · exact B104631
  · exact B104635
  · exact B104639
  · exact B104643
  · exact B104647
  · exact B104651
  · exact B104655
  · exact B104659
  · exact B104663
  · exact B104667
  · exact B104671
  · exact B104675
  · exact B104679
  · exact B104683
  · exact B104687
  · exact B104691
  · exact B104695
  · exact B104699
  · exact B104703
  · exact B104707
  · exact B104711
  · exact B104715
  · exact B104719
  · exact B104723
  · exact B104727
  · exact B104731
  · exact B104735
  · exact B104739
  · exact B104743
  · exact B104747
  · exact B104751
  · exact B104755
  · exact B104759
  · exact B104763
  · exact B104767
  · exact B104771
  · exact B104775
  · exact B104779
  · exact B104783
  · exact B104787
  · exact B104791
  · exact B104795
  · exact B104799
  · exact B104803
  · exact B104807
  · exact B104811
  · exact B104815
  · exact B104819
  · exact B104823
  · exact B104827
  · exact B104831
  · exact B104835
  · exact B104839
  · exact B104843
  · exact B104847
  · exact B104851
  · exact B104855
  · exact B104859
  · exact B104863
  · exact B104867
  · exact B104871
  · exact B104875
  · exact B104879
  · exact B104883
  · exact B104887
  · exact B104891
  · exact B104895
  · exact B104899
  · exact B104903
  · exact B104907
  · exact B104911
  · exact B104915
  · exact B104919
  · exact B104923
  · exact B104927
  · exact B104931
  · exact B104935
  · exact B104939
  · exact B104943
  · exact B104947
  · exact B104951
  · exact B104955
  · exact B104959
  · exact B104963
  · exact B104967
  · exact B104971
  · exact B104975
  · exact B104979
  · exact B104983
  · exact B104987
  · exact B104991
  · exact B104995
  · exact B104999
  · exact B105003
  · exact B105007
  · exact B105011
  · exact B105015
  · exact B105019
  · exact B105023
  · exact B105027
  · exact B105031
  · exact B105035
  · exact B105039
  · exact B105043
  · exact B105047
  · exact B105051
  · exact B105055
  · exact B105059
  · exact B105063
  · exact B105067
  · exact B105071
  · exact B105075
  · exact B105079
  · exact B105083
  · exact B105087
  · exact B105091
  · exact B105095
  · exact B105099
  · exact B105103
  · exact B105107
  · exact B105111
  · exact B105115
  · exact B105119
  · exact B105123
  · exact B105127
  · exact B105131
  · exact B105135
  · exact B105139
  · exact B105143
  · exact B105147
  · exact B105151
  · exact B105155
  · exact B105159
  · exact B105163
  · exact B105167
  · exact B105171
  · exact B105175
  · exact B105179
  · exact B105183
  · exact B105187
  · exact B105191
  · exact B105195
  · exact B105199
  · exact B105203
  · exact B105207
  · exact B105211
  · exact B105215
  · exact B105219
  · exact B105223
  · exact B105227
  · exact B105231
  · exact B105235
  · exact B105239
  · exact B105243
  · exact B105247
  · exact B105251
  · exact B105255
  · exact B105259
  · exact B105263
  · exact B105267
  · exact B105271
  · exact B105275
  · exact B105279
  · exact B105283
  · exact B105287
  · exact B105291
  · exact B105295
  · exact B105299
  · exact B105303
  · exact B105307
  · exact B105311
  · exact B105315
  · exact B105319
  · exact B105323
  · exact B105327
  · exact B105331
  · exact B105335
  · exact B105339
  · exact B105343
  · exact B105347
  · exact B105351
  · exact B105355
  · exact B105359
  · exact B105363
  · exact B105367
  · exact B105371
  · exact B105375
  · exact B105379
  · exact B105383
  · exact B105387
  · exact B105391
  · exact B105395
  · exact B105399
  · exact B105403
  · exact B105407
  · exact B105411
  · exact B105415
  · exact B105419
  · exact B105423
  · exact B105427
  · exact B105431
  · exact B105435
  · exact B105439
  · exact B105443
  · exact B105447
  · exact B105451
  · exact B105455
  · exact B105459
  · exact B105463
  · exact B105467
  · exact B105471
  · exact B105475
  · exact B105479
  · exact B105483
  · exact B105487
  · exact B105491
  · exact B105495
  · exact B105499
  · exact B105503
  · exact B105507
  · exact B105511
  · exact B105515
  · exact B105519
  · exact B105523
  · exact B105527
  · exact B105531
  · exact B105535
  · exact B105539
  · exact B105543
  · exact B105547
  · exact B105551
  · exact B105555
  · exact B105559
  · exact B105563
  · exact B105567
  · exact B105571
  · exact B105575
  · exact B105579
  · exact B105583
  · exact B105587
  · exact B105591
  · exact B105595
  · exact B105599
  · exact B105603
  · exact B105607
  · exact B105611
  · exact B105615
  · exact B105619
  · exact B105623
  · exact B105627
  · exact B105631
  · exact B105635
  · exact B105639
  · exact B105643
  · exact B105647
  · exact B105651
  · exact B105655
  · exact B105659
  · exact B105663
  · exact B105667
  · exact B105671
  · exact B105675
  · exact B105679
  · exact B105683
  · exact B105687
  · exact B105691
  · exact B105695
  · exact B105699
  · exact B105703
  · exact B105707
  · exact B105711
  · exact B105715
  · exact B105719
  · exact B105723
  · exact B105727
  · exact B105731
  · exact B105735
  · exact B105739
  · exact B105743
  · exact B105747
  · exact B105751
  · exact B105755
  · exact B105759
  · exact B105763
  · exact B105767
  · exact B105771
  · exact B105775
  · exact B105779
  · exact B105783
  · exact B105787
  · exact B105791
  · exact B105795
  · exact B105799
  · exact B105803
  · exact B105807
  · exact B105811
  · exact B105815
  · exact B105819
  · exact B105823
  · exact B105827
  · exact B105831
  · exact B105835
  · exact B105839
  · exact B105843
  · exact B105847
  · exact B105851
  · exact B105855
  · exact B105859
  · exact B105863
  · exact B105867
  · exact B105871
  · exact B105875
  · exact B105879
  · exact B105883
  · exact B105887
  · exact B105891
  · exact B105895
  · exact B105899
  · exact B105903
  · exact B105907
  · exact B105911
  · exact B105915
  · exact B105919
  · exact B105923
  · exact B105927
  · exact B105931
  · exact B105935
  · exact B105939
  · exact B105943
  · exact B105947
  · exact B105951
  · exact B105955
  · exact B105959
  · exact B105963
  · exact B105967
  · exact B105971
  · exact B105975
  · exact B105979
  · exact B105983
  · exact B105987
  · exact B105991
  · exact B105995
  · exact B105999
  · exact B106003
  · exact B106007
  · exact B106011
  · exact B106015
  · exact B106019
  · exact B106023
  · exact B106027
  · exact B106031
  · exact B106035
  · exact B106039
  · exact B106043
  · exact B106047
  · exact B106051
  · exact B106055
  · exact B106059
  · exact B106063
  · exact B106067
  · exact B106071
  · exact B106075
  · exact B106079
  · exact B106083
  · exact B106087
  · exact B106091
  · exact B106095
  · exact B106099
  · exact B106103
  · exact B106107
  · exact B106111
  · exact B106115
  · exact B106119
  · exact B106123
  · exact B106127
  · exact B106131
  · exact B106135
  · exact B106139
  · exact B106143
  · exact B106147
  · exact B106151
  · exact B106155
  · exact B106159
  · exact B106163
  · exact B106167
  · exact B106171
  · exact B106175
  · exact B106179
  · exact B106183
  · exact B106187
  · exact B106191
  · exact B106195
  · exact B106199
  · exact B106203
  · exact B106207
  · exact B106211
  · exact B106215
  · exact B106219
  · exact B106223
  · exact B106227
  · exact B106231
  · exact B106235
  · exact B106239
  · exact B106243
  · exact B106247
  · exact B106251
  · exact B106255
  · exact B106259
  · exact B106263
  · exact B106267
  · exact B106271
  · exact B106275
  · exact B106279
  · exact B106283
  · exact B106287
  · exact B106291
  · exact B106295
  · exact B106299
  · exact B106303
  · exact B106307
  · exact B106311
  · exact B106315
  · exact B106319
  · exact B106323
  · exact B106327
  · exact B106331
  · exact B106335
  · exact B106339
  · exact B106343
  · exact B106347
  · exact B106351
  · exact B106355
  · exact B106359
  · exact B106363
  · exact B106367
  · exact B106371
  · exact B106375
  · exact B106379
  · exact B106383
  · exact B106387
  · exact B106391
  · exact B106395
  · exact B106399
  · exact B106403
  · exact B106407
  · exact B106411
  · exact B106415
  · exact B106419
  · exact B106423
  · exact B106427
  · exact B106431
  · exact B106435
  · exact B106439
  · exact B106443
  · exact B106447
  · exact B106451
  · exact B106455
  · exact B106459
  · exact B106463
  · exact B106467
  · exact B106471
  · exact B106475
  · exact B106479
  · exact B106483
  · exact B106487
  · exact B106491
  · exact B106495
  · exact B106499
  · exact B106503
  · exact B106507
  · exact B106511
  · exact B106515
  · exact B106519
  · exact B106523
  · exact B106527
  · exact B106531
  · exact B106535
  · exact B106539
  · exact B106543
  · exact B106547
  · exact B106551
  · exact B106555
  · exact B106559
  · exact B106563
  · exact B106567
  · exact B106571
  · exact B106575
  · exact B106579

theorem C1 (j : ℕ) (h1 : 26645 ≤ j) (h2 : j ≤ 26944) : Blo 103782 (4 * j + 3) := by
  interval_cases j
  · exact B106583
  · exact B106587
  · exact B106591
  · exact B106595
  · exact B106599
  · exact B106603
  · exact B106607
  · exact B106611
  · exact B106615
  · exact B106619
  · exact B106623
  · exact B106627
  · exact B106631
  · exact B106635
  · exact B106639
  · exact B106643
  · exact B106647
  · exact B106651
  · exact B106655
  · exact B106659
  · exact B106663
  · exact B106667
  · exact B106671
  · exact B106675
  · exact B106679
  · exact B106683
  · exact B106687
  · exact B106691
  · exact B106695
  · exact B106699
  · exact B106703
  · exact B106707
  · exact B106711
  · exact B106715
  · exact B106719
  · exact B106723
  · exact B106727
  · exact B106731
  · exact B106735
  · exact B106739
  · exact B106743
  · exact B106747
  · exact B106751
  · exact B106755
  · exact B106759
  · exact B106763
  · exact B106767
  · exact B106771
  · exact B106775
  · exact B106779
  · exact B106783
  · exact B106787
  · exact B106791
  · exact B106795
  · exact B106799
  · exact B106803
  · exact B106807
  · exact B106811
  · exact B106815
  · exact B106819
  · exact B106823
  · exact B106827
  · exact B106831
  · exact B106835
  · exact B106839
  · exact B106843
  · exact B106847
  · exact B106851
  · exact B106855
  · exact B106859
  · exact B106863
  · exact B106867
  · exact B106871
  · exact B106875
  · exact B106879
  · exact B106883
  · exact B106887
  · exact B106891
  · exact B106895
  · exact B106899
  · exact B106903
  · exact B106907
  · exact B106911
  · exact B106915
  · exact B106919
  · exact B106923
  · exact B106927
  · exact B106931
  · exact B106935
  · exact B106939
  · exact B106943
  · exact B106947
  · exact B106951
  · exact B106955
  · exact B106959
  · exact B106963
  · exact B106967
  · exact B106971
  · exact B106975
  · exact B106979
  · exact B106983
  · exact B106987
  · exact B106991
  · exact B106995
  · exact B106999
  · exact B107003
  · exact B107007
  · exact B107011
  · exact B107015
  · exact B107019
  · exact B107023
  · exact B107027
  · exact B107031
  · exact B107035
  · exact B107039
  · exact B107043
  · exact B107047
  · exact B107051
  · exact B107055
  · exact B107059
  · exact B107063
  · exact B107067
  · exact B107071
  · exact B107075
  · exact B107079
  · exact B107083
  · exact B107087
  · exact B107091
  · exact B107095
  · exact B107099
  · exact B107103
  · exact B107107
  · exact B107111
  · exact B107115
  · exact B107119
  · exact B107123
  · exact B107127
  · exact B107131
  · exact B107135
  · exact B107139
  · exact B107143
  · exact B107147
  · exact B107151
  · exact B107155
  · exact B107159
  · exact B107163
  · exact B107167
  · exact B107171
  · exact B107175
  · exact B107179
  · exact B107183
  · exact B107187
  · exact B107191
  · exact B107195
  · exact B107199
  · exact B107203
  · exact B107207
  · exact B107211
  · exact B107215
  · exact B107219
  · exact B107223
  · exact B107227
  · exact B107231
  · exact B107235
  · exact B107239
  · exact B107243
  · exact B107247
  · exact B107251
  · exact B107255
  · exact B107259
  · exact B107263
  · exact B107267
  · exact B107271
  · exact B107275
  · exact B107279
  · exact B107283
  · exact B107287
  · exact B107291
  · exact B107295
  · exact B107299
  · exact B107303
  · exact B107307
  · exact B107311
  · exact B107315
  · exact B107319
  · exact B107323
  · exact B107327
  · exact B107331
  · exact B107335
  · exact B107339
  · exact B107343
  · exact B107347
  · exact B107351
  · exact B107355
  · exact B107359
  · exact B107363
  · exact B107367
  · exact B107371
  · exact B107375
  · exact B107379
  · exact B107383
  · exact B107387
  · exact B107391
  · exact B107395
  · exact B107399
  · exact B107403
  · exact B107407
  · exact B107411
  · exact B107415
  · exact B107419
  · exact B107423
  · exact B107427
  · exact B107431
  · exact B107435
  · exact B107439
  · exact B107443
  · exact B107447
  · exact B107451
  · exact B107455
  · exact B107459
  · exact B107463
  · exact B107467
  · exact B107471
  · exact B107475
  · exact B107479
  · exact B107483
  · exact B107487
  · exact B107491
  · exact B107495
  · exact B107499
  · exact B107503
  · exact B107507
  · exact B107511
  · exact B107515
  · exact B107519
  · exact B107523
  · exact B107527
  · exact B107531
  · exact B107535
  · exact B107539
  · exact B107543
  · exact B107547
  · exact B107551
  · exact B107555
  · exact B107559
  · exact B107563
  · exact B107567
  · exact B107571
  · exact B107575
  · exact B107579
  · exact B107583
  · exact B107587
  · exact B107591
  · exact B107595
  · exact B107599
  · exact B107603
  · exact B107607
  · exact B107611
  · exact B107615
  · exact B107619
  · exact B107623
  · exact B107627
  · exact B107631
  · exact B107635
  · exact B107639
  · exact B107643
  · exact B107647
  · exact B107651
  · exact B107655
  · exact B107659
  · exact B107663
  · exact B107667
  · exact B107671
  · exact B107675
  · exact B107679
  · exact B107683
  · exact B107687
  · exact B107691
  · exact B107695
  · exact B107699
  · exact B107703
  · exact B107707
  · exact B107711
  · exact B107715
  · exact B107719
  · exact B107723
  · exact B107727
  · exact B107731
  · exact B107735
  · exact B107739
  · exact B107743
  · exact B107747
  · exact B107751
  · exact B107755
  · exact B107759
  · exact B107763
  · exact B107767
  · exact B107771
  · exact B107775
  · exact B107779

theorem solution (m : ℕ) (hlo : 103782 ≤ m) (hhi : m ≤ 107782) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 25945 ≤ j := by omega
    have hj2 : j ≤ 26944 := by omega
    have hb : Blo 103782 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 26645 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
