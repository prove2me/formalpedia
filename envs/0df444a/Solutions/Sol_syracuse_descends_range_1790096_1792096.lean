-- Prove2me | solution 1 for syracuse_descends_range_1790096_1792096
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:47:12.466862+00:00
-- url     : https://prove2.me/submissions/0df8432e-e293-4484-b1f2-79790d4fef62

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


theorem B4030469 : Blo 1790096 4030469 := bbase (se 4 (by rfl) ⟨377856, by rfl⟩ : syracuseStep 4030469 = 755713) (by norm_num)
theorem B2686997 : Blo 1790096 2686997 := bbase (se 6 (by rfl) ⟨62976, by rfl⟩ : syracuseStep 2686997 = 125953) (by norm_num)
theorem B2015257 : Blo 1790096 2015257 := bbase (se 2 (by rfl) ⟨755721, by rfl⟩ : syracuseStep 2015257 = 1511443) (by norm_num)
theorem B2687021 : Blo 1790096 2687021 := bbase (se 3 (by rfl) ⟨503816, by rfl⟩ : syracuseStep 2687021 = 1007633) (by norm_num)
theorem B3227701 : Blo 1790096 3227701 := bbase (se 5 (by rfl) ⟨151298, by rfl⟩ : syracuseStep 3227701 = 302597) (by norm_num)
theorem B9068597 : Blo 1790096 9068597 := bbase (se 5 (by rfl) ⟨425090, by rfl⟩ : syracuseStep 9068597 = 850181) (by norm_num)
theorem B2015293 : Blo 1790096 2015293 := bbase (se 3 (by rfl) ⟨377867, by rfl⟩ : syracuseStep 2015293 = 755735) (by norm_num)
theorem B2687045 : Blo 1790096 2687045 := bbase (se 4 (by rfl) ⟨251910, by rfl⟩ : syracuseStep 2687045 = 503821) (by norm_num)
theorem B4030541 : Blo 1790096 4030541 := bbase (se 3 (by rfl) ⟨755726, by rfl⟩ : syracuseStep 4030541 = 1511453) (by norm_num)
theorem B3022933 : Blo 1790096 3022933 := bbase (se 8 (by rfl) ⟨17712, by rfl⟩ : syracuseStep 3022933 = 35425) (by norm_num)
theorem B2687069 : Blo 1790096 2687069 := bbase (se 3 (by rfl) ⟨503825, by rfl⟩ : syracuseStep 2687069 = 1007651) (by norm_num)
theorem B2015329 : Blo 1790096 2015329 := bbase (se 2 (by rfl) ⟨755748, by rfl⟩ : syracuseStep 2015329 = 1511497) (by norm_num)
theorem B15294581 : Blo 1790096 15294581 := bbase (se 5 (by rfl) ⟨716933, by rfl⟩ : syracuseStep 15294581 = 1433867) (by norm_num)
theorem B2687093 : Blo 1790096 2687093 := bbase (se 5 (by rfl) ⟨125957, by rfl⟩ : syracuseStep 2687093 = 251915) (by norm_num)
theorem B2015365 : Blo 1790096 2015365 := bbase (se 4 (by rfl) ⟨188940, by rfl⟩ : syracuseStep 2015365 = 377881) (by norm_num)
theorem B2687117 : Blo 1790096 2687117 := bbase (se 3 (by rfl) ⟨503834, by rfl⟩ : syracuseStep 2687117 = 1007669) (by norm_num)
theorem B4030613 : Blo 1790096 4030613 := bbase (se 6 (by rfl) ⟨94467, by rfl⟩ : syracuseStep 4030613 = 188935) (by norm_num)
theorem B7651493 : Blo 1790096 7651493 := bbase (se 4 (by rfl) ⟨717327, by rfl⟩ : syracuseStep 7651493 = 1434655) (by norm_num)
theorem B2687141 : Blo 1790096 2687141 := bbase (se 4 (by rfl) ⟨251919, by rfl⟩ : syracuseStep 2687141 = 503839) (by norm_num)
theorem B2015401 : Blo 1790096 2015401 := bbase (se 2 (by rfl) ⟨755775, by rfl⟩ : syracuseStep 2015401 = 1511551) (by norm_num)
theorem B3023021 : Blo 1790096 3023021 := bbase (se 3 (by rfl) ⟨566816, by rfl⟩ : syracuseStep 3023021 = 1133633) (by norm_num)
theorem B2687165 : Blo 1790096 2687165 := bbase (se 3 (by rfl) ⟨503843, by rfl⟩ : syracuseStep 2687165 = 1007687) (by norm_num)
theorem B6045893 : Blo 1790096 6045893 := bbase (se 4 (by rfl) ⟨566802, by rfl⟩ : syracuseStep 6045893 = 1133605) (by norm_num)
theorem B2015437 : Blo 1790096 2015437 := bbase (se 3 (by rfl) ⟨377894, by rfl⟩ : syracuseStep 2015437 = 755789) (by norm_num)
theorem B2687189 : Blo 1790096 2687189 := bbase (se 7 (by rfl) ⟨31490, by rfl⟩ : syracuseStep 2687189 = 62981) (by norm_num)
theorem B4030685 : Blo 1790096 4030685 := bbase (se 3 (by rfl) ⟨755753, by rfl⟩ : syracuseStep 4030685 = 1511507) (by norm_num)
theorem B2687213 : Blo 1790096 2687213 := bbase (se 3 (by rfl) ⟨503852, by rfl⟩ : syracuseStep 2687213 = 1007705) (by norm_num)
theorem B2015473 : Blo 1790096 2015473 := bbase (se 2 (by rfl) ⟨755802, by rfl⟩ : syracuseStep 2015473 = 1511605) (by norm_num)
theorem B2687237 : Blo 1790096 2687237 := bbase (se 4 (by rfl) ⟨251928, by rfl⟩ : syracuseStep 2687237 = 503857) (by norm_num)
theorem B2015509 : Blo 1790096 2015509 := bbase (se 6 (by rfl) ⟨47238, by rfl⟩ : syracuseStep 2015509 = 94477) (by norm_num)
theorem B3399965 : Blo 1790096 3399965 := bbase (se 3 (by rfl) ⟨637493, by rfl⟩ : syracuseStep 3399965 = 1274987) (by norm_num)
theorem B2687261 : Blo 1790096 2687261 := bbase (se 3 (by rfl) ⟨503861, by rfl⟩ : syracuseStep 2687261 = 1007723) (by norm_num)
theorem B4030757 : Blo 1790096 4030757 := bbase (se 4 (by rfl) ⟨377883, by rfl⟩ : syracuseStep 4030757 = 755767) (by norm_num)
theorem B3023149 : Blo 1790096 3023149 := bbase (se 3 (by rfl) ⟨566840, by rfl⟩ : syracuseStep 3023149 = 1133681) (by norm_num)
theorem B2687285 : Blo 1790096 2687285 := bbase (se 5 (by rfl) ⟨125966, by rfl⟩ : syracuseStep 2687285 = 251933) (by norm_num)
theorem B2015545 : Blo 1790096 2015545 := bbase (se 2 (by rfl) ⟨755829, by rfl⟩ : syracuseStep 2015545 = 1511659) (by norm_num)
theorem B2687309 : Blo 1790096 2687309 := bbase (se 3 (by rfl) ⟨503870, by rfl⟩ : syracuseStep 2687309 = 1007741) (by norm_num)
theorem B2015581 : Blo 1790096 2015581 := bbase (se 3 (by rfl) ⟨377921, by rfl⟩ : syracuseStep 2015581 = 755843) (by norm_num)
theorem B2687333 : Blo 1790096 2687333 := bbase (se 4 (by rfl) ⟨251937, by rfl⟩ : syracuseStep 2687333 = 503875) (by norm_num)
theorem B4030829 : Blo 1790096 4030829 := bbase (se 3 (by rfl) ⟨755780, by rfl⟩ : syracuseStep 4030829 = 1511561) (by norm_num)
theorem B6799733 : Blo 1790096 6799733 := bbase (se 5 (by rfl) ⟨318737, by rfl⟩ : syracuseStep 6799733 = 637475) (by norm_num)
theorem B2687357 : Blo 1790096 2687357 := bbase (se 3 (by rfl) ⟨503879, by rfl⟩ : syracuseStep 2687357 = 1007759) (by norm_num)
theorem B2015617 : Blo 1790096 2015617 := bbase (se 2 (by rfl) ⟨755856, by rfl⟩ : syracuseStep 2015617 = 1511713) (by norm_num)
theorem B3023237 : Blo 1790096 3023237 := bbase (se 4 (by rfl) ⟨283428, by rfl⟩ : syracuseStep 3023237 = 566857) (by norm_num)
theorem B2687381 : Blo 1790096 2687381 := bbase (se 6 (by rfl) ⟨62985, by rfl⟩ : syracuseStep 2687381 = 125971) (by norm_num)
theorem B6455717 : Blo 1790096 6455717 := bbase (se 4 (by rfl) ⟨605223, by rfl⟩ : syracuseStep 6455717 = 1210447) (by norm_num)
theorem B2015653 : Blo 1790096 2015653 := bbase (se 4 (by rfl) ⟨188967, by rfl⟩ : syracuseStep 2015653 = 377935) (by norm_num)
theorem B2687405 : Blo 1790096 2687405 := bbase (se 3 (by rfl) ⟨503888, by rfl⟩ : syracuseStep 2687405 = 1007777) (by norm_num)
theorem B4301237 : Blo 1790096 4301237 := bbase (se 5 (by rfl) ⟨201620, by rfl⟩ : syracuseStep 4301237 = 403241) (by norm_num)
theorem B10887605 : Blo 1790096 10887605 := bbase (se 5 (by rfl) ⟨510356, by rfl⟩ : syracuseStep 10887605 = 1020713) (by norm_num)
theorem B4030901 : Blo 1790096 4030901 := bbase (se 5 (by rfl) ⟨188948, by rfl⟩ : syracuseStep 4030901 = 377897) (by norm_num)
theorem B2867645 : Blo 1790096 2867645 := bbase (se 3 (by rfl) ⟨537683, by rfl⟩ : syracuseStep 2867645 = 1075367) (by norm_num)
theorem B2687429 : Blo 1790096 2687429 := bbase (se 4 (by rfl) ⟨251946, by rfl⟩ : syracuseStep 2687429 = 503893) (by norm_num)
theorem B2015689 : Blo 1790096 2015689 := bbase (se 2 (by rfl) ⟨755883, by rfl⟩ : syracuseStep 2015689 = 1511767) (by norm_num)
theorem B2687453 : Blo 1790096 2687453 := bbase (se 3 (by rfl) ⟨503897, by rfl⟩ : syracuseStep 2687453 = 1007795) (by norm_num)
theorem B2015725 : Blo 1790096 2015725 := bbase (se 3 (by rfl) ⟨377948, by rfl⟩ : syracuseStep 2015725 = 755897) (by norm_num)
theorem B2687477 : Blo 1790096 2687477 := bbase (se 5 (by rfl) ⟨125975, by rfl⟩ : syracuseStep 2687477 = 251951) (by norm_num)
theorem B4030973 : Blo 1790096 4030973 := bbase (se 3 (by rfl) ⟨755807, by rfl⟩ : syracuseStep 4030973 = 1511615) (by norm_num)
theorem B3023365 : Blo 1790096 3023365 := bbase (se 4 (by rfl) ⟨283440, by rfl⟩ : syracuseStep 3023365 = 566881) (by norm_num)
theorem B2687501 : Blo 1790096 2687501 := bbase (se 3 (by rfl) ⟨503906, by rfl⟩ : syracuseStep 2687501 = 1007813) (by norm_num)
theorem B2015761 : Blo 1790096 2015761 := bbase (se 2 (by rfl) ⟨755910, by rfl⟩ : syracuseStep 2015761 = 1511821) (by norm_num)
theorem B2687525 : Blo 1790096 2687525 := bbase (se 4 (by rfl) ⟨251955, by rfl⟩ : syracuseStep 2687525 = 503911) (by norm_num)
theorem B2015797 : Blo 1790096 2015797 := bbase (se 5 (by rfl) ⟨94490, by rfl⟩ : syracuseStep 2015797 = 188981) (by norm_num)
theorem B2687549 : Blo 1790096 2687549 := bbase (se 3 (by rfl) ⟨503915, by rfl⟩ : syracuseStep 2687549 = 1007831) (by norm_num)
theorem B4031045 : Blo 1790096 4031045 := bbase (se 4 (by rfl) ⟨377910, by rfl⟩ : syracuseStep 4031045 = 755821) (by norm_num)
theorem B5169749 : Blo 1790096 5169749 := bbase (se 8 (by rfl) ⟨30291, by rfl⟩ : syracuseStep 5169749 = 60583) (by norm_num)
theorem B2687573 : Blo 1790096 2687573 := bbase (se 8 (by rfl) ⟨15747, by rfl⟩ : syracuseStep 2687573 = 31495) (by norm_num)
theorem B2015833 : Blo 1790096 2015833 := bbase (se 2 (by rfl) ⟨755937, by rfl⟩ : syracuseStep 2015833 = 1511875) (by norm_num)
theorem B3023453 : Blo 1790096 3023453 := bbase (se 3 (by rfl) ⟨566897, by rfl⟩ : syracuseStep 3023453 = 1133795) (by norm_num)
theorem B2687597 : Blo 1790096 2687597 := bbase (se 3 (by rfl) ⟨503924, by rfl⟩ : syracuseStep 2687597 = 1007849) (by norm_num)
theorem B10887797 : Blo 1790096 10887797 := bbase (se 5 (by rfl) ⟨510365, by rfl⟩ : syracuseStep 10887797 = 1020731) (by norm_num)
theorem B6128245 : Blo 1790096 6128245 := bbase (se 5 (by rfl) ⟨287261, by rfl⟩ : syracuseStep 6128245 = 574523) (by norm_num)
theorem B6046325 : Blo 1790096 6046325 := bbase (se 5 (by rfl) ⟨283421, by rfl⟩ : syracuseStep 6046325 = 566843) (by norm_num)
theorem B2015869 : Blo 1790096 2015869 := bbase (se 3 (by rfl) ⟨377975, by rfl⟩ : syracuseStep 2015869 = 755951) (by norm_num)
theorem B2687621 : Blo 1790096 2687621 := bbase (se 4 (by rfl) ⟨251964, by rfl⟩ : syracuseStep 2687621 = 503929) (by norm_num)
theorem B4031117 : Blo 1790096 4031117 := bbase (se 3 (by rfl) ⟨755834, by rfl⟩ : syracuseStep 4031117 = 1511669) (by norm_num)
theorem B10338965 : Blo 1790096 10338965 := bbase (se 6 (by rfl) ⟨242319, by rfl⟩ : syracuseStep 10338965 = 484639) (by norm_num)
theorem B6800021 : Blo 1790096 6800021 := bbase (se 6 (by rfl) ⟨159375, by rfl⟩ : syracuseStep 6800021 = 318751) (by norm_num)
theorem B2687645 : Blo 1790096 2687645 := bbase (se 3 (by rfl) ⟨503933, by rfl⟩ : syracuseStep 2687645 = 1007867) (by norm_num)
theorem B2015905 : Blo 1790096 2015905 := bbase (se 2 (by rfl) ⟨755964, by rfl⟩ : syracuseStep 2015905 = 1511929) (by norm_num)
theorem B2687669 : Blo 1790096 2687669 := bbase (se 5 (by rfl) ⟨125984, by rfl⟩ : syracuseStep 2687669 = 251969) (by norm_num)
theorem B2015941 : Blo 1790096 2015941 := bbase (se 4 (by rfl) ⟨188994, by rfl⟩ : syracuseStep 2015941 = 377989) (by norm_num)
theorem B2687693 : Blo 1790096 2687693 := bbase (se 3 (by rfl) ⟨503942, by rfl⟩ : syracuseStep 2687693 = 1007885) (by norm_num)
theorem B4301525 : Blo 1790096 4301525 := bbase (se 7 (by rfl) ⟨50408, by rfl⟩ : syracuseStep 4301525 = 100817) (by norm_num)
theorem B4031189 : Blo 1790096 4031189 := bbase (se 7 (by rfl) ⟨47240, by rfl⟩ : syracuseStep 4031189 = 94481) (by norm_num)
theorem B3023581 : Blo 1790096 3023581 := bbase (se 3 (by rfl) ⟨566921, by rfl⟩ : syracuseStep 3023581 = 1133843) (by norm_num)
theorem B2687717 : Blo 1790096 2687717 := bbase (se 4 (by rfl) ⟨251973, by rfl⟩ : syracuseStep 2687717 = 503947) (by norm_num)
theorem B2015977 : Blo 1790096 2015977 := bbase (se 2 (by rfl) ⟨755991, by rfl⟩ : syracuseStep 2015977 = 1511983) (by norm_num)
theorem B2687741 : Blo 1790096 2687741 := bbase (se 3 (by rfl) ⟨503951, by rfl⟩ : syracuseStep 2687741 = 1007903) (by norm_num)
theorem B2016013 : Blo 1790096 2016013 := bbase (se 3 (by rfl) ⟨378002, by rfl⟩ : syracuseStep 2016013 = 756005) (by norm_num)
theorem B2687765 : Blo 1790096 2687765 := bbase (se 6 (by rfl) ⟨62994, by rfl⟩ : syracuseStep 2687765 = 125989) (by norm_num)
theorem B4031261 : Blo 1790096 4031261 := bbase (se 3 (by rfl) ⟨755861, by rfl⟩ : syracuseStep 4031261 = 1511723) (by norm_num)
theorem B2687789 : Blo 1790096 2687789 := bbase (se 3 (by rfl) ⟨503960, by rfl⟩ : syracuseStep 2687789 = 1007921) (by norm_num)
theorem B2016049 : Blo 1790096 2016049 := bbase (se 2 (by rfl) ⟨756018, by rfl⟩ : syracuseStep 2016049 = 1512037) (by norm_num)
theorem B3023669 : Blo 1790096 3023669 := bbase (se 5 (by rfl) ⟨141734, by rfl⟩ : syracuseStep 3023669 = 283469) (by norm_num)
theorem B2868029 : Blo 1790096 2868029 := bbase (se 3 (by rfl) ⟨537755, by rfl⟩ : syracuseStep 2868029 = 1075511) (by norm_num)
theorem B2687813 : Blo 1790096 2687813 := bbase (se 4 (by rfl) ⟨251982, by rfl⟩ : syracuseStep 2687813 = 503965) (by norm_num)
theorem B2016085 : Blo 1790096 2016085 := bbase (se 9 (by rfl) ⟨5906, by rfl⟩ : syracuseStep 2016085 = 11813) (by norm_num)
theorem B2687837 : Blo 1790096 2687837 := bbase (se 3 (by rfl) ⟨503969, by rfl⟩ : syracuseStep 2687837 = 1007939) (by norm_num)
theorem B4031333 : Blo 1790096 4031333 := bbase (se 4 (by rfl) ⟨377937, by rfl⟩ : syracuseStep 4031333 = 755875) (by norm_num)
theorem B2687861 : Blo 1790096 2687861 := bbase (se 5 (by rfl) ⟨125993, by rfl⟩ : syracuseStep 2687861 = 251987) (by norm_num)
theorem B2687885 : Blo 1790096 2687885 := bbase (se 3 (by rfl) ⟨503978, by rfl⟩ : syracuseStep 2687885 = 1007957) (by norm_num)
theorem B7652245 : Blo 1790096 7652245 := bbase (se 6 (by rfl) ⟨179349, by rfl⟩ : syracuseStep 7652245 = 358699) (by norm_num)
theorem B2687909 : Blo 1790096 2687909 := bbase (se 4 (by rfl) ⟨251991, by rfl⟩ : syracuseStep 2687909 = 503983) (by norm_num)
theorem B4031405 : Blo 1790096 4031405 := bbase (se 3 (by rfl) ⟨755888, by rfl⟩ : syracuseStep 4031405 = 1511777) (by norm_num)
theorem B3023797 : Blo 1790096 3023797 := bbase (se 5 (by rfl) ⟨141740, by rfl⟩ : syracuseStep 3023797 = 283481) (by norm_num)
theorem B2868157 : Blo 1790096 2868157 := bbase (se 3 (by rfl) ⟨537779, by rfl⟩ : syracuseStep 2868157 = 1075559) (by norm_num)
theorem B2687933 : Blo 1790096 2687933 := bbase (se 3 (by rfl) ⟨503987, by rfl⟩ : syracuseStep 2687933 = 1007975) (by norm_num)
theorem B2687957 : Blo 1790096 2687957 := bbase (se 7 (by rfl) ⟨31499, by rfl⟩ : syracuseStep 2687957 = 62999) (by norm_num)
theorem B2687981 : Blo 1790096 2687981 := bbase (se 3 (by rfl) ⟨503996, by rfl⟩ : syracuseStep 2687981 = 1007993) (by norm_num)
theorem B4031477 : Blo 1790096 4031477 := bbase (se 5 (by rfl) ⟨188975, by rfl⟩ : syracuseStep 4031477 = 377951) (by norm_num)
theorem B2688005 : Blo 1790096 2688005 := bbase (se 4 (by rfl) ⟨252000, by rfl⟩ : syracuseStep 2688005 = 504001) (by norm_num)
theorem B3400717 : Blo 1790096 3400717 := bbase (se 3 (by rfl) ⟨637634, by rfl⟩ : syracuseStep 3400717 = 1275269) (by norm_num)
theorem B3023885 : Blo 1790096 3023885 := bbase (se 3 (by rfl) ⟨566978, by rfl⟩ : syracuseStep 3023885 = 1133957) (by norm_num)
theorem B3630101 : Blo 1790096 3630101 := bbase (se 6 (by rfl) ⟨85080, by rfl⟩ : syracuseStep 3630101 = 170161) (by norm_num)
theorem B3630109 : Blo 1790096 3630109 := bbase (se 3 (by rfl) ⟨680645, by rfl⟩ : syracuseStep 3630109 = 1361291) (by norm_num)
theorem B2688029 : Blo 1790096 2688029 := bbase (se 3 (by rfl) ⟨504005, by rfl⟩ : syracuseStep 2688029 = 1008011) (by norm_num)
theorem B6046757 : Blo 1790096 6046757 := bbase (se 4 (by rfl) ⟨566883, by rfl⟩ : syracuseStep 6046757 = 1133767) (by norm_num)
theorem B2688053 : Blo 1790096 2688053 := bbase (se 5 (by rfl) ⟨126002, by rfl⟩ : syracuseStep 2688053 = 252005) (by norm_num)
theorem B4531261 : Blo 1790096 4531261 := bbase (se 3 (by rfl) ⟨849611, by rfl⟩ : syracuseStep 4531261 = 1699223) (by norm_num)
theorem B4031549 : Blo 1790096 4031549 := bbase (se 3 (by rfl) ⟨755915, by rfl⟩ : syracuseStep 4031549 = 1511831) (by norm_num)
theorem B2688077 : Blo 1790096 2688077 := bbase (se 3 (by rfl) ⟨504014, by rfl⟩ : syracuseStep 2688077 = 1008029) (by norm_num)
theorem B2688101 : Blo 1790096 2688101 := bbase (se 4 (by rfl) ⟨252009, by rfl⟩ : syracuseStep 2688101 = 504019) (by norm_num)
theorem B2688125 : Blo 1790096 2688125 := bbase (se 3 (by rfl) ⟨504023, by rfl⟩ : syracuseStep 2688125 = 1008047) (by norm_num)
theorem B4031621 : Blo 1790096 4031621 := bbase (se 4 (by rfl) ⟨377964, by rfl⟩ : syracuseStep 4031621 = 755929) (by norm_num)
theorem B3024013 : Blo 1790096 3024013 := bbase (se 3 (by rfl) ⟨567002, by rfl⟩ : syracuseStep 3024013 = 1134005) (by norm_num)
theorem B6456469 : Blo 1790096 6456469 := bbase (se 6 (by rfl) ⟨151323, by rfl⟩ : syracuseStep 6456469 = 302647) (by norm_num)
theorem B3400861 : Blo 1790096 3400861 := bbase (se 3 (by rfl) ⟨637661, by rfl⟩ : syracuseStep 3400861 = 1275323) (by norm_num)
theorem B4531373 : Blo 1790096 4531373 := bbase (se 3 (by rfl) ⟨849632, by rfl⟩ : syracuseStep 4531373 = 1699265) (by norm_num)
theorem B4031693 : Blo 1790096 4031693 := bbase (se 3 (by rfl) ⟨755942, by rfl⟩ : syracuseStep 4031693 = 1511885) (by norm_num)
theorem B3826901 : Blo 1790096 3826901 := bbase (se 7 (by rfl) ⟨44846, by rfl⟩ : syracuseStep 3826901 = 89693) (by norm_num)
theorem B3024101 : Blo 1790096 3024101 := bbase (se 4 (by rfl) ⟨283509, by rfl⟩ : syracuseStep 3024101 = 567019) (by norm_num)
theorem B4031765 : Blo 1790096 4031765 := bbase (se 6 (by rfl) ⟨94494, by rfl⟩ : syracuseStep 4031765 = 188989) (by norm_num)
theorem B3401021 : Blo 1790096 3401021 := bbase (se 3 (by rfl) ⟨637691, by rfl⟩ : syracuseStep 3401021 = 1275383) (by norm_num)
theorem B3065149 : Blo 1790096 3065149 := bbase (se 3 (by rfl) ⟨574715, by rfl⟩ : syracuseStep 3065149 = 1149431) (by norm_num)
theorem B9069893 : Blo 1790096 9069893 := bbase (se 4 (by rfl) ⟨850302, by rfl⟩ : syracuseStep 9069893 = 1700605) (by norm_num)
theorem B12911957 : Blo 1790096 12911957 := bbase (se 12 (by rfl) ⟨4728, by rfl⟩ : syracuseStep 12911957 = 9457) (by norm_num)
theorem B4031837 : Blo 1790096 4031837 := bbase (se 3 (by rfl) ⟨755969, by rfl⟩ : syracuseStep 4031837 = 1511939) (by norm_num)
theorem B3827045 : Blo 1790096 3827045 := bbase (se 4 (by rfl) ⟨358785, by rfl⟩ : syracuseStep 3827045 = 717571) (by norm_num)
theorem B4531565 : Blo 1790096 4531565 := bbase (se 3 (by rfl) ⟨849668, by rfl⟩ : syracuseStep 4531565 = 1699337) (by norm_num)
theorem B3229085 : Blo 1790096 3229085 := bbase (se 3 (by rfl) ⟨605453, by rfl⟩ : syracuseStep 3229085 = 1210907) (by norm_num)
theorem B4031909 : Blo 1790096 4031909 := bbase (se 4 (by rfl) ⟨377991, by rfl⟩ : syracuseStep 4031909 = 755983) (by norm_num)
theorem B3401165 : Blo 1790096 3401165 := bbase (se 3 (by rfl) ⟨637718, by rfl⟩ : syracuseStep 3401165 = 1275437) (by norm_num)
theorem B6047189 : Blo 1790096 6047189 := bbase (se 7 (by rfl) ⟨70865, by rfl⟩ : syracuseStep 6047189 = 141731) (by norm_num)
theorem B4031981 : Blo 1790096 4031981 := bbase (se 3 (by rfl) ⟨755996, by rfl⟩ : syracuseStep 4031981 = 1511993) (by norm_num)
theorem B2549245 : Blo 1790096 2549245 := bbase (se 3 (by rfl) ⟨477983, by rfl⟩ : syracuseStep 2549245 = 955967) (by norm_num)
theorem B3229237 : Blo 1790096 3229237 := bbase (se 5 (by rfl) ⟨151370, by rfl⟩ : syracuseStep 3229237 = 302741) (by norm_num)
theorem B4032053 : Blo 1790096 4032053 := bbase (se 5 (by rfl) ⟨189002, by rfl⟩ : syracuseStep 4032053 = 378005) (by norm_num)
theorem B7652981 : Blo 1790096 7652981 := bbase (se 5 (by rfl) ⟨358733, by rfl⟩ : syracuseStep 7652981 = 717467) (by norm_num)
theorem B3229301 : Blo 1790096 3229301 := bbase (se 5 (by rfl) ⟨151373, by rfl⟩ : syracuseStep 3229301 = 302747) (by norm_num)
theorem B4032125 : Blo 1790096 4032125 := bbase (se 3 (by rfl) ⟨756023, by rfl⟩ : syracuseStep 4032125 = 1512047) (by norm_num)
theorem B4531909 : Blo 1790096 4531909 := bbase (se 4 (by rfl) ⟨424866, by rfl⟩ : syracuseStep 4531909 = 849733) (by norm_num)
theorem B4032197 : Blo 1790096 4032197 := bbase (se 4 (by rfl) ⟨378018, by rfl⟩ : syracuseStep 4032197 = 756037) (by norm_num)
theorem B3827405 : Blo 1790096 3827405 := bbase (se 3 (by rfl) ⟨717638, by rfl⟩ : syracuseStep 3827405 = 1435277) (by norm_num)
theorem B3401453 : Blo 1790096 3401453 := bbase (se 3 (by rfl) ⟨637772, by rfl⟩ : syracuseStep 3401453 = 1275545) (by norm_num)
theorem B4532021 : Blo 1790096 4532021 := bbase (se 5 (by rfl) ⟨212438, by rfl⟩ : syracuseStep 4532021 = 424877) (by norm_num)
theorem B6801205 : Blo 1790096 6801205 := bbase (se 5 (by rfl) ⟨318806, by rfl⟩ : syracuseStep 6801205 = 637613) (by norm_num)
theorem B3106685 : Blo 1790096 3106685 := bbase (se 3 (by rfl) ⟨582503, by rfl⟩ : syracuseStep 3106685 = 1165007) (by norm_num)
theorem B5973893 : Blo 1790096 5973893 := bbase (se 4 (by rfl) ⟨560052, by rfl⟩ : syracuseStep 5973893 = 1120105) (by norm_num)
theorem B3401605 : Blo 1790096 3401605 := bbase (se 4 (by rfl) ⟨318900, by rfl⟩ : syracuseStep 3401605 = 637801) (by norm_num)
theorem B6047621 : Blo 1790096 6047621 := bbase (se 4 (by rfl) ⟨566964, by rfl⟩ : syracuseStep 6047621 = 1133929) (by norm_num)
theorem B2869157 : Blo 1790096 2869157 := bbase (se 4 (by rfl) ⟨268983, by rfl⟩ : syracuseStep 2869157 = 537967) (by norm_num)
theorem B4532213 : Blo 1790096 4532213 := bbase (se 5 (by rfl) ⟨212447, by rfl⟩ : syracuseStep 4532213 = 424895) (by norm_num)
theorem B2869285 : Blo 1790096 2869285 := bbase (se 4 (by rfl) ⟨268995, by rfl⟩ : syracuseStep 2869285 = 537991) (by norm_num)
theorem B2721853 : Blo 1790096 2721853 := bbase (se 3 (by rfl) ⟨510347, by rfl⟩ : syracuseStep 2721853 = 1020695) (by norm_num)
theorem B2549837 : Blo 1790096 2549837 := bbase (se 3 (by rfl) ⟨478094, by rfl⟩ : syracuseStep 2549837 = 956189) (by norm_num)
theorem B5171285 : Blo 1790096 5171285 := bbase (se 8 (by rfl) ⟨30300, by rfl⟩ : syracuseStep 5171285 = 60601) (by norm_num)
theorem B6801509 : Blo 1790096 6801509 := bbase (se 4 (by rfl) ⟨637641, by rfl⟩ : syracuseStep 6801509 = 1275283) (by norm_num)
theorem B2721925 : Blo 1790096 2721925 := bbase (se 4 (by rfl) ⟨255180, by rfl⟩ : syracuseStep 2721925 = 510361) (by norm_num)
theorem B6457477 : Blo 1790096 6457477 := bbase (se 4 (by rfl) ⟨605388, by rfl⟩ : syracuseStep 6457477 = 1210777) (by norm_num)
theorem B2549917 : Blo 1790096 2549917 := bbase (se 3 (by rfl) ⟨478109, by rfl⟩ : syracuseStep 2549917 = 956219) (by norm_num)
theorem B3401909 : Blo 1790096 3401909 := bbase (se 5 (by rfl) ⟨159464, by rfl⟩ : syracuseStep 3401909 = 318929) (by norm_num)
theorem B8284357 : Blo 1790096 8284357 := bbase (se 4 (by rfl) ⟨776658, by rfl⟩ : syracuseStep 8284357 = 1553317) (by norm_num)
theorem B2550037 : Blo 1790096 2550037 := bbase (se 6 (by rfl) ⟨59766, by rfl⟩ : syracuseStep 2550037 = 119533) (by norm_num)
theorem B6048053 : Blo 1790096 6048053 := bbase (se 5 (by rfl) ⟨283502, by rfl⟩ : syracuseStep 6048053 = 567005) (by norm_num)
theorem B3148093 : Blo 1790096 3148093 := bbase (se 3 (by rfl) ⟨590267, by rfl⟩ : syracuseStep 3148093 = 1180535) (by norm_num)
theorem B4532557 : Blo 1790096 4532557 := bbase (se 3 (by rfl) ⟨849854, by rfl⟩ : syracuseStep 4532557 = 1699709) (by norm_num)
theorem B5097829 : Blo 1790096 5097829 := bbase (se 4 (by rfl) ⟨477921, by rfl⟩ : syracuseStep 5097829 = 955843) (by norm_num)
theorem B2550133 : Blo 1790096 2550133 := bbase (se 5 (by rfl) ⟨119537, by rfl⟩ : syracuseStep 2550133 = 239075) (by norm_num)
theorem B2869669 : Blo 1790096 2869669 := bbase (se 4 (by rfl) ⟨269031, by rfl⟩ : syracuseStep 2869669 = 538063) (by norm_num)
theorem B4532669 : Blo 1790096 4532669 := bbase (se 3 (by rfl) ⟨849875, by rfl⟩ : syracuseStep 4532669 = 1699751) (by norm_num)
theorem B4360661 : Blo 1790096 4360661 := bbase (se 7 (by rfl) ⟨51101, by rfl⟩ : syracuseStep 4360661 = 102203) (by norm_num)
theorem B9071189 : Blo 1790096 9071189 := bbase (se 8 (by rfl) ⟨53151, by rfl⟩ : syracuseStep 9071189 = 106303) (by norm_num)
theorem B4532861 : Blo 1790096 4532861 := bbase (se 3 (by rfl) ⟨849911, by rfl⟩ : syracuseStep 4532861 = 1699823) (by norm_num)
theorem B2869925 : Blo 1790096 2869925 := bbase (se 4 (by rfl) ⟨269055, by rfl⟩ : syracuseStep 2869925 = 538111) (by norm_num)
theorem B9186085 : Blo 1790096 9186085 := bbase (se 4 (by rfl) ⟨861195, by rfl⟩ : syracuseStep 9186085 = 1722391) (by norm_num)
theorem B1911605 : Blo 1790096 1911605 := bbase (se 5 (by rfl) ⟨89606, by rfl⟩ : syracuseStep 1911605 = 179213) (by norm_num)
theorem B2550629 : Blo 1790096 2550629 := bbase (se 4 (by rfl) ⟨239121, by rfl⟩ : syracuseStep 2550629 = 478243) (by norm_num)
theorem B4533205 : Blo 1790096 4533205 := bbase (se 7 (by rfl) ⟨53123, by rfl⟩ : syracuseStep 4533205 = 106247) (by norm_num)
theorem B9063413 : Blo 1790096 9063413 := bbase (se 5 (by rfl) ⟨424847, by rfl⟩ : syracuseStep 9063413 = 849695) (by norm_num)
theorem B13093877 : Blo 1790096 13093877 := bbase (se 5 (by rfl) ⟨613775, by rfl⟩ : syracuseStep 13093877 = 1227551) (by norm_num)
theorem B5737493 : Blo 1790096 5737493 := bbase (se 6 (by rfl) ⟨134472, by rfl⟩ : syracuseStep 5737493 = 268945) (by norm_num)
theorem B18385973 : Blo 1790096 18385973 := bbase (se 5 (by rfl) ⟨861842, by rfl⟩ : syracuseStep 18385973 = 1723685) (by norm_num)
theorem B4533317 : Blo 1790096 4533317 := bbase (se 4 (by rfl) ⟨424998, by rfl⟩ : syracuseStep 4533317 = 849997) (by norm_num)
theorem B20393045 : Blo 1790096 20393045 := bbase (se 8 (by rfl) ⟨119490, by rfl⟩ : syracuseStep 20393045 = 238981) (by norm_num)
theorem B2419813 : Blo 1790096 2419813 := bbase (se 4 (by rfl) ⟨226857, by rfl⟩ : syracuseStep 2419813 = 453715) (by norm_num)
theorem B4533509 : Blo 1790096 4533509 := bbase (se 4 (by rfl) ⟨425016, by rfl⟩ : syracuseStep 4533509 = 850033) (by norm_num)
theorem B4082989 : Blo 1790096 4082989 := bbase (se 3 (by rfl) ⟨765560, by rfl⟩ : syracuseStep 4082989 = 1531121) (by norm_num)
theorem B2420029 : Blo 1790096 2420029 := bbase (se 3 (by rfl) ⟨453755, by rfl⟩ : syracuseStep 2420029 = 907511) (by norm_num)
theorem B2551181 : Blo 1790096 2551181 := bbase (se 3 (by rfl) ⟨478346, by rfl⟩ : syracuseStep 2551181 = 956693) (by norm_num)
theorem B4656565 : Blo 1790096 4656565 := bbase (se 5 (by rfl) ⟨218276, by rfl⟩ : syracuseStep 4656565 = 436553) (by norm_num)
theorem B1912357 : Blo 1790096 1912357 := bbase (se 4 (by rfl) ⟨179283, by rfl⟩ : syracuseStep 1912357 = 358567) (by norm_num)
theorem B4533853 : Blo 1790096 4533853 := bbase (se 3 (by rfl) ⟨850097, by rfl⟩ : syracuseStep 4533853 = 1700195) (by norm_num)
theorem B1912429 : Blo 1790096 1912429 := bbase (se 3 (by rfl) ⟨358580, by rfl⟩ : syracuseStep 1912429 = 717161) (by norm_num)
theorem B2043505 : Blo 1790096 2043505 := bbase (se 2 (by rfl) ⟨766314, by rfl⟩ : syracuseStep 2043505 = 1532629) (by norm_num)
theorem B4533965 : Blo 1790096 4533965 := bbase (se 3 (by rfl) ⟨850118, by rfl⟩ : syracuseStep 4533965 = 1700237) (by norm_num)
theorem B2723549 : Blo 1790096 2723549 := bbase (se 3 (by rfl) ⟨510665, by rfl⟩ : syracuseStep 2723549 = 1021331) (by norm_num)
theorem B1912609 : Blo 1790096 1912609 := bbase (se 2 (by rfl) ⟨717228, by rfl⟩ : syracuseStep 1912609 = 1434457) (by norm_num)
theorem B4304677 : Blo 1790096 4304677 := bbase (se 4 (by rfl) ⟨403563, by rfl⟩ : syracuseStep 4304677 = 807127) (by norm_num)
theorem B9072485 : Blo 1790096 9072485 := bbase (se 4 (by rfl) ⟨850545, by rfl⟩ : syracuseStep 9072485 = 1701091) (by norm_num)
theorem B2723701 : Blo 1790096 2723701 := bbase (se 5 (by rfl) ⟨127673, by rfl⟩ : syracuseStep 2723701 = 255347) (by norm_num)
theorem B3633029 : Blo 1790096 3633029 := bbase (se 4 (by rfl) ⟨340596, by rfl⟩ : syracuseStep 3633029 = 681193) (by norm_num)
theorem B4534157 : Blo 1790096 4534157 := bbase (se 3 (by rfl) ⟨850154, by rfl⟩ : syracuseStep 4534157 = 1700309) (by norm_num)
theorem B2723749 : Blo 1790096 2723749 := bbase (se 4 (by rfl) ⟨255351, by rfl⟩ : syracuseStep 2723749 = 510703) (by norm_num)
theorem B15306677 : Blo 1790096 15306677 := bbase (se 5 (by rfl) ⟨717500, by rfl⟩ : syracuseStep 15306677 = 1435001) (by norm_num)
theorem B4419517 : Blo 1790096 4419517 := bbase (se 3 (by rfl) ⟨828659, by rfl⟩ : syracuseStep 4419517 = 1657319) (by norm_num)
theorem B8720389 : Blo 1790096 8720389 := bbase (se 4 (by rfl) ⟨817536, by rfl⟩ : syracuseStep 8720389 = 1635073) (by norm_num)
theorem B7262293 : Blo 1790096 7262293 := bbase (se 8 (by rfl) ⟨42552, by rfl⟩ : syracuseStep 7262293 = 85105) (by norm_num)
theorem B6803621 : Blo 1790096 6803621 := bbase (se 4 (by rfl) ⟨637839, by rfl⟩ : syracuseStep 6803621 = 1275679) (by norm_num)
theorem B1913053 : Blo 1790096 1913053 := bbase (se 3 (by rfl) ⟨358697, by rfl⟩ : syracuseStep 1913053 = 717395) (by norm_num)
theorem B4534501 : Blo 1790096 4534501 := bbase (se 4 (by rfl) ⟨425109, by rfl⟩ : syracuseStep 4534501 = 850219) (by norm_num)
theorem B9064709 : Blo 1790096 9064709 := bbase (se 4 (by rfl) ⟨849816, by rfl⟩ : syracuseStep 9064709 = 1699633) (by norm_num)
theorem B4534613 : Blo 1790096 4534613 := bbase (se 10 (by rfl) ⟨6642, by rfl⟩ : syracuseStep 4534613 = 13285) (by norm_num)
theorem B1913177 : Blo 1790096 1913177 := bbase (se 2 (by rfl) ⟨717441, by rfl⟩ : syracuseStep 1913177 = 1434883) (by norm_num)
theorem B6042005 : Blo 1790096 6042005 := bbase (se 6 (by rfl) ⟨141609, by rfl⟩ : syracuseStep 6042005 = 283219) (by norm_num)
theorem B4084157 : Blo 1790096 4084157 := bbase (se 3 (by rfl) ⟨765779, by rfl⟩ : syracuseStep 4084157 = 1531559) (by norm_num)
theorem B4305349 : Blo 1790096 4305349 := bbase (se 4 (by rfl) ⟨403626, by rfl⟩ : syracuseStep 4305349 = 807253) (by norm_num)
theorem B6803909 : Blo 1790096 6803909 := bbase (se 4 (by rfl) ⟨637866, by rfl⟩ : syracuseStep 6803909 = 1275733) (by norm_num)
theorem B11473397 : Blo 1790096 11473397 := bbase (se 5 (by rfl) ⟨537815, by rfl⟩ : syracuseStep 11473397 = 1075631) (by norm_num)
theorem B4534805 : Blo 1790096 4534805 := bbase (se 6 (by rfl) ⟨106284, by rfl⟩ : syracuseStep 4534805 = 212569) (by norm_num)
theorem B2265661 : Blo 1790096 2265661 := bbase (se 3 (by rfl) ⟨424811, by rfl⟩ : syracuseStep 2265661 = 849623) (by norm_num)
theorem B1913429 : Blo 1790096 1913429 := bbase (se 8 (by rfl) ⟨11211, by rfl⟩ : syracuseStep 1913429 = 22423) (by norm_num)
theorem B2151041 : Blo 1790096 2151041 := bbase (se 2 (by rfl) ⟨806640, by rfl⟩ : syracuseStep 2151041 = 1613281) (by norm_num)
theorem B4305581 : Blo 1790096 4305581 := bbase (se 3 (by rfl) ⟨807296, by rfl⟩ : syracuseStep 4305581 = 1614593) (by norm_num)
theorem B2265833 : Blo 1790096 2265833 := bbase (se 2 (by rfl) ⟨849687, by rfl⟩ : syracuseStep 2265833 = 1699375) (by norm_num)
theorem B3445517 : Blo 1790096 3445517 := bbase (se 3 (by rfl) ⟨646034, by rfl⟩ : syracuseStep 3445517 = 1292069) (by norm_num)
theorem B2265889 : Blo 1790096 2265889 := bbase (se 2 (by rfl) ⟨849708, by rfl⟩ : syracuseStep 2265889 = 1699417) (by norm_num)
theorem B4305725 : Blo 1790096 4305725 := bbase (se 3 (by rfl) ⟨807323, by rfl⟩ : syracuseStep 4305725 = 1614647) (by norm_num)
theorem B6042437 : Blo 1790096 6042437 := bbase (se 4 (by rfl) ⟨566478, by rfl⟩ : syracuseStep 6042437 = 1132957) (by norm_num)
theorem B4535149 : Blo 1790096 4535149 := bbase (se 3 (by rfl) ⟨850340, by rfl⟩ : syracuseStep 4535149 = 1700681) (by norm_num)
theorem B4305773 : Blo 1790096 4305773 := bbase (se 3 (by rfl) ⟨807332, by rfl⟩ : syracuseStep 4305773 = 1614665) (by norm_num)
theorem B2265985 : Blo 1790096 2265985 := bbase (se 2 (by rfl) ⟨849744, by rfl⟩ : syracuseStep 2265985 = 1699489) (by norm_num)
theorem B1815517 : Blo 1790096 1815517 := bbase (se 3 (by rfl) ⟨340409, by rfl⟩ : syracuseStep 1815517 = 680819) (by norm_num)
theorem B4535261 : Blo 1790096 4535261 := bbase (se 3 (by rfl) ⟨850361, by rfl⟩ : syracuseStep 4535261 = 1700723) (by norm_num)
theorem B6542309 : Blo 1790096 6542309 := bbase (se 4 (by rfl) ⟨613341, by rfl⟩ : syracuseStep 6542309 = 1226683) (by norm_num)
theorem B2266157 : Blo 1790096 2266157 := bbase (se 3 (by rfl) ⟨424904, by rfl⟩ : syracuseStep 2266157 = 849809) (by norm_num)
theorem B9679925 : Blo 1790096 9679925 := bbase (se 5 (by rfl) ⟨453746, by rfl⟩ : syracuseStep 9679925 = 907493) (by norm_num)
theorem B2266213 : Blo 1790096 2266213 := bbase (se 4 (by rfl) ⟨212457, by rfl⟩ : syracuseStep 2266213 = 424915) (by norm_num)
theorem B8606837 : Blo 1790096 8606837 := bbase (se 5 (by rfl) ⟨403445, by rfl⟩ : syracuseStep 8606837 = 806891) (by norm_num)
theorem B5100677 : Blo 1790096 5100677 := bbase (se 4 (by rfl) ⟨478188, by rfl⟩ : syracuseStep 5100677 = 956377) (by norm_num)
theorem B4535453 : Blo 1790096 4535453 := bbase (se 3 (by rfl) ⟨850397, by rfl⟩ : syracuseStep 4535453 = 1700795) (by norm_num)
theorem B2266309 : Blo 1790096 2266309 := bbase (se 4 (by rfl) ⟨212466, by rfl⟩ : syracuseStep 2266309 = 424933) (by norm_num)
theorem B6042869 : Blo 1790096 6042869 := bbase (se 5 (by rfl) ⟨283259, by rfl⟩ : syracuseStep 6042869 = 566519) (by norm_num)
theorem B22942997 : Blo 1790096 22942997 := bbase (se 6 (by rfl) ⟨537726, by rfl⟩ : syracuseStep 22942997 = 1075453) (by norm_num)
theorem B2151733 : Blo 1790096 2151733 := bbase (se 5 (by rfl) ⟨100862, by rfl⟩ : syracuseStep 2151733 = 201725) (by norm_num)
theorem B1815865 : Blo 1790096 1815865 := bbase (se 2 (by rfl) ⟨680949, by rfl⟩ : syracuseStep 1815865 = 1361899) (by norm_num)
theorem B4027733 : Blo 1790096 4027733 := bbase (se 13 (by rfl) ⟨737, by rfl⟩ : syracuseStep 4027733 = 1475) (by norm_num)
theorem B2266481 : Blo 1790096 2266481 := bbase (se 2 (by rfl) ⟨849930, by rfl⟩ : syracuseStep 2266481 = 1699861) (by norm_num)
theorem B6124933 : Blo 1790096 6124933 := bbase (se 4 (by rfl) ⟨574212, by rfl⟩ : syracuseStep 6124933 = 1148425) (by norm_num)
theorem B2151829 : Blo 1790096 2151829 := bbase (se 6 (by rfl) ⟨50433, by rfl⟩ : syracuseStep 2151829 = 100867) (by norm_num)
theorem B4027805 : Blo 1790096 4027805 := bbase (se 3 (by rfl) ⟨755213, by rfl⟩ : syracuseStep 4027805 = 1510427) (by norm_num)
theorem B2266537 : Blo 1790096 2266537 := bbase (se 2 (by rfl) ⟨849951, by rfl⟩ : syracuseStep 2266537 = 1699903) (by norm_num)
theorem B4027877 : Blo 1790096 4027877 := bbase (se 4 (by rfl) ⟨377613, by rfl⟩ : syracuseStep 4027877 = 755227) (by norm_num)
theorem B4535797 : Blo 1790096 4535797 := bbase (se 5 (by rfl) ⟨212615, by rfl⟩ : syracuseStep 4535797 = 425231) (by norm_num)
theorem B2266633 : Blo 1790096 2266633 := bbase (se 2 (by rfl) ⟨849987, by rfl⟩ : syracuseStep 2266633 = 1699975) (by norm_num)
theorem B9066005 : Blo 1790096 9066005 := bbase (se 6 (by rfl) ⟨212484, by rfl⟩ : syracuseStep 9066005 = 424969) (by norm_num)
theorem B4027949 : Blo 1790096 4027949 := bbase (se 3 (by rfl) ⟨755240, by rfl⟩ : syracuseStep 4027949 = 1510481) (by norm_num)
theorem B4535909 : Blo 1790096 4535909 := bbase (se 4 (by rfl) ⟨425241, by rfl⟩ : syracuseStep 4535909 = 850483) (by norm_num)
theorem B4028021 : Blo 1790096 4028021 := bbase (se 5 (by rfl) ⟨188813, by rfl⟩ : syracuseStep 4028021 = 377627) (by norm_num)
theorem B6542981 : Blo 1790096 6542981 := bbase (se 4 (by rfl) ⟨613404, by rfl⟩ : syracuseStep 6542981 = 1226809) (by norm_num)
theorem B6043301 : Blo 1790096 6043301 := bbase (se 4 (by rfl) ⟨566559, by rfl⟩ : syracuseStep 6043301 = 1133119) (by norm_num)
theorem B2266805 : Blo 1790096 2266805 := bbase (se 5 (by rfl) ⟨106256, by rfl⟩ : syracuseStep 2266805 = 212513) (by norm_num)
theorem B4028093 : Blo 1790096 4028093 := bbase (se 3 (by rfl) ⟨755267, by rfl⟩ : syracuseStep 4028093 = 1510535) (by norm_num)
theorem B2266861 : Blo 1790096 2266861 := bbase (se 3 (by rfl) ⟨425036, by rfl⟩ : syracuseStep 2266861 = 850073) (by norm_num)
theorem B13604597 : Blo 1790096 13604597 := bbase (se 5 (by rfl) ⟨637715, by rfl⟩ : syracuseStep 13604597 = 1275431) (by norm_num)
theorem B4028165 : Blo 1790096 4028165 := bbase (se 4 (by rfl) ⟨377640, by rfl⟩ : syracuseStep 4028165 = 755281) (by norm_num)
theorem B9189125 : Blo 1790096 9189125 := bbase (se 4 (by rfl) ⟨861480, by rfl⟩ : syracuseStep 9189125 = 1722961) (by norm_num)
theorem B8607509 : Blo 1790096 8607509 := bbase (se 6 (by rfl) ⟨201738, by rfl⟩ : syracuseStep 8607509 = 403477) (by norm_num)
theorem B2152213 : Blo 1790096 2152213 := bbase (se 6 (by rfl) ⟨50442, by rfl⟩ : syracuseStep 2152213 = 100885) (by norm_num)
theorem B4536101 : Blo 1790096 4536101 := bbase (se 4 (by rfl) ⟨425259, by rfl⟩ : syracuseStep 4536101 = 850519) (by norm_num)
theorem B4028237 : Blo 1790096 4028237 := bbase (se 3 (by rfl) ⟨755294, by rfl⟩ : syracuseStep 4028237 = 1510589) (by norm_num)
theorem B2266957 : Blo 1790096 2266957 := bbase (se 3 (by rfl) ⟨425054, by rfl⟩ : syracuseStep 2266957 = 850109) (by norm_num)
theorem B3315589 : Blo 1790096 3315589 := bbase (se 4 (by rfl) ⟨310836, by rfl⟩ : syracuseStep 3315589 = 621673) (by norm_num)
theorem B4028309 : Blo 1790096 4028309 := bbase (se 6 (by rfl) ⟨94413, by rfl⟩ : syracuseStep 4028309 = 188827) (by norm_num)
theorem B1841077 : Blo 1790096 1841077 := bbase (se 5 (by rfl) ⟨86300, by rfl⟩ : syracuseStep 1841077 = 172601) (by norm_num)
theorem B4028381 : Blo 1790096 4028381 := bbase (se 3 (by rfl) ⟨755321, by rfl⟩ : syracuseStep 4028381 = 1510643) (by norm_num)
theorem B2267129 : Blo 1790096 2267129 := bbase (se 2 (by rfl) ⟨850173, by rfl⟩ : syracuseStep 2267129 = 1700347) (by norm_num)
theorem B6797317 : Blo 1790096 6797317 := bbase (se 4 (by rfl) ⟨637248, by rfl⟩ : syracuseStep 6797317 = 1274497) (by norm_num)
theorem B4028453 : Blo 1790096 4028453 := bbase (se 4 (by rfl) ⟨377667, by rfl⟩ : syracuseStep 4028453 = 755335) (by norm_num)
theorem B2267185 : Blo 1790096 2267185 := bbase (se 2 (by rfl) ⟨850194, by rfl⟩ : syracuseStep 2267185 = 1700389) (by norm_num)
theorem B3020861 : Blo 1790096 3020861 := bbase (se 3 (by rfl) ⟨566411, by rfl⟩ : syracuseStep 3020861 = 1132823) (by norm_num)
theorem B6043733 : Blo 1790096 6043733 := bbase (se 8 (by rfl) ⟨35412, by rfl⟩ : syracuseStep 6043733 = 70825) (by norm_num)
theorem B1964137 : Blo 1790096 1964137 := bbase (se 2 (by rfl) ⟨736551, by rfl⟩ : syracuseStep 1964137 = 1473103) (by norm_num)
theorem B4028525 : Blo 1790096 4028525 := bbase (se 3 (by rfl) ⟨755348, by rfl⟩ : syracuseStep 4028525 = 1510697) (by norm_num)
theorem B3823757 : Blo 1790096 3823757 := bbase (se 3 (by rfl) ⟨716954, by rfl⟩ : syracuseStep 3823757 = 1433909) (by norm_num)
theorem B2267281 : Blo 1790096 2267281 := bbase (se 2 (by rfl) ⟨850230, by rfl⟩ : syracuseStep 2267281 = 1700461) (by norm_num)
theorem B13596821 : Blo 1790096 13596821 := bbase (se 6 (by rfl) ⟨318675, by rfl⟩ : syracuseStep 13596821 = 637351) (by norm_num)
theorem B4028597 : Blo 1790096 4028597 := bbase (se 5 (by rfl) ⟨188840, by rfl⟩ : syracuseStep 4028597 = 377681) (by norm_num)
theorem B3020989 : Blo 1790096 3020989 := bbase (se 3 (by rfl) ⟨566435, by rfl⟩ : syracuseStep 3020989 = 1132871) (by norm_num)
theorem B5445845 : Blo 1790096 5445845 := bbase (se 7 (by rfl) ⟨63818, by rfl⟩ : syracuseStep 5445845 = 127637) (by norm_num)
theorem B2685149 : Blo 1790096 2685149 := bbase (se 3 (by rfl) ⟨503465, by rfl⟩ : syracuseStep 2685149 = 1006931) (by norm_num)
theorem B2685173 : Blo 1790096 2685173 := bbase (se 5 (by rfl) ⟨125867, by rfl⟩ : syracuseStep 2685173 = 251735) (by norm_num)
theorem B4028669 : Blo 1790096 4028669 := bbase (se 3 (by rfl) ⟨755375, by rfl⟩ : syracuseStep 4028669 = 1510751) (by norm_num)
theorem B2685197 : Blo 1790096 2685197 := bbase (se 3 (by rfl) ⟨503474, by rfl⟩ : syracuseStep 2685197 = 1006949) (by norm_num)
theorem B3021077 : Blo 1790096 3021077 := bbase (se 6 (by rfl) ⟨70806, by rfl⟩ : syracuseStep 3021077 = 141613) (by norm_num)
theorem B2685221 : Blo 1790096 2685221 := bbase (se 4 (by rfl) ⟨251739, by rfl⟩ : syracuseStep 2685221 = 503479) (by norm_num)
theorem B5101861 : Blo 1790096 5101861 := bbase (se 4 (by rfl) ⟨478299, by rfl⟩ : syracuseStep 5101861 = 956599) (by norm_num)
theorem B6797621 : Blo 1790096 6797621 := bbase (se 5 (by rfl) ⟨318638, by rfl⟩ : syracuseStep 6797621 = 637277) (by norm_num)
theorem B6453557 : Blo 1790096 6453557 := bbase (se 5 (by rfl) ⟨302510, by rfl⟩ : syracuseStep 6453557 = 605021) (by norm_num)
theorem B2685245 : Blo 1790096 2685245 := bbase (se 3 (by rfl) ⟨503483, by rfl⟩ : syracuseStep 2685245 = 1006967) (by norm_num)
theorem B2267453 : Blo 1790096 2267453 := bbase (se 3 (by rfl) ⟨425147, by rfl⟩ : syracuseStep 2267453 = 850295) (by norm_num)
theorem B4028741 : Blo 1790096 4028741 := bbase (se 4 (by rfl) ⟨377694, by rfl⟩ : syracuseStep 4028741 = 755389) (by norm_num)
theorem B2685269 : Blo 1790096 2685269 := bbase (se 10 (by rfl) ⟨3933, by rfl⟩ : syracuseStep 2685269 = 7867) (by norm_num)
theorem B2685293 : Blo 1790096 2685293 := bbase (se 3 (by rfl) ⟨503492, by rfl⟩ : syracuseStep 2685293 = 1006985) (by norm_num)
theorem B2267509 : Blo 1790096 2267509 := bbase (se 5 (by rfl) ⟨106289, by rfl⟩ : syracuseStep 2267509 = 212579) (by norm_num)
theorem B2685317 : Blo 1790096 2685317 := bbase (se 4 (by rfl) ⟨251748, by rfl⟩ : syracuseStep 2685317 = 503497) (by norm_num)
theorem B4028813 : Blo 1790096 4028813 := bbase (se 3 (by rfl) ⟨755402, by rfl⟩ : syracuseStep 4028813 = 1510805) (by norm_num)
theorem B3021205 : Blo 1790096 3021205 := bbase (se 6 (by rfl) ⟨70809, by rfl⟩ : syracuseStep 3021205 = 141619) (by norm_num)
theorem B2685341 : Blo 1790096 2685341 := bbase (se 3 (by rfl) ⟨503501, by rfl⟩ : syracuseStep 2685341 = 1007003) (by norm_num)
theorem B2685365 : Blo 1790096 2685365 := bbase (se 5 (by rfl) ⟨125876, by rfl⟩ : syracuseStep 2685365 = 251753) (by norm_num)
theorem B6453701 : Blo 1790096 6453701 := bbase (se 4 (by rfl) ⟨605034, by rfl⟩ : syracuseStep 6453701 = 1210069) (by norm_num)
theorem B5102021 : Blo 1790096 5102021 := bbase (se 4 (by rfl) ⟨478314, by rfl⟩ : syracuseStep 5102021 = 956629) (by norm_num)
theorem B2685389 : Blo 1790096 2685389 := bbase (se 3 (by rfl) ⟨503510, by rfl⟩ : syracuseStep 2685389 = 1007021) (by norm_num)
theorem B4028885 : Blo 1790096 4028885 := bbase (se 7 (by rfl) ⟨47213, by rfl⟩ : syracuseStep 4028885 = 94427) (by norm_num)
theorem B2267605 : Blo 1790096 2267605 := bbase (se 7 (by rfl) ⟨26573, by rfl⟩ : syracuseStep 2267605 = 53147) (by norm_num)
theorem B2685413 : Blo 1790096 2685413 := bbase (se 4 (by rfl) ⟨251757, by rfl⟩ : syracuseStep 2685413 = 503515) (by norm_num)
theorem B3021293 : Blo 1790096 3021293 := bbase (se 3 (by rfl) ⟨566492, by rfl⟩ : syracuseStep 3021293 = 1132985) (by norm_num)
theorem B2685437 : Blo 1790096 2685437 := bbase (se 3 (by rfl) ⟨503519, by rfl⟩ : syracuseStep 2685437 = 1007039) (by norm_num)
theorem B6044165 : Blo 1790096 6044165 := bbase (se 4 (by rfl) ⟨566640, by rfl⟩ : syracuseStep 6044165 = 1133281) (by norm_num)
theorem B2685461 : Blo 1790096 2685461 := bbase (se 6 (by rfl) ⟨62940, by rfl⟩ : syracuseStep 2685461 = 125881) (by norm_num)
theorem B4028957 : Blo 1790096 4028957 := bbase (se 3 (by rfl) ⟨755429, by rfl⟩ : syracuseStep 4028957 = 1510859) (by norm_num)
theorem B2685485 : Blo 1790096 2685485 := bbase (se 3 (by rfl) ⟨503528, by rfl⟩ : syracuseStep 2685485 = 1007057) (by norm_num)
theorem B2685509 : Blo 1790096 2685509 := bbase (se 4 (by rfl) ⟨251766, by rfl⟩ : syracuseStep 2685509 = 503533) (by norm_num)
theorem B2685533 : Blo 1790096 2685533 := bbase (se 3 (by rfl) ⟨503537, by rfl⟩ : syracuseStep 2685533 = 1007075) (by norm_num)
theorem B4029029 : Blo 1790096 4029029 := bbase (se 4 (by rfl) ⟨377721, by rfl⟩ : syracuseStep 4029029 = 755443) (by norm_num)
theorem B3021421 : Blo 1790096 3021421 := bbase (se 3 (by rfl) ⟨566516, by rfl⟩ : syracuseStep 3021421 = 1133033) (by norm_num)
theorem B2685557 : Blo 1790096 2685557 := bbase (se 5 (by rfl) ⟨125885, by rfl⟩ : syracuseStep 2685557 = 251771) (by norm_num)
theorem B2267777 : Blo 1790096 2267777 := bbase (se 2 (by rfl) ⟨850416, by rfl⟩ : syracuseStep 2267777 = 1700833) (by norm_num)
theorem B2685581 : Blo 1790096 2685581 := bbase (se 3 (by rfl) ⟨503546, by rfl⟩ : syracuseStep 2685581 = 1007093) (by norm_num)
theorem B2685605 : Blo 1790096 2685605 := bbase (se 4 (by rfl) ⟨251775, by rfl⟩ : syracuseStep 2685605 = 503551) (by norm_num)
theorem B4029101 : Blo 1790096 4029101 := bbase (se 3 (by rfl) ⟨755456, by rfl⟩ : syracuseStep 4029101 = 1510913) (by norm_num)
theorem B5102261 : Blo 1790096 5102261 := bbase (se 5 (by rfl) ⟨239168, by rfl⟩ : syracuseStep 5102261 = 478337) (by norm_num)
theorem B2267833 : Blo 1790096 2267833 := bbase (se 2 (by rfl) ⟨850437, by rfl⟩ : syracuseStep 2267833 = 1700875) (by norm_num)
theorem B2685629 : Blo 1790096 2685629 := bbase (se 3 (by rfl) ⟨503555, by rfl⟩ : syracuseStep 2685629 = 1007111) (by norm_num)
theorem B2013889 : Blo 1790096 2013889 := bbase (se 2 (by rfl) ⟨755208, by rfl⟩ : syracuseStep 2013889 = 1510417) (by norm_num)
theorem B3021509 : Blo 1790096 3021509 := bbase (se 4 (by rfl) ⟨283266, by rfl⟩ : syracuseStep 3021509 = 566533) (by norm_num)
theorem B2685653 : Blo 1790096 2685653 := bbase (se 7 (by rfl) ⟨31472, by rfl⟩ : syracuseStep 2685653 = 62945) (by norm_num)
theorem B10205909 : Blo 1790096 10205909 := bbase (se 7 (by rfl) ⟨119600, by rfl⟩ : syracuseStep 10205909 = 239201) (by norm_num)
theorem B2013925 : Blo 1790096 2013925 := bbase (se 4 (by rfl) ⟨188805, by rfl⟩ : syracuseStep 2013925 = 377611) (by norm_num)
theorem B6453989 : Blo 1790096 6453989 := bbase (se 4 (by rfl) ⟨605061, by rfl⟩ : syracuseStep 6453989 = 1210123) (by norm_num)
theorem B2685677 : Blo 1790096 2685677 := bbase (se 3 (by rfl) ⟨503564, by rfl⟩ : syracuseStep 2685677 = 1007129) (by norm_num)
theorem B4029173 : Blo 1790096 4029173 := bbase (se 5 (by rfl) ⟨188867, by rfl⟩ : syracuseStep 4029173 = 377735) (by norm_num)
theorem B2685701 : Blo 1790096 2685701 := bbase (se 4 (by rfl) ⟨251784, by rfl⟩ : syracuseStep 2685701 = 503569) (by norm_num)
theorem B2013961 : Blo 1790096 2013961 := bbase (se 2 (by rfl) ⟨755235, by rfl⟩ : syracuseStep 2013961 = 1510471) (by norm_num)
theorem B2267929 : Blo 1790096 2267929 := bbase (se 2 (by rfl) ⟨850473, by rfl⟩ : syracuseStep 2267929 = 1700947) (by norm_num)
theorem B2685725 : Blo 1790096 2685725 := bbase (se 3 (by rfl) ⟨503573, by rfl⟩ : syracuseStep 2685725 = 1007147) (by norm_num)
theorem B9067301 : Blo 1790096 9067301 := bbase (se 4 (by rfl) ⟨850059, by rfl⟩ : syracuseStep 9067301 = 1700119) (by norm_num)
theorem B2013997 : Blo 1790096 2013997 := bbase (se 3 (by rfl) ⟨377624, by rfl⟩ : syracuseStep 2013997 = 755249) (by norm_num)
theorem B2685749 : Blo 1790096 2685749 := bbase (se 5 (by rfl) ⟨125894, by rfl⟩ : syracuseStep 2685749 = 251789) (by norm_num)
theorem B4029245 : Blo 1790096 4029245 := bbase (se 3 (by rfl) ⟨755483, by rfl⟩ : syracuseStep 4029245 = 1510967) (by norm_num)
theorem B3021637 : Blo 1790096 3021637 := bbase (se 4 (by rfl) ⟨283278, by rfl⟩ : syracuseStep 3021637 = 566557) (by norm_num)
theorem B2685773 : Blo 1790096 2685773 := bbase (se 3 (by rfl) ⟨503582, by rfl⟩ : syracuseStep 2685773 = 1007165) (by norm_num)
theorem B2014033 : Blo 1790096 2014033 := bbase (se 2 (by rfl) ⟨755262, by rfl⟩ : syracuseStep 2014033 = 1510525) (by norm_num)
theorem B10197845 : Blo 1790096 10197845 := bbase (se 9 (by rfl) ⟨29876, by rfl⟩ : syracuseStep 10197845 = 59753) (by norm_num)
theorem B2685797 : Blo 1790096 2685797 := bbase (se 4 (by rfl) ⟨251793, by rfl⟩ : syracuseStep 2685797 = 503587) (by norm_num)
theorem B2014069 : Blo 1790096 2014069 := bbase (se 5 (by rfl) ⟨94409, by rfl⟩ : syracuseStep 2014069 = 188819) (by norm_num)
theorem B5102453 : Blo 1790096 5102453 := bbase (se 5 (by rfl) ⟨239177, by rfl⟩ : syracuseStep 5102453 = 478355) (by norm_num)
theorem B2685821 : Blo 1790096 2685821 := bbase (se 3 (by rfl) ⟨503591, by rfl⟩ : syracuseStep 2685821 = 1007183) (by norm_num)
theorem B3824509 : Blo 1790096 3824509 := bbase (se 3 (by rfl) ⟨717095, by rfl⟩ : syracuseStep 3824509 = 1434191) (by norm_num)
theorem B3447677 : Blo 1790096 3447677 := bbase (se 3 (by rfl) ⟨646439, by rfl⟩ : syracuseStep 3447677 = 1292879) (by norm_num)
theorem B4029317 : Blo 1790096 4029317 := bbase (se 4 (by rfl) ⟨377748, by rfl⟩ : syracuseStep 4029317 = 755497) (by norm_num)
theorem B2685845 : Blo 1790096 2685845 := bbase (se 6 (by rfl) ⟨62949, by rfl⟩ : syracuseStep 2685845 = 125899) (by norm_num)
theorem B2014105 : Blo 1790096 2014105 := bbase (se 2 (by rfl) ⟨755289, by rfl⟩ : syracuseStep 2014105 = 1510579) (by norm_num)
theorem B3021725 : Blo 1790096 3021725 := bbase (se 3 (by rfl) ⟨566573, by rfl⟩ : syracuseStep 3021725 = 1133147) (by norm_num)
theorem B2685869 : Blo 1790096 2685869 := bbase (se 3 (by rfl) ⟨503600, by rfl⟩ : syracuseStep 2685869 = 1007201) (by norm_num)
theorem B6044597 : Blo 1790096 6044597 := bbase (se 5 (by rfl) ⟨283340, by rfl⟩ : syracuseStep 6044597 = 566681) (by norm_num)
theorem B2014141 : Blo 1790096 2014141 := bbase (se 3 (by rfl) ⟨377651, by rfl⟩ : syracuseStep 2014141 = 755303) (by norm_num)
theorem B2685893 : Blo 1790096 2685893 := bbase (se 4 (by rfl) ⟨251802, by rfl⟩ : syracuseStep 2685893 = 503605) (by norm_num)
theorem B2268101 : Blo 1790096 2268101 := bbase (se 4 (by rfl) ⟨212634, by rfl⟩ : syracuseStep 2268101 = 425269) (by norm_num)
theorem B4029389 : Blo 1790096 4029389 := bbase (se 3 (by rfl) ⟨755510, by rfl⟩ : syracuseStep 4029389 = 1511021) (by norm_num)
theorem B2685917 : Blo 1790096 2685917 := bbase (se 3 (by rfl) ⟨503609, by rfl⟩ : syracuseStep 2685917 = 1007219) (by norm_num)
theorem B2014177 : Blo 1790096 2014177 := bbase (se 2 (by rfl) ⟨755316, by rfl⟩ : syracuseStep 2014177 = 1510633) (by norm_num)
theorem B2685941 : Blo 1790096 2685941 := bbase (se 5 (by rfl) ⟨125903, by rfl⟩ : syracuseStep 2685941 = 251807) (by norm_num)
theorem B2014213 : Blo 1790096 2014213 := bbase (se 4 (by rfl) ⟨188832, by rfl⟩ : syracuseStep 2014213 = 377665) (by norm_num)
theorem B2685965 : Blo 1790096 2685965 := bbase (se 3 (by rfl) ⟨503618, by rfl⟩ : syracuseStep 2685965 = 1007237) (by norm_num)
theorem B3824653 : Blo 1790096 3824653 := bbase (se 3 (by rfl) ⟨717122, by rfl⟩ : syracuseStep 3824653 = 1434245) (by norm_num)
theorem B4029461 : Blo 1790096 4029461 := bbase (se 6 (by rfl) ⟨94440, by rfl⟩ : syracuseStep 4029461 = 188881) (by norm_num)
theorem B3021853 : Blo 1790096 3021853 := bbase (se 3 (by rfl) ⟨566597, by rfl⟩ : syracuseStep 3021853 = 1133195) (by norm_num)
theorem B2685989 : Blo 1790096 2685989 := bbase (se 4 (by rfl) ⟨251811, by rfl⟩ : syracuseStep 2685989 = 503623) (by norm_num)
theorem B2014249 : Blo 1790096 2014249 := bbase (se 2 (by rfl) ⟨755343, by rfl⟩ : syracuseStep 2014249 = 1510687) (by norm_num)
theorem B2686013 : Blo 1790096 2686013 := bbase (se 3 (by rfl) ⟨503627, by rfl⟩ : syracuseStep 2686013 = 1007255) (by norm_num)
theorem B2014285 : Blo 1790096 2014285 := bbase (se 3 (by rfl) ⟨377678, by rfl⟩ : syracuseStep 2014285 = 755357) (by norm_num)
theorem B2686037 : Blo 1790096 2686037 := bbase (se 8 (by rfl) ⟨15738, by rfl⟩ : syracuseStep 2686037 = 31477) (by norm_num)
theorem B4029533 : Blo 1790096 4029533 := bbase (se 3 (by rfl) ⟨755537, by rfl⟩ : syracuseStep 4029533 = 1511075) (by norm_num)
theorem B4594789 : Blo 1790096 4594789 := bbase (se 4 (by rfl) ⟨430761, by rfl⟩ : syracuseStep 4594789 = 861523) (by norm_num)
theorem B2686061 : Blo 1790096 2686061 := bbase (se 3 (by rfl) ⟨503636, by rfl⟩ : syracuseStep 2686061 = 1007273) (by norm_num)
theorem B2014321 : Blo 1790096 2014321 := bbase (se 2 (by rfl) ⟨755370, by rfl⟩ : syracuseStep 2014321 = 1510741) (by norm_num)
theorem B3398773 : Blo 1790096 3398773 := bbase (se 5 (by rfl) ⟨159317, by rfl⟩ : syracuseStep 3398773 = 318635) (by norm_num)
theorem B3021941 : Blo 1790096 3021941 := bbase (se 5 (by rfl) ⟨141653, by rfl⟩ : syracuseStep 3021941 = 283307) (by norm_num)
theorem B2686085 : Blo 1790096 2686085 := bbase (se 4 (by rfl) ⟨251820, by rfl⟩ : syracuseStep 2686085 = 503641) (by norm_num)
theorem B2014357 : Blo 1790096 2014357 := bbase (se 6 (by rfl) ⟨47211, by rfl⟩ : syracuseStep 2014357 = 94423) (by norm_num)
theorem B2686109 : Blo 1790096 2686109 := bbase (se 3 (by rfl) ⟨503645, by rfl⟩ : syracuseStep 2686109 = 1007291) (by norm_num)
theorem B4029605 : Blo 1790096 4029605 := bbase (se 4 (by rfl) ⟨377775, by rfl⟩ : syracuseStep 4029605 = 755551) (by norm_num)
theorem B2686133 : Blo 1790096 2686133 := bbase (se 5 (by rfl) ⟨125912, by rfl⟩ : syracuseStep 2686133 = 251825) (by norm_num)
theorem B2014393 : Blo 1790096 2014393 := bbase (se 2 (by rfl) ⟨755397, by rfl⟩ : syracuseStep 2014393 = 1510795) (by norm_num)
theorem B2686157 : Blo 1790096 2686157 := bbase (se 3 (by rfl) ⟨503654, by rfl⟩ : syracuseStep 2686157 = 1007309) (by norm_num)
theorem B2014429 : Blo 1790096 2014429 := bbase (se 3 (by rfl) ⟨377705, by rfl⟩ : syracuseStep 2014429 = 755411) (by norm_num)
theorem B2686181 : Blo 1790096 2686181 := bbase (se 4 (by rfl) ⟨251829, by rfl⟩ : syracuseStep 2686181 = 503659) (by norm_num)
theorem B4029677 : Blo 1790096 4029677 := bbase (se 3 (by rfl) ⟨755564, by rfl⟩ : syracuseStep 4029677 = 1511129) (by norm_num)
theorem B3022069 : Blo 1790096 3022069 := bbase (se 5 (by rfl) ⟨141659, by rfl⟩ : syracuseStep 3022069 = 283319) (by norm_num)
theorem B2686205 : Blo 1790096 2686205 := bbase (se 3 (by rfl) ⟨503663, by rfl⟩ : syracuseStep 2686205 = 1007327) (by norm_num)
theorem B2014465 : Blo 1790096 2014465 := bbase (se 2 (by rfl) ⟨755424, by rfl⟩ : syracuseStep 2014465 = 1510849) (by norm_num)
theorem B3398917 : Blo 1790096 3398917 := bbase (se 4 (by rfl) ⟨318648, by rfl⟩ : syracuseStep 3398917 = 637297) (by norm_num)
theorem B2686229 : Blo 1790096 2686229 := bbase (se 6 (by rfl) ⟨62958, by rfl⟩ : syracuseStep 2686229 = 125917) (by norm_num)
theorem B2014501 : Blo 1790096 2014501 := bbase (se 4 (by rfl) ⟨188859, by rfl⟩ : syracuseStep 2014501 = 377719) (by norm_num)
theorem B2686253 : Blo 1790096 2686253 := bbase (se 3 (by rfl) ⟨503672, by rfl⟩ : syracuseStep 2686253 = 1007345) (by norm_num)
theorem B4029749 : Blo 1790096 4029749 := bbase (se 5 (by rfl) ⟨188894, by rfl⟩ : syracuseStep 4029749 = 377789) (by norm_num)
theorem B5242165 : Blo 1790096 5242165 := bbase (se 5 (by rfl) ⟨245726, by rfl⟩ : syracuseStep 5242165 = 491453) (by norm_num)
theorem B2686277 : Blo 1790096 2686277 := bbase (se 4 (by rfl) ⟨251838, by rfl⟩ : syracuseStep 2686277 = 503677) (by norm_num)
theorem B2014537 : Blo 1790096 2014537 := bbase (se 2 (by rfl) ⟨755451, by rfl⟩ : syracuseStep 2014537 = 1510903) (by norm_num)
theorem B3022157 : Blo 1790096 3022157 := bbase (se 3 (by rfl) ⟨566654, by rfl⟩ : syracuseStep 3022157 = 1133309) (by norm_num)
theorem B2686301 : Blo 1790096 2686301 := bbase (se 3 (by rfl) ⟨503681, by rfl⟩ : syracuseStep 2686301 = 1007363) (by norm_num)
theorem B6045029 : Blo 1790096 6045029 := bbase (se 4 (by rfl) ⟨566721, by rfl⟩ : syracuseStep 6045029 = 1133443) (by norm_num)
theorem B2014573 : Blo 1790096 2014573 := bbase (se 3 (by rfl) ⟨377732, by rfl⟩ : syracuseStep 2014573 = 755465) (by norm_num)
theorem B2686325 : Blo 1790096 2686325 := bbase (se 5 (by rfl) ⟨125921, by rfl⟩ : syracuseStep 2686325 = 251843) (by norm_num)
theorem B4029821 : Blo 1790096 4029821 := bbase (se 3 (by rfl) ⟨755591, by rfl⟩ : syracuseStep 4029821 = 1511183) (by norm_num)
theorem B3825029 : Blo 1790096 3825029 := bbase (se 4 (by rfl) ⟨358596, by rfl⟩ : syracuseStep 3825029 = 717193) (by norm_num)
theorem B2686349 : Blo 1790096 2686349 := bbase (se 3 (by rfl) ⟨503690, by rfl⟩ : syracuseStep 2686349 = 1007381) (by norm_num)
theorem B2014609 : Blo 1790096 2014609 := bbase (se 2 (by rfl) ⟨755478, by rfl⟩ : syracuseStep 2014609 = 1510957) (by norm_num)
theorem B3399077 : Blo 1790096 3399077 := bbase (se 4 (by rfl) ⟨318663, by rfl⟩ : syracuseStep 3399077 = 637327) (by norm_num)
theorem B2686373 : Blo 1790096 2686373 := bbase (se 4 (by rfl) ⟨251847, by rfl⟩ : syracuseStep 2686373 = 503695) (by norm_num)
theorem B2014645 : Blo 1790096 2014645 := bbase (se 5 (by rfl) ⟨94436, by rfl⟩ : syracuseStep 2014645 = 188873) (by norm_num)
theorem B2686397 : Blo 1790096 2686397 := bbase (se 3 (by rfl) ⟨503699, by rfl⟩ : syracuseStep 2686397 = 1007399) (by norm_num)
theorem B4029893 : Blo 1790096 4029893 := bbase (se 4 (by rfl) ⟨377802, by rfl⟩ : syracuseStep 4029893 = 755605) (by norm_num)
theorem B6544837 : Blo 1790096 6544837 := bbase (se 4 (by rfl) ⟨613578, by rfl⟩ : syracuseStep 6544837 = 1227157) (by norm_num)
theorem B3022285 : Blo 1790096 3022285 := bbase (se 3 (by rfl) ⟨566678, by rfl⟩ : syracuseStep 3022285 = 1133357) (by norm_num)
theorem B2686421 : Blo 1790096 2686421 := bbase (se 7 (by rfl) ⟨31481, by rfl⟩ : syracuseStep 2686421 = 62963) (by norm_num)
theorem B2014681 : Blo 1790096 2014681 := bbase (se 2 (by rfl) ⟨755505, by rfl⟩ : syracuseStep 2014681 = 1511011) (by norm_num)
theorem B2686445 : Blo 1790096 2686445 := bbase (se 3 (by rfl) ⟨503708, by rfl⟩ : syracuseStep 2686445 = 1007417) (by norm_num)
theorem B2014717 : Blo 1790096 2014717 := bbase (se 3 (by rfl) ⟨377759, by rfl⟩ : syracuseStep 2014717 = 755519) (by norm_num)
theorem B2686469 : Blo 1790096 2686469 := bbase (se 4 (by rfl) ⟨251856, by rfl⟩ : syracuseStep 2686469 = 503713) (by norm_num)
theorem B4029965 : Blo 1790096 4029965 := bbase (se 3 (by rfl) ⟨755618, by rfl⟩ : syracuseStep 4029965 = 1511237) (by norm_num)
theorem B2686493 : Blo 1790096 2686493 := bbase (se 3 (by rfl) ⟨503717, by rfl⟩ : syracuseStep 2686493 = 1007435) (by norm_num)
theorem B2014753 : Blo 1790096 2014753 := bbase (se 2 (by rfl) ⟨755532, by rfl⟩ : syracuseStep 2014753 = 1511065) (by norm_num)
theorem B3022373 : Blo 1790096 3022373 := bbase (se 4 (by rfl) ⟨283347, by rfl⟩ : syracuseStep 3022373 = 566695) (by norm_num)
theorem B3399221 : Blo 1790096 3399221 := bbase (se 5 (by rfl) ⟨159338, by rfl⟩ : syracuseStep 3399221 = 318677) (by norm_num)
theorem B2686517 : Blo 1790096 2686517 := bbase (se 5 (by rfl) ⟨125930, by rfl⟩ : syracuseStep 2686517 = 251861) (by norm_num)
theorem B2014789 : Blo 1790096 2014789 := bbase (se 4 (by rfl) ⟨188886, by rfl⟩ : syracuseStep 2014789 = 377773) (by norm_num)
theorem B2760269 : Blo 1790096 2760269 := bbase (se 3 (by rfl) ⟨517550, by rfl⟩ : syracuseStep 2760269 = 1035101) (by norm_num)
theorem B2686541 : Blo 1790096 2686541 := bbase (se 3 (by rfl) ⟨503726, by rfl⟩ : syracuseStep 2686541 = 1007453) (by norm_num)
theorem B4030037 : Blo 1790096 4030037 := bbase (se 8 (by rfl) ⟨23613, by rfl⟩ : syracuseStep 4030037 = 47227) (by norm_num)
theorem B2686565 : Blo 1790096 2686565 := bbase (se 4 (by rfl) ⟨251865, by rfl⟩ : syracuseStep 2686565 = 503731) (by norm_num)
theorem B2014825 : Blo 1790096 2014825 := bbase (se 2 (by rfl) ⟨755559, by rfl⟩ : syracuseStep 2014825 = 1511119) (by norm_num)
theorem B2686589 : Blo 1790096 2686589 := bbase (se 3 (by rfl) ⟨503735, by rfl⟩ : syracuseStep 2686589 = 1007471) (by norm_num)
theorem B2014861 : Blo 1790096 2014861 := bbase (se 3 (by rfl) ⟨377786, by rfl⟩ : syracuseStep 2014861 = 755573) (by norm_num)
theorem B2686613 : Blo 1790096 2686613 := bbase (se 6 (by rfl) ⟨62967, by rfl⟩ : syracuseStep 2686613 = 125935) (by norm_num)
theorem B4030109 : Blo 1790096 4030109 := bbase (se 3 (by rfl) ⟨755645, by rfl⟩ : syracuseStep 4030109 = 1511291) (by norm_num)
theorem B3022501 : Blo 1790096 3022501 := bbase (se 4 (by rfl) ⟨283359, by rfl⟩ : syracuseStep 3022501 = 566719) (by norm_num)
theorem B2686637 : Blo 1790096 2686637 := bbase (se 3 (by rfl) ⟨503744, by rfl⟩ : syracuseStep 2686637 = 1007489) (by norm_num)
theorem B2014897 : Blo 1790096 2014897 := bbase (se 2 (by rfl) ⟨755586, by rfl⟩ : syracuseStep 2014897 = 1511173) (by norm_num)
theorem B2686661 : Blo 1790096 2686661 := bbase (se 4 (by rfl) ⟨251874, by rfl⟩ : syracuseStep 2686661 = 503749) (by norm_num)
theorem B2014933 : Blo 1790096 2014933 := bbase (se 7 (by rfl) ⟨23612, by rfl⟩ : syracuseStep 2014933 = 47225) (by norm_num)
theorem B2686685 : Blo 1790096 2686685 := bbase (se 3 (by rfl) ⟨503753, by rfl⟩ : syracuseStep 2686685 = 1007507) (by norm_num)
theorem B4030181 : Blo 1790096 4030181 := bbase (se 4 (by rfl) ⟨377829, by rfl⟩ : syracuseStep 4030181 = 755659) (by norm_num)
theorem B3825397 : Blo 1790096 3825397 := bbase (se 5 (by rfl) ⟨179315, by rfl⟩ : syracuseStep 3825397 = 358631) (by norm_num)
theorem B2686709 : Blo 1790096 2686709 := bbase (se 5 (by rfl) ⟨125939, by rfl⟩ : syracuseStep 2686709 = 251879) (by norm_num)
theorem B2014969 : Blo 1790096 2014969 := bbase (se 2 (by rfl) ⟨755613, by rfl⟩ : syracuseStep 2014969 = 1511227) (by norm_num)
theorem B3022589 : Blo 1790096 3022589 := bbase (se 3 (by rfl) ⟨566735, by rfl⟩ : syracuseStep 3022589 = 1133471) (by norm_num)
theorem B2686733 : Blo 1790096 2686733 := bbase (se 3 (by rfl) ⟨503762, by rfl⟩ : syracuseStep 2686733 = 1007525) (by norm_num)
theorem B6045461 : Blo 1790096 6045461 := bbase (se 6 (by rfl) ⟨141690, by rfl⟩ : syracuseStep 6045461 = 283381) (by norm_num)
theorem B2015005 : Blo 1790096 2015005 := bbase (se 3 (by rfl) ⟨377813, by rfl⟩ : syracuseStep 2015005 = 755627) (by norm_num)
theorem B2686757 : Blo 1790096 2686757 := bbase (se 4 (by rfl) ⟨251883, by rfl⟩ : syracuseStep 2686757 = 503767) (by norm_num)
theorem B4030253 : Blo 1790096 4030253 := bbase (se 3 (by rfl) ⟨755672, by rfl⟩ : syracuseStep 4030253 = 1511345) (by norm_num)
theorem B7757621 : Blo 1790096 7757621 := bbase (se 5 (by rfl) ⟨363638, by rfl⟩ : syracuseStep 7757621 = 727277) (by norm_num)
theorem B10485557 : Blo 1790096 10485557 := bbase (se 5 (by rfl) ⟨491510, by rfl⟩ : syracuseStep 10485557 = 983021) (by norm_num)
theorem B2686781 : Blo 1790096 2686781 := bbase (se 3 (by rfl) ⟨503771, by rfl⟩ : syracuseStep 2686781 = 1007543) (by norm_num)
theorem B2015041 : Blo 1790096 2015041 := bbase (se 2 (by rfl) ⟨755640, by rfl⟩ : syracuseStep 2015041 = 1511281) (by norm_num)
theorem B3399509 : Blo 1790096 3399509 := bbase (se 9 (by rfl) ⟨9959, by rfl⟩ : syracuseStep 3399509 = 19919) (by norm_num)
theorem B2686805 : Blo 1790096 2686805 := bbase (se 9 (by rfl) ⟨7871, by rfl⟩ : syracuseStep 2686805 = 15743) (by norm_num)
theorem B3227485 : Blo 1790096 3227485 := bbase (se 3 (by rfl) ⟨605153, by rfl⟩ : syracuseStep 3227485 = 1210307) (by norm_num)
theorem B2015077 : Blo 1790096 2015077 := bbase (se 4 (by rfl) ⟨188913, by rfl⟩ : syracuseStep 2015077 = 377827) (by norm_num)
theorem B2686829 : Blo 1790096 2686829 := bbase (se 3 (by rfl) ⟨503780, by rfl⟩ : syracuseStep 2686829 = 1007561) (by norm_num)
theorem B4030325 : Blo 1790096 4030325 := bbase (se 5 (by rfl) ⟨188921, by rfl⟩ : syracuseStep 4030325 = 377843) (by norm_num)
theorem B3022717 : Blo 1790096 3022717 := bbase (se 3 (by rfl) ⟨566759, by rfl⟩ : syracuseStep 3022717 = 1133519) (by norm_num)
theorem B7651205 : Blo 1790096 7651205 := bbase (se 4 (by rfl) ⟨717300, by rfl⟩ : syracuseStep 7651205 = 1434601) (by norm_num)
theorem B2686853 : Blo 1790096 2686853 := bbase (se 4 (by rfl) ⟨251892, by rfl⟩ : syracuseStep 2686853 = 503785) (by norm_num)
theorem B2015113 : Blo 1790096 2015113 := bbase (se 2 (by rfl) ⟨755667, by rfl⟩ : syracuseStep 2015113 = 1511335) (by norm_num)
theorem B18628501 : Blo 1790096 18628501 := bbase (se 6 (by rfl) ⟨436605, by rfl⟩ : syracuseStep 18628501 = 873211) (by norm_num)
theorem B2686877 : Blo 1790096 2686877 := bbase (se 3 (by rfl) ⟨503789, by rfl⟩ : syracuseStep 2686877 = 1007579) (by norm_num)
theorem B3063725 : Blo 1790096 3063725 := bbase (se 3 (by rfl) ⟨574448, by rfl⟩ : syracuseStep 3063725 = 1148897) (by norm_num)
theorem B2015149 : Blo 1790096 2015149 := bbase (se 3 (by rfl) ⟨377840, by rfl⟩ : syracuseStep 2015149 = 755681) (by norm_num)
theorem B2686901 : Blo 1790096 2686901 := bbase (se 5 (by rfl) ⟨125948, by rfl⟩ : syracuseStep 2686901 = 251897) (by norm_num)
theorem B4030397 : Blo 1790096 4030397 := bbase (se 3 (by rfl) ⟨755699, by rfl⟩ : syracuseStep 4030397 = 1511399) (by norm_num)
theorem B2686925 : Blo 1790096 2686925 := bbase (se 3 (by rfl) ⟨503798, by rfl⟩ : syracuseStep 2686925 = 1007597) (by norm_num)
theorem B2015185 : Blo 1790096 2015185 := bbase (se 2 (by rfl) ⟨755694, by rfl⟩ : syracuseStep 2015185 = 1511389) (by norm_num)
theorem B3022805 : Blo 1790096 3022805 := bbase (se 7 (by rfl) ⟨35423, by rfl⟩ : syracuseStep 3022805 = 70847) (by norm_num)
theorem B2686949 : Blo 1790096 2686949 := bbase (se 4 (by rfl) ⟨251901, by rfl⟩ : syracuseStep 2686949 = 503803) (by norm_num)
theorem B3399661 : Blo 1790096 3399661 := bbase (se 3 (by rfl) ⟨637436, by rfl⟩ : syracuseStep 3399661 = 1274873) (by norm_num)
theorem B2015221 : Blo 1790096 2015221 := bbase (se 5 (by rfl) ⟨94463, by rfl⟩ : syracuseStep 2015221 = 188927) (by norm_num)
theorem B2686973 : Blo 1790096 2686973 := bbase (se 3 (by rfl) ⟨503807, by rfl⟩ : syracuseStep 2686973 = 1007615) (by norm_num)
theorem B2686979 : Blo 1790096 2686979 := bstep (se 1 (by rfl) ⟨2015234, by rfl⟩ : syracuseStep 2686979 = 4030469) B4030469
theorem B2687009 : Blo 1790096 2687009 := bstep (se 2 (by rfl) ⟨1007628, by rfl⟩ : syracuseStep 2687009 = 2015257) B2015257
theorem B6045731 : Blo 1790096 6045731 := bstep (se 1 (by rfl) ⟨4534298, by rfl⟩ : syracuseStep 6045731 = 9068597) B9068597
theorem B3825713 : Blo 1790096 3825713 := bstep (se 2 (by rfl) ⟨1434642, by rfl⟩ : syracuseStep 3825713 = 2869285) B2869285
theorem B2687027 : Blo 1790096 2687027 := bstep (se 1 (by rfl) ⟨2015270, by rfl⟩ : syracuseStep 2687027 = 4030541) B4030541
theorem B3022913 : Blo 1790096 3022913 := bstep (se 2 (by rfl) ⟨1133592, by rfl⟩ : syracuseStep 3022913 = 2267185) B2267185
theorem B3629137 : Blo 1790096 3629137 := bstep (se 2 (by rfl) ⟨1360926, by rfl⟩ : syracuseStep 3629137 = 2721853) B2721853
theorem B2687057 : Blo 1790096 2687057 := bstep (se 2 (by rfl) ⟨1007646, by rfl⟩ : syracuseStep 2687057 = 2015293) B2015293
theorem B2687075 : Blo 1790096 2687075 := bstep (se 1 (by rfl) ⟨2015306, by rfl⟩ : syracuseStep 2687075 = 4030613) B4030613
theorem B9683057 : Blo 1790096 9683057 := bstep (se 2 (by rfl) ⟨3631146, by rfl⟩ : syracuseStep 9683057 = 7262293) B7262293
theorem B4030577 : Blo 1790096 4030577 := bstep (se 2 (by rfl) ⟨1511466, by rfl⟩ : syracuseStep 4030577 = 3022933) B3022933
theorem B2015347 : Blo 1790096 2015347 := bstep (se 1 (by rfl) ⟨1511510, by rfl⟩ : syracuseStep 2015347 = 3023021) B3023021
theorem B2687105 : Blo 1790096 2687105 := bstep (se 2 (by rfl) ⟨1007664, by rfl⟩ : syracuseStep 2687105 = 2015329) B2015329
theorem B4030595 : Blo 1790096 4030595 := bstep (se 1 (by rfl) ⟨3022946, by rfl⟩ : syracuseStep 4030595 = 6045893) B6045893
theorem B2687123 : Blo 1790096 2687123 := bstep (se 1 (by rfl) ⟨2015342, by rfl⟩ : syracuseStep 2687123 = 4030685) B4030685
theorem B3629233 : Blo 1790096 3629233 := bstep (se 2 (by rfl) ⟨1360962, by rfl⟩ : syracuseStep 3629233 = 2721925) B2721925
theorem B2687153 : Blo 1790096 2687153 := bstep (se 2 (by rfl) ⟨1007682, by rfl⟩ : syracuseStep 2687153 = 2015365) B2015365
theorem B8609969 : Blo 1790096 8609969 := bstep (se 2 (by rfl) ⟨3228738, by rfl⟩ : syracuseStep 8609969 = 6457477) B6457477
theorem B3023041 : Blo 1790096 3023041 := bstep (se 2 (by rfl) ⟨1133640, by rfl⟩ : syracuseStep 3023041 = 2267281) B2267281
theorem B2687171 : Blo 1790096 2687171 := bstep (se 1 (by rfl) ⟨2015378, by rfl⟩ : syracuseStep 2687171 = 4030757) B4030757
theorem B6799565 : Blo 1790096 6799565 := bstep (se 3 (by rfl) ⟨1274918, by rfl⟩ : syracuseStep 6799565 = 2549837) B2549837
theorem B3399889 : Blo 1790096 3399889 := bstep (se 2 (by rfl) ⟨1274958, by rfl⟩ : syracuseStep 3399889 = 2549917) B2549917
theorem B2687201 : Blo 1790096 2687201 := bstep (se 2 (by rfl) ⟨1007700, by rfl⟩ : syracuseStep 2687201 = 2015401) B2015401
theorem B3023075 : Blo 1790096 3023075 := bstep (se 1 (by rfl) ⟨2267306, by rfl⟩ : syracuseStep 3023075 = 4534613) B4534613
theorem B2687219 : Blo 1790096 2687219 := bstep (se 1 (by rfl) ⟨2015414, by rfl⟩ : syracuseStep 2687219 = 4030829) B4030829
theorem B2015491 : Blo 1790096 2015491 := bstep (se 1 (by rfl) ⟨1511618, by rfl⟩ : syracuseStep 2015491 = 3023237) B3023237
theorem B2687249 : Blo 1790096 2687249 := bstep (se 2 (by rfl) ⟨1007718, by rfl⟩ : syracuseStep 2687249 = 2015437) B2015437
theorem B2867491 : Blo 1790096 2867491 := bstep (se 1 (by rfl) ⟨2150618, by rfl⟩ : syracuseStep 2867491 = 4301237) B4301237
theorem B7258403 : Blo 1790096 7258403 := bstep (se 1 (by rfl) ⟨5443802, by rfl⟩ : syracuseStep 7258403 = 10887605) B10887605
theorem B2687267 : Blo 1790096 2687267 := bstep (se 1 (by rfl) ⟨2015450, by rfl⟩ : syracuseStep 2687267 = 4030901) B4030901
theorem B6046001 : Blo 1790096 6046001 := bstep (se 2 (by rfl) ⟨2267250, by rfl⟩ : syracuseStep 6046001 = 4534501) B4534501
theorem B2687297 : Blo 1790096 2687297 := bstep (se 2 (by rfl) ⟨1007736, by rfl⟩ : syracuseStep 2687297 = 2015473) B2015473
theorem B2687315 : Blo 1790096 2687315 := bstep (se 1 (by rfl) ⟨2015486, by rfl⟩ : syracuseStep 2687315 = 4030973) B4030973
theorem B3023203 : Blo 1790096 3023203 := bstep (se 1 (by rfl) ⟨2267402, by rfl⟩ : syracuseStep 3023203 = 4534805) B4534805
theorem B3400049 : Blo 1790096 3400049 := bstep (se 2 (by rfl) ⟨1275018, by rfl⟩ : syracuseStep 3400049 = 2550037) B2550037
theorem B2687345 : Blo 1790096 2687345 := bstep (se 2 (by rfl) ⟨1007754, by rfl⟩ : syracuseStep 2687345 = 2015509) B2015509
theorem B2687363 : Blo 1790096 2687363 := bstep (se 1 (by rfl) ⟨2015522, by rfl⟩ : syracuseStep 2687363 = 4031045) B4031045
theorem B4030865 : Blo 1790096 4030865 := bstep (se 2 (by rfl) ⟨1511574, by rfl⟩ : syracuseStep 4030865 = 3023149) B3023149
theorem B2015635 : Blo 1790096 2015635 := bstep (se 1 (by rfl) ⟨1511726, by rfl⟩ : syracuseStep 2015635 = 3023453) B3023453
theorem B2687393 : Blo 1790096 2687393 := bstep (se 2 (by rfl) ⟨1007772, by rfl⟩ : syracuseStep 2687393 = 2015545) B2015545
theorem B7258531 : Blo 1790096 7258531 := bstep (se 1 (by rfl) ⟨5443898, by rfl⟩ : syracuseStep 7258531 = 10887797) B10887797
theorem B4030883 : Blo 1790096 4030883 := bstep (se 1 (by rfl) ⟨3023162, by rfl⟩ : syracuseStep 4030883 = 6046325) B6046325
theorem B2687411 : Blo 1790096 2687411 := bstep (se 1 (by rfl) ⟨2015558, by rfl⟩ : syracuseStep 2687411 = 4031117) B4031117
theorem B2687441 : Blo 1790096 2687441 := bstep (se 2 (by rfl) ⟨1007790, by rfl⟩ : syracuseStep 2687441 = 2015581) B2015581
theorem B2687459 : Blo 1790096 2687459 := bstep (se 1 (by rfl) ⟨2015594, by rfl⟩ : syracuseStep 2687459 = 4031189) B4031189
theorem B3023345 : Blo 1790096 3023345 := bstep (se 2 (by rfl) ⟨1133754, by rfl⟩ : syracuseStep 3023345 = 2267509) B2267509
theorem B2687489 : Blo 1790096 2687489 := bstep (se 2 (by rfl) ⟨1007808, by rfl⟩ : syracuseStep 2687489 = 2015617) B2015617
theorem B2687507 : Blo 1790096 2687507 := bstep (se 1 (by rfl) ⟨2015630, by rfl⟩ : syracuseStep 2687507 = 4031261) B4031261
theorem B2015779 : Blo 1790096 2015779 := bstep (se 1 (by rfl) ⟨1511834, by rfl⟩ : syracuseStep 2015779 = 3023669) B3023669
theorem B3826225 : Blo 1790096 3826225 := bstep (se 2 (by rfl) ⟨1434834, by rfl⟩ : syracuseStep 3826225 = 2869669) B2869669
theorem B2687537 : Blo 1790096 2687537 := bstep (se 2 (by rfl) ⟨1007826, by rfl⟩ : syracuseStep 2687537 = 2015653) B2015653
theorem B2687555 : Blo 1790096 2687555 := bstep (se 1 (by rfl) ⟨2015666, by rfl⟩ : syracuseStep 2687555 = 4031333) B4031333
theorem B10199621 : Blo 1790096 10199621 := bstep (se 4 (by rfl) ⟨956214, by rfl⟩ : syracuseStep 10199621 = 1912429) B1912429
theorem B2687585 : Blo 1790096 2687585 := bstep (se 2 (by rfl) ⟨1007844, by rfl⟩ : syracuseStep 2687585 = 2015689) B2015689
theorem B3023473 : Blo 1790096 3023473 := bstep (se 2 (by rfl) ⟨1133802, by rfl⟩ : syracuseStep 3023473 = 2267605) B2267605
theorem B2687603 : Blo 1790096 2687603 := bstep (se 1 (by rfl) ⟨2015702, by rfl⟩ : syracuseStep 2687603 = 4031405) B4031405
theorem B2687633 : Blo 1790096 2687633 := bstep (se 2 (by rfl) ⟨1007862, by rfl⟩ : syracuseStep 2687633 = 2015725) B2015725
theorem B3023507 : Blo 1790096 3023507 := bstep (se 1 (by rfl) ⟨2267630, by rfl⟩ : syracuseStep 3023507 = 4535261) B4535261
theorem B2687651 : Blo 1790096 2687651 := bstep (se 1 (by rfl) ⟨2015738, by rfl⟩ : syracuseStep 2687651 = 4031477) B4031477
theorem B4031153 : Blo 1790096 4031153 := bstep (se 2 (by rfl) ⟨1511682, by rfl⟩ : syracuseStep 4031153 = 3023365) B3023365
theorem B2015923 : Blo 1790096 2015923 := bstep (se 1 (by rfl) ⟨1511942, by rfl⟩ : syracuseStep 2015923 = 3023885) B3023885
theorem B2687681 : Blo 1790096 2687681 := bstep (se 2 (by rfl) ⟨1007880, by rfl⟩ : syracuseStep 2687681 = 2015761) B2015761
theorem B4031171 : Blo 1790096 4031171 := bstep (se 1 (by rfl) ⟨3023378, by rfl⟩ : syracuseStep 4031171 = 6046757) B6046757
theorem B2687699 : Blo 1790096 2687699 := bstep (se 1 (by rfl) ⟨2015774, by rfl⟩ : syracuseStep 2687699 = 4031549) B4031549
theorem B2687729 : Blo 1790096 2687729 := bstep (se 2 (by rfl) ⟨1007898, by rfl⟩ : syracuseStep 2687729 = 2015797) B2015797
theorem B3400451 : Blo 1790096 3400451 := bstep (se 1 (by rfl) ⟨2550338, by rfl⟩ : syracuseStep 3400451 = 5100677) B5100677
theorem B2687747 : Blo 1790096 2687747 := bstep (se 1 (by rfl) ⟨2015810, by rfl⟩ : syracuseStep 2687747 = 4031621) B4031621
theorem B3023635 : Blo 1790096 3023635 := bstep (se 1 (by rfl) ⟨2267726, by rfl⟩ : syracuseStep 3023635 = 4535453) B4535453
theorem B58106645 : Blo 1790096 58106645 := bstep (se 6 (by rfl) ⟨1361874, by rfl⟩ : syracuseStep 58106645 = 2723749) B2723749
theorem B2687777 : Blo 1790096 2687777 := bstep (se 2 (by rfl) ⟨1007916, by rfl⟩ : syracuseStep 2687777 = 2015833) B2015833
theorem B2687795 : Blo 1790096 2687795 := bstep (se 1 (by rfl) ⟨2015846, by rfl⟩ : syracuseStep 2687795 = 4031693) B4031693
theorem B2016067 : Blo 1790096 2016067 := bstep (se 1 (by rfl) ⟨1512050, by rfl⟩ : syracuseStep 2016067 = 3024101) B3024101
theorem B6046541 : Blo 1790096 6046541 := bstep (se 3 (by rfl) ⟨1133726, by rfl⟩ : syracuseStep 6046541 = 2267453) B2267453
theorem B2687825 : Blo 1790096 2687825 := bstep (se 2 (by rfl) ⟨1007934, by rfl⟩ : syracuseStep 2687825 = 2015869) B2015869
theorem B15295331 : Blo 1790096 15295331 := bstep (se 1 (by rfl) ⟨11471498, by rfl⟩ : syracuseStep 15295331 = 22942997) B22942997
theorem B2687843 : Blo 1790096 2687843 := bstep (se 1 (by rfl) ⟨2015882, by rfl⟩ : syracuseStep 2687843 = 4031765) B4031765
theorem B2687873 : Blo 1790096 2687873 := bstep (se 2 (by rfl) ⟨1007952, by rfl⟩ : syracuseStep 2687873 = 2015905) B2015905
theorem B6046595 : Blo 1790096 6046595 := bstep (se 1 (by rfl) ⟨4534946, by rfl⟩ : syracuseStep 6046595 = 9069893) B9069893
theorem B2687891 : Blo 1790096 2687891 := bstep (se 1 (by rfl) ⟨2015918, by rfl⟩ : syracuseStep 2687891 = 4031837) B4031837
theorem B3023777 : Blo 1790096 3023777 := bstep (se 2 (by rfl) ⟨1133916, by rfl⟩ : syracuseStep 3023777 = 2267833) B2267833
theorem B2687921 : Blo 1790096 2687921 := bstep (se 2 (by rfl) ⟨1007970, by rfl⟩ : syracuseStep 2687921 = 2015941) B2015941
theorem B2687939 : Blo 1790096 2687939 := bstep (se 1 (by rfl) ⟨2015954, by rfl⟩ : syracuseStep 2687939 = 4031909) B4031909
theorem B4031441 : Blo 1790096 4031441 := bstep (se 2 (by rfl) ⟨1511790, by rfl⟩ : syracuseStep 4031441 = 3023581) B3023581
theorem B2687969 : Blo 1790096 2687969 := bstep (se 2 (by rfl) ⟨1007988, by rfl⟩ : syracuseStep 2687969 = 2015977) B2015977
theorem B4031459 : Blo 1790096 4031459 := bstep (se 1 (by rfl) ⟨3023594, by rfl⟩ : syracuseStep 4031459 = 6047189) B6047189
theorem B2687987 : Blo 1790096 2687987 := bstep (se 1 (by rfl) ⟨2015990, by rfl⟩ : syracuseStep 2687987 = 4031981) B4031981
theorem B10200077 : Blo 1790096 10200077 := bstep (se 3 (by rfl) ⟨1912514, by rfl⟩ : syracuseStep 10200077 = 3825029) B3825029
theorem B2688017 : Blo 1790096 2688017 := bstep (se 2 (by rfl) ⟨1008006, by rfl⟩ : syracuseStep 2688017 = 2016013) B2016013
theorem B3023905 : Blo 1790096 3023905 := bstep (se 2 (by rfl) ⟨1133964, by rfl⟩ : syracuseStep 3023905 = 2267929) B2267929
theorem B2688035 : Blo 1790096 2688035 := bstep (se 1 (by rfl) ⟨2016026, by rfl⟩ : syracuseStep 2688035 = 4032053) B4032053
theorem B12248113 : Blo 1790096 12248113 := bstep (se 2 (by rfl) ⟨4593042, by rfl⟩ : syracuseStep 12248113 = 9186085) B9186085
theorem B2688065 : Blo 1790096 2688065 := bstep (se 2 (by rfl) ⟨1008024, by rfl⟩ : syracuseStep 2688065 = 2016049) B2016049
theorem B3023939 : Blo 1790096 3023939 := bstep (se 1 (by rfl) ⟨2267954, by rfl⟩ : syracuseStep 3023939 = 4535909) B4535909
theorem B8610893 : Blo 1790096 8610893 := bstep (se 3 (by rfl) ⟨1614542, by rfl⟩ : syracuseStep 8610893 = 3229085) B3229085
theorem B2688083 : Blo 1790096 2688083 := bstep (se 1 (by rfl) ⟨2016062, by rfl⟩ : syracuseStep 2688083 = 4032125) B4032125
theorem B2688113 : Blo 1790096 2688113 := bstep (se 2 (by rfl) ⟨1008042, by rfl⟩ : syracuseStep 2688113 = 2016085) B2016085
theorem B2688131 : Blo 1790096 2688131 := bstep (se 1 (by rfl) ⟨2016098, by rfl⟩ : syracuseStep 2688131 = 4032197) B4032197
theorem B6046865 : Blo 1790096 6046865 := bstep (se 2 (by rfl) ⟨2267574, by rfl⟩ : syracuseStep 6046865 = 4535149) B4535149
theorem B9069731 : Blo 1790096 9069731 := bstep (se 1 (by rfl) ⟨6802298, by rfl⟩ : syracuseStep 9069731 = 13604597) B13604597
theorem B3024067 : Blo 1790096 3024067 := bstep (se 1 (by rfl) ⟨2268050, by rfl⟩ : syracuseStep 3024067 = 4536101) B4536101
theorem B4031729 : Blo 1790096 4031729 := bstep (se 2 (by rfl) ⟨1511898, by rfl⟩ : syracuseStep 4031729 = 3023797) B3023797
theorem B4031747 : Blo 1790096 4031747 := bstep (se 1 (by rfl) ⟨3023810, by rfl⟩ : syracuseStep 4031747 = 6047621) B6047621
theorem B2549171 : Blo 1790096 2549171 := bstep (se 1 (by rfl) ⟨1911878, by rfl⟩ : syracuseStep 2549171 = 3823757) B3823757
theorem B3630563 : Blo 1790096 3630563 := bstep (se 1 (by rfl) ⟨2722922, by rfl⟩ : syracuseStep 3630563 = 5445845) B5445845
theorem B4531697 : Blo 1790096 4531697 := bstep (se 2 (by rfl) ⟨1699386, by rfl⟩ : syracuseStep 4531697 = 3398773) B3398773
theorem B4032017 : Blo 1790096 4032017 := bstep (se 2 (by rfl) ⟨1512006, by rfl⟩ : syracuseStep 4032017 = 3024013) B3024013
theorem B4531747 : Blo 1790096 4531747 := bstep (se 1 (by rfl) ⟨3398810, by rfl⟩ : syracuseStep 4531747 = 6797621) B6797621
theorem B4302371 : Blo 1790096 4302371 := bstep (se 1 (by rfl) ⟨3226778, by rfl⟩ : syracuseStep 4302371 = 6453557) B6453557
theorem B4032035 : Blo 1790096 4032035 := bstep (se 1 (by rfl) ⟨3024026, by rfl⟩ : syracuseStep 4032035 = 6048053) B6048053
theorem B4302467 : Blo 1790096 4302467 := bstep (se 1 (by rfl) ⟨3226850, by rfl⟩ : syracuseStep 4302467 = 6453701) B6453701
theorem B3401347 : Blo 1790096 3401347 := bstep (se 1 (by rfl) ⟨2551010, by rfl⟩ : syracuseStep 3401347 = 5102021) B5102021
theorem B9684613 : Blo 1790096 9684613 := bstep (se 4 (by rfl) ⟨907932, by rfl⟩ : syracuseStep 9684613 = 1815865) B1815865
theorem B5736109 : Blo 1790096 5736109 := bstep (se 3 (by rfl) ⟨1075520, by rfl⟩ : syracuseStep 5736109 = 2151041) B2151041
theorem B6047405 : Blo 1790096 6047405 := bstep (se 3 (by rfl) ⟨1133888, by rfl⟩ : syracuseStep 6047405 = 2267777) B2267777
theorem B4531889 : Blo 1790096 4531889 := bstep (se 2 (by rfl) ⟨1699458, by rfl⟩ : syracuseStep 4531889 = 3398917) B3398917
theorem B6047459 : Blo 1790096 6047459 := bstep (se 1 (by rfl) ⟨4535594, by rfl⟩ : syracuseStep 6047459 = 9071189) B9071189
theorem B2868977 : Blo 1790096 2868977 := bstep (se 2 (by rfl) ⟨1075866, by rfl⟩ : syracuseStep 2868977 = 2151733) B2151733
theorem B7653133 : Blo 1790096 7653133 := bstep (se 3 (by rfl) ⟨1434962, by rfl⟩ : syracuseStep 7653133 = 2869925) B2869925
theorem B3401507 : Blo 1790096 3401507 := bstep (se 1 (by rfl) ⟨2551130, by rfl⟩ : syracuseStep 3401507 = 5102261) B5102261
theorem B32679733 : Blo 1790096 32679733 := bstep (se 5 (by rfl) ⟨1531862, by rfl⟩ : syracuseStep 32679733 = 3063725) B3063725
theorem B4302659 : Blo 1790096 4302659 := bstep (se 1 (by rfl) ⟨3226994, by rfl⟩ : syracuseStep 4302659 = 6453989) B6453989
theorem B2869105 : Blo 1790096 2869105 := bstep (se 2 (by rfl) ⟨1075914, by rfl⟩ : syracuseStep 2869105 = 2151829) B2151829
theorem B11470733 : Blo 1790096 11470733 := bstep (se 3 (by rfl) ⟨2150762, by rfl⟩ : syracuseStep 11470733 = 4301525) B4301525
theorem B8726449 : Blo 1790096 8726449 := bstep (se 2 (by rfl) ⟨3272418, by rfl⟩ : syracuseStep 8726449 = 6544837) B6544837
theorem B13600709 : Blo 1790096 13600709 := bstep (se 4 (by rfl) ⟨1275066, by rfl⟩ : syracuseStep 13600709 = 2550133) B2550133
theorem B9070541 : Blo 1790096 9070541 := bstep (se 3 (by rfl) ⟨1700726, by rfl⟩ : syracuseStep 9070541 = 3401453) B3401453
theorem B6047729 : Blo 1790096 6047729 := bstep (se 2 (by rfl) ⟨2267898, by rfl⟩ : syracuseStep 6047729 = 4535797) B4535797
theorem B12257315 : Blo 1790096 12257315 := bstep (se 1 (by rfl) ⟨9192986, by rfl⟩ : syracuseStep 12257315 = 18385973) B18385973
theorem B2549809 : Blo 1790096 2549809 := bstep (se 2 (by rfl) ⟨956178, by rfl⟩ : syracuseStep 2549809 = 1912357) B1912357
theorem B5097613 : Blo 1790096 5097613 := bstep (se 3 (by rfl) ⟨955802, by rfl⟩ : syracuseStep 5097613 = 1911605) B1911605
theorem B6801677 : Blo 1790096 6801677 := bstep (se 3 (by rfl) ⟨1275314, by rfl⟩ : syracuseStep 6801677 = 2550629) B2550629
theorem B8284493 : Blo 1790096 8284493 := bstep (se 3 (by rfl) ⟨1553342, by rfl⟩ : syracuseStep 8284493 = 3106685) B3106685
theorem B2550145 : Blo 1790096 2550145 := bstep (se 2 (by rfl) ⟨956304, by rfl⟩ : syracuseStep 2550145 = 1912609) B1912609
theorem B4303313 : Blo 1790096 4303313 := bstep (se 2 (by rfl) ⟨1613742, by rfl⟩ : syracuseStep 4303313 = 3227485) B3227485
theorem B3631601 : Blo 1790096 3631601 := bstep (se 2 (by rfl) ⟨1361850, by rfl⟩ : syracuseStep 3631601 = 2723701) B2723701
theorem B6048269 : Blo 1790096 6048269 := bstep (se 3 (by rfl) ⟨1134050, by rfl⟩ : syracuseStep 6048269 = 2268101) B2268101
theorem B5171747 : Blo 1790096 5171747 := bstep (se 1 (by rfl) ⟨3878810, by rfl⟩ : syracuseStep 5171747 = 7757621) B7757621
theorem B6990371 : Blo 1790096 6990371 := bstep (se 1 (by rfl) ⟨5242778, by rfl⟩ : syracuseStep 6990371 = 10485557) B10485557
theorem B6048323 : Blo 1790096 6048323 := bstep (se 1 (by rfl) ⟨4536242, by rfl⟩ : syracuseStep 6048323 = 9072485) B9072485
theorem B5892689 : Blo 1790096 5892689 := bstep (se 2 (by rfl) ⟨2209758, by rfl⟩ : syracuseStep 5892689 = 4419517) B4419517
theorem B4532881 : Blo 1790096 4532881 := bstep (se 2 (by rfl) ⟨1699830, by rfl⟩ : syracuseStep 4532881 = 3399661) B3399661
theorem B9063089 : Blo 1790096 9063089 := bstep (se 2 (by rfl) ⟨3398658, by rfl⟩ : syracuseStep 9063089 = 6797317) B6797317
theorem B11627185 : Blo 1790096 11627185 := bstep (se 2 (by rfl) ⟨4360194, by rfl⟩ : syracuseStep 11627185 = 8720389) B8720389
theorem B4303601 : Blo 1790096 4303601 := bstep (se 2 (by rfl) ⟨1613850, by rfl⟩ : syracuseStep 4303601 = 3227701) B3227701
theorem B70732565 : Blo 1790096 70732565 := bstep (se 6 (by rfl) ⟨1657794, by rfl⟩ : syracuseStep 70732565 = 3315589) B3315589
theorem B4533155 : Blo 1790096 4533155 := bstep (se 1 (by rfl) ⟨3399866, by rfl⟩ : syracuseStep 4533155 = 6799733) B6799733
theorem B11045809 : Blo 1790096 11045809 := bstep (se 2 (by rfl) ⟨4142178, by rfl⟩ : syracuseStep 11045809 = 8284357) B8284357
theorem B4303811 : Blo 1790096 4303811 := bstep (se 1 (by rfl) ⟨3227858, by rfl⟩ : syracuseStep 4303811 = 6455717) B6455717
theorem B2550737 : Blo 1790096 2550737 := bstep (se 2 (by rfl) ⟨956526, by rfl⟩ : syracuseStep 2550737 = 1913053) B1913053
theorem B1911763 : Blo 1790096 1911763 := bstep (se 1 (by rfl) ⟨1433822, by rfl⟩ : syracuseStep 1911763 = 2867645) B2867645
theorem B2722771 : Blo 1790096 2722771 := bstep (se 1 (by rfl) ⟨2042078, by rfl⟩ : syracuseStep 2722771 = 4084157) B4084157
theorem B6802481 : Blo 1790096 6802481 := bstep (se 2 (by rfl) ⟨2550930, by rfl⟩ : syracuseStep 6802481 = 5101861) B5101861
theorem B4197457 : Blo 1790096 4197457 := bstep (se 2 (by rfl) ⟨1574046, by rfl⟩ : syracuseStep 4197457 = 3148093) B3148093
theorem B6892643 : Blo 1790096 6892643 := bstep (se 1 (by rfl) ⟨5169482, by rfl⟩ : syracuseStep 6892643 = 10338965) B10338965
theorem B4533347 : Blo 1790096 4533347 := bstep (se 1 (by rfl) ⟨3400010, by rfl⟩ : syracuseStep 4533347 = 6800021) B6800021
theorem B2870387 : Blo 1790096 2870387 := bstep (se 1 (by rfl) ⟨2152790, by rfl⟩ : syracuseStep 2870387 = 4305581) B4305581
theorem B2297011 : Blo 1790096 2297011 := bstep (se 1 (by rfl) ⟨1722758, by rfl⟩ : syracuseStep 2297011 = 3445517) B3445517
theorem B12905669 : Blo 1790096 12905669 := bstep (se 4 (by rfl) ⟨1209906, by rfl⟩ : syracuseStep 12905669 = 2419813) B2419813
theorem B24505541 : Blo 1790096 24505541 := bstep (se 4 (by rfl) ⟨2297394, by rfl⟩ : syracuseStep 24505541 = 4594789) B4594789
theorem B1912019 : Blo 1790096 1912019 := bstep (se 1 (by rfl) ⟨1434014, by rfl⟩ : syracuseStep 1912019 = 2868029) B2868029
theorem B2870483 : Blo 1790096 2870483 := bstep (se 1 (by rfl) ⟨2152862, by rfl⟩ : syracuseStep 2870483 = 4305725) B4305725
theorem B2870515 : Blo 1790096 2870515 := bstep (se 1 (by rfl) ⟨2152886, by rfl⟩ : syracuseStep 2870515 = 4305773) B4305773
theorem B10898693 : Blo 1790096 10898693 := bstep (se 4 (by rfl) ⟨1021752, by rfl⟩ : syracuseStep 10898693 = 2043505) B2043505
theorem B4361539 : Blo 1790096 4361539 := bstep (se 1 (by rfl) ⟨3271154, by rfl⟩ : syracuseStep 4361539 = 6542309) B6542309
theorem B5737891 : Blo 1790096 5737891 := bstep (se 1 (by rfl) ⟨4303418, by rfl⟩ : syracuseStep 5737891 = 8606837) B8606837
theorem B2551267 : Blo 1790096 2551267 := bstep (se 1 (by rfl) ⟨1913450, by rfl⟩ : syracuseStep 2551267 = 3826901) B3826901
theorem B8170993 : Blo 1790096 8170993 := bstep (se 2 (by rfl) ⟨3064122, by rfl⟩ : syracuseStep 8170993 = 6128245) B6128245
theorem B55143989 : Blo 1790096 55143989 := bstep (se 5 (by rfl) ⟨2584874, by rfl⟩ : syracuseStep 55143989 = 5169749) B5169749
theorem B6803149 : Blo 1790096 6803149 := bstep (se 3 (by rfl) ⟨1275590, by rfl⟩ : syracuseStep 6803149 = 2551181) B2551181
theorem B4361987 : Blo 1790096 4361987 := bstep (se 1 (by rfl) ⟨3271490, by rfl⟩ : syracuseStep 4361987 = 6542981) B6542981
theorem B2551603 : Blo 1790096 2551603 := bstep (se 1 (by rfl) ⟨1913702, by rfl⟩ : syracuseStep 2551603 = 3827405) B3827405
theorem B5099345 : Blo 1790096 5099345 := bstep (se 2 (by rfl) ⟨1912254, by rfl⟩ : syracuseStep 5099345 = 3824509) B3824509
theorem B5738339 : Blo 1790096 5738339 := bstep (se 1 (by rfl) ⟨4303754, by rfl⟩ : syracuseStep 5738339 = 8607509) B8607509
theorem B10202993 : Blo 1790096 10202993 := bstep (se 2 (by rfl) ⟨3826122, by rfl⟩ : syracuseStep 10202993 = 7652245) B7652245
theorem B1912771 : Blo 1790096 1912771 := bstep (se 1 (by rfl) ⟨1434578, by rfl⟩ : syracuseStep 1912771 = 2869157) B2869157
theorem B2420689 : Blo 1790096 2420689 := bstep (se 2 (by rfl) ⟨907758, by rfl⟩ : syracuseStep 2420689 = 1815517) B1815517
theorem B5099537 : Blo 1790096 5099537 := bstep (se 2 (by rfl) ⟨1912326, by rfl⟩ : syracuseStep 5099537 = 3824653) B3824653
theorem B4534289 : Blo 1790096 4534289 := bstep (se 2 (by rfl) ⟨1700358, by rfl⟩ : syracuseStep 4534289 = 3400717) B3400717
theorem B63721525 : Blo 1790096 63721525 := bstep (se 5 (by rfl) ⟨2986946, by rfl⟩ : syracuseStep 63721525 = 5973893) B5973893
theorem B4534339 : Blo 1790096 4534339 := bstep (se 1 (by rfl) ⟨3400754, by rfl⟩ : syracuseStep 4534339 = 6801509) B6801509
theorem B6041681 : Blo 1790096 6041681 := bstep (se 2 (by rfl) ⟨2265630, by rfl⟩ : syracuseStep 6041681 = 4531261) B4531261
theorem B9064547 : Blo 1790096 9064547 := bstep (se 1 (by rfl) ⟨6798410, by rfl⟩ : syracuseStep 9064547 = 13596821) B13596821
theorem B1790099 : Blo 1790096 1790099 := bstep (se 1 (by rfl) ⟨1342574, by rfl⟩ : syracuseStep 1790099 = 2685149) B2685149
theorem B1790115 : Blo 1790096 1790115 := bstep (se 1 (by rfl) ⟨1342586, by rfl⟩ : syracuseStep 1790115 = 2685173) B2685173
theorem B1790131 : Blo 1790096 1790131 := bstep (se 1 (by rfl) ⟨1342598, by rfl⟩ : syracuseStep 1790131 = 2685197) B2685197
theorem B1790147 : Blo 1790096 1790147 := bstep (se 1 (by rfl) ⟨1342610, by rfl⟩ : syracuseStep 1790147 = 2685221) B2685221
theorem B7360717 : Blo 1790096 7360717 := bstep (se 3 (by rfl) ⟨1380134, by rfl⟩ : syracuseStep 7360717 = 2760269) B2760269
theorem B4534481 : Blo 1790096 4534481 := bstep (se 2 (by rfl) ⟨1700430, by rfl⟩ : syracuseStep 4534481 = 3400861) B3400861
theorem B1790163 : Blo 1790096 1790163 := bstep (se 1 (by rfl) ⟨1342622, by rfl⟩ : syracuseStep 1790163 = 2685245) B2685245
theorem B1790179 : Blo 1790096 1790179 := bstep (se 1 (by rfl) ⟨1342634, by rfl⟩ : syracuseStep 1790179 = 2685269) B2685269
theorem B1790195 : Blo 1790096 1790195 := bstep (se 1 (by rfl) ⟨1342646, by rfl⟩ : syracuseStep 1790195 = 2685293) B2685293
theorem B1790211 : Blo 1790096 1790211 := bstep (se 1 (by rfl) ⟨1342658, by rfl⟩ : syracuseStep 1790211 = 2685317) B2685317
theorem B1790227 : Blo 1790096 1790227 := bstep (se 1 (by rfl) ⟨1342670, by rfl⟩ : syracuseStep 1790227 = 2685341) B2685341
theorem B1790243 : Blo 1790096 1790243 := bstep (se 1 (by rfl) ⟨1342682, by rfl⟩ : syracuseStep 1790243 = 2685365) B2685365
theorem B1790259 : Blo 1790096 1790259 := bstep (se 1 (by rfl) ⟨1342694, by rfl⟩ : syracuseStep 1790259 = 2685389) B2685389
theorem B1790275 : Blo 1790096 1790275 := bstep (se 1 (by rfl) ⟨1342706, by rfl⟩ : syracuseStep 1790275 = 2685413) B2685413
theorem B1790291 : Blo 1790096 1790291 := bstep (se 1 (by rfl) ⟨1342718, by rfl⟩ : syracuseStep 1790291 = 2685437) B2685437
theorem B1790307 : Blo 1790096 1790307 := bstep (se 1 (by rfl) ⟨1342730, by rfl⟩ : syracuseStep 1790307 = 2685461) B2685461
theorem B1790323 : Blo 1790096 1790323 := bstep (se 1 (by rfl) ⟨1342742, by rfl⟩ : syracuseStep 1790323 = 2685485) B2685485
theorem B1790339 : Blo 1790096 1790339 := bstep (se 1 (by rfl) ⟨1342754, by rfl⟩ : syracuseStep 1790339 = 2685509) B2685509
theorem B5443985 : Blo 1790096 5443985 := bstep (se 2 (by rfl) ⟨2041494, by rfl⟩ : syracuseStep 5443985 = 4082989) B4082989
theorem B1790355 : Blo 1790096 1790355 := bstep (se 1 (by rfl) ⟨1342766, by rfl⟩ : syracuseStep 1790355 = 2685533) B2685533
theorem B1790371 : Blo 1790096 1790371 := bstep (se 1 (by rfl) ⟨1342778, by rfl⟩ : syracuseStep 1790371 = 2685557) B2685557
theorem B1790387 : Blo 1790096 1790387 := bstep (se 1 (by rfl) ⟨1342790, by rfl⟩ : syracuseStep 1790387 = 2685581) B2685581
theorem B1790403 : Blo 1790096 1790403 := bstep (se 1 (by rfl) ⟨1342802, by rfl⟩ : syracuseStep 1790403 = 2685605) B2685605
theorem B1790419 : Blo 1790096 1790419 := bstep (se 1 (by rfl) ⟨1342814, by rfl⟩ : syracuseStep 1790419 = 2685629) B2685629
theorem B1790435 : Blo 1790096 1790435 := bstep (se 1 (by rfl) ⟨1342826, by rfl⟩ : syracuseStep 1790435 = 2685653) B2685653
theorem B6803939 : Blo 1790096 6803939 := bstep (se 1 (by rfl) ⟨5102954, by rfl⟩ : syracuseStep 6803939 = 10205909) B10205909
theorem B1790451 : Blo 1790096 1790451 := bstep (se 1 (by rfl) ⟨1342838, by rfl⟩ : syracuseStep 1790451 = 2685677) B2685677
theorem B1790467 : Blo 1790096 1790467 := bstep (se 1 (by rfl) ⟨1342850, by rfl⟩ : syracuseStep 1790467 = 2685701) B2685701
theorem B1790483 : Blo 1790096 1790483 := bstep (se 1 (by rfl) ⟨1342862, by rfl⟩ : syracuseStep 1790483 = 2685725) B2685725
theorem B1790499 : Blo 1790096 1790499 := bstep (se 1 (by rfl) ⟨1342874, by rfl⟩ : syracuseStep 1790499 = 2685749) B2685749
theorem B1790515 : Blo 1790096 1790515 := bstep (se 1 (by rfl) ⟨1342886, by rfl⟩ : syracuseStep 1790515 = 2685773) B2685773
theorem B1790531 : Blo 1790096 1790531 := bstep (se 1 (by rfl) ⟨1342898, by rfl⟩ : syracuseStep 1790531 = 2685797) B2685797
theorem B7262797 : Blo 1790096 7262797 := bstep (se 3 (by rfl) ⟨1361774, by rfl⟩ : syracuseStep 7262797 = 2723549) B2723549
theorem B1790547 : Blo 1790096 1790547 := bstep (se 1 (by rfl) ⟨1342910, by rfl⟩ : syracuseStep 1790547 = 2685821) B2685821
theorem B2298451 : Blo 1790096 2298451 := bstep (se 1 (by rfl) ⟨1723838, by rfl⟩ : syracuseStep 2298451 = 3447677) B3447677
theorem B1790563 : Blo 1790096 1790563 := bstep (se 1 (by rfl) ⟨1342922, by rfl⟩ : syracuseStep 1790563 = 2685845) B2685845
theorem B6042221 : Blo 1790096 6042221 := bstep (se 3 (by rfl) ⟨1132916, by rfl⟩ : syracuseStep 6042221 = 2265833) B2265833
theorem B1790579 : Blo 1790096 1790579 := bstep (se 1 (by rfl) ⟨1342934, by rfl⟩ : syracuseStep 1790579 = 2685869) B2685869
theorem B1790595 : Blo 1790096 1790595 := bstep (se 1 (by rfl) ⟨1342946, by rfl⟩ : syracuseStep 1790595 = 2685893) B2685893
theorem B1790611 : Blo 1790096 1790611 := bstep (se 1 (by rfl) ⟨1342958, by rfl⟩ : syracuseStep 1790611 = 2685917) B2685917
theorem B6042275 : Blo 1790096 6042275 := bstep (se 1 (by rfl) ⟨4531706, by rfl⟩ : syracuseStep 6042275 = 9063413) B9063413
theorem B1790627 : Blo 1790096 1790627 := bstep (se 1 (by rfl) ⟨1342970, by rfl⟩ : syracuseStep 1790627 = 2685941) B2685941
theorem B8729251 : Blo 1790096 8729251 := bstep (se 1 (by rfl) ⟨6546938, by rfl⟩ : syracuseStep 8729251 = 13093877) B13093877
theorem B1790643 : Blo 1790096 1790643 := bstep (se 1 (by rfl) ⟨1342982, by rfl⟩ : syracuseStep 1790643 = 2685965) B2685965
theorem B1790659 : Blo 1790096 1790659 := bstep (se 1 (by rfl) ⟨1342994, by rfl⟩ : syracuseStep 1790659 = 2685989) B2685989
theorem B1790675 : Blo 1790096 1790675 := bstep (se 1 (by rfl) ⟨1343006, by rfl⟩ : syracuseStep 1790675 = 2686013) B2686013
theorem B13595363 : Blo 1790096 13595363 := bstep (se 1 (by rfl) ⟨10196522, by rfl⟩ : syracuseStep 13595363 = 20393045) B20393045
theorem B1790691 : Blo 1790096 1790691 := bstep (se 1 (by rfl) ⟨1343018, by rfl⟩ : syracuseStep 1790691 = 2686037) B2686037
theorem B4305649 : Blo 1790096 4305649 := bstep (se 2 (by rfl) ⟨1614618, by rfl⟩ : syracuseStep 4305649 = 3229237) B3229237
theorem B1790707 : Blo 1790096 1790707 := bstep (se 1 (by rfl) ⟨1343030, by rfl⟩ : syracuseStep 1790707 = 2686061) B2686061
theorem B1790723 : Blo 1790096 1790723 := bstep (se 1 (by rfl) ⟨1343042, by rfl⟩ : syracuseStep 1790723 = 2686085) B2686085
theorem B1790739 : Blo 1790096 1790739 := bstep (se 1 (by rfl) ⟨1343054, by rfl⟩ : syracuseStep 1790739 = 2686109) B2686109
theorem B1790755 : Blo 1790096 1790755 := bstep (se 1 (by rfl) ⟨1343066, by rfl⟩ : syracuseStep 1790755 = 2686133) B2686133
theorem B1790771 : Blo 1790096 1790771 := bstep (se 1 (by rfl) ⟨1343078, by rfl⟩ : syracuseStep 1790771 = 2686157) B2686157
theorem B1790787 : Blo 1790096 1790787 := bstep (se 1 (by rfl) ⟨1343090, by rfl⟩ : syracuseStep 1790787 = 2686181) B2686181
theorem B1790803 : Blo 1790096 1790803 := bstep (se 1 (by rfl) ⟨1343102, by rfl⟩ : syracuseStep 1790803 = 2686205) B2686205
theorem B1790819 : Blo 1790096 1790819 := bstep (se 1 (by rfl) ⟨1343114, by rfl⟩ : syracuseStep 1790819 = 2686229) B2686229
theorem B1790835 : Blo 1790096 1790835 := bstep (se 1 (by rfl) ⟨1343126, by rfl⟩ : syracuseStep 1790835 = 2686253) B2686253
theorem B1790851 : Blo 1790096 1790851 := bstep (se 1 (by rfl) ⟨1343138, by rfl⟩ : syracuseStep 1790851 = 2686277) B2686277
theorem B9065357 : Blo 1790096 9065357 := bstep (se 3 (by rfl) ⟨1699754, by rfl⟩ : syracuseStep 9065357 = 3399509) B3399509
theorem B1790867 : Blo 1790096 1790867 := bstep (se 1 (by rfl) ⟨1343150, by rfl⟩ : syracuseStep 1790867 = 2686301) B2686301
theorem B1790883 : Blo 1790096 1790883 := bstep (se 1 (by rfl) ⟨1343162, by rfl⟩ : syracuseStep 1790883 = 2686325) B2686325
theorem B6042545 : Blo 1790096 6042545 := bstep (se 2 (by rfl) ⟨2265954, by rfl⟩ : syracuseStep 6042545 = 4531909) B4531909
theorem B1790899 : Blo 1790096 1790899 := bstep (se 1 (by rfl) ⟨1343174, by rfl⟩ : syracuseStep 1790899 = 2686349) B2686349
theorem B2266051 : Blo 1790096 2266051 := bstep (se 1 (by rfl) ⟨1699538, by rfl⟩ : syracuseStep 2266051 = 3399077) B3399077
theorem B1790915 : Blo 1790096 1790915 := bstep (se 1 (by rfl) ⟨1343186, by rfl⟩ : syracuseStep 1790915 = 2686373) B2686373
theorem B1790931 : Blo 1790096 1790931 := bstep (se 1 (by rfl) ⟨1343198, by rfl⟩ : syracuseStep 1790931 = 2686397) B2686397
theorem B1790947 : Blo 1790096 1790947 := bstep (se 1 (by rfl) ⟨1343210, by rfl⟩ : syracuseStep 1790947 = 2686421) B2686421
theorem B5100529 : Blo 1790096 5100529 := bstep (se 2 (by rfl) ⟨1912698, by rfl⟩ : syracuseStep 5100529 = 3825397) B3825397
theorem B1790963 : Blo 1790096 1790963 := bstep (se 1 (by rfl) ⟨1343222, by rfl⟩ : syracuseStep 1790963 = 2686445) B2686445
theorem B1790979 : Blo 1790096 1790979 := bstep (se 1 (by rfl) ⟨1343234, by rfl⟩ : syracuseStep 1790979 = 2686469) B2686469
theorem B1790995 : Blo 1790096 1790995 := bstep (se 1 (by rfl) ⟨1343246, by rfl⟩ : syracuseStep 1790995 = 2686493) B2686493
theorem B2266147 : Blo 1790096 2266147 := bstep (se 1 (by rfl) ⟨1699610, by rfl⟩ : syracuseStep 2266147 = 3399221) B3399221
theorem B1791011 : Blo 1790096 1791011 := bstep (se 1 (by rfl) ⟨1343258, by rfl⟩ : syracuseStep 1791011 = 2686517) B2686517
theorem B5739569 : Blo 1790096 5739569 := bstep (se 2 (by rfl) ⟨2152338, by rfl⟩ : syracuseStep 5739569 = 4304677) B4304677
theorem B1791027 : Blo 1790096 1791027 := bstep (se 1 (by rfl) ⟨1343270, by rfl⟩ : syracuseStep 1791027 = 2686541) B2686541
theorem B1791043 : Blo 1790096 1791043 := bstep (se 1 (by rfl) ⟨1343282, by rfl⟩ : syracuseStep 1791043 = 2686565) B2686565
theorem B1791059 : Blo 1790096 1791059 := bstep (se 1 (by rfl) ⟨1343294, by rfl⟩ : syracuseStep 1791059 = 2686589) B2686589
theorem B1791075 : Blo 1790096 1791075 := bstep (se 1 (by rfl) ⟨1343306, by rfl⟩ : syracuseStep 1791075 = 2686613) B2686613
theorem B1791091 : Blo 1790096 1791091 := bstep (se 1 (by rfl) ⟨1343318, by rfl⟩ : syracuseStep 1791091 = 2686637) B2686637
theorem B1791107 : Blo 1790096 1791107 := bstep (se 1 (by rfl) ⟨1343330, by rfl⟩ : syracuseStep 1791107 = 2686661) B2686661
theorem B1791123 : Blo 1790096 1791123 := bstep (se 1 (by rfl) ⟨1343342, by rfl⟩ : syracuseStep 1791123 = 2686685) B2686685
theorem B1791139 : Blo 1790096 1791139 := bstep (se 1 (by rfl) ⟨1343354, by rfl⟩ : syracuseStep 1791139 = 2686709) B2686709
theorem B4535473 : Blo 1790096 4535473 := bstep (se 2 (by rfl) ⟨1700802, by rfl⟩ : syracuseStep 4535473 = 3401605) B3401605
theorem B1791155 : Blo 1790096 1791155 := bstep (se 1 (by rfl) ⟨1343366, by rfl⟩ : syracuseStep 1791155 = 2686733) B2686733
theorem B1791171 : Blo 1790096 1791171 := bstep (se 1 (by rfl) ⟨1343378, by rfl⟩ : syracuseStep 1791171 = 2686757) B2686757
theorem B1791187 : Blo 1790096 1791187 := bstep (se 1 (by rfl) ⟨1343390, by rfl⟩ : syracuseStep 1791187 = 2686781) B2686781
theorem B1791203 : Blo 1790096 1791203 := bstep (se 1 (by rfl) ⟨1343402, by rfl⟩ : syracuseStep 1791203 = 2686805) B2686805
theorem B2454769 : Blo 1790096 2454769 := bstep (se 2 (by rfl) ⟨920538, by rfl⟩ : syracuseStep 2454769 = 1841077) B1841077
theorem B1791219 : Blo 1790096 1791219 := bstep (se 1 (by rfl) ⟨1343414, by rfl⟩ : syracuseStep 1791219 = 2686829) B2686829
theorem B5100803 : Blo 1790096 5100803 := bstep (se 1 (by rfl) ⟨3825602, by rfl⟩ : syracuseStep 5100803 = 7651205) B7651205
theorem B1791235 : Blo 1790096 1791235 := bstep (se 1 (by rfl) ⟨1343426, by rfl⟩ : syracuseStep 1791235 = 2686853) B2686853
theorem B2422019 : Blo 1790096 2422019 := bstep (se 1 (by rfl) ⟨1816514, by rfl⟩ : syracuseStep 2422019 = 3633029) B3633029
theorem B1791251 : Blo 1790096 1791251 := bstep (se 1 (by rfl) ⟨1343438, by rfl⟩ : syracuseStep 1791251 = 2686877) B2686877
theorem B1791267 : Blo 1790096 1791267 := bstep (se 1 (by rfl) ⟨1343450, by rfl⟩ : syracuseStep 1791267 = 2686901) B2686901
theorem B10204451 : Blo 1790096 10204451 := bstep (se 1 (by rfl) ⟨7653338, by rfl⟩ : syracuseStep 10204451 = 15306677) B15306677
theorem B1791283 : Blo 1790096 1791283 := bstep (se 1 (by rfl) ⟨1343462, by rfl⟩ : syracuseStep 1791283 = 2686925) B2686925
theorem B1791299 : Blo 1790096 1791299 := bstep (se 1 (by rfl) ⟨1343474, by rfl⟩ : syracuseStep 1791299 = 2686949) B2686949
theorem B1791315 : Blo 1790096 1791315 := bstep (se 1 (by rfl) ⟨1343486, by rfl⟩ : syracuseStep 1791315 = 2686973) B2686973
theorem B1791331 : Blo 1790096 1791331 := bstep (se 1 (by rfl) ⟨1343498, by rfl⟩ : syracuseStep 1791331 = 2686997) B2686997
theorem B1791347 : Blo 1790096 1791347 := bstep (se 1 (by rfl) ⟨1343510, by rfl⟩ : syracuseStep 1791347 = 2687021) B2687021
theorem B1791363 : Blo 1790096 1791363 := bstep (se 1 (by rfl) ⟨1343522, by rfl⟩ : syracuseStep 1791363 = 2687045) B2687045
theorem B1791379 : Blo 1790096 1791379 := bstep (se 1 (by rfl) ⟨1343534, by rfl⟩ : syracuseStep 1791379 = 2687069) B2687069
theorem B10196387 : Blo 1790096 10196387 := bstep (se 1 (by rfl) ⟨7647290, by rfl⟩ : syracuseStep 10196387 = 15294581) B15294581
theorem B1791395 : Blo 1790096 1791395 := bstep (se 1 (by rfl) ⟨1343546, by rfl⟩ : syracuseStep 1791395 = 2687093) B2687093
theorem B1791411 : Blo 1790096 1791411 := bstep (se 1 (by rfl) ⟨1343558, by rfl⟩ : syracuseStep 1791411 = 2687117) B2687117
theorem B5100995 : Blo 1790096 5100995 := bstep (se 1 (by rfl) ⟨3825746, by rfl⟩ : syracuseStep 5100995 = 7651493) B7651493
theorem B1791427 : Blo 1790096 1791427 := bstep (se 1 (by rfl) ⟨1343570, by rfl⟩ : syracuseStep 1791427 = 2687141) B2687141
theorem B4535747 : Blo 1790096 4535747 := bstep (se 1 (by rfl) ⟨3401810, by rfl⟩ : syracuseStep 4535747 = 6803621) B6803621
theorem B6043085 : Blo 1790096 6043085 := bstep (se 3 (by rfl) ⟨1133078, by rfl⟩ : syracuseStep 6043085 = 2266157) B2266157
theorem B1791443 : Blo 1790096 1791443 := bstep (se 1 (by rfl) ⟨1343582, by rfl⟩ : syracuseStep 1791443 = 2687165) B2687165
theorem B2618849 : Blo 1790096 2618849 := bstep (se 2 (by rfl) ⟨982068, by rfl⟩ : syracuseStep 2618849 = 1964137) B1964137
theorem B1791459 : Blo 1790096 1791459 := bstep (se 1 (by rfl) ⟨1343594, by rfl⟩ : syracuseStep 1791459 = 2687189) B2687189
theorem B1791475 : Blo 1790096 1791475 := bstep (se 1 (by rfl) ⟨1343606, by rfl⟩ : syracuseStep 1791475 = 2687213) B2687213
theorem B6043139 : Blo 1790096 6043139 := bstep (se 1 (by rfl) ⟨4532354, by rfl⟩ : syracuseStep 6043139 = 9064709) B9064709
theorem B1791491 : Blo 1790096 1791491 := bstep (se 1 (by rfl) ⟨1343618, by rfl⟩ : syracuseStep 1791491 = 2687237) B2687237
theorem B2266643 : Blo 1790096 2266643 := bstep (se 1 (by rfl) ⟨1699982, by rfl⟩ : syracuseStep 2266643 = 3399965) B3399965
theorem B1791507 : Blo 1790096 1791507 := bstep (se 1 (by rfl) ⟨1343630, by rfl⟩ : syracuseStep 1791507 = 2687261) B2687261
theorem B1791523 : Blo 1790096 1791523 := bstep (se 1 (by rfl) ⟨1343642, by rfl⟩ : syracuseStep 1791523 = 2687285) B2687285
theorem B1791539 : Blo 1790096 1791539 := bstep (se 1 (by rfl) ⟨1343654, by rfl⟩ : syracuseStep 1791539 = 2687309) B2687309
theorem B38721077 : Blo 1790096 38721077 := bstep (se 5 (by rfl) ⟨1815050, by rfl⟩ : syracuseStep 38721077 = 3630101) B3630101
theorem B1791555 : Blo 1790096 1791555 := bstep (se 1 (by rfl) ⟨1343666, by rfl⟩ : syracuseStep 1791555 = 2687333) B2687333
theorem B4027985 : Blo 1790096 4027985 := bstep (se 2 (by rfl) ⟨1510494, by rfl⟩ : syracuseStep 4027985 = 3020989) B3020989
theorem B1791571 : Blo 1790096 1791571 := bstep (se 1 (by rfl) ⟨1343678, by rfl⟩ : syracuseStep 1791571 = 2687357) B2687357
theorem B4028003 : Blo 1790096 4028003 := bstep (se 1 (by rfl) ⟨3021002, by rfl⟩ : syracuseStep 4028003 = 6042005) B6042005
theorem B1791587 : Blo 1790096 1791587 := bstep (se 1 (by rfl) ⟨1343690, by rfl⟩ : syracuseStep 1791587 = 2687381) B2687381
theorem B1791603 : Blo 1790096 1791603 := bstep (se 1 (by rfl) ⟨1343702, by rfl⟩ : syracuseStep 1791603 = 2687405) B2687405
theorem B1791619 : Blo 1790096 1791619 := bstep (se 1 (by rfl) ⟨1343714, by rfl⟩ : syracuseStep 1791619 = 2687429) B2687429
theorem B4535939 : Blo 1790096 4535939 := bstep (se 1 (by rfl) ⟨3401954, by rfl⟩ : syracuseStep 4535939 = 6803909) B6803909
theorem B1791635 : Blo 1790096 1791635 := bstep (se 1 (by rfl) ⟨1343726, by rfl⟩ : syracuseStep 1791635 = 2687453) B2687453
theorem B7648931 : Blo 1790096 7648931 := bstep (se 1 (by rfl) ⟨5736698, by rfl⟩ : syracuseStep 7648931 = 11473397) B11473397
theorem B1791651 : Blo 1790096 1791651 := bstep (se 1 (by rfl) ⟨1343738, by rfl⟩ : syracuseStep 1791651 = 2687477) B2687477
theorem B1791667 : Blo 1790096 1791667 := bstep (se 1 (by rfl) ⟨1343750, by rfl⟩ : syracuseStep 1791667 = 2687501) B2687501
theorem B1791683 : Blo 1790096 1791683 := bstep (se 1 (by rfl) ⟨1343762, by rfl⟩ : syracuseStep 1791683 = 2687525) B2687525
theorem B1791699 : Blo 1790096 1791699 := bstep (se 1 (by rfl) ⟨1343774, by rfl⟩ : syracuseStep 1791699 = 2687549) B2687549
theorem B1791715 : Blo 1790096 1791715 := bstep (se 1 (by rfl) ⟨1343786, by rfl⟩ : syracuseStep 1791715 = 2687573) B2687573
theorem B1791731 : Blo 1790096 1791731 := bstep (se 1 (by rfl) ⟨1343798, by rfl⟩ : syracuseStep 1791731 = 2687597) B2687597
theorem B1791747 : Blo 1790096 1791747 := bstep (se 1 (by rfl) ⟨1343810, by rfl⟩ : syracuseStep 1791747 = 2687621) B2687621
theorem B6043409 : Blo 1790096 6043409 := bstep (se 2 (by rfl) ⟨2266278, by rfl⟩ : syracuseStep 6043409 = 4532557) B4532557
theorem B45913877 : Blo 1790096 45913877 := bstep (se 6 (by rfl) ⟨1076106, by rfl⟩ : syracuseStep 45913877 = 2152213) B2152213
theorem B1791763 : Blo 1790096 1791763 := bstep (se 1 (by rfl) ⟨1343822, by rfl⟩ : syracuseStep 1791763 = 2687645) B2687645
theorem B1791779 : Blo 1790096 1791779 := bstep (se 1 (by rfl) ⟨1343834, by rfl⟩ : syracuseStep 1791779 = 2687669) B2687669
theorem B6797105 : Blo 1790096 6797105 := bstep (se 2 (by rfl) ⟨2548914, by rfl⟩ : syracuseStep 6797105 = 5097829) B5097829
theorem B1791795 : Blo 1790096 1791795 := bstep (se 1 (by rfl) ⟨1343846, by rfl⟩ : syracuseStep 1791795 = 2687693) B2687693
theorem B1791811 : Blo 1790096 1791811 := bstep (se 1 (by rfl) ⟨1343858, by rfl⟩ : syracuseStep 1791811 = 2687717) B2687717
theorem B1791827 : Blo 1790096 1791827 := bstep (se 1 (by rfl) ⟨1343870, by rfl⟩ : syracuseStep 1791827 = 2687741) B2687741
theorem B1791843 : Blo 1790096 1791843 := bstep (se 1 (by rfl) ⟨1343882, by rfl⟩ : syracuseStep 1791843 = 2687765) B2687765
theorem B4028273 : Blo 1790096 4028273 := bstep (se 2 (by rfl) ⟨1510602, by rfl⟩ : syracuseStep 4028273 = 3021205) B3021205
theorem B1791859 : Blo 1790096 1791859 := bstep (se 1 (by rfl) ⟨1343894, by rfl⟩ : syracuseStep 1791859 = 2687789) B2687789
theorem B4028291 : Blo 1790096 4028291 := bstep (se 1 (by rfl) ⟨3021218, by rfl⟩ : syracuseStep 4028291 = 6042437) B6042437
theorem B1791875 : Blo 1790096 1791875 := bstep (se 1 (by rfl) ⟨1343906, by rfl⟩ : syracuseStep 1791875 = 2687813) B2687813
theorem B1791891 : Blo 1790096 1791891 := bstep (se 1 (by rfl) ⟨1343918, by rfl⟩ : syracuseStep 1791891 = 2687837) B2687837
theorem B1791907 : Blo 1790096 1791907 := bstep (se 1 (by rfl) ⟨1343930, by rfl⟩ : syracuseStep 1791907 = 2687861) B2687861
theorem B5740465 : Blo 1790096 5740465 := bstep (se 2 (by rfl) ⟨2152674, by rfl⟩ : syracuseStep 5740465 = 4305349) B4305349
theorem B1791923 : Blo 1790096 1791923 := bstep (se 1 (by rfl) ⟨1343942, by rfl⟩ : syracuseStep 1791923 = 2687885) B2687885
theorem B1791939 : Blo 1790096 1791939 := bstep (se 1 (by rfl) ⟨1343954, by rfl⟩ : syracuseStep 1791939 = 2687909) B2687909
theorem B1791955 : Blo 1790096 1791955 := bstep (se 1 (by rfl) ⟨1343966, by rfl⟩ : syracuseStep 1791955 = 2687933) B2687933
theorem B1791971 : Blo 1790096 1791971 := bstep (se 1 (by rfl) ⟨1343978, by rfl⟩ : syracuseStep 1791971 = 2687957) B2687957
theorem B1791987 : Blo 1790096 1791987 := bstep (se 1 (by rfl) ⟨1343990, by rfl⟩ : syracuseStep 1791987 = 2687981) B2687981
theorem B1792003 : Blo 1790096 1792003 := bstep (se 1 (by rfl) ⟨1344002, by rfl⟩ : syracuseStep 1792003 = 2688005) B2688005
theorem B1792019 : Blo 1790096 1792019 := bstep (se 1 (by rfl) ⟨1344014, by rfl⟩ : syracuseStep 1792019 = 2688029) B2688029
theorem B6453283 : Blo 1790096 6453283 := bstep (se 1 (by rfl) ⟨4839962, by rfl⟩ : syracuseStep 6453283 = 9679925) B9679925
theorem B1792035 : Blo 1790096 1792035 := bstep (se 1 (by rfl) ⟨1344026, by rfl⟩ : syracuseStep 1792035 = 2688053) B2688053
theorem B1792051 : Blo 1790096 1792051 := bstep (se 1 (by rfl) ⟨1344038, by rfl⟩ : syracuseStep 1792051 = 2688077) B2688077
theorem B1792067 : Blo 1790096 1792067 := bstep (se 1 (by rfl) ⟨1344050, by rfl⟩ : syracuseStep 1792067 = 2688101) B2688101
theorem B3020881 : Blo 1790096 3020881 := bstep (se 2 (by rfl) ⟨1132830, by rfl⟩ : syracuseStep 3020881 = 2265661) B2265661
theorem B1792083 : Blo 1790096 1792083 := bstep (se 1 (by rfl) ⟨1344062, by rfl⟩ : syracuseStep 1792083 = 2688125) B2688125
theorem B3020915 : Blo 1790096 3020915 := bstep (se 1 (by rfl) ⟨2265686, by rfl⟩ : syracuseStep 3020915 = 4531373) B4531373
theorem B4028561 : Blo 1790096 4028561 := bstep (se 2 (by rfl) ⟨1510710, by rfl⟩ : syracuseStep 4028561 = 3021421) B3021421
theorem B4028579 : Blo 1790096 4028579 := bstep (se 1 (by rfl) ⟨3021434, by rfl⟩ : syracuseStep 4028579 = 6042869) B6042869
theorem B2267347 : Blo 1790096 2267347 := bstep (se 1 (by rfl) ⟨1700510, by rfl⟩ : syracuseStep 2267347 = 3401021) B3401021
theorem B2685155 : Blo 1790096 2685155 := bstep (se 1 (by rfl) ⟨2013866, by rfl⟩ : syracuseStep 2685155 = 4027733) B4027733
theorem B8607971 : Blo 1790096 8607971 := bstep (se 1 (by rfl) ⟨6455978, by rfl⟩ : syracuseStep 8607971 = 12911957) B12911957
theorem B5101805 : Blo 1790096 5101805 := bstep (se 3 (by rfl) ⟨956588, by rfl⟩ : syracuseStep 5101805 = 1913177) B1913177
theorem B3021043 : Blo 1790096 3021043 := bstep (se 1 (by rfl) ⟨2265782, by rfl⟩ : syracuseStep 3021043 = 4531565) B4531565
theorem B2685185 : Blo 1790096 2685185 := bstep (se 2 (by rfl) ⟨1006944, by rfl⟩ : syracuseStep 2685185 = 2013889) B2013889
theorem B10205453 : Blo 1790096 10205453 := bstep (se 3 (by rfl) ⟨1913522, by rfl⟩ : syracuseStep 10205453 = 3827045) B3827045
theorem B2685203 : Blo 1790096 2685203 := bstep (se 1 (by rfl) ⟨2013902, by rfl⟩ : syracuseStep 2685203 = 4027805) B4027805
theorem B6043949 : Blo 1790096 6043949 := bstep (se 3 (by rfl) ⟨1133240, by rfl⟩ : syracuseStep 6043949 = 2266481) B2266481
theorem B2685233 : Blo 1790096 2685233 := bstep (se 2 (by rfl) ⟨1006962, by rfl⟩ : syracuseStep 2685233 = 2013925) B2013925
theorem B2267443 : Blo 1790096 2267443 := bstep (se 1 (by rfl) ⟨1700582, by rfl⟩ : syracuseStep 2267443 = 3401165) B3401165
theorem B2685251 : Blo 1790096 2685251 := bstep (se 1 (by rfl) ⟨2013938, by rfl⟩ : syracuseStep 2685251 = 4027877) B4027877
theorem B2685281 : Blo 1790096 2685281 := bstep (se 2 (by rfl) ⟨1006980, by rfl⟩ : syracuseStep 2685281 = 2013961) B2013961
theorem B6044003 : Blo 1790096 6044003 := bstep (se 1 (by rfl) ⟨4533002, by rfl⟩ : syracuseStep 6044003 = 9066005) B9066005
theorem B2685299 : Blo 1790096 2685299 := bstep (se 1 (by rfl) ⟨2013974, by rfl⟩ : syracuseStep 2685299 = 4027949) B4027949
theorem B3021185 : Blo 1790096 3021185 := bstep (se 2 (by rfl) ⟨1132944, by rfl⟩ : syracuseStep 3021185 = 2265889) B2265889
theorem B2685329 : Blo 1790096 2685329 := bstep (se 2 (by rfl) ⟨1006998, by rfl⟩ : syracuseStep 2685329 = 2013997) B2013997
theorem B2685347 : Blo 1790096 2685347 := bstep (se 1 (by rfl) ⟨2014010, by rfl⟩ : syracuseStep 2685347 = 4028021) B4028021
theorem B5101987 : Blo 1790096 5101987 := bstep (se 1 (by rfl) ⟨3826490, by rfl⟩ : syracuseStep 5101987 = 7652981) B7652981
theorem B2152867 : Blo 1790096 2152867 := bstep (se 1 (by rfl) ⟨1614650, by rfl⟩ : syracuseStep 2152867 = 3229301) B3229301
theorem B4028849 : Blo 1790096 4028849 := bstep (se 2 (by rfl) ⟨1510818, by rfl⟩ : syracuseStep 4028849 = 3021637) B3021637
theorem B2685377 : Blo 1790096 2685377 := bstep (se 2 (by rfl) ⟨1007016, by rfl⟩ : syracuseStep 2685377 = 2014033) B2014033
theorem B4028867 : Blo 1790096 4028867 := bstep (se 1 (by rfl) ⟨3021650, by rfl⟩ : syracuseStep 4028867 = 6043301) B6043301
theorem B2685395 : Blo 1790096 2685395 := bstep (se 1 (by rfl) ⟨2014046, by rfl⟩ : syracuseStep 2685395 = 4028093) B4028093
theorem B2685425 : Blo 1790096 2685425 := bstep (se 2 (by rfl) ⟨1007034, by rfl⟩ : syracuseStep 2685425 = 2014069) B2014069
theorem B3021313 : Blo 1790096 3021313 := bstep (se 2 (by rfl) ⟨1132992, by rfl⟩ : syracuseStep 3021313 = 2265985) B2265985
theorem B2685443 : Blo 1790096 2685443 := bstep (se 1 (by rfl) ⟨2014082, by rfl⟩ : syracuseStep 2685443 = 4028165) B4028165
theorem B6126083 : Blo 1790096 6126083 := bstep (se 1 (by rfl) ⟨4594562, by rfl⟩ : syracuseStep 6126083 = 9189125) B9189125
theorem B2685473 : Blo 1790096 2685473 := bstep (se 2 (by rfl) ⟨1007052, by rfl⟩ : syracuseStep 2685473 = 2014105) B2014105
theorem B3021347 : Blo 1790096 3021347 := bstep (se 1 (by rfl) ⟨2266010, by rfl⟩ : syracuseStep 3021347 = 4532021) B4532021
theorem B2685491 : Blo 1790096 2685491 := bstep (se 1 (by rfl) ⟨2014118, by rfl⟩ : syracuseStep 2685491 = 4028237) B4028237
theorem B2685521 : Blo 1790096 2685521 := bstep (se 2 (by rfl) ⟨1007070, by rfl⟩ : syracuseStep 2685521 = 2014141) B2014141
theorem B3824209 : Blo 1790096 3824209 := bstep (se 2 (by rfl) ⟨1434078, by rfl⟩ : syracuseStep 3824209 = 2868157) B2868157
theorem B2685539 : Blo 1790096 2685539 := bstep (se 1 (by rfl) ⟨2014154, by rfl⟩ : syracuseStep 2685539 = 4028309) B4028309
theorem B6044273 : Blo 1790096 6044273 := bstep (se 2 (by rfl) ⟨2266602, by rfl⟩ : syracuseStep 6044273 = 4533205) B4533205
theorem B2685569 : Blo 1790096 2685569 := bstep (se 2 (by rfl) ⟨1007088, by rfl⟩ : syracuseStep 2685569 = 2014177) B2014177
theorem B2685587 : Blo 1790096 2685587 := bstep (se 1 (by rfl) ⟨2014190, by rfl⟩ : syracuseStep 2685587 = 4028381) B4028381
theorem B3021475 : Blo 1790096 3021475 := bstep (se 1 (by rfl) ⟨2266106, by rfl⟩ : syracuseStep 3021475 = 4532213) B4532213
theorem B2685617 : Blo 1790096 2685617 := bstep (se 2 (by rfl) ⟨1007106, by rfl⟩ : syracuseStep 2685617 = 2014213) B2014213
theorem B2685635 : Blo 1790096 2685635 := bstep (se 1 (by rfl) ⟨2014226, by rfl⟩ : syracuseStep 2685635 = 4028453) B4028453
theorem B4840145 : Blo 1790096 4840145 := bstep (se 2 (by rfl) ⟨1815054, by rfl⟩ : syracuseStep 4840145 = 3630109) B3630109
theorem B4029137 : Blo 1790096 4029137 := bstep (se 2 (by rfl) ⟨1510926, by rfl⟩ : syracuseStep 4029137 = 3021853) B3021853
theorem B2013907 : Blo 1790096 2013907 := bstep (se 1 (by rfl) ⟨1510430, by rfl⟩ : syracuseStep 2013907 = 3020861) B3020861
theorem B2685665 : Blo 1790096 2685665 := bstep (se 2 (by rfl) ⟨1007124, by rfl⟩ : syracuseStep 2685665 = 2014249) B2014249
theorem B4029155 : Blo 1790096 4029155 := bstep (se 1 (by rfl) ⟨3021866, by rfl⟩ : syracuseStep 4029155 = 6043733) B6043733
theorem B3447523 : Blo 1790096 3447523 := bstep (se 1 (by rfl) ⟨2585642, by rfl⟩ : syracuseStep 3447523 = 5171285) B5171285
theorem B2685683 : Blo 1790096 2685683 := bstep (se 1 (by rfl) ⟨2014262, by rfl⟩ : syracuseStep 2685683 = 4028525) B4028525
theorem B2685713 : Blo 1790096 2685713 := bstep (se 2 (by rfl) ⟨1007142, by rfl⟩ : syracuseStep 2685713 = 2014285) B2014285
theorem B2685731 : Blo 1790096 2685731 := bstep (se 1 (by rfl) ⟨2014298, by rfl⟩ : syracuseStep 2685731 = 4028597) B4028597
theorem B2267939 : Blo 1790096 2267939 := bstep (se 1 (by rfl) ⟨1700954, by rfl⟩ : syracuseStep 2267939 = 3401909) B3401909
theorem B3021617 : Blo 1790096 3021617 := bstep (se 2 (by rfl) ⟨1133106, by rfl⟩ : syracuseStep 3021617 = 2266213) B2266213
theorem B2685761 : Blo 1790096 2685761 := bstep (se 2 (by rfl) ⟨1007160, by rfl⟩ : syracuseStep 2685761 = 2014321) B2014321
theorem B2685779 : Blo 1790096 2685779 := bstep (se 1 (by rfl) ⟨2014334, by rfl⟩ : syracuseStep 2685779 = 4028669) B4028669
theorem B2014051 : Blo 1790096 2014051 := bstep (se 1 (by rfl) ⟨1510538, by rfl⟩ : syracuseStep 2014051 = 3021077) B3021077
theorem B2685809 : Blo 1790096 2685809 := bstep (se 2 (by rfl) ⟨1007178, by rfl⟩ : syracuseStep 2685809 = 2014357) B2014357
theorem B8608625 : Blo 1790096 8608625 := bstep (se 2 (by rfl) ⟨3228234, by rfl⟩ : syracuseStep 8608625 = 6456469) B6456469
theorem B2685827 : Blo 1790096 2685827 := bstep (se 1 (by rfl) ⟨2014370, by rfl⟩ : syracuseStep 2685827 = 4028741) B4028741
theorem B5102477 : Blo 1790096 5102477 := bstep (se 3 (by rfl) ⟨956714, by rfl⟩ : syracuseStep 5102477 = 1913429) B1913429
theorem B2685857 : Blo 1790096 2685857 := bstep (se 2 (by rfl) ⟨1007196, by rfl⟩ : syracuseStep 2685857 = 2014393) B2014393
theorem B3021745 : Blo 1790096 3021745 := bstep (se 2 (by rfl) ⟨1133154, by rfl⟩ : syracuseStep 3021745 = 2266309) B2266309
theorem B2685875 : Blo 1790096 2685875 := bstep (se 1 (by rfl) ⟨2014406, by rfl⟩ : syracuseStep 2685875 = 4028813) B4028813
theorem B27958213 : Blo 1790096 27958213 := bstep (se 4 (by rfl) ⟨2621082, by rfl⟩ : syracuseStep 27958213 = 5242165) B5242165
theorem B2685905 : Blo 1790096 2685905 := bstep (se 2 (by rfl) ⟨1007214, by rfl⟩ : syracuseStep 2685905 = 2014429) B2014429
theorem B3021779 : Blo 1790096 3021779 := bstep (se 1 (by rfl) ⟨2266334, by rfl⟩ : syracuseStep 3021779 = 4532669) B4532669
theorem B2907107 : Blo 1790096 2907107 := bstep (se 1 (by rfl) ⟨2180330, by rfl⟩ : syracuseStep 2907107 = 4360661) B4360661
theorem B2685923 : Blo 1790096 2685923 := bstep (se 1 (by rfl) ⟨2014442, by rfl⟩ : syracuseStep 2685923 = 4028885) B4028885
theorem B4029425 : Blo 1790096 4029425 := bstep (se 2 (by rfl) ⟨1511034, by rfl⟩ : syracuseStep 4029425 = 3022069) B3022069
theorem B2014195 : Blo 1790096 2014195 := bstep (se 1 (by rfl) ⟨1510646, by rfl⟩ : syracuseStep 2014195 = 3021293) B3021293
theorem B2685953 : Blo 1790096 2685953 := bstep (se 2 (by rfl) ⟨1007232, by rfl⟩ : syracuseStep 2685953 = 2014465) B2014465
theorem B4029443 : Blo 1790096 4029443 := bstep (se 1 (by rfl) ⟨3022082, by rfl⟩ : syracuseStep 4029443 = 6044165) B6044165
theorem B2685971 : Blo 1790096 2685971 := bstep (se 1 (by rfl) ⟨2014478, by rfl⟩ : syracuseStep 2685971 = 4028957) B4028957
theorem B2686001 : Blo 1790096 2686001 := bstep (se 2 (by rfl) ⟨1007250, by rfl⟩ : syracuseStep 2686001 = 2014501) B2014501
theorem B2686019 : Blo 1790096 2686019 := bstep (se 1 (by rfl) ⟨2014514, by rfl⟩ : syracuseStep 2686019 = 4029029) B4029029
theorem B3226705 : Blo 1790096 3226705 := bstep (se 2 (by rfl) ⟨1210014, by rfl⟩ : syracuseStep 3226705 = 2420029) B2420029
theorem B4086865 : Blo 1790096 4086865 := bstep (se 2 (by rfl) ⟨1532574, by rfl⟩ : syracuseStep 4086865 = 3065149) B3065149
theorem B3021907 : Blo 1790096 3021907 := bstep (se 1 (by rfl) ⟨2266430, by rfl⟩ : syracuseStep 3021907 = 4532861) B4532861
theorem B2686049 : Blo 1790096 2686049 := bstep (se 2 (by rfl) ⟨1007268, by rfl⟩ : syracuseStep 2686049 = 2014537) B2014537
theorem B2686067 : Blo 1790096 2686067 := bstep (se 1 (by rfl) ⟨2014550, by rfl⟩ : syracuseStep 2686067 = 4029101) B4029101
theorem B2014339 : Blo 1790096 2014339 := bstep (se 1 (by rfl) ⟨1510754, by rfl⟩ : syracuseStep 2014339 = 3021509) B3021509
theorem B6044813 : Blo 1790096 6044813 := bstep (se 3 (by rfl) ⟨1133402, by rfl⟩ : syracuseStep 6044813 = 2266805) B2266805
theorem B2686097 : Blo 1790096 2686097 := bstep (se 2 (by rfl) ⟨1007286, by rfl⟩ : syracuseStep 2686097 = 2014573) B2014573
theorem B2686115 : Blo 1790096 2686115 := bstep (se 1 (by rfl) ⟨2014586, by rfl⟩ : syracuseStep 2686115 = 4029173) B4029173
theorem B8166577 : Blo 1790096 8166577 := bstep (se 2 (by rfl) ⟨3062466, by rfl⟩ : syracuseStep 8166577 = 6124933) B6124933
theorem B2686145 : Blo 1790096 2686145 := bstep (se 2 (by rfl) ⟨1007304, by rfl⟩ : syracuseStep 2686145 = 2014609) B2014609
theorem B6044867 : Blo 1790096 6044867 := bstep (se 1 (by rfl) ⟨4533650, by rfl⟩ : syracuseStep 6044867 = 9067301) B9067301
theorem B2686163 : Blo 1790096 2686163 := bstep (se 1 (by rfl) ⟨2014622, by rfl⟩ : syracuseStep 2686163 = 4029245) B4029245
theorem B3022049 : Blo 1790096 3022049 := bstep (se 2 (by rfl) ⟨1133268, by rfl⟩ : syracuseStep 3022049 = 2266537) B2266537
theorem B6798563 : Blo 1790096 6798563 := bstep (se 1 (by rfl) ⟨5098922, by rfl⟩ : syracuseStep 6798563 = 10197845) B10197845
theorem B6208753 : Blo 1790096 6208753 := bstep (se 2 (by rfl) ⟨2328282, by rfl⟩ : syracuseStep 6208753 = 4656565) B4656565
theorem B2686193 : Blo 1790096 2686193 := bstep (se 2 (by rfl) ⟨1007322, by rfl⟩ : syracuseStep 2686193 = 2014645) B2014645
theorem B2686211 : Blo 1790096 2686211 := bstep (se 1 (by rfl) ⟨2014658, by rfl⟩ : syracuseStep 2686211 = 4029317) B4029317
theorem B4029713 : Blo 1790096 4029713 := bstep (se 2 (by rfl) ⟨1511142, by rfl⟩ : syracuseStep 4029713 = 3022285) B3022285
theorem B2014483 : Blo 1790096 2014483 := bstep (se 1 (by rfl) ⟨1510862, by rfl⟩ : syracuseStep 2014483 = 3021725) B3021725
theorem B2686241 : Blo 1790096 2686241 := bstep (se 2 (by rfl) ⟨1007340, by rfl⟩ : syracuseStep 2686241 = 2014681) B2014681
theorem B4029731 : Blo 1790096 4029731 := bstep (se 1 (by rfl) ⟨3022298, by rfl⟩ : syracuseStep 4029731 = 6044597) B6044597
theorem B2686259 : Blo 1790096 2686259 := bstep (se 1 (by rfl) ⟨2014694, by rfl⟩ : syracuseStep 2686259 = 4029389) B4029389
theorem B3398993 : Blo 1790096 3398993 := bstep (se 2 (by rfl) ⟨1274622, by rfl⟩ : syracuseStep 3398993 = 2549245) B2549245
theorem B2686289 : Blo 1790096 2686289 := bstep (se 2 (by rfl) ⟨1007358, by rfl⟩ : syracuseStep 2686289 = 2014717) B2014717
theorem B3022177 : Blo 1790096 3022177 := bstep (se 2 (by rfl) ⟨1133316, by rfl⟩ : syracuseStep 3022177 = 2266633) B2266633
theorem B2686307 : Blo 1790096 2686307 := bstep (se 1 (by rfl) ⟨2014730, by rfl⟩ : syracuseStep 2686307 = 4029461) B4029461
theorem B3824995 : Blo 1790096 3824995 := bstep (se 1 (by rfl) ⟨2868746, by rfl⟩ : syracuseStep 3824995 = 5737493) B5737493
theorem B2686337 : Blo 1790096 2686337 := bstep (se 2 (by rfl) ⟨1007376, by rfl⟩ : syracuseStep 2686337 = 2014753) B2014753
theorem B3022211 : Blo 1790096 3022211 := bstep (se 1 (by rfl) ⟨2266658, by rfl⟩ : syracuseStep 3022211 = 4533317) B4533317
theorem B2686355 : Blo 1790096 2686355 := bstep (se 1 (by rfl) ⟨2014766, by rfl⟩ : syracuseStep 2686355 = 4029533) B4029533
theorem B2014627 : Blo 1790096 2014627 := bstep (se 1 (by rfl) ⟨1510970, by rfl⟩ : syracuseStep 2014627 = 3021941) B3021941
theorem B2686385 : Blo 1790096 2686385 := bstep (se 2 (by rfl) ⟨1007394, by rfl⟩ : syracuseStep 2686385 = 2014789) B2014789
theorem B2686403 : Blo 1790096 2686403 := bstep (se 1 (by rfl) ⟨2014802, by rfl⟩ : syracuseStep 2686403 = 4029605) B4029605
theorem B6045137 : Blo 1790096 6045137 := bstep (se 2 (by rfl) ⟨2266926, by rfl⟩ : syracuseStep 6045137 = 4533853) B4533853
theorem B2686433 : Blo 1790096 2686433 := bstep (se 2 (by rfl) ⟨1007412, by rfl⟩ : syracuseStep 2686433 = 2014825) B2014825
theorem B2686451 : Blo 1790096 2686451 := bstep (se 1 (by rfl) ⟨2014838, by rfl⟩ : syracuseStep 2686451 = 4029677) B4029677
theorem B3022339 : Blo 1790096 3022339 := bstep (se 1 (by rfl) ⟨2266754, by rfl⟩ : syracuseStep 3022339 = 4533509) B4533509
theorem B2686481 : Blo 1790096 2686481 := bstep (se 2 (by rfl) ⟨1007430, by rfl⟩ : syracuseStep 2686481 = 2014861) B2014861
theorem B2686499 : Blo 1790096 2686499 := bstep (se 1 (by rfl) ⟨2014874, by rfl⟩ : syracuseStep 2686499 = 4029749) B4029749
theorem B4030001 : Blo 1790096 4030001 := bstep (se 2 (by rfl) ⟨1511250, by rfl⟩ : syracuseStep 4030001 = 3022501) B3022501
theorem B2014771 : Blo 1790096 2014771 := bstep (se 1 (by rfl) ⟨1511078, by rfl⟩ : syracuseStep 2014771 = 3022157) B3022157
theorem B2686529 : Blo 1790096 2686529 := bstep (se 2 (by rfl) ⟨1007448, by rfl⟩ : syracuseStep 2686529 = 2014897) B2014897
theorem B4030019 : Blo 1790096 4030019 := bstep (se 1 (by rfl) ⟨3022514, by rfl⟩ : syracuseStep 4030019 = 6045029) B6045029
theorem B2686547 : Blo 1790096 2686547 := bstep (se 1 (by rfl) ⟨2014910, by rfl⟩ : syracuseStep 2686547 = 4029821) B4029821
theorem B2686577 : Blo 1790096 2686577 := bstep (se 2 (by rfl) ⟨1007466, by rfl⟩ : syracuseStep 2686577 = 2014933) B2014933
theorem B2686595 : Blo 1790096 2686595 := bstep (se 1 (by rfl) ⟨2014946, by rfl⟩ : syracuseStep 2686595 = 4029893) B4029893
theorem B13606541 : Blo 1790096 13606541 := bstep (se 3 (by rfl) ⟨2551226, by rfl⟩ : syracuseStep 13606541 = 5102453) B5102453
theorem B3022481 : Blo 1790096 3022481 := bstep (se 2 (by rfl) ⟨1133430, by rfl⟩ : syracuseStep 3022481 = 2266861) B2266861
theorem B2686625 : Blo 1790096 2686625 := bstep (se 2 (by rfl) ⟨1007484, by rfl⟩ : syracuseStep 2686625 = 2014969) B2014969
theorem B2686643 : Blo 1790096 2686643 := bstep (se 1 (by rfl) ⟨2014982, by rfl⟩ : syracuseStep 2686643 = 4029965) B4029965
theorem B2014915 : Blo 1790096 2014915 := bstep (se 1 (by rfl) ⟨1511186, by rfl⟩ : syracuseStep 2014915 = 3022373) B3022373
theorem B2686673 : Blo 1790096 2686673 := bstep (se 2 (by rfl) ⟨1007502, by rfl⟩ : syracuseStep 2686673 = 2015005) B2015005
theorem B2686691 : Blo 1790096 2686691 := bstep (se 1 (by rfl) ⟨2015018, by rfl⟩ : syracuseStep 2686691 = 4030037) B4030037
theorem B9068273 : Blo 1790096 9068273 := bstep (se 2 (by rfl) ⟨3400602, by rfl⟩ : syracuseStep 9068273 = 6801205) B6801205
theorem B2686721 : Blo 1790096 2686721 := bstep (se 2 (by rfl) ⟨1007520, by rfl⟩ : syracuseStep 2686721 = 2015041) B2015041
theorem B3022609 : Blo 1790096 3022609 := bstep (se 2 (by rfl) ⟨1133478, by rfl⟩ : syracuseStep 3022609 = 2266957) B2266957
theorem B2686739 : Blo 1790096 2686739 := bstep (se 1 (by rfl) ⟨2015054, by rfl⟩ : syracuseStep 2686739 = 4030109) B4030109
theorem B2686769 : Blo 1790096 2686769 := bstep (se 2 (by rfl) ⟨1007538, by rfl⟩ : syracuseStep 2686769 = 2015077) B2015077
theorem B3022643 : Blo 1790096 3022643 := bstep (se 1 (by rfl) ⟨2266982, by rfl⟩ : syracuseStep 3022643 = 4533965) B4533965
theorem B2686787 : Blo 1790096 2686787 := bstep (se 1 (by rfl) ⟨2015090, by rfl⟩ : syracuseStep 2686787 = 4030181) B4030181
theorem B4030289 : Blo 1790096 4030289 := bstep (se 2 (by rfl) ⟨1511358, by rfl⟩ : syracuseStep 4030289 = 3022717) B3022717
theorem B2015059 : Blo 1790096 2015059 := bstep (se 1 (by rfl) ⟨1511294, by rfl⟩ : syracuseStep 2015059 = 3022589) B3022589
theorem B2686817 : Blo 1790096 2686817 := bstep (se 2 (by rfl) ⟨1007556, by rfl⟩ : syracuseStep 2686817 = 2015113) B2015113
theorem B4030307 : Blo 1790096 4030307 := bstep (se 1 (by rfl) ⟨3022730, by rfl⟩ : syracuseStep 4030307 = 6045461) B6045461
theorem B24838001 : Blo 1790096 24838001 := bstep (se 2 (by rfl) ⟨9314250, by rfl⟩ : syracuseStep 24838001 = 18628501) B18628501
theorem B2686835 : Blo 1790096 2686835 := bstep (se 1 (by rfl) ⟨2015126, by rfl⟩ : syracuseStep 2686835 = 4030253) B4030253
theorem B2686865 : Blo 1790096 2686865 := bstep (se 2 (by rfl) ⟨1007574, by rfl⟩ : syracuseStep 2686865 = 2015149) B2015149
theorem B2686883 : Blo 1790096 2686883 := bstep (se 1 (by rfl) ⟨2015162, by rfl⟩ : syracuseStep 2686883 = 4030325) B4030325
theorem B3022771 : Blo 1790096 3022771 := bstep (se 1 (by rfl) ⟨2267078, by rfl⟩ : syracuseStep 3022771 = 4534157) B4534157
theorem B2686913 : Blo 1790096 2686913 := bstep (se 2 (by rfl) ⟨1007592, by rfl⟩ : syracuseStep 2686913 = 2015185) B2015185
theorem B2686931 : Blo 1790096 2686931 := bstep (se 1 (by rfl) ⟨2015198, by rfl⟩ : syracuseStep 2686931 = 4030397) B4030397
theorem B2015203 : Blo 1790096 2015203 := bstep (se 1 (by rfl) ⟨1511402, by rfl⟩ : syracuseStep 2015203 = 3022805) B3022805
theorem B6045677 : Blo 1790096 6045677 := bstep (se 3 (by rfl) ⟨1133564, by rfl⟩ : syracuseStep 6045677 = 2267129) B2267129
theorem B2686961 : Blo 1790096 2686961 := bstep (se 2 (by rfl) ⟨1007610, by rfl⟩ : syracuseStep 2686961 = 2015221) B2015221
theorem B3022859 : Blo 1790096 3022859 := bstep (se 1 (by rfl) ⟨2267144, by rfl⟩ : syracuseStep 3022859 = 4534289) B4534289
theorem B4030487 : Blo 1790096 4030487 := bstep (se 1 (by rfl) ⟨3022865, by rfl⟩ : syracuseStep 4030487 = 6045731) B6045731
theorem B2015275 : Blo 1790096 2015275 := bstep (se 1 (by rfl) ⟨1511456, by rfl⟩ : syracuseStep 2015275 = 3022913) B3022913
theorem B13598765 : Blo 1790096 13598765 := bstep (se 3 (by rfl) ⟨2549768, by rfl⟩ : syracuseStep 13598765 = 5099537) B5099537
theorem B3399745 : Blo 1790096 3399745 := bstep (se 2 (by rfl) ⟨1274904, by rfl⟩ : syracuseStep 3399745 = 2549809) B2549809
theorem B6455371 : Blo 1790096 6455371 := bstep (se 1 (by rfl) ⟨4841528, by rfl⟩ : syracuseStep 6455371 = 9683057) B9683057
theorem B2687051 : Blo 1790096 2687051 := bstep (se 1 (by rfl) ⟨2015288, by rfl⟩ : syracuseStep 2687051 = 4030577) B4030577
theorem B2687063 : Blo 1790096 2687063 := bstep (se 1 (by rfl) ⟨2015297, by rfl⟩ : syracuseStep 2687063 = 4030595) B4030595
theorem B6045785 : Blo 1790096 6045785 := bstep (se 2 (by rfl) ⟨2267169, by rfl⟩ : syracuseStep 6045785 = 4534339) B4534339
theorem B3022987 : Blo 1790096 3022987 := bstep (se 1 (by rfl) ⟨2267240, by rfl⟩ : syracuseStep 3022987 = 4534481) B4534481
theorem B2015383 : Blo 1790096 2015383 := bstep (se 1 (by rfl) ⟨1511537, by rfl⟩ : syracuseStep 2015383 = 3023075) B3023075
theorem B2687129 : Blo 1790096 2687129 := bstep (se 2 (by rfl) ⟨1007673, by rfl⟩ : syracuseStep 2687129 = 2015347) B2015347
theorem B4030667 : Blo 1790096 4030667 := bstep (se 1 (by rfl) ⟨3023000, by rfl⟩ : syracuseStep 4030667 = 6046001) B6046001
theorem B4030721 : Blo 1790096 4030721 := bstep (se 2 (by rfl) ⟨1511520, by rfl⟩ : syracuseStep 4030721 = 3023041) B3023041
theorem B3629323 : Blo 1790096 3629323 := bstep (se 1 (by rfl) ⟨2721992, by rfl⟩ : syracuseStep 3629323 = 5443985) B5443985
theorem B2687243 : Blo 1790096 2687243 := bstep (se 1 (by rfl) ⟨2015432, by rfl⟩ : syracuseStep 2687243 = 4030865) B4030865
theorem B9814289 : Blo 1790096 9814289 := bstep (se 2 (by rfl) ⟨3680358, by rfl⟩ : syracuseStep 9814289 = 7360717) B7360717
theorem B2687255 : Blo 1790096 2687255 := bstep (se 1 (by rfl) ⟨2015441, by rfl⟩ : syracuseStep 2687255 = 4030883) B4030883
theorem B3023129 : Blo 1790096 3023129 := bstep (se 2 (by rfl) ⟨1133673, by rfl⟩ : syracuseStep 3023129 = 2267347) B2267347
theorem B2015563 : Blo 1790096 2015563 := bstep (se 1 (by rfl) ⟨1511672, by rfl⟩ : syracuseStep 2015563 = 3023345) B3023345
theorem B2687321 : Blo 1790096 2687321 := bstep (se 2 (by rfl) ⟨1007745, by rfl⟩ : syracuseStep 2687321 = 2015491) B2015491
theorem B6799747 : Blo 1790096 6799747 := bstep (se 1 (by rfl) ⟨5099810, by rfl⟩ : syracuseStep 6799747 = 10199621) B10199621
theorem B3023257 : Blo 1790096 3023257 := bstep (se 2 (by rfl) ⟨1133721, by rfl⟩ : syracuseStep 3023257 = 2267443) B2267443
theorem B2015671 : Blo 1790096 2015671 := bstep (se 1 (by rfl) ⟨1511753, by rfl⟩ : syracuseStep 2015671 = 3023507) B3023507
theorem B2687435 : Blo 1790096 2687435 := bstep (se 1 (by rfl) ⟨2015576, by rfl⟩ : syracuseStep 2687435 = 4031153) B4031153
theorem B2687447 : Blo 1790096 2687447 := bstep (se 1 (by rfl) ⟨2015585, by rfl⟩ : syracuseStep 2687447 = 4031171) B4031171
theorem B4030937 : Blo 1790096 4030937 := bstep (se 2 (by rfl) ⟨1511601, by rfl⟩ : syracuseStep 4030937 = 3023203) B3023203
theorem B3400193 : Blo 1790096 3400193 := bstep (se 2 (by rfl) ⟨1275072, by rfl⟩ : syracuseStep 3400193 = 2550145) B2550145
theorem B2687513 : Blo 1790096 2687513 := bstep (se 2 (by rfl) ⟨1007817, by rfl⟩ : syracuseStep 2687513 = 2015635) B2015635
theorem B4031027 : Blo 1790096 4031027 := bstep (se 1 (by rfl) ⟨3023270, by rfl⟩ : syracuseStep 4031027 = 6046541) B6046541
theorem B4031063 : Blo 1790096 4031063 := bstep (se 1 (by rfl) ⟨3023297, by rfl⟩ : syracuseStep 4031063 = 6046595) B6046595
theorem B2015851 : Blo 1790096 2015851 := bstep (se 1 (by rfl) ⟨1511888, by rfl⟩ : syracuseStep 2015851 = 3023777) B3023777
theorem B2687627 : Blo 1790096 2687627 := bstep (se 1 (by rfl) ⟨2015720, by rfl⟩ : syracuseStep 2687627 = 4031441) B4031441
theorem B2687639 : Blo 1790096 2687639 := bstep (se 1 (by rfl) ⟨2015729, by rfl⟩ : syracuseStep 2687639 = 4031459) B4031459
theorem B6800051 : Blo 1790096 6800051 := bstep (se 1 (by rfl) ⟨5100038, by rfl⟩ : syracuseStep 6800051 = 10200077) B10200077
theorem B51651269 : Blo 1790096 51651269 := bstep (se 4 (by rfl) ⟨4842306, by rfl⟩ : syracuseStep 51651269 = 9684613) B9684613
theorem B3826379 : Blo 1790096 3826379 := bstep (se 1 (by rfl) ⟨2869784, by rfl⟩ : syracuseStep 3826379 = 5739569) B5739569
theorem B2015959 : Blo 1790096 2015959 := bstep (se 1 (by rfl) ⟨1511969, by rfl⟩ : syracuseStep 2015959 = 3023939) B3023939
theorem B2687705 : Blo 1790096 2687705 := bstep (se 2 (by rfl) ⟨1007889, by rfl⟩ : syracuseStep 2687705 = 2015779) B2015779
theorem B4031243 : Blo 1790096 4031243 := bstep (se 1 (by rfl) ⟨3023432, by rfl⟩ : syracuseStep 4031243 = 6046865) B6046865
theorem B9683729 : Blo 1790096 9683729 := bstep (se 2 (by rfl) ⟨3631398, by rfl⟩ : syracuseStep 9683729 = 7262797) B7262797
theorem B6046487 : Blo 1790096 6046487 := bstep (se 1 (by rfl) ⟨4534865, by rfl⟩ : syracuseStep 6046487 = 9069731) B9069731
theorem B3064601 : Blo 1790096 3064601 := bstep (se 2 (by rfl) ⟨1149225, by rfl⟩ : syracuseStep 3064601 = 2298451) B2298451
theorem B4031297 : Blo 1790096 4031297 := bstep (se 2 (by rfl) ⟨1511736, by rfl⟩ : syracuseStep 4031297 = 3023473) B3023473
theorem B2687819 : Blo 1790096 2687819 := bstep (se 1 (by rfl) ⟨2015864, by rfl⟩ : syracuseStep 2687819 = 4031729) B4031729
theorem B3400535 : Blo 1790096 3400535 := bstep (se 1 (by rfl) ⟨2550401, by rfl⟩ : syracuseStep 3400535 = 5100803) B5100803
theorem B2687831 : Blo 1790096 2687831 := bstep (se 1 (by rfl) ⟨2015873, by rfl⟩ : syracuseStep 2687831 = 4031747) B4031747
theorem B2687897 : Blo 1790096 2687897 := bstep (se 2 (by rfl) ⟨1007961, by rfl⟩ : syracuseStep 2687897 = 2015923) B2015923
theorem B3023831 : Blo 1790096 3023831 := bstep (se 1 (by rfl) ⟨2267873, by rfl⟩ : syracuseStep 3023831 = 4535747) B4535747
theorem B4596697 : Blo 1790096 4596697 := bstep (se 2 (by rfl) ⟨1723761, by rfl⟩ : syracuseStep 4596697 = 3447523) B3447523
theorem B2688011 : Blo 1790096 2688011 := bstep (se 1 (by rfl) ⟨2016008, by rfl⟩ : syracuseStep 2688011 = 4032017) B4032017
theorem B2868247 : Blo 1790096 2868247 := bstep (se 1 (by rfl) ⟨2151185, by rfl⟩ : syracuseStep 2868247 = 4302371) B4302371
theorem B2688023 : Blo 1790096 2688023 := bstep (se 1 (by rfl) ⟨2016017, by rfl⟩ : syracuseStep 2688023 = 4032035) B4032035
theorem B4031513 : Blo 1790096 4031513 := bstep (se 2 (by rfl) ⟨1511817, by rfl⟩ : syracuseStep 4031513 = 3023635) B3023635
theorem B25814051 : Blo 1790096 25814051 := bstep (se 1 (by rfl) ⟨19360538, by rfl⟩ : syracuseStep 25814051 = 38721077) B38721077
theorem B2868311 : Blo 1790096 2868311 := bstep (se 1 (by rfl) ⟨2151233, by rfl⟩ : syracuseStep 2868311 = 4302467) B4302467
theorem B3023959 : Blo 1790096 3023959 := bstep (se 1 (by rfl) ⟨2267969, by rfl⟩ : syracuseStep 3023959 = 4535939) B4535939
theorem B2688089 : Blo 1790096 2688089 := bstep (se 2 (by rfl) ⟨1008033, by rfl⟩ : syracuseStep 2688089 = 2016067) B2016067
theorem B4031603 : Blo 1790096 4031603 := bstep (se 1 (by rfl) ⟨3023702, by rfl⟩ : syracuseStep 4031603 = 6047405) B6047405
theorem B4031639 : Blo 1790096 4031639 := bstep (se 1 (by rfl) ⟨3023729, by rfl⟩ : syracuseStep 4031639 = 6047459) B6047459
theorem B4531403 : Blo 1790096 4531403 := bstep (se 1 (by rfl) ⟨3398552, by rfl⟩ : syracuseStep 4531403 = 6797105) B6797105
theorem B2868439 : Blo 1790096 2868439 := bstep (se 1 (by rfl) ⟨2151329, by rfl⟩ : syracuseStep 2868439 = 4302659) B4302659
theorem B13092101 : Blo 1790096 13092101 := bstep (se 4 (by rfl) ⟨1227384, by rfl⟩ : syracuseStep 13092101 = 2454769) B2454769
theorem B2549017 : Blo 1790096 2549017 := bstep (se 2 (by rfl) ⟨955881, by rfl⟩ : syracuseStep 2549017 = 1911763) B1911763
theorem B3630361 : Blo 1790096 3630361 := bstep (se 2 (by rfl) ⟨1361385, by rfl⟩ : syracuseStep 3630361 = 2722771) B2722771
theorem B9684269 : Blo 1790096 9684269 := bstep (se 3 (by rfl) ⟨1815800, by rfl⟩ : syracuseStep 9684269 = 3631601) B3631601
theorem B6047027 : Blo 1790096 6047027 := bstep (se 1 (by rfl) ⟨4535270, by rfl⟩ : syracuseStep 6047027 = 9070541) B9070541
theorem B6800705 : Blo 1790096 6800705 := bstep (se 2 (by rfl) ⟨2550264, by rfl⟩ : syracuseStep 6800705 = 5100529) B5100529
theorem B4031819 : Blo 1790096 4031819 := bstep (se 1 (by rfl) ⟨3023864, by rfl⟩ : syracuseStep 4031819 = 6047729) B6047729
theorem B4031873 : Blo 1790096 4031873 := bstep (se 2 (by rfl) ⟨1511952, by rfl⟩ : syracuseStep 4031873 = 3023905) B3023905
theorem B5596609 : Blo 1790096 5596609 := bstep (se 2 (by rfl) ⟨2098728, by rfl⟩ : syracuseStep 5596609 = 4197457) B4197457
theorem B3401203 : Blo 1790096 3401203 := bstep (se 1 (by rfl) ⟨2550902, by rfl⟩ : syracuseStep 3401203 = 5101805) B5101805
theorem B15713837 : Blo 1790096 15713837 := bstep (se 3 (by rfl) ⟨2946344, by rfl⟩ : syracuseStep 15713837 = 5892689) B5892689
theorem B5522995 : Blo 1790096 5522995 := bstep (se 1 (by rfl) ⟨4142246, by rfl⟩ : syracuseStep 5522995 = 8284493) B8284493
theorem B10888769 : Blo 1790096 10888769 := bstep (se 2 (by rfl) ⟨4083288, by rfl⟩ : syracuseStep 10888769 = 8166577) B8166577
theorem B6047297 : Blo 1790096 6047297 := bstep (se 2 (by rfl) ⟨2267736, by rfl⟩ : syracuseStep 6047297 = 4535473) B4535473
theorem B4032089 : Blo 1790096 4032089 := bstep (se 2 (by rfl) ⟨1512033, by rfl⟩ : syracuseStep 4032089 = 3024067) B3024067
theorem B2868875 : Blo 1790096 2868875 := bstep (se 1 (by rfl) ⟨2151656, by rfl⟩ : syracuseStep 2868875 = 4303313) B4303313
theorem B3827353 : Blo 1790096 3827353 := bstep (se 2 (by rfl) ⟨1435257, by rfl⟩ : syracuseStep 3827353 = 2870515) B2870515
theorem B4032179 : Blo 1790096 4032179 := bstep (se 1 (by rfl) ⟨3024134, by rfl⟩ : syracuseStep 4032179 = 6048269) B6048269
theorem B4032215 : Blo 1790096 4032215 := bstep (se 1 (by rfl) ⟨3024161, by rfl⟩ : syracuseStep 4032215 = 6048323) B6048323
theorem B2869067 : Blo 1790096 2869067 := bstep (se 1 (by rfl) ⟨2151800, by rfl⟩ : syracuseStep 2869067 = 4303601) B4303601
theorem B47155043 : Blo 1790096 47155043 := bstep (se 1 (by rfl) ⟨35366282, by rfl⟩ : syracuseStep 47155043 = 70732565) B70732565
theorem B3401651 : Blo 1790096 3401651 := bstep (se 1 (by rfl) ⟨2551238, by rfl⟩ : syracuseStep 3401651 = 5102477) B5102477
theorem B3401689 : Blo 1790096 3401689 := bstep (se 2 (by rfl) ⟨1275633, by rfl⟩ : syracuseStep 3401689 = 2551267) B2551267
theorem B6047837 : Blo 1790096 6047837 := bstep (se 3 (by rfl) ⟨1133969, by rfl⟩ : syracuseStep 6047837 = 2267939) B2267939
theorem B8603779 : Blo 1790096 8603779 := bstep (se 1 (by rfl) ⟨6452834, by rfl⟩ : syracuseStep 8603779 = 12905669) B12905669
theorem B16337027 : Blo 1790096 16337027 := bstep (se 1 (by rfl) ⟨12252770, by rfl⟩ : syracuseStep 16337027 = 24505541) B24505541
theorem B4532375 : Blo 1790096 4532375 := bstep (se 1 (by rfl) ⟨3399281, by rfl⟩ : syracuseStep 4532375 = 6798563) B6798563
theorem B9070865 : Blo 1790096 9070865 := bstep (se 2 (by rfl) ⟨3401574, by rfl⟩ : syracuseStep 9070865 = 6803149) B6803149
theorem B3402137 : Blo 1790096 3402137 := bstep (se 2 (by rfl) ⟨1275801, by rfl⟩ : syracuseStep 3402137 = 2551603) B2551603
theorem B9071027 : Blo 1790096 9071027 := bstep (se 1 (by rfl) ⟨6803270, by rfl⟩ : syracuseStep 9071027 = 13606541) B13606541
theorem B6801965 : Blo 1790096 6801965 := bstep (se 3 (by rfl) ⟨1275368, by rfl⟩ : syracuseStep 6801965 = 2550737) B2550737
theorem B11635265 : Blo 1790096 11635265 := bstep (se 2 (by rfl) ⟨4363224, by rfl⟩ : syracuseStep 11635265 = 8726449) B8726449
theorem B7653953 : Blo 1790096 7653953 := bstep (se 2 (by rfl) ⟨2870232, by rfl⟩ : syracuseStep 7653953 = 5740465) B5740465
theorem B16558667 : Blo 1790096 16558667 := bstep (se 1 (by rfl) ⟨12419000, by rfl⟩ : syracuseStep 16558667 = 24838001) B24838001
theorem B6801995 : Blo 1790096 6801995 := bstep (se 1 (by rfl) ⟨5101496, by rfl⟩ : syracuseStep 6801995 = 10202993) B10202993
theorem B2550361 : Blo 1790096 2550361 := bstep (se 2 (by rfl) ⟨956385, by rfl⟩ : syracuseStep 2550361 = 1912771) B1912771
theorem B2550475 : Blo 1790096 2550475 := bstep (se 1 (by rfl) ⟨1912856, by rfl⟩ : syracuseStep 2550475 = 3825713) B3825713
theorem B8604377 : Blo 1790096 8604377 := bstep (se 2 (by rfl) ⟨3226641, by rfl⟩ : syracuseStep 8604377 = 6453283) B6453283
theorem B84962033 : Blo 1790096 84962033 := bstep (se 2 (by rfl) ⟨31860762, by rfl⟩ : syracuseStep 84962033 = 63721525) B63721525
theorem B4533043 : Blo 1790096 4533043 := bstep (se 1 (by rfl) ⟨3399782, by rfl⟩ : syracuseStep 4533043 = 6799565) B6799565
theorem B4533185 : Blo 1790096 4533185 := bstep (se 2 (by rfl) ⟨1699944, by rfl⟩ : syracuseStep 4533185 = 3399889) B3399889
theorem B9063575 : Blo 1790096 9063575 := bstep (se 1 (by rfl) ⟨6797681, by rfl⟩ : syracuseStep 9063575 = 13595363) B13595363
theorem B9678041 : Blo 1790096 9678041 := bstep (se 2 (by rfl) ⟨3629265, by rfl⟩ : syracuseStep 9678041 = 7258531) B7258531
theorem B6802649 : Blo 1790096 6802649 := bstep (se 2 (by rfl) ⟨2550993, by rfl⟩ : syracuseStep 6802649 = 5101987) B5101987
theorem B2870489 : Blo 1790096 2870489 := bstep (se 2 (by rfl) ⟨1076433, by rfl⟩ : syracuseStep 2870489 = 2152867) B2152867
theorem B5098717 : Blo 1790096 5098717 := bstep (se 3 (by rfl) ⟨956009, by rfl⟩ : syracuseStep 5098717 = 1912019) B1912019
theorem B7654621 : Blo 1790096 7654621 := bstep (se 3 (by rfl) ⟨1435241, by rfl⟩ : syracuseStep 7654621 = 2870483) B2870483
theorem B6458717 : Blo 1790096 6458717 := bstep (se 3 (by rfl) ⟨1211009, by rfl⟩ : syracuseStep 6458717 = 2422019) B2422019
theorem B186224021 : Blo 1790096 186224021 := bstep (se 6 (by rfl) ⟨4364625, by rfl⟩ : syracuseStep 186224021 = 8729251) B8729251
theorem B5098945 : Blo 1790096 5098945 := bstep (se 2 (by rfl) ⟨1912104, by rfl⟩ : syracuseStep 5098945 = 3824209) B3824209
theorem B6802967 : Blo 1790096 6802967 := bstep (se 1 (by rfl) ⟨5102225, by rfl⟩ : syracuseStep 6802967 = 10204451) B10204451
theorem B15502913 : Blo 1790096 15502913 := bstep (se 2 (by rfl) ⟨5813592, by rfl⟩ : syracuseStep 15502913 = 11627185) B11627185
theorem B2420375 : Blo 1790096 2420375 := bstep (se 1 (by rfl) ⟨1815281, by rfl⟩ : syracuseStep 2420375 = 3630563) B3630563
theorem B5099287 : Blo 1790096 5099287 := bstep (se 1 (by rfl) ⟨3824465, by rfl⟩ : syracuseStep 5099287 = 7648931) B7648931
theorem B13602653 : Blo 1790096 13602653 := bstep (se 3 (by rfl) ⟨2550497, by rfl⟩ : syracuseStep 13602653 = 5100995) B5100995
theorem B30609251 : Blo 1790096 30609251 := bstep (se 1 (by rfl) ⟨22956938, by rfl⟩ : syracuseStep 30609251 = 45913877) B45913877
theorem B6983597 : Blo 1790096 6983597 := bstep (se 3 (by rfl) ⟨1309424, by rfl⟩ : syracuseStep 6983597 = 2618849) B2618849
theorem B37277617 : Blo 1790096 37277617 := bstep (se 2 (by rfl) ⟨13979106, by rfl⟩ : syracuseStep 37277617 = 27958213) B27958213
theorem B7647155 : Blo 1790096 7647155 := bstep (se 1 (by rfl) ⟨5735366, by rfl⟩ : syracuseStep 7647155 = 11470733) B11470733
theorem B8171543 : Blo 1790096 8171543 := bstep (se 1 (by rfl) ⟨6128657, by rfl⟩ : syracuseStep 8171543 = 12257315) B12257315
theorem B16330817 : Blo 1790096 16330817 := bstep (se 2 (by rfl) ⟨6124056, by rfl⟩ : syracuseStep 16330817 = 12248113) B12248113
theorem B13791325 : Blo 1790096 13791325 := bstep (se 3 (by rfl) ⟨2585873, by rfl⟩ : syracuseStep 13791325 = 5171747) B5171747
theorem B1790103 : Blo 1790096 1790103 := bstep (se 1 (by rfl) ⟨1342577, by rfl⟩ : syracuseStep 1790103 = 2685155) B2685155
theorem B5738647 : Blo 1790096 5738647 := bstep (se 1 (by rfl) ⟨4303985, by rfl⟩ : syracuseStep 5738647 = 8607971) B8607971
theorem B1790123 : Blo 1790096 1790123 := bstep (se 1 (by rfl) ⟨1342592, by rfl⟩ : syracuseStep 1790123 = 2685185) B2685185
theorem B4534451 : Blo 1790096 4534451 := bstep (se 1 (by rfl) ⟨3400838, by rfl⟩ : syracuseStep 4534451 = 6801677) B6801677
theorem B6803635 : Blo 1790096 6803635 := bstep (se 1 (by rfl) ⟨5102726, by rfl⟩ : syracuseStep 6803635 = 10205453) B10205453
theorem B1790135 : Blo 1790096 1790135 := bstep (se 1 (by rfl) ⟨1342601, by rfl⟩ : syracuseStep 1790135 = 2685203) B2685203
theorem B1790155 : Blo 1790096 1790155 := bstep (se 1 (by rfl) ⟨1342616, by rfl⟩ : syracuseStep 1790155 = 2685233) B2685233
theorem B1790167 : Blo 1790096 1790167 := bstep (se 1 (by rfl) ⟨1342625, by rfl⟩ : syracuseStep 1790167 = 2685251) B2685251
theorem B1790187 : Blo 1790096 1790187 := bstep (se 1 (by rfl) ⟨1342640, by rfl⟩ : syracuseStep 1790187 = 2685281) B2685281
theorem B1790199 : Blo 1790096 1790199 := bstep (se 1 (by rfl) ⟨1342649, by rfl⟩ : syracuseStep 1790199 = 2685299) B2685299
theorem B1790219 : Blo 1790096 1790219 := bstep (se 1 (by rfl) ⟨1342664, by rfl⟩ : syracuseStep 1790219 = 2685329) B2685329
theorem B1790231 : Blo 1790096 1790231 := bstep (se 1 (by rfl) ⟨1342673, by rfl⟩ : syracuseStep 1790231 = 2685347) B2685347
theorem B1790251 : Blo 1790096 1790251 := bstep (se 1 (by rfl) ⟨1342688, by rfl⟩ : syracuseStep 1790251 = 2685377) B2685377
theorem B1790263 : Blo 1790096 1790263 := bstep (se 1 (by rfl) ⟨1342697, by rfl⟩ : syracuseStep 1790263 = 2685395) B2685395
theorem B8278337 : Blo 1790096 8278337 := bstep (se 2 (by rfl) ⟨3104376, by rfl⟩ : syracuseStep 8278337 = 6208753) B6208753
theorem B1790283 : Blo 1790096 1790283 := bstep (se 1 (by rfl) ⟨1342712, by rfl⟩ : syracuseStep 1790283 = 2685425) B2685425
theorem B1790295 : Blo 1790096 1790295 := bstep (se 1 (by rfl) ⟨1342721, by rfl⟩ : syracuseStep 1790295 = 2685443) B2685443
theorem B4084055 : Blo 1790096 4084055 := bstep (se 1 (by rfl) ⟨3063041, by rfl⟩ : syracuseStep 4084055 = 6126083) B6126083
theorem B1790315 : Blo 1790096 1790315 := bstep (se 1 (by rfl) ⟨1342736, by rfl⟩ : syracuseStep 1790315 = 2685473) B2685473
theorem B1790327 : Blo 1790096 1790327 := bstep (se 1 (by rfl) ⟨1342745, by rfl⟩ : syracuseStep 1790327 = 2685491) B2685491
theorem B1790347 : Blo 1790096 1790347 := bstep (se 1 (by rfl) ⟨1342760, by rfl⟩ : syracuseStep 1790347 = 2685521) B2685521
theorem B1790359 : Blo 1790096 1790359 := bstep (se 1 (by rfl) ⟨1342769, by rfl⟩ : syracuseStep 1790359 = 2685539) B2685539
theorem B1790379 : Blo 1790096 1790379 := bstep (se 1 (by rfl) ⟨1342784, by rfl⟩ : syracuseStep 1790379 = 2685569) B2685569
theorem B1790391 : Blo 1790096 1790391 := bstep (se 1 (by rfl) ⟨1342793, by rfl⟩ : syracuseStep 1790391 = 2685587) B2685587
theorem B6042059 : Blo 1790096 6042059 := bstep (se 1 (by rfl) ⟨4531544, by rfl⟩ : syracuseStep 6042059 = 9063089) B9063089
theorem B1790411 : Blo 1790096 1790411 := bstep (se 1 (by rfl) ⟨1342808, by rfl⟩ : syracuseStep 1790411 = 2685617) B2685617
theorem B1790423 : Blo 1790096 1790423 := bstep (se 1 (by rfl) ⟨1342817, by rfl⟩ : syracuseStep 1790423 = 2685635) B2685635
theorem B5099993 : Blo 1790096 5099993 := bstep (se 2 (by rfl) ⟨1912497, by rfl⟩ : syracuseStep 5099993 = 3824995) B3824995
theorem B1790443 : Blo 1790096 1790443 := bstep (se 1 (by rfl) ⟨1342832, by rfl⟩ : syracuseStep 1790443 = 2685665) B2685665
theorem B1790455 : Blo 1790096 1790455 := bstep (se 1 (by rfl) ⟨1342841, by rfl⟩ : syracuseStep 1790455 = 2685683) B2685683
theorem B1790475 : Blo 1790096 1790475 := bstep (se 1 (by rfl) ⟨1342856, by rfl⟩ : syracuseStep 1790475 = 2685713) B2685713
theorem B1790487 : Blo 1790096 1790487 := bstep (se 1 (by rfl) ⟨1342865, by rfl⟩ : syracuseStep 1790487 = 2685731) B2685731
theorem B1790507 : Blo 1790096 1790507 := bstep (se 1 (by rfl) ⟨1342880, by rfl⟩ : syracuseStep 1790507 = 2685761) B2685761
theorem B1790519 : Blo 1790096 1790519 := bstep (se 1 (by rfl) ⟨1342889, by rfl⟩ : syracuseStep 1790519 = 2685779) B2685779
theorem B1790539 : Blo 1790096 1790539 := bstep (se 1 (by rfl) ⟨1342904, by rfl⟩ : syracuseStep 1790539 = 2685809) B2685809
theorem B5739083 : Blo 1790096 5739083 := bstep (se 1 (by rfl) ⟨4304312, by rfl⟩ : syracuseStep 5739083 = 8608625) B8608625
theorem B1790551 : Blo 1790096 1790551 := bstep (se 1 (by rfl) ⟨1342913, by rfl⟩ : syracuseStep 1790551 = 2685827) B2685827
theorem B1790571 : Blo 1790096 1790571 := bstep (se 1 (by rfl) ⟨1342928, by rfl⟩ : syracuseStep 1790571 = 2685857) B2685857
theorem B1790583 : Blo 1790096 1790583 := bstep (se 1 (by rfl) ⟨1342937, by rfl⟩ : syracuseStep 1790583 = 2685875) B2685875
theorem B1790603 : Blo 1790096 1790603 := bstep (se 1 (by rfl) ⟨1342952, by rfl⟩ : syracuseStep 1790603 = 2685905) B2685905
theorem B1938071 : Blo 1790096 1938071 := bstep (se 1 (by rfl) ⟨1453553, by rfl⟩ : syracuseStep 1938071 = 2907107) B2907107
theorem B1790615 : Blo 1790096 1790615 := bstep (se 1 (by rfl) ⟨1342961, by rfl⟩ : syracuseStep 1790615 = 2685923) B2685923
theorem B1790635 : Blo 1790096 1790635 := bstep (se 1 (by rfl) ⟨1342976, by rfl⟩ : syracuseStep 1790635 = 2685953) B2685953
theorem B1790647 : Blo 1790096 1790647 := bstep (se 1 (by rfl) ⟨1342985, by rfl⟩ : syracuseStep 1790647 = 2685971) B2685971
theorem B1790667 : Blo 1790096 1790667 := bstep (se 1 (by rfl) ⟨1343000, by rfl⟩ : syracuseStep 1790667 = 2686001) B2686001
theorem B4534987 : Blo 1790096 4534987 := bstep (se 1 (by rfl) ⟨3401240, by rfl⟩ : syracuseStep 4534987 = 6802481) B6802481
theorem B1790679 : Blo 1790096 1790679 := bstep (se 1 (by rfl) ⟨1343009, by rfl⟩ : syracuseStep 1790679 = 2686019) B2686019
theorem B6042329 : Blo 1790096 6042329 := bstep (se 2 (by rfl) ⟨2265873, by rfl⟩ : syracuseStep 6042329 = 4531747) B4531747
theorem B1790699 : Blo 1790096 1790699 := bstep (se 1 (by rfl) ⟨1343024, by rfl⟩ : syracuseStep 1790699 = 2686049) B2686049
theorem B1790711 : Blo 1790096 1790711 := bstep (se 1 (by rfl) ⟨1343033, by rfl⟩ : syracuseStep 1790711 = 2686067) B2686067
theorem B1913591 : Blo 1790096 1913591 := bstep (se 1 (by rfl) ⟨1435193, by rfl⟩ : syracuseStep 1913591 = 2870387) B2870387
theorem B1790731 : Blo 1790096 1790731 := bstep (se 1 (by rfl) ⟨1343048, by rfl⟩ : syracuseStep 1790731 = 2686097) B2686097
theorem B1790743 : Blo 1790096 1790743 := bstep (se 1 (by rfl) ⟨1343057, by rfl⟩ : syracuseStep 1790743 = 2686115) B2686115
theorem B1790763 : Blo 1790096 1790763 := bstep (se 1 (by rfl) ⟨1343072, by rfl⟩ : syracuseStep 1790763 = 2686145) B2686145
theorem B1790775 : Blo 1790096 1790775 := bstep (se 1 (by rfl) ⟨1343081, by rfl⟩ : syracuseStep 1790775 = 2686163) B2686163
theorem B1790795 : Blo 1790096 1790795 := bstep (se 1 (by rfl) ⟨1343096, by rfl⟩ : syracuseStep 1790795 = 2686193) B2686193
theorem B1790807 : Blo 1790096 1790807 := bstep (se 1 (by rfl) ⟨1343105, by rfl⟩ : syracuseStep 1790807 = 2686211) B2686211
theorem B4535129 : Blo 1790096 4535129 := bstep (se 2 (by rfl) ⟨1700673, by rfl⟩ : syracuseStep 4535129 = 3401347) B3401347
theorem B1790827 : Blo 1790096 1790827 := bstep (se 1 (by rfl) ⟨1343120, by rfl⟩ : syracuseStep 1790827 = 2686241) B2686241
theorem B1790839 : Blo 1790096 1790839 := bstep (se 1 (by rfl) ⟨1343129, by rfl⟩ : syracuseStep 1790839 = 2686259) B2686259
theorem B2265995 : Blo 1790096 2265995 := bstep (se 1 (by rfl) ⟨1699496, by rfl⟩ : syracuseStep 2265995 = 3398993) B3398993
theorem B1790859 : Blo 1790096 1790859 := bstep (se 1 (by rfl) ⟨1343144, by rfl⟩ : syracuseStep 1790859 = 2686289) B2686289
theorem B7648145 : Blo 1790096 7648145 := bstep (se 2 (by rfl) ⟨2868054, by rfl⟩ : syracuseStep 7648145 = 5736109) B5736109
theorem B1790871 : Blo 1790096 1790871 := bstep (se 1 (by rfl) ⟨1343153, by rfl⟩ : syracuseStep 1790871 = 2686307) B2686307
theorem B1790891 : Blo 1790096 1790891 := bstep (se 1 (by rfl) ⟨1343168, by rfl⟩ : syracuseStep 1790891 = 2686337) B2686337
theorem B1790903 : Blo 1790096 1790903 := bstep (se 1 (by rfl) ⟨1343177, by rfl⟩ : syracuseStep 1790903 = 2686355) B2686355
theorem B1790923 : Blo 1790096 1790923 := bstep (se 1 (by rfl) ⟨1343192, by rfl⟩ : syracuseStep 1790923 = 2686385) B2686385
theorem B1790935 : Blo 1790096 1790935 := bstep (se 1 (by rfl) ⟨1343201, by rfl⟩ : syracuseStep 1790935 = 2686403) B2686403
theorem B1790955 : Blo 1790096 1790955 := bstep (se 1 (by rfl) ⟨1343216, by rfl⟩ : syracuseStep 1790955 = 2686433) B2686433
theorem B1790967 : Blo 1790096 1790967 := bstep (se 1 (by rfl) ⟨1343225, by rfl⟩ : syracuseStep 1790967 = 2686451) B2686451
theorem B1790987 : Blo 1790096 1790987 := bstep (se 1 (by rfl) ⟨1343240, by rfl⟩ : syracuseStep 1790987 = 2686481) B2686481
theorem B10204177 : Blo 1790096 10204177 := bstep (se 2 (by rfl) ⟨3826566, by rfl⟩ : syracuseStep 10204177 = 7653133) B7653133
theorem B1790999 : Blo 1790096 1790999 := bstep (se 1 (by rfl) ⟨1343249, by rfl⟩ : syracuseStep 1790999 = 2686499) B2686499
theorem B36762659 : Blo 1790096 36762659 := bstep (se 1 (by rfl) ⟨27571994, by rfl⟩ : syracuseStep 36762659 = 55143989) B55143989
theorem B1791019 : Blo 1790096 1791019 := bstep (se 1 (by rfl) ⟨1343264, by rfl⟩ : syracuseStep 1791019 = 2686529) B2686529
theorem B1791031 : Blo 1790096 1791031 := bstep (se 1 (by rfl) ⟨1343273, by rfl⟩ : syracuseStep 1791031 = 2686547) B2686547
theorem B1791051 : Blo 1790096 1791051 := bstep (se 1 (by rfl) ⟨1343288, by rfl⟩ : syracuseStep 1791051 = 2686577) B2686577
theorem B1791063 : Blo 1790096 1791063 := bstep (se 1 (by rfl) ⟨1343297, by rfl⟩ : syracuseStep 1791063 = 2686595) B2686595
theorem B1791083 : Blo 1790096 1791083 := bstep (se 1 (by rfl) ⟨1343312, by rfl⟩ : syracuseStep 1791083 = 2686625) B2686625
theorem B1791095 : Blo 1790096 1791095 := bstep (se 1 (by rfl) ⟨1343321, by rfl⟩ : syracuseStep 1791095 = 2686643) B2686643
theorem B1791115 : Blo 1790096 1791115 := bstep (se 1 (by rfl) ⟨1343336, by rfl⟩ : syracuseStep 1791115 = 2686673) B2686673
theorem B1791127 : Blo 1790096 1791127 := bstep (se 1 (by rfl) ⟨1343345, by rfl⟩ : syracuseStep 1791127 = 2686691) B2686691
theorem B1791147 : Blo 1790096 1791147 := bstep (se 1 (by rfl) ⟨1343360, by rfl⟩ : syracuseStep 1791147 = 2686721) B2686721
theorem B1791159 : Blo 1790096 1791159 := bstep (se 1 (by rfl) ⟨1343369, by rfl⟩ : syracuseStep 1791159 = 2686739) B2686739
theorem B1791179 : Blo 1790096 1791179 := bstep (se 1 (by rfl) ⟨1343384, by rfl⟩ : syracuseStep 1791179 = 2686769) B2686769
theorem B1791191 : Blo 1790096 1791191 := bstep (se 1 (by rfl) ⟨1343393, by rfl⟩ : syracuseStep 1791191 = 2686787) B2686787
theorem B1791211 : Blo 1790096 1791211 := bstep (se 1 (by rfl) ⟨1343408, by rfl⟩ : syracuseStep 1791211 = 2686817) B2686817
theorem B1791223 : Blo 1790096 1791223 := bstep (se 1 (by rfl) ⟨1343417, by rfl⟩ : syracuseStep 1791223 = 2686835) B2686835
theorem B1791243 : Blo 1790096 1791243 := bstep (se 1 (by rfl) ⟨1343432, by rfl⟩ : syracuseStep 1791243 = 2686865) B2686865
theorem B1791255 : Blo 1790096 1791255 := bstep (se 1 (by rfl) ⟨1343441, by rfl⟩ : syracuseStep 1791255 = 2686883) B2686883
theorem B1791275 : Blo 1790096 1791275 := bstep (se 1 (by rfl) ⟨1343456, by rfl⟩ : syracuseStep 1791275 = 2686913) B2686913
theorem B1791287 : Blo 1790096 1791287 := bstep (se 1 (by rfl) ⟨1343465, by rfl⟩ : syracuseStep 1791287 = 2686931) B2686931
theorem B1791307 : Blo 1790096 1791307 := bstep (se 1 (by rfl) ⟨1343480, by rfl⟩ : syracuseStep 1791307 = 2686961) B2686961
theorem B1791319 : Blo 1790096 1791319 := bstep (se 1 (by rfl) ⟨1343489, by rfl⟩ : syracuseStep 1791319 = 2686979) B2686979
theorem B1791339 : Blo 1790096 1791339 := bstep (se 1 (by rfl) ⟨1343504, by rfl⟩ : syracuseStep 1791339 = 2687009) B2687009
theorem B1791351 : Blo 1790096 1791351 := bstep (se 1 (by rfl) ⟨1343513, by rfl⟩ : syracuseStep 1791351 = 2687027) B2687027
theorem B4027787 : Blo 1790096 4027787 := bstep (se 1 (by rfl) ⟨3020840, by rfl⟩ : syracuseStep 4027787 = 6041681) B6041681
theorem B1791371 : Blo 1790096 1791371 := bstep (se 1 (by rfl) ⟨1343528, by rfl⟩ : syracuseStep 1791371 = 2687057) B2687057
theorem B6043031 : Blo 1790096 6043031 := bstep (se 1 (by rfl) ⟨4532273, by rfl⟩ : syracuseStep 6043031 = 9064547) B9064547
theorem B1791383 : Blo 1790096 1791383 := bstep (se 1 (by rfl) ⟨1343537, by rfl⟩ : syracuseStep 1791383 = 2687075) B2687075
theorem B1791403 : Blo 1790096 1791403 := bstep (se 1 (by rfl) ⟨1343552, by rfl⟩ : syracuseStep 1791403 = 2687105) B2687105
theorem B1791415 : Blo 1790096 1791415 := bstep (se 1 (by rfl) ⟨1343561, by rfl⟩ : syracuseStep 1791415 = 2687123) B2687123
theorem B4838849 : Blo 1790096 4838849 := bstep (se 2 (by rfl) ⟨1814568, by rfl⟩ : syracuseStep 4838849 = 3629137) B3629137
theorem B4027841 : Blo 1790096 4027841 := bstep (se 2 (by rfl) ⟨1510440, by rfl⟩ : syracuseStep 4027841 = 3020881) B3020881
theorem B1791435 : Blo 1790096 1791435 := bstep (se 1 (by rfl) ⟨1343576, by rfl⟩ : syracuseStep 1791435 = 2687153) B2687153
theorem B5739979 : Blo 1790096 5739979 := bstep (se 1 (by rfl) ⟨4304984, by rfl⟩ : syracuseStep 5739979 = 8609969) B8609969
theorem B1791447 : Blo 1790096 1791447 := bstep (se 1 (by rfl) ⟨1343585, by rfl⟩ : syracuseStep 1791447 = 2687171) B2687171
theorem B1791467 : Blo 1790096 1791467 := bstep (se 1 (by rfl) ⟨1343600, by rfl⟩ : syracuseStep 1791467 = 2687201) B2687201
theorem B1791479 : Blo 1790096 1791479 := bstep (se 1 (by rfl) ⟨1343609, by rfl⟩ : syracuseStep 1791479 = 2687219) B2687219
theorem B1791499 : Blo 1790096 1791499 := bstep (se 1 (by rfl) ⟨1343624, by rfl⟩ : syracuseStep 1791499 = 2687249) B2687249
theorem B6796817 : Blo 1790096 6796817 := bstep (se 2 (by rfl) ⟨2548806, by rfl⟩ : syracuseStep 6796817 = 5097613) B5097613
theorem B4838935 : Blo 1790096 4838935 := bstep (se 1 (by rfl) ⟨3629201, by rfl⟩ : syracuseStep 4838935 = 7258403) B7258403
theorem B1791511 : Blo 1790096 1791511 := bstep (se 1 (by rfl) ⟨1343633, by rfl⟩ : syracuseStep 1791511 = 2687267) B2687267
theorem B1791531 : Blo 1790096 1791531 := bstep (se 1 (by rfl) ⟨1343648, by rfl⟩ : syracuseStep 1791531 = 2687297) B2687297
theorem B1791543 : Blo 1790096 1791543 := bstep (se 1 (by rfl) ⟨1343657, by rfl⟩ : syracuseStep 1791543 = 2687315) B2687315
theorem B4838977 : Blo 1790096 4838977 := bstep (se 2 (by rfl) ⟨1814616, by rfl⟩ : syracuseStep 4838977 = 3629233) B3629233
theorem B2266699 : Blo 1790096 2266699 := bstep (se 1 (by rfl) ⟨1700024, by rfl⟩ : syracuseStep 2266699 = 3400049) B3400049
theorem B1791563 : Blo 1790096 1791563 := bstep (se 1 (by rfl) ⟨1343672, by rfl⟩ : syracuseStep 1791563 = 2687345) B2687345
theorem B1791575 : Blo 1790096 1791575 := bstep (se 1 (by rfl) ⟨1343681, by rfl⟩ : syracuseStep 1791575 = 2687363) B2687363
theorem B1791595 : Blo 1790096 1791595 := bstep (se 1 (by rfl) ⟨1343696, by rfl⟩ : syracuseStep 1791595 = 2687393) B2687393
theorem B1791607 : Blo 1790096 1791607 := bstep (se 1 (by rfl) ⟨1343705, by rfl⟩ : syracuseStep 1791607 = 2687411) B2687411
theorem B1791627 : Blo 1790096 1791627 := bstep (se 1 (by rfl) ⟨1343720, by rfl⟩ : syracuseStep 1791627 = 2687441) B2687441
theorem B1791639 : Blo 1790096 1791639 := bstep (se 1 (by rfl) ⟨1343729, by rfl⟩ : syracuseStep 1791639 = 2687459) B2687459
theorem B4535959 : Blo 1790096 4535959 := bstep (se 1 (by rfl) ⟨3401969, by rfl⟩ : syracuseStep 4535959 = 6803939) B6803939
theorem B4028057 : Blo 1790096 4028057 := bstep (se 2 (by rfl) ⟨1510521, by rfl⟩ : syracuseStep 4028057 = 3021043) B3021043
theorem B1791659 : Blo 1790096 1791659 := bstep (se 1 (by rfl) ⟨1343744, by rfl⟩ : syracuseStep 1791659 = 2687489) B2687489
theorem B1791671 : Blo 1790096 1791671 := bstep (se 1 (by rfl) ⟨1343753, by rfl⟩ : syracuseStep 1791671 = 2687507) B2687507
theorem B1791691 : Blo 1790096 1791691 := bstep (se 1 (by rfl) ⟨1343768, by rfl⟩ : syracuseStep 1791691 = 2687537) B2687537
theorem B1791703 : Blo 1790096 1791703 := bstep (se 1 (by rfl) ⟨1343777, by rfl⟩ : syracuseStep 1791703 = 2687555) B2687555
theorem B3823321 : Blo 1790096 3823321 := bstep (se 2 (by rfl) ⟨1433745, by rfl⟩ : syracuseStep 3823321 = 2867491) B2867491
theorem B1791723 : Blo 1790096 1791723 := bstep (se 1 (by rfl) ⟨1343792, by rfl⟩ : syracuseStep 1791723 = 2687585) B2687585
theorem B4028147 : Blo 1790096 4028147 := bstep (se 1 (by rfl) ⟨3021110, by rfl⟩ : syracuseStep 4028147 = 6042221) B6042221
theorem B1791735 : Blo 1790096 1791735 := bstep (se 1 (by rfl) ⟨1343801, by rfl⟩ : syracuseStep 1791735 = 2687603) B2687603
theorem B17209093 : Blo 1790096 17209093 := bstep (se 4 (by rfl) ⟨1613352, by rfl⟩ : syracuseStep 17209093 = 3226705) B3226705
theorem B21796613 : Blo 1790096 21796613 := bstep (se 4 (by rfl) ⟨2043432, by rfl⟩ : syracuseStep 21796613 = 4086865) B4086865
theorem B1791755 : Blo 1790096 1791755 := bstep (se 1 (by rfl) ⟨1343816, by rfl⟩ : syracuseStep 1791755 = 2687633) B2687633
theorem B4028183 : Blo 1790096 4028183 := bstep (se 1 (by rfl) ⟨3021137, by rfl⟩ : syracuseStep 4028183 = 6042275) B6042275
theorem B1791767 : Blo 1790096 1791767 := bstep (se 1 (by rfl) ⟨1343825, by rfl⟩ : syracuseStep 1791767 = 2687651) B2687651
theorem B1791787 : Blo 1790096 1791787 := bstep (se 1 (by rfl) ⟨1343840, by rfl⟩ : syracuseStep 1791787 = 2687681) B2687681
theorem B1791799 : Blo 1790096 1791799 := bstep (se 1 (by rfl) ⟨1343849, by rfl⟩ : syracuseStep 1791799 = 2687699) B2687699
theorem B1791819 : Blo 1790096 1791819 := bstep (se 1 (by rfl) ⟨1343864, by rfl⟩ : syracuseStep 1791819 = 2687729) B2687729
theorem B2266967 : Blo 1790096 2266967 := bstep (se 1 (by rfl) ⟨1700225, by rfl⟩ : syracuseStep 2266967 = 3400451) B3400451
theorem B1791831 : Blo 1790096 1791831 := bstep (se 1 (by rfl) ⟨1343873, by rfl⟩ : syracuseStep 1791831 = 2687747) B2687747
theorem B38737763 : Blo 1790096 38737763 := bstep (se 1 (by rfl) ⟨29053322, by rfl⟩ : syracuseStep 38737763 = 58106645) B58106645
theorem B1791851 : Blo 1790096 1791851 := bstep (se 1 (by rfl) ⟨1343888, by rfl⟩ : syracuseStep 1791851 = 2687777) B2687777
theorem B1791863 : Blo 1790096 1791863 := bstep (se 1 (by rfl) ⟨1343897, by rfl⟩ : syracuseStep 1791863 = 2687795) B2687795
theorem B1791883 : Blo 1790096 1791883 := bstep (se 1 (by rfl) ⟨1343912, by rfl⟩ : syracuseStep 1791883 = 2687825) B2687825
theorem B10196887 : Blo 1790096 10196887 := bstep (se 1 (by rfl) ⟨7647665, by rfl⟩ : syracuseStep 10196887 = 15295331) B15295331
theorem B1791895 : Blo 1790096 1791895 := bstep (se 1 (by rfl) ⟨1343921, by rfl⟩ : syracuseStep 1791895 = 2687843) B2687843
theorem B1791915 : Blo 1790096 1791915 := bstep (se 1 (by rfl) ⟨1343936, by rfl⟩ : syracuseStep 1791915 = 2687873) B2687873
theorem B6043571 : Blo 1790096 6043571 := bstep (se 1 (by rfl) ⟨4532678, by rfl⟩ : syracuseStep 6043571 = 9065357) B9065357
theorem B1791927 : Blo 1790096 1791927 := bstep (se 1 (by rfl) ⟨1343945, by rfl⟩ : syracuseStep 1791927 = 2687891) B2687891
theorem B4028363 : Blo 1790096 4028363 := bstep (se 1 (by rfl) ⟨3021272, by rfl⟩ : syracuseStep 4028363 = 6042545) B6042545
theorem B1791947 : Blo 1790096 1791947 := bstep (se 1 (by rfl) ⟨1343960, by rfl⟩ : syracuseStep 1791947 = 2687921) B2687921
theorem B1791959 : Blo 1790096 1791959 := bstep (se 1 (by rfl) ⟨1343969, by rfl⟩ : syracuseStep 1791959 = 2687939) B2687939
theorem B1791979 : Blo 1790096 1791979 := bstep (se 1 (by rfl) ⟨1343984, by rfl⟩ : syracuseStep 1791979 = 2687969) B2687969
theorem B1791991 : Blo 1790096 1791991 := bstep (se 1 (by rfl) ⟨1343993, by rfl⟩ : syracuseStep 1791991 = 2687987) B2687987
theorem B4028417 : Blo 1790096 4028417 := bstep (se 2 (by rfl) ⟨1510656, by rfl⟩ : syracuseStep 4028417 = 3021313) B3021313
theorem B1792011 : Blo 1790096 1792011 := bstep (se 1 (by rfl) ⟨1344008, by rfl⟩ : syracuseStep 1792011 = 2688017) B2688017
theorem B1792023 : Blo 1790096 1792023 := bstep (se 1 (by rfl) ⟨1344017, by rfl⟩ : syracuseStep 1792023 = 2688035) B2688035
theorem B1792043 : Blo 1790096 1792043 := bstep (se 1 (by rfl) ⟨1344032, by rfl⟩ : syracuseStep 1792043 = 2688065) B2688065
theorem B5740595 : Blo 1790096 5740595 := bstep (se 1 (by rfl) ⟨4305446, by rfl⟩ : syracuseStep 5740595 = 8610893) B8610893
theorem B1792055 : Blo 1790096 1792055 := bstep (se 1 (by rfl) ⟨1344041, by rfl⟩ : syracuseStep 1792055 = 2688083) B2688083
theorem B5101633 : Blo 1790096 5101633 := bstep (se 2 (by rfl) ⟨1913112, by rfl⟩ : syracuseStep 5101633 = 3826225) B3826225
theorem B1792075 : Blo 1790096 1792075 := bstep (se 1 (by rfl) ⟨1344056, by rfl⟩ : syracuseStep 1792075 = 2688113) B2688113
theorem B1792087 : Blo 1790096 1792087 := bstep (se 1 (by rfl) ⟨1344065, by rfl⟩ : syracuseStep 1792087 = 2688131) B2688131
theorem B6043841 : Blo 1790096 6043841 := bstep (se 2 (by rfl) ⟨2266440, by rfl⟩ : syracuseStep 6043841 = 4532881) B4532881
theorem B4028633 : Blo 1790096 4028633 := bstep (se 2 (by rfl) ⟨1510737, by rfl⟩ : syracuseStep 4028633 = 3021475) B3021475
theorem B6797591 : Blo 1790096 6797591 := bstep (se 1 (by rfl) ⟨5098193, by rfl⟩ : syracuseStep 6797591 = 10196387) B10196387
theorem B2685209 : Blo 1790096 2685209 := bstep (se 2 (by rfl) ⟨1006953, by rfl⟩ : syracuseStep 2685209 = 2013907) B2013907
theorem B4028723 : Blo 1790096 4028723 := bstep (se 1 (by rfl) ⟨3021542, by rfl⟩ : syracuseStep 4028723 = 6043085) B6043085
theorem B5740865 : Blo 1790096 5740865 := bstep (se 2 (by rfl) ⟨2152824, by rfl⟩ : syracuseStep 5740865 = 4305649) B4305649
theorem B3021131 : Blo 1790096 3021131 := bstep (se 1 (by rfl) ⟨2265848, by rfl⟩ : syracuseStep 3021131 = 4531697) B4531697
theorem B4028759 : Blo 1790096 4028759 := bstep (se 1 (by rfl) ⟨3021569, by rfl⟩ : syracuseStep 4028759 = 6043139) B6043139
theorem B2685323 : Blo 1790096 2685323 := bstep (se 1 (by rfl) ⟨2013992, by rfl⟩ : syracuseStep 2685323 = 4027985) B4027985
theorem B2685335 : Blo 1790096 2685335 := bstep (se 1 (by rfl) ⟨2014001, by rfl⟩ : syracuseStep 2685335 = 4028003) B4028003
theorem B3021259 : Blo 1790096 3021259 := bstep (se 1 (by rfl) ⟨2265944, by rfl⟩ : syracuseStep 3021259 = 4531889) B4531889
theorem B2685401 : Blo 1790096 2685401 := bstep (se 2 (by rfl) ⟨1007025, by rfl⟩ : syracuseStep 2685401 = 2014051) B2014051
theorem B6797789 : Blo 1790096 6797789 := bstep (se 3 (by rfl) ⟨1274585, by rfl⟩ : syracuseStep 6797789 = 2549171) B2549171
theorem B4028939 : Blo 1790096 4028939 := bstep (se 1 (by rfl) ⟨3021704, by rfl⟩ : syracuseStep 4028939 = 6043409) B6043409
theorem B2267671 : Blo 1790096 2267671 := bstep (se 1 (by rfl) ⟨1700753, by rfl⟩ : syracuseStep 2267671 = 3401507) B3401507
theorem B4028993 : Blo 1790096 4028993 := bstep (se 2 (by rfl) ⟨1510872, by rfl⟩ : syracuseStep 4028993 = 3021745) B3021745
theorem B14727745 : Blo 1790096 14727745 := bstep (se 2 (by rfl) ⟨5522904, by rfl⟩ : syracuseStep 14727745 = 11045809) B11045809
theorem B2685515 : Blo 1790096 2685515 := bstep (se 1 (by rfl) ⟨2014136, by rfl⟩ : syracuseStep 2685515 = 4028273) B4028273
theorem B2685527 : Blo 1790096 2685527 := bstep (se 1 (by rfl) ⟨2014145, by rfl⟩ : syracuseStep 2685527 = 4028291) B4028291
theorem B3021401 : Blo 1790096 3021401 := bstep (se 2 (by rfl) ⟨1133025, by rfl⟩ : syracuseStep 3021401 = 2266051) B2266051
theorem B9067139 : Blo 1790096 9067139 := bstep (se 1 (by rfl) ⟨6800354, by rfl⟩ : syracuseStep 9067139 = 13600709) B13600709
theorem B2685593 : Blo 1790096 2685593 := bstep (se 2 (by rfl) ⟨1007097, by rfl⟩ : syracuseStep 2685593 = 2014195) B2014195
theorem B3021529 : Blo 1790096 3021529 := bstep (se 2 (by rfl) ⟨1133073, by rfl⟩ : syracuseStep 3021529 = 2266147) B2266147
theorem B6044381 : Blo 1790096 6044381 := bstep (se 3 (by rfl) ⟨1133321, by rfl⟩ : syracuseStep 6044381 = 2266643) B2266643
theorem B2013943 : Blo 1790096 2013943 := bstep (se 1 (by rfl) ⟨1510457, by rfl⟩ : syracuseStep 2013943 = 3020915) B3020915
theorem B2685707 : Blo 1790096 2685707 := bstep (se 1 (by rfl) ⟨2014280, by rfl⟩ : syracuseStep 2685707 = 4028561) B4028561
theorem B2685719 : Blo 1790096 2685719 := bstep (se 1 (by rfl) ⟨2014289, by rfl⟩ : syracuseStep 2685719 = 4028579) B4028579
theorem B4029209 : Blo 1790096 4029209 := bstep (se 2 (by rfl) ⟨1510953, by rfl⟩ : syracuseStep 4029209 = 3021907) B3021907
theorem B2685785 : Blo 1790096 2685785 := bstep (se 2 (by rfl) ⟨1007169, by rfl⟩ : syracuseStep 2685785 = 2014339) B2014339
theorem B4029299 : Blo 1790096 4029299 := bstep (se 1 (by rfl) ⟨3021974, by rfl⟩ : syracuseStep 4029299 = 6043949) B6043949
theorem B4029335 : Blo 1790096 4029335 := bstep (se 1 (by rfl) ⟨3022001, by rfl⟩ : syracuseStep 4029335 = 6044003) B6044003
theorem B3062681 : Blo 1790096 3062681 := bstep (se 2 (by rfl) ⟨1148505, by rfl⟩ : syracuseStep 3062681 = 2297011) B2297011
theorem B2014123 : Blo 1790096 2014123 := bstep (se 1 (by rfl) ⟨1510592, by rfl⟩ : syracuseStep 2014123 = 3021185) B3021185
theorem B2685899 : Blo 1790096 2685899 := bstep (se 1 (by rfl) ⟨2014424, by rfl⟩ : syracuseStep 2685899 = 4028849) B4028849
theorem B2685911 : Blo 1790096 2685911 := bstep (se 1 (by rfl) ⟨2014433, by rfl⟩ : syracuseStep 2685911 = 4028867) B4028867
theorem B2014231 : Blo 1790096 2014231 := bstep (se 1 (by rfl) ⟨1510673, by rfl⟩ : syracuseStep 2014231 = 3021347) B3021347
theorem B4660247 : Blo 1790096 4660247 := bstep (se 1 (by rfl) ⟨3495185, by rfl⟩ : syracuseStep 4660247 = 6990371) B6990371
theorem B2685977 : Blo 1790096 2685977 := bstep (se 2 (by rfl) ⟨1007241, by rfl⟩ : syracuseStep 2685977 = 2014483) B2014483
theorem B4029515 : Blo 1790096 4029515 := bstep (se 1 (by rfl) ⟨3022136, by rfl⟩ : syracuseStep 4029515 = 6044273) B6044273
theorem B5815385 : Blo 1790096 5815385 := bstep (se 2 (by rfl) ⟨2180769, by rfl⟩ : syracuseStep 5815385 = 4361539) B4361539
theorem B4029569 : Blo 1790096 4029569 := bstep (se 2 (by rfl) ⟨1511088, by rfl⟩ : syracuseStep 4029569 = 3022177) B3022177
theorem B3226763 : Blo 1790096 3226763 := bstep (se 1 (by rfl) ⟨2420072, by rfl⟩ : syracuseStep 3226763 = 4840145) B4840145
theorem B2686091 : Blo 1790096 2686091 := bstep (se 1 (by rfl) ⟨2014568, by rfl⟩ : syracuseStep 2686091 = 4029137) B4029137
theorem B2686103 : Blo 1790096 2686103 := bstep (se 1 (by rfl) ⟨2014577, by rfl⟩ : syracuseStep 2686103 = 4029155) B4029155
theorem B2014411 : Blo 1790096 2014411 := bstep (se 1 (by rfl) ⟨1510808, by rfl⟩ : syracuseStep 2014411 = 3021617) B3021617
theorem B2686169 : Blo 1790096 2686169 := bstep (se 2 (by rfl) ⟨1007313, by rfl⟩ : syracuseStep 2686169 = 2014627) B2014627
theorem B7650521 : Blo 1790096 7650521 := bstep (se 2 (by rfl) ⟨2868945, by rfl⟩ : syracuseStep 7650521 = 5737891) B5737891
theorem B3022103 : Blo 1790096 3022103 := bstep (se 1 (by rfl) ⟨2266577, by rfl⟩ : syracuseStep 3022103 = 4533155) B4533155
theorem B7650605 : Blo 1790096 7650605 := bstep (se 3 (by rfl) ⟨1434488, by rfl⟩ : syracuseStep 7650605 = 2868977) B2868977
theorem B2014519 : Blo 1790096 2014519 := bstep (se 1 (by rfl) ⟨1510889, by rfl⟩ : syracuseStep 2014519 = 3021779) B3021779
theorem B10894657 : Blo 1790096 10894657 := bstep (se 2 (by rfl) ⟨4085496, by rfl⟩ : syracuseStep 10894657 = 8170993) B8170993
theorem B2686283 : Blo 1790096 2686283 := bstep (se 1 (by rfl) ⟨2014712, by rfl⟩ : syracuseStep 2686283 = 4029425) B4029425
theorem B2686295 : Blo 1790096 2686295 := bstep (se 1 (by rfl) ⟨2014721, by rfl⟩ : syracuseStep 2686295 = 4029443) B4029443
theorem B4029785 : Blo 1790096 4029785 := bstep (se 2 (by rfl) ⟨1511169, by rfl⟩ : syracuseStep 4029785 = 3022339) B3022339
theorem B4595095 : Blo 1790096 4595095 := bstep (se 1 (by rfl) ⟨3446321, by rfl⟩ : syracuseStep 4595095 = 6892643) B6892643
theorem B3022231 : Blo 1790096 3022231 := bstep (se 1 (by rfl) ⟨2266673, by rfl⟩ : syracuseStep 3022231 = 4533347) B4533347
theorem B2686361 : Blo 1790096 2686361 := bstep (se 2 (by rfl) ⟨1007385, by rfl⟩ : syracuseStep 2686361 = 2014771) B2014771
theorem B4029875 : Blo 1790096 4029875 := bstep (se 1 (by rfl) ⟨3022406, by rfl⟩ : syracuseStep 4029875 = 6044813) B6044813
theorem B4029911 : Blo 1790096 4029911 := bstep (se 1 (by rfl) ⟨3022433, by rfl⟩ : syracuseStep 4029911 = 6044867) B6044867
theorem B2014699 : Blo 1790096 2014699 := bstep (se 1 (by rfl) ⟨1511024, by rfl⟩ : syracuseStep 2014699 = 3022049) B3022049
theorem B7265795 : Blo 1790096 7265795 := bstep (se 1 (by rfl) ⟨5449346, by rfl⟩ : syracuseStep 7265795 = 10898693) B10898693
theorem B2686475 : Blo 1790096 2686475 := bstep (se 1 (by rfl) ⟨2014856, by rfl⟩ : syracuseStep 2686475 = 4029713) B4029713
theorem B2686487 : Blo 1790096 2686487 := bstep (se 1 (by rfl) ⟨2014865, by rfl⟩ : syracuseStep 2686487 = 4029731) B4029731
theorem B2014807 : Blo 1790096 2014807 := bstep (se 1 (by rfl) ⟨1511105, by rfl⟩ : syracuseStep 2014807 = 3022211) B3022211
theorem B2686553 : Blo 1790096 2686553 := bstep (se 2 (by rfl) ⟨1007457, by rfl⟩ : syracuseStep 2686553 = 2014915) B2014915
theorem B4030091 : Blo 1790096 4030091 := bstep (se 1 (by rfl) ⟨3022568, by rfl⟩ : syracuseStep 4030091 = 6045137) B6045137
theorem B4030145 : Blo 1790096 4030145 := bstep (se 2 (by rfl) ⟨1511304, by rfl⟩ : syracuseStep 4030145 = 3022609) B3022609
theorem B2686667 : Blo 1790096 2686667 := bstep (se 1 (by rfl) ⟨2015000, by rfl⟩ : syracuseStep 2686667 = 4030001) B4030001
theorem B2686679 : Blo 1790096 2686679 := bstep (se 1 (by rfl) ⟨2015009, by rfl⟩ : syracuseStep 2686679 = 4030019) B4030019
theorem B43572977 : Blo 1790096 43572977 := bstep (se 2 (by rfl) ⟨16339866, by rfl⟩ : syracuseStep 43572977 = 32679733) B32679733
theorem B2014987 : Blo 1790096 2014987 := bstep (se 1 (by rfl) ⟨1511240, by rfl⟩ : syracuseStep 2014987 = 3022481) B3022481
theorem B2686745 : Blo 1790096 2686745 := bstep (se 2 (by rfl) ⟨1007529, by rfl⟩ : syracuseStep 2686745 = 2015059) B2015059
theorem B3825473 : Blo 1790096 3825473 := bstep (se 2 (by rfl) ⟨1434552, by rfl⟩ : syracuseStep 3825473 = 2869105) B2869105
theorem B6045515 : Blo 1790096 6045515 := bstep (se 1 (by rfl) ⟨4534136, by rfl⟩ : syracuseStep 6045515 = 9068273) B9068273
theorem B2907991 : Blo 1790096 2907991 := bstep (se 1 (by rfl) ⟨2180993, by rfl⟩ : syracuseStep 2907991 = 4361987) B4361987
theorem B11476829 : Blo 1790096 11476829 := bstep (se 3 (by rfl) ⟨2151905, by rfl⟩ : syracuseStep 11476829 = 4303811) B4303811
theorem B2015095 : Blo 1790096 2015095 := bstep (se 1 (by rfl) ⟨1511321, by rfl⟩ : syracuseStep 2015095 = 3022643) B3022643
theorem B3399563 : Blo 1790096 3399563 := bstep (se 1 (by rfl) ⟨2549672, by rfl⟩ : syracuseStep 3399563 = 5099345) B5099345
theorem B2686859 : Blo 1790096 2686859 := bstep (se 1 (by rfl) ⟨2015144, by rfl⟩ : syracuseStep 2686859 = 4030289) B4030289
theorem B3825559 : Blo 1790096 3825559 := bstep (se 1 (by rfl) ⟨2869169, by rfl⟩ : syracuseStep 3825559 = 5738339) B5738339
theorem B2686871 : Blo 1790096 2686871 := bstep (se 1 (by rfl) ⟨2015153, by rfl⟩ : syracuseStep 2686871 = 4030307) B4030307
theorem B4030361 : Blo 1790096 4030361 := bstep (se 2 (by rfl) ⟨1511385, by rfl⟩ : syracuseStep 4030361 = 3022771) B3022771
theorem B3227585 : Blo 1790096 3227585 := bstep (se 2 (by rfl) ⟨1210344, by rfl⟩ : syracuseStep 3227585 = 2420689) B2420689
theorem B2686937 : Blo 1790096 2686937 := bstep (se 2 (by rfl) ⟨1007601, by rfl⟩ : syracuseStep 2686937 = 2015203) B2015203
theorem B4030451 : Blo 1790096 4030451 := bstep (se 1 (by rfl) ⟨3022838, by rfl⟩ : syracuseStep 4030451 = 6045677) B6045677
theorem B2015239 : Blo 1790096 2015239 := bstep (se 1 (by rfl) ⟨1511429, by rfl⟩ : syracuseStep 2015239 = 3022859) B3022859
theorem B2686991 : Blo 1790096 2686991 := bstep (se 1 (by rfl) ⟨2015243, by rfl⟩ : syracuseStep 2686991 = 4030487) B4030487
theorem B5447695 : Blo 1790096 5447695 := bstep (se 1 (by rfl) ⟨4085771, by rfl⟩ : syracuseStep 5447695 = 8171543) B8171543
theorem B10887211 : Blo 1790096 10887211 := bstep (se 1 (by rfl) ⟨8165408, by rfl⟩ : syracuseStep 10887211 = 16330817) B16330817
theorem B2687033 : Blo 1790096 2687033 := bstep (se 2 (by rfl) ⟨1007637, by rfl⟩ : syracuseStep 2687033 = 2015275) B2015275
theorem B4030523 : Blo 1790096 4030523 := bstep (se 1 (by rfl) ⟨3022892, by rfl⟩ : syracuseStep 4030523 = 6045785) B6045785
theorem B3022967 : Blo 1790096 3022967 := bstep (se 1 (by rfl) ⟨2267225, by rfl⟩ : syracuseStep 3022967 = 4534451) B4534451
theorem B2687111 : Blo 1790096 2687111 := bstep (se 1 (by rfl) ⟨2015333, by rfl⟩ : syracuseStep 2687111 = 4030667) B4030667
theorem B2687147 : Blo 1790096 2687147 := bstep (se 1 (by rfl) ⟨2015360, by rfl⟩ : syracuseStep 2687147 = 4030721) B4030721
theorem B4030649 : Blo 1790096 4030649 := bstep (se 2 (by rfl) ⟨1511493, by rfl⟩ : syracuseStep 4030649 = 3022987) B3022987
theorem B2015419 : Blo 1790096 2015419 := bstep (se 1 (by rfl) ⟨1511564, by rfl⟩ : syracuseStep 2015419 = 3023129) B3023129
theorem B7651529 : Blo 1790096 7651529 := bstep (se 2 (by rfl) ⟨2869323, by rfl⟩ : syracuseStep 7651529 = 5738647) B5738647
theorem B2687177 : Blo 1790096 2687177 := bstep (se 2 (by rfl) ⟨1007691, by rfl⟩ : syracuseStep 2687177 = 2015383) B2015383
theorem B3399995 : Blo 1790096 3399995 := bstep (se 1 (by rfl) ⟨2549996, by rfl⟩ : syracuseStep 3399995 = 5099993) B5099993
theorem B2687291 : Blo 1790096 2687291 := bstep (se 1 (by rfl) ⟨2015468, by rfl⟩ : syracuseStep 2687291 = 4030937) B4030937
theorem B2687351 : Blo 1790096 2687351 := bstep (se 1 (by rfl) ⟨2015513, by rfl⟩ : syracuseStep 2687351 = 4031027) B4031027
theorem B3826055 : Blo 1790096 3826055 := bstep (se 1 (by rfl) ⟨2869541, by rfl⟩ : syracuseStep 3826055 = 5739083) B5739083
theorem B2687375 : Blo 1790096 2687375 := bstep (se 1 (by rfl) ⟨2015531, by rfl⟩ : syracuseStep 2687375 = 4031063) B4031063
theorem B2687417 : Blo 1790096 2687417 := bstep (se 2 (by rfl) ⟨1007781, by rfl⟩ : syracuseStep 2687417 = 2015563) B2015563
theorem B2687495 : Blo 1790096 2687495 := bstep (se 1 (by rfl) ⟨2015621, by rfl⟩ : syracuseStep 2687495 = 4031243) B4031243
theorem B6455819 : Blo 1790096 6455819 := bstep (se 1 (by rfl) ⟨4841864, by rfl⟩ : syracuseStep 6455819 = 9683729) B9683729
theorem B4030991 : Blo 1790096 4030991 := bstep (se 1 (by rfl) ⟨3023243, by rfl⟩ : syracuseStep 4030991 = 6046487) B6046487
theorem B4031009 : Blo 1790096 4031009 := bstep (se 2 (by rfl) ⟨1511628, by rfl⟩ : syracuseStep 4031009 = 3023257) B3023257
theorem B2687531 : Blo 1790096 2687531 := bstep (se 1 (by rfl) ⟨2015648, by rfl⟩ : syracuseStep 2687531 = 4031297) B4031297
theorem B3023419 : Blo 1790096 3023419 := bstep (se 1 (by rfl) ⟨2267564, by rfl⟩ : syracuseStep 3023419 = 4535129) B4535129
theorem B2687561 : Blo 1790096 2687561 := bstep (se 2 (by rfl) ⟨1007835, by rfl⟩ : syracuseStep 2687561 = 2015671) B2015671
theorem B2015887 : Blo 1790096 2015887 := bstep (se 1 (by rfl) ⟨1511915, by rfl⟩ : syracuseStep 2015887 = 3023831) B3023831
theorem B2687675 : Blo 1790096 2687675 := bstep (se 1 (by rfl) ⟨2015756, by rfl⟩ : syracuseStep 2687675 = 4031513) B4031513
theorem B3023561 : Blo 1790096 3023561 := bstep (se 2 (by rfl) ⟨1133835, by rfl⟩ : syracuseStep 3023561 = 2267671) B2267671
theorem B2687735 : Blo 1790096 2687735 := bstep (se 1 (by rfl) ⟨2015801, by rfl⟩ : syracuseStep 2687735 = 4031603) B4031603
theorem B19636993 : Blo 1790096 19636993 := bstep (se 2 (by rfl) ⟨7363872, by rfl⟩ : syracuseStep 19636993 = 14727745) B14727745
theorem B2687759 : Blo 1790096 2687759 := bstep (se 1 (by rfl) ⟨2015819, by rfl⟩ : syracuseStep 2687759 = 4031639) B4031639
theorem B3400481 : Blo 1790096 3400481 := bstep (se 2 (by rfl) ⟨1275180, by rfl⟩ : syracuseStep 3400481 = 2550361) B2550361
theorem B2687801 : Blo 1790096 2687801 := bstep (se 2 (by rfl) ⟨1007925, by rfl⟩ : syracuseStep 2687801 = 2015851) B2015851
theorem B6456179 : Blo 1790096 6456179 := bstep (se 1 (by rfl) ⟨4842134, by rfl⟩ : syracuseStep 6456179 = 9684269) B9684269
theorem B4031351 : Blo 1790096 4031351 := bstep (se 1 (by rfl) ⟨3023513, by rfl⟩ : syracuseStep 4031351 = 6047027) B6047027
theorem B2687879 : Blo 1790096 2687879 := bstep (se 1 (by rfl) ⟨2015909, by rfl⟩ : syracuseStep 2687879 = 4031819) B4031819
theorem B2687915 : Blo 1790096 2687915 := bstep (se 1 (by rfl) ⟨2015936, by rfl⟩ : syracuseStep 2687915 = 4031873) B4031873
theorem B3400633 : Blo 1790096 3400633 := bstep (se 2 (by rfl) ⟨1275237, by rfl⟩ : syracuseStep 3400633 = 2550475) B2550475
theorem B6046649 : Blo 1790096 6046649 := bstep (se 2 (by rfl) ⟨2267493, by rfl⟩ : syracuseStep 6046649 = 4534987) B4534987
theorem B2687945 : Blo 1790096 2687945 := bstep (se 2 (by rfl) ⟨1007979, by rfl⟩ : syracuseStep 2687945 = 2015959) B2015959
theorem B4531211 : Blo 1790096 4531211 := bstep (se 1 (by rfl) ⟨3398408, by rfl⟩ : syracuseStep 4531211 = 6796817) B6796817
theorem B4031531 : Blo 1790096 4031531 := bstep (se 1 (by rfl) ⟨3023648, by rfl⟩ : syracuseStep 4031531 = 6047297) B6047297
theorem B2688059 : Blo 1790096 2688059 := bstep (se 1 (by rfl) ⟨2016044, by rfl⟩ : syracuseStep 2688059 = 4032089) B4032089
theorem B2688119 : Blo 1790096 2688119 := bstep (se 1 (by rfl) ⟨2016089, by rfl⟩ : syracuseStep 2688119 = 4032179) B4032179
theorem B2688143 : Blo 1790096 2688143 := bstep (se 1 (by rfl) ⟨2016107, by rfl⟩ : syracuseStep 2688143 = 4032215) B4032215
theorem B6128929 : Blo 1790096 6128929 := bstep (se 2 (by rfl) ⟨2298348, by rfl⟩ : syracuseStep 6128929 = 4596697) B4596697
theorem B19375453 : Blo 1790096 19375453 := bstep (se 3 (by rfl) ⟨3632897, by rfl⟩ : syracuseStep 19375453 = 7265795) B7265795
theorem B3827063 : Blo 1790096 3827063 := bstep (se 1 (by rfl) ⟨2870297, by rfl⟩ : syracuseStep 3827063 = 5740595) B5740595
theorem B4031891 : Blo 1790096 4031891 := bstep (se 1 (by rfl) ⟨3023918, by rfl⟩ : syracuseStep 4031891 = 6047837) B6047837
theorem B4031945 : Blo 1790096 4031945 := bstep (se 2 (by rfl) ⟨1511979, by rfl⟩ : syracuseStep 4031945 = 3023959) B3023959
theorem B6047243 : Blo 1790096 6047243 := bstep (se 1 (by rfl) ⟨4535432, by rfl⟩ : syracuseStep 6047243 = 9070865) B9070865
theorem B4531727 : Blo 1790096 4531727 := bstep (se 1 (by rfl) ⟨3398795, by rfl⟩ : syracuseStep 4531727 = 6797591) B6797591
theorem B3827243 : Blo 1790096 3827243 := bstep (se 1 (by rfl) ⟨2870432, by rfl⟩ : syracuseStep 3827243 = 5740865) B5740865
theorem B6047351 : Blo 1790096 6047351 := bstep (se 1 (by rfl) ⟨4535513, by rfl⟩ : syracuseStep 6047351 = 9071027) B9071027
theorem B4531859 : Blo 1790096 4531859 := bstep (se 1 (by rfl) ⟨3398894, by rfl⟩ : syracuseStep 4531859 = 6797789) B6797789
theorem B14526209 : Blo 1790096 14526209 := bstep (se 2 (by rfl) ⟨5447328, by rfl⟩ : syracuseStep 14526209 = 10894657) B10894657
theorem B5736251 : Blo 1790096 5736251 := bstep (se 1 (by rfl) ⟨4302188, by rfl⟩ : syracuseStep 5736251 = 8604377) B8604377
theorem B56641355 : Blo 1790096 56641355 := bstep (se 1 (by rfl) ⟨42481016, by rfl⟩ : syracuseStep 56641355 = 84962033) B84962033
theorem B7653305 : Blo 1790096 7653305 := bstep (se 2 (by rfl) ⟨2869989, by rfl⟩ : syracuseStep 7653305 = 5739979) B5739979
theorem B2041787 : Blo 1790096 2041787 := bstep (se 1 (by rfl) ⟨1531340, by rfl⟩ : syracuseStep 2041787 = 3062681) B3062681
theorem B3106831 : Blo 1790096 3106831 := bstep (se 1 (by rfl) ⟨2330123, by rfl⟩ : syracuseStep 3106831 = 4660247) B4660247
theorem B3876923 : Blo 1790096 3876923 := bstep (se 1 (by rfl) ⟨2907692, by rfl⟩ : syracuseStep 3876923 = 5815385) B5815385
theorem B10201261 : Blo 1790096 10201261 := bstep (se 3 (by rfl) ⟨1912736, by rfl⟩ : syracuseStep 10201261 = 3825473) B3825473
theorem B6047945 : Blo 1790096 6047945 := bstep (se 2 (by rfl) ⟨2267979, by rfl⟩ : syracuseStep 6047945 = 4535959) B4535959
theorem B5097761 : Blo 1790096 5097761 := bstep (se 2 (by rfl) ⟨1911660, by rfl⟩ : syracuseStep 5097761 = 3823321) B3823321
theorem B3877321 : Blo 1790096 3877321 := bstep (se 2 (by rfl) ⟨1453995, by rfl⟩ : syracuseStep 3877321 = 2907991) B2907991
theorem B49703489 : Blo 1790096 49703489 := bstep (se 2 (by rfl) ⟨18638808, by rfl⟩ : syracuseStep 49703489 = 37277617) B37277617
theorem B4655731 : Blo 1790096 4655731 := bstep (se 1 (by rfl) ⟨3491798, by rfl⟩ : syracuseStep 4655731 = 6983597) B6983597
theorem B5098103 : Blo 1790096 5098103 := bstep (se 1 (by rfl) ⟨3823577, by rfl⟩ : syracuseStep 5098103 = 7647155) B7647155
theorem B4532993 : Blo 1790096 4532993 := bstep (se 2 (by rfl) ⟨1699872, by rfl⟩ : syracuseStep 4532993 = 3399745) B3399745
theorem B6802177 : Blo 1790096 6802177 := bstep (se 2 (by rfl) ⟨2550816, by rfl⟩ : syracuseStep 6802177 = 5101633) B5101633
theorem B11471705 : Blo 1790096 11471705 := bstep (se 2 (by rfl) ⟨4301889, by rfl⟩ : syracuseStep 11471705 = 8603779) B8603779
theorem B2722703 : Blo 1790096 2722703 := bstep (se 1 (by rfl) ⟨2042027, by rfl⟩ : syracuseStep 2722703 = 4084055) B4084055
theorem B9071513 : Blo 1790096 9071513 := bstep (se 2 (by rfl) ⟨3401817, by rfl⟩ : syracuseStep 9071513 = 6803635) B6803635
theorem B8604701 : Blo 1790096 8604701 := bstep (se 3 (by rfl) ⟨1613381, by rfl⟩ : syracuseStep 8604701 = 3226763) B3226763
theorem B4533367 : Blo 1790096 4533367 := bstep (se 1 (by rfl) ⟨3400025, by rfl⟩ : syracuseStep 4533367 = 6800051) B6800051
theorem B34434179 : Blo 1790096 34434179 := bstep (se 1 (by rfl) ⟨25825634, by rfl⟩ : syracuseStep 34434179 = 51651269) B51651269
theorem B7654637 : Blo 1790096 7654637 := bstep (se 3 (by rfl) ⟨1435244, by rfl⟩ : syracuseStep 7654637 = 2870489) B2870489
theorem B5098763 : Blo 1790096 5098763 := bstep (se 1 (by rfl) ⟨3824072, by rfl⟩ : syracuseStep 5098763 = 7648145) B7648145
theorem B8728067 : Blo 1790096 8728067 := bstep (se 1 (by rfl) ⟨6546050, by rfl⟩ : syracuseStep 8728067 = 13092101) B13092101
theorem B4533803 : Blo 1790096 4533803 := bstep (se 1 (by rfl) ⟨3400352, by rfl⟩ : syracuseStep 4533803 = 6800705) B6800705
theorem B1912583 : Blo 1790096 1912583 := bstep (se 1 (by rfl) ⟨1434437, by rfl⟩ : syracuseStep 1912583 = 2868875) B2868875
theorem B31436695 : Blo 1790096 31436695 := bstep (se 1 (by rfl) ⟨23577521, by rfl⟩ : syracuseStep 31436695 = 47155043) B47155043
theorem B25825175 : Blo 1790096 25825175 := bstep (se 1 (by rfl) ⟨19368881, by rfl⟩ : syracuseStep 25825175 = 38737763) B38737763
theorem B10891351 : Blo 1790096 10891351 := bstep (se 1 (by rfl) ⟨8168513, by rfl⟩ : syracuseStep 10891351 = 16337027) B16337027
theorem B29036717 : Blo 1790096 29036717 := bstep (se 3 (by rfl) ⟨5444384, by rfl⟩ : syracuseStep 29036717 = 10888769) B10888769
theorem B20410541 : Blo 1790096 20410541 := bstep (se 3 (by rfl) ⟨3826976, by rfl⟩ : syracuseStep 20410541 = 7653953) B7653953
theorem B1790139 : Blo 1790096 1790139 := bstep (se 1 (by rfl) ⟨1342604, by rfl⟩ : syracuseStep 1790139 = 2685209) B2685209
theorem B1790215 : Blo 1790096 1790215 := bstep (se 1 (by rfl) ⟨1342661, by rfl⟩ : syracuseStep 1790215 = 2685323) B2685323
theorem B1790223 : Blo 1790096 1790223 := bstep (se 1 (by rfl) ⟨1342667, by rfl⟩ : syracuseStep 1790223 = 2685335) B2685335
theorem B1790267 : Blo 1790096 1790267 := bstep (se 1 (by rfl) ⟨1342700, by rfl⟩ : syracuseStep 1790267 = 2685401) B2685401
theorem B4534643 : Blo 1790096 4534643 := bstep (se 1 (by rfl) ⟨3400982, by rfl⟩ : syracuseStep 4534643 = 6801965) B6801965
theorem B1790343 : Blo 1790096 1790343 := bstep (se 1 (by rfl) ⟨1342757, by rfl⟩ : syracuseStep 1790343 = 2685515) B2685515
theorem B11039111 : Blo 1790096 11039111 := bstep (se 1 (by rfl) ⟨8279333, by rfl⟩ : syracuseStep 11039111 = 16558667) B16558667
theorem B4534663 : Blo 1790096 4534663 := bstep (se 1 (by rfl) ⟨3400997, by rfl⟩ : syracuseStep 4534663 = 6801995) B6801995
theorem B1790351 : Blo 1790096 1790351 := bstep (se 1 (by rfl) ⟨1342763, by rfl⟩ : syracuseStep 1790351 = 2685527) B2685527
theorem B1790395 : Blo 1790096 1790395 := bstep (se 1 (by rfl) ⟨1342796, by rfl⟩ : syracuseStep 1790395 = 2685593) B2685593
theorem B1790471 : Blo 1790096 1790471 := bstep (se 1 (by rfl) ⟨1342853, by rfl⟩ : syracuseStep 1790471 = 2685707) B2685707
theorem B1790479 : Blo 1790096 1790479 := bstep (se 1 (by rfl) ⟨1342859, by rfl⟩ : syracuseStep 1790479 = 2685719) B2685719
theorem B10203677 : Blo 1790096 10203677 := bstep (se 3 (by rfl) ⟨1913189, by rfl⟩ : syracuseStep 10203677 = 3826379) B3826379
theorem B1790523 : Blo 1790096 1790523 := bstep (se 1 (by rfl) ⟨1342892, by rfl⟩ : syracuseStep 1790523 = 2685785) B2685785
theorem B1790599 : Blo 1790096 1790599 := bstep (se 1 (by rfl) ⟨1342949, by rfl⟩ : syracuseStep 1790599 = 2685899) B2685899
theorem B1790607 : Blo 1790096 1790607 := bstep (se 1 (by rfl) ⟨1342955, by rfl⟩ : syracuseStep 1790607 = 2685911) B2685911
theorem B4534937 : Blo 1790096 4534937 := bstep (se 2 (by rfl) ⟨1700601, by rfl⟩ : syracuseStep 4534937 = 3401203) B3401203
theorem B1790651 : Blo 1790096 1790651 := bstep (se 1 (by rfl) ⟨1342988, by rfl⟩ : syracuseStep 1790651 = 2685977) B2685977
theorem B6451913 : Blo 1790096 6451913 := bstep (se 2 (by rfl) ⟨2419467, by rfl⟩ : syracuseStep 6451913 = 4838935) B4838935
theorem B8172269 : Blo 1790096 8172269 := bstep (se 3 (by rfl) ⟨1532300, by rfl⟩ : syracuseStep 8172269 = 3064601) B3064601
theorem B6451969 : Blo 1790096 6451969 := bstep (se 2 (by rfl) ⟨2419488, by rfl⟩ : syracuseStep 6451969 = 4838977) B4838977
theorem B1790727 : Blo 1790096 1790727 := bstep (se 1 (by rfl) ⟨1343045, by rfl⟩ : syracuseStep 1790727 = 2686091) B2686091
theorem B6042383 : Blo 1790096 6042383 := bstep (se 1 (by rfl) ⟨4531787, by rfl⟩ : syracuseStep 6042383 = 9063575) B9063575
theorem B1790735 : Blo 1790096 1790735 := bstep (se 1 (by rfl) ⟨1343051, by rfl⟩ : syracuseStep 1790735 = 2686103) B2686103
theorem B24507173 : Blo 1790096 24507173 := bstep (se 4 (by rfl) ⟨2297547, by rfl⟩ : syracuseStep 24507173 = 4595095) B4595095
theorem B6452027 : Blo 1790096 6452027 := bstep (se 1 (by rfl) ⟨4839020, by rfl⟩ : syracuseStep 6452027 = 9678041) B9678041
theorem B1790779 : Blo 1790096 1790779 := bstep (se 1 (by rfl) ⟨1343084, by rfl⟩ : syracuseStep 1790779 = 2686169) B2686169
theorem B5100347 : Blo 1790096 5100347 := bstep (se 1 (by rfl) ⟨3825260, by rfl⟩ : syracuseStep 5100347 = 7650521) B7650521
theorem B4535099 : Blo 1790096 4535099 := bstep (se 1 (by rfl) ⟨3401324, by rfl⟩ : syracuseStep 4535099 = 6802649) B6802649
theorem B5100403 : Blo 1790096 5100403 := bstep (se 1 (by rfl) ⟨3825302, by rfl⟩ : syracuseStep 5100403 = 7650605) B7650605
theorem B1790855 : Blo 1790096 1790855 := bstep (se 1 (by rfl) ⟨1343141, by rfl⟩ : syracuseStep 1790855 = 2686283) B2686283
theorem B1790863 : Blo 1790096 1790863 := bstep (se 1 (by rfl) ⟨1343147, by rfl⟩ : syracuseStep 1790863 = 2686295) B2686295
theorem B4305811 : Blo 1790096 4305811 := bstep (se 1 (by rfl) ⟨3229358, by rfl⟩ : syracuseStep 4305811 = 6458717) B6458717
theorem B1790907 : Blo 1790096 1790907 := bstep (se 1 (by rfl) ⟨1343180, by rfl⟩ : syracuseStep 1790907 = 2686361) B2686361
theorem B1790983 : Blo 1790096 1790983 := bstep (se 1 (by rfl) ⟨1343237, by rfl⟩ : syracuseStep 1790983 = 2686475) B2686475
theorem B1790991 : Blo 1790096 1790991 := bstep (se 1 (by rfl) ⟨1343243, by rfl⟩ : syracuseStep 1790991 = 2686487) B2686487
theorem B4535311 : Blo 1790096 4535311 := bstep (se 1 (by rfl) ⟨3401483, by rfl⟩ : syracuseStep 4535311 = 6802967) B6802967
theorem B6042653 : Blo 1790096 6042653 := bstep (se 3 (by rfl) ⟨1132997, by rfl⟩ : syracuseStep 6042653 = 2265995) B2265995
theorem B10335275 : Blo 1790096 10335275 := bstep (se 1 (by rfl) ⟨7751456, by rfl⟩ : syracuseStep 10335275 = 15502913) B15502913
theorem B1791035 : Blo 1790096 1791035 := bstep (se 1 (by rfl) ⟨1343276, by rfl⟩ : syracuseStep 1791035 = 2686553) B2686553
theorem B1791111 : Blo 1790096 1791111 := bstep (se 1 (by rfl) ⟨1343333, by rfl⟩ : syracuseStep 1791111 = 2686667) B2686667
theorem B1791119 : Blo 1790096 1791119 := bstep (se 1 (by rfl) ⟨1343339, by rfl⟩ : syracuseStep 1791119 = 2686679) B2686679
theorem B8606893 : Blo 1790096 8606893 := bstep (se 3 (by rfl) ⟨1613792, by rfl⟩ : syracuseStep 8606893 = 3227585) B3227585
theorem B1791163 : Blo 1790096 1791163 := bstep (se 1 (by rfl) ⟨1343372, by rfl⟩ : syracuseStep 1791163 = 2686745) B2686745
theorem B13595849 : Blo 1790096 13595849 := bstep (se 2 (by rfl) ⟨5098443, by rfl⟩ : syracuseStep 13595849 = 10196887) B10196887
theorem B5100745 : Blo 1790096 5100745 := bstep (se 2 (by rfl) ⟨1912779, by rfl⟩ : syracuseStep 5100745 = 3825559) B3825559
theorem B2266375 : Blo 1790096 2266375 := bstep (se 1 (by rfl) ⟨1699781, by rfl⟩ : syracuseStep 2266375 = 3399563) B3399563
theorem B1791239 : Blo 1790096 1791239 := bstep (se 1 (by rfl) ⟨1343429, by rfl⟩ : syracuseStep 1791239 = 2686859) B2686859
theorem B1791247 : Blo 1790096 1791247 := bstep (se 1 (by rfl) ⟨1343435, by rfl⟩ : syracuseStep 1791247 = 2686871) B2686871
theorem B4535585 : Blo 1790096 4535585 := bstep (se 2 (by rfl) ⟨1700844, by rfl⟩ : syracuseStep 4535585 = 3401689) B3401689
theorem B1791291 : Blo 1790096 1791291 := bstep (se 1 (by rfl) ⟨1343468, by rfl⟩ : syracuseStep 1791291 = 2686937) B2686937
theorem B9065843 : Blo 1790096 9065843 := bstep (se 1 (by rfl) ⟨6799382, by rfl⟩ : syracuseStep 9065843 = 13598765) B13598765
theorem B1791367 : Blo 1790096 1791367 := bstep (se 1 (by rfl) ⟨1343525, by rfl⟩ : syracuseStep 1791367 = 2687051) B2687051
theorem B1791375 : Blo 1790096 1791375 := bstep (se 1 (by rfl) ⟨1343531, by rfl⟩ : syracuseStep 1791375 = 2687063) B2687063
theorem B8607161 : Blo 1790096 8607161 := bstep (se 2 (by rfl) ⟨3227685, by rfl⟩ : syracuseStep 8607161 = 6455371) B6455371
theorem B1791419 : Blo 1790096 1791419 := bstep (se 1 (by rfl) ⟨1343564, by rfl⟩ : syracuseStep 1791419 = 2687129) B2687129
theorem B18388433 : Blo 1790096 18388433 := bstep (se 2 (by rfl) ⟨6895662, by rfl⟩ : syracuseStep 18388433 = 13791325) B13791325
theorem B1791495 : Blo 1790096 1791495 := bstep (se 1 (by rfl) ⟨1343621, by rfl⟩ : syracuseStep 1791495 = 2687243) B2687243
theorem B1791503 : Blo 1790096 1791503 := bstep (se 1 (by rfl) ⟨1343627, by rfl⟩ : syracuseStep 1791503 = 2687255) B2687255
theorem B5518891 : Blo 1790096 5518891 := bstep (se 1 (by rfl) ⟨4139168, by rfl⟩ : syracuseStep 5518891 = 8278337) B8278337
theorem B1791547 : Blo 1790096 1791547 := bstep (se 1 (by rfl) ⟨1343660, by rfl⟩ : syracuseStep 1791547 = 2687321) B2687321
theorem B7648829 : Blo 1790096 7648829 := bstep (se 3 (by rfl) ⟨1434155, by rfl⟩ : syracuseStep 7648829 = 2868311) B2868311
theorem B4028039 : Blo 1790096 4028039 := bstep (se 1 (by rfl) ⟨3021029, by rfl⟩ : syracuseStep 4028039 = 6042059) B6042059
theorem B1791623 : Blo 1790096 1791623 := bstep (se 1 (by rfl) ⟨1343717, by rfl⟩ : syracuseStep 1791623 = 2687435) B2687435
theorem B1791631 : Blo 1790096 1791631 := bstep (se 1 (by rfl) ⟨1343723, by rfl⟩ : syracuseStep 1791631 = 2687447) B2687447
theorem B2266795 : Blo 1790096 2266795 := bstep (se 1 (by rfl) ⟨1700096, by rfl⟩ : syracuseStep 2266795 = 3400193) B3400193
theorem B4839097 : Blo 1790096 4839097 := bstep (se 2 (by rfl) ⟨1814661, by rfl⟩ : syracuseStep 4839097 = 3629323) B3629323
theorem B1791675 : Blo 1790096 1791675 := bstep (se 1 (by rfl) ⟨1343756, by rfl⟩ : syracuseStep 1791675 = 2687513) B2687513
theorem B1791751 : Blo 1790096 1791751 := bstep (se 1 (by rfl) ⟨1343813, by rfl⟩ : syracuseStep 1791751 = 2687627) B2687627
theorem B1791759 : Blo 1790096 1791759 := bstep (se 1 (by rfl) ⟨1343819, by rfl⟩ : syracuseStep 1791759 = 2687639) B2687639
theorem B4028219 : Blo 1790096 4028219 := bstep (se 1 (by rfl) ⟨3021164, by rfl⟩ : syracuseStep 4028219 = 6042329) B6042329
theorem B1791803 : Blo 1790096 1791803 := bstep (se 1 (by rfl) ⟨1343852, by rfl⟩ : syracuseStep 1791803 = 2687705) B2687705
theorem B9066329 : Blo 1790096 9066329 := bstep (se 2 (by rfl) ⟨3399873, by rfl⟩ : syracuseStep 9066329 = 6799747) B6799747
theorem B1791879 : Blo 1790096 1791879 := bstep (se 1 (by rfl) ⟨1343909, by rfl⟩ : syracuseStep 1791879 = 2687819) B2687819
theorem B2267023 : Blo 1790096 2267023 := bstep (se 1 (by rfl) ⟨1700267, by rfl⟩ : syracuseStep 2267023 = 3400535) B3400535
theorem B1791887 : Blo 1790096 1791887 := bstep (se 1 (by rfl) ⟨1343915, by rfl⟩ : syracuseStep 1791887 = 2687831) B2687831
theorem B4028345 : Blo 1790096 4028345 := bstep (se 2 (by rfl) ⟨1510629, by rfl⟩ : syracuseStep 4028345 = 3021259) B3021259
theorem B1791931 : Blo 1790096 1791931 := bstep (se 1 (by rfl) ⟨1343948, by rfl⟩ : syracuseStep 1791931 = 2687897) B2687897
theorem B1792007 : Blo 1790096 1792007 := bstep (se 1 (by rfl) ⟨1344005, by rfl⟩ : syracuseStep 1792007 = 2688011) B2688011
theorem B1792015 : Blo 1790096 1792015 := bstep (se 1 (by rfl) ⟨1344011, by rfl⟩ : syracuseStep 1792015 = 2688023) B2688023
theorem B17209367 : Blo 1790096 17209367 := bstep (se 1 (by rfl) ⟨12907025, by rfl⟩ : syracuseStep 17209367 = 25814051) B25814051
theorem B24508439 : Blo 1790096 24508439 := bstep (se 1 (by rfl) ⟨18381329, by rfl⟩ : syracuseStep 24508439 = 36762659) B36762659
theorem B26171437 : Blo 1790096 26171437 := bstep (se 3 (by rfl) ⟨4907144, by rfl⟩ : syracuseStep 26171437 = 9814289) B9814289
theorem B1792059 : Blo 1790096 1792059 := bstep (se 1 (by rfl) ⟨1344044, by rfl⟩ : syracuseStep 1792059 = 2688089) B2688089
theorem B3020935 : Blo 1790096 3020935 := bstep (se 1 (by rfl) ⟨2265701, by rfl⟩ : syracuseStep 3020935 = 4531403) B4531403
theorem B2685191 : Blo 1790096 2685191 := bstep (se 1 (by rfl) ⟨2013893, by rfl⟩ : syracuseStep 2685191 = 4027787) B4027787
theorem B4028687 : Blo 1790096 4028687 := bstep (se 1 (by rfl) ⟨3021515, by rfl⟩ : syracuseStep 4028687 = 6043031) B6043031
theorem B4028705 : Blo 1790096 4028705 := bstep (se 2 (by rfl) ⟨1510764, by rfl⟩ : syracuseStep 4028705 = 3021529) B3021529
theorem B3225899 : Blo 1790096 3225899 := bstep (se 1 (by rfl) ⟨2419424, by rfl⟩ : syracuseStep 3225899 = 4838849) B4838849
theorem B2685227 : Blo 1790096 2685227 := bstep (se 1 (by rfl) ⟨2013920, by rfl⟩ : syracuseStep 2685227 = 4027841) B4027841
theorem B2685257 : Blo 1790096 2685257 := bstep (se 2 (by rfl) ⟨1006971, by rfl⟩ : syracuseStep 2685257 = 2013943) B2013943
theorem B10475891 : Blo 1790096 10475891 := bstep (se 1 (by rfl) ⟨7856918, by rfl⟩ : syracuseStep 10475891 = 15713837) B15713837
theorem B6044057 : Blo 1790096 6044057 := bstep (se 2 (by rfl) ⟨2266521, by rfl⟩ : syracuseStep 6044057 = 4533043) B4533043
theorem B2685371 : Blo 1790096 2685371 := bstep (se 1 (by rfl) ⟨2014028, by rfl⟩ : syracuseStep 2685371 = 4028057) B4028057
theorem B2685431 : Blo 1790096 2685431 := bstep (se 1 (by rfl) ⟨2014073, by rfl⟩ : syracuseStep 2685431 = 4028147) B4028147
theorem B14531075 : Blo 1790096 14531075 := bstep (se 1 (by rfl) ⟨10898306, by rfl⟩ : syracuseStep 14531075 = 21796613) B21796613
theorem B2685455 : Blo 1790096 2685455 := bstep (se 1 (by rfl) ⟨2014091, by rfl⟩ : syracuseStep 2685455 = 4028183) B4028183
theorem B2685497 : Blo 1790096 2685497 := bstep (se 2 (by rfl) ⟨1007061, by rfl⟩ : syracuseStep 2685497 = 2014123) B2014123
theorem B4029047 : Blo 1790096 4029047 := bstep (se 1 (by rfl) ⟨3021785, by rfl⟩ : syracuseStep 4029047 = 6043571) B6043571
theorem B2267767 : Blo 1790096 2267767 := bstep (se 1 (by rfl) ⟨1700825, by rfl⟩ : syracuseStep 2267767 = 3401651) B3401651
theorem B2685575 : Blo 1790096 2685575 := bstep (se 1 (by rfl) ⟨2014181, by rfl⟩ : syracuseStep 2685575 = 4028363) B4028363
theorem B2685611 : Blo 1790096 2685611 := bstep (se 1 (by rfl) ⟨2014208, by rfl⟩ : syracuseStep 2685611 = 4028417) B4028417
theorem B13605569 : Blo 1790096 13605569 := bstep (se 2 (by rfl) ⟨5102088, by rfl⟩ : syracuseStep 13605569 = 10204177) B10204177
theorem B2685641 : Blo 1790096 2685641 := bstep (se 2 (by rfl) ⟨1007115, by rfl⟩ : syracuseStep 2685641 = 2014231) B2014231
theorem B3824329 : Blo 1790096 3824329 := bstep (se 2 (by rfl) ⟨1434123, by rfl⟩ : syracuseStep 3824329 = 2868247) B2868247
theorem B3021583 : Blo 1790096 3021583 := bstep (se 1 (by rfl) ⟨2266187, by rfl⟩ : syracuseStep 3021583 = 4532375) B4532375
theorem B4029227 : Blo 1790096 4029227 := bstep (se 1 (by rfl) ⟨3021920, by rfl⟩ : syracuseStep 4029227 = 6043841) B6043841
theorem B2685755 : Blo 1790096 2685755 := bstep (se 1 (by rfl) ⟨2014316, by rfl⟩ : syracuseStep 2685755 = 4028633) B4028633
theorem B2685815 : Blo 1790096 2685815 := bstep (se 1 (by rfl) ⟨2014361, by rfl⟩ : syracuseStep 2685815 = 4028723) B4028723
theorem B2014087 : Blo 1790096 2014087 := bstep (se 1 (by rfl) ⟨1510565, by rfl⟩ : syracuseStep 2014087 = 3021131) B3021131
theorem B2685839 : Blo 1790096 2685839 := bstep (se 1 (by rfl) ⟨2014379, by rfl⟩ : syracuseStep 2685839 = 4028759) B4028759
theorem B2685881 : Blo 1790096 2685881 := bstep (se 2 (by rfl) ⟨1007205, by rfl⟩ : syracuseStep 2685881 = 2014411) B2014411
theorem B2268091 : Blo 1790096 2268091 := bstep (se 1 (by rfl) ⟨1701068, by rfl⟩ : syracuseStep 2268091 = 3402137) B3402137
theorem B3824585 : Blo 1790096 3824585 := bstep (se 2 (by rfl) ⟨1434219, by rfl⟩ : syracuseStep 3824585 = 2868439) B2868439
theorem B6798289 : Blo 1790096 6798289 := bstep (se 2 (by rfl) ⟨2549358, by rfl⟩ : syracuseStep 6798289 = 5098717) B5098717
theorem B10206161 : Blo 1790096 10206161 := bstep (se 2 (by rfl) ⟨3827310, by rfl⟩ : syracuseStep 10206161 = 7654621) B7654621
theorem B2685959 : Blo 1790096 2685959 := bstep (se 1 (by rfl) ⟨2014469, by rfl⟩ : syracuseStep 2685959 = 4028939) B4028939
theorem B3398689 : Blo 1790096 3398689 := bstep (se 2 (by rfl) ⟨1274508, by rfl⟩ : syracuseStep 3398689 = 2549017) B2549017
theorem B4840481 : Blo 1790096 4840481 := bstep (se 2 (by rfl) ⟨1815180, by rfl⟩ : syracuseStep 4840481 = 3630361) B3630361
theorem B2685995 : Blo 1790096 2685995 := bstep (se 1 (by rfl) ⟨2014496, by rfl⟩ : syracuseStep 2685995 = 4028993) B4028993
theorem B7756843 : Blo 1790096 7756843 := bstep (se 1 (by rfl) ⟨5817632, by rfl⟩ : syracuseStep 7756843 = 11635265) B11635265
theorem B2014267 : Blo 1790096 2014267 := bstep (se 1 (by rfl) ⟨1510700, by rfl⟩ : syracuseStep 2014267 = 3021401) B3021401
theorem B5168189 : Blo 1790096 5168189 := bstep (se 3 (by rfl) ⟨969035, by rfl⟩ : syracuseStep 5168189 = 1938071) B1938071
theorem B6454333 : Blo 1790096 6454333 := bstep (se 3 (by rfl) ⟨1210187, by rfl⟩ : syracuseStep 6454333 = 2420375) B2420375
theorem B2686025 : Blo 1790096 2686025 := bstep (se 2 (by rfl) ⟨1007259, by rfl⟩ : syracuseStep 2686025 = 2014519) B2014519
theorem B6044759 : Blo 1790096 6044759 := bstep (se 1 (by rfl) ⟨4533569, by rfl⟩ : syracuseStep 6044759 = 9067139) B9067139
theorem B4029587 : Blo 1790096 4029587 := bstep (se 1 (by rfl) ⟨3022190, by rfl⟩ : syracuseStep 4029587 = 6044381) B6044381
theorem B2686139 : Blo 1790096 2686139 := bstep (se 1 (by rfl) ⟨2014604, by rfl⟩ : syracuseStep 2686139 = 4029209) B4029209
theorem B4029641 : Blo 1790096 4029641 := bstep (se 2 (by rfl) ⟨1511115, by rfl⟩ : syracuseStep 4029641 = 3022231) B3022231
theorem B2686199 : Blo 1790096 2686199 := bstep (se 1 (by rfl) ⟨2014649, by rfl⟩ : syracuseStep 2686199 = 4029299) B4029299
theorem B6798593 : Blo 1790096 6798593 := bstep (se 2 (by rfl) ⟨2549472, by rfl⟩ : syracuseStep 6798593 = 5098945) B5098945
theorem B7462145 : Blo 1790096 7462145 := bstep (se 2 (by rfl) ⟨2798304, by rfl⟩ : syracuseStep 7462145 = 5596609) B5596609
theorem B2686223 : Blo 1790096 2686223 := bstep (se 1 (by rfl) ⟨2014667, by rfl⟩ : syracuseStep 2686223 = 4029335) B4029335
theorem B3022123 : Blo 1790096 3022123 := bstep (se 1 (by rfl) ⟨2266592, by rfl⟩ : syracuseStep 3022123 = 4533185) B4533185
theorem B2686265 : Blo 1790096 2686265 := bstep (se 2 (by rfl) ⟨1007349, by rfl⟩ : syracuseStep 2686265 = 2014699) B2014699
theorem B5102909 : Blo 1790096 5102909 := bstep (se 3 (by rfl) ⟨956795, by rfl⟩ : syracuseStep 5102909 = 1913591) B1913591
theorem B2686343 : Blo 1790096 2686343 := bstep (se 1 (by rfl) ⟨2014757, by rfl⟩ : syracuseStep 2686343 = 4029515) B4029515
theorem B7363993 : Blo 1790096 7363993 := bstep (se 2 (by rfl) ⟨2761497, by rfl⟩ : syracuseStep 7363993 = 5522995) B5522995
theorem B2686379 : Blo 1790096 2686379 := bstep (se 1 (by rfl) ⟨2014784, by rfl⟩ : syracuseStep 2686379 = 4029569) B4029569
theorem B3022265 : Blo 1790096 3022265 := bstep (se 2 (by rfl) ⟨1133349, by rfl⟩ : syracuseStep 3022265 = 2266699) B2266699
theorem B2686409 : Blo 1790096 2686409 := bstep (se 2 (by rfl) ⟨1007403, by rfl⟩ : syracuseStep 2686409 = 2014807) B2014807
theorem B2014735 : Blo 1790096 2014735 := bstep (se 1 (by rfl) ⟨1511051, by rfl⟩ : syracuseStep 2014735 = 3022103) B3022103
theorem B7650845 : Blo 1790096 7650845 := bstep (se 3 (by rfl) ⟨1434533, by rfl⟩ : syracuseStep 7650845 = 2869067) B2869067
theorem B5103137 : Blo 1790096 5103137 := bstep (se 2 (by rfl) ⟨1913676, by rfl⟩ : syracuseStep 5103137 = 3827353) B3827353
theorem B2686523 : Blo 1790096 2686523 := bstep (se 1 (by rfl) ⟨2014892, by rfl⟩ : syracuseStep 2686523 = 4029785) B4029785
theorem B6045245 : Blo 1790096 6045245 := bstep (se 3 (by rfl) ⟨1133483, by rfl⟩ : syracuseStep 6045245 = 2266967) B2266967
theorem B30604877 : Blo 1790096 30604877 := bstep (se 3 (by rfl) ⟨5738414, by rfl⟩ : syracuseStep 30604877 = 11476829) B11476829
theorem B124149347 : Blo 1790096 124149347 := bstep (se 1 (by rfl) ⟨93112010, by rfl⟩ : syracuseStep 124149347 = 186224021) B186224021
theorem B2686583 : Blo 1790096 2686583 := bstep (se 1 (by rfl) ⟨2014937, by rfl⟩ : syracuseStep 2686583 = 4029875) B4029875
theorem B2686607 : Blo 1790096 2686607 := bstep (se 1 (by rfl) ⟨2014955, by rfl⟩ : syracuseStep 2686607 = 4029911) B4029911
theorem B22945457 : Blo 1790096 22945457 := bstep (se 2 (by rfl) ⟨8604546, by rfl⟩ : syracuseStep 22945457 = 17209093) B17209093
theorem B2686649 : Blo 1790096 2686649 := bstep (se 2 (by rfl) ⟨1007493, by rfl⟩ : syracuseStep 2686649 = 2014987) B2014987
theorem B6799049 : Blo 1790096 6799049 := bstep (se 2 (by rfl) ⟨2549643, by rfl⟩ : syracuseStep 6799049 = 5099287) B5099287
theorem B2686727 : Blo 1790096 2686727 := bstep (se 1 (by rfl) ⟨2015045, by rfl⟩ : syracuseStep 2686727 = 4030091) B4030091
theorem B2686763 : Blo 1790096 2686763 := bstep (se 1 (by rfl) ⟨2015072, by rfl⟩ : syracuseStep 2686763 = 4030145) B4030145
theorem B2686793 : Blo 1790096 2686793 := bstep (se 2 (by rfl) ⟨1007547, by rfl⟩ : syracuseStep 2686793 = 2015095) B2015095
theorem B29048651 : Blo 1790096 29048651 := bstep (se 1 (by rfl) ⟨21786488, by rfl⟩ : syracuseStep 29048651 = 43572977) B43572977
theorem B4030343 : Blo 1790096 4030343 := bstep (se 1 (by rfl) ⟨3022757, by rfl⟩ : syracuseStep 4030343 = 6045515) B6045515
theorem B9068435 : Blo 1790096 9068435 := bstep (se 1 (by rfl) ⟨6801326, by rfl⟩ : syracuseStep 9068435 = 13602653) B13602653
theorem B20406167 : Blo 1790096 20406167 := bstep (se 1 (by rfl) ⟨15304625, by rfl⟩ : syracuseStep 20406167 = 30609251) B30609251
theorem B2686907 : Blo 1790096 2686907 := bstep (se 1 (by rfl) ⟨2015180, by rfl⟩ : syracuseStep 2686907 = 4030361) B4030361
theorem B2686967 : Blo 1790096 2686967 := bstep (se 1 (by rfl) ⟨2015225, by rfl⟩ : syracuseStep 2686967 = 4030451) B4030451
theorem B2686985 : Blo 1790096 2686985 := bstep (se 2 (by rfl) ⟨1007619, by rfl⟩ : syracuseStep 2686985 = 2015239) B2015239
theorem B2687015 : Blo 1790096 2687015 := bstep (se 1 (by rfl) ⟨2015261, by rfl⟩ : syracuseStep 2687015 = 4030523) B4030523
theorem B14516281 : Blo 1790096 14516281 := bstep (se 2 (by rfl) ⟨5443605, by rfl⟩ : syracuseStep 14516281 = 10887211) B10887211
theorem B2015311 : Blo 1790096 2015311 := bstep (se 1 (by rfl) ⟨1511483, by rfl⟩ : syracuseStep 2015311 = 3022967) B3022967
theorem B19357811 : Blo 1790096 19357811 := bstep (se 1 (by rfl) ⟨14518358, by rfl⟩ : syracuseStep 19357811 = 29036717) B29036717
theorem B13607027 : Blo 1790096 13607027 := bstep (se 1 (by rfl) ⟨10205270, by rfl⟩ : syracuseStep 13607027 = 20410541) B20410541
theorem B2687099 : Blo 1790096 2687099 := bstep (se 1 (by rfl) ⟨2015324, by rfl⟩ : syracuseStep 2687099 = 4030649) B4030649
theorem B3023095 : Blo 1790096 3023095 := bstep (se 1 (by rfl) ⟨2267321, by rfl⟩ : syracuseStep 3023095 = 4534643) B4534643
theorem B2687225 : Blo 1790096 2687225 := bstep (se 2 (by rfl) ⟨1007709, by rfl⟩ : syracuseStep 2687225 = 2015419) B2015419
theorem B2687327 : Blo 1790096 2687327 := bstep (se 1 (by rfl) ⟨2015495, by rfl⟩ : syracuseStep 2687327 = 4030991) B4030991
theorem B2687339 : Blo 1790096 2687339 := bstep (se 1 (by rfl) ⟨2015504, by rfl⟩ : syracuseStep 2687339 = 4031009) B4031009
theorem B3023291 : Blo 1790096 3023291 := bstep (se 1 (by rfl) ⟨2267468, by rfl⟩ : syracuseStep 3023291 = 4534937) B4534937
theorem B4301275 : Blo 1790096 4301275 := bstep (se 1 (by rfl) ⟨3225956, by rfl⟩ : syracuseStep 4301275 = 6451913) B6451913
theorem B2015707 : Blo 1790096 2015707 := bstep (se 1 (by rfl) ⟨1511780, by rfl⟩ : syracuseStep 2015707 = 3023561) B3023561
theorem B5448179 : Blo 1790096 5448179 := bstep (se 1 (by rfl) ⟨4086134, by rfl⟩ : syracuseStep 5448179 = 8172269) B8172269
theorem B6046217 : Blo 1790096 6046217 := bstep (se 2 (by rfl) ⟨2267331, by rfl⟩ : syracuseStep 6046217 = 4534663) B4534663
theorem B4301351 : Blo 1790096 4301351 := bstep (se 1 (by rfl) ⟨3226013, by rfl⟩ : syracuseStep 4301351 = 6452027) B6452027
theorem B3400231 : Blo 1790096 3400231 := bstep (se 1 (by rfl) ⟨2550173, by rfl⟩ : syracuseStep 3400231 = 5100347) B5100347
theorem B3023399 : Blo 1790096 3023399 := bstep (se 1 (by rfl) ⟨2267549, by rfl⟩ : syracuseStep 3023399 = 4535099) B4535099
theorem B2687567 : Blo 1790096 2687567 := bstep (se 1 (by rfl) ⟨2015675, by rfl⟩ : syracuseStep 2687567 = 4031351) B4031351
theorem B5169761 : Blo 1790096 5169761 := bstep (se 2 (by rfl) ⟨1938660, by rfl⟩ : syracuseStep 5169761 = 3877321) B3877321
theorem B4031099 : Blo 1790096 4031099 := bstep (se 1 (by rfl) ⟨3023324, by rfl⟩ : syracuseStep 4031099 = 6046649) B6046649
theorem B19899053 : Blo 1790096 19899053 := bstep (se 3 (by rfl) ⟨3731072, by rfl⟩ : syracuseStep 19899053 = 7462145) B7462145
theorem B6890183 : Blo 1790096 6890183 := bstep (se 1 (by rfl) ⟨5167637, by rfl⟩ : syracuseStep 6890183 = 10335275) B10335275
theorem B2687687 : Blo 1790096 2687687 := bstep (se 1 (by rfl) ⟨2015765, by rfl⟩ : syracuseStep 2687687 = 4031531) B4031531
theorem B4031225 : Blo 1790096 4031225 := bstep (se 2 (by rfl) ⟨1511709, by rfl⟩ : syracuseStep 4031225 = 3023419) B3023419
theorem B3023689 : Blo 1790096 3023689 := bstep (se 2 (by rfl) ⟨1133883, by rfl⟩ : syracuseStep 3023689 = 2267767) B2267767
theorem B2687849 : Blo 1790096 2687849 := bstep (se 2 (by rfl) ⟨1007943, by rfl⟩ : syracuseStep 2687849 = 2015887) B2015887
theorem B3023723 : Blo 1790096 3023723 := bstep (se 1 (by rfl) ⟨2267792, by rfl⟩ : syracuseStep 3023723 = 4535585) B4535585
theorem B2687927 : Blo 1790096 2687927 := bstep (se 1 (by rfl) ⟨2015945, by rfl⟩ : syracuseStep 2687927 = 4031891) B4031891
theorem B2687963 : Blo 1790096 2687963 := bstep (se 1 (by rfl) ⟨2015972, by rfl⟩ : syracuseStep 2687963 = 4031945) B4031945
theorem B8602625 : Blo 1790096 8602625 := bstep (se 2 (by rfl) ⟨3225984, by rfl⟩ : syracuseStep 8602625 = 6451969) B6451969
theorem B9069569 : Blo 1790096 9069569 := bstep (se 2 (by rfl) ⟨3401088, by rfl⟩ : syracuseStep 9069569 = 6802177) B6802177
theorem B4031495 : Blo 1790096 4031495 := bstep (se 1 (by rfl) ⟨3023621, by rfl⟩ : syracuseStep 4031495 = 6047243) B6047243
theorem B4031567 : Blo 1790096 4031567 := bstep (se 1 (by rfl) ⟨3023675, by rfl⟩ : syracuseStep 4031567 = 6047351) B6047351
theorem B6800537 : Blo 1790096 6800537 := bstep (se 2 (by rfl) ⟨2550201, by rfl⟩ : syracuseStep 6800537 = 5100403) B5100403
theorem B9684139 : Blo 1790096 9684139 := bstep (se 1 (by rfl) ⟨7263104, by rfl⟩ : syracuseStep 9684139 = 14526209) B14526209
theorem B3024121 : Blo 1790096 3024121 := bstep (se 2 (by rfl) ⟨1134045, by rfl⟩ : syracuseStep 3024121 = 2268091) B2268091
theorem B6047081 : Blo 1790096 6047081 := bstep (se 2 (by rfl) ⟨2267655, by rfl⟩ : syracuseStep 6047081 = 4535311) B4535311
theorem B4531585 : Blo 1790096 4531585 := bstep (se 2 (by rfl) ⟨1699344, by rfl⟩ : syracuseStep 4531585 = 3398689) B3398689
theorem B4031963 : Blo 1790096 4031963 := bstep (se 1 (by rfl) ⟨3023972, by rfl⟩ : syracuseStep 4031963 = 6047945) B6047945
theorem B29042165 : Blo 1790096 29042165 := bstep (se 5 (by rfl) ⟨1361351, by rfl⟩ : syracuseStep 29042165 = 2722703) B2722703
theorem B32687621 : Blo 1790096 32687621 := bstep (se 4 (by rfl) ⟨3064464, by rfl⟩ : syracuseStep 32687621 = 6128929) B6128929
theorem B6800993 : Blo 1790096 6800993 := bstep (se 2 (by rfl) ⟨2550372, by rfl⟩ : syracuseStep 6800993 = 5100745) B5100745
theorem B9070379 : Blo 1790096 9070379 := bstep (se 1 (by rfl) ⟨6802784, by rfl⟩ : syracuseStep 9070379 = 13605569) B13605569
theorem B103335749 : Blo 1790096 103335749 := bstep (se 4 (by rfl) ⟨9687726, by rfl⟩ : syracuseStep 103335749 = 19375453) B19375453
theorem B6047675 : Blo 1790096 6047675 := bstep (se 1 (by rfl) ⟨4535756, by rfl⟩ : syracuseStep 6047675 = 9071513) B9071513
theorem B2549723 : Blo 1790096 2549723 := bstep (se 1 (by rfl) ⟨1912292, by rfl⟩ : syracuseStep 2549723 = 3824585) B3824585
theorem B5736467 : Blo 1790096 5736467 := bstep (se 1 (by rfl) ⟨4302350, by rfl⟩ : syracuseStep 5736467 = 8604701) B8604701
theorem B7358521 : Blo 1790096 7358521 := bstep (se 2 (by rfl) ⟨2759445, by rfl⟩ : syracuseStep 7358521 = 5518891) B5518891
theorem B22956119 : Blo 1790096 22956119 := bstep (se 1 (by rfl) ⟨17217089, by rfl⟩ : syracuseStep 22956119 = 34434179) B34434179
theorem B4532395 : Blo 1790096 4532395 := bstep (se 1 (by rfl) ⟨3399296, by rfl⟩ : syracuseStep 4532395 = 6798593) B6798593
theorem B3401939 : Blo 1790096 3401939 := bstep (se 1 (by rfl) ⟨2551454, by rfl⟩ : syracuseStep 3401939 = 5102909) B5102909
theorem B5818711 : Blo 1790096 5818711 := bstep (se 1 (by rfl) ⟨4364033, by rfl⟩ : syracuseStep 5818711 = 8728067) B8728067
theorem B3402091 : Blo 1790096 3402091 := bstep (se 1 (by rfl) ⟨2551568, by rfl⟩ : syracuseStep 3402091 = 5103137) B5103137
theorem B82766231 : Blo 1790096 82766231 := bstep (se 1 (by rfl) ⟨62074673, by rfl⟩ : syracuseStep 82766231 = 124149347) B124149347
theorem B15296971 : Blo 1790096 15296971 := bstep (se 1 (by rfl) ⟨11472728, by rfl⟩ : syracuseStep 15296971 = 22945457) B22945457
theorem B4532699 : Blo 1790096 4532699 := bstep (se 1 (by rfl) ⟨3399524, by rfl⟩ : syracuseStep 4532699 = 6799049) B6799049
theorem B13601681 : Blo 1790096 13601681 := bstep (se 2 (by rfl) ⟨5100630, by rfl⟩ : syracuseStep 13601681 = 10201261) B10201261
theorem B7359407 : Blo 1790096 7359407 := bstep (se 1 (by rfl) ⟨5519555, by rfl⟩ : syracuseStep 7359407 = 11039111) B11039111
theorem B2550703 : Blo 1790096 2550703 := bstep (se 1 (by rfl) ⟨1913027, by rfl⟩ : syracuseStep 2550703 = 3826055) B3826055
theorem B6802451 : Blo 1790096 6802451 := bstep (se 1 (by rfl) ⟨5101838, by rfl⟩ : syracuseStep 6802451 = 10203677) B10203677
theorem B16338115 : Blo 1790096 16338115 := bstep (se 1 (by rfl) ⟨12253586, by rfl⟩ : syracuseStep 16338115 = 24507173) B24507173
theorem B4304119 : Blo 1790096 4304119 := bstep (se 1 (by rfl) ⟨3228089, by rfl⟩ : syracuseStep 4304119 = 6456179) B6456179
theorem B9063899 : Blo 1790096 9063899 := bstep (se 1 (by rfl) ⟨6797924, by rfl⟩ : syracuseStep 9063899 = 13595849) B13595849
theorem B2551375 : Blo 1790096 2551375 := bstep (se 1 (by rfl) ⟨1913531, by rfl⟩ : syracuseStep 2551375 = 3827063) B3827063
theorem B5099105 : Blo 1790096 5099105 := bstep (se 2 (by rfl) ⟨1912164, by rfl⟩ : syracuseStep 5099105 = 3824329) B3824329
theorem B12258955 : Blo 1790096 12258955 := bstep (se 1 (by rfl) ⟨9194216, by rfl⟩ : syracuseStep 12258955 = 18388433) B18388433
theorem B2551495 : Blo 1790096 2551495 := bstep (se 1 (by rfl) ⟨1913621, by rfl⟩ : syracuseStep 2551495 = 3827243) B3827243
theorem B5099219 : Blo 1790096 5099219 := bstep (se 1 (by rfl) ⟨3824414, by rfl⟩ : syracuseStep 5099219 = 7648829) B7648829
theorem B37760903 : Blo 1790096 37760903 := bstep (se 1 (by rfl) ⟨28320677, by rfl⟩ : syracuseStep 37760903 = 56641355) B56641355
theorem B4534177 : Blo 1790096 4534177 := bstep (se 2 (by rfl) ⟨1700316, by rfl⟩ : syracuseStep 4534177 = 3400633) B3400633
theorem B9064385 : Blo 1790096 9064385 := bstep (se 2 (by rfl) ⟨3399144, by rfl⟩ : syracuseStep 9064385 = 6798289) B6798289
theorem B104730629 : Blo 1790096 104730629 := bstep (se 4 (by rfl) ⟨9818496, by rfl⟩ : syracuseStep 104730629 = 19636993) B19636993
theorem B11472911 : Blo 1790096 11472911 := bstep (se 1 (by rfl) ⟨8604683, by rfl⟩ : syracuseStep 11472911 = 17209367) B17209367
theorem B16338959 : Blo 1790096 16338959 := bstep (se 1 (by rfl) ⟨12254219, by rfl⟩ : syracuseStep 16338959 = 24508439) B24508439
theorem B17215517 : Blo 1790096 17215517 := bstep (se 3 (by rfl) ⟨3227909, by rfl⟩ : syracuseStep 17215517 = 6455819) B6455819
theorem B2584615 : Blo 1790096 2584615 := bstep (se 1 (by rfl) ⟨1938461, by rfl⟩ : syracuseStep 2584615 = 3876923) B3876923
theorem B10342457 : Blo 1790096 10342457 := bstep (se 2 (by rfl) ⟨3878421, by rfl⟩ : syracuseStep 10342457 = 7756843) B7756843
theorem B8605777 : Blo 1790096 8605777 := bstep (se 2 (by rfl) ⟨3227166, by rfl⟩ : syracuseStep 8605777 = 6454333) B6454333
theorem B1790127 : Blo 1790096 1790127 := bstep (se 1 (by rfl) ⟨1342595, by rfl⟩ : syracuseStep 1790127 = 2685191) B2685191
theorem B2150599 : Blo 1790096 2150599 := bstep (se 1 (by rfl) ⟨1612949, by rfl⟩ : syracuseStep 2150599 = 3225899) B3225899
theorem B1790151 : Blo 1790096 1790151 := bstep (se 1 (by rfl) ⟨1342613, by rfl⟩ : syracuseStep 1790151 = 2685227) B2685227
theorem B1790171 : Blo 1790096 1790171 := bstep (se 1 (by rfl) ⟨1342628, by rfl⟩ : syracuseStep 1790171 = 2685257) B2685257
theorem B6983927 : Blo 1790096 6983927 := bstep (se 1 (by rfl) ⟨5237945, by rfl⟩ : syracuseStep 6983927 = 10475891) B10475891
theorem B1790247 : Blo 1790096 1790247 := bstep (se 1 (by rfl) ⟨1342685, by rfl⟩ : syracuseStep 1790247 = 2685371) B2685371
theorem B1790287 : Blo 1790096 1790287 := bstep (se 1 (by rfl) ⟨1342715, by rfl⟩ : syracuseStep 1790287 = 2685431) B2685431
theorem B9687383 : Blo 1790096 9687383 := bstep (se 1 (by rfl) ⟨7265537, by rfl⟩ : syracuseStep 9687383 = 14531075) B14531075
theorem B1790303 : Blo 1790096 1790303 := bstep (se 1 (by rfl) ⟨1342727, by rfl⟩ : syracuseStep 1790303 = 2685455) B2685455
theorem B1790331 : Blo 1790096 1790331 := bstep (se 1 (by rfl) ⟨1342748, by rfl⟩ : syracuseStep 1790331 = 2685497) B2685497
theorem B1790383 : Blo 1790096 1790383 := bstep (se 1 (by rfl) ⟨1342787, by rfl⟩ : syracuseStep 1790383 = 2685575) B2685575
theorem B1790407 : Blo 1790096 1790407 := bstep (se 1 (by rfl) ⟨1342805, by rfl⟩ : syracuseStep 1790407 = 2685611) B2685611
theorem B1790427 : Blo 1790096 1790427 := bstep (se 1 (by rfl) ⟨1342820, by rfl⟩ : syracuseStep 1790427 = 2685641) B2685641
theorem B9818657 : Blo 1790096 9818657 := bstep (se 2 (by rfl) ⟨3681996, by rfl⟩ : syracuseStep 9818657 = 7363993) B7363993
theorem B1790503 : Blo 1790096 1790503 := bstep (se 1 (by rfl) ⟨1342877, by rfl⟩ : syracuseStep 1790503 = 2685755) B2685755
theorem B7647803 : Blo 1790096 7647803 := bstep (se 1 (by rfl) ⟨5735852, by rfl⟩ : syracuseStep 7647803 = 11471705) B11471705
theorem B1790543 : Blo 1790096 1790543 := bstep (se 1 (by rfl) ⟨1342907, by rfl⟩ : syracuseStep 1790543 = 2685815) B2685815
theorem B1790559 : Blo 1790096 1790559 := bstep (se 1 (by rfl) ⟨1342919, by rfl⟩ : syracuseStep 1790559 = 2685839) B2685839
theorem B1790587 : Blo 1790096 1790587 := bstep (se 1 (by rfl) ⟨1342940, by rfl⟩ : syracuseStep 1790587 = 2685881) B2685881
theorem B6804107 : Blo 1790096 6804107 := bstep (se 1 (by rfl) ⟨5103080, by rfl⟩ : syracuseStep 6804107 = 10206161) B10206161
theorem B1790639 : Blo 1790096 1790639 := bstep (se 1 (by rfl) ⟨1342979, by rfl⟩ : syracuseStep 1790639 = 2685959) B2685959
theorem B5100221 : Blo 1790096 5100221 := bstep (se 3 (by rfl) ⟨956291, by rfl⟩ : syracuseStep 5100221 = 1912583) B1912583
theorem B1790663 : Blo 1790096 1790663 := bstep (se 1 (by rfl) ⟨1342997, by rfl⟩ : syracuseStep 1790663 = 2685995) B2685995
theorem B3445459 : Blo 1790096 3445459 := bstep (se 1 (by rfl) ⟨2584094, by rfl⟩ : syracuseStep 3445459 = 5168189) B5168189
theorem B1790683 : Blo 1790096 1790683 := bstep (se 1 (by rfl) ⟨1343012, by rfl⟩ : syracuseStep 1790683 = 2686025) B2686025
theorem B1790759 : Blo 1790096 1790759 := bstep (se 1 (by rfl) ⟨1343069, by rfl⟩ : syracuseStep 1790759 = 2686139) B2686139
theorem B1790799 : Blo 1790096 1790799 := bstep (se 1 (by rfl) ⟨1343099, by rfl⟩ : syracuseStep 1790799 = 2686199) B2686199
theorem B1790815 : Blo 1790096 1790815 := bstep (se 1 (by rfl) ⟨1343111, by rfl⟩ : syracuseStep 1790815 = 2686223) B2686223
theorem B1790843 : Blo 1790096 1790843 := bstep (se 1 (by rfl) ⟨1343132, by rfl⟩ : syracuseStep 1790843 = 2686265) B2686265
theorem B6452129 : Blo 1790096 6452129 := bstep (se 2 (by rfl) ⟨2419548, by rfl⟩ : syracuseStep 6452129 = 4839097) B4839097
theorem B1790895 : Blo 1790096 1790895 := bstep (se 1 (by rfl) ⟨1343171, by rfl⟩ : syracuseStep 1790895 = 2686343) B2686343
theorem B1790919 : Blo 1790096 1790919 := bstep (se 1 (by rfl) ⟨1343189, by rfl⟩ : syracuseStep 1790919 = 2686379) B2686379
theorem B1790939 : Blo 1790096 1790939 := bstep (se 1 (by rfl) ⟨1343204, by rfl⟩ : syracuseStep 1790939 = 2686409) B2686409
theorem B5100563 : Blo 1790096 5100563 := bstep (se 1 (by rfl) ⟨3825422, by rfl⟩ : syracuseStep 5100563 = 7650845) B7650845
theorem B1791015 : Blo 1790096 1791015 := bstep (se 1 (by rfl) ⟨1343261, by rfl⟩ : syracuseStep 1791015 = 2686523) B2686523
theorem B20403251 : Blo 1790096 20403251 := bstep (se 1 (by rfl) ⟨15302438, by rfl⟩ : syracuseStep 20403251 = 30604877) B30604877
theorem B1791055 : Blo 1790096 1791055 := bstep (se 1 (by rfl) ⟨1343291, by rfl⟩ : syracuseStep 1791055 = 2686583) B2686583
theorem B1791071 : Blo 1790096 1791071 := bstep (se 1 (by rfl) ⟨1343303, by rfl⟩ : syracuseStep 1791071 = 2686607) B2686607
theorem B1791099 : Blo 1790096 1791099 := bstep (se 1 (by rfl) ⟨1343324, by rfl⟩ : syracuseStep 1791099 = 2686649) B2686649
theorem B5444765 : Blo 1790096 5444765 := bstep (se 3 (by rfl) ⟨1020893, by rfl⟩ : syracuseStep 5444765 = 2041787) B2041787
theorem B1791151 : Blo 1790096 1791151 := bstep (se 1 (by rfl) ⟨1343363, by rfl⟩ : syracuseStep 1791151 = 2686727) B2686727
theorem B1791175 : Blo 1790096 1791175 := bstep (se 1 (by rfl) ⟨1343381, by rfl⟩ : syracuseStep 1791175 = 2686763) B2686763
theorem B41915593 : Blo 1790096 41915593 := bstep (se 2 (by rfl) ⟨15718347, by rfl⟩ : syracuseStep 41915593 = 31436695) B31436695
theorem B1791195 : Blo 1790096 1791195 := bstep (se 1 (by rfl) ⟨1343396, by rfl⟩ : syracuseStep 1791195 = 2686793) B2686793
theorem B17216783 : Blo 1790096 17216783 := bstep (se 1 (by rfl) ⟨12912587, by rfl⟩ : syracuseStep 17216783 = 25825175) B25825175
theorem B13604111 : Blo 1790096 13604111 := bstep (se 1 (by rfl) ⟨10203083, by rfl⟩ : syracuseStep 13604111 = 20406167) B20406167
theorem B1791271 : Blo 1790096 1791271 := bstep (se 1 (by rfl) ⟨1343453, by rfl⟩ : syracuseStep 1791271 = 2686907) B2686907
theorem B1791311 : Blo 1790096 1791311 := bstep (se 1 (by rfl) ⟨1343483, by rfl⟩ : syracuseStep 1791311 = 2686967) B2686967
theorem B1791327 : Blo 1790096 1791327 := bstep (se 1 (by rfl) ⟨1343495, by rfl⟩ : syracuseStep 1791327 = 2686991) B2686991
theorem B7263593 : Blo 1790096 7263593 := bstep (se 2 (by rfl) ⟨2723847, by rfl⟩ : syracuseStep 7263593 = 5447695) B5447695
theorem B4142441 : Blo 1790096 4142441 := bstep (se 2 (by rfl) ⟨1553415, by rfl⟩ : syracuseStep 4142441 = 3106831) B3106831
theorem B1791355 : Blo 1790096 1791355 := bstep (se 1 (by rfl) ⟨1343516, by rfl⟩ : syracuseStep 1791355 = 2687033) B2687033
theorem B34895249 : Blo 1790096 34895249 := bstep (se 2 (by rfl) ⟨13085718, by rfl⟩ : syracuseStep 34895249 = 26171437) B26171437
theorem B1791407 : Blo 1790096 1791407 := bstep (se 1 (by rfl) ⟨1343555, by rfl⟩ : syracuseStep 1791407 = 2687111) B2687111
theorem B1791431 : Blo 1790096 1791431 := bstep (se 1 (by rfl) ⟨1343573, by rfl⟩ : syracuseStep 1791431 = 2687147) B2687147
theorem B14521801 : Blo 1790096 14521801 := bstep (se 2 (by rfl) ⟨5445675, by rfl⟩ : syracuseStep 14521801 = 10891351) B10891351
theorem B5101019 : Blo 1790096 5101019 := bstep (se 1 (by rfl) ⟨3825764, by rfl⟩ : syracuseStep 5101019 = 7651529) B7651529
theorem B1791451 : Blo 1790096 1791451 := bstep (se 1 (by rfl) ⟨1343588, by rfl⟩ : syracuseStep 1791451 = 2687177) B2687177
theorem B4027913 : Blo 1790096 4027913 := bstep (se 2 (by rfl) ⟨1510467, by rfl⟩ : syracuseStep 4027913 = 3020935) B3020935
theorem B1791527 : Blo 1790096 1791527 := bstep (se 1 (by rfl) ⟨1343645, by rfl⟩ : syracuseStep 1791527 = 2687291) B2687291
theorem B1791567 : Blo 1790096 1791567 := bstep (se 1 (by rfl) ⟨1343675, by rfl⟩ : syracuseStep 1791567 = 2687351) B2687351
theorem B1791583 : Blo 1790096 1791583 := bstep (se 1 (by rfl) ⟨1343687, by rfl⟩ : syracuseStep 1791583 = 2687375) B2687375
theorem B1791611 : Blo 1790096 1791611 := bstep (se 1 (by rfl) ⟨1343708, by rfl⟩ : syracuseStep 1791611 = 2687417) B2687417
theorem B1791663 : Blo 1790096 1791663 := bstep (se 1 (by rfl) ⟨1343747, by rfl⟩ : syracuseStep 1791663 = 2687495) B2687495
theorem B1791687 : Blo 1790096 1791687 := bstep (se 1 (by rfl) ⟨1343765, by rfl⟩ : syracuseStep 1791687 = 2687531) B2687531
theorem B1791707 : Blo 1790096 1791707 := bstep (se 1 (by rfl) ⟨1343780, by rfl⟩ : syracuseStep 1791707 = 2687561) B2687561
theorem B1791783 : Blo 1790096 1791783 := bstep (se 1 (by rfl) ⟨1343837, by rfl⟩ : syracuseStep 1791783 = 2687675) B2687675
theorem B1791823 : Blo 1790096 1791823 := bstep (se 1 (by rfl) ⟨1343867, by rfl⟩ : syracuseStep 1791823 = 2687735) B2687735
theorem B4028255 : Blo 1790096 4028255 := bstep (se 1 (by rfl) ⟨3021191, by rfl⟩ : syracuseStep 4028255 = 6042383) B6042383
theorem B1791839 : Blo 1790096 1791839 := bstep (se 1 (by rfl) ⟨1343879, by rfl⟩ : syracuseStep 1791839 = 2687759) B2687759
theorem B1791867 : Blo 1790096 1791867 := bstep (se 1 (by rfl) ⟨1343900, by rfl⟩ : syracuseStep 1791867 = 2687801) B2687801
theorem B1791919 : Blo 1790096 1791919 := bstep (se 1 (by rfl) ⟨1343939, by rfl⟩ : syracuseStep 1791919 = 2687879) B2687879
theorem B1791943 : Blo 1790096 1791943 := bstep (se 1 (by rfl) ⟨1343957, by rfl⟩ : syracuseStep 1791943 = 2687915) B2687915
theorem B1791963 : Blo 1790096 1791963 := bstep (se 1 (by rfl) ⟨1343972, by rfl⟩ : syracuseStep 1791963 = 2687945) B2687945
theorem B3020807 : Blo 1790096 3020807 := bstep (se 1 (by rfl) ⟨2265605, by rfl⟩ : syracuseStep 3020807 = 4531211) B4531211
theorem B4028435 : Blo 1790096 4028435 := bstep (se 1 (by rfl) ⟨3021326, by rfl⟩ : syracuseStep 4028435 = 6042653) B6042653
theorem B1792039 : Blo 1790096 1792039 := bstep (se 1 (by rfl) ⟨1344029, by rfl⟩ : syracuseStep 1792039 = 2688059) B2688059
theorem B1792079 : Blo 1790096 1792079 := bstep (se 1 (by rfl) ⟨1344059, by rfl⟩ : syracuseStep 1792079 = 2688119) B2688119
theorem B1792095 : Blo 1790096 1792095 := bstep (se 1 (by rfl) ⟨1344071, by rfl⟩ : syracuseStep 1792095 = 2688143) B2688143
theorem B6207641 : Blo 1790096 6207641 := bstep (se 2 (by rfl) ⟨2327865, by rfl⟩ : syracuseStep 6207641 = 4655731) B4655731
theorem B9066653 : Blo 1790096 9066653 := bstep (se 3 (by rfl) ⟨1699997, by rfl⟩ : syracuseStep 9066653 = 3399995) B3399995
theorem B6043895 : Blo 1790096 6043895 := bstep (se 1 (by rfl) ⟨4532921, by rfl⟩ : syracuseStep 6043895 = 9065843) B9065843
theorem B3021151 : Blo 1790096 3021151 := bstep (se 1 (by rfl) ⟨2265863, by rfl⟩ : syracuseStep 3021151 = 4531727) B4531727
theorem B4028777 : Blo 1790096 4028777 := bstep (se 2 (by rfl) ⟨1510791, by rfl⟩ : syracuseStep 4028777 = 3021583) B3021583
theorem B2685359 : Blo 1790096 2685359 := bstep (se 1 (by rfl) ⟨2014019, by rfl⟩ : syracuseStep 2685359 = 4028039) B4028039
theorem B3021239 : Blo 1790096 3021239 := bstep (se 1 (by rfl) ⟨2265929, by rfl⟩ : syracuseStep 3021239 = 4531859) B4531859
theorem B22952429 : Blo 1790096 22952429 := bstep (se 3 (by rfl) ⟨4303580, by rfl⟩ : syracuseStep 22952429 = 8607161) B8607161
theorem B2685449 : Blo 1790096 2685449 := bstep (se 2 (by rfl) ⟨1007043, by rfl⟩ : syracuseStep 2685449 = 2014087) B2014087
theorem B5741081 : Blo 1790096 5741081 := bstep (se 2 (by rfl) ⟨2152905, by rfl⟩ : syracuseStep 5741081 = 4305811) B4305811
theorem B2685479 : Blo 1790096 2685479 := bstep (se 1 (by rfl) ⟨2014109, by rfl⟩ : syracuseStep 2685479 = 4028219) B4028219
theorem B3824167 : Blo 1790096 3824167 := bstep (se 1 (by rfl) ⟨2868125, by rfl⟩ : syracuseStep 3824167 = 5736251) B5736251
theorem B6044219 : Blo 1790096 6044219 := bstep (se 1 (by rfl) ⟨4533164, by rfl⟩ : syracuseStep 6044219 = 9066329) B9066329
theorem B2685563 : Blo 1790096 2685563 := bstep (se 1 (by rfl) ⟨2014172, by rfl⟩ : syracuseStep 2685563 = 4028345) B4028345
theorem B5102203 : Blo 1790096 5102203 := bstep (se 1 (by rfl) ⟨3826652, by rfl⟩ : syracuseStep 5102203 = 7653305) B7653305
theorem B2685689 : Blo 1790096 2685689 := bstep (se 2 (by rfl) ⟨1007133, by rfl⟩ : syracuseStep 2685689 = 2014267) B2014267
theorem B6044489 : Blo 1790096 6044489 := bstep (se 2 (by rfl) ⟨2266683, by rfl⟩ : syracuseStep 6044489 = 4533367) B4533367
theorem B2685791 : Blo 1790096 2685791 := bstep (se 1 (by rfl) ⟨2014343, by rfl⟩ : syracuseStep 2685791 = 4028687) B4028687
theorem B3398507 : Blo 1790096 3398507 := bstep (se 1 (by rfl) ⟨2548880, by rfl⟩ : syracuseStep 3398507 = 5097761) B5097761
theorem B2685803 : Blo 1790096 2685803 := bstep (se 1 (by rfl) ⟨2014352, by rfl⟩ : syracuseStep 2685803 = 4028705) B4028705
theorem B11475857 : Blo 1790096 11475857 := bstep (se 2 (by rfl) ⟨4303446, by rfl⟩ : syracuseStep 11475857 = 8606893) B8606893
theorem B4029371 : Blo 1790096 4029371 := bstep (se 1 (by rfl) ⟨3022028, by rfl⟩ : syracuseStep 4029371 = 6044057) B6044057
theorem B3021833 : Blo 1790096 3021833 := bstep (se 2 (by rfl) ⟨1133187, by rfl⟩ : syracuseStep 3021833 = 2266375) B2266375
theorem B33135659 : Blo 1790096 33135659 := bstep (se 1 (by rfl) ⟨24851744, by rfl⟩ : syracuseStep 33135659 = 49703489) B49703489
theorem B4029497 : Blo 1790096 4029497 := bstep (se 2 (by rfl) ⟨1511061, by rfl⟩ : syracuseStep 4029497 = 3022123) B3022123
theorem B3398735 : Blo 1790096 3398735 := bstep (se 1 (by rfl) ⟨2549051, by rfl⟩ : syracuseStep 3398735 = 5098103) B5098103
theorem B2686031 : Blo 1790096 2686031 := bstep (se 1 (by rfl) ⟨2014523, by rfl⟩ : syracuseStep 2686031 = 4029047) B4029047
theorem B3021995 : Blo 1790096 3021995 := bstep (se 1 (by rfl) ⟨2266496, by rfl⟩ : syracuseStep 3021995 = 4532993) B4532993
theorem B2686151 : Blo 1790096 2686151 := bstep (se 1 (by rfl) ⟨2014613, by rfl⟩ : syracuseStep 2686151 = 4029227) B4029227
theorem B2686313 : Blo 1790096 2686313 := bstep (se 2 (by rfl) ⟨1007367, by rfl⟩ : syracuseStep 2686313 = 2014735) B2014735
theorem B3226987 : Blo 1790096 3226987 := bstep (se 1 (by rfl) ⟨2420240, by rfl⟩ : syracuseStep 3226987 = 4840481) B4840481
theorem B4029839 : Blo 1790096 4029839 := bstep (se 1 (by rfl) ⟨3022379, by rfl⟩ : syracuseStep 4029839 = 6044759) B6044759
theorem B9067949 : Blo 1790096 9067949 := bstep (se 3 (by rfl) ⟨1700240, by rfl⟩ : syracuseStep 9067949 = 3400481) B3400481
theorem B2686391 : Blo 1790096 2686391 := bstep (se 1 (by rfl) ⟨2014793, by rfl⟩ : syracuseStep 2686391 = 4029587) B4029587
theorem B2686427 : Blo 1790096 2686427 := bstep (se 1 (by rfl) ⟨2014820, by rfl⟩ : syracuseStep 2686427 = 4029641) B4029641
theorem B5103091 : Blo 1790096 5103091 := bstep (se 1 (by rfl) ⟨3827318, by rfl⟩ : syracuseStep 5103091 = 7654637) B7654637
theorem B3399175 : Blo 1790096 3399175 := bstep (se 1 (by rfl) ⟨2549381, by rfl⟩ : syracuseStep 3399175 = 5098763) B5098763
theorem B3022393 : Blo 1790096 3022393 := bstep (se 2 (by rfl) ⟨1133397, by rfl⟩ : syracuseStep 3022393 = 2266795) B2266795
theorem B2014843 : Blo 1790096 2014843 := bstep (se 1 (by rfl) ⟨1511132, by rfl⟩ : syracuseStep 2014843 = 3022265) B3022265
theorem B3022535 : Blo 1790096 3022535 := bstep (se 1 (by rfl) ⟨2266901, by rfl⟩ : syracuseStep 3022535 = 4533803) B4533803
theorem B4030163 : Blo 1790096 4030163 := bstep (se 1 (by rfl) ⟨3022622, by rfl⟩ : syracuseStep 4030163 = 6045245) B6045245
theorem B3022697 : Blo 1790096 3022697 := bstep (se 2 (by rfl) ⟨1133511, by rfl⟩ : syracuseStep 3022697 = 2267023) B2267023
theorem B19365767 : Blo 1790096 19365767 := bstep (se 1 (by rfl) ⟨14524325, by rfl⟩ : syracuseStep 19365767 = 29048651) B29048651
theorem B2686895 : Blo 1790096 2686895 := bstep (se 1 (by rfl) ⟨2015171, by rfl⟩ : syracuseStep 2686895 = 4030343) B4030343
theorem B6045623 : Blo 1790096 6045623 := bstep (se 1 (by rfl) ⟨4534217, by rfl⟩ : syracuseStep 6045623 = 9068435) B9068435
theorem B279281677 : Blo 1790096 279281677 := bstep (se 3 (by rfl) ⟨52365314, by rfl⟩ : syracuseStep 279281677 = 104730629) B104730629
theorem B11477011 : Blo 1790096 11477011 := bstep (se 1 (by rfl) ⟨8607758, by rfl⟩ : syracuseStep 11477011 = 17215517) B17215517
theorem B2687081 : Blo 1790096 2687081 := bstep (se 2 (by rfl) ⟨1007655, by rfl⟩ : syracuseStep 2687081 = 2015311) B2015311
theorem B2867465 : Blo 1790096 2867465 := bstep (se 2 (by rfl) ⟨1075299, by rfl⟩ : syracuseStep 2867465 = 2150599) B2150599
theorem B2015527 : Blo 1790096 2015527 := bstep (se 1 (by rfl) ⟨1511645, by rfl⟩ : syracuseStep 2015527 = 3023291) B3023291
theorem B4030793 : Blo 1790096 4030793 := bstep (se 2 (by rfl) ⟨1511547, by rfl⟩ : syracuseStep 4030793 = 3023095) B3023095
theorem B4030811 : Blo 1790096 4030811 := bstep (se 1 (by rfl) ⟨3023108, by rfl⟩ : syracuseStep 4030811 = 6046217) B6046217
theorem B6545771 : Blo 1790096 6545771 := bstep (se 1 (by rfl) ⟨4909328, by rfl⟩ : syracuseStep 6545771 = 9818657) B9818657
theorem B2867567 : Blo 1790096 2867567 := bstep (se 1 (by rfl) ⟨2150675, by rfl⟩ : syracuseStep 2867567 = 4301351) B4301351
theorem B2015599 : Blo 1790096 2015599 := bstep (se 1 (by rfl) ⟨1511699, by rfl⟩ : syracuseStep 2015599 = 3023399) B3023399
theorem B2687399 : Blo 1790096 2687399 := bstep (se 1 (by rfl) ⟨2015549, by rfl⟩ : syracuseStep 2687399 = 4031099) B4031099
theorem B7758281 : Blo 1790096 7758281 := bstep (se 2 (by rfl) ⟨2909355, by rfl⟩ : syracuseStep 7758281 = 5818711) B5818711
theorem B3400147 : Blo 1790096 3400147 := bstep (se 1 (by rfl) ⟨2550110, by rfl⟩ : syracuseStep 3400147 = 5100221) B5100221
theorem B2687483 : Blo 1790096 2687483 := bstep (se 1 (by rfl) ⟨2015612, by rfl⟩ : syracuseStep 2687483 = 4031225) B4031225
theorem B2015815 : Blo 1790096 2015815 := bstep (se 1 (by rfl) ⟨1511861, by rfl⟩ : syracuseStep 2015815 = 3023723) B3023723
theorem B4301419 : Blo 1790096 4301419 := bstep (se 1 (by rfl) ⟨3226064, by rfl⟩ : syracuseStep 4301419 = 6452129) B6452129
theorem B5735033 : Blo 1790096 5735033 := bstep (se 2 (by rfl) ⟨2150637, by rfl⟩ : syracuseStep 5735033 = 4301275) B4301275
theorem B2687609 : Blo 1790096 2687609 := bstep (se 2 (by rfl) ⟨1007853, by rfl⟩ : syracuseStep 2687609 = 2015707) B2015707
theorem B6046379 : Blo 1790096 6046379 := bstep (se 1 (by rfl) ⟨4534784, by rfl⟩ : syracuseStep 6046379 = 9069569) B9069569
theorem B2687663 : Blo 1790096 2687663 := bstep (se 1 (by rfl) ⟨2015747, by rfl⟩ : syracuseStep 2687663 = 4031495) B4031495
theorem B3400375 : Blo 1790096 3400375 := bstep (se 1 (by rfl) ⟨2550281, by rfl⟩ : syracuseStep 3400375 = 5100563) B5100563
theorem B2687711 : Blo 1790096 2687711 := bstep (se 1 (by rfl) ⟨2015783, by rfl⟩ : syracuseStep 2687711 = 4031567) B4031567
theorem B3629843 : Blo 1790096 3629843 := bstep (se 1 (by rfl) ⟨2722382, by rfl⟩ : syracuseStep 3629843 = 5444765) B5444765
theorem B11477855 : Blo 1790096 11477855 := bstep (se 1 (by rfl) ⟨8608391, by rfl⟩ : syracuseStep 11477855 = 17216783) B17216783
theorem B9069407 : Blo 1790096 9069407 := bstep (se 1 (by rfl) ⟨6802055, by rfl⟩ : syracuseStep 9069407 = 13604111) B13604111
theorem B4842395 : Blo 1790096 4842395 := bstep (se 1 (by rfl) ⟨3631796, by rfl⟩ : syracuseStep 4842395 = 7263593) B7263593
theorem B4031387 : Blo 1790096 4031387 := bstep (se 1 (by rfl) ⟨3023540, by rfl⟩ : syracuseStep 4031387 = 6047081) B6047081
theorem B2761627 : Blo 1790096 2761627 := bstep (se 1 (by rfl) ⟨2071220, by rfl⟩ : syracuseStep 2761627 = 4142441) B4142441
theorem B3400679 : Blo 1790096 3400679 := bstep (se 1 (by rfl) ⟨2550509, by rfl⟩ : syracuseStep 3400679 = 5101019) B5101019
theorem B2687975 : Blo 1790096 2687975 := bstep (se 1 (by rfl) ⟨2015981, by rfl⟩ : syracuseStep 2687975 = 4031963) B4031963
theorem B21791747 : Blo 1790096 21791747 := bstep (se 1 (by rfl) ⟨16343810, by rfl⟩ : syracuseStep 21791747 = 32687621) B32687621
theorem B4031585 : Blo 1790096 4031585 := bstep (se 2 (by rfl) ⟨1511844, by rfl⟩ : syracuseStep 4031585 = 3023689) B3023689
theorem B6046919 : Blo 1790096 6046919 := bstep (se 1 (by rfl) ⟨4535189, by rfl⟩ : syracuseStep 6046919 = 9070379) B9070379
theorem B3400937 : Blo 1790096 3400937 := bstep (se 2 (by rfl) ⟨1275351, by rfl⟩ : syracuseStep 3400937 = 2550703) B2550703
theorem B4031783 : Blo 1790096 4031783 := bstep (se 1 (by rfl) ⟨3023837, by rfl⟩ : syracuseStep 4031783 = 6047675) B6047675
theorem B15304079 : Blo 1790096 15304079 := bstep (se 1 (by rfl) ⟨11478059, by rfl⟩ : syracuseStep 15304079 = 22956119) B22956119
theorem B4138427 : Blo 1790096 4138427 := bstep (se 1 (by rfl) ⟨3103820, by rfl⟩ : syracuseStep 4138427 = 6207641) B6207641
theorem B12912185 : Blo 1790096 12912185 := bstep (se 2 (by rfl) ⟨4842069, by rfl⟩ : syracuseStep 12912185 = 9684139) B9684139
theorem B21784153 : Blo 1790096 21784153 := bstep (se 2 (by rfl) ⟨8169057, by rfl⟩ : syracuseStep 21784153 = 16338115) B16338115
theorem B55887457 : Blo 1790096 55887457 := bstep (se 2 (by rfl) ⟨20957796, by rfl⟩ : syracuseStep 55887457 = 41915593) B41915593
theorem B4032161 : Blo 1790096 4032161 := bstep (se 2 (by rfl) ⟨1512060, by rfl⟩ : syracuseStep 4032161 = 3024121) B3024121
theorem B3827387 : Blo 1790096 3827387 := bstep (se 1 (by rfl) ⟨2870540, by rfl⟩ : syracuseStep 3827387 = 5741081) B5741081
theorem B4302649 : Blo 1790096 4302649 := bstep (se 2 (by rfl) ⟨1613493, by rfl⟩ : syracuseStep 4302649 = 3226987) B3226987
theorem B4532233 : Blo 1790096 4532233 := bstep (se 2 (by rfl) ⟨1699587, by rfl⟩ : syracuseStep 4532233 = 3399175) B3399175
theorem B3401833 : Blo 1790096 3401833 := bstep (se 2 (by rfl) ⟨1275687, by rfl⟩ : syracuseStep 3401833 = 2551375) B2551375
theorem B16345273 : Blo 1790096 16345273 := bstep (se 2 (by rfl) ⟨6129477, by rfl⟩ : syracuseStep 16345273 = 12258955) B12258955
theorem B3401993 : Blo 1790096 3401993 := bstep (se 2 (by rfl) ⟨1275747, by rfl⟩ : syracuseStep 3401993 = 2551495) B2551495
theorem B22940333 : Blo 1790096 22940333 := bstep (se 3 (by rfl) ⟨4301312, by rfl⟩ : syracuseStep 22940333 = 8602625) B8602625
theorem B15297245 : Blo 1790096 15297245 := bstep (se 3 (by rfl) ⟨2868233, by rfl⟩ : syracuseStep 15297245 = 5736467) B5736467
theorem B12905207 : Blo 1790096 12905207 := bstep (se 1 (by rfl) ⟨9678905, by rfl⟩ : syracuseStep 12905207 = 19357811) B19357811
theorem B9071351 : Blo 1790096 9071351 := bstep (se 1 (by rfl) ⟨6803513, by rfl⟩ : syracuseStep 9071351 = 13607027) B13607027
theorem B4655951 : Blo 1790096 4655951 := bstep (se 1 (by rfl) ⟨3491963, by rfl⟩ : syracuseStep 4655951 = 6983927) B6983927
theorem B6458255 : Blo 1790096 6458255 := bstep (se 1 (by rfl) ⟨4843691, by rfl⟩ : syracuseStep 6458255 = 9687383) B9687383
theorem B5098535 : Blo 1790096 5098535 := bstep (se 1 (by rfl) ⟨3823901, by rfl⟩ : syracuseStep 5098535 = 7647803) B7647803
theorem B13266035 : Blo 1790096 13266035 := bstep (se 1 (by rfl) ⟨9949526, by rfl⟩ : syracuseStep 13266035 = 19899053) B19899053
theorem B9071837 : Blo 1790096 9071837 := bstep (se 3 (by rfl) ⟨1700969, by rfl⟩ : syracuseStep 9071837 = 3401939) B3401939
theorem B13602167 : Blo 1790096 13602167 := bstep (se 1 (by rfl) ⟨10201625, by rfl⟩ : syracuseStep 13602167 = 20403251) B20403251
theorem B5098889 : Blo 1790096 5098889 := bstep (se 2 (by rfl) ⟨1912083, by rfl⟩ : syracuseStep 5098889 = 3824167) B3824167
theorem B4533641 : Blo 1790096 4533641 := bstep (se 2 (by rfl) ⟨1700115, by rfl⟩ : syracuseStep 4533641 = 3400231) B3400231
theorem B4533691 : Blo 1790096 4533691 := bstep (se 1 (by rfl) ⟨3400268, by rfl⟩ : syracuseStep 4533691 = 6800537) B6800537
theorem B6802937 : Blo 1790096 6802937 := bstep (se 2 (by rfl) ⟨2551101, by rfl⟩ : syracuseStep 6802937 = 5102203) B5102203
theorem B19361443 : Blo 1790096 19361443 := bstep (se 1 (by rfl) ⟨14521082, by rfl⟩ : syracuseStep 19361443 = 29042165) B29042165
theorem B4533995 : Blo 1790096 4533995 := bstep (se 1 (by rfl) ⟨3400496, by rfl⟩ : syracuseStep 4533995 = 6800993) B6800993
theorem B68890499 : Blo 1790096 68890499 := bstep (se 1 (by rfl) ⟨51667874, by rfl⟩ : syracuseStep 68890499 = 103335749) B103335749
theorem B14528477 : Blo 1790096 14528477 := bstep (se 3 (by rfl) ⟨2724089, by rfl⟩ : syracuseStep 14528477 = 5448179) B5448179
theorem B55177487 : Blo 1790096 55177487 := bstep (se 1 (by rfl) ⟨41383115, by rfl⟩ : syracuseStep 55177487 = 82766231) B82766231
theorem B1790239 : Blo 1790096 1790239 := bstep (se 1 (by rfl) ⟨1342679, by rfl⟩ : syracuseStep 1790239 = 2685359) B2685359
theorem B5738825 : Blo 1790096 5738825 := bstep (se 2 (by rfl) ⟨2152059, by rfl⟩ : syracuseStep 5738825 = 4304119) B4304119
theorem B1790299 : Blo 1790096 1790299 := bstep (se 1 (by rfl) ⟨1342724, by rfl⟩ : syracuseStep 1790299 = 2685449) B2685449
theorem B1790319 : Blo 1790096 1790319 := bstep (se 1 (by rfl) ⟨1342739, by rfl⟩ : syracuseStep 1790319 = 2685479) B2685479
theorem B73503125 : Blo 1790096 73503125 := bstep (se 6 (by rfl) ⟨1722729, by rfl⟩ : syracuseStep 73503125 = 3445459) B3445459
theorem B1790375 : Blo 1790096 1790375 := bstep (se 1 (by rfl) ⟨1342781, by rfl⟩ : syracuseStep 1790375 = 2685563) B2685563
theorem B1790459 : Blo 1790096 1790459 := bstep (se 1 (by rfl) ⟨1342844, by rfl⟩ : syracuseStep 1790459 = 2685689) B2685689
theorem B6042113 : Blo 1790096 6042113 := bstep (se 2 (by rfl) ⟨2265792, by rfl⟩ : syracuseStep 6042113 = 4531585) B4531585
theorem B1790527 : Blo 1790096 1790527 := bstep (se 1 (by rfl) ⟨1342895, by rfl⟩ : syracuseStep 1790527 = 2685791) B2685791
theorem B2265671 : Blo 1790096 2265671 := bstep (se 1 (by rfl) ⟨1699253, by rfl⟩ : syracuseStep 2265671 = 3398507) B3398507
theorem B1790535 : Blo 1790096 1790535 := bstep (se 1 (by rfl) ⟨1342901, by rfl⟩ : syracuseStep 1790535 = 2685803) B2685803
theorem B19362401 : Blo 1790096 19362401 := bstep (se 2 (by rfl) ⟨7260900, by rfl⟩ : syracuseStep 19362401 = 14521801) B14521801
theorem B6804121 : Blo 1790096 6804121 := bstep (se 2 (by rfl) ⟨2551545, by rfl⟩ : syracuseStep 6804121 = 5103091) B5103091
theorem B4534967 : Blo 1790096 4534967 := bstep (se 1 (by rfl) ⟨3401225, by rfl⟩ : syracuseStep 4534967 = 6802451) B6802451
theorem B22090439 : Blo 1790096 22090439 := bstep (se 1 (by rfl) ⟨16567829, by rfl⟩ : syracuseStep 22090439 = 33135659) B33135659
theorem B2265823 : Blo 1790096 2265823 := bstep (se 1 (by rfl) ⟨1699367, by rfl⟩ : syracuseStep 2265823 = 3398735) B3398735
theorem B1790687 : Blo 1790096 1790687 := bstep (se 1 (by rfl) ⟨1343015, by rfl⟩ : syracuseStep 1790687 = 2686031) B2686031
theorem B1790767 : Blo 1790096 1790767 := bstep (se 1 (by rfl) ⟨1343075, by rfl⟩ : syracuseStep 1790767 = 2686151) B2686151
theorem B1790875 : Blo 1790096 1790875 := bstep (se 1 (by rfl) ⟨1343156, by rfl⟩ : syracuseStep 1790875 = 2686313) B2686313
theorem B1790927 : Blo 1790096 1790927 := bstep (se 1 (by rfl) ⟨1343195, by rfl⟩ : syracuseStep 1790927 = 2686391) B2686391
theorem B6042599 : Blo 1790096 6042599 := bstep (se 1 (by rfl) ⟨4531949, by rfl⟩ : syracuseStep 6042599 = 9063899) B9063899
theorem B1790951 : Blo 1790096 1790951 := bstep (se 1 (by rfl) ⟨1343213, by rfl⟩ : syracuseStep 1790951 = 2686427) B2686427
theorem B1791263 : Blo 1790096 1791263 := bstep (se 1 (by rfl) ⟨1343447, by rfl⟩ : syracuseStep 1791263 = 2686895) B2686895
theorem B6042923 : Blo 1790096 6042923 := bstep (se 1 (by rfl) ⟨4532192, by rfl⟩ : syracuseStep 6042923 = 9064385) B9064385
theorem B1791323 : Blo 1790096 1791323 := bstep (se 1 (by rfl) ⟨1343492, by rfl⟩ : syracuseStep 1791323 = 2686985) B2686985
theorem B7648607 : Blo 1790096 7648607 := bstep (se 1 (by rfl) ⟨5736455, by rfl⟩ : syracuseStep 7648607 = 11472911) B11472911
theorem B10892639 : Blo 1790096 10892639 := bstep (se 1 (by rfl) ⟨8169479, by rfl⟩ : syracuseStep 10892639 = 16338959) B16338959
theorem B1791343 : Blo 1790096 1791343 := bstep (se 1 (by rfl) ⟨1343507, by rfl⟩ : syracuseStep 1791343 = 2687015) B2687015
theorem B6894971 : Blo 1790096 6894971 := bstep (se 1 (by rfl) ⟨5171228, by rfl⟩ : syracuseStep 6894971 = 10342457) B10342457
theorem B3446153 : Blo 1790096 3446153 := bstep (se 2 (by rfl) ⟨1292307, by rfl⟩ : syracuseStep 3446153 = 2584615) B2584615
theorem B19355041 : Blo 1790096 19355041 := bstep (se 2 (by rfl) ⟨7258140, by rfl⟩ : syracuseStep 19355041 = 14516281) B14516281
theorem B9811361 : Blo 1790096 9811361 := bstep (se 2 (by rfl) ⟨3679260, by rfl⟩ : syracuseStep 9811361 = 7358521) B7358521
theorem B1791399 : Blo 1790096 1791399 := bstep (se 1 (by rfl) ⟨1343549, by rfl⟩ : syracuseStep 1791399 = 2687099) B2687099
theorem B11474369 : Blo 1790096 11474369 := bstep (se 2 (by rfl) ⟨4302888, by rfl⟩ : syracuseStep 11474369 = 8605777) B8605777
theorem B1791483 : Blo 1790096 1791483 := bstep (se 1 (by rfl) ⟨1343612, by rfl⟩ : syracuseStep 1791483 = 2687225) B2687225
theorem B6043193 : Blo 1790096 6043193 := bstep (se 2 (by rfl) ⟨2266197, by rfl⟩ : syracuseStep 6043193 = 4532395) B4532395
theorem B1791551 : Blo 1790096 1791551 := bstep (se 1 (by rfl) ⟨1343663, by rfl⟩ : syracuseStep 1791551 = 2687327) B2687327
theorem B1791559 : Blo 1790096 1791559 := bstep (se 1 (by rfl) ⟨1343669, by rfl⟩ : syracuseStep 1791559 = 2687339) B2687339
theorem B1791711 : Blo 1790096 1791711 := bstep (se 1 (by rfl) ⟨1343783, by rfl⟩ : syracuseStep 1791711 = 2687567) B2687567
theorem B3446507 : Blo 1790096 3446507 := bstep (se 1 (by rfl) ⟨2584880, by rfl⟩ : syracuseStep 3446507 = 5169761) B5169761
theorem B4536071 : Blo 1790096 4536071 := bstep (se 1 (by rfl) ⟨3402053, by rfl⟩ : syracuseStep 4536071 = 6804107) B6804107
theorem B4028201 : Blo 1790096 4028201 := bstep (se 2 (by rfl) ⟨1510575, by rfl⟩ : syracuseStep 4028201 = 3021151) B3021151
theorem B4593455 : Blo 1790096 4593455 := bstep (se 1 (by rfl) ⟨3445091, by rfl⟩ : syracuseStep 4593455 = 6890183) B6890183
theorem B1791791 : Blo 1790096 1791791 := bstep (se 1 (by rfl) ⟨1343843, by rfl⟩ : syracuseStep 1791791 = 2687687) B2687687
theorem B4536121 : Blo 1790096 4536121 := bstep (se 2 (by rfl) ⟨1701045, by rfl⟩ : syracuseStep 4536121 = 3402091) B3402091
theorem B1791899 : Blo 1790096 1791899 := bstep (se 1 (by rfl) ⟨1343924, by rfl⟩ : syracuseStep 1791899 = 2687849) B2687849
theorem B20395961 : Blo 1790096 20395961 := bstep (se 2 (by rfl) ⟨7648485, by rfl⟩ : syracuseStep 20395961 = 15296971) B15296971
theorem B1791951 : Blo 1790096 1791951 := bstep (se 1 (by rfl) ⟨1343963, by rfl⟩ : syracuseStep 1791951 = 2687927) B2687927
theorem B1791975 : Blo 1790096 1791975 := bstep (se 1 (by rfl) ⟨1343981, by rfl⟩ : syracuseStep 1791975 = 2687963) B2687963
theorem B23263499 : Blo 1790096 23263499 := bstep (se 1 (by rfl) ⟨17447624, by rfl⟩ : syracuseStep 23263499 = 34895249) B34895249
theorem B2685275 : Blo 1790096 2685275 := bstep (se 1 (by rfl) ⟨2013956, by rfl⟩ : syracuseStep 2685275 = 4027913) B4027913
theorem B2685503 : Blo 1790096 2685503 := bstep (se 1 (by rfl) ⟨2014127, by rfl⟩ : syracuseStep 2685503 = 4028255) B4028255
theorem B2013871 : Blo 1790096 2013871 := bstep (se 1 (by rfl) ⟨1510403, by rfl⟩ : syracuseStep 2013871 = 3020807) B3020807
theorem B2685623 : Blo 1790096 2685623 := bstep (se 1 (by rfl) ⟨2014217, by rfl⟩ : syracuseStep 2685623 = 4028435) B4028435
theorem B6044435 : Blo 1790096 6044435 := bstep (se 1 (by rfl) ⟨4533326, by rfl⟩ : syracuseStep 6044435 = 9066653) B9066653
theorem B4029263 : Blo 1790096 4029263 := bstep (se 1 (by rfl) ⟨3021947, by rfl⟩ : syracuseStep 4029263 = 6043895) B6043895
theorem B2685851 : Blo 1790096 2685851 := bstep (se 1 (by rfl) ⟨2014388, by rfl⟩ : syracuseStep 2685851 = 4028777) B4028777
theorem B2014159 : Blo 1790096 2014159 := bstep (se 1 (by rfl) ⟨1510619, by rfl⟩ : syracuseStep 2014159 = 3021239) B3021239
theorem B3021799 : Blo 1790096 3021799 := bstep (se 1 (by rfl) ⟨2266349, by rfl⟩ : syracuseStep 3021799 = 4532699) B4532699
theorem B15301619 : Blo 1790096 15301619 := bstep (se 1 (by rfl) ⟨11476214, by rfl⟩ : syracuseStep 15301619 = 22952429) B22952429
theorem B4029479 : Blo 1790096 4029479 := bstep (se 1 (by rfl) ⟨3022109, by rfl⟩ : syracuseStep 4029479 = 6044219) B6044219
theorem B4029659 : Blo 1790096 4029659 := bstep (se 1 (by rfl) ⟨3022244, by rfl⟩ : syracuseStep 4029659 = 6044489) B6044489
theorem B7650571 : Blo 1790096 7650571 := bstep (se 1 (by rfl) ⟨5737928, by rfl⟩ : syracuseStep 7650571 = 11475857) B11475857
theorem B9067787 : Blo 1790096 9067787 := bstep (se 1 (by rfl) ⟨6800840, by rfl⟩ : syracuseStep 9067787 = 13601681) B13601681
theorem B4906271 : Blo 1790096 4906271 := bstep (se 1 (by rfl) ⟨3679703, by rfl⟩ : syracuseStep 4906271 = 7359407) B7359407
theorem B2686247 : Blo 1790096 2686247 := bstep (se 1 (by rfl) ⟨2014685, by rfl⟩ : syracuseStep 2686247 = 4029371) B4029371
theorem B2014555 : Blo 1790096 2014555 := bstep (se 1 (by rfl) ⟨1510916, by rfl⟩ : syracuseStep 2014555 = 3021833) B3021833
theorem B2686331 : Blo 1790096 2686331 := bstep (se 1 (by rfl) ⟨2014748, by rfl⟩ : syracuseStep 2686331 = 4029497) B4029497
theorem B4029857 : Blo 1790096 4029857 := bstep (se 2 (by rfl) ⟨1511196, by rfl⟩ : syracuseStep 4029857 = 3022393) B3022393
theorem B2014663 : Blo 1790096 2014663 := bstep (se 1 (by rfl) ⟨1510997, by rfl⟩ : syracuseStep 2014663 = 3021995) B3021995
theorem B2686457 : Blo 1790096 2686457 := bstep (se 2 (by rfl) ⟨1007421, by rfl⟩ : syracuseStep 2686457 = 2014843) B2014843
theorem B2686559 : Blo 1790096 2686559 := bstep (se 1 (by rfl) ⟨2014919, by rfl⟩ : syracuseStep 2686559 = 4029839) B4029839
theorem B6045299 : Blo 1790096 6045299 := bstep (se 1 (by rfl) ⟨4533974, by rfl⟩ : syracuseStep 6045299 = 9067949) B9067949
theorem B3399403 : Blo 1790096 3399403 := bstep (se 1 (by rfl) ⟨2549552, by rfl⟩ : syracuseStep 3399403 = 5099105) B5099105
theorem B2015023 : Blo 1790096 2015023 := bstep (se 1 (by rfl) ⟨1511267, by rfl⟩ : syracuseStep 2015023 = 3022535) B3022535
theorem B3399479 : Blo 1790096 3399479 := bstep (se 1 (by rfl) ⟨2549609, by rfl⟩ : syracuseStep 3399479 = 5099219) B5099219
theorem B2686775 : Blo 1790096 2686775 := bstep (se 1 (by rfl) ⟨2015081, by rfl⟩ : syracuseStep 2686775 = 4030163) B4030163
theorem B6045569 : Blo 1790096 6045569 := bstep (se 2 (by rfl) ⟨2267088, by rfl⟩ : syracuseStep 6045569 = 4534177) B4534177
theorem B2015131 : Blo 1790096 2015131 := bstep (se 1 (by rfl) ⟨1511348, by rfl⟩ : syracuseStep 2015131 = 3022697) B3022697
theorem B6799261 : Blo 1790096 6799261 := bstep (se 3 (by rfl) ⟨1274861, by rfl⟩ : syracuseStep 6799261 = 2549723) B2549723
theorem B25173935 : Blo 1790096 25173935 := bstep (se 1 (by rfl) ⟨18880451, by rfl⟩ : syracuseStep 25173935 = 37760903) B37760903
theorem B12910511 : Blo 1790096 12910511 := bstep (se 1 (by rfl) ⟨9682883, by rfl⟩ : syracuseStep 12910511 = 19365767) B19365767
theorem B4030415 : Blo 1790096 4030415 := bstep (se 1 (by rfl) ⟨3022811, by rfl⟩ : syracuseStep 4030415 = 6045623) B6045623
theorem B372375569 : Blo 1790096 372375569 := bstep (se 2 (by rfl) ⟨139640838, by rfl⟩ : syracuseStep 372375569 = 279281677) B279281677
theorem B15302681 : Blo 1790096 15302681 := bstep (se 2 (by rfl) ⟨5738505, by rfl⟩ : syracuseStep 15302681 = 11477011) B11477011
theorem B3825883 : Blo 1790096 3825883 := bstep (se 1 (by rfl) ⟨2869412, by rfl⟩ : syracuseStep 3825883 = 5738825) B5738825
theorem B2687195 : Blo 1790096 2687195 := bstep (se 1 (by rfl) ⟨2015396, by rfl⟩ : syracuseStep 2687195 = 4030793) B4030793
theorem B2687207 : Blo 1790096 2687207 := bstep (se 1 (by rfl) ⟨2015405, by rfl⟩ : syracuseStep 2687207 = 4030811) B4030811
theorem B2687369 : Blo 1790096 2687369 := bstep (se 2 (by rfl) ⟨1007763, by rfl⟩ : syracuseStep 2687369 = 2015527) B2015527
theorem B4030919 : Blo 1790096 4030919 := bstep (se 1 (by rfl) ⟨3023189, by rfl⟩ : syracuseStep 4030919 = 6046379) B6046379
theorem B3023311 : Blo 1790096 3023311 := bstep (se 1 (by rfl) ⟨2267483, by rfl⟩ : syracuseStep 3023311 = 4534967) B4534967
theorem B2687465 : Blo 1790096 2687465 := bstep (se 2 (by rfl) ⟨1007799, by rfl⟩ : syracuseStep 2687465 = 2015599) B2015599
theorem B7651903 : Blo 1790096 7651903 := bstep (se 1 (by rfl) ⟨5738927, by rfl⟩ : syracuseStep 7651903 = 11477855) B11477855
theorem B6046271 : Blo 1790096 6046271 := bstep (se 1 (by rfl) ⟨4534703, by rfl⟩ : syracuseStep 6046271 = 9069407) B9069407
theorem B3228263 : Blo 1790096 3228263 := bstep (se 1 (by rfl) ⟨2421197, by rfl⟩ : syracuseStep 3228263 = 4842395) B4842395
theorem B2687591 : Blo 1790096 2687591 := bstep (se 1 (by rfl) ⟨2015693, by rfl⟩ : syracuseStep 2687591 = 4031387) B4031387
theorem B2687723 : Blo 1790096 2687723 := bstep (se 1 (by rfl) ⟨2015792, by rfl⟩ : syracuseStep 2687723 = 4031585) B4031585
theorem B2687753 : Blo 1790096 2687753 := bstep (se 2 (by rfl) ⟨1007907, by rfl⟩ : syracuseStep 2687753 = 2015815) B2015815
theorem B4031279 : Blo 1790096 4031279 := bstep (se 1 (by rfl) ⟨3023459, by rfl⟩ : syracuseStep 4031279 = 6046919) B6046919
theorem B5735225 : Blo 1790096 5735225 := bstep (se 2 (by rfl) ⟨2150709, by rfl⟩ : syracuseStep 5735225 = 4301419) B4301419
theorem B2687855 : Blo 1790096 2687855 := bstep (se 1 (by rfl) ⟨2015891, by rfl⟩ : syracuseStep 2687855 = 4031783) B4031783
theorem B4596647 : Blo 1790096 4596647 := bstep (se 1 (by rfl) ⟨3447485, by rfl⟩ : syracuseStep 4596647 = 6894971) B6894971
theorem B2688107 : Blo 1790096 2688107 := bstep (se 1 (by rfl) ⟨2016080, by rfl⟩ : syracuseStep 2688107 = 4032161) B4032161
theorem B3024047 : Blo 1790096 3024047 := bstep (se 1 (by rfl) ⟨2268035, by rfl⟩ : syracuseStep 3024047 = 4536071) B4536071
theorem B15508999 : Blo 1790096 15508999 := bstep (se 1 (by rfl) ⟨11631749, by rfl⟩ : syracuseStep 15508999 = 23263499) B23263499
theorem B22947461 : Blo 1790096 22947461 := bstep (se 4 (by rfl) ⟨2151324, by rfl⟩ : syracuseStep 22947461 = 4302649) B4302649
theorem B10200761 : Blo 1790096 10200761 := bstep (se 2 (by rfl) ⟨3825285, by rfl⟩ : syracuseStep 10200761 = 7650571) B7650571
theorem B8603471 : Blo 1790096 8603471 := bstep (se 1 (by rfl) ⟨6452603, by rfl⟩ : syracuseStep 8603471 = 12905207) B12905207
theorem B6047567 : Blo 1790096 6047567 := bstep (se 1 (by rfl) ⟨4535675, by rfl⟩ : syracuseStep 6047567 = 9071351) B9071351
theorem B25806721 : Blo 1790096 25806721 := bstep (se 2 (by rfl) ⟨9677520, by rfl⟩ : syracuseStep 25806721 = 19355041) B19355041
theorem B10201079 : Blo 1790096 10201079 := bstep (se 1 (by rfl) ⟨7650809, by rfl⟩ : syracuseStep 10201079 = 15301619) B15301619
theorem B74516609 : Blo 1790096 74516609 := bstep (se 2 (by rfl) ⟨27943728, by rfl⟩ : syracuseStep 74516609 = 55887457) B55887457
theorem B6047891 : Blo 1790096 6047891 := bstep (se 1 (by rfl) ⟨4535918, by rfl⟩ : syracuseStep 6047891 = 9071837) B9071837
theorem B3270847 : Blo 1790096 3270847 := bstep (se 1 (by rfl) ⟨2453135, by rfl⟩ : syracuseStep 3270847 = 4906271) B4906271
theorem B25815257 : Blo 1790096 25815257 := bstep (se 2 (by rfl) ⟨9680721, by rfl⟩ : syracuseStep 25815257 = 19361443) B19361443
theorem B4532537 : Blo 1790096 4532537 := bstep (se 2 (by rfl) ⟨1699701, by rfl⟩ : syracuseStep 4532537 = 3399403) B3399403
theorem B6048161 : Blo 1790096 6048161 := bstep (se 2 (by rfl) ⟨2268060, by rfl⟩ : syracuseStep 6048161 = 4536121) B4536121
theorem B45926999 : Blo 1790096 45926999 := bstep (se 1 (by rfl) ⟨34445249, by rfl⟩ : syracuseStep 45926999 = 68890499) B68890499
theorem B9685651 : Blo 1790096 9685651 := bstep (se 1 (by rfl) ⟨7264238, by rfl⟩ : syracuseStep 9685651 = 14528477) B14528477
theorem B1911643 : Blo 1790096 1911643 := bstep (se 1 (by rfl) ⟨1433732, by rfl⟩ : syracuseStep 1911643 = 2867465) B2867465
theorem B36784991 : Blo 1790096 36784991 := bstep (se 1 (by rfl) ⟨27588743, by rfl⟩ : syracuseStep 36784991 = 55177487) B55177487
theorem B21793697 : Blo 1790096 21793697 := bstep (se 2 (by rfl) ⟨8172636, by rfl⟩ : syracuseStep 21793697 = 16345273) B16345273
theorem B5172187 : Blo 1790096 5172187 := bstep (se 1 (by rfl) ⟨3879140, by rfl⟩ : syracuseStep 5172187 = 7758281) B7758281
theorem B2419895 : Blo 1790096 2419895 := bstep (se 1 (by rfl) ⟨1814921, by rfl⟩ : syracuseStep 2419895 = 3629843) B3629843
theorem B4533529 : Blo 1790096 4533529 := bstep (se 2 (by rfl) ⟨1700073, by rfl⟩ : syracuseStep 4533529 = 3400147) B3400147
theorem B14527831 : Blo 1790096 14527831 := bstep (se 1 (by rfl) ⟨10895873, by rfl⟩ : syracuseStep 14527831 = 21791747) B21791747
theorem B9072161 : Blo 1790096 9072161 := bstep (se 2 (by rfl) ⟨3402060, by rfl⟩ : syracuseStep 9072161 = 6804121) B6804121
theorem B5099071 : Blo 1790096 5099071 := bstep (se 1 (by rfl) ⟨3824303, by rfl⟩ : syracuseStep 5099071 = 7648607) B7648607
theorem B7261759 : Blo 1790096 7261759 := bstep (se 1 (by rfl) ⟨5446319, by rfl⟩ : syracuseStep 7261759 = 10892639) B10892639
theorem B4533833 : Blo 1790096 4533833 := bstep (se 2 (by rfl) ⟨1700187, by rfl⟩ : syracuseStep 4533833 = 3400375) B3400375
theorem B2297435 : Blo 1790096 2297435 := bstep (se 1 (by rfl) ⟨1723076, by rfl⟩ : syracuseStep 2297435 = 3446153) B3446153
theorem B10202719 : Blo 1790096 10202719 := bstep (se 1 (by rfl) ⟨7652039, by rfl⟩ : syracuseStep 10202719 = 15304079) B15304079
theorem B6540907 : Blo 1790096 6540907 := bstep (se 1 (by rfl) ⟨4905680, by rfl⟩ : syracuseStep 6540907 = 9811361) B9811361
theorem B2551591 : Blo 1790096 2551591 := bstep (se 1 (by rfl) ⟨1913693, by rfl⟩ : syracuseStep 2551591 = 3827387) B3827387
theorem B3682169 : Blo 1790096 3682169 := bstep (se 2 (by rfl) ⟨1380813, by rfl⟩ : syracuseStep 3682169 = 2761627) B2761627
theorem B6041789 : Blo 1790096 6041789 := bstep (se 3 (by rfl) ⟨1132835, by rfl⟩ : syracuseStep 6041789 = 2265671) B2265671
theorem B1790183 : Blo 1790096 1790183 := bstep (se 1 (by rfl) ⟨1342637, by rfl⟩ : syracuseStep 1790183 = 2685275) B2685275
theorem B1790335 : Blo 1790096 1790335 := bstep (se 1 (by rfl) ⟨1342751, by rfl⟩ : syracuseStep 1790335 = 2685503) B2685503
theorem B1790415 : Blo 1790096 1790415 := bstep (se 1 (by rfl) ⟨1342811, by rfl⟩ : syracuseStep 1790415 = 2685623) B2685623
theorem B4305503 : Blo 1790096 4305503 := bstep (se 1 (by rfl) ⟨3229127, by rfl⟩ : syracuseStep 4305503 = 6458255) B6458255
theorem B1790567 : Blo 1790096 1790567 := bstep (se 1 (by rfl) ⟨1342925, by rfl⟩ : syracuseStep 1790567 = 2685851) B2685851
theorem B8844023 : Blo 1790096 8844023 := bstep (se 1 (by rfl) ⟨6633017, by rfl⟩ : syracuseStep 8844023 = 13266035) B13266035
theorem B29045537 : Blo 1790096 29045537 := bstep (se 2 (by rfl) ⟨10892076, by rfl⟩ : syracuseStep 29045537 = 21784153) B21784153
theorem B1790831 : Blo 1790096 1790831 := bstep (se 1 (by rfl) ⟨1343123, by rfl⟩ : syracuseStep 1790831 = 2686247) B2686247
theorem B1790887 : Blo 1790096 1790887 := bstep (se 1 (by rfl) ⟨1343165, by rfl⟩ : syracuseStep 1790887 = 2686331) B2686331
theorem B1790971 : Blo 1790096 1790971 := bstep (se 1 (by rfl) ⟨1343228, by rfl⟩ : syracuseStep 1790971 = 2686457) B2686457
theorem B4535291 : Blo 1790096 4535291 := bstep (se 1 (by rfl) ⟨3401468, by rfl⟩ : syracuseStep 4535291 = 6802937) B6802937
theorem B1791039 : Blo 1790096 1791039 := bstep (se 1 (by rfl) ⟨1343279, by rfl⟩ : syracuseStep 1791039 = 2686559) B2686559
theorem B2266319 : Blo 1790096 2266319 := bstep (se 1 (by rfl) ⟨1699739, by rfl⟩ : syracuseStep 2266319 = 3399479) B3399479
theorem B1791183 : Blo 1790096 1791183 := bstep (se 1 (by rfl) ⟨1343387, by rfl⟩ : syracuseStep 1791183 = 2686775) B2686775
theorem B9065681 : Blo 1790096 9065681 := bstep (se 2 (by rfl) ⟨3399630, by rfl⟩ : syracuseStep 9065681 = 6799261) B6799261
theorem B16782623 : Blo 1790096 16782623 := bstep (se 1 (by rfl) ⟨12586967, by rfl⟩ : syracuseStep 16782623 = 25173935) B25173935
theorem B8607007 : Blo 1790096 8607007 := bstep (se 1 (by rfl) ⟨6455255, by rfl⟩ : syracuseStep 8607007 = 12910511) B12910511
theorem B6042977 : Blo 1790096 6042977 := bstep (se 2 (by rfl) ⟨2266116, by rfl⟩ : syracuseStep 6042977 = 4532233) B4532233
theorem B1791387 : Blo 1790096 1791387 := bstep (se 1 (by rfl) ⟨1343540, by rfl⟩ : syracuseStep 1791387 = 2687081) B2687081
theorem B4535777 : Blo 1790096 4535777 := bstep (se 2 (by rfl) ⟨1700916, by rfl⟩ : syracuseStep 4535777 = 3401833) B3401833
theorem B4363847 : Blo 1790096 4363847 := bstep (se 1 (by rfl) ⟨3272885, by rfl⟩ : syracuseStep 4363847 = 6545771) B6545771
theorem B49002083 : Blo 1790096 49002083 := bstep (se 1 (by rfl) ⟨36751562, by rfl⟩ : syracuseStep 49002083 = 73503125) B73503125
theorem B1791599 : Blo 1790096 1791599 := bstep (se 1 (by rfl) ⟨1343699, by rfl⟩ : syracuseStep 1791599 = 2687399) B2687399
theorem B1791655 : Blo 1790096 1791655 := bstep (se 1 (by rfl) ⟨1343741, by rfl⟩ : syracuseStep 1791655 = 2687483) B2687483
theorem B4028075 : Blo 1790096 4028075 := bstep (se 1 (by rfl) ⟨3021056, by rfl⟩ : syracuseStep 4028075 = 6042113) B6042113
theorem B12908267 : Blo 1790096 12908267 := bstep (se 1 (by rfl) ⟨9681200, by rfl⟩ : syracuseStep 12908267 = 19362401) B19362401
theorem B3823355 : Blo 1790096 3823355 := bstep (se 1 (by rfl) ⟨2867516, by rfl⟩ : syracuseStep 3823355 = 5735033) B5735033
theorem B1791739 : Blo 1790096 1791739 := bstep (se 1 (by rfl) ⟨1343804, by rfl⟩ : syracuseStep 1791739 = 2687609) B2687609
theorem B1791775 : Blo 1790096 1791775 := bstep (se 1 (by rfl) ⟨1343831, by rfl⟩ : syracuseStep 1791775 = 2687663) B2687663
theorem B1791807 : Blo 1790096 1791807 := bstep (se 1 (by rfl) ⟨1343855, by rfl⟩ : syracuseStep 1791807 = 2687711) B2687711
theorem B4028399 : Blo 1790096 4028399 := bstep (se 1 (by rfl) ⟨3021299, by rfl⟩ : syracuseStep 4028399 = 6042599) B6042599
theorem B2267119 : Blo 1790096 2267119 := bstep (se 1 (by rfl) ⟨1700339, by rfl⟩ : syracuseStep 2267119 = 3400679) B3400679
theorem B1791983 : Blo 1790096 1791983 := bstep (se 1 (by rfl) ⟨1343987, by rfl⟩ : syracuseStep 1791983 = 2687975) B2687975
theorem B2267291 : Blo 1790096 2267291 := bstep (se 1 (by rfl) ⟨1700468, by rfl⟩ : syracuseStep 2267291 = 3400937) B3400937
theorem B4028615 : Blo 1790096 4028615 := bstep (se 1 (by rfl) ⟨3021461, by rfl⟩ : syracuseStep 4028615 = 6042923) B6042923
theorem B2685161 : Blo 1790096 2685161 := bstep (se 2 (by rfl) ⟨1006935, by rfl⟩ : syracuseStep 2685161 = 2013871) B2013871
theorem B2758951 : Blo 1790096 2758951 := bstep (se 1 (by rfl) ⟨2069213, by rfl⟩ : syracuseStep 2758951 = 4138427) B4138427
theorem B3021097 : Blo 1790096 3021097 := bstep (se 2 (by rfl) ⟨1132911, by rfl⟩ : syracuseStep 3021097 = 2265823) B2265823
theorem B7649579 : Blo 1790096 7649579 := bstep (se 1 (by rfl) ⟨5737184, by rfl⟩ : syracuseStep 7649579 = 11474369) B11474369
theorem B4028795 : Blo 1790096 4028795 := bstep (se 1 (by rfl) ⟨3021596, by rfl⟩ : syracuseStep 4028795 = 6043193) B6043193
theorem B8608123 : Blo 1790096 8608123 := bstep (se 1 (by rfl) ⟨6456092, by rfl⟩ : syracuseStep 8608123 = 12912185) B12912185
theorem B30587381 : Blo 1790096 30587381 := bstep (se 5 (by rfl) ⟨1433783, by rfl⟩ : syracuseStep 30587381 = 2867567) B2867567
theorem B2685467 : Blo 1790096 2685467 := bstep (se 1 (by rfl) ⟨2014100, by rfl⟩ : syracuseStep 2685467 = 4028201) B4028201
theorem B3062303 : Blo 1790096 3062303 := bstep (se 1 (by rfl) ⟨2296727, by rfl⟩ : syracuseStep 3062303 = 4593455) B4593455
theorem B2685545 : Blo 1790096 2685545 := bstep (se 2 (by rfl) ⟨1007079, by rfl⟩ : syracuseStep 2685545 = 2014159) B2014159
theorem B13597307 : Blo 1790096 13597307 := bstep (se 1 (by rfl) ⟨10197980, by rfl⟩ : syracuseStep 13597307 = 20395961) B20395961
theorem B4029065 : Blo 1790096 4029065 := bstep (se 2 (by rfl) ⟨1510899, by rfl⟩ : syracuseStep 4029065 = 3021799) B3021799
theorem B2267995 : Blo 1790096 2267995 := bstep (se 1 (by rfl) ⟨1700996, by rfl⟩ : syracuseStep 2267995 = 3401993) B3401993
theorem B15293555 : Blo 1790096 15293555 := bstep (se 1 (by rfl) ⟨11470166, by rfl⟩ : syracuseStep 15293555 = 22940333) B22940333
theorem B2686073 : Blo 1790096 2686073 := bstep (se 2 (by rfl) ⟨1007277, by rfl⟩ : syracuseStep 2686073 = 2014555) B2014555
theorem B10198163 : Blo 1790096 10198163 := bstep (se 1 (by rfl) ⟨7648622, by rfl⟩ : syracuseStep 10198163 = 15297245) B15297245
theorem B4029623 : Blo 1790096 4029623 := bstep (se 1 (by rfl) ⟨3022217, by rfl⟩ : syracuseStep 4029623 = 6044435) B6044435
theorem B58907837 : Blo 1790096 58907837 := bstep (se 3 (by rfl) ⟨11045219, by rfl⟩ : syracuseStep 58907837 = 22090439) B22090439
theorem B3103967 : Blo 1790096 3103967 := bstep (se 1 (by rfl) ⟨2327975, by rfl⟩ : syracuseStep 3103967 = 4655951) B4655951
theorem B2686175 : Blo 1790096 2686175 := bstep (se 1 (by rfl) ⟨2014631, by rfl⟩ : syracuseStep 2686175 = 4029263) B4029263
theorem B6044921 : Blo 1790096 6044921 := bstep (se 2 (by rfl) ⟨2266845, by rfl⟩ : syracuseStep 6044921 = 4533691) B4533691
theorem B2686217 : Blo 1790096 2686217 := bstep (se 2 (by rfl) ⟨1007331, by rfl⟩ : syracuseStep 2686217 = 2014663) B2014663
theorem B9190685 : Blo 1790096 9190685 := bstep (se 3 (by rfl) ⟨1723253, by rfl⟩ : syracuseStep 9190685 = 3446507) B3446507
theorem B3399023 : Blo 1790096 3399023 := bstep (se 1 (by rfl) ⟨2549267, by rfl⟩ : syracuseStep 3399023 = 5098535) B5098535
theorem B2686319 : Blo 1790096 2686319 := bstep (se 1 (by rfl) ⟨2014739, by rfl⟩ : syracuseStep 2686319 = 4029479) B4029479
theorem B2686439 : Blo 1790096 2686439 := bstep (se 1 (by rfl) ⟨2014829, by rfl⟩ : syracuseStep 2686439 = 4029659) B4029659
theorem B6045191 : Blo 1790096 6045191 := bstep (se 1 (by rfl) ⟨4533893, by rfl⟩ : syracuseStep 6045191 = 9067787) B9067787
theorem B9068111 : Blo 1790096 9068111 := bstep (se 1 (by rfl) ⟨6801083, by rfl⟩ : syracuseStep 9068111 = 13602167) B13602167
theorem B3399259 : Blo 1790096 3399259 := bstep (se 1 (by rfl) ⟨2549444, by rfl⟩ : syracuseStep 3399259 = 5098889) B5098889
theorem B3022427 : Blo 1790096 3022427 := bstep (se 1 (by rfl) ⟨2266820, by rfl⟩ : syracuseStep 3022427 = 4533641) B4533641
theorem B2686571 : Blo 1790096 2686571 := bstep (se 1 (by rfl) ⟨2014928, by rfl⟩ : syracuseStep 2686571 = 4029857) B4029857
theorem B2686697 : Blo 1790096 2686697 := bstep (se 2 (by rfl) ⟨1007511, by rfl⟩ : syracuseStep 2686697 = 2015023) B2015023
theorem B4030199 : Blo 1790096 4030199 := bstep (se 1 (by rfl) ⟨3022649, by rfl⟩ : syracuseStep 4030199 = 6045299) B6045299
theorem B3022663 : Blo 1790096 3022663 := bstep (se 1 (by rfl) ⟨2266997, by rfl⟩ : syracuseStep 3022663 = 4533995) B4533995
theorem B2686841 : Blo 1790096 2686841 := bstep (se 2 (by rfl) ⟨1007565, by rfl⟩ : syracuseStep 2686841 = 2015131) B2015131
theorem B4030379 : Blo 1790096 4030379 := bstep (se 1 (by rfl) ⟨3022784, by rfl⟩ : syracuseStep 4030379 = 6045569) B6045569
theorem B2686943 : Blo 1790096 2686943 := bstep (se 1 (by rfl) ⟨2015207, by rfl⟩ : syracuseStep 2686943 = 4030415) B4030415
theorem B248250379 : Blo 1790096 248250379 := bstep (se 1 (by rfl) ⟨186187784, by rfl⟩ : syracuseStep 248250379 = 372375569) B372375569
theorem B2687279 : Blo 1790096 2687279 := bstep (se 1 (by rfl) ⟨2015459, by rfl⟩ : syracuseStep 2687279 = 4030919) B4030919
theorem B4030847 : Blo 1790096 4030847 := bstep (se 1 (by rfl) ⟨3023135, by rfl⟩ : syracuseStep 4030847 = 6046271) B6046271
theorem B6046109 : Blo 1790096 6046109 := bstep (se 3 (by rfl) ⟨1133645, by rfl⟩ : syracuseStep 6046109 = 2267291) B2267291
theorem B11477497 : Blo 1790096 11477497 := bstep (se 2 (by rfl) ⟨4304061, by rfl⟩ : syracuseStep 11477497 = 8608123) B8608123
theorem B2687519 : Blo 1790096 2687519 := bstep (se 1 (by rfl) ⟨2015639, by rfl⟩ : syracuseStep 2687519 = 4031279) B4031279
theorem B4031081 : Blo 1790096 4031081 := bstep (se 2 (by rfl) ⟨1511655, by rfl⟩ : syracuseStep 4031081 = 3023311) B3023311
theorem B3023527 : Blo 1790096 3023527 := bstep (se 1 (by rfl) ⟨2267645, by rfl⟩ : syracuseStep 3023527 = 4535291) B4535291
theorem B20398877 : Blo 1790096 20398877 := bstep (se 3 (by rfl) ⟨3824789, by rfl⟩ : syracuseStep 20398877 = 7649579) B7649579
theorem B2016031 : Blo 1790096 2016031 := bstep (se 1 (by rfl) ⟨1512023, by rfl⟩ : syracuseStep 2016031 = 3024047) B3024047
theorem B3023851 : Blo 1790096 3023851 := bstep (se 1 (by rfl) ⟨2267888, by rfl⟩ : syracuseStep 3023851 = 4535777) B4535777
theorem B2909231 : Blo 1790096 2909231 := bstep (se 1 (by rfl) ⟨2181923, by rfl⟩ : syracuseStep 2909231 = 4363847) B4363847
theorem B3023993 : Blo 1790096 3023993 := bstep (se 2 (by rfl) ⟨1133997, by rfl⟩ : syracuseStep 3023993 = 2267995) B2267995
theorem B6800507 : Blo 1790096 6800507 := bstep (se 1 (by rfl) ⟨5100380, by rfl⟩ : syracuseStep 6800507 = 10200761) B10200761
theorem B2548903 : Blo 1790096 2548903 := bstep (se 1 (by rfl) ⟨1911677, by rfl⟩ : syracuseStep 2548903 = 3823355) B3823355
theorem B5735647 : Blo 1790096 5735647 := bstep (se 1 (by rfl) ⟨4301735, by rfl⟩ : syracuseStep 5735647 = 8603471) B8603471
theorem B4031711 : Blo 1790096 4031711 := bstep (se 1 (by rfl) ⟨3023783, by rfl⟩ : syracuseStep 4031711 = 6047567) B6047567
theorem B6800719 : Blo 1790096 6800719 := bstep (se 1 (by rfl) ⟨5100539, by rfl⟩ : syracuseStep 6800719 = 10201079) B10201079
theorem B4031927 : Blo 1790096 4031927 := bstep (se 1 (by rfl) ⟨3023945, by rfl⟩ : syracuseStep 4031927 = 6047891) B6047891
theorem B14714405 : Blo 1790096 14714405 := bstep (se 4 (by rfl) ⟨1379475, by rfl⟩ : syracuseStep 14714405 = 2758951) B2758951
theorem B13608485 : Blo 1790096 13608485 := bstep (se 4 (by rfl) ⟨1275795, by rfl⟩ : syracuseStep 13608485 = 2551591) B2551591
theorem B4032107 : Blo 1790096 4032107 := bstep (se 1 (by rfl) ⟨3024080, by rfl⟩ : syracuseStep 4032107 = 6048161) B6048161
theorem B20391587 : Blo 1790096 20391587 := bstep (se 1 (by rfl) ⟨15293690, by rfl⟩ : syracuseStep 20391587 = 30587381) B30587381
theorem B2041535 : Blo 1790096 2041535 := bstep (se 1 (by rfl) ⟨1531151, by rfl⟩ : syracuseStep 2041535 = 3062303) B3062303
theorem B20678665 : Blo 1790096 20678665 := bstep (se 2 (by rfl) ⟨7754499, by rfl⟩ : syracuseStep 20678665 = 15508999) B15508999
theorem B4532345 : Blo 1790096 4532345 := bstep (se 2 (by rfl) ⟨1699629, by rfl⟩ : syracuseStep 4532345 = 3399259) B3399259
theorem B6048107 : Blo 1790096 6048107 := bstep (se 1 (by rfl) ⟨4536080, by rfl⟩ : syracuseStep 6048107 = 9072161) B9072161
theorem B12257725 : Blo 1790096 12257725 := bstep (se 3 (by rfl) ⟨2298323, by rfl⟩ : syracuseStep 12257725 = 4596647) B4596647
theorem B34408961 : Blo 1790096 34408961 := bstep (se 2 (by rfl) ⟨12903360, by rfl⟩ : syracuseStep 34408961 = 25806721) B25806721
theorem B10201787 : Blo 1790096 10201787 := bstep (se 1 (by rfl) ⟨7651340, by rfl⟩ : syracuseStep 10201787 = 15302681) B15302681
theorem B4361129 : Blo 1790096 4361129 := bstep (se 2 (by rfl) ⟨1635423, by rfl⟩ : syracuseStep 4361129 = 3270847) B3270847
theorem B2870335 : Blo 1790096 2870335 := bstep (se 1 (by rfl) ⟨2152751, by rfl⟩ : syracuseStep 2870335 = 4305503) B4305503
theorem B10202537 : Blo 1790096 10202537 := bstep (se 2 (by rfl) ⟨3825951, by rfl⟩ : syracuseStep 10202537 = 7651903) B7651903
theorem B12914201 : Blo 1790096 12914201 := bstep (se 2 (by rfl) ⟨4842825, by rfl⟩ : syracuseStep 12914201 = 9685651) B9685651
theorem B24505973 : Blo 1790096 24505973 := bstep (se 5 (by rfl) ⟨1148717, by rfl⟩ : syracuseStep 24505973 = 2297435) B2297435
theorem B9064061 : Blo 1790096 9064061 := bstep (se 3 (by rfl) ⟨1699511, by rfl⟩ : syracuseStep 9064061 = 3399023) B3399023
theorem B15298307 : Blo 1790096 15298307 := bstep (se 1 (by rfl) ⟨11473730, by rfl⟩ : syracuseStep 15298307 = 22947461) B22947461
theorem B8605511 : Blo 1790096 8605511 := bstep (se 1 (by rfl) ⟨6454133, by rfl⟩ : syracuseStep 8605511 = 12908267) B12908267
theorem B1790107 : Blo 1790096 1790107 := bstep (se 1 (by rfl) ⟨1342580, by rfl⟩ : syracuseStep 1790107 = 2685161) B2685161
theorem B1790311 : Blo 1790096 1790311 := bstep (se 1 (by rfl) ⟨1342733, by rfl⟩ : syracuseStep 1790311 = 2685467) B2685467
theorem B30617999 : Blo 1790096 30617999 := bstep (se 1 (by rfl) ⟨22963499, by rfl⟩ : syracuseStep 30617999 = 45926999) B45926999
theorem B1790363 : Blo 1790096 1790363 := bstep (se 1 (by rfl) ⟨1342772, by rfl⟩ : syracuseStep 1790363 = 2685545) B2685545
theorem B9064871 : Blo 1790096 9064871 := bstep (se 1 (by rfl) ⟨6798653, by rfl⟩ : syracuseStep 9064871 = 13597307) B13597307
theorem B19370441 : Blo 1790096 19370441 := bstep (se 2 (by rfl) ⟨7263915, by rfl⟩ : syracuseStep 19370441 = 14527831) B14527831
theorem B10195429 : Blo 1790096 10195429 := bstep (se 4 (by rfl) ⟨955821, by rfl⟩ : syracuseStep 10195429 = 1911643) B1911643
theorem B24523327 : Blo 1790096 24523327 := bstep (se 1 (by rfl) ⟨18392495, by rfl⟩ : syracuseStep 24523327 = 36784991) B36784991
theorem B14529131 : Blo 1790096 14529131 := bstep (se 1 (by rfl) ⟨10896848, by rfl⟩ : syracuseStep 14529131 = 21793697) B21793697
theorem B10195703 : Blo 1790096 10195703 := bstep (se 1 (by rfl) ⟨7646777, by rfl⟩ : syracuseStep 10195703 = 15293555) B15293555
theorem B1790715 : Blo 1790096 1790715 := bstep (se 1 (by rfl) ⟨1343036, by rfl⟩ : syracuseStep 1790715 = 2686073) B2686073
theorem B13603625 : Blo 1790096 13603625 := bstep (se 2 (by rfl) ⟨5101359, by rfl⟩ : syracuseStep 13603625 = 10202719) B10202719
theorem B8721209 : Blo 1790096 8721209 := bstep (se 2 (by rfl) ⟨3270453, by rfl⟩ : syracuseStep 8721209 = 6540907) B6540907
theorem B2069311 : Blo 1790096 2069311 := bstep (se 1 (by rfl) ⟨1551983, by rfl⟩ : syracuseStep 2069311 = 3103967) B3103967
theorem B1790783 : Blo 1790096 1790783 := bstep (se 1 (by rfl) ⟨1343087, by rfl⟩ : syracuseStep 1790783 = 2686175) B2686175
theorem B1790811 : Blo 1790096 1790811 := bstep (se 1 (by rfl) ⟨1343108, by rfl⟩ : syracuseStep 1790811 = 2686217) B2686217
theorem B1790879 : Blo 1790096 1790879 := bstep (se 1 (by rfl) ⟨1343159, by rfl⟩ : syracuseStep 1790879 = 2686319) B2686319
theorem B1790959 : Blo 1790096 1790959 := bstep (se 1 (by rfl) ⟨1343219, by rfl⟩ : syracuseStep 1790959 = 2686439) B2686439
theorem B1791047 : Blo 1790096 1791047 := bstep (se 1 (by rfl) ⟨1343285, by rfl⟩ : syracuseStep 1791047 = 2686571) B2686571
theorem B1791131 : Blo 1790096 1791131 := bstep (se 1 (by rfl) ⟨1343348, by rfl⟩ : syracuseStep 1791131 = 2686697) B2686697
theorem B1791227 : Blo 1790096 1791227 := bstep (se 1 (by rfl) ⟨1343420, by rfl⟩ : syracuseStep 1791227 = 2686841) B2686841
theorem B2454779 : Blo 1790096 2454779 := bstep (se 1 (by rfl) ⟨1841084, by rfl⟩ : syracuseStep 2454779 = 3682169) B3682169
theorem B1791295 : Blo 1790096 1791295 := bstep (se 1 (by rfl) ⟨1343471, by rfl⟩ : syracuseStep 1791295 = 2686943) B2686943
theorem B4027859 : Blo 1790096 4027859 := bstep (se 1 (by rfl) ⟨3020894, by rfl⟩ : syracuseStep 4027859 = 6041789) B6041789
theorem B1791463 : Blo 1790096 1791463 := bstep (se 1 (by rfl) ⟨1343597, by rfl⟩ : syracuseStep 1791463 = 2687195) B2687195
theorem B1791471 : Blo 1790096 1791471 := bstep (se 1 (by rfl) ⟨1343603, by rfl⟩ : syracuseStep 1791471 = 2687207) B2687207
theorem B1791579 : Blo 1790096 1791579 := bstep (se 1 (by rfl) ⟨1343684, by rfl⟩ : syracuseStep 1791579 = 2687369) B2687369
theorem B1791643 : Blo 1790096 1791643 := bstep (se 1 (by rfl) ⟨1343732, by rfl⟩ : syracuseStep 1791643 = 2687465) B2687465
theorem B198710957 : Blo 1790096 198710957 := bstep (se 3 (by rfl) ⟨37258304, by rfl⟩ : syracuseStep 198710957 = 74516609) B74516609
theorem B4028129 : Blo 1790096 4028129 := bstep (se 2 (by rfl) ⟨1510548, by rfl⟩ : syracuseStep 4028129 = 3021097) B3021097
theorem B2152175 : Blo 1790096 2152175 := bstep (se 1 (by rfl) ⟨1614131, by rfl⟩ : syracuseStep 2152175 = 3228263) B3228263
theorem B1791727 : Blo 1790096 1791727 := bstep (se 1 (by rfl) ⟨1343795, by rfl⟩ : syracuseStep 1791727 = 2687591) B2687591
theorem B6453053 : Blo 1790096 6453053 := bstep (se 3 (by rfl) ⟨1209947, by rfl⟩ : syracuseStep 6453053 = 2419895) B2419895
theorem B1791815 : Blo 1790096 1791815 := bstep (se 1 (by rfl) ⟨1343861, by rfl⟩ : syracuseStep 1791815 = 2687723) B2687723
theorem B1791835 : Blo 1790096 1791835 := bstep (se 1 (by rfl) ⟨1343876, by rfl⟩ : syracuseStep 1791835 = 2687753) B2687753
theorem B19363691 : Blo 1790096 19363691 := bstep (se 1 (by rfl) ⟨14522768, by rfl⟩ : syracuseStep 19363691 = 29045537) B29045537
theorem B6043517 : Blo 1790096 6043517 := bstep (se 3 (by rfl) ⟨1133159, by rfl⟩ : syracuseStep 6043517 = 2266319) B2266319
theorem B1791903 : Blo 1790096 1791903 := bstep (se 1 (by rfl) ⟨1343927, by rfl⟩ : syracuseStep 1791903 = 2687855) B2687855
theorem B1792071 : Blo 1790096 1792071 := bstep (se 1 (by rfl) ⟨1344053, by rfl⟩ : syracuseStep 1792071 = 2688107) B2688107
theorem B24508493 : Blo 1790096 24508493 := bstep (se 3 (by rfl) ⟨4595342, by rfl⟩ : syracuseStep 24508493 = 9190685) B9190685
theorem B6043787 : Blo 1790096 6043787 := bstep (se 1 (by rfl) ⟨4532840, by rfl⟩ : syracuseStep 6043787 = 9065681) B9065681
theorem B11188415 : Blo 1790096 11188415 := bstep (se 1 (by rfl) ⟨8391311, by rfl⟩ : syracuseStep 11188415 = 16782623) B16782623
theorem B4028651 : Blo 1790096 4028651 := bstep (se 1 (by rfl) ⟨3021488, by rfl⟩ : syracuseStep 4028651 = 6042977) B6042977
theorem B32668055 : Blo 1790096 32668055 := bstep (se 1 (by rfl) ⟨24501041, by rfl⟩ : syracuseStep 32668055 = 49002083) B49002083
theorem B2685383 : Blo 1790096 2685383 := bstep (se 1 (by rfl) ⟨2014037, by rfl⟩ : syracuseStep 2685383 = 4028075) B4028075
theorem B20404709 : Blo 1790096 20404709 := bstep (se 4 (by rfl) ⟨1912941, by rfl⟩ : syracuseStep 20404709 = 3825883) B3825883
theorem B6896249 : Blo 1790096 6896249 := bstep (se 2 (by rfl) ⟨2586093, by rfl⟩ : syracuseStep 6896249 = 5172187) B5172187
theorem B2685599 : Blo 1790096 2685599 := bstep (se 1 (by rfl) ⟨2014199, by rfl⟩ : syracuseStep 2685599 = 4028399) B4028399
theorem B2685743 : Blo 1790096 2685743 := bstep (se 1 (by rfl) ⟨2014307, by rfl⟩ : syracuseStep 2685743 = 4028615) B4028615
theorem B17210171 : Blo 1790096 17210171 := bstep (se 1 (by rfl) ⟨12907628, by rfl⟩ : syracuseStep 17210171 = 25815257) B25815257
theorem B3021691 : Blo 1790096 3021691 := bstep (se 1 (by rfl) ⟨2266268, by rfl⟩ : syracuseStep 3021691 = 4532537) B4532537
theorem B2685863 : Blo 1790096 2685863 := bstep (se 1 (by rfl) ⟨2014397, by rfl⟩ : syracuseStep 2685863 = 4028795) B4028795
theorem B6044705 : Blo 1790096 6044705 := bstep (se 2 (by rfl) ⟨2266764, by rfl⟩ : syracuseStep 6044705 = 4533529) B4533529
theorem B11476009 : Blo 1790096 11476009 := bstep (se 2 (by rfl) ⟨4303503, by rfl⟩ : syracuseStep 11476009 = 8607007) B8607007
theorem B2686043 : Blo 1790096 2686043 := bstep (se 1 (by rfl) ⟨2014532, by rfl⟩ : syracuseStep 2686043 = 4029065) B4029065
theorem B23584061 : Blo 1790096 23584061 := bstep (se 3 (by rfl) ⟨4422011, by rfl⟩ : syracuseStep 23584061 = 8844023) B8844023
theorem B6798761 : Blo 1790096 6798761 := bstep (se 2 (by rfl) ⟨2549535, by rfl⟩ : syracuseStep 6798761 = 5099071) B5099071
theorem B9682345 : Blo 1790096 9682345 := bstep (se 2 (by rfl) ⟨3630879, by rfl⟩ : syracuseStep 9682345 = 7261759) B7261759
theorem B6798775 : Blo 1790096 6798775 := bstep (se 1 (by rfl) ⟨5099081, by rfl⟩ : syracuseStep 6798775 = 10198163) B10198163
theorem B2686415 : Blo 1790096 2686415 := bstep (se 1 (by rfl) ⟨2014811, by rfl⟩ : syracuseStep 2686415 = 4029623) B4029623
theorem B39271891 : Blo 1790096 39271891 := bstep (se 1 (by rfl) ⟨29453918, by rfl⟩ : syracuseStep 39271891 = 58907837) B58907837
theorem B15293933 : Blo 1790096 15293933 := bstep (se 3 (by rfl) ⟨2867612, by rfl⟩ : syracuseStep 15293933 = 5735225) B5735225
theorem B4029947 : Blo 1790096 4029947 := bstep (se 1 (by rfl) ⟨3022460, by rfl⟩ : syracuseStep 4029947 = 6044921) B6044921
theorem B4030127 : Blo 1790096 4030127 := bstep (se 1 (by rfl) ⟨3022595, by rfl⟩ : syracuseStep 4030127 = 6045191) B6045191
theorem B3022555 : Blo 1790096 3022555 := bstep (se 1 (by rfl) ⟨2266916, by rfl⟩ : syracuseStep 3022555 = 4533833) B4533833
theorem B6045407 : Blo 1790096 6045407 := bstep (se 1 (by rfl) ⟨4534055, by rfl⟩ : syracuseStep 6045407 = 9068111) B9068111
theorem B2014951 : Blo 1790096 2014951 := bstep (se 1 (by rfl) ⟨1511213, by rfl⟩ : syracuseStep 2014951 = 3022427) B3022427
theorem B4030217 : Blo 1790096 4030217 := bstep (se 2 (by rfl) ⟨1511331, by rfl⟩ : syracuseStep 4030217 = 3022663) B3022663
theorem B2686799 : Blo 1790096 2686799 := bstep (se 1 (by rfl) ⟨2015099, by rfl⟩ : syracuseStep 2686799 = 4030199) B4030199
theorem B2686919 : Blo 1790096 2686919 := bstep (se 1 (by rfl) ⟨2015189, by rfl⟩ : syracuseStep 2686919 = 4030379) B4030379
theorem B3022825 : Blo 1790096 3022825 := bstep (se 2 (by rfl) ⟨1133559, by rfl⟩ : syracuseStep 3022825 = 2267119) B2267119
theorem B2687231 : Blo 1790096 2687231 := bstep (se 1 (by rfl) ⟨2015423, by rfl⟩ : syracuseStep 2687231 = 4030847) B4030847
theorem B4030739 : Blo 1790096 4030739 := bstep (se 1 (by rfl) ⟨3023054, by rfl⟩ : syracuseStep 4030739 = 6046109) B6046109
theorem B2687387 : Blo 1790096 2687387 := bstep (se 1 (by rfl) ⟨2015540, by rfl⟩ : syracuseStep 2687387 = 4031081) B4031081
theorem B29835773 : Blo 1790096 29835773 := bstep (se 3 (by rfl) ⟨5594207, by rfl⟩ : syracuseStep 29835773 = 11188415) B11188415
theorem B13599251 : Blo 1790096 13599251 := bstep (se 1 (by rfl) ⟨10199438, by rfl⟩ : syracuseStep 13599251 = 20398877) B20398877
theorem B9069083 : Blo 1790096 9069083 := bstep (se 1 (by rfl) ⟨6801812, by rfl⟩ : syracuseStep 9069083 = 13603625) B13603625
theorem B16343633 : Blo 1790096 16343633 := bstep (se 2 (by rfl) ⟨6128862, by rfl⟩ : syracuseStep 16343633 = 12257725) B12257725
theorem B6546077 : Blo 1790096 6546077 := bstep (se 3 (by rfl) ⟨1227389, by rfl⟩ : syracuseStep 6546077 = 2454779) B2454779
theorem B15303329 : Blo 1790096 15303329 := bstep (se 2 (by rfl) ⟨5738748, by rfl⟩ : syracuseStep 15303329 = 11477497) B11477497
theorem B2015995 : Blo 1790096 2015995 := bstep (se 1 (by rfl) ⟨1511996, by rfl⟩ : syracuseStep 2015995 = 3023993) B3023993
theorem B2687807 : Blo 1790096 2687807 := bstep (se 1 (by rfl) ⟨2015855, by rfl⟩ : syracuseStep 2687807 = 4031711) B4031711
theorem B62890829 : Blo 1790096 62890829 := bstep (se 3 (by rfl) ⟨11792030, by rfl⟩ : syracuseStep 62890829 = 23584061) B23584061
theorem B4031369 : Blo 1790096 4031369 := bstep (se 2 (by rfl) ⟨1511763, by rfl⟩ : syracuseStep 4031369 = 3023527) B3023527
theorem B2687951 : Blo 1790096 2687951 := bstep (se 1 (by rfl) ⟨2015963, by rfl⟩ : syracuseStep 2687951 = 4031927) B4031927
theorem B2688041 : Blo 1790096 2688041 := bstep (se 2 (by rfl) ⟨1008015, by rfl⟩ : syracuseStep 2688041 = 2016031) B2016031
theorem B2688071 : Blo 1790096 2688071 := bstep (se 1 (by rfl) ⟨2016053, by rfl⟩ : syracuseStep 2688071 = 4032107) B4032107
theorem B132473971 : Blo 1790096 132473971 := bstep (se 1 (by rfl) ⟨99355478, by rfl⟩ : syracuseStep 132473971 = 198710957) B198710957
theorem B4302035 : Blo 1790096 4302035 := bstep (se 1 (by rfl) ⟨3226526, by rfl⟩ : syracuseStep 4302035 = 6453053) B6453053
theorem B4031801 : Blo 1790096 4031801 := bstep (se 2 (by rfl) ⟨1511925, by rfl⟩ : syracuseStep 4031801 = 3023851) B3023851
theorem B4032071 : Blo 1790096 4032071 := bstep (se 1 (by rfl) ⟨3024053, by rfl⟩ : syracuseStep 4032071 = 6048107) B6048107
theorem B22939307 : Blo 1790096 22939307 := bstep (se 1 (by rfl) ⟨17204480, by rfl⟩ : syracuseStep 22939307 = 34408961) B34408961
theorem B4597499 : Blo 1790096 4597499 := bstep (se 1 (by rfl) ⟨3448124, by rfl⟩ : syracuseStep 4597499 = 6896249) B6896249
theorem B6801191 : Blo 1790096 6801191 := bstep (se 1 (by rfl) ⟨5100893, by rfl⟩ : syracuseStep 6801191 = 10201787) B10201787
theorem B4532507 : Blo 1790096 4532507 := bstep (se 1 (by rfl) ⟨3399380, by rfl⟩ : syracuseStep 4532507 = 6798761) B6798761
theorem B6801691 : Blo 1790096 6801691 := bstep (se 1 (by rfl) ⟨5101268, by rfl⟩ : syracuseStep 6801691 = 10202537) B10202537
theorem B16337315 : Blo 1790096 16337315 := bstep (se 1 (by rfl) ⟨12252986, by rfl⟩ : syracuseStep 16337315 = 24505973) B24505973
theorem B5737007 : Blo 1790096 5737007 := bstep (se 1 (by rfl) ⟨4302755, by rfl⟩ : syracuseStep 5737007 = 8605511) B8605511
theorem B331000505 : Blo 1790096 331000505 := bstep (se 2 (by rfl) ⟨124125189, by rfl⟩ : syracuseStep 331000505 = 248250379) B248250379
theorem B12913627 : Blo 1790096 12913627 := bstep (se 1 (by rfl) ⟨9685220, by rfl⟩ : syracuseStep 12913627 = 19370441) B19370441
theorem B9686087 : Blo 1790096 9686087 := bstep (se 1 (by rfl) ⟨7264565, by rfl⟩ : syracuseStep 9686087 = 14529131) B14529131
theorem B13593905 : Blo 1790096 13593905 := bstep (se 2 (by rfl) ⟨5097714, by rfl⟩ : syracuseStep 13593905 = 10195429) B10195429
theorem B4533671 : Blo 1790096 4533671 := bstep (se 1 (by rfl) ⟨3400253, by rfl⟩ : syracuseStep 4533671 = 6800507) B6800507
theorem B32697769 : Blo 1790096 32697769 := bstep (se 2 (by rfl) ⟨12261663, by rfl⟩ : syracuseStep 32697769 = 24523327) B24523327
theorem B9809603 : Blo 1790096 9809603 := bstep (se 1 (by rfl) ⟨7357202, by rfl⟩ : syracuseStep 9809603 = 14714405) B14714405
theorem B9072323 : Blo 1790096 9072323 := bstep (se 1 (by rfl) ⟨6804242, by rfl⟩ : syracuseStep 9072323 = 13608485) B13608485
theorem B13594391 : Blo 1790096 13594391 := bstep (se 1 (by rfl) ⟨10195793, by rfl⟩ : syracuseStep 13594391 = 20391587) B20391587
theorem B16338995 : Blo 1790096 16338995 := bstep (se 1 (by rfl) ⟨12254246, by rfl⟩ : syracuseStep 16338995 = 24508493) B24508493
theorem B21778703 : Blo 1790096 21778703 := bstep (se 1 (by rfl) ⟨16334027, by rfl⟩ : syracuseStep 21778703 = 32668055) B32668055
theorem B7647529 : Blo 1790096 7647529 := bstep (se 2 (by rfl) ⟨2867823, by rfl⟩ : syracuseStep 7647529 = 5735647) B5735647
theorem B1790255 : Blo 1790096 1790255 := bstep (se 1 (by rfl) ⟨1342691, by rfl⟩ : syracuseStep 1790255 = 2685383) B2685383
theorem B13603139 : Blo 1790096 13603139 := bstep (se 1 (by rfl) ⟨10202354, by rfl⟩ : syracuseStep 13603139 = 20404709) B20404709
theorem B1790399 : Blo 1790096 1790399 := bstep (se 1 (by rfl) ⟨1342799, by rfl⟩ : syracuseStep 1790399 = 2685599) B2685599
theorem B5444093 : Blo 1790096 5444093 := bstep (se 3 (by rfl) ⟨1020767, by rfl⟩ : syracuseStep 5444093 = 2041535) B2041535
theorem B1790495 : Blo 1790096 1790495 := bstep (se 1 (by rfl) ⟨1342871, by rfl⟩ : syracuseStep 1790495 = 2685743) B2685743
theorem B11473447 : Blo 1790096 11473447 := bstep (se 1 (by rfl) ⟨8605085, by rfl⟩ : syracuseStep 11473447 = 17210171) B17210171
theorem B9065033 : Blo 1790096 9065033 := bstep (se 2 (by rfl) ⟨3399387, by rfl⟩ : syracuseStep 9065033 = 6798775) B6798775
theorem B1790575 : Blo 1790096 1790575 := bstep (se 1 (by rfl) ⟨1342931, by rfl⟩ : syracuseStep 1790575 = 2685863) B2685863
theorem B5739133 : Blo 1790096 5739133 := bstep (se 3 (by rfl) ⟨1076087, by rfl⟩ : syracuseStep 5739133 = 2152175) B2152175
theorem B1790695 : Blo 1790096 1790695 := bstep (se 1 (by rfl) ⟨1343021, by rfl⟩ : syracuseStep 1790695 = 2686043) B2686043
theorem B1790943 : Blo 1790096 1790943 := bstep (se 1 (by rfl) ⟨1343207, by rfl⟩ : syracuseStep 1790943 = 2686415) B2686415
theorem B10195955 : Blo 1790096 10195955 := bstep (se 1 (by rfl) ⟨7646966, by rfl⟩ : syracuseStep 10195955 = 15293933) B15293933
theorem B6042707 : Blo 1790096 6042707 := bstep (se 1 (by rfl) ⟨4532030, by rfl⟩ : syracuseStep 6042707 = 9064061) B9064061
theorem B1791199 : Blo 1790096 1791199 := bstep (se 1 (by rfl) ⟨1343399, by rfl⟩ : syracuseStep 1791199 = 2686799) B2686799
theorem B1791279 : Blo 1790096 1791279 := bstep (se 1 (by rfl) ⟨1343459, by rfl⟩ : syracuseStep 1791279 = 2686919) B2686919
theorem B27571553 : Blo 1790096 27571553 := bstep (se 2 (by rfl) ⟨10339332, by rfl⟩ : syracuseStep 27571553 = 20678665) B20678665
theorem B1791519 : Blo 1790096 1791519 := bstep (se 1 (by rfl) ⟨1343639, by rfl⟩ : syracuseStep 1791519 = 2687279) B2687279
theorem B20411999 : Blo 1790096 20411999 := bstep (se 1 (by rfl) ⟨15308999, by rfl⟩ : syracuseStep 20411999 = 30617999) B30617999
theorem B6043247 : Blo 1790096 6043247 := bstep (se 1 (by rfl) ⟨4532435, by rfl⟩ : syracuseStep 6043247 = 9064871) B9064871
theorem B15308453 : Blo 1790096 15308453 := bstep (se 4 (by rfl) ⟨1435167, by rfl⟩ : syracuseStep 15308453 = 2870335) B2870335
theorem B1791679 : Blo 1790096 1791679 := bstep (se 1 (by rfl) ⟨1343759, by rfl⟩ : syracuseStep 1791679 = 2687519) B2687519
theorem B6797135 : Blo 1790096 6797135 := bstep (se 1 (by rfl) ⟨5097851, by rfl⟩ : syracuseStep 6797135 = 10195703) B10195703
theorem B1939487 : Blo 1790096 1939487 := bstep (se 1 (by rfl) ⟨1454615, by rfl⟩ : syracuseStep 1939487 = 2909231) B2909231
theorem B2685239 : Blo 1790096 2685239 := bstep (se 1 (by rfl) ⟨2013929, by rfl⟩ : syracuseStep 2685239 = 4027859) B4027859
theorem B2759081 : Blo 1790096 2759081 := bstep (se 2 (by rfl) ⟨1034655, by rfl⟩ : syracuseStep 2759081 = 2069311) B2069311
theorem B2685419 : Blo 1790096 2685419 := bstep (se 1 (by rfl) ⟨2014064, by rfl⟩ : syracuseStep 2685419 = 4028129) B4028129
theorem B4028921 : Blo 1790096 4028921 := bstep (se 2 (by rfl) ⟨1510845, by rfl⟩ : syracuseStep 4028921 = 3021691) B3021691
theorem B12909127 : Blo 1790096 12909127 := bstep (se 1 (by rfl) ⟨9681845, by rfl⟩ : syracuseStep 12909127 = 19363691) B19363691
theorem B4029011 : Blo 1790096 4029011 := bstep (se 1 (by rfl) ⟨3021758, by rfl⟩ : syracuseStep 4029011 = 6043517) B6043517
theorem B15301345 : Blo 1790096 15301345 := bstep (se 2 (by rfl) ⟨5738004, by rfl⟩ : syracuseStep 15301345 = 11476009) B11476009
theorem B34437869 : Blo 1790096 34437869 := bstep (se 3 (by rfl) ⟨6457100, by rfl⟩ : syracuseStep 34437869 = 12914201) B12914201
theorem B3021563 : Blo 1790096 3021563 := bstep (se 1 (by rfl) ⟨2266172, by rfl⟩ : syracuseStep 3021563 = 4532345) B4532345
theorem B4029191 : Blo 1790096 4029191 := bstep (se 1 (by rfl) ⟨3021893, by rfl⟩ : syracuseStep 4029191 = 6043787) B6043787
theorem B2685767 : Blo 1790096 2685767 := bstep (se 1 (by rfl) ⟨2014325, by rfl⟩ : syracuseStep 2685767 = 4028651) B4028651
theorem B3398537 : Blo 1790096 3398537 := bstep (se 2 (by rfl) ⟨1274451, by rfl⟩ : syracuseStep 3398537 = 2548903) B2548903
theorem B9067625 : Blo 1790096 9067625 := bstep (se 2 (by rfl) ⟨3400359, by rfl⟩ : syracuseStep 9067625 = 6800719) B6800719
theorem B12909793 : Blo 1790096 12909793 := bstep (se 2 (by rfl) ⟨4841172, by rfl⟩ : syracuseStep 12909793 = 9682345) B9682345
theorem B52362521 : Blo 1790096 52362521 := bstep (se 2 (by rfl) ⟨19635945, by rfl⟩ : syracuseStep 52362521 = 39271891) B39271891
theorem B2907419 : Blo 1790096 2907419 := bstep (se 1 (by rfl) ⟨2180564, by rfl⟩ : syracuseStep 2907419 = 4361129) B4361129
theorem B4029803 : Blo 1790096 4029803 := bstep (se 1 (by rfl) ⟨3022352, by rfl⟩ : syracuseStep 4029803 = 6044705) B6044705
theorem B23256557 : Blo 1790096 23256557 := bstep (se 3 (by rfl) ⟨4360604, by rfl⟩ : syracuseStep 23256557 = 8721209) B8721209
theorem B4030073 : Blo 1790096 4030073 := bstep (se 2 (by rfl) ⟨1511277, by rfl⟩ : syracuseStep 4030073 = 3022555) B3022555
theorem B2686601 : Blo 1790096 2686601 := bstep (se 2 (by rfl) ⟨1007475, by rfl⟩ : syracuseStep 2686601 = 2014951) B2014951
theorem B2686631 : Blo 1790096 2686631 := bstep (se 1 (by rfl) ⟨2014973, by rfl⟩ : syracuseStep 2686631 = 4029947) B4029947
theorem B2686751 : Blo 1790096 2686751 := bstep (se 1 (by rfl) ⟨2015063, by rfl⟩ : syracuseStep 2686751 = 4030127) B4030127
theorem B4030271 : Blo 1790096 4030271 := bstep (se 1 (by rfl) ⟨3022703, by rfl⟩ : syracuseStep 4030271 = 6045407) B6045407
theorem B10198871 : Blo 1790096 10198871 := bstep (se 1 (by rfl) ⟨7649153, by rfl⟩ : syracuseStep 10198871 = 15298307) B15298307
theorem B2686811 : Blo 1790096 2686811 := bstep (se 1 (by rfl) ⟨2015108, by rfl⟩ : syracuseStep 2686811 = 4030217) B4030217
theorem B4030433 : Blo 1790096 4030433 := bstep (se 2 (by rfl) ⟨1511412, by rfl⟩ : syracuseStep 4030433 = 3022825) B3022825
theorem B2687159 : Blo 1790096 2687159 := bstep (se 1 (by rfl) ⟨2015369, by rfl⟩ : syracuseStep 2687159 = 4030739) B4030739
theorem B9068759 : Blo 1790096 9068759 := bstep (se 1 (by rfl) ⟨6801569, by rfl⟩ : syracuseStep 9068759 = 13603139) B13603139
theorem B3629395 : Blo 1790096 3629395 := bstep (se 1 (by rfl) ⟨2722046, by rfl⟩ : syracuseStep 3629395 = 5444093) B5444093
theorem B19890515 : Blo 1790096 19890515 := bstep (se 1 (by rfl) ⟨14917886, by rfl⟩ : syracuseStep 19890515 = 29835773) B29835773
theorem B6046055 : Blo 1790096 6046055 := bstep (se 1 (by rfl) ⟨4534541, by rfl⟩ : syracuseStep 6046055 = 9069083) B9069083
theorem B9068921 : Blo 1790096 9068921 := bstep (se 2 (by rfl) ⟨3400845, by rfl⟩ : syracuseStep 9068921 = 6801691) B6801691
theorem B10895755 : Blo 1790096 10895755 := bstep (se 1 (by rfl) ⟨8171816, by rfl⟩ : syracuseStep 10895755 = 16343633) B16343633
theorem B41927219 : Blo 1790096 41927219 := bstep (se 1 (by rfl) ⟨31445414, by rfl⟩ : syracuseStep 41927219 = 62890829) B62890829
theorem B2687579 : Blo 1790096 2687579 := bstep (se 1 (by rfl) ⟨2015684, by rfl⟩ : syracuseStep 2687579 = 4031369) B4031369
theorem B17212169 : Blo 1790096 17212169 := bstep (se 2 (by rfl) ⟨6454563, by rfl⟩ : syracuseStep 17212169 = 12909127) B12909127
theorem B2868023 : Blo 1790096 2868023 := bstep (se 1 (by rfl) ⟨2151017, by rfl⟩ : syracuseStep 2868023 = 4302035) B4302035
theorem B7652177 : Blo 1790096 7652177 := bstep (se 2 (by rfl) ⟨2869566, by rfl⟩ : syracuseStep 7652177 = 5739133) B5739133
theorem B2687867 : Blo 1790096 2687867 := bstep (se 1 (by rfl) ⟨2015900, by rfl⟩ : syracuseStep 2687867 = 4031801) B4031801
theorem B2687993 : Blo 1790096 2687993 := bstep (se 2 (by rfl) ⟨1007997, by rfl⟩ : syracuseStep 2687993 = 2015995) B2015995
theorem B2688047 : Blo 1790096 2688047 := bstep (se 1 (by rfl) ⟨2016035, by rfl⟩ : syracuseStep 2688047 = 4032071) B4032071
theorem B13607999 : Blo 1790096 13607999 := bstep (se 1 (by rfl) ⟨10205999, by rfl⟩ : syracuseStep 13607999 = 20411999) B20411999
theorem B7357549 : Blo 1790096 7357549 := bstep (se 3 (by rfl) ⟨1379540, by rfl⟩ : syracuseStep 7357549 = 2759081) B2759081
theorem B3064999 : Blo 1790096 3064999 := bstep (se 1 (by rfl) ⟨2298749, by rfl⟩ : syracuseStep 3064999 = 4597499) B4597499
theorem B4531423 : Blo 1790096 4531423 := bstep (se 1 (by rfl) ⟨3398567, by rfl⟩ : syracuseStep 4531423 = 6797135) B6797135
theorem B17213057 : Blo 1790096 17213057 := bstep (se 2 (by rfl) ⟨6454896, by rfl⟩ : syracuseStep 17213057 = 12909793) B12909793
theorem B4364051 : Blo 1790096 4364051 := bstep (se 1 (by rfl) ⟨3273038, by rfl⟩ : syracuseStep 4364051 = 6546077) B6546077
theorem B6457391 : Blo 1790096 6457391 := bstep (se 1 (by rfl) ⟨4843043, by rfl⟩ : syracuseStep 6457391 = 9686087) B9686087
theorem B34908347 : Blo 1790096 34908347 := bstep (se 1 (by rfl) ⟨26181260, by rfl⟩ : syracuseStep 34908347 = 52362521) B52362521
theorem B9062603 : Blo 1790096 9062603 := bstep (se 1 (by rfl) ⟨6796952, by rfl⟩ : syracuseStep 9062603 = 13593905) B13593905
theorem B9062765 : Blo 1790096 9062765 := bstep (se 3 (by rfl) ⟨1699268, by rfl⟩ : syracuseStep 9062765 = 3398537) B3398537
theorem B6539735 : Blo 1790096 6539735 := bstep (se 1 (by rfl) ⟨4904801, by rfl⟩ : syracuseStep 6539735 = 9809603) B9809603
theorem B6048215 : Blo 1790096 6048215 := bstep (se 1 (by rfl) ⟨4536161, by rfl⟩ : syracuseStep 6048215 = 9072323) B9072323
theorem B9062927 : Blo 1790096 9062927 := bstep (se 1 (by rfl) ⟨6797195, by rfl⟩ : syracuseStep 9062927 = 13594391) B13594391
theorem B14519135 : Blo 1790096 14519135 := bstep (se 1 (by rfl) ⟨10889351, by rfl⟩ : syracuseStep 14519135 = 21778703) B21778703
theorem B20687861 : Blo 1790096 20687861 := bstep (se 5 (by rfl) ⟨969743, by rfl⟩ : syracuseStep 20687861 = 1939487) B1939487
theorem B10202219 : Blo 1790096 10202219 := bstep (se 1 (by rfl) ⟨7651664, by rfl⟩ : syracuseStep 10202219 = 15303329) B15303329
theorem B15297929 : Blo 1790096 15297929 := bstep (se 2 (by rfl) ⟨5736723, by rfl⟩ : syracuseStep 15297929 = 11473447) B11473447
theorem B7753117 : Blo 1790096 7753117 := bstep (se 3 (by rfl) ⟨1453709, by rfl⟩ : syracuseStep 7753117 = 2907419) B2907419
theorem B20401793 : Blo 1790096 20401793 := bstep (se 2 (by rfl) ⟨7650672, by rfl⟩ : syracuseStep 20401793 = 15301345) B15301345
theorem B4534127 : Blo 1790096 4534127 := bstep (se 1 (by rfl) ⟨3400595, by rfl⟩ : syracuseStep 4534127 = 6801191) B6801191
theorem B176631961 : Blo 1790096 176631961 := bstep (se 2 (by rfl) ⟨66236985, by rfl⟩ : syracuseStep 176631961 = 132473971) B132473971
theorem B1790159 : Blo 1790096 1790159 := bstep (se 1 (by rfl) ⟨1342619, by rfl⟩ : syracuseStep 1790159 = 2685239) B2685239
theorem B10891543 : Blo 1790096 10891543 := bstep (se 1 (by rfl) ⟨8168657, by rfl⟩ : syracuseStep 10891543 = 16337315) B16337315
theorem B1790279 : Blo 1790096 1790279 := bstep (se 1 (by rfl) ⟨1342709, by rfl⟩ : syracuseStep 1790279 = 2685419) B2685419
theorem B22958579 : Blo 1790096 22958579 := bstep (se 1 (by rfl) ⟨17218934, by rfl⟩ : syracuseStep 22958579 = 34437869) B34437869
theorem B1790511 : Blo 1790096 1790511 := bstep (se 1 (by rfl) ⟨1342883, by rfl⟩ : syracuseStep 1790511 = 2685767) B2685767
theorem B15504371 : Blo 1790096 15504371 := bstep (se 1 (by rfl) ⟨11628278, by rfl⟩ : syracuseStep 15504371 = 23256557) B23256557
theorem B1791067 : Blo 1790096 1791067 := bstep (se 1 (by rfl) ⟨1343300, by rfl⟩ : syracuseStep 1791067 = 2686601) B2686601
theorem B1791087 : Blo 1790096 1791087 := bstep (se 1 (by rfl) ⟨1343315, by rfl⟩ : syracuseStep 1791087 = 2686631) B2686631
theorem B1791167 : Blo 1790096 1791167 := bstep (se 1 (by rfl) ⟨1343375, by rfl⟩ : syracuseStep 1791167 = 2686751) B2686751
theorem B1791207 : Blo 1790096 1791207 := bstep (se 1 (by rfl) ⟨1343405, by rfl⟩ : syracuseStep 1791207 = 2686811) B2686811
theorem B10892663 : Blo 1790096 10892663 := bstep (se 1 (by rfl) ⟨8169497, by rfl⟩ : syracuseStep 10892663 = 16338995) B16338995
theorem B1791487 : Blo 1790096 1791487 := bstep (se 1 (by rfl) ⟨1343615, by rfl⟩ : syracuseStep 1791487 = 2687231) B2687231
theorem B1791591 : Blo 1790096 1791591 := bstep (se 1 (by rfl) ⟨1343693, by rfl⟩ : syracuseStep 1791591 = 2687387) B2687387
theorem B9066167 : Blo 1790096 9066167 := bstep (se 1 (by rfl) ⟨6799625, by rfl⟩ : syracuseStep 9066167 = 13599251) B13599251
theorem B6043355 : Blo 1790096 6043355 := bstep (se 1 (by rfl) ⟨4532516, by rfl⟩ : syracuseStep 6043355 = 9065033) B9065033
theorem B10196705 : Blo 1790096 10196705 := bstep (se 2 (by rfl) ⟨3823764, by rfl⟩ : syracuseStep 10196705 = 7647529) B7647529
theorem B1791871 : Blo 1790096 1791871 := bstep (se 1 (by rfl) ⟨1343903, by rfl⟩ : syracuseStep 1791871 = 2687807) B2687807
theorem B1791967 : Blo 1790096 1791967 := bstep (se 1 (by rfl) ⟨1343975, by rfl⟩ : syracuseStep 1791967 = 2687951) B2687951
theorem B6797303 : Blo 1790096 6797303 := bstep (se 1 (by rfl) ⟨5097977, by rfl⟩ : syracuseStep 6797303 = 10195955) B10195955
theorem B1792027 : Blo 1790096 1792027 := bstep (se 1 (by rfl) ⟨1344020, by rfl⟩ : syracuseStep 1792027 = 2688041) B2688041
theorem B1792047 : Blo 1790096 1792047 := bstep (se 1 (by rfl) ⟨1344035, by rfl⟩ : syracuseStep 1792047 = 2688071) B2688071
theorem B4028471 : Blo 1790096 4028471 := bstep (se 1 (by rfl) ⟨3021353, by rfl⟩ : syracuseStep 4028471 = 6042707) B6042707
theorem B18381035 : Blo 1790096 18381035 := bstep (se 1 (by rfl) ⟨13785776, by rfl⟩ : syracuseStep 18381035 = 27571553) B27571553
theorem B4028831 : Blo 1790096 4028831 := bstep (se 1 (by rfl) ⟨3021623, by rfl⟩ : syracuseStep 4028831 = 6043247) B6043247
theorem B15292871 : Blo 1790096 15292871 := bstep (se 1 (by rfl) ⟨11469653, by rfl⟩ : syracuseStep 15292871 = 22939307) B22939307
theorem B10205635 : Blo 1790096 10205635 := bstep (se 1 (by rfl) ⟨7654226, by rfl⟩ : syracuseStep 10205635 = 15308453) B15308453
theorem B17218169 : Blo 1790096 17218169 := bstep (se 2 (by rfl) ⟨6456813, by rfl⟩ : syracuseStep 17218169 = 12913627) B12913627
theorem B3021671 : Blo 1790096 3021671 := bstep (se 1 (by rfl) ⟨2266253, by rfl⟩ : syracuseStep 3021671 = 4532507) B4532507
theorem B2685947 : Blo 1790096 2685947 := bstep (se 1 (by rfl) ⟨2014460, by rfl⟩ : syracuseStep 2685947 = 4028921) B4028921
theorem B3824671 : Blo 1790096 3824671 := bstep (se 1 (by rfl) ⟨2868503, by rfl⟩ : syracuseStep 3824671 = 5737007) B5737007
theorem B2686007 : Blo 1790096 2686007 := bstep (se 1 (by rfl) ⟨2014505, by rfl⟩ : syracuseStep 2686007 = 4029011) B4029011
theorem B220667003 : Blo 1790096 220667003 := bstep (se 1 (by rfl) ⟨165500252, by rfl⟩ : syracuseStep 220667003 = 331000505) B331000505
theorem B2014375 : Blo 1790096 2014375 := bstep (se 1 (by rfl) ⟨1510781, by rfl⟩ : syracuseStep 2014375 = 3021563) B3021563
theorem B2686127 : Blo 1790096 2686127 := bstep (se 1 (by rfl) ⟨2014595, by rfl⟩ : syracuseStep 2686127 = 4029191) B4029191
theorem B43597025 : Blo 1790096 43597025 := bstep (se 2 (by rfl) ⟨16348884, by rfl⟩ : syracuseStep 43597025 = 32697769) B32697769
theorem B6045083 : Blo 1790096 6045083 := bstep (se 1 (by rfl) ⟨4533812, by rfl⟩ : syracuseStep 6045083 = 9067625) B9067625
theorem B2686535 : Blo 1790096 2686535 := bstep (se 1 (by rfl) ⟨2014901, by rfl⟩ : syracuseStep 2686535 = 4029803) B4029803
theorem B3022447 : Blo 1790096 3022447 := bstep (se 1 (by rfl) ⟨2266835, by rfl⟩ : syracuseStep 3022447 = 4533671) B4533671
theorem B2686715 : Blo 1790096 2686715 := bstep (se 1 (by rfl) ⟨2015036, by rfl⟩ : syracuseStep 2686715 = 4030073) B4030073
theorem B2686847 : Blo 1790096 2686847 := bstep (se 1 (by rfl) ⟨2015135, by rfl⟩ : syracuseStep 2686847 = 4030271) B4030271
theorem B6799247 : Blo 1790096 6799247 := bstep (se 1 (by rfl) ⟨5099435, by rfl⟩ : syracuseStep 6799247 = 10198871) B10198871
theorem B2686955 : Blo 1790096 2686955 := bstep (se 1 (by rfl) ⟨2015216, by rfl⟩ : syracuseStep 2686955 = 4030433) B4030433
theorem B6045839 : Blo 1790096 6045839 := bstep (se 1 (by rfl) ⟨4534379, by rfl⟩ : syracuseStep 6045839 = 9068759) B9068759
theorem B4030703 : Blo 1790096 4030703 := bstep (se 1 (by rfl) ⟨3023027, by rfl⟩ : syracuseStep 4030703 = 6046055) B6046055
theorem B6045947 : Blo 1790096 6045947 := bstep (se 1 (by rfl) ⟨4534460, by rfl⟩ : syracuseStep 6045947 = 9068921) B9068921
theorem B27951479 : Blo 1790096 27951479 := bstep (se 1 (by rfl) ⟨20963609, by rfl⟩ : syracuseStep 27951479 = 41927219) B41927219
theorem B13607513 : Blo 1790096 13607513 := bstep (se 2 (by rfl) ⟨5102817, by rfl⟩ : syracuseStep 13607513 = 10205635) B10205635
theorem B4531535 : Blo 1790096 4531535 := bstep (se 1 (by rfl) ⟨3398651, by rfl⟩ : syracuseStep 4531535 = 6797303) B6797303
theorem B4032143 : Blo 1790096 4032143 := bstep (se 1 (by rfl) ⟨3024107, by rfl⟩ : syracuseStep 4032143 = 6048215) B6048215
theorem B11478779 : Blo 1790096 11478779 := bstep (se 1 (by rfl) ⟨8609084, by rfl⟩ : syracuseStep 11478779 = 17218169) B17218169
theorem B6801479 : Blo 1790096 6801479 := bstep (se 1 (by rfl) ⟨5101109, by rfl⟩ : syracuseStep 6801479 = 10202219) B10202219
theorem B13601195 : Blo 1790096 13601195 := bstep (se 1 (by rfl) ⟨10200896, by rfl⟩ : syracuseStep 13601195 = 20401793) B20401793
theorem B4532831 : Blo 1790096 4532831 := bstep (se 1 (by rfl) ⟨3399623, by rfl⟩ : syracuseStep 4532831 = 6799247) B6799247
theorem B15305719 : Blo 1790096 15305719 := bstep (se 1 (by rfl) ⟨11479289, by rfl⟩ : syracuseStep 15305719 = 22958579) B22958579
theorem B93088925 : Blo 1790096 93088925 := bstep (se 3 (by rfl) ⟨17454173, by rfl⟩ : syracuseStep 93088925 = 34908347) B34908347
theorem B14527673 : Blo 1790096 14527673 := bstep (se 2 (by rfl) ⟨5447877, by rfl⟩ : syracuseStep 14527673 = 10895755) B10895755
theorem B1912015 : Blo 1790096 1912015 := bstep (se 1 (by rfl) ⟨1434011, by rfl⟩ : syracuseStep 1912015 = 2868023) B2868023
theorem B9071999 : Blo 1790096 9071999 := bstep (se 1 (by rfl) ⟨6803999, by rfl⟩ : syracuseStep 9071999 = 13607999) B13607999
theorem B7261775 : Blo 1790096 7261775 := bstep (se 1 (by rfl) ⟨5446331, by rfl⟩ : syracuseStep 7261775 = 10892663) B10892663
theorem B4304927 : Blo 1790096 4304927 := bstep (se 1 (by rfl) ⟨3228695, by rfl⟩ : syracuseStep 4304927 = 6457391) B6457391
theorem B5099561 : Blo 1790096 5099561 := bstep (se 2 (by rfl) ⟨1912335, by rfl⟩ : syracuseStep 5099561 = 3824671) B3824671
theorem B6041735 : Blo 1790096 6041735 := bstep (se 1 (by rfl) ⟨4531301, by rfl⟩ : syracuseStep 6041735 = 9062603) B9062603
theorem B9810065 : Blo 1790096 9810065 := bstep (se 2 (by rfl) ⟨3678774, by rfl⟩ : syracuseStep 9810065 = 7357549) B7357549
theorem B6041843 : Blo 1790096 6041843 := bstep (se 1 (by rfl) ⟨4531382, by rfl⟩ : syracuseStep 6041843 = 9062765) B9062765
theorem B6041897 : Blo 1790096 6041897 := bstep (se 2 (by rfl) ⟨2265711, by rfl⟩ : syracuseStep 6041897 = 4531423) B4531423
theorem B10195247 : Blo 1790096 10195247 := bstep (se 1 (by rfl) ⟨7646435, by rfl⟩ : syracuseStep 10195247 = 15292871) B15292871
theorem B6041951 : Blo 1790096 6041951 := bstep (se 1 (by rfl) ⟨4531463, by rfl⟩ : syracuseStep 6041951 = 9062927) B9062927
theorem B9679423 : Blo 1790096 9679423 := bstep (se 1 (by rfl) ⟨7259567, by rfl⟩ : syracuseStep 9679423 = 14519135) B14519135
theorem B13791907 : Blo 1790096 13791907 := bstep (se 1 (by rfl) ⟨10343930, by rfl⟩ : syracuseStep 13791907 = 20687861) B20687861
theorem B1790631 : Blo 1790096 1790631 := bstep (se 1 (by rfl) ⟨1342973, by rfl⟩ : syracuseStep 1790631 = 2685947) B2685947
theorem B1790671 : Blo 1790096 1790671 := bstep (se 1 (by rfl) ⟨1343003, by rfl⟩ : syracuseStep 1790671 = 2686007) B2686007
theorem B11637469 : Blo 1790096 11637469 := bstep (se 3 (by rfl) ⟨2182025, by rfl⟩ : syracuseStep 11637469 = 4364051) B4364051
theorem B1790751 : Blo 1790096 1790751 := bstep (se 1 (by rfl) ⟨1343063, by rfl⟩ : syracuseStep 1790751 = 2686127) B2686127
theorem B1791023 : Blo 1790096 1791023 := bstep (se 1 (by rfl) ⟨1343267, by rfl⟩ : syracuseStep 1791023 = 2686535) B2686535
theorem B1791143 : Blo 1790096 1791143 := bstep (se 1 (by rfl) ⟨1343357, by rfl⟩ : syracuseStep 1791143 = 2686715) B2686715
theorem B1791231 : Blo 1790096 1791231 := bstep (se 1 (by rfl) ⟨1343423, by rfl⟩ : syracuseStep 1791231 = 2686847) B2686847
theorem B1791303 : Blo 1790096 1791303 := bstep (se 1 (by rfl) ⟨1343477, by rfl⟩ : syracuseStep 1791303 = 2686955) B2686955
theorem B1791439 : Blo 1790096 1791439 := bstep (se 1 (by rfl) ⟨1343579, by rfl⟩ : syracuseStep 1791439 = 2687159) B2687159
theorem B235509281 : Blo 1790096 235509281 := bstep (se 2 (by rfl) ⟨88315980, by rfl⟩ : syracuseStep 235509281 = 176631961) B176631961
theorem B13260343 : Blo 1790096 13260343 := bstep (se 1 (by rfl) ⟨9945257, by rfl⟩ : syracuseStep 13260343 = 19890515) B19890515
theorem B14522057 : Blo 1790096 14522057 := bstep (se 2 (by rfl) ⟨5445771, by rfl⟩ : syracuseStep 14522057 = 10891543) B10891543
theorem B1791719 : Blo 1790096 1791719 := bstep (se 1 (by rfl) ⟨1343789, by rfl⟩ : syracuseStep 1791719 = 2687579) B2687579
theorem B4839193 : Blo 1790096 4839193 := bstep (se 2 (by rfl) ⟨1814697, by rfl⟩ : syracuseStep 4839193 = 3629395) B3629395
theorem B11474779 : Blo 1790096 11474779 := bstep (se 1 (by rfl) ⟨8606084, by rfl⟩ : syracuseStep 11474779 = 17212169) B17212169
theorem B5101451 : Blo 1790096 5101451 := bstep (se 1 (by rfl) ⟨3826088, by rfl⟩ : syracuseStep 5101451 = 7652177) B7652177
theorem B1791911 : Blo 1790096 1791911 := bstep (se 1 (by rfl) ⟨1343933, by rfl⟩ : syracuseStep 1791911 = 2687867) B2687867
theorem B10336247 : Blo 1790096 10336247 := bstep (se 1 (by rfl) ⟨7752185, by rfl⟩ : syracuseStep 10336247 = 15504371) B15504371
theorem B1791995 : Blo 1790096 1791995 := bstep (se 1 (by rfl) ⟨1343996, by rfl⟩ : syracuseStep 1791995 = 2687993) B2687993
theorem B1792031 : Blo 1790096 1792031 := bstep (se 1 (by rfl) ⟨1344023, by rfl⟩ : syracuseStep 1792031 = 2688047) B2688047
theorem B11475371 : Blo 1790096 11475371 := bstep (se 1 (by rfl) ⟨8606528, by rfl⟩ : syracuseStep 11475371 = 17213057) B17213057
theorem B6044111 : Blo 1790096 6044111 := bstep (se 1 (by rfl) ⟨4533083, by rfl⟩ : syracuseStep 6044111 = 9066167) B9066167
theorem B4028903 : Blo 1790096 4028903 := bstep (se 1 (by rfl) ⟨3021677, by rfl⟩ : syracuseStep 4028903 = 6043355) B6043355
theorem B6797803 : Blo 1790096 6797803 := bstep (se 1 (by rfl) ⟨5098352, by rfl⟩ : syracuseStep 6797803 = 10196705) B10196705
theorem B17439293 : Blo 1790096 17439293 := bstep (se 3 (by rfl) ⟨3269867, by rfl⟩ : syracuseStep 17439293 = 6539735) B6539735
theorem B2685647 : Blo 1790096 2685647 := bstep (se 1 (by rfl) ⟨2014235, by rfl⟩ : syracuseStep 2685647 = 4028471) B4028471
theorem B12254023 : Blo 1790096 12254023 := bstep (se 1 (by rfl) ⟨9190517, by rfl⟩ : syracuseStep 12254023 = 18381035) B18381035
theorem B2685833 : Blo 1790096 2685833 := bstep (se 2 (by rfl) ⟨1007187, by rfl⟩ : syracuseStep 2685833 = 2014375) B2014375
theorem B4086665 : Blo 1790096 4086665 := bstep (se 2 (by rfl) ⟨1532499, by rfl⟩ : syracuseStep 4086665 = 3064999) B3064999
theorem B2685887 : Blo 1790096 2685887 := bstep (se 1 (by rfl) ⟨2014415, by rfl⟩ : syracuseStep 2685887 = 4028831) B4028831
theorem B10337489 : Blo 1790096 10337489 := bstep (se 2 (by rfl) ⟨3876558, by rfl⟩ : syracuseStep 10337489 = 7753117) B7753117
theorem B2014447 : Blo 1790096 2014447 := bstep (se 1 (by rfl) ⟨1510835, by rfl⟩ : syracuseStep 2014447 = 3021671) B3021671
theorem B147111335 : Blo 1790096 147111335 := bstep (se 1 (by rfl) ⟨110333501, by rfl⟩ : syracuseStep 147111335 = 220667003) B220667003
theorem B4029929 : Blo 1790096 4029929 := bstep (se 2 (by rfl) ⟨1511223, by rfl⟩ : syracuseStep 4029929 = 3022447) B3022447
theorem B29064683 : Blo 1790096 29064683 := bstep (se 1 (by rfl) ⟨21798512, by rfl⟩ : syracuseStep 29064683 = 43597025) B43597025
theorem B10198619 : Blo 1790096 10198619 := bstep (se 1 (by rfl) ⟨7648964, by rfl⟩ : syracuseStep 10198619 = 15297929) B15297929
theorem B4030055 : Blo 1790096 4030055 := bstep (se 1 (by rfl) ⟨3022541, by rfl⟩ : syracuseStep 4030055 = 6045083) B6045083
theorem B3022751 : Blo 1790096 3022751 := bstep (se 1 (by rfl) ⟨2267063, by rfl⟩ : syracuseStep 3022751 = 4534127) B4534127
theorem B3399707 : Blo 1790096 3399707 := bstep (se 1 (by rfl) ⟨2549780, by rfl⟩ : syracuseStep 3399707 = 5099561) B5099561
theorem B4030559 : Blo 1790096 4030559 := bstep (se 1 (by rfl) ⟨3022919, by rfl⟩ : syracuseStep 4030559 = 6045839) B6045839
theorem B2687135 : Blo 1790096 2687135 := bstep (se 1 (by rfl) ⟨2015351, by rfl⟩ : syracuseStep 2687135 = 4030703) B4030703
theorem B4030631 : Blo 1790096 4030631 := bstep (se 1 (by rfl) ⟨3022973, by rfl⟩ : syracuseStep 4030631 = 6045947) B6045947
theorem B15516625 : Blo 1790096 15516625 := bstep (se 2 (by rfl) ⟨5818734, by rfl⟩ : syracuseStep 15516625 = 11637469) B11637469
theorem B2688095 : Blo 1790096 2688095 := bstep (se 1 (by rfl) ⟨2016071, by rfl⟩ : syracuseStep 2688095 = 4032143) B4032143
theorem B7652519 : Blo 1790096 7652519 := bstep (se 1 (by rfl) ⟨5739389, by rfl⟩ : syracuseStep 7652519 = 11478779) B11478779
theorem B3400967 : Blo 1790096 3400967 := bstep (se 1 (by rfl) ⟨2550725, by rfl⟩ : syracuseStep 3400967 = 5101451) B5101451
theorem B20407625 : Blo 1790096 20407625 := bstep (se 2 (by rfl) ⟨7652859, by rfl⟩ : syracuseStep 20407625 = 15305719) B15305719
theorem B6890831 : Blo 1790096 6890831 := bstep (se 1 (by rfl) ⟨5168123, by rfl⟩ : syracuseStep 6890831 = 10336247) B10336247
theorem B11626195 : Blo 1790096 11626195 := bstep (se 1 (by rfl) ⟨8719646, by rfl⟩ : syracuseStep 11626195 = 17439293) B17439293
theorem B17680457 : Blo 1790096 17680457 := bstep (se 2 (by rfl) ⟨6630171, by rfl⟩ : syracuseStep 17680457 = 13260343) B13260343
theorem B9685115 : Blo 1790096 9685115 := bstep (se 1 (by rfl) ⟨7263836, by rfl⟩ : syracuseStep 9685115 = 14527673) B14527673
theorem B6891659 : Blo 1790096 6891659 := bstep (se 1 (by rfl) ⟨5168744, by rfl⟩ : syracuseStep 6891659 = 10337489) B10337489
theorem B6047999 : Blo 1790096 6047999 := bstep (se 1 (by rfl) ⟨4535999, by rfl⟩ : syracuseStep 6047999 = 9071999) B9071999
theorem B19376455 : Blo 1790096 19376455 := bstep (se 1 (by rfl) ⟨14532341, by rfl⟩ : syracuseStep 19376455 = 29064683) B29064683
theorem B11479805 : Blo 1790096 11479805 := bstep (se 3 (by rfl) ⟨2152463, by rfl⟩ : syracuseStep 11479805 = 4304927) B4304927
theorem B6540043 : Blo 1790096 6540043 := bstep (se 1 (by rfl) ⟨4905032, by rfl⟩ : syracuseStep 6540043 = 9810065) B9810065
theorem B9071675 : Blo 1790096 9071675 := bstep (se 1 (by rfl) ⟨6803756, by rfl⟩ : syracuseStep 9071675 = 13607513) B13607513
theorem B9063737 : Blo 1790096 9063737 := bstep (se 2 (by rfl) ⟨3398901, by rfl⟩ : syracuseStep 9063737 = 6797803) B6797803
theorem B12905897 : Blo 1790096 12905897 := bstep (se 2 (by rfl) ⟨4839711, by rfl⟩ : syracuseStep 12905897 = 9679423) B9679423
theorem B4534319 : Blo 1790096 4534319 := bstep (se 1 (by rfl) ⟨3400739, by rfl⟩ : syracuseStep 4534319 = 6801479) B6801479
theorem B25809029 : Blo 1790096 25809029 := bstep (se 4 (by rfl) ⟨2419596, by rfl⟩ : syracuseStep 25809029 = 4839193) B4839193
theorem B1790431 : Blo 1790096 1790431 := bstep (se 1 (by rfl) ⟨1342823, by rfl⟩ : syracuseStep 1790431 = 2685647) B2685647
theorem B1790555 : Blo 1790096 1790555 := bstep (se 1 (by rfl) ⟨1342916, by rfl⟩ : syracuseStep 1790555 = 2685833) B2685833
theorem B2724443 : Blo 1790096 2724443 := bstep (se 1 (by rfl) ⟨2043332, by rfl⟩ : syracuseStep 2724443 = 4086665) B4086665
theorem B1790591 : Blo 1790096 1790591 := bstep (se 1 (by rfl) ⟨1342943, by rfl⟩ : syracuseStep 1790591 = 2685887) B2685887
theorem B62059283 : Blo 1790096 62059283 := bstep (se 1 (by rfl) ⟨46544462, by rfl⟩ : syracuseStep 62059283 = 93088925) B93088925
theorem B15299705 : Blo 1790096 15299705 := bstep (se 2 (by rfl) ⟨5737389, by rfl⟩ : syracuseStep 15299705 = 11474779) B11474779
theorem B4027823 : Blo 1790096 4027823 := bstep (se 1 (by rfl) ⟨3020867, by rfl⟩ : syracuseStep 4027823 = 6041735) B6041735
theorem B4027895 : Blo 1790096 4027895 := bstep (se 1 (by rfl) ⟨3020921, by rfl⟩ : syracuseStep 4027895 = 6041843) B6041843
theorem B4027931 : Blo 1790096 4027931 := bstep (se 1 (by rfl) ⟨3020948, by rfl⟩ : syracuseStep 4027931 = 6041897) B6041897
theorem B6796831 : Blo 1790096 6796831 := bstep (se 1 (by rfl) ⟨5097623, by rfl⟩ : syracuseStep 6796831 = 10195247) B10195247
theorem B4027967 : Blo 1790096 4027967 := bstep (se 1 (by rfl) ⟨3020975, by rfl⟩ : syracuseStep 4027967 = 6041951) B6041951
theorem B18634319 : Blo 1790096 18634319 := bstep (se 1 (by rfl) ⟨13975739, by rfl⟩ : syracuseStep 18634319 = 27951479) B27951479
theorem B18389209 : Blo 1790096 18389209 := bstep (se 2 (by rfl) ⟨6895953, by rfl⟩ : syracuseStep 18389209 = 13791907) B13791907
theorem B3021023 : Blo 1790096 3021023 := bstep (se 1 (by rfl) ⟨2265767, by rfl⟩ : syracuseStep 3021023 = 4531535) B4531535
theorem B157006187 : Blo 1790096 157006187 := bstep (se 1 (by rfl) ⟨117754640, by rfl⟩ : syracuseStep 157006187 = 235509281) B235509281
theorem B10197413 : Blo 1790096 10197413 := bstep (se 4 (by rfl) ⟨956007, by rfl⟩ : syracuseStep 10197413 = 1912015) B1912015
theorem B9681371 : Blo 1790096 9681371 := bstep (se 1 (by rfl) ⟨7261028, by rfl⟩ : syracuseStep 9681371 = 14522057) B14522057
theorem B7650247 : Blo 1790096 7650247 := bstep (se 1 (by rfl) ⟨5737685, by rfl⟩ : syracuseStep 7650247 = 11475371) B11475371
theorem B9067463 : Blo 1790096 9067463 := bstep (se 1 (by rfl) ⟨6800597, by rfl⟩ : syracuseStep 9067463 = 13601195) B13601195
theorem B4029407 : Blo 1790096 4029407 := bstep (se 1 (by rfl) ⟨3022055, by rfl⟩ : syracuseStep 4029407 = 6044111) B6044111
theorem B2685929 : Blo 1790096 2685929 := bstep (se 2 (by rfl) ⟨1007223, by rfl⟩ : syracuseStep 2685929 = 2014447) B2014447
theorem B2685935 : Blo 1790096 2685935 := bstep (se 1 (by rfl) ⟨2014451, by rfl⟩ : syracuseStep 2685935 = 4028903) B4028903
theorem B65354789 : Blo 1790096 65354789 := bstep (se 4 (by rfl) ⟨6127011, by rfl⟩ : syracuseStep 65354789 = 12254023) B12254023
theorem B3021887 : Blo 1790096 3021887 := bstep (se 1 (by rfl) ⟨2266415, by rfl⟩ : syracuseStep 3021887 = 4532831) B4532831
theorem B98074223 : Blo 1790096 98074223 := bstep (se 1 (by rfl) ⟨73555667, by rfl⟩ : syracuseStep 98074223 = 147111335) B147111335
theorem B2686619 : Blo 1790096 2686619 := bstep (se 1 (by rfl) ⟨2014964, by rfl⟩ : syracuseStep 2686619 = 4029929) B4029929
theorem B4841183 : Blo 1790096 4841183 := bstep (se 1 (by rfl) ⟨3630887, by rfl⟩ : syracuseStep 4841183 = 7261775) B7261775
theorem B6799079 : Blo 1790096 6799079 := bstep (se 1 (by rfl) ⟨5099309, by rfl⟩ : syracuseStep 6799079 = 10198619) B10198619
theorem B2686703 : Blo 1790096 2686703 := bstep (se 1 (by rfl) ⟨2015027, by rfl⟩ : syracuseStep 2686703 = 4030055) B4030055
theorem B2015167 : Blo 1790096 2015167 := bstep (se 1 (by rfl) ⟨1511375, by rfl⟩ : syracuseStep 2015167 = 3022751) B3022751
theorem B3022879 : Blo 1790096 3022879 := bstep (se 1 (by rfl) ⟨2267159, by rfl⟩ : syracuseStep 3022879 = 4534319) B4534319
theorem B2687039 : Blo 1790096 2687039 := bstep (se 1 (by rfl) ⟨2015279, by rfl⟩ : syracuseStep 2687039 = 4030559) B4030559
theorem B2687087 : Blo 1790096 2687087 := bstep (se 1 (by rfl) ⟨2015315, by rfl⟩ : syracuseStep 2687087 = 4030631) B4030631
theorem B24518945 : Blo 1790096 24518945 := bstep (se 2 (by rfl) ⟨9194604, by rfl⟩ : syracuseStep 24518945 = 18389209) B18389209
theorem B9069245 : Blo 1790096 9069245 := bstep (se 3 (by rfl) ⟨1700483, by rfl⟩ : syracuseStep 9069245 = 3400967) B3400967
theorem B10199803 : Blo 1790096 10199803 := bstep (se 1 (by rfl) ⟨7649852, by rfl⟩ : syracuseStep 10199803 = 15299705) B15299705
theorem B34415725 : Blo 1790096 34415725 := bstep (se 3 (by rfl) ⟨6452948, by rfl⟩ : syracuseStep 34415725 = 12905897) B12905897
theorem B10200329 : Blo 1790096 10200329 := bstep (se 2 (by rfl) ⟨3825123, by rfl⟩ : syracuseStep 10200329 = 7650247) B7650247
theorem B6456743 : Blo 1790096 6456743 := bstep (se 1 (by rfl) ⟨4842557, by rfl⟩ : syracuseStep 6456743 = 9685115) B9685115
theorem B4031999 : Blo 1790096 4031999 := bstep (se 1 (by rfl) ⟨3023999, by rfl⟩ : syracuseStep 4031999 = 6047999) B6047999
theorem B104670791 : Blo 1790096 104670791 := bstep (se 1 (by rfl) ⟨78503093, by rfl⟩ : syracuseStep 104670791 = 157006187) B157006187
theorem B7653203 : Blo 1790096 7653203 := bstep (se 1 (by rfl) ⟨5739902, by rfl⟩ : syracuseStep 7653203 = 11479805) B11479805
theorem B6047783 : Blo 1790096 6047783 := bstep (se 1 (by rfl) ⟨4535837, by rfl⟩ : syracuseStep 6047783 = 9071675) B9071675
theorem B9062441 : Blo 1790096 9062441 := bstep (se 2 (by rfl) ⟨3398415, by rfl⟩ : syracuseStep 9062441 = 6796831) B6796831
theorem B15501593 : Blo 1790096 15501593 := bstep (se 2 (by rfl) ⟨5813097, by rfl⟩ : syracuseStep 15501593 = 11626195) B11626195
theorem B65382815 : Blo 1790096 65382815 := bstep (se 1 (by rfl) ⟨49037111, by rfl⟩ : syracuseStep 65382815 = 98074223) B98074223
theorem B4532719 : Blo 1790096 4532719 := bstep (se 1 (by rfl) ⟨3399539, by rfl⟩ : syracuseStep 4532719 = 6799079) B6799079
theorem B17206019 : Blo 1790096 17206019 := bstep (se 1 (by rfl) ⟨12904514, by rfl⟩ : syracuseStep 17206019 = 25809029) B25809029
theorem B41372855 : Blo 1790096 41372855 := bstep (se 1 (by rfl) ⟨31029641, by rfl⟩ : syracuseStep 41372855 = 62059283) B62059283
theorem B8720057 : Blo 1790096 8720057 := bstep (se 2 (by rfl) ⟨3270021, by rfl⟩ : syracuseStep 8720057 = 6540043) B6540043
theorem B12422879 : Blo 1790096 12422879 := bstep (se 1 (by rfl) ⟨9317159, by rfl⟩ : syracuseStep 12422879 = 18634319) B18634319
theorem B20688833 : Blo 1790096 20688833 := bstep (se 2 (by rfl) ⟨7758312, by rfl⟩ : syracuseStep 20688833 = 15516625) B15516625
theorem B1790619 : Blo 1790096 1790619 := bstep (se 1 (by rfl) ⟨1342964, by rfl⟩ : syracuseStep 1790619 = 2685929) B2685929
theorem B1790623 : Blo 1790096 1790623 := bstep (se 1 (by rfl) ⟨1342967, by rfl⟩ : syracuseStep 1790623 = 2685935) B2685935
theorem B43569859 : Blo 1790096 43569859 := bstep (se 1 (by rfl) ⟨32677394, by rfl⟩ : syracuseStep 43569859 = 65354789) B65354789
theorem B6042491 : Blo 1790096 6042491 := bstep (se 1 (by rfl) ⟨4531868, by rfl⟩ : syracuseStep 6042491 = 9063737) B9063737
theorem B1791079 : Blo 1790096 1791079 := bstep (se 1 (by rfl) ⟨1343309, by rfl⟩ : syracuseStep 1791079 = 2686619) B2686619
theorem B1791135 : Blo 1790096 1791135 := bstep (se 1 (by rfl) ⟨1343351, by rfl⟩ : syracuseStep 1791135 = 2686703) B2686703
theorem B2266471 : Blo 1790096 2266471 := bstep (se 1 (by rfl) ⟨1699853, by rfl⟩ : syracuseStep 2266471 = 3399707) B3399707
theorem B1791423 : Blo 1790096 1791423 := bstep (se 1 (by rfl) ⟨1343567, by rfl⟩ : syracuseStep 1791423 = 2687135) B2687135
theorem B1816295 : Blo 1790096 1816295 := bstep (se 1 (by rfl) ⟨1362221, by rfl⟩ : syracuseStep 1816295 = 2724443) B2724443
theorem B25835273 : Blo 1790096 25835273 := bstep (se 2 (by rfl) ⟨9688227, by rfl⟩ : syracuseStep 25835273 = 19376455) B19376455
theorem B1792063 : Blo 1790096 1792063 := bstep (se 1 (by rfl) ⟨1344047, by rfl⟩ : syracuseStep 1792063 = 2688095) B2688095
theorem B5101679 : Blo 1790096 5101679 := bstep (se 1 (by rfl) ⟨3826259, by rfl⟩ : syracuseStep 5101679 = 7652519) B7652519
theorem B13605083 : Blo 1790096 13605083 := bstep (se 1 (by rfl) ⟨10203812, by rfl⟩ : syracuseStep 13605083 = 20407625) B20407625
theorem B4593887 : Blo 1790096 4593887 := bstep (se 1 (by rfl) ⟨3445415, by rfl⟩ : syracuseStep 4593887 = 6890831) B6890831
theorem B2685215 : Blo 1790096 2685215 := bstep (se 1 (by rfl) ⟨2013911, by rfl⟩ : syracuseStep 2685215 = 4027823) B4027823
theorem B2685263 : Blo 1790096 2685263 := bstep (se 1 (by rfl) ⟨2013947, by rfl⟩ : syracuseStep 2685263 = 4027895) B4027895
theorem B2685287 : Blo 1790096 2685287 := bstep (se 1 (by rfl) ⟨2013965, by rfl⟩ : syracuseStep 2685287 = 4027931) B4027931
theorem B2685311 : Blo 1790096 2685311 := bstep (se 1 (by rfl) ⟨2013983, by rfl⟩ : syracuseStep 2685311 = 4027967) B4027967
theorem B11786971 : Blo 1790096 11786971 := bstep (se 1 (by rfl) ⟨8840228, by rfl⟩ : syracuseStep 11786971 = 17680457) B17680457
theorem B4594439 : Blo 1790096 4594439 := bstep (se 1 (by rfl) ⟨3445829, by rfl⟩ : syracuseStep 4594439 = 6891659) B6891659
theorem B2014015 : Blo 1790096 2014015 := bstep (se 1 (by rfl) ⟨1510511, by rfl⟩ : syracuseStep 2014015 = 3021023) B3021023
theorem B6798275 : Blo 1790096 6798275 := bstep (se 1 (by rfl) ⟨5098706, by rfl⟩ : syracuseStep 6798275 = 10197413) B10197413
theorem B6454247 : Blo 1790096 6454247 := bstep (se 1 (by rfl) ⟨4840685, by rfl⟩ : syracuseStep 6454247 = 9681371) B9681371
theorem B6044975 : Blo 1790096 6044975 := bstep (se 1 (by rfl) ⟨4533731, by rfl⟩ : syracuseStep 6044975 = 9067463) B9067463
theorem B2686271 : Blo 1790096 2686271 := bstep (se 1 (by rfl) ⟨2014703, by rfl⟩ : syracuseStep 2686271 = 4029407) B4029407
theorem B2014591 : Blo 1790096 2014591 := bstep (se 1 (by rfl) ⟨1510943, by rfl⟩ : syracuseStep 2014591 = 3021887) B3021887
theorem B3227455 : Blo 1790096 3227455 := bstep (se 1 (by rfl) ⟨2420591, by rfl⟩ : syracuseStep 3227455 = 4841183) B4841183
theorem B2686889 : Blo 1790096 2686889 := bstep (se 2 (by rfl) ⟨1007583, by rfl⟩ : syracuseStep 2686889 = 2015167) B2015167
theorem B4030505 : Blo 1790096 4030505 := bstep (se 2 (by rfl) ⟨1511439, by rfl⟩ : syracuseStep 4030505 = 3022879) B3022879
theorem B6046163 : Blo 1790096 6046163 := bstep (se 1 (by rfl) ⟨4534622, by rfl⟩ : syracuseStep 6046163 = 9069245) B9069245
theorem B6800219 : Blo 1790096 6800219 := bstep (se 1 (by rfl) ⟨5100164, by rfl⟩ : syracuseStep 6800219 = 10200329) B10200329
theorem B13599737 : Blo 1790096 13599737 := bstep (se 2 (by rfl) ⟨5099901, by rfl⟩ : syracuseStep 13599737 = 10199803) B10199803
theorem B2687999 : Blo 1790096 2687999 := bstep (se 1 (by rfl) ⟨2015999, by rfl⟩ : syracuseStep 2687999 = 4031999) B4031999
theorem B69780527 : Blo 1790096 69780527 := bstep (se 1 (by rfl) ⟨52335395, by rfl⟩ : syracuseStep 69780527 = 104670791) B104670791
theorem B4031855 : Blo 1790096 4031855 := bstep (se 1 (by rfl) ⟨3023891, by rfl⟩ : syracuseStep 4031855 = 6047783) B6047783
theorem B3401119 : Blo 1790096 3401119 := bstep (se 1 (by rfl) ⟨2550839, by rfl⟩ : syracuseStep 3401119 = 5101679) B5101679
theorem B9070055 : Blo 1790096 9070055 := bstep (se 1 (by rfl) ⟨6802541, by rfl⟩ : syracuseStep 9070055 = 13605083) B13605083
theorem B17213093 : Blo 1790096 17213093 := bstep (se 4 (by rfl) ⟨1613727, by rfl⟩ : syracuseStep 17213093 = 3227455) B3227455
theorem B11470679 : Blo 1790096 11470679 := bstep (se 1 (by rfl) ⟨8603009, by rfl⟩ : syracuseStep 11470679 = 17206019) B17206019
theorem B4532183 : Blo 1790096 4532183 := bstep (se 1 (by rfl) ⟨3399137, by rfl⟩ : syracuseStep 4532183 = 6798275) B6798275
theorem B16345963 : Blo 1790096 16345963 := bstep (se 1 (by rfl) ⟨12259472, by rfl⟩ : syracuseStep 16345963 = 24518945) B24518945
theorem B58093145 : Blo 1790096 58093145 := bstep (se 2 (by rfl) ⟨21784929, by rfl⟩ : syracuseStep 58093145 = 43569859) B43569859
theorem B4304495 : Blo 1790096 4304495 := bstep (se 1 (by rfl) ⟨3228371, by rfl⟩ : syracuseStep 4304495 = 6456743) B6456743
theorem B15715961 : Blo 1790096 15715961 := bstep (se 2 (by rfl) ⟨5893485, by rfl⟩ : syracuseStep 15715961 = 11786971) B11786971
theorem B17223515 : Blo 1790096 17223515 := bstep (se 1 (by rfl) ⟨12917636, by rfl⟩ : syracuseStep 17223515 = 25835273) B25835273
theorem B6041627 : Blo 1790096 6041627 := bstep (se 1 (by rfl) ⟨4531220, by rfl⟩ : syracuseStep 6041627 = 9062441) B9062441
theorem B45887633 : Blo 1790096 45887633 := bstep (se 2 (by rfl) ⟨17207862, by rfl⟩ : syracuseStep 45887633 = 34415725) B34415725
theorem B10334395 : Blo 1790096 10334395 := bstep (se 1 (by rfl) ⟨7750796, by rfl⟩ : syracuseStep 10334395 = 15501593) B15501593
theorem B1790143 : Blo 1790096 1790143 := bstep (se 1 (by rfl) ⟨1342607, by rfl⟩ : syracuseStep 1790143 = 2685215) B2685215
theorem B1790175 : Blo 1790096 1790175 := bstep (se 1 (by rfl) ⟨1342631, by rfl⟩ : syracuseStep 1790175 = 2685263) B2685263
theorem B1790191 : Blo 1790096 1790191 := bstep (se 1 (by rfl) ⟨1342643, by rfl⟩ : syracuseStep 1790191 = 2685287) B2685287
theorem B1790207 : Blo 1790096 1790207 := bstep (se 1 (by rfl) ⟨1342655, by rfl⟩ : syracuseStep 1790207 = 2685311) B2685311
theorem B12251837 : Blo 1790096 12251837 := bstep (se 3 (by rfl) ⟨2297219, by rfl⟩ : syracuseStep 12251837 = 4594439) B4594439
theorem B1790847 : Blo 1790096 1790847 := bstep (se 1 (by rfl) ⟨1343135, by rfl⟩ : syracuseStep 1790847 = 2686271) B2686271
theorem B5813371 : Blo 1790096 5813371 := bstep (se 1 (by rfl) ⟨4360028, by rfl⟩ : syracuseStep 5813371 = 8720057) B8720057
theorem B1791259 : Blo 1790096 1791259 := bstep (se 1 (by rfl) ⟨1343444, by rfl⟩ : syracuseStep 1791259 = 2686889) B2686889
theorem B13792555 : Blo 1790096 13792555 := bstep (se 1 (by rfl) ⟨10344416, by rfl⟩ : syracuseStep 13792555 = 20688833) B20688833
theorem B1791359 : Blo 1790096 1791359 := bstep (se 1 (by rfl) ⟨1343519, by rfl⟩ : syracuseStep 1791359 = 2687039) B2687039
theorem B1791391 : Blo 1790096 1791391 := bstep (se 1 (by rfl) ⟨1343543, by rfl⟩ : syracuseStep 1791391 = 2687087) B2687087
theorem B4028327 : Blo 1790096 4028327 := bstep (se 1 (by rfl) ⟨3021245, by rfl⟩ : syracuseStep 4028327 = 6042491) B6042491
theorem B6043625 : Blo 1790096 6043625 := bstep (se 2 (by rfl) ⟨2266359, by rfl⟩ : syracuseStep 6043625 = 4532719) B4532719
theorem B2685353 : Blo 1790096 2685353 := bstep (se 2 (by rfl) ⟨1007007, by rfl⟩ : syracuseStep 2685353 = 2014015) B2014015
theorem B5102135 : Blo 1790096 5102135 := bstep (se 1 (by rfl) ⟨3826601, by rfl⟩ : syracuseStep 5102135 = 7653203) B7653203
theorem B3062591 : Blo 1790096 3062591 := bstep (se 1 (by rfl) ⟨2296943, by rfl⟩ : syracuseStep 3062591 = 4593887) B4593887
theorem B43588543 : Blo 1790096 43588543 := bstep (se 1 (by rfl) ⟨32691407, by rfl⟩ : syracuseStep 43588543 = 65382815) B65382815
theorem B3021961 : Blo 1790096 3021961 := bstep (se 2 (by rfl) ⟨1133235, by rfl⟩ : syracuseStep 3021961 = 2266471) B2266471
theorem B2686121 : Blo 1790096 2686121 := bstep (se 2 (by rfl) ⟨1007295, by rfl⟩ : syracuseStep 2686121 = 2014591) B2014591
theorem B27581903 : Blo 1790096 27581903 := bstep (se 1 (by rfl) ⟨20686427, by rfl⟩ : syracuseStep 27581903 = 41372855) B41372855
theorem B4029983 : Blo 1790096 4029983 := bstep (se 1 (by rfl) ⟨3022487, by rfl⟩ : syracuseStep 4029983 = 6044975) B6044975
theorem B19373813 : Blo 1790096 19373813 := bstep (se 5 (by rfl) ⟨908147, by rfl⟩ : syracuseStep 19373813 = 1816295) B1816295
theorem B8281919 : Blo 1790096 8281919 := bstep (se 1 (by rfl) ⟨6211439, by rfl⟩ : syracuseStep 8281919 = 12422879) B12422879
theorem B17211325 : Blo 1790096 17211325 := bstep (se 3 (by rfl) ⟨3227123, by rfl⟩ : syracuseStep 17211325 = 6454247) B6454247
theorem B2687003 : Blo 1790096 2687003 := bstep (se 1 (by rfl) ⟨2015252, by rfl⟩ : syracuseStep 2687003 = 4030505) B4030505
theorem B4030775 : Blo 1790096 4030775 := bstep (se 1 (by rfl) ⟨3023081, by rfl⟩ : syracuseStep 4030775 = 6046163) B6046163
theorem B8167891 : Blo 1790096 8167891 := bstep (se 1 (by rfl) ⟨6125918, by rfl⟩ : syracuseStep 8167891 = 12251837) B12251837
theorem B2687903 : Blo 1790096 2687903 := bstep (se 1 (by rfl) ⟨2015927, by rfl⟩ : syracuseStep 2687903 = 4031855) B4031855
theorem B55116773 : Blo 1790096 55116773 := bstep (se 4 (by rfl) ⟨5167197, by rfl⟩ : syracuseStep 55116773 = 10334395) B10334395
theorem B6046703 : Blo 1790096 6046703 := bstep (se 1 (by rfl) ⟨4535027, by rfl⟩ : syracuseStep 6046703 = 9070055) B9070055
theorem B7751161 : Blo 1790096 7751161 := bstep (se 2 (by rfl) ⟨2906685, by rfl⟩ : syracuseStep 7751161 = 5813371) B5813371
theorem B3401423 : Blo 1790096 3401423 := bstep (se 1 (by rfl) ⟨2551067, by rfl⟩ : syracuseStep 3401423 = 5102135) B5102135
theorem B2041727 : Blo 1790096 2041727 := bstep (se 1 (by rfl) ⟨1531295, by rfl⟩ : syracuseStep 2041727 = 3062591) B3062591
theorem B2869663 : Blo 1790096 2869663 := bstep (se 1 (by rfl) ⟨2152247, by rfl⟩ : syracuseStep 2869663 = 4304495) B4304495
theorem B22948433 : Blo 1790096 22948433 := bstep (se 2 (by rfl) ⟨8605662, by rfl⟩ : syracuseStep 22948433 = 17211325) B17211325
theorem B30591755 : Blo 1790096 30591755 := bstep (se 1 (by rfl) ⟨22943816, by rfl⟩ : syracuseStep 30591755 = 45887633) B45887633
theorem B4533479 : Blo 1790096 4533479 := bstep (se 1 (by rfl) ⟨3400109, by rfl⟩ : syracuseStep 4533479 = 6800219) B6800219
theorem B21794617 : Blo 1790096 21794617 := bstep (se 2 (by rfl) ⟨8172981, by rfl⟩ : syracuseStep 21794617 = 16345963) B16345963
theorem B7647119 : Blo 1790096 7647119 := bstep (se 1 (by rfl) ⟨5735339, by rfl⟩ : syracuseStep 7647119 = 11470679) B11470679
theorem B58118057 : Blo 1790096 58118057 := bstep (se 2 (by rfl) ⟨21794271, by rfl⟩ : syracuseStep 58118057 = 43588543) B43588543
theorem B1790235 : Blo 1790096 1790235 := bstep (se 1 (by rfl) ⟨1342676, by rfl⟩ : syracuseStep 1790235 = 2685353) B2685353
theorem B4534825 : Blo 1790096 4534825 := bstep (se 2 (by rfl) ⟨1700559, by rfl⟩ : syracuseStep 4534825 = 3401119) B3401119
theorem B1790747 : Blo 1790096 1790747 := bstep (se 1 (by rfl) ⟨1343060, by rfl⟩ : syracuseStep 1790747 = 2686121) B2686121
theorem B18387935 : Blo 1790096 18387935 := bstep (se 1 (by rfl) ⟨13790951, by rfl⟩ : syracuseStep 18387935 = 27581903) B27581903
theorem B38728763 : Blo 1790096 38728763 := bstep (se 1 (by rfl) ⟨29046572, by rfl⟩ : syracuseStep 38728763 = 58093145) B58093145
theorem B12915875 : Blo 1790096 12915875 := bstep (se 1 (by rfl) ⟨9686906, by rfl⟩ : syracuseStep 12915875 = 19373813) B19373813
theorem B11482343 : Blo 1790096 11482343 := bstep (se 1 (by rfl) ⟨8611757, by rfl⟩ : syracuseStep 11482343 = 17223515) B17223515
theorem B4027751 : Blo 1790096 4027751 := bstep (se 1 (by rfl) ⟨3020813, by rfl⟩ : syracuseStep 4027751 = 6041627) B6041627
theorem B9066491 : Blo 1790096 9066491 := bstep (se 1 (by rfl) ⟨6799868, by rfl⟩ : syracuseStep 9066491 = 13599737) B13599737
theorem B1791999 : Blo 1790096 1791999 := bstep (se 1 (by rfl) ⟨1343999, by rfl⟩ : syracuseStep 1791999 = 2687999) B2687999
theorem B46520351 : Blo 1790096 46520351 := bstep (se 1 (by rfl) ⟨34890263, by rfl⟩ : syracuseStep 46520351 = 69780527) B69780527
theorem B11475395 : Blo 1790096 11475395 := bstep (se 1 (by rfl) ⟨8606546, by rfl⟩ : syracuseStep 11475395 = 17213093) B17213093
theorem B2685551 : Blo 1790096 2685551 := bstep (se 1 (by rfl) ⟨2014163, by rfl⟩ : syracuseStep 2685551 = 4028327) B4028327
theorem B3021455 : Blo 1790096 3021455 := bstep (se 1 (by rfl) ⟨2266091, by rfl⟩ : syracuseStep 3021455 = 4532183) B4532183
theorem B4029083 : Blo 1790096 4029083 := bstep (se 1 (by rfl) ⟨3021812, by rfl⟩ : syracuseStep 4029083 = 6043625) B6043625
theorem B4029281 : Blo 1790096 4029281 := bstep (se 2 (by rfl) ⟨1510980, by rfl⟩ : syracuseStep 4029281 = 3021961) B3021961
theorem B18390073 : Blo 1790096 18390073 := bstep (se 2 (by rfl) ⟨6896277, by rfl⟩ : syracuseStep 18390073 = 13792555) B13792555
theorem B2686655 : Blo 1790096 2686655 := bstep (se 1 (by rfl) ⟨2014991, by rfl⟩ : syracuseStep 2686655 = 4029983) B4029983
theorem B10477307 : Blo 1790096 10477307 := bstep (se 1 (by rfl) ⟨7857980, by rfl⟩ : syracuseStep 10477307 = 15715961) B15715961
theorem B5521279 : Blo 1790096 5521279 := bstep (se 1 (by rfl) ⟨4140959, by rfl⟩ : syracuseStep 5521279 = 8281919) B8281919
theorem B2687183 : Blo 1790096 2687183 := bstep (se 1 (by rfl) ⟨2015387, by rfl⟩ : syracuseStep 2687183 = 4030775) B4030775
theorem B3826217 : Blo 1790096 3826217 := bstep (se 2 (by rfl) ⟨1434831, by rfl⟩ : syracuseStep 3826217 = 2869663) B2869663
theorem B4031135 : Blo 1790096 4031135 := bstep (se 1 (by rfl) ⟨3023351, by rfl⟩ : syracuseStep 4031135 = 6046703) B6046703
theorem B6046433 : Blo 1790096 6046433 := bstep (se 2 (by rfl) ⟨2267412, by rfl⟩ : syracuseStep 6046433 = 4534825) B4534825
theorem B24520097 : Blo 1790096 24520097 := bstep (se 2 (by rfl) ⟨9195036, by rfl⟩ : syracuseStep 24520097 = 18390073) B18390073
theorem B29059489 : Blo 1790096 29059489 := bstep (se 2 (by rfl) ⟨10897308, by rfl⟩ : syracuseStep 29059489 = 21794617) B21794617
theorem B5098079 : Blo 1790096 5098079 := bstep (se 1 (by rfl) ⟨3823559, by rfl⟩ : syracuseStep 5098079 = 7647119) B7647119
theorem B34442333 : Blo 1790096 34442333 := bstep (se 3 (by rfl) ⟨6457937, by rfl⟩ : syracuseStep 34442333 = 12915875) B12915875
theorem B10890521 : Blo 1790096 10890521 := bstep (se 2 (by rfl) ⟨4083945, by rfl⟩ : syracuseStep 10890521 = 8167891) B8167891
theorem B12258623 : Blo 1790096 12258623 := bstep (se 1 (by rfl) ⟨9193967, by rfl⟩ : syracuseStep 12258623 = 18387935) B18387935
theorem B36744515 : Blo 1790096 36744515 := bstep (se 1 (by rfl) ⟨27558386, by rfl⟩ : syracuseStep 36744515 = 55116773) B55116773
theorem B7654895 : Blo 1790096 7654895 := bstep (se 1 (by rfl) ⟨5741171, by rfl⟩ : syracuseStep 7654895 = 11482343) B11482343
theorem B15298955 : Blo 1790096 15298955 := bstep (se 1 (by rfl) ⟨11474216, by rfl⟩ : syracuseStep 15298955 = 22948433) B22948433
theorem B1790367 : Blo 1790096 1790367 := bstep (se 1 (by rfl) ⟨1342775, by rfl⟩ : syracuseStep 1790367 = 2685551) B2685551
theorem B20394503 : Blo 1790096 20394503 := bstep (se 1 (by rfl) ⟨15295877, by rfl⟩ : syracuseStep 20394503 = 30591755) B30591755
theorem B27939485 : Blo 1790096 27939485 := bstep (se 3 (by rfl) ⟨5238653, by rfl⟩ : syracuseStep 27939485 = 10477307) B10477307
theorem B10334881 : Blo 1790096 10334881 := bstep (se 2 (by rfl) ⟨3875580, by rfl⟩ : syracuseStep 10334881 = 7751161) B7751161
theorem B5444605 : Blo 1790096 5444605 := bstep (se 3 (by rfl) ⟨1020863, by rfl⟩ : syracuseStep 5444605 = 2041727) B2041727
theorem B1791103 : Blo 1790096 1791103 := bstep (se 1 (by rfl) ⟨1343327, by rfl⟩ : syracuseStep 1791103 = 2686655) B2686655
theorem B7361705 : Blo 1790096 7361705 := bstep (se 2 (by rfl) ⟨2760639, by rfl⟩ : syracuseStep 7361705 = 5521279) B5521279
theorem B38745371 : Blo 1790096 38745371 := bstep (se 1 (by rfl) ⟨29059028, by rfl⟩ : syracuseStep 38745371 = 58118057) B58118057
theorem B1791335 : Blo 1790096 1791335 := bstep (se 1 (by rfl) ⟨1343501, by rfl⟩ : syracuseStep 1791335 = 2687003) B2687003
theorem B1791935 : Blo 1790096 1791935 := bstep (se 1 (by rfl) ⟨1343951, by rfl⟩ : syracuseStep 1791935 = 2687903) B2687903
theorem B25819175 : Blo 1790096 25819175 := bstep (se 1 (by rfl) ⟨19364381, by rfl⟩ : syracuseStep 25819175 = 38728763) B38728763
theorem B2685167 : Blo 1790096 2685167 := bstep (se 1 (by rfl) ⟨2013875, by rfl⟩ : syracuseStep 2685167 = 4027751) B4027751
theorem B2267615 : Blo 1790096 2267615 := bstep (se 1 (by rfl) ⟨1700711, by rfl⟩ : syracuseStep 2267615 = 3401423) B3401423
theorem B6044327 : Blo 1790096 6044327 := bstep (se 1 (by rfl) ⟨4533245, by rfl⟩ : syracuseStep 6044327 = 9066491) B9066491
theorem B31013567 : Blo 1790096 31013567 := bstep (se 1 (by rfl) ⟨23260175, by rfl⟩ : syracuseStep 31013567 = 46520351) B46520351
theorem B7650263 : Blo 1790096 7650263 := bstep (se 1 (by rfl) ⟨5737697, by rfl⟩ : syracuseStep 7650263 = 11475395) B11475395
theorem B2014303 : Blo 1790096 2014303 := bstep (se 1 (by rfl) ⟨1510727, by rfl⟩ : syracuseStep 2014303 = 3021455) B3021455
theorem B2686055 : Blo 1790096 2686055 := bstep (se 1 (by rfl) ⟨2014541, by rfl⟩ : syracuseStep 2686055 = 4029083) B4029083
theorem B2686187 : Blo 1790096 2686187 := bstep (se 1 (by rfl) ⟨2014640, by rfl⟩ : syracuseStep 2686187 = 4029281) B4029281
theorem B3022319 : Blo 1790096 3022319 := bstep (se 1 (by rfl) ⟨2266739, by rfl⟩ : syracuseStep 3022319 = 4533479) B4533479
theorem B10199303 : Blo 1790096 10199303 := bstep (se 1 (by rfl) ⟨7649477, by rfl⟩ : syracuseStep 10199303 = 15298955) B15298955
theorem B2687423 : Blo 1790096 2687423 := bstep (se 1 (by rfl) ⟨2015567, by rfl⟩ : syracuseStep 2687423 = 4031135) B4031135
theorem B4030955 : Blo 1790096 4030955 := bstep (se 1 (by rfl) ⟨3023216, by rfl⟩ : syracuseStep 4030955 = 6046433) B6046433
theorem B4907803 : Blo 1790096 4907803 := bstep (se 1 (by rfl) ⟨3680852, by rfl⟩ : syracuseStep 4907803 = 7361705) B7361705
theorem B25830247 : Blo 1790096 25830247 := bstep (se 1 (by rfl) ⟨19372685, by rfl⟩ : syracuseStep 25830247 = 38745371) B38745371
theorem B13779841 : Blo 1790096 13779841 := bstep (se 2 (by rfl) ⟨5167440, by rfl⟩ : syracuseStep 13779841 = 10334881) B10334881
theorem B6046973 : Blo 1790096 6046973 := bstep (se 3 (by rfl) ⟨1133807, by rfl⟩ : syracuseStep 6046973 = 2267615) B2267615
theorem B7259473 : Blo 1790096 7259473 := bstep (se 2 (by rfl) ⟨2722302, by rfl⟩ : syracuseStep 7259473 = 5444605) B5444605
theorem B7260347 : Blo 1790096 7260347 := bstep (se 1 (by rfl) ⟨5445260, by rfl⟩ : syracuseStep 7260347 = 10890521) B10890521
theorem B24496343 : Blo 1790096 24496343 := bstep (se 1 (by rfl) ⟨18372257, by rfl⟩ : syracuseStep 24496343 = 36744515) B36744515
theorem B10203245 : Blo 1790096 10203245 := bstep (se 3 (by rfl) ⟨1913108, by rfl⟩ : syracuseStep 10203245 = 3826217) B3826217
theorem B1790111 : Blo 1790096 1790111 := bstep (se 1 (by rfl) ⟨1342583, by rfl⟩ : syracuseStep 1790111 = 2685167) B2685167
theorem B13594877 : Blo 1790096 13594877 := bstep (se 3 (by rfl) ⟨2549039, by rfl⟩ : syracuseStep 13594877 = 5098079) B5098079
theorem B5100175 : Blo 1790096 5100175 := bstep (se 1 (by rfl) ⟨3825131, by rfl⟩ : syracuseStep 5100175 = 7650263) B7650263
theorem B1790703 : Blo 1790096 1790703 := bstep (se 1 (by rfl) ⟨1343027, by rfl⟩ : syracuseStep 1790703 = 2686055) B2686055
theorem B1790791 : Blo 1790096 1790791 := bstep (se 1 (by rfl) ⟨1343093, by rfl⟩ : syracuseStep 1790791 = 2686187) B2686187
theorem B8172415 : Blo 1790096 8172415 := bstep (se 1 (by rfl) ⟨6129311, by rfl⟩ : syracuseStep 8172415 = 12258623) B12258623
theorem B68851133 : Blo 1790096 68851133 := bstep (se 3 (by rfl) ⟨12909587, by rfl⟩ : syracuseStep 68851133 = 25819175) B25819175
theorem B1791455 : Blo 1790096 1791455 := bstep (se 1 (by rfl) ⟨1343591, by rfl⟩ : syracuseStep 1791455 = 2687183) B2687183
theorem B13596335 : Blo 1790096 13596335 := bstep (se 1 (by rfl) ⟨10197251, by rfl⟩ : syracuseStep 13596335 = 20394503) B20394503
theorem B18626323 : Blo 1790096 18626323 := bstep (se 1 (by rfl) ⟨13969742, by rfl⟩ : syracuseStep 18626323 = 27939485) B27939485
theorem B38745985 : Blo 1790096 38745985 := bstep (se 2 (by rfl) ⟨14529744, by rfl⟩ : syracuseStep 38745985 = 29059489) B29059489
theorem B65386925 : Blo 1790096 65386925 := bstep (se 3 (by rfl) ⟨12260048, by rfl⟩ : syracuseStep 65386925 = 24520097) B24520097
theorem B2685737 : Blo 1790096 2685737 := bstep (se 2 (by rfl) ⟨1007151, by rfl⟩ : syracuseStep 2685737 = 2014303) B2014303
theorem B4029551 : Blo 1790096 4029551 := bstep (se 1 (by rfl) ⟨3022163, by rfl⟩ : syracuseStep 4029551 = 6044327) B6044327
theorem B20675711 : Blo 1790096 20675711 := bstep (se 1 (by rfl) ⟨15506783, by rfl⟩ : syracuseStep 20675711 = 31013567) B31013567
theorem B22961555 : Blo 1790096 22961555 := bstep (se 1 (by rfl) ⟨17221166, by rfl⟩ : syracuseStep 22961555 = 34442333) B34442333
theorem B2014879 : Blo 1790096 2014879 := bstep (se 1 (by rfl) ⟨1511159, by rfl⟩ : syracuseStep 2014879 = 3022319) B3022319
theorem B5103263 : Blo 1790096 5103263 := bstep (se 1 (by rfl) ⟨3827447, by rfl⟩ : syracuseStep 5103263 = 7654895) B7654895
theorem B6799535 : Blo 1790096 6799535 := bstep (se 1 (by rfl) ⟨5099651, by rfl⟩ : syracuseStep 6799535 = 10199303) B10199303
theorem B2687303 : Blo 1790096 2687303 := bstep (se 1 (by rfl) ⟨2015477, by rfl⟩ : syracuseStep 2687303 = 4030955) B4030955
theorem B4031315 : Blo 1790096 4031315 := bstep (se 1 (by rfl) ⟨3023486, by rfl⟩ : syracuseStep 4031315 = 6046973) B6046973
theorem B6800233 : Blo 1790096 6800233 := bstep (se 2 (by rfl) ⟨2550087, by rfl⟩ : syracuseStep 6800233 = 5100175) B5100175
theorem B45900755 : Blo 1790096 45900755 := bstep (se 1 (by rfl) ⟨34425566, by rfl⟩ : syracuseStep 45900755 = 68851133) B68851133
theorem B34440329 : Blo 1790096 34440329 := bstep (se 2 (by rfl) ⟨12915123, by rfl⟩ : syracuseStep 34440329 = 25830247) B25830247
theorem B10896553 : Blo 1790096 10896553 := bstep (se 2 (by rfl) ⟨4086207, by rfl⟩ : syracuseStep 10896553 = 8172415) B8172415
theorem B43591283 : Blo 1790096 43591283 := bstep (se 1 (by rfl) ⟨32693462, by rfl⟩ : syracuseStep 43591283 = 65386925) B65386925
theorem B3402175 : Blo 1790096 3402175 := bstep (se 1 (by rfl) ⟨2551631, by rfl⟩ : syracuseStep 3402175 = 5103263) B5103263
theorem B51661313 : Blo 1790096 51661313 := bstep (se 2 (by rfl) ⟨19372992, by rfl⟩ : syracuseStep 51661313 = 38745985) B38745985
theorem B6802163 : Blo 1790096 6802163 := bstep (se 1 (by rfl) ⟨5101622, by rfl⟩ : syracuseStep 6802163 = 10203245) B10203245
theorem B9063251 : Blo 1790096 9063251 := bstep (se 1 (by rfl) ⟨6797438, by rfl⟩ : syracuseStep 9063251 = 13594877) B13594877
theorem B9064223 : Blo 1790096 9064223 := bstep (se 1 (by rfl) ⟨6798167, by rfl⟩ : syracuseStep 9064223 = 13596335) B13596335
theorem B16330895 : Blo 1790096 16330895 := bstep (se 1 (by rfl) ⟨12248171, by rfl⟩ : syracuseStep 16330895 = 24496343) B24496343
theorem B9679297 : Blo 1790096 9679297 := bstep (se 2 (by rfl) ⟨3629736, by rfl⟩ : syracuseStep 9679297 = 7259473) B7259473
theorem B1790491 : Blo 1790096 1790491 := bstep (se 1 (by rfl) ⟨1342868, by rfl⟩ : syracuseStep 1790491 = 2685737) B2685737
theorem B13783807 : Blo 1790096 13783807 := bstep (se 1 (by rfl) ⟨10337855, by rfl⟩ : syracuseStep 13783807 = 20675711) B20675711
theorem B15307703 : Blo 1790096 15307703 := bstep (se 1 (by rfl) ⟨11480777, by rfl⟩ : syracuseStep 15307703 = 22961555) B22961555
theorem B24835097 : Blo 1790096 24835097 := bstep (se 2 (by rfl) ⟨9313161, by rfl⟩ : syracuseStep 24835097 = 18626323) B18626323
theorem B1791615 : Blo 1790096 1791615 := bstep (se 1 (by rfl) ⟨1343711, by rfl⟩ : syracuseStep 1791615 = 2687423) B2687423
theorem B6543737 : Blo 1790096 6543737 := bstep (se 2 (by rfl) ⟨2453901, by rfl⟩ : syracuseStep 6543737 = 4907803) B4907803
theorem B18373121 : Blo 1790096 18373121 := bstep (se 2 (by rfl) ⟨6889920, by rfl⟩ : syracuseStep 18373121 = 13779841) B13779841
theorem B4840231 : Blo 1790096 4840231 := bstep (se 1 (by rfl) ⟨3630173, by rfl⟩ : syracuseStep 4840231 = 7260347) B7260347
theorem B2686367 : Blo 1790096 2686367 := bstep (se 1 (by rfl) ⟨2014775, by rfl⟩ : syracuseStep 2686367 = 4029551) B4029551
theorem B2686505 : Blo 1790096 2686505 := bstep (se 2 (by rfl) ⟨1007439, by rfl⟩ : syracuseStep 2686505 = 2014879) B2014879
theorem B10887263 : Blo 1790096 10887263 := bstep (se 1 (by rfl) ⟨8165447, by rfl⟩ : syracuseStep 10887263 = 16330895) B16330895
theorem B2687543 : Blo 1790096 2687543 := bstep (se 1 (by rfl) ⟨2015657, by rfl⟩ : syracuseStep 2687543 = 4031315) B4031315
theorem B16556731 : Blo 1790096 16556731 := bstep (se 1 (by rfl) ⟨12417548, by rfl⟩ : syracuseStep 16556731 = 24835097) B24835097
theorem B12248747 : Blo 1790096 12248747 := bstep (se 1 (by rfl) ⟨9186560, by rfl⟩ : syracuseStep 12248747 = 18373121) B18373121
theorem B34440875 : Blo 1790096 34440875 := bstep (se 1 (by rfl) ⟨25830656, by rfl⟩ : syracuseStep 34440875 = 51661313) B51661313
theorem B4533023 : Blo 1790096 4533023 := bstep (se 1 (by rfl) ⟨3399767, by rfl⟩ : syracuseStep 4533023 = 6799535) B6799535
theorem B12905729 : Blo 1790096 12905729 := bstep (se 2 (by rfl) ⟨4839648, by rfl⟩ : syracuseStep 12905729 = 9679297) B9679297
theorem B30600503 : Blo 1790096 30600503 := bstep (se 1 (by rfl) ⟨22950377, by rfl⟩ : syracuseStep 30600503 = 45900755) B45900755
theorem B18378409 : Blo 1790096 18378409 := bstep (se 2 (by rfl) ⟨6891903, by rfl⟩ : syracuseStep 18378409 = 13783807) B13783807
theorem B29060855 : Blo 1790096 29060855 := bstep (se 1 (by rfl) ⟨21795641, by rfl⟩ : syracuseStep 29060855 = 43591283) B43591283
theorem B14528737 : Blo 1790096 14528737 := bstep (se 2 (by rfl) ⟨5448276, by rfl⟩ : syracuseStep 14528737 = 10896553) B10896553
theorem B4362491 : Blo 1790096 4362491 := bstep (se 1 (by rfl) ⟨3271868, by rfl⟩ : syracuseStep 4362491 = 6543737) B6543737
theorem B4534775 : Blo 1790096 4534775 := bstep (se 1 (by rfl) ⟨3401081, by rfl⟩ : syracuseStep 4534775 = 6802163) B6802163
theorem B6042167 : Blo 1790096 6042167 := bstep (se 1 (by rfl) ⟨4531625, by rfl⟩ : syracuseStep 6042167 = 9063251) B9063251
theorem B1790911 : Blo 1790096 1790911 := bstep (se 1 (by rfl) ⟨1343183, by rfl⟩ : syracuseStep 1790911 = 2686367) B2686367
theorem B1791003 : Blo 1790096 1791003 := bstep (se 1 (by rfl) ⟨1343252, by rfl⟩ : syracuseStep 1791003 = 2686505) B2686505
theorem B6042815 : Blo 1790096 6042815 := bstep (se 1 (by rfl) ⟨4532111, by rfl⟩ : syracuseStep 6042815 = 9064223) B9064223
theorem B1791535 : Blo 1790096 1791535 := bstep (se 1 (by rfl) ⟨1343651, by rfl⟩ : syracuseStep 1791535 = 2687303) B2687303
theorem B4536233 : Blo 1790096 4536233 := bstep (se 2 (by rfl) ⟨1701087, by rfl⟩ : syracuseStep 4536233 = 3402175) B3402175
theorem B10205135 : Blo 1790096 10205135 := bstep (se 1 (by rfl) ⟨7653851, by rfl⟩ : syracuseStep 10205135 = 15307703) B15307703
theorem B22960219 : Blo 1790096 22960219 := bstep (se 1 (by rfl) ⟨17220164, by rfl⟩ : syracuseStep 22960219 = 34440329) B34440329
theorem B6453641 : Blo 1790096 6453641 := bstep (se 2 (by rfl) ⟨2420115, by rfl⟩ : syracuseStep 6453641 = 4840231) B4840231
theorem B9066977 : Blo 1790096 9066977 := bstep (se 2 (by rfl) ⟨3400116, by rfl⟩ : syracuseStep 9066977 = 6800233) B6800233
theorem B7258175 : Blo 1790096 7258175 := bstep (se 1 (by rfl) ⟨5443631, by rfl⟩ : syracuseStep 7258175 = 10887263) B10887263
theorem B30613625 : Blo 1790096 30613625 := bstep (se 2 (by rfl) ⟨11480109, by rfl⟩ : syracuseStep 30613625 = 22960219) B22960219
theorem B3023183 : Blo 1790096 3023183 := bstep (se 1 (by rfl) ⟨2267387, by rfl⟩ : syracuseStep 3023183 = 4534775) B4534775
theorem B11633309 : Blo 1790096 11633309 := bstep (se 3 (by rfl) ⟨2181245, by rfl⟩ : syracuseStep 11633309 = 4362491) B4362491
theorem B88302565 : Blo 1790096 88302565 := bstep (se 4 (by rfl) ⟨8278365, by rfl⟩ : syracuseStep 88302565 = 16556731) B16556731
theorem B3024155 : Blo 1790096 3024155 := bstep (se 1 (by rfl) ⟨2268116, by rfl⟩ : syracuseStep 3024155 = 4536233) B4536233
theorem B8603819 : Blo 1790096 8603819 := bstep (se 1 (by rfl) ⟨6452864, by rfl⟩ : syracuseStep 8603819 = 12905729) B12905729
theorem B20400335 : Blo 1790096 20400335 := bstep (se 1 (by rfl) ⟨15300251, by rfl⟩ : syracuseStep 20400335 = 30600503) B30600503
theorem B24504545 : Blo 1790096 24504545 := bstep (se 2 (by rfl) ⟨9189204, by rfl⟩ : syracuseStep 24504545 = 18378409) B18378409
theorem B6803423 : Blo 1790096 6803423 := bstep (se 1 (by rfl) ⟨5102567, by rfl⟩ : syracuseStep 6803423 = 10205135) B10205135
theorem B19371649 : Blo 1790096 19371649 := bstep (se 2 (by rfl) ⟨7264368, by rfl⟩ : syracuseStep 19371649 = 14528737) B14528737
theorem B4028111 : Blo 1790096 4028111 := bstep (se 1 (by rfl) ⟨3021083, by rfl⟩ : syracuseStep 4028111 = 6042167) B6042167
theorem B1791695 : Blo 1790096 1791695 := bstep (se 1 (by rfl) ⟨1343771, by rfl⟩ : syracuseStep 1791695 = 2687543) B2687543
theorem B4028543 : Blo 1790096 4028543 := bstep (se 1 (by rfl) ⟨3021407, by rfl⟩ : syracuseStep 4028543 = 6042815) B6042815
theorem B17209709 : Blo 1790096 17209709 := bstep (se 3 (by rfl) ⟨3226820, by rfl⟩ : syracuseStep 17209709 = 6453641) B6453641
theorem B8165831 : Blo 1790096 8165831 := bstep (se 1 (by rfl) ⟨6124373, by rfl⟩ : syracuseStep 8165831 = 12248747) B12248747
theorem B22960583 : Blo 1790096 22960583 := bstep (se 1 (by rfl) ⟨17220437, by rfl⟩ : syracuseStep 22960583 = 34440875) B34440875
theorem B6044651 : Blo 1790096 6044651 := bstep (se 1 (by rfl) ⟨4533488, by rfl⟩ : syracuseStep 6044651 = 9066977) B9066977
theorem B3022015 : Blo 1790096 3022015 := bstep (se 1 (by rfl) ⟨2266511, by rfl⟩ : syracuseStep 3022015 = 4533023) B4533023
theorem B19373903 : Blo 1790096 19373903 := bstep (se 1 (by rfl) ⟨14530427, by rfl⟩ : syracuseStep 19373903 = 29060855) B29060855
theorem B2015455 : Blo 1790096 2015455 := bstep (se 1 (by rfl) ⟨1511591, by rfl⟩ : syracuseStep 2015455 = 3023183) B3023183
theorem B2016103 : Blo 1790096 2016103 := bstep (se 1 (by rfl) ⟨1512077, by rfl⟩ : syracuseStep 2016103 = 3024155) B3024155
theorem B21775549 : Blo 1790096 21775549 := bstep (se 3 (by rfl) ⟨4082915, by rfl⟩ : syracuseStep 21775549 = 8165831) B8165831
theorem B117736753 : Blo 1790096 117736753 := bstep (se 2 (by rfl) ⟨44151282, by rfl⟩ : syracuseStep 117736753 = 88302565) B88302565
theorem B5735879 : Blo 1790096 5735879 := bstep (se 1 (by rfl) ⟨4301909, by rfl⟩ : syracuseStep 5735879 = 8603819) B8603819
theorem B13600223 : Blo 1790096 13600223 := bstep (se 1 (by rfl) ⟨10200167, by rfl⟩ : syracuseStep 13600223 = 20400335) B20400335
theorem B16336363 : Blo 1790096 16336363 := bstep (se 1 (by rfl) ⟨12252272, by rfl⟩ : syracuseStep 16336363 = 24504545) B24504545
theorem B20409083 : Blo 1790096 20409083 := bstep (se 1 (by rfl) ⟨15306812, by rfl⟩ : syracuseStep 20409083 = 30613625) B30613625
theorem B11473139 : Blo 1790096 11473139 := bstep (se 1 (by rfl) ⟨8604854, by rfl⟩ : syracuseStep 11473139 = 17209709) B17209709
theorem B15307055 : Blo 1790096 15307055 := bstep (se 1 (by rfl) ⟨11480291, by rfl⟩ : syracuseStep 15307055 = 22960583) B22960583
theorem B12915935 : Blo 1790096 12915935 := bstep (se 1 (by rfl) ⟨9686951, by rfl⟩ : syracuseStep 12915935 = 19373903) B19373903
theorem B4535615 : Blo 1790096 4535615 := bstep (se 1 (by rfl) ⟨3401711, by rfl⟩ : syracuseStep 4535615 = 6803423) B6803423
theorem B4838783 : Blo 1790096 4838783 := bstep (se 1 (by rfl) ⟨3629087, by rfl⟩ : syracuseStep 4838783 = 7258175) B7258175
theorem B7755539 : Blo 1790096 7755539 := bstep (se 1 (by rfl) ⟨5816654, by rfl⟩ : syracuseStep 7755539 = 11633309) B11633309
theorem B2685407 : Blo 1790096 2685407 := bstep (se 1 (by rfl) ⟨2014055, by rfl⟩ : syracuseStep 2685407 = 4028111) B4028111
theorem B2685695 : Blo 1790096 2685695 := bstep (se 1 (by rfl) ⟨2014271, by rfl⟩ : syracuseStep 2685695 = 4028543) B4028543
theorem B4029353 : Blo 1790096 4029353 := bstep (se 2 (by rfl) ⟨1511007, by rfl⟩ : syracuseStep 4029353 = 3022015) B3022015
theorem B4029767 : Blo 1790096 4029767 := bstep (se 1 (by rfl) ⟨3022325, by rfl⟩ : syracuseStep 4029767 = 6044651) B6044651
theorem B25828865 : Blo 1790096 25828865 := bstep (se 2 (by rfl) ⟨9685824, by rfl⟩ : syracuseStep 25828865 = 19371649) B19371649
theorem B2687273 : Blo 1790096 2687273 := bstep (se 2 (by rfl) ⟨1007727, by rfl⟩ : syracuseStep 2687273 = 2015455) B2015455
theorem B8610623 : Blo 1790096 8610623 := bstep (se 1 (by rfl) ⟨6457967, by rfl⟩ : syracuseStep 8610623 = 12915935) B12915935
theorem B3023743 : Blo 1790096 3023743 := bstep (se 1 (by rfl) ⟨2267807, by rfl⟩ : syracuseStep 3023743 = 4535615) B4535615
theorem B12903421 : Blo 1790096 12903421 := bstep (se 3 (by rfl) ⟨2419391, by rfl⟩ : syracuseStep 12903421 = 4838783) B4838783
theorem B2688137 : Blo 1790096 2688137 := bstep (se 2 (by rfl) ⟨1008051, by rfl⟩ : syracuseStep 2688137 = 2016103) B2016103
theorem B29034065 : Blo 1790096 29034065 := bstep (se 2 (by rfl) ⟨10887774, by rfl⟩ : syracuseStep 29034065 = 21775549) B21775549
theorem B1790271 : Blo 1790096 1790271 := bstep (se 1 (by rfl) ⟨1342703, by rfl⟩ : syracuseStep 1790271 = 2685407) B2685407
theorem B1790463 : Blo 1790096 1790463 := bstep (se 1 (by rfl) ⟨1342847, by rfl⟩ : syracuseStep 1790463 = 2685695) B2685695
theorem B20681437 : Blo 1790096 20681437 := bstep (se 3 (by rfl) ⟨3877769, by rfl⟩ : syracuseStep 20681437 = 7755539) B7755539
theorem B7648759 : Blo 1790096 7648759 := bstep (se 1 (by rfl) ⟨5736569, by rfl⟩ : syracuseStep 7648759 = 11473139) B11473139
theorem B10204703 : Blo 1790096 10204703 := bstep (se 1 (by rfl) ⟨7653527, by rfl⟩ : syracuseStep 10204703 = 15307055) B15307055
theorem B3823919 : Blo 1790096 3823919 := bstep (se 1 (by rfl) ⟨2867939, by rfl⟩ : syracuseStep 3823919 = 5735879) B5735879
theorem B9066815 : Blo 1790096 9066815 := bstep (se 1 (by rfl) ⟨6800111, by rfl⟩ : syracuseStep 9066815 = 13600223) B13600223
theorem B156982337 : Blo 1790096 156982337 := bstep (se 2 (by rfl) ⟨58868376, by rfl⟩ : syracuseStep 156982337 = 117736753) B117736753
theorem B13606055 : Blo 1790096 13606055 := bstep (se 1 (by rfl) ⟨10204541, by rfl⟩ : syracuseStep 13606055 = 20409083) B20409083
theorem B2686235 : Blo 1790096 2686235 := bstep (se 1 (by rfl) ⟨2014676, by rfl⟩ : syracuseStep 2686235 = 4029353) B4029353
theorem B21781817 : Blo 1790096 21781817 := bstep (se 2 (by rfl) ⟨8168181, by rfl⟩ : syracuseStep 21781817 = 16336363) B16336363
theorem B2686511 : Blo 1790096 2686511 := bstep (se 1 (by rfl) ⟨2014883, by rfl⟩ : syracuseStep 2686511 = 4029767) B4029767
theorem B17219243 : Blo 1790096 17219243 := bstep (se 1 (by rfl) ⟨12914432, by rfl⟩ : syracuseStep 17219243 = 25828865) B25828865
theorem B27575249 : Blo 1790096 27575249 := bstep (se 2 (by rfl) ⟨10340718, by rfl⟩ : syracuseStep 27575249 = 20681437) B20681437
theorem B4031657 : Blo 1790096 4031657 := bstep (se 2 (by rfl) ⟨1511871, by rfl⟩ : syracuseStep 4031657 = 3023743) B3023743
theorem B17204561 : Blo 1790096 17204561 := bstep (se 2 (by rfl) ⟨6451710, by rfl⟩ : syracuseStep 17204561 = 12903421) B12903421
theorem B2549279 : Blo 1790096 2549279 := bstep (se 1 (by rfl) ⟨1911959, by rfl⟩ : syracuseStep 2549279 = 3823919) B3823919
theorem B104654891 : Blo 1790096 104654891 := bstep (se 1 (by rfl) ⟨78491168, by rfl⟩ : syracuseStep 104654891 = 156982337) B156982337
theorem B9070703 : Blo 1790096 9070703 := bstep (se 1 (by rfl) ⟨6803027, by rfl⟩ : syracuseStep 9070703 = 13606055) B13606055
theorem B11479495 : Blo 1790096 11479495 := bstep (se 1 (by rfl) ⟨8609621, by rfl⟩ : syracuseStep 11479495 = 17219243) B17219243
theorem B6803135 : Blo 1790096 6803135 := bstep (se 1 (by rfl) ⟨5102351, by rfl⟩ : syracuseStep 6803135 = 10204703) B10204703
theorem B1790823 : Blo 1790096 1790823 := bstep (se 1 (by rfl) ⟨1343117, by rfl⟩ : syracuseStep 1790823 = 2686235) B2686235
theorem B14521211 : Blo 1790096 14521211 := bstep (se 1 (by rfl) ⟨10890908, by rfl⟩ : syracuseStep 14521211 = 21781817) B21781817
theorem B1791007 : Blo 1790096 1791007 := bstep (se 1 (by rfl) ⟨1343255, by rfl⟩ : syracuseStep 1791007 = 2686511) B2686511
theorem B1791515 : Blo 1790096 1791515 := bstep (se 1 (by rfl) ⟨1343636, by rfl⟩ : syracuseStep 1791515 = 2687273) B2687273
theorem B5740415 : Blo 1790096 5740415 := bstep (se 1 (by rfl) ⟨4305311, by rfl⟩ : syracuseStep 5740415 = 8610623) B8610623
theorem B1792091 : Blo 1790096 1792091 := bstep (se 1 (by rfl) ⟨1344068, by rfl⟩ : syracuseStep 1792091 = 2688137) B2688137
theorem B19356043 : Blo 1790096 19356043 := bstep (se 1 (by rfl) ⟨14517032, by rfl⟩ : syracuseStep 19356043 = 29034065) B29034065
theorem B6044543 : Blo 1790096 6044543 := bstep (se 1 (by rfl) ⟨4533407, by rfl⟩ : syracuseStep 6044543 = 9066815) B9066815
theorem B10198345 : Blo 1790096 10198345 := bstep (se 2 (by rfl) ⟨3824379, by rfl⟩ : syracuseStep 10198345 = 7648759) B7648759
theorem B2687771 : Blo 1790096 2687771 := bstep (se 1 (by rfl) ⟨2015828, by rfl⟩ : syracuseStep 2687771 = 4031657) B4031657
theorem B11469707 : Blo 1790096 11469707 := bstep (se 1 (by rfl) ⟨8602280, by rfl⟩ : syracuseStep 11469707 = 17204561) B17204561
theorem B3826943 : Blo 1790096 3826943 := bstep (se 1 (by rfl) ⟨2870207, by rfl⟩ : syracuseStep 3826943 = 5740415) B5740415
theorem B6047135 : Blo 1790096 6047135 := bstep (se 1 (by rfl) ⟨4535351, by rfl⟩ : syracuseStep 6047135 = 9070703) B9070703
theorem B73533997 : Blo 1790096 73533997 := bstep (se 3 (by rfl) ⟨13787624, by rfl⟩ : syracuseStep 73533997 = 27575249) B27575249
theorem B25808057 : Blo 1790096 25808057 := bstep (se 2 (by rfl) ⟨9678021, by rfl⟩ : syracuseStep 25808057 = 19356043) B19356043
theorem B15305993 : Blo 1790096 15305993 := bstep (se 2 (by rfl) ⟨5739747, by rfl⟩ : syracuseStep 15305993 = 11479495) B11479495
theorem B4535423 : Blo 1790096 4535423 := bstep (se 1 (by rfl) ⟨3401567, by rfl⟩ : syracuseStep 4535423 = 6803135) B6803135
theorem B9680807 : Blo 1790096 9680807 := bstep (se 1 (by rfl) ⟨7260605, by rfl⟩ : syracuseStep 9680807 = 14521211) B14521211
theorem B69769927 : Blo 1790096 69769927 := bstep (se 1 (by rfl) ⟨52327445, by rfl⟩ : syracuseStep 69769927 = 104654891) B104654891
theorem B6798077 : Blo 1790096 6798077 := bstep (se 3 (by rfl) ⟨1274639, by rfl⟩ : syracuseStep 6798077 = 2549279) B2549279
theorem B13597793 : Blo 1790096 13597793 := bstep (se 2 (by rfl) ⟨5099172, by rfl⟩ : syracuseStep 13597793 = 10198345) B10198345
theorem B4029695 : Blo 1790096 4029695 := bstep (se 1 (by rfl) ⟨3022271, by rfl⟩ : syracuseStep 4029695 = 6044543) B6044543
theorem B3023615 : Blo 1790096 3023615 := bstep (se 1 (by rfl) ⟨2267711, by rfl⟩ : syracuseStep 3023615 = 4535423) B4535423
theorem B4031423 : Blo 1790096 4031423 := bstep (se 1 (by rfl) ⟨3023567, by rfl⟩ : syracuseStep 4031423 = 6047135) B6047135
theorem B4532051 : Blo 1790096 4532051 := bstep (se 1 (by rfl) ⟨3399038, by rfl⟩ : syracuseStep 4532051 = 6798077) B6798077
theorem B17205371 : Blo 1790096 17205371 := bstep (se 1 (by rfl) ⟨12904028, by rfl⟩ : syracuseStep 17205371 = 25808057) B25808057
theorem B25815485 : Blo 1790096 25815485 := bstep (se 3 (by rfl) ⟨4840403, by rfl⟩ : syracuseStep 25815485 = 9680807) B9680807
theorem B7646471 : Blo 1790096 7646471 := bstep (se 1 (by rfl) ⟨5734853, by rfl⟩ : syracuseStep 7646471 = 11469707) B11469707
theorem B98045329 : Blo 1790096 98045329 := bstep (se 2 (by rfl) ⟨36766998, by rfl⟩ : syracuseStep 98045329 = 73533997) B73533997
theorem B2551295 : Blo 1790096 2551295 := bstep (se 1 (by rfl) ⟨1913471, by rfl⟩ : syracuseStep 2551295 = 3826943) B3826943
theorem B9065195 : Blo 1790096 9065195 := bstep (se 1 (by rfl) ⟨6798896, by rfl⟩ : syracuseStep 9065195 = 13597793) B13597793
theorem B10203995 : Blo 1790096 10203995 := bstep (se 1 (by rfl) ⟨7652996, by rfl⟩ : syracuseStep 10203995 = 15305993) B15305993
theorem B1791847 : Blo 1790096 1791847 := bstep (se 1 (by rfl) ⟨1343885, by rfl⟩ : syracuseStep 1791847 = 2687771) B2687771
theorem B93026569 : Blo 1790096 93026569 := bstep (se 2 (by rfl) ⟨34884963, by rfl⟩ : syracuseStep 93026569 = 69769927) B69769927
theorem B2686463 : Blo 1790096 2686463 := bstep (se 1 (by rfl) ⟨2014847, by rfl⟩ : syracuseStep 2686463 = 4029695) B4029695
theorem B124035425 : Blo 1790096 124035425 := bstep (se 2 (by rfl) ⟨46513284, by rfl⟩ : syracuseStep 124035425 = 93026569) B93026569
theorem B2015743 : Blo 1790096 2015743 := bstep (se 1 (by rfl) ⟨1511807, by rfl⟩ : syracuseStep 2015743 = 3023615) B3023615
theorem B2687615 : Blo 1790096 2687615 := bstep (se 1 (by rfl) ⟨2015711, by rfl⟩ : syracuseStep 2687615 = 4031423) B4031423
theorem B11470247 : Blo 1790096 11470247 := bstep (se 1 (by rfl) ⟨8602685, by rfl⟩ : syracuseStep 11470247 = 17205371) B17205371
theorem B5097647 : Blo 1790096 5097647 := bstep (se 1 (by rfl) ⟨3823235, by rfl⟩ : syracuseStep 5097647 = 7646471) B7646471
theorem B6802663 : Blo 1790096 6802663 := bstep (se 1 (by rfl) ⟨5101997, by rfl⟩ : syracuseStep 6802663 = 10203995) B10203995
theorem B6803453 : Blo 1790096 6803453 := bstep (se 3 (by rfl) ⟨1275647, by rfl⟩ : syracuseStep 6803453 = 2551295) B2551295
theorem B1790975 : Blo 1790096 1790975 := bstep (se 1 (by rfl) ⟨1343231, by rfl⟩ : syracuseStep 1790975 = 2686463) B2686463
theorem B6043463 : Blo 1790096 6043463 := bstep (se 1 (by rfl) ⟨4532597, by rfl⟩ : syracuseStep 6043463 = 9065195) B9065195
theorem B3021367 : Blo 1790096 3021367 := bstep (se 1 (by rfl) ⟨2266025, by rfl⟩ : syracuseStep 3021367 = 4532051) B4532051
theorem B17210323 : Blo 1790096 17210323 := bstep (se 1 (by rfl) ⟨12907742, by rfl⟩ : syracuseStep 17210323 = 25815485) B25815485
theorem B130727105 : Blo 1790096 130727105 := bstep (se 2 (by rfl) ⟨49022664, by rfl⟩ : syracuseStep 130727105 = 98045329) B98045329
theorem B82690283 : Blo 1790096 82690283 := bstep (se 1 (by rfl) ⟨62017712, by rfl⟩ : syracuseStep 82690283 = 124035425) B124035425
theorem B2687657 : Blo 1790096 2687657 := bstep (se 2 (by rfl) ⟨1007871, by rfl⟩ : syracuseStep 2687657 = 2015743) B2015743
theorem B22947097 : Blo 1790096 22947097 := bstep (se 2 (by rfl) ⟨8605161, by rfl⟩ : syracuseStep 22947097 = 17210323) B17210323
theorem B9070217 : Blo 1790096 9070217 := bstep (se 2 (by rfl) ⟨3401331, by rfl⟩ : syracuseStep 9070217 = 6802663) B6802663
theorem B7646831 : Blo 1790096 7646831 := bstep (se 1 (by rfl) ⟨5735123, by rfl⟩ : syracuseStep 7646831 = 11470247) B11470247
theorem B87151403 : Blo 1790096 87151403 := bstep (se 1 (by rfl) ⟨65363552, by rfl⟩ : syracuseStep 87151403 = 130727105) B130727105
theorem B4535635 : Blo 1790096 4535635 := bstep (se 1 (by rfl) ⟨3401726, by rfl⟩ : syracuseStep 4535635 = 6803453) B6803453
theorem B1791743 : Blo 1790096 1791743 := bstep (se 1 (by rfl) ⟨1343807, by rfl⟩ : syracuseStep 1791743 = 2687615) B2687615
theorem B4028489 : Blo 1790096 4028489 := bstep (se 2 (by rfl) ⟨1510683, by rfl⟩ : syracuseStep 4028489 = 3021367) B3021367
theorem B4028975 : Blo 1790096 4028975 := bstep (se 1 (by rfl) ⟨3021731, by rfl⟩ : syracuseStep 4028975 = 6043463) B6043463
theorem B3398431 : Blo 1790096 3398431 := bstep (se 1 (by rfl) ⟨2548823, by rfl⟩ : syracuseStep 3398431 = 5097647) B5097647
theorem B4531241 : Blo 1790096 4531241 := bstep (se 2 (by rfl) ⟨1699215, by rfl⟩ : syracuseStep 4531241 = 3398431) B3398431
theorem B6046811 : Blo 1790096 6046811 := bstep (se 1 (by rfl) ⟨4535108, by rfl⟩ : syracuseStep 6046811 = 9070217) B9070217
theorem B6047513 : Blo 1790096 6047513 := bstep (se 2 (by rfl) ⟨2267817, by rfl⟩ : syracuseStep 6047513 = 4535635) B4535635
theorem B5097887 : Blo 1790096 5097887 := bstep (se 1 (by rfl) ⟨3823415, by rfl⟩ : syracuseStep 5097887 = 7646831) B7646831
theorem B55126855 : Blo 1790096 55126855 := bstep (se 1 (by rfl) ⟨41345141, by rfl⟩ : syracuseStep 55126855 = 82690283) B82690283
theorem B58100935 : Blo 1790096 58100935 := bstep (se 1 (by rfl) ⟨43575701, by rfl⟩ : syracuseStep 58100935 = 87151403) B87151403
theorem B1791771 : Blo 1790096 1791771 := bstep (se 1 (by rfl) ⟨1343828, by rfl⟩ : syracuseStep 1791771 = 2687657) B2687657
theorem B2685659 : Blo 1790096 2685659 := bstep (se 1 (by rfl) ⟨2014244, by rfl⟩ : syracuseStep 2685659 = 4028489) B4028489
theorem B2685983 : Blo 1790096 2685983 := bstep (se 1 (by rfl) ⟨2014487, by rfl⟩ : syracuseStep 2685983 = 4028975) B4028975
theorem B30596129 : Blo 1790096 30596129 := bstep (se 2 (by rfl) ⟨11473548, by rfl⟩ : syracuseStep 30596129 = 22947097) B22947097
theorem B4031207 : Blo 1790096 4031207 := bstep (se 1 (by rfl) ⟨3023405, by rfl⟩ : syracuseStep 4031207 = 6046811) B6046811
theorem B4031675 : Blo 1790096 4031675 := bstep (se 1 (by rfl) ⟨3023756, by rfl⟩ : syracuseStep 4031675 = 6047513) B6047513
theorem B73502473 : Blo 1790096 73502473 := bstep (se 2 (by rfl) ⟨27563427, by rfl⟩ : syracuseStep 73502473 = 55126855) B55126855
theorem B77467913 : Blo 1790096 77467913 := bstep (se 2 (by rfl) ⟨29050467, by rfl⟩ : syracuseStep 77467913 = 58100935) B58100935
theorem B1790439 : Blo 1790096 1790439 := bstep (se 1 (by rfl) ⟨1342829, by rfl⟩ : syracuseStep 1790439 = 2685659) B2685659
theorem B1790655 : Blo 1790096 1790655 := bstep (se 1 (by rfl) ⟨1342991, by rfl⟩ : syracuseStep 1790655 = 2685983) B2685983
theorem B3020827 : Blo 1790096 3020827 := bstep (se 1 (by rfl) ⟨2265620, by rfl⟩ : syracuseStep 3020827 = 4531241) B4531241
theorem B3398591 : Blo 1790096 3398591 := bstep (se 1 (by rfl) ⟨2548943, by rfl⟩ : syracuseStep 3398591 = 5097887) B5097887
theorem B20397419 : Blo 1790096 20397419 := bstep (se 1 (by rfl) ⟨15298064, by rfl⟩ : syracuseStep 20397419 = 30596129) B30596129
theorem B2687471 : Blo 1790096 2687471 := bstep (se 1 (by rfl) ⟨2015603, by rfl⟩ : syracuseStep 2687471 = 4031207) B4031207
theorem B2687783 : Blo 1790096 2687783 := bstep (se 1 (by rfl) ⟨2015837, by rfl⟩ : syracuseStep 2687783 = 4031675) B4031675
theorem B98003297 : Blo 1790096 98003297 := bstep (se 2 (by rfl) ⟨36751236, by rfl⟩ : syracuseStep 98003297 = 73502473) B73502473
theorem B51645275 : Blo 1790096 51645275 := bstep (se 1 (by rfl) ⟨38733956, by rfl⟩ : syracuseStep 51645275 = 77467913) B77467913
theorem B2265727 : Blo 1790096 2265727 := bstep (se 1 (by rfl) ⟨1699295, by rfl⟩ : syracuseStep 2265727 = 3398591) B3398591
theorem B4027769 : Blo 1790096 4027769 := bstep (se 2 (by rfl) ⟨1510413, by rfl⟩ : syracuseStep 4027769 = 3020827) B3020827
theorem B13598279 : Blo 1790096 13598279 := bstep (se 1 (by rfl) ⟨10198709, by rfl⟩ : syracuseStep 13598279 = 20397419) B20397419
theorem B65335531 : Blo 1790096 65335531 := bstep (se 1 (by rfl) ⟨49001648, by rfl⟩ : syracuseStep 65335531 = 98003297) B98003297
theorem B9065519 : Blo 1790096 9065519 := bstep (se 1 (by rfl) ⟨6799139, by rfl⟩ : syracuseStep 9065519 = 13598279) B13598279
theorem B1791647 : Blo 1790096 1791647 := bstep (se 1 (by rfl) ⟨1343735, by rfl⟩ : syracuseStep 1791647 = 2687471) B2687471
theorem B1791855 : Blo 1790096 1791855 := bstep (se 1 (by rfl) ⟨1343891, by rfl⟩ : syracuseStep 1791855 = 2687783) B2687783
theorem B3020969 : Blo 1790096 3020969 := bstep (se 2 (by rfl) ⟨1132863, by rfl⟩ : syracuseStep 3020969 = 2265727) B2265727
theorem B2685179 : Blo 1790096 2685179 := bstep (se 1 (by rfl) ⟨2013884, by rfl⟩ : syracuseStep 2685179 = 4027769) B4027769
theorem B34430183 : Blo 1790096 34430183 := bstep (se 1 (by rfl) ⟨25822637, by rfl⟩ : syracuseStep 34430183 = 51645275) B51645275
theorem B87114041 : Blo 1790096 87114041 := bstep (se 2 (by rfl) ⟨32667765, by rfl⟩ : syracuseStep 87114041 = 65335531) B65335531
theorem B1790119 : Blo 1790096 1790119 := bstep (se 1 (by rfl) ⟨1342589, by rfl⟩ : syracuseStep 1790119 = 2685179) B2685179
theorem B6043679 : Blo 1790096 6043679 := bstep (se 1 (by rfl) ⟨4532759, by rfl⟩ : syracuseStep 6043679 = 9065519) B9065519
theorem B2013979 : Blo 1790096 2013979 := bstep (se 1 (by rfl) ⟨1510484, by rfl⟩ : syracuseStep 2013979 = 3020969) B3020969
theorem B22953455 : Blo 1790096 22953455 := bstep (se 1 (by rfl) ⟨17215091, by rfl⟩ : syracuseStep 22953455 = 34430183) B34430183
theorem B58076027 : Blo 1790096 58076027 := bstep (se 1 (by rfl) ⟨43557020, by rfl⟩ : syracuseStep 58076027 = 87114041) B87114041
theorem B2685305 : Blo 1790096 2685305 := bstep (se 2 (by rfl) ⟨1006989, by rfl⟩ : syracuseStep 2685305 = 2013979) B2013979
theorem B4029119 : Blo 1790096 4029119 := bstep (se 1 (by rfl) ⟨3021839, by rfl⟩ : syracuseStep 4029119 = 6043679) B6043679
theorem B15302303 : Blo 1790096 15302303 := bstep (se 1 (by rfl) ⟨11476727, by rfl⟩ : syracuseStep 15302303 = 22953455) B22953455
theorem B38717351 : Blo 1790096 38717351 := bstep (se 1 (by rfl) ⟨29038013, by rfl⟩ : syracuseStep 38717351 = 58076027) B58076027
theorem B10201535 : Blo 1790096 10201535 := bstep (se 1 (by rfl) ⟨7651151, by rfl⟩ : syracuseStep 10201535 = 15302303) B15302303
theorem B1790203 : Blo 1790096 1790203 := bstep (se 1 (by rfl) ⟨1342652, by rfl⟩ : syracuseStep 1790203 = 2685305) B2685305
theorem B2686079 : Blo 1790096 2686079 := bstep (se 1 (by rfl) ⟨2014559, by rfl⟩ : syracuseStep 2686079 = 4029119) B4029119
theorem B6801023 : Blo 1790096 6801023 := bstep (se 1 (by rfl) ⟨5100767, by rfl⟩ : syracuseStep 6801023 = 10201535) B10201535
theorem B1790719 : Blo 1790096 1790719 := bstep (se 1 (by rfl) ⟨1343039, by rfl⟩ : syracuseStep 1790719 = 2686079) B2686079
theorem B25811567 : Blo 1790096 25811567 := bstep (se 1 (by rfl) ⟨19358675, by rfl⟩ : syracuseStep 25811567 = 38717351) B38717351
theorem B4534015 : Blo 1790096 4534015 := bstep (se 1 (by rfl) ⟨3400511, by rfl⟩ : syracuseStep 4534015 = 6801023) B6801023
theorem B17207711 : Blo 1790096 17207711 := bstep (se 1 (by rfl) ⟨12905783, by rfl⟩ : syracuseStep 17207711 = 25811567) B25811567
theorem B11471807 : Blo 1790096 11471807 := bstep (se 1 (by rfl) ⟨8603855, by rfl⟩ : syracuseStep 11471807 = 17207711) B17207711
theorem B6045353 : Blo 1790096 6045353 := bstep (se 2 (by rfl) ⟨2267007, by rfl⟩ : syracuseStep 6045353 = 4534015) B4534015
theorem B7647871 : Blo 1790096 7647871 := bstep (se 1 (by rfl) ⟨5735903, by rfl⟩ : syracuseStep 7647871 = 11471807) B11471807
theorem B4030235 : Blo 1790096 4030235 := bstep (se 1 (by rfl) ⟨3022676, by rfl⟩ : syracuseStep 4030235 = 6045353) B6045353
theorem B10197161 : Blo 1790096 10197161 := bstep (se 2 (by rfl) ⟨3823935, by rfl⟩ : syracuseStep 10197161 = 7647871) B7647871
theorem B2686823 : Blo 1790096 2686823 := bstep (se 1 (by rfl) ⟨2015117, by rfl⟩ : syracuseStep 2686823 = 4030235) B4030235
theorem B1791215 : Blo 1790096 1791215 := bstep (se 1 (by rfl) ⟨1343411, by rfl⟩ : syracuseStep 1791215 = 2686823) B2686823
theorem B6798107 : Blo 1790096 6798107 := bstep (se 1 (by rfl) ⟨5098580, by rfl⟩ : syracuseStep 6798107 = 10197161) B10197161
theorem B4532071 : Blo 1790096 4532071 := bstep (se 1 (by rfl) ⟨3399053, by rfl⟩ : syracuseStep 4532071 = 6798107) B6798107
theorem B6042761 : Blo 1790096 6042761 := bstep (se 2 (by rfl) ⟨2266035, by rfl⟩ : syracuseStep 6042761 = 4532071) B4532071
theorem B4028507 : Blo 1790096 4028507 := bstep (se 1 (by rfl) ⟨3021380, by rfl⟩ : syracuseStep 4028507 = 6042761) B6042761
theorem B2685671 : Blo 1790096 2685671 := bstep (se 1 (by rfl) ⟨2014253, by rfl⟩ : syracuseStep 2685671 = 4028507) B4028507
theorem B1790447 : Blo 1790096 1790447 := bstep (se 1 (by rfl) ⟨1342835, by rfl⟩ : syracuseStep 1790447 = 2685671) B2685671

theorem C0 (j : ℕ) (h1 : 447524 ≤ j) (h2 : j ≤ 448023) : Blo 1790096 (4 * j + 3) := by
  interval_cases j
  · exact B1790099
  · exact B1790103
  · exact B1790107
  · exact B1790111
  · exact B1790115
  · exact B1790119
  · exact B1790123
  · exact B1790127
  · exact B1790131
  · exact B1790135
  · exact B1790139
  · exact B1790143
  · exact B1790147
  · exact B1790151
  · exact B1790155
  · exact B1790159
  · exact B1790163
  · exact B1790167
  · exact B1790171
  · exact B1790175
  · exact B1790179
  · exact B1790183
  · exact B1790187
  · exact B1790191
  · exact B1790195
  · exact B1790199
  · exact B1790203
  · exact B1790207
  · exact B1790211
  · exact B1790215
  · exact B1790219
  · exact B1790223
  · exact B1790227
  · exact B1790231
  · exact B1790235
  · exact B1790239
  · exact B1790243
  · exact B1790247
  · exact B1790251
  · exact B1790255
  · exact B1790259
  · exact B1790263
  · exact B1790267
  · exact B1790271
  · exact B1790275
  · exact B1790279
  · exact B1790283
  · exact B1790287
  · exact B1790291
  · exact B1790295
  · exact B1790299
  · exact B1790303
  · exact B1790307
  · exact B1790311
  · exact B1790315
  · exact B1790319
  · exact B1790323
  · exact B1790327
  · exact B1790331
  · exact B1790335
  · exact B1790339
  · exact B1790343
  · exact B1790347
  · exact B1790351
  · exact B1790355
  · exact B1790359
  · exact B1790363
  · exact B1790367
  · exact B1790371
  · exact B1790375
  · exact B1790379
  · exact B1790383
  · exact B1790387
  · exact B1790391
  · exact B1790395
  · exact B1790399
  · exact B1790403
  · exact B1790407
  · exact B1790411
  · exact B1790415
  · exact B1790419
  · exact B1790423
  · exact B1790427
  · exact B1790431
  · exact B1790435
  · exact B1790439
  · exact B1790443
  · exact B1790447
  · exact B1790451
  · exact B1790455
  · exact B1790459
  · exact B1790463
  · exact B1790467
  · exact B1790471
  · exact B1790475
  · exact B1790479
  · exact B1790483
  · exact B1790487
  · exact B1790491
  · exact B1790495
  · exact B1790499
  · exact B1790503
  · exact B1790507
  · exact B1790511
  · exact B1790515
  · exact B1790519
  · exact B1790523
  · exact B1790527
  · exact B1790531
  · exact B1790535
  · exact B1790539
  · exact B1790543
  · exact B1790547
  · exact B1790551
  · exact B1790555
  · exact B1790559
  · exact B1790563
  · exact B1790567
  · exact B1790571
  · exact B1790575
  · exact B1790579
  · exact B1790583
  · exact B1790587
  · exact B1790591
  · exact B1790595
  · exact B1790599
  · exact B1790603
  · exact B1790607
  · exact B1790611
  · exact B1790615
  · exact B1790619
  · exact B1790623
  · exact B1790627
  · exact B1790631
  · exact B1790635
  · exact B1790639
  · exact B1790643
  · exact B1790647
  · exact B1790651
  · exact B1790655
  · exact B1790659
  · exact B1790663
  · exact B1790667
  · exact B1790671
  · exact B1790675
  · exact B1790679
  · exact B1790683
  · exact B1790687
  · exact B1790691
  · exact B1790695
  · exact B1790699
  · exact B1790703
  · exact B1790707
  · exact B1790711
  · exact B1790715
  · exact B1790719
  · exact B1790723
  · exact B1790727
  · exact B1790731
  · exact B1790735
  · exact B1790739
  · exact B1790743
  · exact B1790747
  · exact B1790751
  · exact B1790755
  · exact B1790759
  · exact B1790763
  · exact B1790767
  · exact B1790771
  · exact B1790775
  · exact B1790779
  · exact B1790783
  · exact B1790787
  · exact B1790791
  · exact B1790795
  · exact B1790799
  · exact B1790803
  · exact B1790807
  · exact B1790811
  · exact B1790815
  · exact B1790819
  · exact B1790823
  · exact B1790827
  · exact B1790831
  · exact B1790835
  · exact B1790839
  · exact B1790843
  · exact B1790847
  · exact B1790851
  · exact B1790855
  · exact B1790859
  · exact B1790863
  · exact B1790867
  · exact B1790871
  · exact B1790875
  · exact B1790879
  · exact B1790883
  · exact B1790887
  · exact B1790891
  · exact B1790895
  · exact B1790899
  · exact B1790903
  · exact B1790907
  · exact B1790911
  · exact B1790915
  · exact B1790919
  · exact B1790923
  · exact B1790927
  · exact B1790931
  · exact B1790935
  · exact B1790939
  · exact B1790943
  · exact B1790947
  · exact B1790951
  · exact B1790955
  · exact B1790959
  · exact B1790963
  · exact B1790967
  · exact B1790971
  · exact B1790975
  · exact B1790979
  · exact B1790983
  · exact B1790987
  · exact B1790991
  · exact B1790995
  · exact B1790999
  · exact B1791003
  · exact B1791007
  · exact B1791011
  · exact B1791015
  · exact B1791019
  · exact B1791023
  · exact B1791027
  · exact B1791031
  · exact B1791035
  · exact B1791039
  · exact B1791043
  · exact B1791047
  · exact B1791051
  · exact B1791055
  · exact B1791059
  · exact B1791063
  · exact B1791067
  · exact B1791071
  · exact B1791075
  · exact B1791079
  · exact B1791083
  · exact B1791087
  · exact B1791091
  · exact B1791095
  · exact B1791099
  · exact B1791103
  · exact B1791107
  · exact B1791111
  · exact B1791115
  · exact B1791119
  · exact B1791123
  · exact B1791127
  · exact B1791131
  · exact B1791135
  · exact B1791139
  · exact B1791143
  · exact B1791147
  · exact B1791151
  · exact B1791155
  · exact B1791159
  · exact B1791163
  · exact B1791167
  · exact B1791171
  · exact B1791175
  · exact B1791179
  · exact B1791183
  · exact B1791187
  · exact B1791191
  · exact B1791195
  · exact B1791199
  · exact B1791203
  · exact B1791207
  · exact B1791211
  · exact B1791215
  · exact B1791219
  · exact B1791223
  · exact B1791227
  · exact B1791231
  · exact B1791235
  · exact B1791239
  · exact B1791243
  · exact B1791247
  · exact B1791251
  · exact B1791255
  · exact B1791259
  · exact B1791263
  · exact B1791267
  · exact B1791271
  · exact B1791275
  · exact B1791279
  · exact B1791283
  · exact B1791287
  · exact B1791291
  · exact B1791295
  · exact B1791299
  · exact B1791303
  · exact B1791307
  · exact B1791311
  · exact B1791315
  · exact B1791319
  · exact B1791323
  · exact B1791327
  · exact B1791331
  · exact B1791335
  · exact B1791339
  · exact B1791343
  · exact B1791347
  · exact B1791351
  · exact B1791355
  · exact B1791359
  · exact B1791363
  · exact B1791367
  · exact B1791371
  · exact B1791375
  · exact B1791379
  · exact B1791383
  · exact B1791387
  · exact B1791391
  · exact B1791395
  · exact B1791399
  · exact B1791403
  · exact B1791407
  · exact B1791411
  · exact B1791415
  · exact B1791419
  · exact B1791423
  · exact B1791427
  · exact B1791431
  · exact B1791435
  · exact B1791439
  · exact B1791443
  · exact B1791447
  · exact B1791451
  · exact B1791455
  · exact B1791459
  · exact B1791463
  · exact B1791467
  · exact B1791471
  · exact B1791475
  · exact B1791479
  · exact B1791483
  · exact B1791487
  · exact B1791491
  · exact B1791495
  · exact B1791499
  · exact B1791503
  · exact B1791507
  · exact B1791511
  · exact B1791515
  · exact B1791519
  · exact B1791523
  · exact B1791527
  · exact B1791531
  · exact B1791535
  · exact B1791539
  · exact B1791543
  · exact B1791547
  · exact B1791551
  · exact B1791555
  · exact B1791559
  · exact B1791563
  · exact B1791567
  · exact B1791571
  · exact B1791575
  · exact B1791579
  · exact B1791583
  · exact B1791587
  · exact B1791591
  · exact B1791595
  · exact B1791599
  · exact B1791603
  · exact B1791607
  · exact B1791611
  · exact B1791615
  · exact B1791619
  · exact B1791623
  · exact B1791627
  · exact B1791631
  · exact B1791635
  · exact B1791639
  · exact B1791643
  · exact B1791647
  · exact B1791651
  · exact B1791655
  · exact B1791659
  · exact B1791663
  · exact B1791667
  · exact B1791671
  · exact B1791675
  · exact B1791679
  · exact B1791683
  · exact B1791687
  · exact B1791691
  · exact B1791695
  · exact B1791699
  · exact B1791703
  · exact B1791707
  · exact B1791711
  · exact B1791715
  · exact B1791719
  · exact B1791723
  · exact B1791727
  · exact B1791731
  · exact B1791735
  · exact B1791739
  · exact B1791743
  · exact B1791747
  · exact B1791751
  · exact B1791755
  · exact B1791759
  · exact B1791763
  · exact B1791767
  · exact B1791771
  · exact B1791775
  · exact B1791779
  · exact B1791783
  · exact B1791787
  · exact B1791791
  · exact B1791795
  · exact B1791799
  · exact B1791803
  · exact B1791807
  · exact B1791811
  · exact B1791815
  · exact B1791819
  · exact B1791823
  · exact B1791827
  · exact B1791831
  · exact B1791835
  · exact B1791839
  · exact B1791843
  · exact B1791847
  · exact B1791851
  · exact B1791855
  · exact B1791859
  · exact B1791863
  · exact B1791867
  · exact B1791871
  · exact B1791875
  · exact B1791879
  · exact B1791883
  · exact B1791887
  · exact B1791891
  · exact B1791895
  · exact B1791899
  · exact B1791903
  · exact B1791907
  · exact B1791911
  · exact B1791915
  · exact B1791919
  · exact B1791923
  · exact B1791927
  · exact B1791931
  · exact B1791935
  · exact B1791939
  · exact B1791943
  · exact B1791947
  · exact B1791951
  · exact B1791955
  · exact B1791959
  · exact B1791963
  · exact B1791967
  · exact B1791971
  · exact B1791975
  · exact B1791979
  · exact B1791983
  · exact B1791987
  · exact B1791991
  · exact B1791995
  · exact B1791999
  · exact B1792003
  · exact B1792007
  · exact B1792011
  · exact B1792015
  · exact B1792019
  · exact B1792023
  · exact B1792027
  · exact B1792031
  · exact B1792035
  · exact B1792039
  · exact B1792043
  · exact B1792047
  · exact B1792051
  · exact B1792055
  · exact B1792059
  · exact B1792063
  · exact B1792067
  · exact B1792071
  · exact B1792075
  · exact B1792079
  · exact B1792083
  · exact B1792087
  · exact B1792091
  · exact B1792095

theorem solution (m : ℕ) (hlo : 1790096 ≤ m) (hhi : m ≤ 1792096) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 447524 ≤ j := by omega
    have hj2 : j ≤ 448023 := by omega
    have hb : Blo 1790096 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
