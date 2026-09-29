-- Prove2me | solution 1 for syracuse_descends_range_239816_243816
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:44:00.584036+00:00
-- url     : https://prove2.me/submissions/5a1c63fe-16f2-45e9-9c08-b81cdd96ffee

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


theorem B360461 : Blo 239816 360461 := bbase (se 3 (by rfl) ⟨67586, by rfl⟩ : syracuseStep 360461 = 135173) (by norm_num)
theorem B360485 : Blo 239816 360485 := bbase (se 4 (by rfl) ⟨33795, by rfl⟩ : syracuseStep 360485 = 67591) (by norm_num)
theorem B360509 : Blo 239816 360509 := bbase (se 3 (by rfl) ⟨67595, by rfl⟩ : syracuseStep 360509 = 135191) (by norm_num)
theorem B360533 : Blo 239816 360533 := bbase (se 8 (by rfl) ⟨2112, by rfl⟩ : syracuseStep 360533 = 4225) (by norm_num)
theorem B360557 : Blo 239816 360557 := bbase (se 3 (by rfl) ⟨67604, by rfl⟩ : syracuseStep 360557 = 135209) (by norm_num)
theorem B360581 : Blo 239816 360581 := bbase (se 4 (by rfl) ⟨33804, by rfl⟩ : syracuseStep 360581 = 67609) (by norm_num)
theorem B360605 : Blo 239816 360605 := bbase (se 3 (by rfl) ⟨67613, by rfl⟩ : syracuseStep 360605 = 135227) (by norm_num)
theorem B360629 : Blo 239816 360629 := bbase (se 5 (by rfl) ⟨16904, by rfl⟩ : syracuseStep 360629 = 33809) (by norm_num)
theorem B524485 : Blo 239816 524485 := bbase (se 4 (by rfl) ⟨49170, by rfl⟩ : syracuseStep 524485 = 98341) (by norm_num)
theorem B360653 : Blo 239816 360653 := bbase (se 3 (by rfl) ⟨67622, by rfl⟩ : syracuseStep 360653 = 135245) (by norm_num)
theorem B360677 : Blo 239816 360677 := bbase (se 4 (by rfl) ⟨33813, by rfl⟩ : syracuseStep 360677 = 67627) (by norm_num)
theorem B360701 : Blo 239816 360701 := bbase (se 3 (by rfl) ⟨67631, by rfl⟩ : syracuseStep 360701 = 135263) (by norm_num)
theorem B360725 : Blo 239816 360725 := bbase (se 6 (by rfl) ⟨8454, by rfl⟩ : syracuseStep 360725 = 16909) (by norm_num)
theorem B360749 : Blo 239816 360749 := bbase (se 3 (by rfl) ⟨67640, by rfl⟩ : syracuseStep 360749 = 135281) (by norm_num)
theorem B360773 : Blo 239816 360773 := bbase (se 4 (by rfl) ⟨33822, by rfl⟩ : syracuseStep 360773 = 67645) (by norm_num)
theorem B360797 : Blo 239816 360797 := bbase (se 3 (by rfl) ⟨67649, by rfl⟩ : syracuseStep 360797 = 135299) (by norm_num)
theorem B491869 : Blo 239816 491869 := bbase (se 3 (by rfl) ⟨92225, by rfl⟩ : syracuseStep 491869 = 184451) (by norm_num)
theorem B819557 : Blo 239816 819557 := bbase (se 4 (by rfl) ⟨76833, by rfl⟩ : syracuseStep 819557 = 153667) (by norm_num)
theorem B360821 : Blo 239816 360821 := bbase (se 5 (by rfl) ⟨16913, by rfl⟩ : syracuseStep 360821 = 33827) (by norm_num)
theorem B360845 : Blo 239816 360845 := bbase (se 3 (by rfl) ⟨67658, by rfl⟩ : syracuseStep 360845 = 135317) (by norm_num)
theorem B360869 : Blo 239816 360869 := bbase (se 4 (by rfl) ⟨33831, by rfl⟩ : syracuseStep 360869 = 67663) (by norm_num)
theorem B360893 : Blo 239816 360893 := bbase (se 3 (by rfl) ⟨67667, by rfl⟩ : syracuseStep 360893 = 135335) (by norm_num)
theorem B360917 : Blo 239816 360917 := bbase (se 7 (by rfl) ⟨4229, by rfl⟩ : syracuseStep 360917 = 8459) (by norm_num)
theorem B360941 : Blo 239816 360941 := bbase (se 3 (by rfl) ⟨67676, by rfl⟩ : syracuseStep 360941 = 135353) (by norm_num)
theorem B360965 : Blo 239816 360965 := bbase (se 4 (by rfl) ⟨33840, by rfl⟩ : syracuseStep 360965 = 67681) (by norm_num)
theorem B360989 : Blo 239816 360989 := bbase (se 3 (by rfl) ⟨67685, by rfl⟩ : syracuseStep 360989 = 135371) (by norm_num)
theorem B361013 : Blo 239816 361013 := bbase (se 5 (by rfl) ⟨16922, by rfl⟩ : syracuseStep 361013 = 33845) (by norm_num)
theorem B361037 : Blo 239816 361037 := bbase (se 3 (by rfl) ⟨67694, by rfl⟩ : syracuseStep 361037 = 135389) (by norm_num)
theorem B361061 : Blo 239816 361061 := bbase (se 4 (by rfl) ⟨33849, by rfl⟩ : syracuseStep 361061 = 67699) (by norm_num)
theorem B361085 : Blo 239816 361085 := bbase (se 3 (by rfl) ⟨67703, by rfl⟩ : syracuseStep 361085 = 135407) (by norm_num)
theorem B361109 : Blo 239816 361109 := bbase (se 6 (by rfl) ⟨8463, by rfl⟩ : syracuseStep 361109 = 16927) (by norm_num)
theorem B361133 : Blo 239816 361133 := bbase (se 3 (by rfl) ⟨67712, by rfl⟩ : syracuseStep 361133 = 135425) (by norm_num)
theorem B459445 : Blo 239816 459445 := bbase (se 5 (by rfl) ⟨21536, by rfl⟩ : syracuseStep 459445 = 43073) (by norm_num)
theorem B361157 : Blo 239816 361157 := bbase (se 4 (by rfl) ⟨33858, by rfl⟩ : syracuseStep 361157 = 67717) (by norm_num)
theorem B688837 : Blo 239816 688837 := bbase (se 4 (by rfl) ⟨64578, by rfl⟩ : syracuseStep 688837 = 129157) (by norm_num)
theorem B361181 : Blo 239816 361181 := bbase (se 3 (by rfl) ⟨67721, by rfl⟩ : syracuseStep 361181 = 135443) (by norm_num)
theorem B361205 : Blo 239816 361205 := bbase (se 5 (by rfl) ⟨16931, by rfl⟩ : syracuseStep 361205 = 33863) (by norm_num)
theorem B361229 : Blo 239816 361229 := bbase (se 3 (by rfl) ⟨67730, by rfl⟩ : syracuseStep 361229 = 135461) (by norm_num)
theorem B819989 : Blo 239816 819989 := bbase (se 6 (by rfl) ⟨19218, by rfl⟩ : syracuseStep 819989 = 38437) (by norm_num)
theorem B361253 : Blo 239816 361253 := bbase (se 4 (by rfl) ⟨33867, by rfl⟩ : syracuseStep 361253 = 67735) (by norm_num)
theorem B361277 : Blo 239816 361277 := bbase (se 3 (by rfl) ⟨67739, by rfl⟩ : syracuseStep 361277 = 135479) (by norm_num)
theorem B459589 : Blo 239816 459589 := bbase (se 4 (by rfl) ⟨43086, by rfl⟩ : syracuseStep 459589 = 86173) (by norm_num)
theorem B361301 : Blo 239816 361301 := bbase (se 9 (by rfl) ⟨1058, by rfl⟩ : syracuseStep 361301 = 2117) (by norm_num)
theorem B492389 : Blo 239816 492389 := bbase (se 4 (by rfl) ⟨46161, by rfl⟩ : syracuseStep 492389 = 92323) (by norm_num)
theorem B361325 : Blo 239816 361325 := bbase (se 3 (by rfl) ⟨67748, by rfl⟩ : syracuseStep 361325 = 135497) (by norm_num)
theorem B361349 : Blo 239816 361349 := bbase (se 4 (by rfl) ⟨33876, by rfl⟩ : syracuseStep 361349 = 67753) (by norm_num)
theorem B295825 : Blo 239816 295825 := bbase (se 2 (by rfl) ⟨110934, by rfl⟩ : syracuseStep 295825 = 221869) (by norm_num)
theorem B361373 : Blo 239816 361373 := bbase (se 3 (by rfl) ⟨67757, by rfl⟩ : syracuseStep 361373 = 135515) (by norm_num)
theorem B361397 : Blo 239816 361397 := bbase (se 5 (by rfl) ⟨16940, by rfl⟩ : syracuseStep 361397 = 33881) (by norm_num)
theorem B361421 : Blo 239816 361421 := bbase (se 3 (by rfl) ⟨67766, by rfl⟩ : syracuseStep 361421 = 135533) (by norm_num)
theorem B361445 : Blo 239816 361445 := bbase (se 4 (by rfl) ⟨33885, by rfl⟩ : syracuseStep 361445 = 67771) (by norm_num)
theorem B459749 : Blo 239816 459749 := bbase (se 4 (by rfl) ⟨43101, by rfl⟩ : syracuseStep 459749 = 86203) (by norm_num)
theorem B361469 : Blo 239816 361469 := bbase (se 3 (by rfl) ⟨67775, by rfl⟩ : syracuseStep 361469 = 135551) (by norm_num)
theorem B361493 : Blo 239816 361493 := bbase (se 6 (by rfl) ⟨8472, by rfl⟩ : syracuseStep 361493 = 16945) (by norm_num)
theorem B361517 : Blo 239816 361517 := bbase (se 3 (by rfl) ⟨67784, by rfl⟩ : syracuseStep 361517 = 135569) (by norm_num)
theorem B361541 : Blo 239816 361541 := bbase (se 4 (by rfl) ⟨33894, by rfl⟩ : syracuseStep 361541 = 67789) (by norm_num)
theorem B361565 : Blo 239816 361565 := bbase (se 3 (by rfl) ⟨67793, by rfl⟩ : syracuseStep 361565 = 135587) (by norm_num)
theorem B361589 : Blo 239816 361589 := bbase (se 5 (by rfl) ⟨16949, by rfl⟩ : syracuseStep 361589 = 33899) (by norm_num)
theorem B459893 : Blo 239816 459893 := bbase (se 5 (by rfl) ⟨21557, by rfl⟩ : syracuseStep 459893 = 43115) (by norm_num)
theorem B918661 : Blo 239816 918661 := bbase (se 4 (by rfl) ⟨86124, by rfl⟩ : syracuseStep 918661 = 172249) (by norm_num)
theorem B361613 : Blo 239816 361613 := bbase (se 3 (by rfl) ⟨67802, by rfl⟩ : syracuseStep 361613 = 135605) (by norm_num)
theorem B525461 : Blo 239816 525461 := bbase (se 6 (by rfl) ⟨12315, by rfl⟩ : syracuseStep 525461 = 24631) (by norm_num)
theorem B361637 : Blo 239816 361637 := bbase (se 4 (by rfl) ⟨33903, by rfl⟩ : syracuseStep 361637 = 67807) (by norm_num)
theorem B361661 : Blo 239816 361661 := bbase (se 3 (by rfl) ⟨67811, by rfl⟩ : syracuseStep 361661 = 135623) (by norm_num)
theorem B820421 : Blo 239816 820421 := bbase (se 4 (by rfl) ⟨76914, by rfl⟩ : syracuseStep 820421 = 153829) (by norm_num)
theorem B361685 : Blo 239816 361685 := bbase (se 7 (by rfl) ⟨4238, by rfl⟩ : syracuseStep 361685 = 8477) (by norm_num)
theorem B2065621 : Blo 239816 2065621 := bbase (se 7 (by rfl) ⟨24206, by rfl⟩ : syracuseStep 2065621 = 48413) (by norm_num)
theorem B361709 : Blo 239816 361709 := bbase (se 3 (by rfl) ⟨67820, by rfl⟩ : syracuseStep 361709 = 135641) (by norm_num)
theorem B361733 : Blo 239816 361733 := bbase (se 4 (by rfl) ⟨33912, by rfl⟩ : syracuseStep 361733 = 67825) (by norm_num)
theorem B361757 : Blo 239816 361757 := bbase (se 3 (by rfl) ⟨67829, by rfl⟩ : syracuseStep 361757 = 135659) (by norm_num)
theorem B394541 : Blo 239816 394541 := bbase (se 3 (by rfl) ⟨73976, by rfl⟩ : syracuseStep 394541 = 147953) (by norm_num)
theorem B329005 : Blo 239816 329005 := bbase (se 3 (by rfl) ⟨61688, by rfl⟩ : syracuseStep 329005 = 123377) (by norm_num)
theorem B361781 : Blo 239816 361781 := bbase (se 5 (by rfl) ⟨16958, by rfl⟩ : syracuseStep 361781 = 33917) (by norm_num)
theorem B361805 : Blo 239816 361805 := bbase (se 3 (by rfl) ⟨67838, by rfl⟩ : syracuseStep 361805 = 135677) (by norm_num)
theorem B361829 : Blo 239816 361829 := bbase (se 4 (by rfl) ⟨33921, by rfl⟩ : syracuseStep 361829 = 67843) (by norm_num)
theorem B1246565 : Blo 239816 1246565 := bbase (se 4 (by rfl) ⟨116865, by rfl⟩ : syracuseStep 1246565 = 233731) (by norm_num)
theorem B361853 : Blo 239816 361853 := bbase (se 3 (by rfl) ⟨67847, by rfl⟩ : syracuseStep 361853 = 135695) (by norm_num)
theorem B492941 : Blo 239816 492941 := bbase (se 3 (by rfl) ⟨92426, by rfl⟩ : syracuseStep 492941 = 184853) (by norm_num)
theorem B361877 : Blo 239816 361877 := bbase (se 6 (by rfl) ⟨8481, by rfl⟩ : syracuseStep 361877 = 16963) (by norm_num)
theorem B460181 : Blo 239816 460181 := bbase (se 6 (by rfl) ⟨10785, by rfl⟩ : syracuseStep 460181 = 21571) (by norm_num)
theorem B361901 : Blo 239816 361901 := bbase (se 3 (by rfl) ⟨67856, by rfl⟩ : syracuseStep 361901 = 135713) (by norm_num)
theorem B918965 : Blo 239816 918965 := bbase (se 5 (by rfl) ⟨43076, by rfl⟩ : syracuseStep 918965 = 86153) (by norm_num)
theorem B361925 : Blo 239816 361925 := bbase (se 4 (by rfl) ⟨33930, by rfl⟩ : syracuseStep 361925 = 67861) (by norm_num)
theorem B361949 : Blo 239816 361949 := bbase (se 3 (by rfl) ⟨67865, by rfl⟩ : syracuseStep 361949 = 135731) (by norm_num)
theorem B329189 : Blo 239816 329189 := bbase (se 4 (by rfl) ⟨30861, by rfl⟩ : syracuseStep 329189 = 61723) (by norm_num)
theorem B263657 : Blo 239816 263657 := bbase (se 2 (by rfl) ⟨98871, by rfl⟩ : syracuseStep 263657 = 197743) (by norm_num)
theorem B493037 : Blo 239816 493037 := bbase (se 3 (by rfl) ⟨92444, by rfl⟩ : syracuseStep 493037 = 184889) (by norm_num)
theorem B361973 : Blo 239816 361973 := bbase (se 5 (by rfl) ⟨16967, by rfl⟩ : syracuseStep 361973 = 33935) (by norm_num)
theorem B624125 : Blo 239816 624125 := bbase (se 3 (by rfl) ⟨117023, by rfl⟩ : syracuseStep 624125 = 234047) (by norm_num)
theorem B361997 : Blo 239816 361997 := bbase (se 3 (by rfl) ⟨67874, by rfl⟩ : syracuseStep 361997 = 135749) (by norm_num)
theorem B362021 : Blo 239816 362021 := bbase (se 4 (by rfl) ⟨33939, by rfl⟩ : syracuseStep 362021 = 67879) (by norm_num)
theorem B460333 : Blo 239816 460333 := bbase (se 3 (by rfl) ⟨86312, by rfl⟩ : syracuseStep 460333 = 172625) (by norm_num)
theorem B362045 : Blo 239816 362045 := bbase (se 3 (by rfl) ⟨67883, by rfl⟩ : syracuseStep 362045 = 135767) (by norm_num)
theorem B362069 : Blo 239816 362069 := bbase (se 8 (by rfl) ⟨2121, by rfl⟩ : syracuseStep 362069 = 4243) (by norm_num)
theorem B362093 : Blo 239816 362093 := bbase (se 3 (by rfl) ⟨67892, by rfl⟩ : syracuseStep 362093 = 135785) (by norm_num)
theorem B820853 : Blo 239816 820853 := bbase (se 5 (by rfl) ⟨38477, by rfl⟩ : syracuseStep 820853 = 76955) (by norm_num)
theorem B329341 : Blo 239816 329341 := bbase (se 3 (by rfl) ⟨61751, by rfl⟩ : syracuseStep 329341 = 123503) (by norm_num)
theorem B362117 : Blo 239816 362117 := bbase (se 4 (by rfl) ⟨33948, by rfl⟩ : syracuseStep 362117 = 67897) (by norm_num)
theorem B362141 : Blo 239816 362141 := bbase (se 3 (by rfl) ⟨67901, by rfl⟩ : syracuseStep 362141 = 135803) (by norm_num)
theorem B362165 : Blo 239816 362165 := bbase (se 5 (by rfl) ⟨16976, by rfl⟩ : syracuseStep 362165 = 33953) (by norm_num)
theorem B362189 : Blo 239816 362189 := bbase (se 3 (by rfl) ⟨67910, by rfl⟩ : syracuseStep 362189 = 135821) (by norm_num)
theorem B362213 : Blo 239816 362213 := bbase (se 4 (by rfl) ⟨33957, by rfl⟩ : syracuseStep 362213 = 67915) (by norm_num)
theorem B362237 : Blo 239816 362237 := bbase (se 3 (by rfl) ⟨67919, by rfl⟩ : syracuseStep 362237 = 135839) (by norm_num)
theorem B362261 : Blo 239816 362261 := bbase (se 6 (by rfl) ⟨8490, by rfl⟩ : syracuseStep 362261 = 16981) (by norm_num)
theorem B362285 : Blo 239816 362285 := bbase (se 3 (by rfl) ⟨67928, by rfl⟩ : syracuseStep 362285 = 135857) (by norm_num)
theorem B362309 : Blo 239816 362309 := bbase (se 4 (by rfl) ⟨33966, by rfl⟩ : syracuseStep 362309 = 67933) (by norm_num)
theorem B362333 : Blo 239816 362333 := bbase (se 3 (by rfl) ⟨67937, by rfl⟩ : syracuseStep 362333 = 135875) (by norm_num)
theorem B460637 : Blo 239816 460637 := bbase (se 3 (by rfl) ⟨86369, by rfl⟩ : syracuseStep 460637 = 172739) (by norm_num)
theorem B362357 : Blo 239816 362357 := bbase (se 5 (by rfl) ⟨16985, by rfl⟩ : syracuseStep 362357 = 33971) (by norm_num)
theorem B362381 : Blo 239816 362381 := bbase (se 3 (by rfl) ⟨67946, by rfl⟩ : syracuseStep 362381 = 135893) (by norm_num)
theorem B362405 : Blo 239816 362405 := bbase (se 4 (by rfl) ⟨33975, by rfl⟩ : syracuseStep 362405 = 67951) (by norm_num)
theorem B362429 : Blo 239816 362429 := bbase (se 3 (by rfl) ⟨67955, by rfl⟩ : syracuseStep 362429 = 135911) (by norm_num)
theorem B362453 : Blo 239816 362453 := bbase (se 7 (by rfl) ⟨4247, by rfl⟩ : syracuseStep 362453 = 8495) (by norm_num)
theorem B264173 : Blo 239816 264173 := bbase (se 3 (by rfl) ⟨49532, by rfl⟩ : syracuseStep 264173 = 99065) (by norm_num)
theorem B362477 : Blo 239816 362477 := bbase (se 3 (by rfl) ⟨67964, by rfl⟩ : syracuseStep 362477 = 135929) (by norm_num)
theorem B362501 : Blo 239816 362501 := bbase (se 4 (by rfl) ⟨33984, by rfl⟩ : syracuseStep 362501 = 67969) (by norm_num)
theorem B362525 : Blo 239816 362525 := bbase (se 3 (by rfl) ⟨67973, by rfl⟩ : syracuseStep 362525 = 135947) (by norm_num)
theorem B821285 : Blo 239816 821285 := bbase (se 4 (by rfl) ⟨76995, by rfl⟩ : syracuseStep 821285 = 153991) (by norm_num)
theorem B362549 : Blo 239816 362549 := bbase (se 5 (by rfl) ⟨16994, by rfl⟩ : syracuseStep 362549 = 33989) (by norm_num)
theorem B362573 : Blo 239816 362573 := bbase (se 3 (by rfl) ⟨67982, by rfl⟩ : syracuseStep 362573 = 135965) (by norm_num)
theorem B362597 : Blo 239816 362597 := bbase (se 4 (by rfl) ⟨33993, by rfl⟩ : syracuseStep 362597 = 67987) (by norm_num)
theorem B362621 : Blo 239816 362621 := bbase (se 3 (by rfl) ⟨67991, by rfl⟩ : syracuseStep 362621 = 135983) (by norm_num)
theorem B821381 : Blo 239816 821381 := bbase (se 4 (by rfl) ⟨77004, by rfl⟩ : syracuseStep 821381 = 154009) (by norm_num)
theorem B362645 : Blo 239816 362645 := bbase (se 6 (by rfl) ⟨8499, by rfl⟩ : syracuseStep 362645 = 16999) (by norm_num)
theorem B362669 : Blo 239816 362669 := bbase (se 3 (by rfl) ⟨68000, by rfl⟩ : syracuseStep 362669 = 136001) (by norm_num)
theorem B362693 : Blo 239816 362693 := bbase (se 4 (by rfl) ⟨34002, by rfl⟩ : syracuseStep 362693 = 68005) (by norm_num)
theorem B362717 : Blo 239816 362717 := bbase (se 3 (by rfl) ⟨68009, by rfl⟩ : syracuseStep 362717 = 136019) (by norm_num)
theorem B362741 : Blo 239816 362741 := bbase (se 5 (by rfl) ⟨17003, by rfl⟩ : syracuseStep 362741 = 34007) (by norm_num)
theorem B362765 : Blo 239816 362765 := bbase (se 3 (by rfl) ⟨68018, by rfl⟩ : syracuseStep 362765 = 136037) (by norm_num)
theorem B362789 : Blo 239816 362789 := bbase (se 4 (by rfl) ⟨34011, by rfl⟩ : syracuseStep 362789 = 68023) (by norm_num)
theorem B362813 : Blo 239816 362813 := bbase (se 3 (by rfl) ⟨68027, by rfl⟩ : syracuseStep 362813 = 136055) (by norm_num)
theorem B362837 : Blo 239816 362837 := bbase (se 10 (by rfl) ⟨531, by rfl⟩ : syracuseStep 362837 = 1063) (by norm_num)
theorem B559445 : Blo 239816 559445 := bbase (se 10 (by rfl) ⟨819, by rfl⟩ : syracuseStep 559445 = 1639) (by norm_num)
theorem B362861 : Blo 239816 362861 := bbase (se 3 (by rfl) ⟨68036, by rfl⟩ : syracuseStep 362861 = 136073) (by norm_num)
theorem B1214837 : Blo 239816 1214837 := bbase (se 5 (by rfl) ⟨56945, by rfl⟩ : syracuseStep 1214837 = 113891) (by norm_num)
theorem B362885 : Blo 239816 362885 := bbase (se 4 (by rfl) ⟨34020, by rfl⟩ : syracuseStep 362885 = 68041) (by norm_num)
theorem B362909 : Blo 239816 362909 := bbase (se 3 (by rfl) ⟨68045, by rfl⟩ : syracuseStep 362909 = 136091) (by norm_num)
theorem B362933 : Blo 239816 362933 := bbase (se 5 (by rfl) ⟨17012, by rfl⟩ : syracuseStep 362933 = 34025) (by norm_num)
theorem B362957 : Blo 239816 362957 := bbase (se 3 (by rfl) ⟨68054, by rfl⟩ : syracuseStep 362957 = 136109) (by norm_num)
theorem B821717 : Blo 239816 821717 := bbase (se 7 (by rfl) ⟨9629, by rfl⟩ : syracuseStep 821717 = 19259) (by norm_num)
theorem B362981 : Blo 239816 362981 := bbase (se 4 (by rfl) ⟨34029, by rfl⟩ : syracuseStep 362981 = 68059) (by norm_num)
theorem B363005 : Blo 239816 363005 := bbase (se 3 (by rfl) ⟨68063, by rfl⟩ : syracuseStep 363005 = 136127) (by norm_num)
theorem B363029 : Blo 239816 363029 := bbase (se 6 (by rfl) ⟨8508, by rfl⟩ : syracuseStep 363029 = 17017) (by norm_num)
theorem B363053 : Blo 239816 363053 := bbase (se 3 (by rfl) ⟨68072, by rfl⟩ : syracuseStep 363053 = 136145) (by norm_num)
theorem B363077 : Blo 239816 363077 := bbase (se 4 (by rfl) ⟨34038, by rfl⟩ : syracuseStep 363077 = 68077) (by norm_num)
theorem B461389 : Blo 239816 461389 := bbase (se 3 (by rfl) ⟨86510, by rfl⟩ : syracuseStep 461389 = 173021) (by norm_num)
theorem B363101 : Blo 239816 363101 := bbase (se 3 (by rfl) ⟨68081, by rfl⟩ : syracuseStep 363101 = 136163) (by norm_num)
theorem B363125 : Blo 239816 363125 := bbase (se 5 (by rfl) ⟨17021, by rfl⟩ : syracuseStep 363125 = 34043) (by norm_num)
theorem B363149 : Blo 239816 363149 := bbase (se 3 (by rfl) ⟨68090, by rfl⟩ : syracuseStep 363149 = 136181) (by norm_num)
theorem B363173 : Blo 239816 363173 := bbase (se 4 (by rfl) ⟨34047, by rfl⟩ : syracuseStep 363173 = 68095) (by norm_num)
theorem B363197 : Blo 239816 363197 := bbase (se 3 (by rfl) ⟨68099, by rfl⟩ : syracuseStep 363197 = 136199) (by norm_num)
theorem B363221 : Blo 239816 363221 := bbase (se 7 (by rfl) ⟨4256, by rfl⟩ : syracuseStep 363221 = 8513) (by norm_num)
theorem B985813 : Blo 239816 985813 := bbase (se 7 (by rfl) ⟨11552, by rfl⟩ : syracuseStep 985813 = 23105) (by norm_num)
theorem B461533 : Blo 239816 461533 := bbase (se 3 (by rfl) ⟨86537, by rfl⟩ : syracuseStep 461533 = 173075) (by norm_num)
theorem B363245 : Blo 239816 363245 := bbase (se 3 (by rfl) ⟨68108, by rfl⟩ : syracuseStep 363245 = 136217) (by norm_num)
theorem B363269 : Blo 239816 363269 := bbase (se 4 (by rfl) ⟨34056, by rfl⟩ : syracuseStep 363269 = 68113) (by norm_num)
theorem B363293 : Blo 239816 363293 := bbase (se 3 (by rfl) ⟨68117, by rfl⟩ : syracuseStep 363293 = 136235) (by norm_num)
theorem B363317 : Blo 239816 363317 := bbase (se 5 (by rfl) ⟨17030, by rfl⟩ : syracuseStep 363317 = 34061) (by norm_num)
theorem B363341 : Blo 239816 363341 := bbase (se 3 (by rfl) ⟨68126, by rfl⟩ : syracuseStep 363341 = 136253) (by norm_num)
theorem B363365 : Blo 239816 363365 := bbase (se 4 (by rfl) ⟨34065, by rfl⟩ : syracuseStep 363365 = 68131) (by norm_num)
theorem B363389 : Blo 239816 363389 := bbase (se 3 (by rfl) ⟨68135, by rfl⟩ : syracuseStep 363389 = 136271) (by norm_num)
theorem B461693 : Blo 239816 461693 := bbase (se 3 (by rfl) ⟨86567, by rfl⟩ : syracuseStep 461693 = 173135) (by norm_num)
theorem B822149 : Blo 239816 822149 := bbase (se 4 (by rfl) ⟨77076, by rfl⟩ : syracuseStep 822149 = 154153) (by norm_num)
theorem B363413 : Blo 239816 363413 := bbase (se 6 (by rfl) ⟨8517, by rfl⟩ : syracuseStep 363413 = 17035) (by norm_num)
theorem B363437 : Blo 239816 363437 := bbase (se 3 (by rfl) ⟨68144, by rfl⟩ : syracuseStep 363437 = 136289) (by norm_num)
theorem B363461 : Blo 239816 363461 := bbase (se 4 (by rfl) ⟨34074, by rfl⟩ : syracuseStep 363461 = 68149) (by norm_num)
theorem B363485 : Blo 239816 363485 := bbase (se 3 (by rfl) ⟨68153, by rfl⟩ : syracuseStep 363485 = 136307) (by norm_num)
theorem B363509 : Blo 239816 363509 := bbase (se 5 (by rfl) ⟨17039, by rfl⟩ : syracuseStep 363509 = 34079) (by norm_num)
theorem B658421 : Blo 239816 658421 := bbase (se 5 (by rfl) ⟨30863, by rfl⟩ : syracuseStep 658421 = 61727) (by norm_num)
theorem B363533 : Blo 239816 363533 := bbase (se 3 (by rfl) ⟨68162, by rfl⟩ : syracuseStep 363533 = 136325) (by norm_num)
theorem B461837 : Blo 239816 461837 := bbase (se 3 (by rfl) ⟨86594, by rfl⟩ : syracuseStep 461837 = 173189) (by norm_num)
theorem B363557 : Blo 239816 363557 := bbase (se 4 (by rfl) ⟨34083, by rfl⟩ : syracuseStep 363557 = 68167) (by norm_num)
theorem B363581 : Blo 239816 363581 := bbase (se 3 (by rfl) ⟨68171, by rfl⟩ : syracuseStep 363581 = 136343) (by norm_num)
theorem B363605 : Blo 239816 363605 := bbase (se 8 (by rfl) ⟨2130, by rfl⟩ : syracuseStep 363605 = 4261) (by norm_num)
theorem B363629 : Blo 239816 363629 := bbase (se 3 (by rfl) ⟨68180, by rfl⟩ : syracuseStep 363629 = 136361) (by norm_num)
theorem B494717 : Blo 239816 494717 := bbase (se 3 (by rfl) ⟨92759, by rfl⟩ : syracuseStep 494717 = 185519) (by norm_num)
theorem B363653 : Blo 239816 363653 := bbase (se 4 (by rfl) ⟨34092, by rfl⟩ : syracuseStep 363653 = 68185) (by norm_num)
theorem B2067605 : Blo 239816 2067605 := bbase (se 6 (by rfl) ⟨48459, by rfl⟩ : syracuseStep 2067605 = 96919) (by norm_num)
theorem B363677 : Blo 239816 363677 := bbase (se 3 (by rfl) ⟨68189, by rfl⟩ : syracuseStep 363677 = 136379) (by norm_num)
theorem B363701 : Blo 239816 363701 := bbase (se 5 (by rfl) ⟨17048, by rfl⟩ : syracuseStep 363701 = 34097) (by norm_num)
theorem B363725 : Blo 239816 363725 := bbase (se 3 (by rfl) ⟨68198, by rfl⟩ : syracuseStep 363725 = 136397) (by norm_num)
theorem B363749 : Blo 239816 363749 := bbase (se 4 (by rfl) ⟨34101, by rfl⟩ : syracuseStep 363749 = 68203) (by norm_num)
theorem B363773 : Blo 239816 363773 := bbase (se 3 (by rfl) ⟨68207, by rfl⟩ : syracuseStep 363773 = 136415) (by norm_num)
theorem B363797 : Blo 239816 363797 := bbase (se 6 (by rfl) ⟨8526, by rfl⟩ : syracuseStep 363797 = 17053) (by norm_num)
theorem B363821 : Blo 239816 363821 := bbase (se 3 (by rfl) ⟨68216, by rfl⟩ : syracuseStep 363821 = 136433) (by norm_num)
theorem B462125 : Blo 239816 462125 := bbase (se 3 (by rfl) ⟨86648, by rfl⟩ : syracuseStep 462125 = 173297) (by norm_num)
theorem B822581 : Blo 239816 822581 := bbase (se 5 (by rfl) ⟨38558, by rfl⟩ : syracuseStep 822581 = 77117) (by norm_num)
theorem B363845 : Blo 239816 363845 := bbase (se 4 (by rfl) ⟨34110, by rfl⟩ : syracuseStep 363845 = 68221) (by norm_num)
theorem B363869 : Blo 239816 363869 := bbase (se 3 (by rfl) ⟨68225, by rfl⟩ : syracuseStep 363869 = 136451) (by norm_num)
theorem B527717 : Blo 239816 527717 := bbase (se 4 (by rfl) ⟨49473, by rfl⟩ : syracuseStep 527717 = 98947) (by norm_num)
theorem B363893 : Blo 239816 363893 := bbase (se 5 (by rfl) ⟨17057, by rfl⟩ : syracuseStep 363893 = 34115) (by norm_num)
theorem B363917 : Blo 239816 363917 := bbase (se 3 (by rfl) ⟨68234, by rfl⟩ : syracuseStep 363917 = 136469) (by norm_num)
theorem B363941 : Blo 239816 363941 := bbase (se 4 (by rfl) ⟨34119, by rfl⟩ : syracuseStep 363941 = 68239) (by norm_num)
theorem B363965 : Blo 239816 363965 := bbase (se 3 (by rfl) ⟨68243, by rfl⟩ : syracuseStep 363965 = 136487) (by norm_num)
theorem B462277 : Blo 239816 462277 := bbase (se 4 (by rfl) ⟨43338, by rfl⟩ : syracuseStep 462277 = 86677) (by norm_num)
theorem B363989 : Blo 239816 363989 := bbase (se 7 (by rfl) ⟨4265, by rfl⟩ : syracuseStep 363989 = 8531) (by norm_num)
theorem B691685 : Blo 239816 691685 := bbase (se 4 (by rfl) ⟨64845, by rfl⟩ : syracuseStep 691685 = 129691) (by norm_num)
theorem B364013 : Blo 239816 364013 := bbase (se 3 (by rfl) ⟨68252, by rfl⟩ : syracuseStep 364013 = 136505) (by norm_num)
theorem B921077 : Blo 239816 921077 := bbase (se 5 (by rfl) ⟨43175, by rfl⟩ : syracuseStep 921077 = 86351) (by norm_num)
theorem B364037 : Blo 239816 364037 := bbase (se 4 (by rfl) ⟨34128, by rfl⟩ : syracuseStep 364037 = 68257) (by norm_num)
theorem B1379861 : Blo 239816 1379861 := bbase (se 6 (by rfl) ⟨32340, by rfl⟩ : syracuseStep 1379861 = 64681) (by norm_num)
theorem B364061 : Blo 239816 364061 := bbase (se 3 (by rfl) ⟨68261, by rfl⟩ : syracuseStep 364061 = 136523) (by norm_num)
theorem B364085 : Blo 239816 364085 := bbase (se 5 (by rfl) ⟨17066, by rfl⟩ : syracuseStep 364085 = 34133) (by norm_num)
theorem B1248821 : Blo 239816 1248821 := bbase (se 5 (by rfl) ⟨58538, by rfl⟩ : syracuseStep 1248821 = 117077) (by norm_num)
theorem B462397 : Blo 239816 462397 := bbase (se 3 (by rfl) ⟨86699, by rfl⟩ : syracuseStep 462397 = 173399) (by norm_num)
theorem B364109 : Blo 239816 364109 := bbase (se 3 (by rfl) ⟨68270, by rfl⟩ : syracuseStep 364109 = 136541) (by norm_num)
theorem B364133 : Blo 239816 364133 := bbase (se 4 (by rfl) ⟨34137, by rfl⟩ : syracuseStep 364133 = 68275) (by norm_num)
theorem B364157 : Blo 239816 364157 := bbase (se 3 (by rfl) ⟨68279, by rfl⟩ : syracuseStep 364157 = 136559) (by norm_num)
theorem B1216133 : Blo 239816 1216133 := bbase (se 4 (by rfl) ⟨114012, by rfl⟩ : syracuseStep 1216133 = 228025) (by norm_num)
theorem B364181 : Blo 239816 364181 := bbase (se 6 (by rfl) ⟨8535, by rfl⟩ : syracuseStep 364181 = 17071) (by norm_num)
theorem B364205 : Blo 239816 364205 := bbase (se 3 (by rfl) ⟨68288, by rfl⟩ : syracuseStep 364205 = 136577) (by norm_num)
theorem B364229 : Blo 239816 364229 := bbase (se 4 (by rfl) ⟨34146, by rfl⟩ : syracuseStep 364229 = 68293) (by norm_num)
theorem B364253 : Blo 239816 364253 := bbase (se 3 (by rfl) ⟨68297, by rfl⟩ : syracuseStep 364253 = 136595) (by norm_num)
theorem B364277 : Blo 239816 364277 := bbase (se 5 (by rfl) ⟨17075, by rfl⟩ : syracuseStep 364277 = 34151) (by norm_num)
theorem B462581 : Blo 239816 462581 := bbase (se 5 (by rfl) ⟨21683, by rfl⟩ : syracuseStep 462581 = 43367) (by norm_num)
theorem B364301 : Blo 239816 364301 := bbase (se 3 (by rfl) ⟨68306, by rfl⟩ : syracuseStep 364301 = 136613) (by norm_num)
theorem B921365 : Blo 239816 921365 := bbase (se 6 (by rfl) ⟨21594, by rfl⟩ : syracuseStep 921365 = 43189) (by norm_num)
theorem B364325 : Blo 239816 364325 := bbase (se 4 (by rfl) ⟨34155, by rfl⟩ : syracuseStep 364325 = 68311) (by norm_num)
theorem B364349 : Blo 239816 364349 := bbase (se 3 (by rfl) ⟨68315, by rfl⟩ : syracuseStep 364349 = 136631) (by norm_num)
theorem B560981 : Blo 239816 560981 := bbase (se 9 (by rfl) ⟨1643, by rfl⟩ : syracuseStep 560981 = 3287) (by norm_num)
theorem B364373 : Blo 239816 364373 := bbase (se 9 (by rfl) ⟨1067, by rfl⟩ : syracuseStep 364373 = 2135) (by norm_num)
theorem B364397 : Blo 239816 364397 := bbase (se 3 (by rfl) ⟨68324, by rfl⟩ : syracuseStep 364397 = 136649) (by norm_num)
theorem B364421 : Blo 239816 364421 := bbase (se 4 (by rfl) ⟨34164, by rfl⟩ : syracuseStep 364421 = 68329) (by norm_num)
theorem B1576853 : Blo 239816 1576853 := bbase (se 6 (by rfl) ⟨36957, by rfl⟩ : syracuseStep 1576853 = 73915) (by norm_num)
theorem B364445 : Blo 239816 364445 := bbase (se 3 (by rfl) ⟨68333, by rfl⟩ : syracuseStep 364445 = 136667) (by norm_num)
theorem B364469 : Blo 239816 364469 := bbase (se 5 (by rfl) ⟨17084, by rfl⟩ : syracuseStep 364469 = 34169) (by norm_num)
theorem B364493 : Blo 239816 364493 := bbase (se 3 (by rfl) ⟨68342, by rfl⟩ : syracuseStep 364493 = 136685) (by norm_num)
theorem B364517 : Blo 239816 364517 := bbase (se 4 (by rfl) ⟨34173, by rfl⟩ : syracuseStep 364517 = 68347) (by norm_num)
theorem B364541 : Blo 239816 364541 := bbase (se 3 (by rfl) ⟨68351, by rfl⟩ : syracuseStep 364541 = 136703) (by norm_num)
theorem B364565 : Blo 239816 364565 := bbase (se 6 (by rfl) ⟨8544, by rfl⟩ : syracuseStep 364565 = 17089) (by norm_num)
theorem B364589 : Blo 239816 364589 := bbase (se 3 (by rfl) ⟨68360, by rfl⟩ : syracuseStep 364589 = 136721) (by norm_num)
theorem B364613 : Blo 239816 364613 := bbase (se 4 (by rfl) ⟨34182, by rfl⟩ : syracuseStep 364613 = 68365) (by norm_num)
theorem B364637 : Blo 239816 364637 := bbase (se 3 (by rfl) ⟨68369, by rfl⟩ : syracuseStep 364637 = 136739) (by norm_num)
theorem B364661 : Blo 239816 364661 := bbase (se 5 (by rfl) ⟨17093, by rfl⟩ : syracuseStep 364661 = 34187) (by norm_num)
theorem B364685 : Blo 239816 364685 := bbase (se 3 (by rfl) ⟨68378, by rfl⟩ : syracuseStep 364685 = 136757) (by norm_num)
theorem B364709 : Blo 239816 364709 := bbase (se 4 (by rfl) ⟨34191, by rfl⟩ : syracuseStep 364709 = 68383) (by norm_num)
theorem B364733 : Blo 239816 364733 := bbase (se 3 (by rfl) ⟨68387, by rfl⟩ : syracuseStep 364733 = 136775) (by norm_num)
theorem B364757 : Blo 239816 364757 := bbase (se 7 (by rfl) ⟨4274, by rfl⟩ : syracuseStep 364757 = 8549) (by norm_num)
theorem B364781 : Blo 239816 364781 := bbase (se 3 (by rfl) ⟨68396, by rfl⟩ : syracuseStep 364781 = 136793) (by norm_num)
theorem B364805 : Blo 239816 364805 := bbase (se 4 (by rfl) ⟨34200, by rfl⟩ : syracuseStep 364805 = 68401) (by norm_num)
theorem B364829 : Blo 239816 364829 := bbase (se 3 (by rfl) ⟨68405, by rfl⟩ : syracuseStep 364829 = 136811) (by norm_num)
theorem B1544501 : Blo 239816 1544501 := bbase (se 5 (by rfl) ⟨72398, by rfl⟩ : syracuseStep 1544501 = 144797) (by norm_num)
theorem B364853 : Blo 239816 364853 := bbase (se 5 (by rfl) ⟨17102, by rfl⟩ : syracuseStep 364853 = 34205) (by norm_num)
theorem B364877 : Blo 239816 364877 := bbase (se 3 (by rfl) ⟨68414, by rfl⟩ : syracuseStep 364877 = 136829) (by norm_num)
theorem B364901 : Blo 239816 364901 := bbase (se 4 (by rfl) ⟨34209, by rfl⟩ : syracuseStep 364901 = 68419) (by norm_num)
theorem B364925 : Blo 239816 364925 := bbase (se 3 (by rfl) ⟨68423, by rfl⟩ : syracuseStep 364925 = 136847) (by norm_num)
theorem B1839509 : Blo 239816 1839509 := bbase (se 6 (by rfl) ⟨43113, by rfl⟩ : syracuseStep 1839509 = 86227) (by norm_num)
theorem B364949 : Blo 239816 364949 := bbase (se 6 (by rfl) ⟨8553, by rfl⟩ : syracuseStep 364949 = 17107) (by norm_num)
theorem B364973 : Blo 239816 364973 := bbase (se 3 (by rfl) ⟨68432, by rfl⟩ : syracuseStep 364973 = 136865) (by norm_num)
theorem B364997 : Blo 239816 364997 := bbase (se 4 (by rfl) ⟨34218, by rfl⟩ : syracuseStep 364997 = 68437) (by norm_num)
theorem B2757077 : Blo 239816 2757077 := bbase (se 7 (by rfl) ⟨32309, by rfl⟩ : syracuseStep 2757077 = 64619) (by norm_num)
theorem B365021 : Blo 239816 365021 := bbase (se 3 (by rfl) ⟨68441, by rfl⟩ : syracuseStep 365021 = 136883) (by norm_num)
theorem B365045 : Blo 239816 365045 := bbase (se 5 (by rfl) ⟨17111, by rfl⟩ : syracuseStep 365045 = 34223) (by norm_num)
theorem B365069 : Blo 239816 365069 := bbase (se 3 (by rfl) ⟨68450, by rfl⟩ : syracuseStep 365069 = 136901) (by norm_num)
theorem B365093 : Blo 239816 365093 := bbase (se 4 (by rfl) ⟨34227, by rfl⟩ : syracuseStep 365093 = 68455) (by norm_num)
theorem B561709 : Blo 239816 561709 := bbase (se 3 (by rfl) ⟨105320, by rfl⟩ : syracuseStep 561709 = 210641) (by norm_num)
theorem B365117 : Blo 239816 365117 := bbase (se 3 (by rfl) ⟨68459, by rfl⟩ : syracuseStep 365117 = 136919) (by norm_num)
theorem B365141 : Blo 239816 365141 := bbase (se 8 (by rfl) ⟨2139, by rfl⟩ : syracuseStep 365141 = 4279) (by norm_num)
theorem B365165 : Blo 239816 365165 := bbase (se 3 (by rfl) ⟨68468, by rfl⟩ : syracuseStep 365165 = 136937) (by norm_num)
theorem B692869 : Blo 239816 692869 := bbase (se 4 (by rfl) ⟨64956, by rfl⟩ : syracuseStep 692869 = 129913) (by norm_num)
theorem B365189 : Blo 239816 365189 := bbase (se 4 (by rfl) ⟨34236, by rfl⟩ : syracuseStep 365189 = 68473) (by norm_num)
theorem B365213 : Blo 239816 365213 := bbase (se 3 (by rfl) ⟨68477, by rfl⟩ : syracuseStep 365213 = 136955) (by norm_num)
theorem B365237 : Blo 239816 365237 := bbase (se 5 (by rfl) ⟨17120, by rfl⟩ : syracuseStep 365237 = 34241) (by norm_num)
theorem B365261 : Blo 239816 365261 := bbase (se 3 (by rfl) ⟨68486, by rfl⟩ : syracuseStep 365261 = 136973) (by norm_num)
theorem B365285 : Blo 239816 365285 := bbase (se 4 (by rfl) ⟨34245, by rfl⟩ : syracuseStep 365285 = 68491) (by norm_num)
theorem B365309 : Blo 239816 365309 := bbase (se 3 (by rfl) ⟨68495, by rfl⟩ : syracuseStep 365309 = 136991) (by norm_num)
theorem B365333 : Blo 239816 365333 := bbase (se 6 (by rfl) ⟨8562, by rfl⟩ : syracuseStep 365333 = 17125) (by norm_num)
theorem B693029 : Blo 239816 693029 := bbase (se 4 (by rfl) ⟨64971, by rfl⟩ : syracuseStep 693029 = 129943) (by norm_num)
theorem B365357 : Blo 239816 365357 := bbase (se 3 (by rfl) ⟨68504, by rfl⟩ : syracuseStep 365357 = 137009) (by norm_num)
theorem B365381 : Blo 239816 365381 := bbase (se 4 (by rfl) ⟨34254, by rfl⟩ : syracuseStep 365381 = 68509) (by norm_num)
theorem B365405 : Blo 239816 365405 := bbase (se 3 (by rfl) ⟨68513, by rfl⟩ : syracuseStep 365405 = 137027) (by norm_num)
theorem B365429 : Blo 239816 365429 := bbase (se 5 (by rfl) ⟨17129, by rfl⟩ : syracuseStep 365429 = 34259) (by norm_num)
theorem B365453 : Blo 239816 365453 := bbase (se 3 (by rfl) ⟨68522, by rfl⟩ : syracuseStep 365453 = 137045) (by norm_num)
theorem B1217429 : Blo 239816 1217429 := bbase (se 6 (by rfl) ⟨28533, by rfl⟩ : syracuseStep 1217429 = 57067) (by norm_num)
theorem B365477 : Blo 239816 365477 := bbase (se 4 (by rfl) ⟨34263, by rfl⟩ : syracuseStep 365477 = 68527) (by norm_num)
theorem B922549 : Blo 239816 922549 := bbase (se 5 (by rfl) ⟨43244, by rfl⟩ : syracuseStep 922549 = 86489) (by norm_num)
theorem B365501 : Blo 239816 365501 := bbase (se 3 (by rfl) ⟨68531, by rfl⟩ : syracuseStep 365501 = 137063) (by norm_num)
theorem B365525 : Blo 239816 365525 := bbase (se 7 (by rfl) ⟨4283, by rfl⟩ : syracuseStep 365525 = 8567) (by norm_num)
theorem B365549 : Blo 239816 365549 := bbase (se 3 (by rfl) ⟨68540, by rfl⟩ : syracuseStep 365549 = 137081) (by norm_num)
theorem B365573 : Blo 239816 365573 := bbase (se 4 (by rfl) ⟨34272, by rfl⟩ : syracuseStep 365573 = 68545) (by norm_num)
theorem B693269 : Blo 239816 693269 := bbase (se 6 (by rfl) ⟨16248, by rfl⟩ : syracuseStep 693269 = 32497) (by norm_num)
theorem B365597 : Blo 239816 365597 := bbase (se 3 (by rfl) ⟨68549, by rfl⟩ : syracuseStep 365597 = 137099) (by norm_num)
theorem B365621 : Blo 239816 365621 := bbase (se 5 (by rfl) ⟨17138, by rfl⟩ : syracuseStep 365621 = 34277) (by norm_num)
theorem B365645 : Blo 239816 365645 := bbase (se 3 (by rfl) ⟨68558, by rfl⟩ : syracuseStep 365645 = 137117) (by norm_num)
theorem B365669 : Blo 239816 365669 := bbase (se 4 (by rfl) ⟨34281, by rfl⟩ : syracuseStep 365669 = 68563) (by norm_num)
theorem B365693 : Blo 239816 365693 := bbase (se 3 (by rfl) ⟨68567, by rfl⟩ : syracuseStep 365693 = 137135) (by norm_num)
theorem B365717 : Blo 239816 365717 := bbase (se 6 (by rfl) ⟨8571, by rfl⟩ : syracuseStep 365717 = 17143) (by norm_num)
theorem B693461 : Blo 239816 693461 := bbase (se 7 (by rfl) ⟨8126, by rfl⟩ : syracuseStep 693461 = 16253) (by norm_num)
theorem B922853 : Blo 239816 922853 := bbase (se 4 (by rfl) ⟨86517, by rfl⟩ : syracuseStep 922853 = 173035) (by norm_num)
theorem B890677 : Blo 239816 890677 := bbase (se 5 (by rfl) ⟨41750, by rfl⟩ : syracuseStep 890677 = 83501) (by norm_num)
theorem B1218725 : Blo 239816 1218725 := bbase (se 4 (by rfl) ⟨114255, by rfl⟩ : syracuseStep 1218725 = 228511) (by norm_num)
theorem B432373 : Blo 239816 432373 := bbase (se 5 (by rfl) ⟨20267, by rfl⟩ : syracuseStep 432373 = 40535) (by norm_num)
theorem B432677 : Blo 239816 432677 := bbase (se 4 (by rfl) ⟨40563, by rfl⟩ : syracuseStep 432677 = 81127) (by norm_num)
theorem B367613 : Blo 239816 367613 := bbase (se 3 (by rfl) ⟨68927, by rfl⟩ : syracuseStep 367613 = 137855) (by norm_num)
theorem B662581 : Blo 239816 662581 := bbase (se 5 (by rfl) ⟨31058, by rfl⟩ : syracuseStep 662581 = 62117) (by norm_num)
theorem B1023205 : Blo 239816 1023205 := bbase (se 4 (by rfl) ⟨95925, by rfl⟩ : syracuseStep 1023205 = 191851) (by norm_num)
theorem B924965 : Blo 239816 924965 := bbase (se 4 (by rfl) ⟨86715, by rfl⟩ : syracuseStep 924965 = 173431) (by norm_num)
theorem B1220021 : Blo 239816 1220021 := bbase (se 5 (by rfl) ⟨57188, by rfl⟩ : syracuseStep 1220021 = 114377) (by norm_num)
theorem B433613 : Blo 239816 433613 := bbase (se 3 (by rfl) ⟨81302, by rfl⟩ : syracuseStep 433613 = 162605) (by norm_num)
theorem B269797 : Blo 239816 269797 := bbase (se 4 (by rfl) ⟨25293, by rfl⟩ : syracuseStep 269797 = 50587) (by norm_num)
theorem B269833 : Blo 239816 269833 := bbase (se 2 (by rfl) ⟨101187, by rfl⟩ : syracuseStep 269833 = 202375) (by norm_num)
theorem B3317269 : Blo 239816 3317269 := bbase (se 6 (by rfl) ⟨77748, by rfl⟩ : syracuseStep 3317269 = 155497) (by norm_num)
theorem B269869 : Blo 239816 269869 := bbase (se 3 (by rfl) ⟨50600, by rfl⟩ : syracuseStep 269869 = 101201) (by norm_num)
theorem B925253 : Blo 239816 925253 := bbase (se 4 (by rfl) ⟨86742, by rfl⟩ : syracuseStep 925253 = 173485) (by norm_num)
theorem B269905 : Blo 239816 269905 := bbase (se 2 (by rfl) ⟨101214, by rfl⟩ : syracuseStep 269905 = 202429) (by norm_num)
theorem B368221 : Blo 239816 368221 := bbase (se 3 (by rfl) ⟨69041, by rfl⟩ : syracuseStep 368221 = 138083) (by norm_num)
theorem B269941 : Blo 239816 269941 := bbase (se 5 (by rfl) ⟨12653, by rfl⟩ : syracuseStep 269941 = 25307) (by norm_num)
theorem B269977 : Blo 239816 269977 := bbase (se 2 (by rfl) ⟨101241, by rfl⟩ : syracuseStep 269977 = 202483) (by norm_num)
theorem B1482421 : Blo 239816 1482421 := bbase (se 5 (by rfl) ⟨69488, by rfl⟩ : syracuseStep 1482421 = 138977) (by norm_num)
theorem B270013 : Blo 239816 270013 := bbase (se 3 (by rfl) ⟨50627, by rfl⟩ : syracuseStep 270013 = 101255) (by norm_num)
theorem B270049 : Blo 239816 270049 := bbase (se 2 (by rfl) ⟨101268, by rfl⟩ : syracuseStep 270049 = 202537) (by norm_num)
theorem B270085 : Blo 239816 270085 := bbase (se 4 (by rfl) ⟨25320, by rfl⟩ : syracuseStep 270085 = 50641) (by norm_num)
theorem B270121 : Blo 239816 270121 := bbase (se 2 (by rfl) ⟨101295, by rfl⟩ : syracuseStep 270121 = 202591) (by norm_num)
theorem B270157 : Blo 239816 270157 := bbase (se 3 (by rfl) ⟨50654, by rfl⟩ : syracuseStep 270157 = 101309) (by norm_num)
theorem B270193 : Blo 239816 270193 := bbase (se 2 (by rfl) ⟨101322, by rfl⟩ : syracuseStep 270193 = 202645) (by norm_num)
theorem B270229 : Blo 239816 270229 := bbase (se 6 (by rfl) ⟨6333, by rfl⟩ : syracuseStep 270229 = 12667) (by norm_num)
theorem B270265 : Blo 239816 270265 := bbase (se 2 (by rfl) ⟨101349, by rfl⟩ : syracuseStep 270265 = 202699) (by norm_num)
theorem B2957269 : Blo 239816 2957269 := bbase (se 7 (by rfl) ⟨34655, by rfl⟩ : syracuseStep 2957269 = 69311) (by norm_num)
theorem B270301 : Blo 239816 270301 := bbase (se 3 (by rfl) ⟨50681, by rfl⟩ : syracuseStep 270301 = 101363) (by norm_num)
theorem B270337 : Blo 239816 270337 := bbase (se 2 (by rfl) ⟨101376, by rfl⟩ : syracuseStep 270337 = 202753) (by norm_num)
theorem B270373 : Blo 239816 270373 := bbase (se 4 (by rfl) ⟨25347, by rfl⟩ : syracuseStep 270373 = 50695) (by norm_num)
theorem B270409 : Blo 239816 270409 := bbase (se 2 (by rfl) ⟨101403, by rfl⟩ : syracuseStep 270409 = 202807) (by norm_num)
theorem B270445 : Blo 239816 270445 := bbase (se 3 (by rfl) ⟨50708, by rfl⟩ : syracuseStep 270445 = 101417) (by norm_num)
theorem B270481 : Blo 239816 270481 := bbase (se 2 (by rfl) ⟨101430, by rfl⟩ : syracuseStep 270481 = 202861) (by norm_num)
theorem B270517 : Blo 239816 270517 := bbase (se 5 (by rfl) ⟨12680, by rfl⟩ : syracuseStep 270517 = 25361) (by norm_num)
theorem B270553 : Blo 239816 270553 := bbase (se 2 (by rfl) ⟨101457, by rfl⟩ : syracuseStep 270553 = 202915) (by norm_num)
theorem B270589 : Blo 239816 270589 := bbase (se 3 (by rfl) ⟨50735, by rfl⟩ : syracuseStep 270589 = 101471) (by norm_num)
theorem B270625 : Blo 239816 270625 := bbase (se 2 (by rfl) ⟨101484, by rfl⟩ : syracuseStep 270625 = 202969) (by norm_num)
theorem B270661 : Blo 239816 270661 := bbase (se 4 (by rfl) ⟨25374, by rfl⟩ : syracuseStep 270661 = 50749) (by norm_num)
theorem B270697 : Blo 239816 270697 := bbase (se 2 (by rfl) ⟨101511, by rfl⟩ : syracuseStep 270697 = 203023) (by norm_num)
theorem B270733 : Blo 239816 270733 := bbase (se 3 (by rfl) ⟨50762, by rfl⟩ : syracuseStep 270733 = 101525) (by norm_num)
theorem B270769 : Blo 239816 270769 := bbase (se 2 (by rfl) ⟨101538, by rfl⟩ : syracuseStep 270769 = 203077) (by norm_num)
theorem B270805 : Blo 239816 270805 := bbase (se 7 (by rfl) ⟨3173, by rfl⟩ : syracuseStep 270805 = 6347) (by norm_num)
theorem B270841 : Blo 239816 270841 := bbase (se 2 (by rfl) ⟨101565, by rfl⟩ : syracuseStep 270841 = 203131) (by norm_num)
theorem B270877 : Blo 239816 270877 := bbase (se 3 (by rfl) ⟨50789, by rfl⟩ : syracuseStep 270877 = 101579) (by norm_num)
theorem B270913 : Blo 239816 270913 := bbase (se 2 (by rfl) ⟨101592, by rfl⟩ : syracuseStep 270913 = 203185) (by norm_num)
theorem B303689 : Blo 239816 303689 := bbase (se 2 (by rfl) ⟨113883, by rfl⟩ : syracuseStep 303689 = 227767) (by norm_num)
theorem B270949 : Blo 239816 270949 := bbase (se 4 (by rfl) ⟨25401, by rfl⟩ : syracuseStep 270949 = 50803) (by norm_num)
theorem B303745 : Blo 239816 303745 := bbase (se 2 (by rfl) ⟨113904, by rfl⟩ : syracuseStep 303745 = 227809) (by norm_num)
theorem B270985 : Blo 239816 270985 := bbase (se 2 (by rfl) ⟨101619, by rfl⟩ : syracuseStep 270985 = 203239) (by norm_num)
theorem B271021 : Blo 239816 271021 := bbase (se 3 (by rfl) ⟨50816, by rfl⟩ : syracuseStep 271021 = 101633) (by norm_num)
theorem B1221317 : Blo 239816 1221317 := bbase (se 4 (by rfl) ⟨114498, by rfl⟩ : syracuseStep 1221317 = 228997) (by norm_num)
theorem B271057 : Blo 239816 271057 := bbase (se 2 (by rfl) ⟨101646, by rfl⟩ : syracuseStep 271057 = 203293) (by norm_num)
theorem B303841 : Blo 239816 303841 := bbase (se 2 (by rfl) ⟨113940, by rfl⟩ : syracuseStep 303841 = 227881) (by norm_num)
theorem B271093 : Blo 239816 271093 := bbase (se 5 (by rfl) ⟨12707, by rfl⟩ : syracuseStep 271093 = 25415) (by norm_num)
theorem B271129 : Blo 239816 271129 := bbase (se 2 (by rfl) ⟨101673, by rfl⟩ : syracuseStep 271129 = 203347) (by norm_num)
theorem B271165 : Blo 239816 271165 := bbase (se 3 (by rfl) ⟨50843, by rfl⟩ : syracuseStep 271165 = 101687) (by norm_num)
theorem B271201 : Blo 239816 271201 := bbase (se 2 (by rfl) ⟨101700, by rfl⟩ : syracuseStep 271201 = 203401) (by norm_num)
theorem B992101 : Blo 239816 992101 := bbase (se 4 (by rfl) ⟨93009, by rfl⟩ : syracuseStep 992101 = 186019) (by norm_num)
theorem B271237 : Blo 239816 271237 := bbase (se 4 (by rfl) ⟨25428, by rfl⟩ : syracuseStep 271237 = 50857) (by norm_num)
theorem B304013 : Blo 239816 304013 := bbase (se 3 (by rfl) ⟨57002, by rfl⟩ : syracuseStep 304013 = 114005) (by norm_num)
theorem B271273 : Blo 239816 271273 := bbase (se 2 (by rfl) ⟨101727, by rfl⟩ : syracuseStep 271273 = 203455) (by norm_num)
theorem B304069 : Blo 239816 304069 := bbase (se 4 (by rfl) ⟨28506, by rfl⟩ : syracuseStep 304069 = 57013) (by norm_num)
theorem B271309 : Blo 239816 271309 := bbase (se 3 (by rfl) ⟨50870, by rfl⟩ : syracuseStep 271309 = 101741) (by norm_num)
theorem B1156069 : Blo 239816 1156069 := bbase (se 4 (by rfl) ⟨108381, by rfl⟩ : syracuseStep 1156069 = 216763) (by norm_num)
theorem B271345 : Blo 239816 271345 := bbase (se 2 (by rfl) ⟨101754, by rfl⟩ : syracuseStep 271345 = 203509) (by norm_num)
theorem B271381 : Blo 239816 271381 := bbase (se 6 (by rfl) ⟨6360, by rfl⟩ : syracuseStep 271381 = 12721) (by norm_num)
theorem B304165 : Blo 239816 304165 := bbase (se 4 (by rfl) ⟨28515, by rfl⟩ : syracuseStep 304165 = 57031) (by norm_num)
theorem B271417 : Blo 239816 271417 := bbase (se 2 (by rfl) ⟨101781, by rfl⟩ : syracuseStep 271417 = 203563) (by norm_num)
theorem B271453 : Blo 239816 271453 := bbase (se 3 (by rfl) ⟨50897, by rfl⟩ : syracuseStep 271453 = 101795) (by norm_num)
theorem B271489 : Blo 239816 271489 := bbase (se 2 (by rfl) ⟨101808, by rfl⟩ : syracuseStep 271489 = 203617) (by norm_num)
theorem B271525 : Blo 239816 271525 := bbase (se 4 (by rfl) ⟨25455, by rfl⟩ : syracuseStep 271525 = 50911) (by norm_num)
theorem B271561 : Blo 239816 271561 := bbase (se 2 (by rfl) ⟨101835, by rfl⟩ : syracuseStep 271561 = 203671) (by norm_num)
theorem B304337 : Blo 239816 304337 := bbase (se 2 (by rfl) ⟨114126, by rfl⟩ : syracuseStep 304337 = 228253) (by norm_num)
theorem B271597 : Blo 239816 271597 := bbase (se 3 (by rfl) ⟨50924, by rfl⟩ : syracuseStep 271597 = 101849) (by norm_num)
theorem B304393 : Blo 239816 304393 := bbase (se 2 (by rfl) ⟨114147, by rfl⟩ : syracuseStep 304393 = 228295) (by norm_num)
theorem B271633 : Blo 239816 271633 := bbase (se 2 (by rfl) ⟨101862, by rfl⟩ : syracuseStep 271633 = 203725) (by norm_num)
theorem B271669 : Blo 239816 271669 := bbase (se 5 (by rfl) ⟨12734, by rfl⟩ : syracuseStep 271669 = 25469) (by norm_num)
theorem B271705 : Blo 239816 271705 := bbase (se 2 (by rfl) ⟨101889, by rfl⟩ : syracuseStep 271705 = 203779) (by norm_num)
theorem B304489 : Blo 239816 304489 := bbase (se 2 (by rfl) ⟨114183, by rfl⟩ : syracuseStep 304489 = 228367) (by norm_num)
theorem B664949 : Blo 239816 664949 := bbase (se 5 (by rfl) ⟨31169, by rfl⟩ : syracuseStep 664949 = 62339) (by norm_num)
theorem B271741 : Blo 239816 271741 := bbase (se 3 (by rfl) ⟨50951, by rfl⟩ : syracuseStep 271741 = 101903) (by norm_num)
theorem B271777 : Blo 239816 271777 := bbase (se 2 (by rfl) ⟨101916, by rfl⟩ : syracuseStep 271777 = 203833) (by norm_num)
theorem B271813 : Blo 239816 271813 := bbase (se 4 (by rfl) ⟨25482, by rfl⟩ : syracuseStep 271813 = 50965) (by norm_num)
theorem B271849 : Blo 239816 271849 := bbase (se 2 (by rfl) ⟨101943, by rfl⟩ : syracuseStep 271849 = 203887) (by norm_num)
theorem B271885 : Blo 239816 271885 := bbase (se 3 (by rfl) ⟨50978, by rfl⟩ : syracuseStep 271885 = 101957) (by norm_num)
theorem B304661 : Blo 239816 304661 := bbase (se 6 (by rfl) ⟨7140, by rfl⟩ : syracuseStep 304661 = 14281) (by norm_num)
theorem B271921 : Blo 239816 271921 := bbase (se 2 (by rfl) ⟨101970, by rfl⟩ : syracuseStep 271921 = 203941) (by norm_num)
theorem B304717 : Blo 239816 304717 := bbase (se 3 (by rfl) ⟨57134, by rfl⟩ : syracuseStep 304717 = 114269) (by norm_num)
theorem B271957 : Blo 239816 271957 := bbase (se 8 (by rfl) ⟨1593, by rfl⟩ : syracuseStep 271957 = 3187) (by norm_num)
theorem B271993 : Blo 239816 271993 := bbase (se 2 (by rfl) ⟨101997, by rfl⟩ : syracuseStep 271993 = 203995) (by norm_num)
theorem B272029 : Blo 239816 272029 := bbase (se 3 (by rfl) ⟨51005, by rfl⟩ : syracuseStep 272029 = 102011) (by norm_num)
theorem B304813 : Blo 239816 304813 := bbase (se 3 (by rfl) ⟨57152, by rfl⟩ : syracuseStep 304813 = 114305) (by norm_num)
theorem B272065 : Blo 239816 272065 := bbase (se 2 (by rfl) ⟨102024, by rfl⟩ : syracuseStep 272065 = 204049) (by norm_num)
theorem B272101 : Blo 239816 272101 := bbase (se 4 (by rfl) ⟨25509, by rfl⟩ : syracuseStep 272101 = 51019) (by norm_num)
theorem B272137 : Blo 239816 272137 := bbase (se 2 (by rfl) ⟨102051, by rfl⟩ : syracuseStep 272137 = 204103) (by norm_num)
theorem B272173 : Blo 239816 272173 := bbase (se 3 (by rfl) ⟨51032, by rfl⟩ : syracuseStep 272173 = 102065) (by norm_num)
theorem B272209 : Blo 239816 272209 := bbase (se 2 (by rfl) ⟨102078, by rfl⟩ : syracuseStep 272209 = 204157) (by norm_num)
theorem B304985 : Blo 239816 304985 := bbase (se 2 (by rfl) ⟨114369, by rfl⟩ : syracuseStep 304985 = 228739) (by norm_num)
theorem B1025909 : Blo 239816 1025909 := bbase (se 5 (by rfl) ⟨48089, by rfl⟩ : syracuseStep 1025909 = 96179) (by norm_num)
theorem B272245 : Blo 239816 272245 := bbase (se 5 (by rfl) ⟨12761, by rfl⟩ : syracuseStep 272245 = 25523) (by norm_num)
theorem B305041 : Blo 239816 305041 := bbase (se 2 (by rfl) ⟨114390, by rfl⟩ : syracuseStep 305041 = 228781) (by norm_num)
theorem B272281 : Blo 239816 272281 := bbase (se 2 (by rfl) ⟨102105, by rfl⟩ : syracuseStep 272281 = 204211) (by norm_num)
theorem B272317 : Blo 239816 272317 := bbase (se 3 (by rfl) ⟨51059, by rfl⟩ : syracuseStep 272317 = 102119) (by norm_num)
theorem B1222613 : Blo 239816 1222613 := bbase (se 7 (by rfl) ⟨14327, by rfl⟩ : syracuseStep 1222613 = 28655) (by norm_num)
theorem B272353 : Blo 239816 272353 := bbase (se 2 (by rfl) ⟨102132, by rfl⟩ : syracuseStep 272353 = 204265) (by norm_num)
theorem B305137 : Blo 239816 305137 := bbase (se 2 (by rfl) ⟨114426, by rfl⟩ : syracuseStep 305137 = 228853) (by norm_num)
theorem B272389 : Blo 239816 272389 := bbase (se 4 (by rfl) ⟨25536, by rfl⟩ : syracuseStep 272389 = 51073) (by norm_num)
theorem B272425 : Blo 239816 272425 := bbase (se 2 (by rfl) ⟨102159, by rfl⟩ : syracuseStep 272425 = 204319) (by norm_num)
theorem B272461 : Blo 239816 272461 := bbase (se 3 (by rfl) ⟨51086, by rfl⟩ : syracuseStep 272461 = 102173) (by norm_num)
theorem B272497 : Blo 239816 272497 := bbase (se 2 (by rfl) ⟨102186, by rfl⟩ : syracuseStep 272497 = 204373) (by norm_num)
theorem B272533 : Blo 239816 272533 := bbase (se 6 (by rfl) ⟨6387, by rfl⟩ : syracuseStep 272533 = 12775) (by norm_num)
theorem B305309 : Blo 239816 305309 := bbase (se 3 (by rfl) ⟨57245, by rfl⟩ : syracuseStep 305309 = 114491) (by norm_num)
theorem B272569 : Blo 239816 272569 := bbase (se 2 (by rfl) ⟨102213, by rfl⟩ : syracuseStep 272569 = 204427) (by norm_num)
theorem B305365 : Blo 239816 305365 := bbase (se 7 (by rfl) ⟨3578, by rfl⟩ : syracuseStep 305365 = 7157) (by norm_num)
theorem B272605 : Blo 239816 272605 := bbase (se 3 (by rfl) ⟨51113, by rfl⟩ : syracuseStep 272605 = 102227) (by norm_num)
theorem B272641 : Blo 239816 272641 := bbase (se 2 (by rfl) ⟨102240, by rfl⟩ : syracuseStep 272641 = 204481) (by norm_num)
theorem B272677 : Blo 239816 272677 := bbase (se 4 (by rfl) ⟨25563, by rfl⟩ : syracuseStep 272677 = 51127) (by norm_num)
theorem B305461 : Blo 239816 305461 := bbase (se 5 (by rfl) ⟨14318, by rfl⟩ : syracuseStep 305461 = 28637) (by norm_num)
theorem B272713 : Blo 239816 272713 := bbase (se 2 (by rfl) ⟨102267, by rfl⟩ : syracuseStep 272713 = 204535) (by norm_num)
theorem B272749 : Blo 239816 272749 := bbase (se 3 (by rfl) ⟨51140, by rfl⟩ : syracuseStep 272749 = 102281) (by norm_num)
theorem B2107765 : Blo 239816 2107765 := bbase (se 5 (by rfl) ⟨98801, by rfl⟩ : syracuseStep 2107765 = 197603) (by norm_num)
theorem B272785 : Blo 239816 272785 := bbase (se 2 (by rfl) ⟨102294, by rfl⟩ : syracuseStep 272785 = 204589) (by norm_num)
theorem B1321397 : Blo 239816 1321397 := bbase (se 5 (by rfl) ⟨61940, by rfl⟩ : syracuseStep 1321397 = 123881) (by norm_num)
theorem B272821 : Blo 239816 272821 := bbase (se 5 (by rfl) ⟨12788, by rfl⟩ : syracuseStep 272821 = 25577) (by norm_num)
theorem B272857 : Blo 239816 272857 := bbase (se 2 (by rfl) ⟨102321, by rfl⟩ : syracuseStep 272857 = 204643) (by norm_num)
theorem B305633 : Blo 239816 305633 := bbase (se 2 (by rfl) ⟨114612, by rfl⟩ : syracuseStep 305633 = 229225) (by norm_num)
theorem B272893 : Blo 239816 272893 := bbase (se 3 (by rfl) ⟨51167, by rfl⟩ : syracuseStep 272893 = 102335) (by norm_num)
theorem B305689 : Blo 239816 305689 := bbase (se 2 (by rfl) ⟨114633, by rfl⟩ : syracuseStep 305689 = 229267) (by norm_num)
theorem B272929 : Blo 239816 272929 := bbase (se 2 (by rfl) ⟨102348, by rfl⟩ : syracuseStep 272929 = 204697) (by norm_num)
theorem B371237 : Blo 239816 371237 := bbase (se 4 (by rfl) ⟨34803, by rfl⟩ : syracuseStep 371237 = 69607) (by norm_num)
theorem B272965 : Blo 239816 272965 := bbase (se 4 (by rfl) ⟨25590, by rfl⟩ : syracuseStep 272965 = 51181) (by norm_num)
theorem B273001 : Blo 239816 273001 := bbase (se 2 (by rfl) ⟨102375, by rfl⟩ : syracuseStep 273001 = 204751) (by norm_num)
theorem B305785 : Blo 239816 305785 := bbase (se 2 (by rfl) ⟨114669, by rfl⟩ : syracuseStep 305785 = 229339) (by norm_num)
theorem B273037 : Blo 239816 273037 := bbase (se 3 (by rfl) ⟨51194, by rfl⟩ : syracuseStep 273037 = 102389) (by norm_num)
theorem B273073 : Blo 239816 273073 := bbase (se 2 (by rfl) ⟨102402, by rfl⟩ : syracuseStep 273073 = 204805) (by norm_num)
theorem B273109 : Blo 239816 273109 := bbase (se 7 (by rfl) ⟨3200, by rfl⟩ : syracuseStep 273109 = 6401) (by norm_num)
theorem B273145 : Blo 239816 273145 := bbase (se 2 (by rfl) ⟨102429, by rfl⟩ : syracuseStep 273145 = 204859) (by norm_num)
theorem B273181 : Blo 239816 273181 := bbase (se 3 (by rfl) ⟨51221, by rfl⟩ : syracuseStep 273181 = 102443) (by norm_num)
theorem B305957 : Blo 239816 305957 := bbase (se 4 (by rfl) ⟨28683, by rfl⟩ : syracuseStep 305957 = 57367) (by norm_num)
theorem B273217 : Blo 239816 273217 := bbase (se 2 (by rfl) ⟨102456, by rfl⟩ : syracuseStep 273217 = 204913) (by norm_num)
theorem B306013 : Blo 239816 306013 := bbase (se 3 (by rfl) ⟨57377, by rfl⟩ : syracuseStep 306013 = 114755) (by norm_num)
theorem B273253 : Blo 239816 273253 := bbase (se 4 (by rfl) ⟨25617, by rfl⟩ : syracuseStep 273253 = 51235) (by norm_num)
theorem B273289 : Blo 239816 273289 := bbase (se 2 (by rfl) ⟨102483, by rfl⟩ : syracuseStep 273289 = 204967) (by norm_num)
theorem B732053 : Blo 239816 732053 := bbase (se 6 (by rfl) ⟨17157, by rfl⟩ : syracuseStep 732053 = 34315) (by norm_num)
theorem B273325 : Blo 239816 273325 := bbase (se 3 (by rfl) ⟨51248, by rfl⟩ : syracuseStep 273325 = 102497) (by norm_num)
theorem B306109 : Blo 239816 306109 := bbase (se 3 (by rfl) ⟨57395, by rfl⟩ : syracuseStep 306109 = 114791) (by norm_num)
theorem B273361 : Blo 239816 273361 := bbase (se 2 (by rfl) ⟨102510, by rfl⟩ : syracuseStep 273361 = 205021) (by norm_num)
theorem B273397 : Blo 239816 273397 := bbase (se 5 (by rfl) ⟨12815, by rfl⟩ : syracuseStep 273397 = 25631) (by norm_num)
theorem B273433 : Blo 239816 273433 := bbase (se 2 (by rfl) ⟨102537, by rfl⟩ : syracuseStep 273433 = 205075) (by norm_num)
theorem B273469 : Blo 239816 273469 := bbase (se 3 (by rfl) ⟨51275, by rfl⟩ : syracuseStep 273469 = 102551) (by norm_num)
theorem B273505 : Blo 239816 273505 := bbase (se 2 (by rfl) ⟨102564, by rfl⟩ : syracuseStep 273505 = 205129) (by norm_num)
theorem B306281 : Blo 239816 306281 := bbase (se 2 (by rfl) ⟨114855, by rfl⟩ : syracuseStep 306281 = 229711) (by norm_num)
theorem B273541 : Blo 239816 273541 := bbase (se 4 (by rfl) ⟨25644, by rfl⟩ : syracuseStep 273541 = 51289) (by norm_num)
theorem B306337 : Blo 239816 306337 := bbase (se 2 (by rfl) ⟨114876, by rfl⟩ : syracuseStep 306337 = 229753) (by norm_num)
theorem B273577 : Blo 239816 273577 := bbase (se 2 (by rfl) ⟨102591, by rfl⟩ : syracuseStep 273577 = 205183) (by norm_num)
theorem B273613 : Blo 239816 273613 := bbase (se 3 (by rfl) ⟨51302, by rfl⟩ : syracuseStep 273613 = 102605) (by norm_num)
theorem B1223909 : Blo 239816 1223909 := bbase (se 4 (by rfl) ⟨114741, by rfl⟩ : syracuseStep 1223909 = 229483) (by norm_num)
theorem B273649 : Blo 239816 273649 := bbase (se 2 (by rfl) ⟨102618, by rfl⟩ : syracuseStep 273649 = 205237) (by norm_num)
theorem B306433 : Blo 239816 306433 := bbase (se 2 (by rfl) ⟨114912, by rfl⟩ : syracuseStep 306433 = 229825) (by norm_num)
theorem B273685 : Blo 239816 273685 := bbase (se 6 (by rfl) ⟨6414, by rfl⟩ : syracuseStep 273685 = 12829) (by norm_num)
theorem B273721 : Blo 239816 273721 := bbase (se 2 (by rfl) ⟨102645, by rfl⟩ : syracuseStep 273721 = 205291) (by norm_num)
theorem B404797 : Blo 239816 404797 := bbase (se 3 (by rfl) ⟨75899, by rfl⟩ : syracuseStep 404797 = 151799) (by norm_num)
theorem B273757 : Blo 239816 273757 := bbase (se 3 (by rfl) ⟨51329, by rfl⟩ : syracuseStep 273757 = 102659) (by norm_num)
theorem B273793 : Blo 239816 273793 := bbase (se 2 (by rfl) ⟨102672, by rfl⟩ : syracuseStep 273793 = 205345) (by norm_num)
theorem B404885 : Blo 239816 404885 := bbase (se 6 (by rfl) ⟨9489, by rfl⟩ : syracuseStep 404885 = 18979) (by norm_num)
theorem B1387925 : Blo 239816 1387925 := bbase (se 6 (by rfl) ⟨32529, by rfl⟩ : syracuseStep 1387925 = 65059) (by norm_num)
theorem B273829 : Blo 239816 273829 := bbase (se 4 (by rfl) ⟨25671, by rfl⟩ : syracuseStep 273829 = 51343) (by norm_num)
theorem B306605 : Blo 239816 306605 := bbase (se 3 (by rfl) ⟨57488, by rfl⟩ : syracuseStep 306605 = 114977) (by norm_num)
theorem B1748405 : Blo 239816 1748405 := bbase (se 5 (by rfl) ⟨81956, by rfl⟩ : syracuseStep 1748405 = 163913) (by norm_num)
theorem B273865 : Blo 239816 273865 := bbase (se 2 (by rfl) ⟨102699, by rfl⟩ : syracuseStep 273865 = 205399) (by norm_num)
theorem B306661 : Blo 239816 306661 := bbase (se 4 (by rfl) ⟨28749, by rfl⟩ : syracuseStep 306661 = 57499) (by norm_num)
theorem B273901 : Blo 239816 273901 := bbase (se 3 (by rfl) ⟨51356, by rfl⟩ : syracuseStep 273901 = 102713) (by norm_num)
theorem B273937 : Blo 239816 273937 := bbase (se 2 (by rfl) ⟨102726, by rfl⟩ : syracuseStep 273937 = 205453) (by norm_num)
theorem B405013 : Blo 239816 405013 := bbase (se 6 (by rfl) ⟨9492, by rfl⟩ : syracuseStep 405013 = 18985) (by norm_num)
theorem B798245 : Blo 239816 798245 := bbase (se 4 (by rfl) ⟨74835, by rfl⟩ : syracuseStep 798245 = 149671) (by norm_num)
theorem B273973 : Blo 239816 273973 := bbase (se 5 (by rfl) ⟨12842, by rfl⟩ : syracuseStep 273973 = 25685) (by norm_num)
theorem B306757 : Blo 239816 306757 := bbase (se 4 (by rfl) ⟨28758, by rfl⟩ : syracuseStep 306757 = 57517) (by norm_num)
theorem B274009 : Blo 239816 274009 := bbase (se 2 (by rfl) ⟨102753, by rfl⟩ : syracuseStep 274009 = 205507) (by norm_num)
theorem B405101 : Blo 239816 405101 := bbase (se 3 (by rfl) ⟨75956, by rfl⟩ : syracuseStep 405101 = 151913) (by norm_num)
theorem B274045 : Blo 239816 274045 := bbase (se 3 (by rfl) ⟨51383, by rfl⟩ : syracuseStep 274045 = 102767) (by norm_num)
theorem B274081 : Blo 239816 274081 := bbase (se 2 (by rfl) ⟨102780, by rfl⟩ : syracuseStep 274081 = 205561) (by norm_num)
theorem B274117 : Blo 239816 274117 := bbase (se 4 (by rfl) ⟨25698, by rfl⟩ : syracuseStep 274117 = 51397) (by norm_num)
theorem B437981 : Blo 239816 437981 := bbase (se 3 (by rfl) ⟨82121, by rfl⟩ : syracuseStep 437981 = 164243) (by norm_num)
theorem B241385 : Blo 239816 241385 := bbase (se 2 (by rfl) ⟨90519, by rfl⟩ : syracuseStep 241385 = 181039) (by norm_num)
theorem B274153 : Blo 239816 274153 := bbase (se 2 (by rfl) ⟨102807, by rfl⟩ : syracuseStep 274153 = 205615) (by norm_num)
theorem B405229 : Blo 239816 405229 := bbase (se 3 (by rfl) ⟨75980, by rfl⟩ : syracuseStep 405229 = 151961) (by norm_num)
theorem B306929 : Blo 239816 306929 := bbase (se 2 (by rfl) ⟨115098, by rfl⟩ : syracuseStep 306929 = 230197) (by norm_num)
theorem B274189 : Blo 239816 274189 := bbase (se 3 (by rfl) ⟨51410, by rfl⟩ : syracuseStep 274189 = 102821) (by norm_num)
theorem B306985 : Blo 239816 306985 := bbase (se 2 (by rfl) ⟨115119, by rfl⟩ : syracuseStep 306985 = 230239) (by norm_num)
theorem B274225 : Blo 239816 274225 := bbase (se 2 (by rfl) ⟨102834, by rfl⟩ : syracuseStep 274225 = 205669) (by norm_num)
theorem B405317 : Blo 239816 405317 := bbase (se 4 (by rfl) ⟨37998, by rfl⟩ : syracuseStep 405317 = 75997) (by norm_num)
theorem B274261 : Blo 239816 274261 := bbase (se 9 (by rfl) ⟨803, by rfl⟩ : syracuseStep 274261 = 1607) (by norm_num)
theorem B307081 : Blo 239816 307081 := bbase (se 2 (by rfl) ⟨115155, by rfl⟩ : syracuseStep 307081 = 230311) (by norm_num)
theorem B405445 : Blo 239816 405445 := bbase (se 4 (by rfl) ⟨38010, by rfl⟩ : syracuseStep 405445 = 76021) (by norm_num)
theorem B1847285 : Blo 239816 1847285 := bbase (se 5 (by rfl) ⟨86591, by rfl⟩ : syracuseStep 1847285 = 173183) (by norm_num)
theorem B2306069 : Blo 239816 2306069 := bbase (se 6 (by rfl) ⟨54048, by rfl⟩ : syracuseStep 2306069 = 108097) (by norm_num)
theorem B405533 : Blo 239816 405533 := bbase (se 3 (by rfl) ⟨76037, by rfl⟩ : syracuseStep 405533 = 152075) (by norm_num)
theorem B307253 : Blo 239816 307253 := bbase (se 5 (by rfl) ⟨14402, by rfl⟩ : syracuseStep 307253 = 28805) (by norm_num)
theorem B307309 : Blo 239816 307309 := bbase (se 3 (by rfl) ⟨57620, by rfl⟩ : syracuseStep 307309 = 115241) (by norm_num)
theorem B405661 : Blo 239816 405661 := bbase (se 3 (by rfl) ⟨76061, by rfl⟩ : syracuseStep 405661 = 152123) (by norm_num)
theorem B307405 : Blo 239816 307405 := bbase (se 3 (by rfl) ⟨57638, by rfl⟩ : syracuseStep 307405 = 115277) (by norm_num)
theorem B438485 : Blo 239816 438485 := bbase (se 7 (by rfl) ⟨5138, by rfl⟩ : syracuseStep 438485 = 10277) (by norm_num)
theorem B405749 : Blo 239816 405749 := bbase (se 5 (by rfl) ⟨19019, by rfl⟩ : syracuseStep 405749 = 38039) (by norm_num)
theorem B405877 : Blo 239816 405877 := bbase (se 5 (by rfl) ⟨19025, by rfl⟩ : syracuseStep 405877 = 38051) (by norm_num)
theorem B307577 : Blo 239816 307577 := bbase (se 2 (by rfl) ⟨115341, by rfl⟩ : syracuseStep 307577 = 230683) (by norm_num)
theorem B1159589 : Blo 239816 1159589 := bbase (se 4 (by rfl) ⟨108711, by rfl⟩ : syracuseStep 1159589 = 217423) (by norm_num)
theorem B307633 : Blo 239816 307633 := bbase (se 2 (by rfl) ⟨115362, by rfl⟩ : syracuseStep 307633 = 230725) (by norm_num)
theorem B405965 : Blo 239816 405965 := bbase (se 3 (by rfl) ⟨76118, by rfl⟩ : syracuseStep 405965 = 152237) (by norm_num)
theorem B274925 : Blo 239816 274925 := bbase (se 3 (by rfl) ⟨51548, by rfl⟩ : syracuseStep 274925 = 103097) (by norm_num)
theorem B1225205 : Blo 239816 1225205 := bbase (se 5 (by rfl) ⟨57431, by rfl⟩ : syracuseStep 1225205 = 114863) (by norm_num)
theorem B307729 : Blo 239816 307729 := bbase (se 2 (by rfl) ⟨115398, by rfl⟩ : syracuseStep 307729 = 230797) (by norm_num)
theorem B406093 : Blo 239816 406093 := bbase (se 3 (by rfl) ⟨76142, by rfl⟩ : syracuseStep 406093 = 152285) (by norm_num)
theorem B406181 : Blo 239816 406181 := bbase (se 4 (by rfl) ⟨38079, by rfl⟩ : syracuseStep 406181 = 76159) (by norm_num)
theorem B307901 : Blo 239816 307901 := bbase (se 3 (by rfl) ⟨57731, by rfl⟩ : syracuseStep 307901 = 115463) (by norm_num)
theorem B701173 : Blo 239816 701173 := bbase (se 5 (by rfl) ⟨32867, by rfl⟩ : syracuseStep 701173 = 65735) (by norm_num)
theorem B307957 : Blo 239816 307957 := bbase (se 5 (by rfl) ⟨14435, by rfl⟩ : syracuseStep 307957 = 28871) (by norm_num)
theorem B406309 : Blo 239816 406309 := bbase (se 4 (by rfl) ⟨38091, by rfl⟩ : syracuseStep 406309 = 76183) (by norm_num)
theorem B308053 : Blo 239816 308053 := bbase (se 9 (by rfl) ⟨902, by rfl⟩ : syracuseStep 308053 = 1805) (by norm_num)
theorem B406397 : Blo 239816 406397 := bbase (se 3 (by rfl) ⟨76199, by rfl⟩ : syracuseStep 406397 = 152399) (by norm_num)
theorem B439229 : Blo 239816 439229 := bbase (se 3 (by rfl) ⟨82355, by rfl⟩ : syracuseStep 439229 = 164711) (by norm_num)
theorem B406525 : Blo 239816 406525 := bbase (se 3 (by rfl) ⟨76223, by rfl⟩ : syracuseStep 406525 = 152447) (by norm_num)
theorem B308225 : Blo 239816 308225 := bbase (se 2 (by rfl) ⟨115584, by rfl⟩ : syracuseStep 308225 = 231169) (by norm_num)
theorem B275509 : Blo 239816 275509 := bbase (se 5 (by rfl) ⟨12914, by rfl⟩ : syracuseStep 275509 = 25829) (by norm_num)
theorem B308281 : Blo 239816 308281 := bbase (se 2 (by rfl) ⟨115605, by rfl⟩ : syracuseStep 308281 = 231211) (by norm_num)
theorem B406613 : Blo 239816 406613 := bbase (se 8 (by rfl) ⟨2382, by rfl⟩ : syracuseStep 406613 = 4765) (by norm_num)
theorem B308377 : Blo 239816 308377 := bbase (se 2 (by rfl) ⟨115641, by rfl⟩ : syracuseStep 308377 = 231283) (by norm_num)
theorem B406741 : Blo 239816 406741 := bbase (se 7 (by rfl) ⟨4766, by rfl⟩ : syracuseStep 406741 = 9533) (by norm_num)
theorem B308521 : Blo 239816 308521 := bbase (se 2 (by rfl) ⟨115695, by rfl⟩ : syracuseStep 308521 = 231391) (by norm_num)
theorem B406829 : Blo 239816 406829 := bbase (se 3 (by rfl) ⟨76280, by rfl⟩ : syracuseStep 406829 = 152561) (by norm_num)
theorem B308549 : Blo 239816 308549 := bbase (se 4 (by rfl) ⟨28926, by rfl⟩ : syracuseStep 308549 = 57853) (by norm_num)
theorem B1095029 : Blo 239816 1095029 := bbase (se 5 (by rfl) ⟨51329, by rfl⟩ : syracuseStep 1095029 = 102659) (by norm_num)
theorem B308605 : Blo 239816 308605 := bbase (se 3 (by rfl) ⟨57863, by rfl⟩ : syracuseStep 308605 = 115727) (by norm_num)
theorem B406957 : Blo 239816 406957 := bbase (se 3 (by rfl) ⟨76304, by rfl⟩ : syracuseStep 406957 = 152609) (by norm_num)
theorem B243145 : Blo 239816 243145 := bbase (se 2 (by rfl) ⟨91179, by rfl⟩ : syracuseStep 243145 = 182359) (by norm_num)
theorem B407045 : Blo 239816 407045 := bbase (se 4 (by rfl) ⟨38160, by rfl⟩ : syracuseStep 407045 = 76321) (by norm_num)
theorem B341605 : Blo 239816 341605 := bbase (se 4 (by rfl) ⟨32025, by rfl⟩ : syracuseStep 341605 = 64051) (by norm_num)
theorem B407173 : Blo 239816 407173 := bbase (se 4 (by rfl) ⟨38172, by rfl⟩ : syracuseStep 407173 = 76345) (by norm_num)
theorem B1160837 : Blo 239816 1160837 := bbase (se 4 (by rfl) ⟨108828, by rfl⟩ : syracuseStep 1160837 = 217657) (by norm_num)
theorem B308917 : Blo 239816 308917 := bbase (se 5 (by rfl) ⟨14480, by rfl⟩ : syracuseStep 308917 = 28961) (by norm_num)
theorem B407261 : Blo 239816 407261 := bbase (se 3 (by rfl) ⟨76361, by rfl⟩ : syracuseStep 407261 = 152723) (by norm_num)
theorem B276221 : Blo 239816 276221 := bbase (se 3 (by rfl) ⟨51791, by rfl⟩ : syracuseStep 276221 = 103583) (by norm_num)
theorem B1226501 : Blo 239816 1226501 := bbase (se 4 (by rfl) ⟨114984, by rfl⟩ : syracuseStep 1226501 = 229969) (by norm_num)
theorem B1029941 : Blo 239816 1029941 := bbase (se 5 (by rfl) ⟨48278, by rfl⟩ : syracuseStep 1029941 = 96557) (by norm_num)
theorem B407389 : Blo 239816 407389 := bbase (se 3 (by rfl) ⟨76385, by rfl⟩ : syracuseStep 407389 = 152771) (by norm_num)
theorem B276385 : Blo 239816 276385 := bbase (se 2 (by rfl) ⟨103644, by rfl⟩ : syracuseStep 276385 = 207289) (by norm_num)
theorem B407477 : Blo 239816 407477 := bbase (se 5 (by rfl) ⟨19100, by rfl⟩ : syracuseStep 407477 = 38201) (by norm_num)
theorem B243697 : Blo 239816 243697 := bbase (se 2 (by rfl) ⟨91386, by rfl⟩ : syracuseStep 243697 = 182773) (by norm_num)
theorem B407605 : Blo 239816 407605 := bbase (se 5 (by rfl) ⟨19106, by rfl⟩ : syracuseStep 407605 = 38213) (by norm_num)
theorem B407693 : Blo 239816 407693 := bbase (se 3 (by rfl) ⟨76442, by rfl⟩ : syracuseStep 407693 = 152885) (by norm_num)
theorem B407821 : Blo 239816 407821 := bbase (se 3 (by rfl) ⟨76466, by rfl⟩ : syracuseStep 407821 = 152933) (by norm_num)
theorem B833813 : Blo 239816 833813 := bbase (se 6 (by rfl) ⟨19542, by rfl⟩ : syracuseStep 833813 = 39085) (by norm_num)
theorem B1096037 : Blo 239816 1096037 := bbase (se 4 (by rfl) ⟨102753, by rfl⟩ : syracuseStep 1096037 = 205507) (by norm_num)
theorem B407909 : Blo 239816 407909 := bbase (se 4 (by rfl) ⟨38241, by rfl⟩ : syracuseStep 407909 = 76483) (by norm_num)
theorem B342397 : Blo 239816 342397 := bbase (se 3 (by rfl) ⟨64199, by rfl⟩ : syracuseStep 342397 = 128399) (by norm_num)
theorem B309701 : Blo 239816 309701 := bbase (se 4 (by rfl) ⟨29034, by rfl⟩ : syracuseStep 309701 = 58069) (by norm_num)
theorem B408037 : Blo 239816 408037 := bbase (se 4 (by rfl) ⟨38253, by rfl⟩ : syracuseStep 408037 = 76507) (by norm_num)
theorem B408125 : Blo 239816 408125 := bbase (se 3 (by rfl) ⟨76523, by rfl⟩ : syracuseStep 408125 = 153047) (by norm_num)
theorem B408253 : Blo 239816 408253 := bbase (se 3 (by rfl) ⟨76547, by rfl⟩ : syracuseStep 408253 = 153095) (by norm_num)
theorem B342733 : Blo 239816 342733 := bbase (se 3 (by rfl) ⟨64262, by rfl⟩ : syracuseStep 342733 = 128525) (by norm_num)
theorem B408341 : Blo 239816 408341 := bbase (se 6 (by rfl) ⟨9570, by rfl⟩ : syracuseStep 408341 = 19141) (by norm_num)
theorem B637733 : Blo 239816 637733 := bbase (se 4 (by rfl) ⟨59787, by rfl⟩ : syracuseStep 637733 = 119575) (by norm_num)
theorem B408469 : Blo 239816 408469 := bbase (se 6 (by rfl) ⟨9573, by rfl⟩ : syracuseStep 408469 = 19147) (by norm_num)
theorem B342949 : Blo 239816 342949 := bbase (se 4 (by rfl) ⟨32151, by rfl⟩ : syracuseStep 342949 = 64303) (by norm_num)
theorem B277453 : Blo 239816 277453 := bbase (se 3 (by rfl) ⟨52022, by rfl⟩ : syracuseStep 277453 = 104045) (by norm_num)
theorem B2079701 : Blo 239816 2079701 := bbase (se 7 (by rfl) ⟨24371, by rfl⟩ : syracuseStep 2079701 = 48743) (by norm_num)
theorem B539621 : Blo 239816 539621 := bbase (se 4 (by rfl) ⟨50589, by rfl⟩ : syracuseStep 539621 = 101179) (by norm_num)
theorem B408557 : Blo 239816 408557 := bbase (se 3 (by rfl) ⟨76604, by rfl⟩ : syracuseStep 408557 = 153209) (by norm_num)
theorem B1260533 : Blo 239816 1260533 := bbase (se 5 (by rfl) ⟨59087, by rfl⟩ : syracuseStep 1260533 = 118175) (by norm_num)
theorem B703477 : Blo 239816 703477 := bbase (se 5 (by rfl) ⟨32975, by rfl⟩ : syracuseStep 703477 = 65951) (by norm_num)
theorem B310277 : Blo 239816 310277 := bbase (se 4 (by rfl) ⟨29088, by rfl⟩ : syracuseStep 310277 = 58177) (by norm_num)
theorem B1227797 : Blo 239816 1227797 := bbase (se 6 (by rfl) ⟨28776, by rfl⟩ : syracuseStep 1227797 = 57553) (by norm_num)
theorem B539693 : Blo 239816 539693 := bbase (se 3 (by rfl) ⟨101192, by rfl⟩ : syracuseStep 539693 = 202385) (by norm_num)
theorem B277553 : Blo 239816 277553 := bbase (se 2 (by rfl) ⟨104082, by rfl⟩ : syracuseStep 277553 = 208165) (by norm_num)
theorem B408685 : Blo 239816 408685 := bbase (se 3 (by rfl) ⟨76628, by rfl⟩ : syracuseStep 408685 = 153257) (by norm_num)
theorem B539765 : Blo 239816 539765 := bbase (se 5 (by rfl) ⟨25301, by rfl⟩ : syracuseStep 539765 = 50603) (by norm_num)
theorem B277625 : Blo 239816 277625 := bbase (se 2 (by rfl) ⟨104109, by rfl⟩ : syracuseStep 277625 = 208219) (by norm_num)
theorem B244873 : Blo 239816 244873 := bbase (se 2 (by rfl) ⟨91827, by rfl⟩ : syracuseStep 244873 = 183655) (by norm_num)
theorem B539837 : Blo 239816 539837 := bbase (se 3 (by rfl) ⟨101219, by rfl⟩ : syracuseStep 539837 = 202439) (by norm_num)
theorem B408773 : Blo 239816 408773 := bbase (se 4 (by rfl) ⟨38322, by rfl⟩ : syracuseStep 408773 = 76645) (by norm_num)
theorem B539909 : Blo 239816 539909 := bbase (se 4 (by rfl) ⟨50616, by rfl⟩ : syracuseStep 539909 = 101233) (by norm_num)
theorem B343325 : Blo 239816 343325 := bbase (se 3 (by rfl) ⟨64373, by rfl⟩ : syracuseStep 343325 = 128747) (by norm_num)
theorem B408901 : Blo 239816 408901 := bbase (se 4 (by rfl) ⟨38334, by rfl⟩ : syracuseStep 408901 = 76669) (by norm_num)
theorem B539981 : Blo 239816 539981 := bbase (se 3 (by rfl) ⟨101246, by rfl⟩ : syracuseStep 539981 = 202493) (by norm_num)
theorem B310657 : Blo 239816 310657 := bbase (se 2 (by rfl) ⟨116496, by rfl⟩ : syracuseStep 310657 = 232993) (by norm_num)
theorem B540053 : Blo 239816 540053 := bbase (se 6 (by rfl) ⟨12657, by rfl⟩ : syracuseStep 540053 = 25315) (by norm_num)
theorem B408989 : Blo 239816 408989 := bbase (se 3 (by rfl) ⟨76685, by rfl⟩ : syracuseStep 408989 = 153371) (by norm_num)
theorem B540125 : Blo 239816 540125 := bbase (se 3 (by rfl) ⟨101273, by rfl⟩ : syracuseStep 540125 = 202547) (by norm_num)
theorem B409117 : Blo 239816 409117 := bbase (se 3 (by rfl) ⟨76709, by rfl⟩ : syracuseStep 409117 = 153419) (by norm_num)
theorem B540197 : Blo 239816 540197 := bbase (se 4 (by rfl) ⟨50643, by rfl⟩ : syracuseStep 540197 = 101287) (by norm_num)
theorem B1031717 : Blo 239816 1031717 := bbase (se 4 (by rfl) ⟨96723, by rfl⟩ : syracuseStep 1031717 = 193447) (by norm_num)
theorem B933445 : Blo 239816 933445 := bbase (se 4 (by rfl) ⟨87510, by rfl⟩ : syracuseStep 933445 = 175021) (by norm_num)
theorem B769637 : Blo 239816 769637 := bbase (se 4 (by rfl) ⟨72153, by rfl⟩ : syracuseStep 769637 = 144307) (by norm_num)
theorem B540269 : Blo 239816 540269 := bbase (se 3 (by rfl) ⟨101300, by rfl⟩ : syracuseStep 540269 = 202601) (by norm_num)
theorem B409205 : Blo 239816 409205 := bbase (se 5 (by rfl) ⟨19181, by rfl⟩ : syracuseStep 409205 = 38363) (by norm_num)
theorem B442013 : Blo 239816 442013 := bbase (se 3 (by rfl) ⟨82877, by rfl⟩ : syracuseStep 442013 = 165755) (by norm_num)
theorem B540341 : Blo 239816 540341 := bbase (se 5 (by rfl) ⟨25328, by rfl⟩ : syracuseStep 540341 = 50657) (by norm_num)
theorem B409333 : Blo 239816 409333 := bbase (se 5 (by rfl) ⟨19187, by rfl⟩ : syracuseStep 409333 = 38375) (by norm_num)
theorem B540413 : Blo 239816 540413 := bbase (se 3 (by rfl) ⟨101327, by rfl⟩ : syracuseStep 540413 = 202655) (by norm_num)
theorem B540485 : Blo 239816 540485 := bbase (se 4 (by rfl) ⟨50670, by rfl⟩ : syracuseStep 540485 = 101341) (by norm_num)
theorem B409421 : Blo 239816 409421 := bbase (se 3 (by rfl) ⟨76766, by rfl⟩ : syracuseStep 409421 = 153533) (by norm_num)
theorem B540557 : Blo 239816 540557 := bbase (se 3 (by rfl) ⟨101354, by rfl⟩ : syracuseStep 540557 = 202709) (by norm_num)
theorem B376741 : Blo 239816 376741 := bbase (se 4 (by rfl) ⟨35319, by rfl⟩ : syracuseStep 376741 = 70639) (by norm_num)
theorem B409549 : Blo 239816 409549 := bbase (se 3 (by rfl) ⟨76790, by rfl⟩ : syracuseStep 409549 = 153581) (by norm_num)
theorem B540629 : Blo 239816 540629 := bbase (se 7 (by rfl) ⟨6335, by rfl⟩ : syracuseStep 540629 = 12671) (by norm_num)
theorem B540701 : Blo 239816 540701 := bbase (se 3 (by rfl) ⟨101381, by rfl⟩ : syracuseStep 540701 = 202763) (by norm_num)
theorem B409637 : Blo 239816 409637 := bbase (se 4 (by rfl) ⟨38403, by rfl⟩ : syracuseStep 409637 = 76807) (by norm_num)
theorem B540773 : Blo 239816 540773 := bbase (se 4 (by rfl) ⟨50697, by rfl⟩ : syracuseStep 540773 = 101395) (by norm_num)
theorem B1556597 : Blo 239816 1556597 := bbase (se 5 (by rfl) ⟨72965, by rfl⟩ : syracuseStep 1556597 = 145931) (by norm_num)
theorem B409765 : Blo 239816 409765 := bbase (se 4 (by rfl) ⟨38415, by rfl⟩ : syracuseStep 409765 = 76831) (by norm_num)
theorem B540845 : Blo 239816 540845 := bbase (se 3 (by rfl) ⟨101408, by rfl⟩ : syracuseStep 540845 = 202817) (by norm_num)
theorem B540917 : Blo 239816 540917 := bbase (se 5 (by rfl) ⟨25355, by rfl⟩ : syracuseStep 540917 = 50711) (by norm_num)
theorem B409853 : Blo 239816 409853 := bbase (se 3 (by rfl) ⟨76847, by rfl⟩ : syracuseStep 409853 = 153695) (by norm_num)
theorem B1229093 : Blo 239816 1229093 := bbase (se 4 (by rfl) ⟨115227, by rfl⟩ : syracuseStep 1229093 = 230455) (by norm_num)
theorem B540989 : Blo 239816 540989 := bbase (se 3 (by rfl) ⟨101435, by rfl⟩ : syracuseStep 540989 = 202871) (by norm_num)
theorem B1163605 : Blo 239816 1163605 := bbase (se 10 (by rfl) ⟨1704, by rfl⟩ : syracuseStep 1163605 = 3409) (by norm_num)
theorem B409981 : Blo 239816 409981 := bbase (se 3 (by rfl) ⟨76871, by rfl⟩ : syracuseStep 409981 = 153743) (by norm_num)
theorem B541061 : Blo 239816 541061 := bbase (se 4 (by rfl) ⟨50724, by rfl⟩ : syracuseStep 541061 = 101449) (by norm_num)
theorem B541133 : Blo 239816 541133 := bbase (se 3 (by rfl) ⟨101462, by rfl⟩ : syracuseStep 541133 = 202925) (by norm_num)
theorem B410069 : Blo 239816 410069 := bbase (se 7 (by rfl) ⟨4805, by rfl⟩ : syracuseStep 410069 = 9611) (by norm_num)
theorem B1032709 : Blo 239816 1032709 := bbase (se 4 (by rfl) ⟨96816, by rfl⟩ : syracuseStep 1032709 = 193633) (by norm_num)
theorem B541205 : Blo 239816 541205 := bbase (se 6 (by rfl) ⟨12684, by rfl⟩ : syracuseStep 541205 = 25369) (by norm_num)
theorem B1458773 : Blo 239816 1458773 := bbase (se 8 (by rfl) ⟨8547, by rfl⟩ : syracuseStep 1458773 = 17095) (by norm_num)
theorem B410197 : Blo 239816 410197 := bbase (se 8 (by rfl) ⟨2403, by rfl⟩ : syracuseStep 410197 = 4807) (by norm_num)
theorem B541277 : Blo 239816 541277 := bbase (se 3 (by rfl) ⟨101489, by rfl⟩ : syracuseStep 541277 = 202979) (by norm_num)
theorem B246421 : Blo 239816 246421 := bbase (se 6 (by rfl) ⟨5775, by rfl⟩ : syracuseStep 246421 = 11551) (by norm_num)
theorem B541349 : Blo 239816 541349 := bbase (se 4 (by rfl) ⟨50751, by rfl⟩ : syracuseStep 541349 = 101503) (by norm_num)
theorem B344749 : Blo 239816 344749 := bbase (se 3 (by rfl) ⟨64640, by rfl⟩ : syracuseStep 344749 = 129281) (by norm_num)
theorem B410285 : Blo 239816 410285 := bbase (se 3 (by rfl) ⟨76928, by rfl⟩ : syracuseStep 410285 = 153857) (by norm_num)
theorem B541421 : Blo 239816 541421 := bbase (se 3 (by rfl) ⟨101516, by rfl⟩ : syracuseStep 541421 = 203033) (by norm_num)
theorem B738085 : Blo 239816 738085 := bbase (se 4 (by rfl) ⟨69195, by rfl⟩ : syracuseStep 738085 = 138391) (by norm_num)
theorem B410413 : Blo 239816 410413 := bbase (se 3 (by rfl) ⟨76952, by rfl⟩ : syracuseStep 410413 = 153905) (by norm_num)
theorem B541493 : Blo 239816 541493 := bbase (se 5 (by rfl) ⟨25382, by rfl⟩ : syracuseStep 541493 = 50765) (by norm_num)
theorem B607085 : Blo 239816 607085 := bbase (se 3 (by rfl) ⟨113828, by rfl⟩ : syracuseStep 607085 = 227657) (by norm_num)
theorem B541565 : Blo 239816 541565 := bbase (se 3 (by rfl) ⟨101543, by rfl⟩ : syracuseStep 541565 = 203087) (by norm_num)
theorem B410501 : Blo 239816 410501 := bbase (se 4 (by rfl) ⟨38484, by rfl⟩ : syracuseStep 410501 = 76969) (by norm_num)
theorem B541637 : Blo 239816 541637 := bbase (se 4 (by rfl) ⟨50778, by rfl⟩ : syracuseStep 541637 = 101557) (by norm_num)
theorem B410629 : Blo 239816 410629 := bbase (se 4 (by rfl) ⟨38496, by rfl⟩ : syracuseStep 410629 = 76993) (by norm_num)
theorem B541709 : Blo 239816 541709 := bbase (se 3 (by rfl) ⟨101570, by rfl⟩ : syracuseStep 541709 = 203141) (by norm_num)
theorem B738341 : Blo 239816 738341 := bbase (se 4 (by rfl) ⟨69219, by rfl⟩ : syracuseStep 738341 = 138439) (by norm_num)
theorem B607277 : Blo 239816 607277 := bbase (se 3 (by rfl) ⟨113864, by rfl⟩ : syracuseStep 607277 = 227729) (by norm_num)
theorem B541781 : Blo 239816 541781 := bbase (se 8 (by rfl) ⟨3174, by rfl⟩ : syracuseStep 541781 = 6349) (by norm_num)
theorem B410717 : Blo 239816 410717 := bbase (se 3 (by rfl) ⟨77009, by rfl⟩ : syracuseStep 410717 = 154019) (by norm_num)
theorem B541853 : Blo 239816 541853 := bbase (se 3 (by rfl) ⟨101597, by rfl⟩ : syracuseStep 541853 = 203195) (by norm_num)
theorem B738485 : Blo 239816 738485 := bbase (se 5 (by rfl) ⟨34616, by rfl⟩ : syracuseStep 738485 = 69233) (by norm_num)
theorem B410845 : Blo 239816 410845 := bbase (se 3 (by rfl) ⟨77033, by rfl⟩ : syracuseStep 410845 = 154067) (by norm_num)
theorem B541925 : Blo 239816 541925 := bbase (se 4 (by rfl) ⟨50805, by rfl⟩ : syracuseStep 541925 = 101611) (by norm_num)
theorem B345341 : Blo 239816 345341 := bbase (se 3 (by rfl) ⟨64751, by rfl⟩ : syracuseStep 345341 = 129503) (by norm_num)
theorem B541997 : Blo 239816 541997 := bbase (se 3 (by rfl) ⟨101624, by rfl⟩ : syracuseStep 541997 = 203249) (by norm_num)
theorem B410933 : Blo 239816 410933 := bbase (se 5 (by rfl) ⟨19262, by rfl⟩ : syracuseStep 410933 = 38525) (by norm_num)
theorem B345421 : Blo 239816 345421 := bbase (se 3 (by rfl) ⟨64766, by rfl⟩ : syracuseStep 345421 = 129533) (by norm_num)
theorem B542069 : Blo 239816 542069 := bbase (se 5 (by rfl) ⟨25409, by rfl⟩ : syracuseStep 542069 = 50819) (by norm_num)
theorem B607621 : Blo 239816 607621 := bbase (se 4 (by rfl) ⟨56964, by rfl⟩ : syracuseStep 607621 = 113929) (by norm_num)
theorem B2049461 : Blo 239816 2049461 := bbase (se 5 (by rfl) ⟨96068, by rfl⟩ : syracuseStep 2049461 = 192137) (by norm_num)
theorem B411061 : Blo 239816 411061 := bbase (se 5 (by rfl) ⟨19268, by rfl⟩ : syracuseStep 411061 = 38537) (by norm_num)
theorem B542141 : Blo 239816 542141 := bbase (se 3 (by rfl) ⟨101651, by rfl⟩ : syracuseStep 542141 = 203303) (by norm_num)
theorem B345541 : Blo 239816 345541 := bbase (se 4 (by rfl) ⟨32394, by rfl⟩ : syracuseStep 345541 = 64789) (by norm_num)
theorem B2803157 : Blo 239816 2803157 := bbase (se 7 (by rfl) ⟨32849, by rfl⟩ : syracuseStep 2803157 = 65699) (by norm_num)
theorem B607733 : Blo 239816 607733 := bbase (se 5 (by rfl) ⟨28487, by rfl⟩ : syracuseStep 607733 = 56975) (by norm_num)
theorem B542213 : Blo 239816 542213 := bbase (se 4 (by rfl) ⟨50832, by rfl⟩ : syracuseStep 542213 = 101665) (by norm_num)
theorem B411149 : Blo 239816 411149 := bbase (se 3 (by rfl) ⟨77090, by rfl⟩ : syracuseStep 411149 = 154181) (by norm_num)
theorem B345637 : Blo 239816 345637 := bbase (se 4 (by rfl) ⟨32403, by rfl⟩ : syracuseStep 345637 = 64807) (by norm_num)
theorem B1230389 : Blo 239816 1230389 := bbase (se 5 (by rfl) ⟨57674, by rfl⟩ : syracuseStep 1230389 = 115349) (by norm_num)
theorem B542285 : Blo 239816 542285 := bbase (se 3 (by rfl) ⟨101678, by rfl⟩ : syracuseStep 542285 = 203357) (by norm_num)
theorem B411277 : Blo 239816 411277 := bbase (se 3 (by rfl) ⟨77114, by rfl⟩ : syracuseStep 411277 = 154229) (by norm_num)
theorem B542357 : Blo 239816 542357 := bbase (se 6 (by rfl) ⟨12711, by rfl⟩ : syracuseStep 542357 = 25423) (by norm_num)
theorem B607925 : Blo 239816 607925 := bbase (se 5 (by rfl) ⟨28496, by rfl⟩ : syracuseStep 607925 = 56993) (by norm_num)
theorem B542429 : Blo 239816 542429 := bbase (se 3 (by rfl) ⟨101705, by rfl⟩ : syracuseStep 542429 = 203411) (by norm_num)
theorem B411365 : Blo 239816 411365 := bbase (se 4 (by rfl) ⟨38565, by rfl⟩ : syracuseStep 411365 = 77131) (by norm_num)
theorem B542501 : Blo 239816 542501 := bbase (se 4 (by rfl) ⟨50859, by rfl⟩ : syracuseStep 542501 = 101719) (by norm_num)
theorem B771893 : Blo 239816 771893 := bbase (se 5 (by rfl) ⟨36182, by rfl⟩ : syracuseStep 771893 = 72365) (by norm_num)
theorem B542573 : Blo 239816 542573 := bbase (se 3 (by rfl) ⟨101732, by rfl⟩ : syracuseStep 542573 = 203465) (by norm_num)
theorem B542645 : Blo 239816 542645 := bbase (se 5 (by rfl) ⟨25436, by rfl⟩ : syracuseStep 542645 = 50873) (by norm_num)
theorem B542717 : Blo 239816 542717 := bbase (se 3 (by rfl) ⟨101759, by rfl⟩ : syracuseStep 542717 = 203519) (by norm_num)
theorem B313345 : Blo 239816 313345 := bbase (se 2 (by rfl) ⟨117504, by rfl⟩ : syracuseStep 313345 = 235009) (by norm_num)
theorem B608269 : Blo 239816 608269 := bbase (se 3 (by rfl) ⟨114050, by rfl⟩ : syracuseStep 608269 = 228101) (by norm_num)
theorem B4769813 : Blo 239816 4769813 := bbase (se 6 (by rfl) ⟨111792, by rfl⟩ : syracuseStep 4769813 = 223585) (by norm_num)
theorem B346133 : Blo 239816 346133 := bbase (se 6 (by rfl) ⟨8112, by rfl⟩ : syracuseStep 346133 = 16225) (by norm_num)
theorem B542789 : Blo 239816 542789 := bbase (se 4 (by rfl) ⟨50886, by rfl⟩ : syracuseStep 542789 = 101773) (by norm_num)
theorem B608381 : Blo 239816 608381 := bbase (se 3 (by rfl) ⟨114071, by rfl⟩ : syracuseStep 608381 = 228143) (by norm_num)
theorem B542861 : Blo 239816 542861 := bbase (se 3 (by rfl) ⟨101786, by rfl⟩ : syracuseStep 542861 = 203573) (by norm_num)
theorem B542933 : Blo 239816 542933 := bbase (se 7 (by rfl) ⟨6362, by rfl⟩ : syracuseStep 542933 = 12725) (by norm_num)
theorem B543005 : Blo 239816 543005 := bbase (se 3 (by rfl) ⟨101813, by rfl⟩ : syracuseStep 543005 = 203627) (by norm_num)
theorem B608573 : Blo 239816 608573 := bbase (se 3 (by rfl) ⟨114107, by rfl⟩ : syracuseStep 608573 = 228215) (by norm_num)
theorem B543077 : Blo 239816 543077 := bbase (se 4 (by rfl) ⟨50913, by rfl⟩ : syracuseStep 543077 = 101827) (by norm_num)
theorem B543149 : Blo 239816 543149 := bbase (se 3 (by rfl) ⟨101840, by rfl⟩ : syracuseStep 543149 = 203681) (by norm_num)
theorem B1100213 : Blo 239816 1100213 := bbase (se 5 (by rfl) ⟨51572, by rfl⟩ : syracuseStep 1100213 = 103145) (by norm_num)
theorem B543221 : Blo 239816 543221 := bbase (se 5 (by rfl) ⟨25463, by rfl⟩ : syracuseStep 543221 = 50927) (by norm_num)
theorem B772661 : Blo 239816 772661 := bbase (se 5 (by rfl) ⟨36218, by rfl⟩ : syracuseStep 772661 = 72437) (by norm_num)
theorem B543293 : Blo 239816 543293 := bbase (se 3 (by rfl) ⟨101867, by rfl⟩ : syracuseStep 543293 = 203735) (by norm_num)
theorem B346685 : Blo 239816 346685 := bbase (se 3 (by rfl) ⟨65003, by rfl⟩ : syracuseStep 346685 = 130007) (by norm_num)
theorem B412237 : Blo 239816 412237 := bbase (se 3 (by rfl) ⟨77294, by rfl⟩ : syracuseStep 412237 = 154589) (by norm_num)
theorem B543365 : Blo 239816 543365 := bbase (se 4 (by rfl) ⟨50940, by rfl⟩ : syracuseStep 543365 = 101881) (by norm_num)
theorem B608917 : Blo 239816 608917 := bbase (se 6 (by rfl) ⟨14271, by rfl⟩ : syracuseStep 608917 = 28543) (by norm_num)
theorem B543437 : Blo 239816 543437 := bbase (se 3 (by rfl) ⟨101894, by rfl⟩ : syracuseStep 543437 = 203789) (by norm_num)
theorem B576229 : Blo 239816 576229 := bbase (se 4 (by rfl) ⟨54021, by rfl⟩ : syracuseStep 576229 = 108043) (by norm_num)
theorem B609029 : Blo 239816 609029 := bbase (se 4 (by rfl) ⟨57096, by rfl⟩ : syracuseStep 609029 = 114193) (by norm_num)
theorem B543509 : Blo 239816 543509 := bbase (se 6 (by rfl) ⟨12738, by rfl⟩ : syracuseStep 543509 = 25477) (by norm_num)
theorem B1231685 : Blo 239816 1231685 := bbase (se 4 (by rfl) ⟨115470, by rfl⟩ : syracuseStep 1231685 = 230941) (by norm_num)
theorem B543581 : Blo 239816 543581 := bbase (se 3 (by rfl) ⟨101921, by rfl⟩ : syracuseStep 543581 = 203843) (by norm_num)
theorem B543653 : Blo 239816 543653 := bbase (se 4 (by rfl) ⟨50967, by rfl⟩ : syracuseStep 543653 = 101935) (by norm_num)
theorem B609221 : Blo 239816 609221 := bbase (se 4 (by rfl) ⟨57114, by rfl⟩ : syracuseStep 609221 = 114229) (by norm_num)
theorem B543725 : Blo 239816 543725 := bbase (se 3 (by rfl) ⟨101948, by rfl⟩ : syracuseStep 543725 = 203897) (by norm_num)
theorem B1559573 : Blo 239816 1559573 := bbase (se 6 (by rfl) ⟨36552, by rfl⟩ : syracuseStep 1559573 = 73105) (by norm_num)
theorem B773173 : Blo 239816 773173 := bbase (se 5 (by rfl) ⟨36242, by rfl⟩ : syracuseStep 773173 = 72485) (by norm_num)
theorem B543797 : Blo 239816 543797 := bbase (se 5 (by rfl) ⟨25490, by rfl⟩ : syracuseStep 543797 = 50981) (by norm_num)
theorem B543869 : Blo 239816 543869 := bbase (se 3 (by rfl) ⟨101975, by rfl⟩ : syracuseStep 543869 = 203951) (by norm_num)
theorem B543941 : Blo 239816 543941 := bbase (se 4 (by rfl) ⟨50994, by rfl⟩ : syracuseStep 543941 = 101989) (by norm_num)
theorem B544013 : Blo 239816 544013 := bbase (se 3 (by rfl) ⟨102002, by rfl⟩ : syracuseStep 544013 = 204005) (by norm_num)
theorem B642325 : Blo 239816 642325 := bbase (se 6 (by rfl) ⟨15054, by rfl⟩ : syracuseStep 642325 = 30109) (by norm_num)
theorem B609565 : Blo 239816 609565 := bbase (se 3 (by rfl) ⟨114293, by rfl⟩ : syracuseStep 609565 = 228587) (by norm_num)
theorem B576845 : Blo 239816 576845 := bbase (se 3 (by rfl) ⟨108158, by rfl⟩ : syracuseStep 576845 = 216317) (by norm_num)
theorem B544085 : Blo 239816 544085 := bbase (se 11 (by rfl) ⟨398, by rfl⟩ : syracuseStep 544085 = 797) (by norm_num)
theorem B609677 : Blo 239816 609677 := bbase (se 3 (by rfl) ⟨114314, by rfl⟩ : syracuseStep 609677 = 228629) (by norm_num)
theorem B544157 : Blo 239816 544157 := bbase (se 3 (by rfl) ⟨102029, by rfl⟩ : syracuseStep 544157 = 204059) (by norm_num)
theorem B544229 : Blo 239816 544229 := bbase (se 4 (by rfl) ⟨51021, by rfl⟩ : syracuseStep 544229 = 102043) (by norm_num)
theorem B544301 : Blo 239816 544301 := bbase (se 3 (by rfl) ⟨102056, by rfl⟩ : syracuseStep 544301 = 204113) (by norm_num)
theorem B609869 : Blo 239816 609869 := bbase (se 3 (by rfl) ⟨114350, by rfl⟩ : syracuseStep 609869 = 228701) (by norm_num)
theorem B544373 : Blo 239816 544373 := bbase (se 5 (by rfl) ⟨25517, by rfl⟩ : syracuseStep 544373 = 51035) (by norm_num)
theorem B577181 : Blo 239816 577181 := bbase (se 3 (by rfl) ⟨108221, by rfl⟩ : syracuseStep 577181 = 216443) (by norm_num)
theorem B544445 : Blo 239816 544445 := bbase (se 3 (by rfl) ⟨102083, by rfl⟩ : syracuseStep 544445 = 204167) (by norm_num)
theorem B544517 : Blo 239816 544517 := bbase (se 4 (by rfl) ⟨51048, by rfl⟩ : syracuseStep 544517 = 102097) (by norm_num)
theorem B544589 : Blo 239816 544589 := bbase (se 3 (by rfl) ⟨102110, by rfl⟩ : syracuseStep 544589 = 204221) (by norm_num)
theorem B544661 : Blo 239816 544661 := bbase (se 6 (by rfl) ⟨12765, by rfl⟩ : syracuseStep 544661 = 25531) (by norm_num)
theorem B610213 : Blo 239816 610213 := bbase (se 4 (by rfl) ⟨57207, by rfl⟩ : syracuseStep 610213 = 114415) (by norm_num)
theorem B544733 : Blo 239816 544733 := bbase (se 3 (by rfl) ⟨102137, by rfl⟩ : syracuseStep 544733 = 204275) (by norm_num)
theorem B610325 : Blo 239816 610325 := bbase (se 6 (by rfl) ⟨14304, by rfl⟩ : syracuseStep 610325 = 28609) (by norm_num)
theorem B577573 : Blo 239816 577573 := bbase (se 4 (by rfl) ⟨54147, by rfl⟩ : syracuseStep 577573 = 108295) (by norm_num)
theorem B544805 : Blo 239816 544805 := bbase (se 4 (by rfl) ⟨51075, by rfl⟩ : syracuseStep 544805 = 102151) (by norm_num)
theorem B1232981 : Blo 239816 1232981 := bbase (se 8 (by rfl) ⟨7224, by rfl⟩ : syracuseStep 1232981 = 14449) (by norm_num)
theorem B544877 : Blo 239816 544877 := bbase (se 3 (by rfl) ⟨102164, by rfl⟩ : syracuseStep 544877 = 204329) (by norm_num)
theorem B544949 : Blo 239816 544949 := bbase (se 5 (by rfl) ⟨25544, by rfl⟩ : syracuseStep 544949 = 51089) (by norm_num)
theorem B610517 : Blo 239816 610517 := bbase (se 7 (by rfl) ⟨7154, by rfl⟩ : syracuseStep 610517 = 14309) (by norm_num)
theorem B512237 : Blo 239816 512237 := bbase (se 3 (by rfl) ⟨96044, by rfl⟩ : syracuseStep 512237 = 192089) (by norm_num)
theorem B545021 : Blo 239816 545021 := bbase (se 3 (by rfl) ⟨102191, by rfl⟩ : syracuseStep 545021 = 204383) (by norm_num)
theorem B545093 : Blo 239816 545093 := bbase (se 4 (by rfl) ⟨51102, by rfl⟩ : syracuseStep 545093 = 102205) (by norm_num)
theorem B414085 : Blo 239816 414085 := bbase (se 4 (by rfl) ⟨38820, by rfl⟩ : syracuseStep 414085 = 77641) (by norm_num)
theorem B545165 : Blo 239816 545165 := bbase (se 3 (by rfl) ⟨102218, by rfl⟩ : syracuseStep 545165 = 204437) (by norm_num)
theorem B1167797 : Blo 239816 1167797 := bbase (se 5 (by rfl) ⟨54740, by rfl⟩ : syracuseStep 1167797 = 109481) (by norm_num)
theorem B545237 : Blo 239816 545237 := bbase (se 7 (by rfl) ⟨6389, by rfl⟩ : syracuseStep 545237 = 12779) (by norm_num)
theorem B1102325 : Blo 239816 1102325 := bbase (se 5 (by rfl) ⟨51671, by rfl⟩ : syracuseStep 1102325 = 103343) (by norm_num)
theorem B545309 : Blo 239816 545309 := bbase (se 3 (by rfl) ⟨102245, by rfl⟩ : syracuseStep 545309 = 204491) (by norm_num)
theorem B610861 : Blo 239816 610861 := bbase (se 3 (by rfl) ⟨114536, by rfl⟩ : syracuseStep 610861 = 229073) (by norm_num)
theorem B971365 : Blo 239816 971365 := bbase (se 4 (by rfl) ⟨91065, by rfl⟩ : syracuseStep 971365 = 182131) (by norm_num)
theorem B545381 : Blo 239816 545381 := bbase (se 4 (by rfl) ⟨51129, by rfl⟩ : syracuseStep 545381 = 102259) (by norm_num)
theorem B610973 : Blo 239816 610973 := bbase (se 3 (by rfl) ⟨114557, by rfl⟩ : syracuseStep 610973 = 229115) (by norm_num)
theorem B545453 : Blo 239816 545453 := bbase (se 3 (by rfl) ⟨102272, by rfl⟩ : syracuseStep 545453 = 204545) (by norm_num)
theorem B545525 : Blo 239816 545525 := bbase (se 5 (by rfl) ⟨25571, by rfl⟩ : syracuseStep 545525 = 51143) (by norm_num)
theorem B774917 : Blo 239816 774917 := bbase (se 4 (by rfl) ⟨72648, by rfl⟩ : syracuseStep 774917 = 145297) (by norm_num)
theorem B938789 : Blo 239816 938789 := bbase (se 4 (by rfl) ⟨88011, by rfl⟩ : syracuseStep 938789 = 176023) (by norm_num)
theorem B545597 : Blo 239816 545597 := bbase (se 3 (by rfl) ⟨102299, by rfl⟩ : syracuseStep 545597 = 204599) (by norm_num)
theorem B611165 : Blo 239816 611165 := bbase (se 3 (by rfl) ⟨114593, by rfl⟩ : syracuseStep 611165 = 229187) (by norm_num)
theorem B545669 : Blo 239816 545669 := bbase (se 4 (by rfl) ⟨51156, by rfl⟩ : syracuseStep 545669 = 102313) (by norm_num)
theorem B4445077 : Blo 239816 4445077 := bbase (se 6 (by rfl) ⟨104181, by rfl⟩ : syracuseStep 4445077 = 208363) (by norm_num)
theorem B775109 : Blo 239816 775109 := bbase (se 4 (by rfl) ⟨72666, by rfl⟩ : syracuseStep 775109 = 145333) (by norm_num)
theorem B545741 : Blo 239816 545741 := bbase (se 3 (by rfl) ⟨102326, by rfl⟩ : syracuseStep 545741 = 204653) (by norm_num)
theorem B545813 : Blo 239816 545813 := bbase (se 6 (by rfl) ⟨12792, by rfl⟩ : syracuseStep 545813 = 25585) (by norm_num)
theorem B545885 : Blo 239816 545885 := bbase (se 3 (by rfl) ⟨102353, by rfl⟩ : syracuseStep 545885 = 204707) (by norm_num)
theorem B545957 : Blo 239816 545957 := bbase (se 4 (by rfl) ⟨51183, by rfl⟩ : syracuseStep 545957 = 102367) (by norm_num)
theorem B611509 : Blo 239816 611509 := bbase (se 5 (by rfl) ⟨28664, by rfl⟩ : syracuseStep 611509 = 57329) (by norm_num)
theorem B1823957 : Blo 239816 1823957 := bbase (se 7 (by rfl) ⟨21374, by rfl⟩ : syracuseStep 1823957 = 42749) (by norm_num)
theorem B546029 : Blo 239816 546029 := bbase (se 3 (by rfl) ⟨102380, by rfl⟩ : syracuseStep 546029 = 204761) (by norm_num)
theorem B611621 : Blo 239816 611621 := bbase (se 4 (by rfl) ⟨57339, by rfl⟩ : syracuseStep 611621 = 114679) (by norm_num)
theorem B546101 : Blo 239816 546101 := bbase (se 5 (by rfl) ⟨25598, by rfl⟩ : syracuseStep 546101 = 51197) (by norm_num)
theorem B1234277 : Blo 239816 1234277 := bbase (se 4 (by rfl) ⟨115713, by rfl⟩ : syracuseStep 1234277 = 231427) (by norm_num)
theorem B546173 : Blo 239816 546173 := bbase (se 3 (by rfl) ⟨102407, by rfl⟩ : syracuseStep 546173 = 204815) (by norm_num)
theorem B1037717 : Blo 239816 1037717 := bbase (se 6 (by rfl) ⟨24321, by rfl⟩ : syracuseStep 1037717 = 48643) (by norm_num)
theorem B546245 : Blo 239816 546245 := bbase (se 4 (by rfl) ⟨51210, by rfl⟩ : syracuseStep 546245 = 102421) (by norm_num)
theorem B611813 : Blo 239816 611813 := bbase (se 4 (by rfl) ⟨57357, by rfl⟩ : syracuseStep 611813 = 114715) (by norm_num)
theorem B546317 : Blo 239816 546317 := bbase (se 3 (by rfl) ⟨102434, by rfl⟩ : syracuseStep 546317 = 204869) (by norm_num)
theorem B546389 : Blo 239816 546389 := bbase (se 8 (by rfl) ⟨3201, by rfl⟩ : syracuseStep 546389 = 6403) (by norm_num)
theorem B546461 : Blo 239816 546461 := bbase (se 3 (by rfl) ⟨102461, by rfl⟩ : syracuseStep 546461 = 204923) (by norm_num)
theorem B1038005 : Blo 239816 1038005 := bbase (se 5 (by rfl) ⟨48656, by rfl⟩ : syracuseStep 1038005 = 97313) (by norm_num)
theorem B546533 : Blo 239816 546533 := bbase (se 4 (by rfl) ⟨51237, by rfl⟩ : syracuseStep 546533 = 102475) (by norm_num)
theorem B546605 : Blo 239816 546605 := bbase (se 3 (by rfl) ⟨102488, by rfl⟩ : syracuseStep 546605 = 204977) (by norm_num)
theorem B612157 : Blo 239816 612157 := bbase (se 3 (by rfl) ⟨114779, by rfl⟩ : syracuseStep 612157 = 229559) (by norm_num)
theorem B513877 : Blo 239816 513877 := bbase (se 9 (by rfl) ⟨1505, by rfl⟩ : syracuseStep 513877 = 3011) (by norm_num)
theorem B382837 : Blo 239816 382837 := bbase (se 5 (by rfl) ⟨17945, by rfl⟩ : syracuseStep 382837 = 35891) (by norm_num)
theorem B546677 : Blo 239816 546677 := bbase (se 5 (by rfl) ⟨25625, by rfl⟩ : syracuseStep 546677 = 51251) (by norm_num)
theorem B612269 : Blo 239816 612269 := bbase (se 3 (by rfl) ⟨114800, by rfl⟩ : syracuseStep 612269 = 229601) (by norm_num)
theorem B546749 : Blo 239816 546749 := bbase (se 3 (by rfl) ⟨102515, by rfl⟩ : syracuseStep 546749 = 205031) (by norm_num)
theorem B546821 : Blo 239816 546821 := bbase (se 4 (by rfl) ⟨51264, by rfl⟩ : syracuseStep 546821 = 102529) (by norm_num)
theorem B546893 : Blo 239816 546893 := bbase (se 3 (by rfl) ⟨102542, by rfl⟩ : syracuseStep 546893 = 205085) (by norm_num)
theorem B612461 : Blo 239816 612461 := bbase (se 3 (by rfl) ⟨114836, by rfl⟩ : syracuseStep 612461 = 229673) (by norm_num)
theorem B546965 : Blo 239816 546965 := bbase (se 6 (by rfl) ⟨12819, by rfl⟩ : syracuseStep 546965 = 25639) (by norm_num)
theorem B547037 : Blo 239816 547037 := bbase (se 3 (by rfl) ⟨102569, by rfl⟩ : syracuseStep 547037 = 205139) (by norm_num)
theorem B547069 : Blo 239816 547069 := bbase (se 3 (by rfl) ⟨102575, by rfl⟩ : syracuseStep 547069 = 205151) (by norm_num)
theorem B547109 : Blo 239816 547109 := bbase (se 4 (by rfl) ⟨51291, by rfl⟩ : syracuseStep 547109 = 102583) (by norm_num)
theorem B547181 : Blo 239816 547181 := bbase (se 3 (by rfl) ⟨102596, by rfl⟩ : syracuseStep 547181 = 205193) (by norm_num)
theorem B1038757 : Blo 239816 1038757 := bbase (se 4 (by rfl) ⟨97383, by rfl⟩ : syracuseStep 1038757 = 194767) (by norm_num)
theorem B547253 : Blo 239816 547253 := bbase (se 5 (by rfl) ⟨25652, by rfl⟩ : syracuseStep 547253 = 51305) (by norm_num)
theorem B612805 : Blo 239816 612805 := bbase (se 4 (by rfl) ⟨57450, by rfl⟩ : syracuseStep 612805 = 114901) (by norm_num)
theorem B547325 : Blo 239816 547325 := bbase (se 3 (by rfl) ⟨102623, by rfl⟩ : syracuseStep 547325 = 205247) (by norm_num)
theorem B612917 : Blo 239816 612917 := bbase (se 5 (by rfl) ⟨28730, by rfl⟩ : syracuseStep 612917 = 57461) (by norm_num)
theorem B547397 : Blo 239816 547397 := bbase (se 4 (by rfl) ⟨51318, by rfl⟩ : syracuseStep 547397 = 102637) (by norm_num)
theorem B5331541 : Blo 239816 5331541 := bbase (se 8 (by rfl) ⟨31239, by rfl⟩ : syracuseStep 5331541 = 62479) (by norm_num)
theorem B875125 : Blo 239816 875125 := bbase (se 5 (by rfl) ⟨41021, by rfl⟩ : syracuseStep 875125 = 82043) (by norm_num)
theorem B547469 : Blo 239816 547469 := bbase (se 3 (by rfl) ⟨102650, by rfl⟩ : syracuseStep 547469 = 205301) (by norm_num)
theorem B809621 : Blo 239816 809621 := bbase (se 6 (by rfl) ⟨18975, by rfl⟩ : syracuseStep 809621 = 37951) (by norm_num)
theorem B514765 : Blo 239816 514765 := bbase (se 3 (by rfl) ⟨96518, by rfl⟩ : syracuseStep 514765 = 193037) (by norm_num)
theorem B547541 : Blo 239816 547541 := bbase (se 7 (by rfl) ⟨6416, by rfl⟩ : syracuseStep 547541 = 12833) (by norm_num)
theorem B613109 : Blo 239816 613109 := bbase (se 5 (by rfl) ⟨28739, by rfl⟩ : syracuseStep 613109 = 57479) (by norm_num)
theorem B547613 : Blo 239816 547613 := bbase (se 3 (by rfl) ⟨102677, by rfl⟩ : syracuseStep 547613 = 205355) (by norm_num)
theorem B547685 : Blo 239816 547685 := bbase (se 4 (by rfl) ⟨51345, by rfl⟩ : syracuseStep 547685 = 102691) (by norm_num)
theorem B547757 : Blo 239816 547757 := bbase (se 3 (by rfl) ⟨102704, by rfl⟩ : syracuseStep 547757 = 205409) (by norm_num)
theorem B547829 : Blo 239816 547829 := bbase (se 5 (by rfl) ⟨25679, by rfl⟩ : syracuseStep 547829 = 51359) (by norm_num)
theorem B547901 : Blo 239816 547901 := bbase (se 3 (by rfl) ⟨102731, by rfl⟩ : syracuseStep 547901 = 205463) (by norm_num)
theorem B810053 : Blo 239816 810053 := bbase (se 4 (by rfl) ⟨75942, by rfl⟩ : syracuseStep 810053 = 151885) (by norm_num)
theorem B613453 : Blo 239816 613453 := bbase (se 3 (by rfl) ⟨115022, by rfl⟩ : syracuseStep 613453 = 230045) (by norm_num)
theorem B580717 : Blo 239816 580717 := bbase (se 3 (by rfl) ⟨108884, by rfl⟩ : syracuseStep 580717 = 217769) (by norm_num)
theorem B1039493 : Blo 239816 1039493 := bbase (se 4 (by rfl) ⟨97452, by rfl⟩ : syracuseStep 1039493 = 194905) (by norm_num)
theorem B547973 : Blo 239816 547973 := bbase (se 4 (by rfl) ⟨51372, by rfl⟩ : syracuseStep 547973 = 102745) (by norm_num)
theorem B580765 : Blo 239816 580765 := bbase (se 3 (by rfl) ⟨108893, by rfl⟩ : syracuseStep 580765 = 217787) (by norm_num)
theorem B515261 : Blo 239816 515261 := bbase (se 3 (by rfl) ⟨96611, by rfl⟩ : syracuseStep 515261 = 193223) (by norm_num)
theorem B613565 : Blo 239816 613565 := bbase (se 3 (by rfl) ⟨115043, by rfl⟩ : syracuseStep 613565 = 230087) (by norm_num)
theorem B548045 : Blo 239816 548045 := bbase (se 3 (by rfl) ⟨102758, by rfl⟩ : syracuseStep 548045 = 205517) (by norm_num)
theorem B548117 : Blo 239816 548117 := bbase (se 6 (by rfl) ⟨12846, by rfl⟩ : syracuseStep 548117 = 25693) (by norm_num)
theorem B548189 : Blo 239816 548189 := bbase (se 3 (by rfl) ⟨102785, by rfl⟩ : syracuseStep 548189 = 205571) (by norm_num)
theorem B613757 : Blo 239816 613757 := bbase (se 3 (by rfl) ⟨115079, by rfl⟩ : syracuseStep 613757 = 230159) (by norm_num)
theorem B548237 : Blo 239816 548237 := bbase (se 3 (by rfl) ⟨102794, by rfl⟩ : syracuseStep 548237 = 205589) (by norm_num)
theorem B548261 : Blo 239816 548261 := bbase (se 4 (by rfl) ⟨51399, by rfl⟩ : syracuseStep 548261 = 102799) (by norm_num)
theorem B548309 : Blo 239816 548309 := bbase (se 7 (by rfl) ⟨6425, by rfl⟩ : syracuseStep 548309 = 12851) (by norm_num)
theorem B384485 : Blo 239816 384485 := bbase (se 4 (by rfl) ⟨36045, by rfl⟩ : syracuseStep 384485 = 72091) (by norm_num)
theorem B548333 : Blo 239816 548333 := bbase (se 3 (by rfl) ⟨102812, by rfl⟩ : syracuseStep 548333 = 205625) (by norm_num)
theorem B810485 : Blo 239816 810485 := bbase (se 5 (by rfl) ⟨37991, by rfl⟩ : syracuseStep 810485 = 75983) (by norm_num)
theorem B548405 : Blo 239816 548405 := bbase (se 5 (by rfl) ⟨25706, by rfl⟩ : syracuseStep 548405 = 51413) (by norm_num)
theorem B548477 : Blo 239816 548477 := bbase (se 3 (by rfl) ⟨102839, by rfl⟩ : syracuseStep 548477 = 205679) (by norm_num)
theorem B548549 : Blo 239816 548549 := bbase (se 4 (by rfl) ⟨51426, by rfl⟩ : syracuseStep 548549 = 102853) (by norm_num)
theorem B1367765 : Blo 239816 1367765 := bbase (se 7 (by rfl) ⟨16028, by rfl⟩ : syracuseStep 1367765 = 32057) (by norm_num)
theorem B614101 : Blo 239816 614101 := bbase (se 7 (by rfl) ⟨7196, by rfl⟩ : syracuseStep 614101 = 14393) (by norm_num)
theorem B581381 : Blo 239816 581381 := bbase (se 4 (by rfl) ⟨54504, by rfl⟩ : syracuseStep 581381 = 109009) (by norm_num)
theorem B614213 : Blo 239816 614213 := bbase (se 4 (by rfl) ⟨57582, by rfl⟩ : syracuseStep 614213 = 115165) (by norm_num)
theorem B810917 : Blo 239816 810917 := bbase (se 4 (by rfl) ⟨76023, by rfl⟩ : syracuseStep 810917 = 152047) (by norm_num)
theorem B1105829 : Blo 239816 1105829 := bbase (se 4 (by rfl) ⟨103671, by rfl⟩ : syracuseStep 1105829 = 207343) (by norm_num)
theorem B614405 : Blo 239816 614405 := bbase (se 4 (by rfl) ⟨57600, by rfl⟩ : syracuseStep 614405 = 115201) (by norm_num)
theorem B548893 : Blo 239816 548893 := bbase (se 3 (by rfl) ⟨102917, by rfl⟩ : syracuseStep 548893 = 205835) (by norm_num)
theorem B516125 : Blo 239816 516125 := bbase (se 3 (by rfl) ⟨96773, by rfl⟩ : syracuseStep 516125 = 193547) (by norm_num)
theorem B581725 : Blo 239816 581725 := bbase (se 3 (by rfl) ⟨109073, by rfl⟩ : syracuseStep 581725 = 218147) (by norm_num)
theorem B385165 : Blo 239816 385165 := bbase (se 3 (by rfl) ⟨72218, by rfl⟩ : syracuseStep 385165 = 144437) (by norm_num)
theorem B516269 : Blo 239816 516269 := bbase (se 3 (by rfl) ⟨96800, by rfl⟩ : syracuseStep 516269 = 193601) (by norm_num)
theorem B385229 : Blo 239816 385229 := bbase (se 3 (by rfl) ⟨72230, by rfl⟩ : syracuseStep 385229 = 144461) (by norm_num)
theorem B581957 : Blo 239816 581957 := bbase (se 4 (by rfl) ⟨54558, by rfl⟩ : syracuseStep 581957 = 109117) (by norm_num)
theorem B811349 : Blo 239816 811349 := bbase (se 10 (by rfl) ⟨1188, by rfl⟩ : syracuseStep 811349 = 2377) (by norm_num)
theorem B614749 : Blo 239816 614749 := bbase (se 3 (by rfl) ⟨115265, by rfl⟩ : syracuseStep 614749 = 230531) (by norm_num)
theorem B614861 : Blo 239816 614861 := bbase (se 3 (by rfl) ⟨115286, by rfl⟩ : syracuseStep 614861 = 230573) (by norm_num)
theorem B778709 : Blo 239816 778709 := bbase (se 7 (by rfl) ⟨9125, by rfl⟩ : syracuseStep 778709 = 18251) (by norm_num)
theorem B582149 : Blo 239816 582149 := bbase (se 4 (by rfl) ⟨54576, by rfl⟩ : syracuseStep 582149 = 109153) (by norm_num)
theorem B549413 : Blo 239816 549413 := bbase (se 4 (by rfl) ⟨51507, by rfl⟩ : syracuseStep 549413 = 103015) (by norm_num)
theorem B1237637 : Blo 239816 1237637 := bbase (se 4 (by rfl) ⟨116028, by rfl⟩ : syracuseStep 1237637 = 232057) (by norm_num)
theorem B615053 : Blo 239816 615053 := bbase (se 3 (by rfl) ⟨115322, by rfl⟩ : syracuseStep 615053 = 230645) (by norm_num)
theorem B352981 : Blo 239816 352981 := bbase (se 7 (by rfl) ⟨4136, by rfl⟩ : syracuseStep 352981 = 8273) (by norm_num)
theorem B811781 : Blo 239816 811781 := bbase (se 4 (by rfl) ⟨76104, by rfl⟩ : syracuseStep 811781 = 152209) (by norm_num)
theorem B582437 : Blo 239816 582437 := bbase (se 4 (by rfl) ⟨54603, by rfl⟩ : syracuseStep 582437 = 109207) (by norm_num)
theorem B517013 : Blo 239816 517013 := bbase (se 6 (by rfl) ⟨12117, by rfl⟩ : syracuseStep 517013 = 24235) (by norm_num)
theorem B615397 : Blo 239816 615397 := bbase (se 4 (by rfl) ⟨57693, by rfl⟩ : syracuseStep 615397 = 115387) (by norm_num)
theorem B615509 : Blo 239816 615509 := bbase (se 8 (by rfl) ⟨3606, by rfl⟩ : syracuseStep 615509 = 7213) (by norm_num)
theorem B812213 : Blo 239816 812213 := bbase (se 5 (by rfl) ⟨38072, by rfl⟩ : syracuseStep 812213 = 76145) (by norm_num)
theorem B1729781 : Blo 239816 1729781 := bbase (se 5 (by rfl) ⟨81083, by rfl⟩ : syracuseStep 1729781 = 162167) (by norm_num)
theorem B615701 : Blo 239816 615701 := bbase (se 6 (by rfl) ⟨14430, by rfl⟩ : syracuseStep 615701 = 28861) (by norm_num)
theorem B550253 : Blo 239816 550253 := bbase (se 3 (by rfl) ⟨103172, by rfl⟩ : syracuseStep 550253 = 206345) (by norm_num)
theorem B386549 : Blo 239816 386549 := bbase (se 5 (by rfl) ⟨18119, by rfl⟩ : syracuseStep 386549 = 36239) (by norm_num)
theorem B910885 : Blo 239816 910885 := bbase (se 4 (by rfl) ⟨85395, by rfl⟩ : syracuseStep 910885 = 170791) (by norm_num)
theorem B812645 : Blo 239816 812645 := bbase (se 4 (by rfl) ⟨76185, by rfl⟩ : syracuseStep 812645 = 152371) (by norm_num)
theorem B616045 : Blo 239816 616045 := bbase (se 3 (by rfl) ⟨115508, by rfl⟩ : syracuseStep 616045 = 231017) (by norm_num)
theorem B517765 : Blo 239816 517765 := bbase (se 4 (by rfl) ⟨48540, by rfl⟩ : syracuseStep 517765 = 97081) (by norm_num)
theorem B386741 : Blo 239816 386741 := bbase (se 5 (by rfl) ⟨18128, by rfl⟩ : syracuseStep 386741 = 36257) (by norm_num)
theorem B616157 : Blo 239816 616157 := bbase (se 3 (by rfl) ⟨115529, by rfl⟩ : syracuseStep 616157 = 231059) (by norm_num)
theorem B517909 : Blo 239816 517909 := bbase (se 6 (by rfl) ⟨12138, by rfl⟩ : syracuseStep 517909 = 24277) (by norm_num)
theorem B386869 : Blo 239816 386869 := bbase (se 5 (by rfl) ⟨18134, by rfl⟩ : syracuseStep 386869 = 36269) (by norm_num)
theorem B911189 : Blo 239816 911189 := bbase (se 9 (by rfl) ⟨2669, by rfl⟩ : syracuseStep 911189 = 5339) (by norm_num)
theorem B1369973 : Blo 239816 1369973 := bbase (se 5 (by rfl) ⟨64217, by rfl⟩ : syracuseStep 1369973 = 128435) (by norm_num)
theorem B616349 : Blo 239816 616349 := bbase (se 3 (by rfl) ⟨115565, by rfl⟩ : syracuseStep 616349 = 231131) (by norm_num)
theorem B3467285 : Blo 239816 3467285 := bbase (se 6 (by rfl) ⟨81264, by rfl⟩ : syracuseStep 3467285 = 162529) (by norm_num)
theorem B813077 : Blo 239816 813077 := bbase (se 6 (by rfl) ⟨19056, by rfl⟩ : syracuseStep 813077 = 38113) (by norm_num)
theorem B1173541 : Blo 239816 1173541 := bbase (se 4 (by rfl) ⟨110019, by rfl⟩ : syracuseStep 1173541 = 220039) (by norm_num)
theorem B518285 : Blo 239816 518285 := bbase (se 3 (by rfl) ⟨97178, by rfl⟩ : syracuseStep 518285 = 194357) (by norm_num)
theorem B616693 : Blo 239816 616693 := bbase (se 5 (by rfl) ⟨28907, by rfl⟩ : syracuseStep 616693 = 57815) (by norm_num)
theorem B256289 : Blo 239816 256289 := bbase (se 2 (by rfl) ⟨96108, by rfl⟩ : syracuseStep 256289 = 192217) (by norm_num)
theorem B616805 : Blo 239816 616805 := bbase (se 4 (by rfl) ⟨57825, by rfl⟩ : syracuseStep 616805 = 115651) (by norm_num)
theorem B387509 : Blo 239816 387509 := bbase (se 5 (by rfl) ⟨18164, by rfl⟩ : syracuseStep 387509 = 36329) (by norm_num)
theorem B813509 : Blo 239816 813509 := bbase (se 4 (by rfl) ⟨76266, by rfl⟩ : syracuseStep 813509 = 152533) (by norm_num)
theorem B289229 : Blo 239816 289229 := bbase (se 3 (by rfl) ⟨54230, by rfl⟩ : syracuseStep 289229 = 108461) (by norm_num)
theorem B518653 : Blo 239816 518653 := bbase (se 3 (by rfl) ⟨97247, by rfl⟩ : syracuseStep 518653 = 194495) (by norm_num)
theorem B256537 : Blo 239816 256537 := bbase (se 2 (by rfl) ⟨96201, by rfl⟩ : syracuseStep 256537 = 192403) (by norm_num)
theorem B616997 : Blo 239816 616997 := bbase (se 4 (by rfl) ⟨57843, by rfl⟩ : syracuseStep 616997 = 115687) (by norm_num)
theorem B289325 : Blo 239816 289325 := bbase (se 3 (by rfl) ⟨54248, by rfl⟩ : syracuseStep 289325 = 108497) (by norm_num)
theorem B289345 : Blo 239816 289345 := bbase (se 2 (by rfl) ⟨108504, by rfl⟩ : syracuseStep 289345 = 217009) (by norm_num)
theorem B780965 : Blo 239816 780965 := bbase (se 4 (by rfl) ⟨73215, by rfl⟩ : syracuseStep 780965 = 146431) (by norm_num)
theorem B289489 : Blo 239816 289489 := bbase (se 2 (by rfl) ⟨108558, by rfl⟩ : syracuseStep 289489 = 217117) (by norm_num)
theorem B781093 : Blo 239816 781093 := bbase (se 4 (by rfl) ⟨73227, by rfl⟩ : syracuseStep 781093 = 146455) (by norm_num)
theorem B813941 : Blo 239816 813941 := bbase (se 5 (by rfl) ⟨38153, by rfl⟩ : syracuseStep 813941 = 76307) (by norm_num)
theorem B387965 : Blo 239816 387965 := bbase (se 3 (by rfl) ⟨72743, by rfl⟩ : syracuseStep 387965 = 145487) (by norm_num)
theorem B256969 : Blo 239816 256969 := bbase (se 2 (by rfl) ⟨96363, by rfl⟩ : syracuseStep 256969 = 192727) (by norm_num)
theorem B257041 : Blo 239816 257041 := bbase (se 2 (by rfl) ⟨96390, by rfl⟩ : syracuseStep 257041 = 192781) (by norm_num)
theorem B388189 : Blo 239816 388189 := bbase (se 3 (by rfl) ⟨72785, by rfl⟩ : syracuseStep 388189 = 145571) (by norm_num)
theorem B388253 : Blo 239816 388253 := bbase (se 3 (by rfl) ⟨72797, by rfl⟩ : syracuseStep 388253 = 145595) (by norm_num)
theorem B1109189 : Blo 239816 1109189 := bbase (se 4 (by rfl) ⟨103986, by rfl⟩ : syracuseStep 1109189 = 207973) (by norm_num)
theorem B1731797 : Blo 239816 1731797 := bbase (se 7 (by rfl) ⟨20294, by rfl⟩ : syracuseStep 1731797 = 40589) (by norm_num)
theorem B388381 : Blo 239816 388381 := bbase (se 3 (by rfl) ⟨72821, by rfl⟩ : syracuseStep 388381 = 145643) (by norm_num)
theorem B814373 : Blo 239816 814373 := bbase (se 4 (by rfl) ⟨76347, by rfl⟩ : syracuseStep 814373 = 152695) (by norm_num)
theorem B650549 : Blo 239816 650549 := bbase (se 5 (by rfl) ⟨30494, by rfl⟩ : syracuseStep 650549 = 60989) (by norm_num)
theorem B257413 : Blo 239816 257413 := bbase (se 4 (by rfl) ⟨24132, by rfl⟩ : syracuseStep 257413 = 48265) (by norm_num)
theorem B814805 : Blo 239816 814805 := bbase (se 7 (by rfl) ⟨9548, by rfl⟩ : syracuseStep 814805 = 19097) (by norm_num)
theorem B257789 : Blo 239816 257789 := bbase (se 3 (by rfl) ⟨48335, by rfl⟩ : syracuseStep 257789 = 96671) (by norm_num)
theorem B257861 : Blo 239816 257861 := bbase (se 4 (by rfl) ⟨24174, by rfl⟩ : syracuseStep 257861 = 48349) (by norm_num)
theorem B683893 : Blo 239816 683893 := bbase (se 5 (by rfl) ⟨32057, by rfl⟩ : syracuseStep 683893 = 64115) (by norm_num)
theorem B913301 : Blo 239816 913301 := bbase (se 6 (by rfl) ⟨21405, by rfl⟩ : syracuseStep 913301 = 42811) (by norm_num)
theorem B520157 : Blo 239816 520157 := bbase (se 3 (by rfl) ⟨97529, by rfl⟩ : syracuseStep 520157 = 195059) (by norm_num)
theorem B258049 : Blo 239816 258049 := bbase (se 2 (by rfl) ⟨96768, by rfl⟩ : syracuseStep 258049 = 193537) (by norm_num)
theorem B520301 : Blo 239816 520301 := bbase (se 3 (by rfl) ⟨97556, by rfl⟩ : syracuseStep 520301 = 195113) (by norm_num)
theorem B815237 : Blo 239816 815237 := bbase (se 4 (by rfl) ⟨76428, by rfl⟩ : syracuseStep 815237 = 152857) (by norm_num)
theorem B913589 : Blo 239816 913589 := bbase (se 5 (by rfl) ⟨42824, by rfl⟩ : syracuseStep 913589 = 85649) (by norm_num)
theorem B258233 : Blo 239816 258233 := bbase (se 2 (by rfl) ⟨96837, by rfl⟩ : syracuseStep 258233 = 193675) (by norm_num)
theorem B1241413 : Blo 239816 1241413 := bbase (se 4 (by rfl) ⟨116382, by rfl⟩ : syracuseStep 1241413 = 232765) (by norm_num)
theorem B291281 : Blo 239816 291281 := bbase (se 2 (by rfl) ⟨109230, by rfl⟩ : syracuseStep 291281 = 218461) (by norm_num)
theorem B520661 : Blo 239816 520661 := bbase (se 7 (by rfl) ⟨6101, by rfl⟩ : syracuseStep 520661 = 12203) (by norm_num)
theorem B389605 : Blo 239816 389605 := bbase (se 4 (by rfl) ⟨36525, by rfl⟩ : syracuseStep 389605 = 73051) (by norm_num)
theorem B815669 : Blo 239816 815669 := bbase (se 5 (by rfl) ⟨38234, by rfl⟩ : syracuseStep 815669 = 76469) (by norm_num)
theorem B1110629 : Blo 239816 1110629 := bbase (se 4 (by rfl) ⟨104121, by rfl⟩ : syracuseStep 1110629 = 208243) (by norm_num)
theorem B619157 : Blo 239816 619157 := bbase (se 6 (by rfl) ⟨14511, by rfl⟩ : syracuseStep 619157 = 29023) (by norm_num)
theorem B488141 : Blo 239816 488141 := bbase (se 3 (by rfl) ⟨91526, by rfl⟩ : syracuseStep 488141 = 183053) (by norm_num)
theorem B488189 : Blo 239816 488189 := bbase (se 3 (by rfl) ⟨91535, by rfl⟩ : syracuseStep 488189 = 183071) (by norm_num)
theorem B291613 : Blo 239816 291613 := bbase (se 3 (by rfl) ⟨54677, by rfl⟩ : syracuseStep 291613 = 109355) (by norm_num)
theorem B1831733 : Blo 239816 1831733 := bbase (se 5 (by rfl) ⟨85862, by rfl⟩ : syracuseStep 1831733 = 171725) (by norm_num)
theorem B455557 : Blo 239816 455557 := bbase (se 4 (by rfl) ⟨42708, by rfl⟩ : syracuseStep 455557 = 85417) (by norm_num)
theorem B258985 : Blo 239816 258985 := bbase (se 2 (by rfl) ⟨97119, by rfl⟩ : syracuseStep 258985 = 194239) (by norm_num)
theorem B291757 : Blo 239816 291757 := bbase (se 3 (by rfl) ⟨54704, by rfl⟩ : syracuseStep 291757 = 109409) (by norm_num)
theorem B816101 : Blo 239816 816101 := bbase (se 4 (by rfl) ⟨76509, by rfl⟩ : syracuseStep 816101 = 153019) (by norm_num)
theorem B259057 : Blo 239816 259057 := bbase (se 2 (by rfl) ⟨97146, by rfl⟩ : syracuseStep 259057 = 194293) (by norm_num)
theorem B455701 : Blo 239816 455701 := bbase (se 6 (by rfl) ⟨10680, by rfl⟩ : syracuseStep 455701 = 21361) (by norm_num)
theorem B390277 : Blo 239816 390277 := bbase (se 4 (by rfl) ⟨36588, by rfl⟩ : syracuseStep 390277 = 73177) (by norm_num)
theorem B259237 : Blo 239816 259237 := bbase (se 4 (by rfl) ⟨24303, by rfl⟩ : syracuseStep 259237 = 48607) (by norm_num)
theorem B455861 : Blo 239816 455861 := bbase (se 5 (by rfl) ⟨21368, by rfl⟩ : syracuseStep 455861 = 42737) (by norm_num)
theorem B324821 : Blo 239816 324821 := bbase (se 7 (by rfl) ⟨3806, by rfl⟩ : syracuseStep 324821 = 7613) (by norm_num)
theorem B324853 : Blo 239816 324853 := bbase (se 5 (by rfl) ⟨15227, by rfl⟩ : syracuseStep 324853 = 30455) (by norm_num)
theorem B456005 : Blo 239816 456005 := bbase (se 4 (by rfl) ⟨42750, by rfl⟩ : syracuseStep 456005 = 85501) (by norm_num)
theorem B685397 : Blo 239816 685397 := bbase (se 13 (by rfl) ⟨125, by rfl⟩ : syracuseStep 685397 = 251) (by norm_num)
theorem B914773 : Blo 239816 914773 := bbase (se 13 (by rfl) ⟨167, by rfl⟩ : syracuseStep 914773 = 335) (by norm_num)
theorem B816533 : Blo 239816 816533 := bbase (se 6 (by rfl) ⟨19137, by rfl⟩ : syracuseStep 816533 = 38275) (by norm_num)
theorem B587213 : Blo 239816 587213 := bbase (se 3 (by rfl) ⟨110102, by rfl⟩ : syracuseStep 587213 = 220205) (by norm_num)
theorem B652789 : Blo 239816 652789 := bbase (se 5 (by rfl) ⟨30599, by rfl⟩ : syracuseStep 652789 = 61199) (by norm_num)
theorem B259681 : Blo 239816 259681 := bbase (se 2 (by rfl) ⟨97380, by rfl⟩ : syracuseStep 259681 = 194761) (by norm_num)
theorem B456293 : Blo 239816 456293 := bbase (se 4 (by rfl) ⟨42777, by rfl⟩ : syracuseStep 456293 = 85555) (by norm_num)
theorem B915077 : Blo 239816 915077 := bbase (se 4 (by rfl) ⟨85788, by rfl⟩ : syracuseStep 915077 = 171577) (by norm_num)
theorem B980693 : Blo 239816 980693 := bbase (se 7 (by rfl) ⟨11492, by rfl⟩ : syracuseStep 980693 = 22985) (by norm_num)
theorem B259805 : Blo 239816 259805 := bbase (se 3 (by rfl) ⟨48713, by rfl⟩ : syracuseStep 259805 = 97427) (by norm_num)
theorem B2324213 : Blo 239816 2324213 := bbase (se 5 (by rfl) ⟨108947, by rfl⟩ : syracuseStep 2324213 = 217895) (by norm_num)
theorem B456445 : Blo 239816 456445 := bbase (se 3 (by rfl) ⟨85583, by rfl⟩ : syracuseStep 456445 = 171167) (by norm_num)
theorem B816965 : Blo 239816 816965 := bbase (se 4 (by rfl) ⟨76590, by rfl⟩ : syracuseStep 816965 = 153181) (by norm_num)
theorem B292781 : Blo 239816 292781 := bbase (se 3 (by rfl) ⟨54896, by rfl⟩ : syracuseStep 292781 = 109793) (by norm_num)
theorem B260057 : Blo 239816 260057 := bbase (se 2 (by rfl) ⟨97521, by rfl⟩ : syracuseStep 260057 = 195043) (by norm_num)
theorem B489461 : Blo 239816 489461 := bbase (se 5 (by rfl) ⟨22943, by rfl⟩ : syracuseStep 489461 = 45887) (by norm_num)
theorem B456749 : Blo 239816 456749 := bbase (se 3 (by rfl) ⟨85640, by rfl⟩ : syracuseStep 456749 = 171281) (by norm_num)
theorem B587893 : Blo 239816 587893 := bbase (se 5 (by rfl) ⟨27557, by rfl⟩ : syracuseStep 587893 = 55115) (by norm_num)
theorem B817397 : Blo 239816 817397 := bbase (se 5 (by rfl) ⟨38315, by rfl⟩ : syracuseStep 817397 = 76631) (by norm_num)
theorem B1538453 : Blo 239816 1538453 := bbase (se 6 (by rfl) ⟨36057, by rfl⟩ : syracuseStep 1538453 = 72115) (by norm_num)
theorem B489989 : Blo 239816 489989 := bbase (se 4 (by rfl) ⟨45936, by rfl⟩ : syracuseStep 489989 = 91873) (by norm_num)
theorem B260653 : Blo 239816 260653 := bbase (se 3 (by rfl) ⟨48872, by rfl⟩ : syracuseStep 260653 = 97745) (by norm_num)
theorem B260753 : Blo 239816 260753 := bbase (se 2 (by rfl) ⟨97782, by rfl⟩ : syracuseStep 260753 = 195565) (by norm_num)
theorem B817829 : Blo 239816 817829 := bbase (se 4 (by rfl) ⟨76671, by rfl⟩ : syracuseStep 817829 = 153343) (by norm_num)
theorem B457501 : Blo 239816 457501 := bbase (se 3 (by rfl) ⟨85781, by rfl⟩ : syracuseStep 457501 = 171563) (by norm_num)
theorem B686981 : Blo 239816 686981 := bbase (se 4 (by rfl) ⟨64404, by rfl⟩ : syracuseStep 686981 = 128809) (by norm_num)
theorem B457645 : Blo 239816 457645 := bbase (se 3 (by rfl) ⟨85808, by rfl⟩ : syracuseStep 457645 = 171617) (by norm_num)
theorem B293917 : Blo 239816 293917 := bbase (se 3 (by rfl) ⟨55109, by rfl⟩ : syracuseStep 293917 = 110219) (by norm_num)
theorem B457805 : Blo 239816 457805 := bbase (se 3 (by rfl) ⟨85838, by rfl⟩ : syracuseStep 457805 = 171677) (by norm_num)
theorem B818261 : Blo 239816 818261 := bbase (se 8 (by rfl) ⟨4794, by rfl⟩ : syracuseStep 818261 = 9589) (by norm_num)
theorem B457949 : Blo 239816 457949 := bbase (se 3 (by rfl) ⟨85865, by rfl⟩ : syracuseStep 457949 = 171731) (by norm_num)
theorem B392501 : Blo 239816 392501 := bbase (se 5 (by rfl) ⟨18398, by rfl⟩ : syracuseStep 392501 = 36797) (by norm_num)
theorem B359741 : Blo 239816 359741 := bbase (se 3 (by rfl) ⟨67451, by rfl⟩ : syracuseStep 359741 = 134903) (by norm_num)
theorem B359765 : Blo 239816 359765 := bbase (se 11 (by rfl) ⟨263, by rfl⟩ : syracuseStep 359765 = 527) (by norm_num)
theorem B359789 : Blo 239816 359789 := bbase (se 3 (by rfl) ⟨67460, by rfl⟩ : syracuseStep 359789 = 134921) (by norm_num)
theorem B359813 : Blo 239816 359813 := bbase (se 4 (by rfl) ⟨33732, by rfl⟩ : syracuseStep 359813 = 67465) (by norm_num)
theorem B359837 : Blo 239816 359837 := bbase (se 3 (by rfl) ⟨67469, by rfl⟩ : syracuseStep 359837 = 134939) (by norm_num)
theorem B359861 : Blo 239816 359861 := bbase (se 5 (by rfl) ⟨16868, by rfl⟩ : syracuseStep 359861 = 33737) (by norm_num)
theorem B359885 : Blo 239816 359885 := bbase (se 3 (by rfl) ⟨67478, by rfl⟩ : syracuseStep 359885 = 134957) (by norm_num)
theorem B359909 : Blo 239816 359909 := bbase (se 4 (by rfl) ⟨33741, by rfl⟩ : syracuseStep 359909 = 67483) (by norm_num)
theorem B359933 : Blo 239816 359933 := bbase (se 3 (by rfl) ⟨67487, by rfl⟩ : syracuseStep 359933 = 134975) (by norm_num)
theorem B458237 : Blo 239816 458237 := bbase (se 3 (by rfl) ⟨85919, by rfl⟩ : syracuseStep 458237 = 171839) (by norm_num)
theorem B818693 : Blo 239816 818693 := bbase (se 4 (by rfl) ⟨76752, by rfl⟩ : syracuseStep 818693 = 153505) (by norm_num)
theorem B359957 : Blo 239816 359957 := bbase (se 6 (by rfl) ⟨8436, by rfl⟩ : syracuseStep 359957 = 16873) (by norm_num)
theorem B687653 : Blo 239816 687653 := bbase (se 4 (by rfl) ⟨64467, by rfl⟩ : syracuseStep 687653 = 128935) (by norm_num)
theorem B359981 : Blo 239816 359981 := bbase (se 3 (by rfl) ⟨67496, by rfl⟩ : syracuseStep 359981 = 134993) (by norm_num)
theorem B360005 : Blo 239816 360005 := bbase (se 4 (by rfl) ⟨33750, by rfl⟩ : syracuseStep 360005 = 67501) (by norm_num)
theorem B360029 : Blo 239816 360029 := bbase (se 3 (by rfl) ⟨67505, by rfl⟩ : syracuseStep 360029 = 135011) (by norm_num)
theorem B360053 : Blo 239816 360053 := bbase (se 5 (by rfl) ⟨16877, by rfl⟩ : syracuseStep 360053 = 33755) (by norm_num)
theorem B1638005 : Blo 239816 1638005 := bbase (se 5 (by rfl) ⟨76781, by rfl⟩ : syracuseStep 1638005 = 153563) (by norm_num)
theorem B360077 : Blo 239816 360077 := bbase (se 3 (by rfl) ⟨67514, by rfl⟩ : syracuseStep 360077 = 135029) (by norm_num)
theorem B458389 : Blo 239816 458389 := bbase (se 6 (by rfl) ⟨10743, by rfl⟩ : syracuseStep 458389 = 21487) (by norm_num)
theorem B360101 : Blo 239816 360101 := bbase (se 4 (by rfl) ⟨33759, by rfl⟩ : syracuseStep 360101 = 67519) (by norm_num)
theorem B360125 : Blo 239816 360125 := bbase (se 3 (by rfl) ⟨67523, by rfl⟩ : syracuseStep 360125 = 135047) (by norm_num)
theorem B917189 : Blo 239816 917189 := bbase (se 4 (by rfl) ⟨85986, by rfl⟩ : syracuseStep 917189 = 171973) (by norm_num)
theorem B360149 : Blo 239816 360149 := bbase (se 7 (by rfl) ⟨4220, by rfl⟩ : syracuseStep 360149 = 8441) (by norm_num)
theorem B360173 : Blo 239816 360173 := bbase (se 3 (by rfl) ⟨67532, by rfl⟩ : syracuseStep 360173 = 135065) (by norm_num)
theorem B360197 : Blo 239816 360197 := bbase (se 4 (by rfl) ⟨33768, by rfl⟩ : syracuseStep 360197 = 67537) (by norm_num)
theorem B360221 : Blo 239816 360221 := bbase (se 3 (by rfl) ⟨67541, by rfl⟩ : syracuseStep 360221 = 135083) (by norm_num)
theorem B360245 : Blo 239816 360245 := bbase (se 5 (by rfl) ⟨16886, by rfl⟩ : syracuseStep 360245 = 33773) (by norm_num)
theorem B360269 : Blo 239816 360269 := bbase (se 3 (by rfl) ⟨67550, by rfl⟩ : syracuseStep 360269 = 135101) (by norm_num)
theorem B360293 : Blo 239816 360293 := bbase (se 4 (by rfl) ⟨33777, by rfl⟩ : syracuseStep 360293 = 67555) (by norm_num)
theorem B360317 : Blo 239816 360317 := bbase (se 3 (by rfl) ⟨67559, by rfl⟩ : syracuseStep 360317 = 135119) (by norm_num)
theorem B360341 : Blo 239816 360341 := bbase (se 6 (by rfl) ⟨8445, by rfl⟩ : syracuseStep 360341 = 16891) (by norm_num)
theorem B360365 : Blo 239816 360365 := bbase (se 3 (by rfl) ⟨67568, by rfl⟩ : syracuseStep 360365 = 135137) (by norm_num)
theorem B819125 : Blo 239816 819125 := bbase (se 5 (by rfl) ⟨38396, by rfl⟩ : syracuseStep 819125 = 76793) (by norm_num)
theorem B360389 : Blo 239816 360389 := bbase (se 4 (by rfl) ⟨33786, by rfl⟩ : syracuseStep 360389 = 67573) (by norm_num)
theorem B458693 : Blo 239816 458693 := bbase (se 4 (by rfl) ⟨43002, by rfl⟩ : syracuseStep 458693 = 86005) (by norm_num)
theorem B688085 : Blo 239816 688085 := bbase (se 7 (by rfl) ⟨8063, by rfl⟩ : syracuseStep 688085 = 16127) (by norm_num)
theorem B360413 : Blo 239816 360413 := bbase (se 3 (by rfl) ⟨67577, by rfl⟩ : syracuseStep 360413 = 135155) (by norm_num)
theorem B917477 : Blo 239816 917477 := bbase (se 4 (by rfl) ⟨86013, by rfl⟩ : syracuseStep 917477 = 172027) (by norm_num)
theorem B360437 : Blo 239816 360437 := bbase (se 5 (by rfl) ⟨16895, by rfl⟩ : syracuseStep 360437 = 33791) (by norm_num)
theorem B360449 : Blo 239816 360449 := bstep (se 2 (by rfl) ⟨135168, by rfl⟩ : syracuseStep 360449 = 270337) B270337
theorem B1376261 : Blo 239816 1376261 := bstep (se 4 (by rfl) ⟨129024, by rfl⟩ : syracuseStep 1376261 = 258049) B258049
theorem B360467 : Blo 239816 360467 := bstep (se 1 (by rfl) ⟨270350, by rfl⟩ : syracuseStep 360467 = 540701) B540701
theorem B360497 : Blo 239816 360497 := bstep (se 2 (by rfl) ⟨135186, by rfl⟩ : syracuseStep 360497 = 270373) B270373
theorem B360515 : Blo 239816 360515 := bstep (se 1 (by rfl) ⟨270386, by rfl⟩ : syracuseStep 360515 = 540773) B540773
theorem B360545 : Blo 239816 360545 := bstep (se 2 (by rfl) ⟨135204, by rfl⟩ : syracuseStep 360545 = 270409) B270409
theorem B360563 : Blo 239816 360563 := bstep (se 1 (by rfl) ⟨270422, by rfl⟩ : syracuseStep 360563 = 540845) B540845
theorem B819341 : Blo 239816 819341 := bstep (se 3 (by rfl) ⟨153626, by rfl⟩ : syracuseStep 819341 = 307253) B307253
theorem B360593 : Blo 239816 360593 := bstep (se 2 (by rfl) ⟨135222, by rfl⟩ : syracuseStep 360593 = 270445) B270445
theorem B360611 : Blo 239816 360611 := bstep (se 1 (by rfl) ⟨270458, by rfl⟩ : syracuseStep 360611 = 540917) B540917
theorem B360641 : Blo 239816 360641 := bstep (se 2 (by rfl) ⟨135240, by rfl⟩ : syracuseStep 360641 = 270481) B270481
theorem B819395 : Blo 239816 819395 := bstep (se 1 (by rfl) ⟨614546, by rfl⟩ : syracuseStep 819395 = 1229093) B1229093
theorem B3080389 : Blo 239816 3080389 := bstep (se 4 (by rfl) ⟨288786, by rfl⟩ : syracuseStep 3080389 = 577573) B577573
theorem B360659 : Blo 239816 360659 := bstep (se 1 (by rfl) ⟨270494, by rfl⟩ : syracuseStep 360659 = 540989) B540989
theorem B360689 : Blo 239816 360689 := bstep (se 2 (by rfl) ⟨135258, by rfl⟩ : syracuseStep 360689 = 270517) B270517
theorem B360707 : Blo 239816 360707 := bstep (se 1 (by rfl) ⟨270530, by rfl⟩ : syracuseStep 360707 = 541061) B541061
theorem B360737 : Blo 239816 360737 := bstep (se 2 (by rfl) ⟨135276, by rfl⟩ : syracuseStep 360737 = 270553) B270553
theorem B360755 : Blo 239816 360755 := bstep (se 1 (by rfl) ⟨270566, by rfl⟩ : syracuseStep 360755 = 541133) B541133
theorem B360785 : Blo 239816 360785 := bstep (se 2 (by rfl) ⟨135294, by rfl⟩ : syracuseStep 360785 = 270589) B270589
theorem B360803 : Blo 239816 360803 := bstep (se 1 (by rfl) ⟨270602, by rfl⟩ : syracuseStep 360803 = 541205) B541205
theorem B360833 : Blo 239816 360833 := bstep (se 2 (by rfl) ⟨135312, by rfl⟩ : syracuseStep 360833 = 270625) B270625
theorem B360851 : Blo 239816 360851 := bstep (se 1 (by rfl) ⟨270638, by rfl⟩ : syracuseStep 360851 = 541277) B541277
theorem B360881 : Blo 239816 360881 := bstep (se 2 (by rfl) ⟨135330, by rfl⟩ : syracuseStep 360881 = 270661) B270661
theorem B360899 : Blo 239816 360899 := bstep (se 1 (by rfl) ⟨270674, by rfl⟩ : syracuseStep 360899 = 541349) B541349
theorem B655825 : Blo 239816 655825 := bstep (se 2 (by rfl) ⟨245934, by rfl⟩ : syracuseStep 655825 = 491869) B491869
theorem B819665 : Blo 239816 819665 := bstep (se 2 (by rfl) ⟨307374, by rfl⟩ : syracuseStep 819665 = 614749) B614749
theorem B360929 : Blo 239816 360929 := bstep (se 2 (by rfl) ⟨135348, by rfl⟩ : syracuseStep 360929 = 270697) B270697
theorem B688621 : Blo 239816 688621 := bstep (se 3 (by rfl) ⟨129116, by rfl⟩ : syracuseStep 688621 = 258233) B258233
theorem B360947 : Blo 239816 360947 := bstep (se 1 (by rfl) ⟨270710, by rfl⟩ : syracuseStep 360947 = 541421) B541421
theorem B360977 : Blo 239816 360977 := bstep (se 2 (by rfl) ⟨135366, by rfl⟩ : syracuseStep 360977 = 270733) B270733
theorem B360995 : Blo 239816 360995 := bstep (se 1 (by rfl) ⟨270746, by rfl⟩ : syracuseStep 360995 = 541493) B541493
theorem B361025 : Blo 239816 361025 := bstep (se 2 (by rfl) ⟨135384, by rfl⟩ : syracuseStep 361025 = 270769) B270769
theorem B328259 : Blo 239816 328259 := bstep (se 1 (by rfl) ⟨246194, by rfl⟩ : syracuseStep 328259 = 492389) B492389
theorem B361043 : Blo 239816 361043 := bstep (se 1 (by rfl) ⟨270782, by rfl⟩ : syracuseStep 361043 = 541565) B541565
theorem B361073 : Blo 239816 361073 := bstep (se 2 (by rfl) ⟨135402, by rfl⟩ : syracuseStep 361073 = 270805) B270805
theorem B361091 : Blo 239816 361091 := bstep (se 1 (by rfl) ⟨270818, by rfl⟩ : syracuseStep 361091 = 541637) B541637
theorem B361121 : Blo 239816 361121 := bstep (se 2 (by rfl) ⟨135420, by rfl⟩ : syracuseStep 361121 = 270841) B270841
theorem B1376945 : Blo 239816 1376945 := bstep (se 2 (by rfl) ⟨516354, by rfl⟩ : syracuseStep 1376945 = 1032709) B1032709
theorem B361139 : Blo 239816 361139 := bstep (se 1 (by rfl) ⟨270854, by rfl⟩ : syracuseStep 361139 = 541709) B541709
theorem B492227 : Blo 239816 492227 := bstep (se 1 (by rfl) ⟨369170, by rfl⟩ : syracuseStep 492227 = 738341) B738341
theorem B361169 : Blo 239816 361169 := bstep (se 2 (by rfl) ⟨135438, by rfl⟩ : syracuseStep 361169 = 270877) B270877
theorem B361187 : Blo 239816 361187 := bstep (se 1 (by rfl) ⟨270890, by rfl⟩ : syracuseStep 361187 = 541781) B541781
theorem B361217 : Blo 239816 361217 := bstep (se 2 (by rfl) ⟨135456, by rfl⟩ : syracuseStep 361217 = 270913) B270913
theorem B361235 : Blo 239816 361235 := bstep (se 1 (by rfl) ⟨270926, by rfl⟩ : syracuseStep 361235 = 541853) B541853
theorem B492323 : Blo 239816 492323 := bstep (se 1 (by rfl) ⟨369242, by rfl⟩ : syracuseStep 492323 = 738485) B738485
theorem B361265 : Blo 239816 361265 := bstep (se 2 (by rfl) ⟨135474, by rfl⟩ : syracuseStep 361265 = 270949) B270949
theorem B361283 : Blo 239816 361283 := bstep (se 1 (by rfl) ⟨270962, by rfl⟩ : syracuseStep 361283 = 541925) B541925
theorem B361313 : Blo 239816 361313 := bstep (se 2 (by rfl) ⟨135492, by rfl⟩ : syracuseStep 361313 = 270985) B270985
theorem B361331 : Blo 239816 361331 := bstep (se 1 (by rfl) ⟨270998, by rfl⟩ : syracuseStep 361331 = 541997) B541997
theorem B263027 : Blo 239816 263027 := bstep (se 1 (by rfl) ⟨197270, by rfl⟩ : syracuseStep 263027 = 394541) B394541
theorem B361361 : Blo 239816 361361 := bstep (se 2 (by rfl) ⟨135510, by rfl⟩ : syracuseStep 361361 = 271021) B271021
theorem B459665 : Blo 239816 459665 := bstep (se 2 (by rfl) ⟨172374, by rfl⟩ : syracuseStep 459665 = 344749) B344749
theorem B361379 : Blo 239816 361379 := bstep (se 1 (by rfl) ⟨271034, by rfl⟩ : syracuseStep 361379 = 542069) B542069
theorem B918449 : Blo 239816 918449 := bstep (se 2 (by rfl) ⟨344418, by rfl⟩ : syracuseStep 918449 = 688837) B688837
theorem B328627 : Blo 239816 328627 := bstep (se 1 (by rfl) ⟨246470, by rfl⟩ : syracuseStep 328627 = 492941) B492941
theorem B361409 : Blo 239816 361409 := bstep (se 2 (by rfl) ⟨135528, by rfl⟩ : syracuseStep 361409 = 271057) B271057
theorem B361427 : Blo 239816 361427 := bstep (se 1 (by rfl) ⟨271070, by rfl⟩ : syracuseStep 361427 = 542141) B542141
theorem B1868771 : Blo 239816 1868771 := bstep (se 1 (by rfl) ⟨1401578, by rfl⟩ : syracuseStep 1868771 = 2803157) B2803157
theorem B820205 : Blo 239816 820205 := bstep (se 3 (by rfl) ⟨153788, by rfl⟩ : syracuseStep 820205 = 307577) B307577
theorem B361457 : Blo 239816 361457 := bstep (se 2 (by rfl) ⟨135546, by rfl⟩ : syracuseStep 361457 = 271093) B271093
theorem B328691 : Blo 239816 328691 := bstep (se 1 (by rfl) ⟨246518, by rfl⟩ : syracuseStep 328691 = 493037) B493037
theorem B361475 : Blo 239816 361475 := bstep (se 1 (by rfl) ⟨271106, by rfl⟩ : syracuseStep 361475 = 542213) B542213
theorem B361505 : Blo 239816 361505 := bstep (se 2 (by rfl) ⟨135564, by rfl⟩ : syracuseStep 361505 = 271129) B271129
theorem B820259 : Blo 239816 820259 := bstep (se 1 (by rfl) ⟨615194, by rfl⟩ : syracuseStep 820259 = 1230389) B1230389
theorem B984113 : Blo 239816 984113 := bstep (se 2 (by rfl) ⟨369042, by rfl⟩ : syracuseStep 984113 = 738085) B738085
theorem B361523 : Blo 239816 361523 := bstep (se 1 (by rfl) ⟨271142, by rfl⟩ : syracuseStep 361523 = 542285) B542285
theorem B361553 : Blo 239816 361553 := bstep (se 2 (by rfl) ⟨135582, by rfl⟩ : syracuseStep 361553 = 271165) B271165
theorem B361571 : Blo 239816 361571 := bstep (se 1 (by rfl) ⟨271178, by rfl⟩ : syracuseStep 361571 = 542357) B542357
theorem B361601 : Blo 239816 361601 := bstep (se 2 (by rfl) ⟨135600, by rfl⟩ : syracuseStep 361601 = 271201) B271201
theorem B361619 : Blo 239816 361619 := bstep (se 1 (by rfl) ⟨271214, by rfl⟩ : syracuseStep 361619 = 542429) B542429
theorem B361649 : Blo 239816 361649 := bstep (se 2 (by rfl) ⟨135618, by rfl⟩ : syracuseStep 361649 = 271237) B271237
theorem B394433 : Blo 239816 394433 := bstep (se 2 (by rfl) ⟨147912, by rfl⟩ : syracuseStep 394433 = 295825) B295825
theorem B361667 : Blo 239816 361667 := bstep (se 1 (by rfl) ⟨271250, by rfl⟩ : syracuseStep 361667 = 542501) B542501
theorem B361697 : Blo 239816 361697 := bstep (se 2 (by rfl) ⟨135636, by rfl⟩ : syracuseStep 361697 = 271273) B271273
theorem B361715 : Blo 239816 361715 := bstep (se 1 (by rfl) ⟨271286, by rfl⟩ : syracuseStep 361715 = 542573) B542573
theorem B361745 : Blo 239816 361745 := bstep (se 2 (by rfl) ⟨135654, by rfl⟩ : syracuseStep 361745 = 271309) B271309
theorem B361763 : Blo 239816 361763 := bstep (se 1 (by rfl) ⟨271322, by rfl⟩ : syracuseStep 361763 = 542645) B542645
theorem B1541425 : Blo 239816 1541425 := bstep (se 2 (by rfl) ⟨578034, by rfl⟩ : syracuseStep 1541425 = 1156069) B1156069
theorem B820529 : Blo 239816 820529 := bstep (se 2 (by rfl) ⟨307698, by rfl⟩ : syracuseStep 820529 = 615397) B615397
theorem B5276981 : Blo 239816 5276981 := bstep (se 5 (by rfl) ⟨247358, by rfl⟩ : syracuseStep 5276981 = 494717) B494717
theorem B361793 : Blo 239816 361793 := bstep (se 2 (by rfl) ⟨135672, by rfl⟩ : syracuseStep 361793 = 271345) B271345
theorem B361811 : Blo 239816 361811 := bstep (se 1 (by rfl) ⟨271358, by rfl⟩ : syracuseStep 361811 = 542717) B542717
theorem B361841 : Blo 239816 361841 := bstep (se 2 (by rfl) ⟨135690, by rfl⟩ : syracuseStep 361841 = 271381) B271381
theorem B361859 : Blo 239816 361859 := bstep (se 1 (by rfl) ⟨271394, by rfl⟩ : syracuseStep 361859 = 542789) B542789
theorem B361889 : Blo 239816 361889 := bstep (se 2 (by rfl) ⟨135708, by rfl⟩ : syracuseStep 361889 = 271417) B271417
theorem B361907 : Blo 239816 361907 := bstep (se 1 (by rfl) ⟨271430, by rfl⟩ : syracuseStep 361907 = 542861) B542861
theorem B361937 : Blo 239816 361937 := bstep (se 2 (by rfl) ⟨135726, by rfl⟩ : syracuseStep 361937 = 271453) B271453
theorem B361955 : Blo 239816 361955 := bstep (se 1 (by rfl) ⟨271466, by rfl⟩ : syracuseStep 361955 = 542933) B542933
theorem B361985 : Blo 239816 361985 := bstep (se 2 (by rfl) ⟨135744, by rfl⟩ : syracuseStep 361985 = 271489) B271489
theorem B362003 : Blo 239816 362003 := bstep (se 1 (by rfl) ⟨271502, by rfl⟩ : syracuseStep 362003 = 543005) B543005
theorem B362033 : Blo 239816 362033 := bstep (se 2 (by rfl) ⟨135762, by rfl⟩ : syracuseStep 362033 = 271525) B271525
theorem B362051 : Blo 239816 362051 := bstep (se 1 (by rfl) ⟨271538, by rfl⟩ : syracuseStep 362051 = 543077) B543077
theorem B362081 : Blo 239816 362081 := bstep (se 2 (by rfl) ⟨135780, by rfl⟩ : syracuseStep 362081 = 271561) B271561
theorem B2754161 : Blo 239816 2754161 := bstep (se 2 (by rfl) ⟨1032810, by rfl⟩ : syracuseStep 2754161 = 2065621) B2065621
theorem B362099 : Blo 239816 362099 := bstep (se 1 (by rfl) ⟨271574, by rfl⟩ : syracuseStep 362099 = 543149) B543149
theorem B362129 : Blo 239816 362129 := bstep (se 2 (by rfl) ⟨135798, by rfl⟩ : syracuseStep 362129 = 271597) B271597
theorem B362147 : Blo 239816 362147 := bstep (se 1 (by rfl) ⟨271610, by rfl⟩ : syracuseStep 362147 = 543221) B543221
theorem B362177 : Blo 239816 362177 := bstep (se 2 (by rfl) ⟨135816, by rfl⟩ : syracuseStep 362177 = 271633) B271633
theorem B6620869 : Blo 239816 6620869 := bstep (se 4 (by rfl) ⟨620706, by rfl⟩ : syracuseStep 6620869 = 1241413) B1241413
theorem B362195 : Blo 239816 362195 := bstep (se 1 (by rfl) ⟨271646, by rfl⟩ : syracuseStep 362195 = 543293) B543293
theorem B362225 : Blo 239816 362225 := bstep (se 2 (by rfl) ⟨135834, by rfl⟩ : syracuseStep 362225 = 271669) B271669
theorem B362243 : Blo 239816 362243 := bstep (se 1 (by rfl) ⟨271682, by rfl⟩ : syracuseStep 362243 = 543365) B543365
theorem B460561 : Blo 239816 460561 := bstep (se 2 (by rfl) ⟨172710, by rfl⟩ : syracuseStep 460561 = 345421) B345421
theorem B362273 : Blo 239816 362273 := bstep (se 2 (by rfl) ⟨135852, by rfl⟩ : syracuseStep 362273 = 271705) B271705
theorem B362291 : Blo 239816 362291 := bstep (se 1 (by rfl) ⟨271718, by rfl⟩ : syracuseStep 362291 = 543437) B543437
theorem B821069 : Blo 239816 821069 := bstep (se 3 (by rfl) ⟨153950, by rfl⟩ : syracuseStep 821069 = 307901) B307901
theorem B362321 : Blo 239816 362321 := bstep (se 2 (by rfl) ⟨135870, by rfl⟩ : syracuseStep 362321 = 271741) B271741
theorem B362339 : Blo 239816 362339 := bstep (se 1 (by rfl) ⟨271754, by rfl⟩ : syracuseStep 362339 = 543509) B543509
theorem B362369 : Blo 239816 362369 := bstep (se 2 (by rfl) ⟨135888, by rfl⟩ : syracuseStep 362369 = 271777) B271777
theorem B821123 : Blo 239816 821123 := bstep (se 1 (by rfl) ⟨615842, by rfl⟩ : syracuseStep 821123 = 1231685) B1231685
theorem B362387 : Blo 239816 362387 := bstep (se 1 (by rfl) ⟨271790, by rfl⟩ : syracuseStep 362387 = 543581) B543581
theorem B362417 : Blo 239816 362417 := bstep (se 2 (by rfl) ⟨135906, by rfl⟩ : syracuseStep 362417 = 271813) B271813
theorem B460721 : Blo 239816 460721 := bstep (se 2 (by rfl) ⟨172770, by rfl⟩ : syracuseStep 460721 = 345541) B345541
theorem B362435 : Blo 239816 362435 := bstep (se 1 (by rfl) ⟨271826, by rfl⟩ : syracuseStep 362435 = 543653) B543653
theorem B11241413 : Blo 239816 11241413 := bstep (se 4 (by rfl) ⟨1053882, by rfl⟩ : syracuseStep 11241413 = 2107765) B2107765
theorem B362465 : Blo 239816 362465 := bstep (se 2 (by rfl) ⟨135924, by rfl⟩ : syracuseStep 362465 = 271849) B271849
theorem B362483 : Blo 239816 362483 := bstep (se 1 (by rfl) ⟨271862, by rfl⟩ : syracuseStep 362483 = 543725) B543725
theorem B362513 : Blo 239816 362513 := bstep (se 2 (by rfl) ⟨135942, by rfl⟩ : syracuseStep 362513 = 271885) B271885
theorem B362531 : Blo 239816 362531 := bstep (se 1 (by rfl) ⟨271898, by rfl⟩ : syracuseStep 362531 = 543797) B543797
theorem B1214513 : Blo 239816 1214513 := bstep (se 2 (by rfl) ⟨455442, by rfl⟩ : syracuseStep 1214513 = 910885) B910885
theorem B362561 : Blo 239816 362561 := bstep (se 2 (by rfl) ⟨135960, by rfl⟩ : syracuseStep 362561 = 271921) B271921
theorem B362579 : Blo 239816 362579 := bstep (se 1 (by rfl) ⟨271934, by rfl⟩ : syracuseStep 362579 = 543869) B543869
theorem B1378403 : Blo 239816 1378403 := bstep (se 1 (by rfl) ⟨1033802, by rfl⟩ : syracuseStep 1378403 = 2067605) B2067605
theorem B362609 : Blo 239816 362609 := bstep (se 2 (by rfl) ⟨135978, by rfl⟩ : syracuseStep 362609 = 271957) B271957
theorem B362627 : Blo 239816 362627 := bstep (se 1 (by rfl) ⟨271970, by rfl⟩ : syracuseStep 362627 = 543941) B543941
theorem B821393 : Blo 239816 821393 := bstep (se 2 (by rfl) ⟨308022, by rfl⟩ : syracuseStep 821393 = 616045) B616045
theorem B362657 : Blo 239816 362657 := bstep (se 2 (by rfl) ⟨135996, by rfl⟩ : syracuseStep 362657 = 271993) B271993
theorem B690353 : Blo 239816 690353 := bstep (se 2 (by rfl) ⟨258882, by rfl⟩ : syracuseStep 690353 = 517765) B517765
theorem B362675 : Blo 239816 362675 := bstep (se 1 (by rfl) ⟨272006, by rfl⟩ : syracuseStep 362675 = 544013) B544013
theorem B362705 : Blo 239816 362705 := bstep (se 2 (by rfl) ⟨136014, by rfl⟩ : syracuseStep 362705 = 272029) B272029
theorem B362723 : Blo 239816 362723 := bstep (se 1 (by rfl) ⟨272042, by rfl⟩ : syracuseStep 362723 = 544085) B544085
theorem B362753 : Blo 239816 362753 := bstep (se 2 (by rfl) ⟨136032, by rfl⟩ : syracuseStep 362753 = 272065) B272065
theorem B362771 : Blo 239816 362771 := bstep (se 1 (by rfl) ⟨272078, by rfl⟩ : syracuseStep 362771 = 544157) B544157
theorem B362801 : Blo 239816 362801 := bstep (se 2 (by rfl) ⟨136050, by rfl⟩ : syracuseStep 362801 = 272101) B272101
theorem B362819 : Blo 239816 362819 := bstep (se 1 (by rfl) ⟨272114, by rfl⟩ : syracuseStep 362819 = 544229) B544229
theorem B461123 : Blo 239816 461123 := bstep (se 1 (by rfl) ⟨345842, by rfl⟩ : syracuseStep 461123 = 691685) B691685
theorem B362849 : Blo 239816 362849 := bstep (se 2 (by rfl) ⟨136068, by rfl⟩ : syracuseStep 362849 = 272137) B272137
theorem B919907 : Blo 239816 919907 := bstep (se 1 (by rfl) ⟨689930, by rfl⟩ : syracuseStep 919907 = 1379861) B1379861
theorem B690545 : Blo 239816 690545 := bstep (se 2 (by rfl) ⟨258954, by rfl⟩ : syracuseStep 690545 = 517909) B517909
theorem B362867 : Blo 239816 362867 := bstep (se 1 (by rfl) ⟨272150, by rfl⟩ : syracuseStep 362867 = 544301) B544301
theorem B362897 : Blo 239816 362897 := bstep (se 2 (by rfl) ⟨136086, by rfl⟩ : syracuseStep 362897 = 272173) B272173
theorem B362915 : Blo 239816 362915 := bstep (se 1 (by rfl) ⟨272186, by rfl⟩ : syracuseStep 362915 = 544373) B544373
theorem B362945 : Blo 239816 362945 := bstep (se 2 (by rfl) ⟨136104, by rfl⟩ : syracuseStep 362945 = 272209) B272209
theorem B362963 : Blo 239816 362963 := bstep (se 1 (by rfl) ⟨272222, by rfl⟩ : syracuseStep 362963 = 544445) B544445
theorem B362993 : Blo 239816 362993 := bstep (se 2 (by rfl) ⟨136122, by rfl⟩ : syracuseStep 362993 = 272245) B272245
theorem B363011 : Blo 239816 363011 := bstep (se 1 (by rfl) ⟨272258, by rfl⟩ : syracuseStep 363011 = 544517) B544517
theorem B2066957 : Blo 239816 2066957 := bstep (se 3 (by rfl) ⟨387554, by rfl⟩ : syracuseStep 2066957 = 775109) B775109
theorem B363041 : Blo 239816 363041 := bstep (se 2 (by rfl) ⟨136140, by rfl⟩ : syracuseStep 363041 = 272281) B272281
theorem B363059 : Blo 239816 363059 := bstep (se 1 (by rfl) ⟨272294, by rfl⟩ : syracuseStep 363059 = 544589) B544589
theorem B363089 : Blo 239816 363089 := bstep (se 2 (by rfl) ⟨136158, by rfl⟩ : syracuseStep 363089 = 272317) B272317
theorem B363107 : Blo 239816 363107 := bstep (se 1 (by rfl) ⟨272330, by rfl⟩ : syracuseStep 363107 = 544661) B544661
theorem B1051235 : Blo 239816 1051235 := bstep (se 1 (by rfl) ⟨788426, by rfl⟩ : syracuseStep 1051235 = 1576853) B1576853
theorem B363137 : Blo 239816 363137 := bstep (se 2 (by rfl) ⟨136176, by rfl⟩ : syracuseStep 363137 = 272353) B272353
theorem B363155 : Blo 239816 363155 := bstep (se 1 (by rfl) ⟨272366, by rfl⟩ : syracuseStep 363155 = 544733) B544733
theorem B821933 : Blo 239816 821933 := bstep (se 3 (by rfl) ⟨154112, by rfl⟩ : syracuseStep 821933 = 308225) B308225
theorem B363185 : Blo 239816 363185 := bstep (se 2 (by rfl) ⟨136194, by rfl⟩ : syracuseStep 363185 = 272389) B272389
theorem B363203 : Blo 239816 363203 := bstep (se 1 (by rfl) ⟨272402, by rfl⟩ : syracuseStep 363203 = 544805) B544805
theorem B363233 : Blo 239816 363233 := bstep (se 2 (by rfl) ⟨136212, by rfl⟩ : syracuseStep 363233 = 272425) B272425
theorem B821987 : Blo 239816 821987 := bstep (se 1 (by rfl) ⟨616490, by rfl⟩ : syracuseStep 821987 = 1232981) B1232981
theorem B363251 : Blo 239816 363251 := bstep (se 1 (by rfl) ⟨272438, by rfl⟩ : syracuseStep 363251 = 544877) B544877
theorem B363281 : Blo 239816 363281 := bstep (se 2 (by rfl) ⟨136230, by rfl⟩ : syracuseStep 363281 = 272461) B272461
theorem B363299 : Blo 239816 363299 := bstep (se 1 (by rfl) ⟨272474, by rfl⟩ : syracuseStep 363299 = 544949) B544949
theorem B363329 : Blo 239816 363329 := bstep (se 2 (by rfl) ⟨136248, by rfl⟩ : syracuseStep 363329 = 272497) B272497
theorem B363347 : Blo 239816 363347 := bstep (se 1 (by rfl) ⟨272510, by rfl⟩ : syracuseStep 363347 = 545021) B545021
theorem B363377 : Blo 239816 363377 := bstep (se 2 (by rfl) ⟨136266, by rfl⟩ : syracuseStep 363377 = 272533) B272533
theorem B363395 : Blo 239816 363395 := bstep (se 1 (by rfl) ⟨272546, by rfl⟩ : syracuseStep 363395 = 545093) B545093
theorem B363425 : Blo 239816 363425 := bstep (se 2 (by rfl) ⟨136284, by rfl⟩ : syracuseStep 363425 = 272569) B272569
theorem B363443 : Blo 239816 363443 := bstep (se 1 (by rfl) ⟨272582, by rfl⟩ : syracuseStep 363443 = 545165) B545165
theorem B363473 : Blo 239816 363473 := bstep (se 2 (by rfl) ⟨136302, by rfl⟩ : syracuseStep 363473 = 272605) B272605
theorem B1838051 : Blo 239816 1838051 := bstep (se 1 (by rfl) ⟨1378538, by rfl⟩ : syracuseStep 1838051 = 2757077) B2757077
theorem B363491 : Blo 239816 363491 := bstep (se 1 (by rfl) ⟨272618, by rfl⟩ : syracuseStep 363491 = 545237) B545237
theorem B822257 : Blo 239816 822257 := bstep (se 2 (by rfl) ⟨308346, by rfl⟩ : syracuseStep 822257 = 616693) B616693
theorem B363521 : Blo 239816 363521 := bstep (se 2 (by rfl) ⟨136320, by rfl⟩ : syracuseStep 363521 = 272641) B272641
theorem B363539 : Blo 239816 363539 := bstep (se 1 (by rfl) ⟨272654, by rfl⟩ : syracuseStep 363539 = 545309) B545309
theorem B363569 : Blo 239816 363569 := bstep (se 2 (by rfl) ⟨136338, by rfl⟩ : syracuseStep 363569 = 272677) B272677
theorem B363587 : Blo 239816 363587 := bstep (se 1 (by rfl) ⟨272690, by rfl⟩ : syracuseStep 363587 = 545381) B545381
theorem B363617 : Blo 239816 363617 := bstep (se 2 (by rfl) ⟨136356, by rfl⟩ : syracuseStep 363617 = 272713) B272713
theorem B363635 : Blo 239816 363635 := bstep (se 1 (by rfl) ⟨272726, by rfl⟩ : syracuseStep 363635 = 545453) B545453
theorem B363665 : Blo 239816 363665 := bstep (se 2 (by rfl) ⟨136374, by rfl⟩ : syracuseStep 363665 = 272749) B272749
theorem B363683 : Blo 239816 363683 := bstep (se 1 (by rfl) ⟨272762, by rfl⟩ : syracuseStep 363683 = 545525) B545525
theorem B363713 : Blo 239816 363713 := bstep (se 2 (by rfl) ⟨136392, by rfl⟩ : syracuseStep 363713 = 272785) B272785
theorem B625859 : Blo 239816 625859 := bstep (se 1 (by rfl) ⟨469394, by rfl⟩ : syracuseStep 625859 = 938789) B938789
theorem B462019 : Blo 239816 462019 := bstep (se 1 (by rfl) ⟨346514, by rfl⟩ : syracuseStep 462019 = 693029) B693029
theorem B363731 : Blo 239816 363731 := bstep (se 1 (by rfl) ⟨272798, by rfl⟩ : syracuseStep 363731 = 545597) B545597
theorem B363761 : Blo 239816 363761 := bstep (se 2 (by rfl) ⟨136410, by rfl⟩ : syracuseStep 363761 = 272821) B272821
theorem B363779 : Blo 239816 363779 := bstep (se 1 (by rfl) ⟨272834, by rfl⟩ : syracuseStep 363779 = 545669) B545669
theorem B363809 : Blo 239816 363809 := bstep (se 2 (by rfl) ⟨136428, by rfl⟩ : syracuseStep 363809 = 272857) B272857
theorem B363827 : Blo 239816 363827 := bstep (se 1 (by rfl) ⟨272870, by rfl⟩ : syracuseStep 363827 = 545741) B545741
theorem B920909 : Blo 239816 920909 := bstep (se 3 (by rfl) ⟨172670, by rfl⟩ : syracuseStep 920909 = 345341) B345341
theorem B363857 : Blo 239816 363857 := bstep (se 2 (by rfl) ⟨136446, by rfl⟩ : syracuseStep 363857 = 272893) B272893
theorem B691537 : Blo 239816 691537 := bstep (se 2 (by rfl) ⟨259326, by rfl⟩ : syracuseStep 691537 = 518653) B518653
theorem B363875 : Blo 239816 363875 := bstep (se 1 (by rfl) ⟨272906, by rfl⟩ : syracuseStep 363875 = 545813) B545813
theorem B462179 : Blo 239816 462179 := bstep (se 1 (by rfl) ⟨346634, by rfl⟩ : syracuseStep 462179 = 693269) B693269
theorem B363905 : Blo 239816 363905 := bstep (se 2 (by rfl) ⟨136464, by rfl⟩ : syracuseStep 363905 = 272929) B272929
theorem B363923 : Blo 239816 363923 := bstep (se 1 (by rfl) ⟨272942, by rfl⟩ : syracuseStep 363923 = 545885) B545885
theorem B363953 : Blo 239816 363953 := bstep (se 2 (by rfl) ⟨136482, by rfl⟩ : syracuseStep 363953 = 272965) B272965
theorem B363971 : Blo 239816 363971 := bstep (se 1 (by rfl) ⟨272978, by rfl⟩ : syracuseStep 363971 = 545957) B545957
theorem B1314245 : Blo 239816 1314245 := bstep (se 4 (by rfl) ⟨123210, by rfl⟩ : syracuseStep 1314245 = 246421) B246421
theorem B364001 : Blo 239816 364001 := bstep (se 2 (by rfl) ⟨136500, by rfl⟩ : syracuseStep 364001 = 273001) B273001
theorem B1215971 : Blo 239816 1215971 := bstep (se 1 (by rfl) ⟨911978, by rfl⟩ : syracuseStep 1215971 = 1823957) B1823957
theorem B364019 : Blo 239816 364019 := bstep (se 1 (by rfl) ⟨273014, by rfl⟩ : syracuseStep 364019 = 546029) B546029
theorem B822797 : Blo 239816 822797 := bstep (se 3 (by rfl) ⟨154274, by rfl⟩ : syracuseStep 822797 = 308549) B308549
theorem B364049 : Blo 239816 364049 := bstep (se 2 (by rfl) ⟨136518, by rfl⟩ : syracuseStep 364049 = 273037) B273037
theorem B364067 : Blo 239816 364067 := bstep (se 1 (by rfl) ⟨273050, by rfl⟩ : syracuseStep 364067 = 546101) B546101
theorem B364097 : Blo 239816 364097 := bstep (se 2 (by rfl) ⟨136536, by rfl⟩ : syracuseStep 364097 = 273073) B273073
theorem B822851 : Blo 239816 822851 := bstep (se 1 (by rfl) ⟨617138, by rfl⟩ : syracuseStep 822851 = 1234277) B1234277
theorem B364115 : Blo 239816 364115 := bstep (se 1 (by rfl) ⟨273086, by rfl⟩ : syracuseStep 364115 = 546173) B546173
theorem B691811 : Blo 239816 691811 := bstep (se 1 (by rfl) ⟨518858, by rfl⟩ : syracuseStep 691811 = 1037717) B1037717
theorem B364145 : Blo 239816 364145 := bstep (se 2 (by rfl) ⟨136554, by rfl⟩ : syracuseStep 364145 = 273109) B273109
theorem B364163 : Blo 239816 364163 := bstep (se 1 (by rfl) ⟨273122, by rfl⟩ : syracuseStep 364163 = 546245) B546245
theorem B1773197 : Blo 239816 1773197 := bstep (se 3 (by rfl) ⟨332474, by rfl⟩ : syracuseStep 1773197 = 664949) B664949
theorem B364193 : Blo 239816 364193 := bstep (se 2 (by rfl) ⟨136572, by rfl⟩ : syracuseStep 364193 = 273145) B273145
theorem B364211 : Blo 239816 364211 := bstep (se 1 (by rfl) ⟨273158, by rfl⟩ : syracuseStep 364211 = 546317) B546317
theorem B364241 : Blo 239816 364241 := bstep (se 2 (by rfl) ⟨136590, by rfl⟩ : syracuseStep 364241 = 273181) B273181
theorem B364259 : Blo 239816 364259 := bstep (se 1 (by rfl) ⟨273194, by rfl⟩ : syracuseStep 364259 = 546389) B546389
theorem B364289 : Blo 239816 364289 := bstep (se 2 (by rfl) ⟨136608, by rfl⟩ : syracuseStep 364289 = 273217) B273217
theorem B364307 : Blo 239816 364307 := bstep (se 1 (by rfl) ⟨273230, by rfl⟩ : syracuseStep 364307 = 546461) B546461
theorem B692003 : Blo 239816 692003 := bstep (se 1 (by rfl) ⟨519002, by rfl⟩ : syracuseStep 692003 = 1038005) B1038005
theorem B364337 : Blo 239816 364337 := bstep (se 2 (by rfl) ⟨136626, by rfl⟩ : syracuseStep 364337 = 273253) B273253
theorem B364355 : Blo 239816 364355 := bstep (se 1 (by rfl) ⟨273266, by rfl⟩ : syracuseStep 364355 = 546533) B546533
theorem B364385 : Blo 239816 364385 := bstep (se 2 (by rfl) ⟨136644, by rfl⟩ : syracuseStep 364385 = 273289) B273289
theorem B364403 : Blo 239816 364403 := bstep (se 1 (by rfl) ⟨273302, by rfl⟩ : syracuseStep 364403 = 546605) B546605
theorem B364433 : Blo 239816 364433 := bstep (se 2 (by rfl) ⟨136662, by rfl⟩ : syracuseStep 364433 = 273325) B273325
theorem B364451 : Blo 239816 364451 := bstep (se 1 (by rfl) ⟨273338, by rfl⟩ : syracuseStep 364451 = 546677) B546677
theorem B364481 : Blo 239816 364481 := bstep (se 2 (by rfl) ⟨136680, by rfl⟩ : syracuseStep 364481 = 273361) B273361
theorem B364499 : Blo 239816 364499 := bstep (se 1 (by rfl) ⟨273374, by rfl⟩ : syracuseStep 364499 = 546749) B546749
theorem B364529 : Blo 239816 364529 := bstep (se 2 (by rfl) ⟨136698, by rfl⟩ : syracuseStep 364529 = 273397) B273397
theorem B364547 : Blo 239816 364547 := bstep (se 1 (by rfl) ⟨273410, by rfl⟩ : syracuseStep 364547 = 546821) B546821
theorem B364577 : Blo 239816 364577 := bstep (se 2 (by rfl) ⟨136716, by rfl⟩ : syracuseStep 364577 = 273433) B273433
theorem B364595 : Blo 239816 364595 := bstep (se 1 (by rfl) ⟨273446, by rfl⟩ : syracuseStep 364595 = 546893) B546893
theorem B364625 : Blo 239816 364625 := bstep (se 2 (by rfl) ⟨136734, by rfl⟩ : syracuseStep 364625 = 273469) B273469
theorem B364643 : Blo 239816 364643 := bstep (se 1 (by rfl) ⟨273482, by rfl⟩ : syracuseStep 364643 = 546965) B546965
theorem B364673 : Blo 239816 364673 := bstep (se 2 (by rfl) ⟨136752, by rfl⟩ : syracuseStep 364673 = 273505) B273505
theorem B364691 : Blo 239816 364691 := bstep (se 1 (by rfl) ⟨273518, by rfl⟩ : syracuseStep 364691 = 547037) B547037
theorem B364721 : Blo 239816 364721 := bstep (se 2 (by rfl) ⟨136770, by rfl⟩ : syracuseStep 364721 = 273541) B273541
theorem B364739 : Blo 239816 364739 := bstep (se 1 (by rfl) ⟨273554, by rfl⟩ : syracuseStep 364739 = 547109) B547109
theorem B364769 : Blo 239816 364769 := bstep (se 2 (by rfl) ⟨136788, by rfl⟩ : syracuseStep 364769 = 273577) B273577
theorem B364787 : Blo 239816 364787 := bstep (se 1 (by rfl) ⟨273590, by rfl⟩ : syracuseStep 364787 = 547181) B547181
theorem B1216781 : Blo 239816 1216781 := bstep (se 3 (by rfl) ⟨228146, by rfl⟩ : syracuseStep 1216781 = 456293) B456293
theorem B364817 : Blo 239816 364817 := bstep (se 2 (by rfl) ⟨136806, by rfl⟩ : syracuseStep 364817 = 273613) B273613
theorem B364835 : Blo 239816 364835 := bstep (se 1 (by rfl) ⟨273626, by rfl⟩ : syracuseStep 364835 = 547253) B547253
theorem B364865 : Blo 239816 364865 := bstep (se 2 (by rfl) ⟨136824, by rfl⟩ : syracuseStep 364865 = 273649) B273649
theorem B364883 : Blo 239816 364883 := bstep (se 1 (by rfl) ⟨273662, by rfl⟩ : syracuseStep 364883 = 547325) B547325
theorem B856433 : Blo 239816 856433 := bstep (se 2 (by rfl) ⟨321162, by rfl⟩ : syracuseStep 856433 = 642325) B642325
theorem B364913 : Blo 239816 364913 := bstep (se 2 (by rfl) ⟨136842, by rfl⟩ : syracuseStep 364913 = 273685) B273685
theorem B364931 : Blo 239816 364931 := bstep (se 1 (by rfl) ⟨273698, by rfl⟩ : syracuseStep 364931 = 547397) B547397
theorem B364961 : Blo 239816 364961 := bstep (se 2 (by rfl) ⟨136860, by rfl⟩ : syracuseStep 364961 = 273721) B273721
theorem B364979 : Blo 239816 364979 := bstep (se 1 (by rfl) ⟨273734, by rfl⟩ : syracuseStep 364979 = 547469) B547469
theorem B365009 : Blo 239816 365009 := bstep (se 2 (by rfl) ⟨136878, by rfl⟩ : syracuseStep 365009 = 273757) B273757
theorem B365027 : Blo 239816 365027 := bstep (se 1 (by rfl) ⟨273770, by rfl⟩ : syracuseStep 365027 = 547541) B547541
theorem B365057 : Blo 239816 365057 := bstep (se 2 (by rfl) ⟨136896, by rfl⟩ : syracuseStep 365057 = 273793) B273793
theorem B365075 : Blo 239816 365075 := bstep (se 1 (by rfl) ⟨273806, by rfl⟩ : syracuseStep 365075 = 547613) B547613
theorem B365105 : Blo 239816 365105 := bstep (se 2 (by rfl) ⟨136914, by rfl⟩ : syracuseStep 365105 = 273829) B273829
theorem B4133429 : Blo 239816 4133429 := bstep (se 5 (by rfl) ⟨193754, by rfl⟩ : syracuseStep 4133429 = 387509) B387509
theorem B365123 : Blo 239816 365123 := bstep (se 1 (by rfl) ⟨273842, by rfl⟩ : syracuseStep 365123 = 547685) B547685
theorem B692813 : Blo 239816 692813 := bstep (se 3 (by rfl) ⟨129902, by rfl⟩ : syracuseStep 692813 = 259805) B259805
theorem B365153 : Blo 239816 365153 := bstep (se 2 (by rfl) ⟨136932, by rfl⟩ : syracuseStep 365153 = 273865) B273865
theorem B365171 : Blo 239816 365171 := bstep (se 1 (by rfl) ⟨273878, by rfl⟩ : syracuseStep 365171 = 547757) B547757
theorem B365201 : Blo 239816 365201 := bstep (se 2 (by rfl) ⟨136950, by rfl⟩ : syracuseStep 365201 = 273901) B273901
theorem B365219 : Blo 239816 365219 := bstep (se 1 (by rfl) ⟨273914, by rfl⟩ : syracuseStep 365219 = 547829) B547829
theorem B365249 : Blo 239816 365249 := bstep (se 2 (by rfl) ⟨136968, by rfl⟩ : syracuseStep 365249 = 273937) B273937
theorem B365267 : Blo 239816 365267 := bstep (se 1 (by rfl) ⟨273950, by rfl⟩ : syracuseStep 365267 = 547901) B547901
theorem B365297 : Blo 239816 365297 := bstep (se 2 (by rfl) ⟨136986, by rfl⟩ : syracuseStep 365297 = 273973) B273973
theorem B692995 : Blo 239816 692995 := bstep (se 1 (by rfl) ⟨519746, by rfl⟩ : syracuseStep 692995 = 1039493) B1039493
theorem B365315 : Blo 239816 365315 := bstep (se 1 (by rfl) ⟨273986, by rfl⟩ : syracuseStep 365315 = 547973) B547973
theorem B365345 : Blo 239816 365345 := bstep (se 2 (by rfl) ⟨137004, by rfl⟩ : syracuseStep 365345 = 274009) B274009
theorem B365363 : Blo 239816 365363 := bstep (se 1 (by rfl) ⟨274022, by rfl⟩ : syracuseStep 365363 = 548045) B548045
theorem B365393 : Blo 239816 365393 := bstep (se 2 (by rfl) ⟨137022, by rfl⟩ : syracuseStep 365393 = 274045) B274045
theorem B365411 : Blo 239816 365411 := bstep (se 1 (by rfl) ⟨274058, by rfl⟩ : syracuseStep 365411 = 548117) B548117
theorem B365441 : Blo 239816 365441 := bstep (se 2 (by rfl) ⟨137040, by rfl⟩ : syracuseStep 365441 = 274081) B274081
theorem B365459 : Blo 239816 365459 := bstep (se 1 (by rfl) ⟨274094, by rfl⟩ : syracuseStep 365459 = 548189) B548189
theorem B365489 : Blo 239816 365489 := bstep (se 2 (by rfl) ⟨137058, by rfl⟩ : syracuseStep 365489 = 274117) B274117
theorem B365491 : Blo 239816 365491 := bstep (se 1 (by rfl) ⟨274118, by rfl⟩ : syracuseStep 365491 = 548237) B548237
theorem B365507 : Blo 239816 365507 := bstep (se 1 (by rfl) ⟨274130, by rfl⟩ : syracuseStep 365507 = 548261) B548261
theorem B365537 : Blo 239816 365537 := bstep (se 2 (by rfl) ⟨137076, by rfl⟩ : syracuseStep 365537 = 274153) B274153
theorem B365555 : Blo 239816 365555 := bstep (se 1 (by rfl) ⟨274166, by rfl⟩ : syracuseStep 365555 = 548333) B548333
theorem B365585 : Blo 239816 365585 := bstep (se 2 (by rfl) ⟨137094, by rfl⟩ : syracuseStep 365585 = 274189) B274189
theorem B365603 : Blo 239816 365603 := bstep (se 1 (by rfl) ⟨274202, by rfl⟩ : syracuseStep 365603 = 548405) B548405
theorem B365633 : Blo 239816 365633 := bstep (se 2 (by rfl) ⟨137112, by rfl⟩ : syracuseStep 365633 = 274225) B274225
theorem B365651 : Blo 239816 365651 := bstep (se 1 (by rfl) ⟨274238, by rfl⟩ : syracuseStep 365651 = 548477) B548477
theorem B365681 : Blo 239816 365681 := bstep (se 2 (by rfl) ⟨137130, by rfl⟩ : syracuseStep 365681 = 274261) B274261
theorem B365699 : Blo 239816 365699 := bstep (se 1 (by rfl) ⟨274274, by rfl⟩ : syracuseStep 365699 = 548549) B548549
theorem B693485 : Blo 239816 693485 := bstep (se 3 (by rfl) ⟨130028, by rfl⟩ : syracuseStep 693485 = 260057) B260057
theorem B1381637 : Blo 239816 1381637 := bstep (se 4 (by rfl) ⟨129528, by rfl⟩ : syracuseStep 1381637 = 259057) B259057
theorem B12719501 : Blo 239816 12719501 := bstep (se 3 (by rfl) ⟨2384906, by rfl⟩ : syracuseStep 12719501 = 4769813) B4769813
theorem B923021 : Blo 239816 923021 := bstep (se 3 (by rfl) ⟨173066, by rfl⟩ : syracuseStep 923021 = 346133) B346133
theorem B366275 : Blo 239816 366275 := bstep (se 1 (by rfl) ⟨274706, by rfl⟩ : syracuseStep 366275 = 549413) B549413
theorem B1382093 : Blo 239816 1382093 := bstep (se 3 (by rfl) ⟨259142, by rfl⟩ : syracuseStep 1382093 = 518285) B518285
theorem B1153187 : Blo 239816 1153187 := bstep (se 1 (by rfl) ⟨864890, by rfl⟩ : syracuseStep 1153187 = 1729781) B1729781
theorem B923825 : Blo 239816 923825 := bstep (se 2 (by rfl) ⟨346434, by rfl⟩ : syracuseStep 923825 = 692869) B692869
theorem B825869 : Blo 239816 825869 := bstep (se 3 (by rfl) ⟨154850, by rfl⟩ : syracuseStep 825869 = 309701) B309701
theorem B367345 : Blo 239816 367345 := bstep (se 2 (by rfl) ⟨137754, by rfl⟩ : syracuseStep 367345 = 275509) B275509
theorem B989965 : Blo 239816 989965 := bstep (se 3 (by rfl) ⟨185618, by rfl⟩ : syracuseStep 989965 = 371237) B371237
theorem B924493 : Blo 239816 924493 := bstep (se 3 (by rfl) ⟨173342, by rfl⟩ : syracuseStep 924493 = 346685) B346685
theorem B695341 : Blo 239816 695341 := bstep (se 3 (by rfl) ⟨130376, by rfl⟩ : syracuseStep 695341 = 260753) B260753
theorem B1219697 : Blo 239816 1219697 := bstep (se 2 (by rfl) ⟨457386, by rfl⟩ : syracuseStep 1219697 = 914773) B914773
theorem B1154531 : Blo 239816 1154531 := bstep (se 1 (by rfl) ⟨865898, by rfl⟩ : syracuseStep 1154531 = 1731797) B1731797
theorem B269923 : Blo 239816 269923 := bstep (se 1 (by rfl) ⟨202442, by rfl⟩ : syracuseStep 269923 = 404885) B404885
theorem B925283 : Blo 239816 925283 := bstep (se 1 (by rfl) ⟨693962, by rfl⟩ : syracuseStep 925283 = 1387925) B1387925
theorem B532163 : Blo 239816 532163 := bstep (se 1 (by rfl) ⟨399122, by rfl⟩ : syracuseStep 532163 = 798245) B798245
theorem B1187569 : Blo 239816 1187569 := bstep (se 2 (by rfl) ⟨445338, by rfl⟩ : syracuseStep 1187569 = 890677) B890677
theorem B270067 : Blo 239816 270067 := bstep (se 1 (by rfl) ⟨202550, by rfl⟩ : syracuseStep 270067 = 405101) B405101
theorem B368513 : Blo 239816 368513 := bstep (se 2 (by rfl) ⟨138192, by rfl⟩ : syracuseStep 368513 = 276385) B276385
theorem B270211 : Blo 239816 270211 := bstep (se 1 (by rfl) ⟨202658, by rfl⟩ : syracuseStep 270211 = 405317) B405317
theorem B827405 : Blo 239816 827405 := bstep (se 3 (by rfl) ⟨155138, by rfl⟩ : syracuseStep 827405 = 310277) B310277
theorem B270355 : Blo 239816 270355 := bstep (se 1 (by rfl) ⟨202766, by rfl⟩ : syracuseStep 270355 = 405533) B405533
theorem B270499 : Blo 239816 270499 := bstep (se 1 (by rfl) ⟨202874, by rfl⟩ : syracuseStep 270499 = 405749) B405749
theorem B1843397 : Blo 239816 1843397 := bstep (se 4 (by rfl) ⟨172818, by rfl⟩ : syracuseStep 1843397 = 345637) B345637
theorem B270643 : Blo 239816 270643 := bstep (se 1 (by rfl) ⟨202982, by rfl⟩ : syracuseStep 270643 = 405965) B405965
theorem B729425 : Blo 239816 729425 := bstep (se 2 (by rfl) ⟨273534, by rfl⟩ : syracuseStep 729425 = 547069) B547069
theorem B270787 : Blo 239816 270787 := bstep (se 1 (by rfl) ⟨203090, by rfl⟩ : syracuseStep 270787 = 406181) B406181
theorem B1221155 : Blo 239816 1221155 := bstep (se 1 (by rfl) ⟨915866, by rfl⟩ : syracuseStep 1221155 = 1831733) B1831733
theorem B1385009 : Blo 239816 1385009 := bstep (se 2 (by rfl) ⟨519378, by rfl⟩ : syracuseStep 1385009 = 1038757) B1038757
theorem B270931 : Blo 239816 270931 := bstep (se 1 (by rfl) ⟨203198, by rfl⟩ : syracuseStep 270931 = 406397) B406397
theorem B271075 : Blo 239816 271075 := bstep (se 1 (by rfl) ⟨203306, by rfl⟩ : syracuseStep 271075 = 406613) B406613
theorem B303907 : Blo 239816 303907 := bstep (se 1 (by rfl) ⟨227930, by rfl⟩ : syracuseStep 303907 = 455861) B455861
theorem B271219 : Blo 239816 271219 := bstep (se 1 (by rfl) ⟨203414, by rfl⟩ : syracuseStep 271219 = 406829) B406829
theorem B304003 : Blo 239816 304003 := bstep (se 1 (by rfl) ⟨228002, by rfl⟩ : syracuseStep 304003 = 456005) B456005
theorem B730019 : Blo 239816 730019 := bstep (se 1 (by rfl) ⟨547514, by rfl⟩ : syracuseStep 730019 = 1095029) B1095029
theorem B271363 : Blo 239816 271363 := bstep (se 1 (by rfl) ⟨203522, by rfl⟩ : syracuseStep 271363 = 407045) B407045
theorem B271507 : Blo 239816 271507 := bstep (se 1 (by rfl) ⟨203630, by rfl⟩ : syracuseStep 271507 = 407261) B407261
theorem B1549475 : Blo 239816 1549475 := bstep (se 1 (by rfl) ⟨1162106, by rfl⟩ : syracuseStep 1549475 = 2324213) B2324213
theorem B1156301 : Blo 239816 1156301 := bstep (se 3 (by rfl) ⟨216806, by rfl⟩ : syracuseStep 1156301 = 433613) B433613
theorem B1025293 : Blo 239816 1025293 := bstep (se 3 (by rfl) ⟨192242, by rfl⟩ : syracuseStep 1025293 = 384485) B384485
theorem B369937 : Blo 239816 369937 := bstep (se 2 (by rfl) ⟨138726, by rfl⟩ : syracuseStep 369937 = 277453) B277453
theorem B271651 : Blo 239816 271651 := bstep (se 1 (by rfl) ⟨203738, by rfl⟩ : syracuseStep 271651 = 407477) B407477
theorem B1221965 : Blo 239816 1221965 := bstep (se 3 (by rfl) ⟨229118, by rfl⟩ : syracuseStep 1221965 = 458237) B458237
theorem B304499 : Blo 239816 304499 := bstep (se 1 (by rfl) ⟨228374, by rfl⟩ : syracuseStep 304499 = 456749) B456749
theorem B271795 : Blo 239816 271795 := bstep (se 1 (by rfl) ⟨203846, by rfl⟩ : syracuseStep 271795 = 407693) B407693
theorem B730691 : Blo 239816 730691 := bstep (se 1 (by rfl) ⟨548018, by rfl⟩ : syracuseStep 730691 = 1096037) B1096037
theorem B271939 : Blo 239816 271939 := bstep (se 1 (by rfl) ⟨203954, by rfl⟩ : syracuseStep 271939 = 407909) B407909
theorem B1025635 : Blo 239816 1025635 := bstep (se 1 (by rfl) ⟨769226, by rfl⟩ : syracuseStep 1025635 = 1538453) B1538453
theorem B4368013 : Blo 239816 4368013 := bstep (se 3 (by rfl) ⟨819002, by rfl⟩ : syracuseStep 4368013 = 1638005) B1638005
theorem B272083 : Blo 239816 272083 := bstep (se 1 (by rfl) ⟨204062, by rfl⟩ : syracuseStep 272083 = 408125) B408125
theorem B272227 : Blo 239816 272227 := bstep (se 1 (by rfl) ⟨204170, by rfl⟩ : syracuseStep 272227 = 408341) B408341
theorem B1386467 : Blo 239816 1386467 := bstep (se 1 (by rfl) ⟨1039850, by rfl⟩ : syracuseStep 1386467 = 2079701) B2079701
theorem B272371 : Blo 239816 272371 := bstep (se 1 (by rfl) ⟨204278, by rfl⟩ : syracuseStep 272371 = 408557) B408557
theorem B305203 : Blo 239816 305203 := bstep (se 1 (by rfl) ⟨228902, by rfl⟩ : syracuseStep 305203 = 457805) B457805
theorem B272515 : Blo 239816 272515 := bstep (se 1 (by rfl) ⟨204386, by rfl⟩ : syracuseStep 272515 = 408773) B408773
theorem B305299 : Blo 239816 305299 := bstep (se 1 (by rfl) ⟨228974, by rfl⟩ : syracuseStep 305299 = 457949) B457949
theorem B2009285 : Blo 239816 2009285 := bstep (se 4 (by rfl) ⟨188370, by rfl⟩ : syracuseStep 2009285 = 376741) B376741
theorem B239827 : Blo 239816 239827 := bstep (se 1 (by rfl) ⟨179870, by rfl⟩ : syracuseStep 239827 = 359741) B359741
theorem B239843 : Blo 239816 239843 := bstep (se 1 (by rfl) ⟨179882, by rfl⟩ : syracuseStep 239843 = 359765) B359765
theorem B1976561 : Blo 239816 1976561 := bstep (se 2 (by rfl) ⟨741210, by rfl⟩ : syracuseStep 1976561 = 1482421) B1482421
theorem B239859 : Blo 239816 239859 := bstep (se 1 (by rfl) ⟨179894, by rfl⟩ : syracuseStep 239859 = 359789) B359789
theorem B239875 : Blo 239816 239875 := bstep (se 1 (by rfl) ⟨179906, by rfl⟩ : syracuseStep 239875 = 359813) B359813
theorem B239891 : Blo 239816 239891 := bstep (se 1 (by rfl) ⟨179918, by rfl⟩ : syracuseStep 239891 = 359837) B359837
theorem B272659 : Blo 239816 272659 := bstep (se 1 (by rfl) ⟨204494, by rfl⟩ : syracuseStep 272659 = 408989) B408989
theorem B239907 : Blo 239816 239907 := bstep (se 1 (by rfl) ⟨179930, by rfl⟩ : syracuseStep 239907 = 359861) B359861
theorem B239923 : Blo 239816 239923 := bstep (se 1 (by rfl) ⟨179942, by rfl⟩ : syracuseStep 239923 = 359885) B359885
theorem B239939 : Blo 239816 239939 := bstep (se 1 (by rfl) ⟨179954, by rfl⟩ : syracuseStep 239939 = 359909) B359909
theorem B239955 : Blo 239816 239955 := bstep (se 1 (by rfl) ⟨179966, by rfl⟩ : syracuseStep 239955 = 359933) B359933
theorem B239971 : Blo 239816 239971 := bstep (se 1 (by rfl) ⟨179978, by rfl⟩ : syracuseStep 239971 = 359957) B359957
theorem B239987 : Blo 239816 239987 := bstep (se 1 (by rfl) ⟨179990, by rfl⟩ : syracuseStep 239987 = 359981) B359981
theorem B240003 : Blo 239816 240003 := bstep (se 1 (by rfl) ⟨180002, by rfl⟩ : syracuseStep 240003 = 360005) B360005
theorem B240019 : Blo 239816 240019 := bstep (se 1 (by rfl) ⟨180014, by rfl⟩ : syracuseStep 240019 = 360029) B360029
theorem B240035 : Blo 239816 240035 := bstep (se 1 (by rfl) ⟨180026, by rfl⟩ : syracuseStep 240035 = 360053) B360053
theorem B272803 : Blo 239816 272803 := bstep (se 1 (by rfl) ⟨204602, by rfl⟩ : syracuseStep 272803 = 409205) B409205
theorem B240051 : Blo 239816 240051 := bstep (se 1 (by rfl) ⟨180038, by rfl⟩ : syracuseStep 240051 = 360077) B360077
theorem B240067 : Blo 239816 240067 := bstep (se 1 (by rfl) ⟨180050, by rfl⟩ : syracuseStep 240067 = 360101) B360101
theorem B240083 : Blo 239816 240083 := bstep (se 1 (by rfl) ⟨180062, by rfl⟩ : syracuseStep 240083 = 360125) B360125
theorem B240099 : Blo 239816 240099 := bstep (se 1 (by rfl) ⟨180074, by rfl⟩ : syracuseStep 240099 = 360149) B360149
theorem B240115 : Blo 239816 240115 := bstep (se 1 (by rfl) ⟨180086, by rfl⟩ : syracuseStep 240115 = 360173) B360173
theorem B240131 : Blo 239816 240131 := bstep (se 1 (by rfl) ⟨180098, by rfl⟩ : syracuseStep 240131 = 360197) B360197
theorem B240147 : Blo 239816 240147 := bstep (se 1 (by rfl) ⟨180110, by rfl⟩ : syracuseStep 240147 = 360221) B360221
theorem B240163 : Blo 239816 240163 := bstep (se 1 (by rfl) ⟨180122, by rfl⟩ : syracuseStep 240163 = 360245) B360245
theorem B240179 : Blo 239816 240179 := bstep (se 1 (by rfl) ⟨180134, by rfl⟩ : syracuseStep 240179 = 360269) B360269
theorem B272947 : Blo 239816 272947 := bstep (se 1 (by rfl) ⟨204710, by rfl⟩ : syracuseStep 272947 = 409421) B409421
theorem B240195 : Blo 239816 240195 := bstep (se 1 (by rfl) ⟨180146, by rfl⟩ : syracuseStep 240195 = 360293) B360293
theorem B240211 : Blo 239816 240211 := bstep (se 1 (by rfl) ⟨180158, by rfl⟩ : syracuseStep 240211 = 360317) B360317
theorem B240227 : Blo 239816 240227 := bstep (se 1 (by rfl) ⟨180170, by rfl⟩ : syracuseStep 240227 = 360341) B360341
theorem B3943025 : Blo 239816 3943025 := bstep (se 2 (by rfl) ⟨1478634, by rfl⟩ : syracuseStep 3943025 = 2957269) B2957269
theorem B240243 : Blo 239816 240243 := bstep (se 1 (by rfl) ⟨180182, by rfl⟩ : syracuseStep 240243 = 360365) B360365
theorem B240259 : Blo 239816 240259 := bstep (se 1 (by rfl) ⟨180194, by rfl⟩ : syracuseStep 240259 = 360389) B360389
theorem B305795 : Blo 239816 305795 := bstep (se 1 (by rfl) ⟨229346, by rfl⟩ : syracuseStep 305795 = 458693) B458693
theorem B240275 : Blo 239816 240275 := bstep (se 1 (by rfl) ⟨180206, by rfl⟩ : syracuseStep 240275 = 360413) B360413
theorem B240291 : Blo 239816 240291 := bstep (se 1 (by rfl) ⟨180218, by rfl⟩ : syracuseStep 240291 = 360437) B360437
theorem B240307 : Blo 239816 240307 := bstep (se 1 (by rfl) ⟨180230, by rfl⟩ : syracuseStep 240307 = 360461) B360461
theorem B240323 : Blo 239816 240323 := bstep (se 1 (by rfl) ⟨180242, by rfl⟩ : syracuseStep 240323 = 360485) B360485
theorem B273091 : Blo 239816 273091 := bstep (se 1 (by rfl) ⟨204818, by rfl⟩ : syracuseStep 273091 = 409637) B409637
theorem B731857 : Blo 239816 731857 := bstep (se 2 (by rfl) ⟨274446, by rfl⟩ : syracuseStep 731857 = 548893) B548893
theorem B240339 : Blo 239816 240339 := bstep (se 1 (by rfl) ⟨180254, by rfl⟩ : syracuseStep 240339 = 360509) B360509
theorem B240355 : Blo 239816 240355 := bstep (se 1 (by rfl) ⟨180266, by rfl⟩ : syracuseStep 240355 = 360533) B360533
theorem B240371 : Blo 239816 240371 := bstep (se 1 (by rfl) ⟨180278, by rfl⟩ : syracuseStep 240371 = 360557) B360557
theorem B240387 : Blo 239816 240387 := bstep (se 1 (by rfl) ⟨180290, by rfl⟩ : syracuseStep 240387 = 360581) B360581
theorem B240403 : Blo 239816 240403 := bstep (se 1 (by rfl) ⟨180302, by rfl⟩ : syracuseStep 240403 = 360605) B360605
theorem B240419 : Blo 239816 240419 := bstep (se 1 (by rfl) ⟨180314, by rfl⟩ : syracuseStep 240419 = 360629) B360629
theorem B240435 : Blo 239816 240435 := bstep (se 1 (by rfl) ⟨180326, by rfl⟩ : syracuseStep 240435 = 360653) B360653
theorem B240451 : Blo 239816 240451 := bstep (se 1 (by rfl) ⟨180338, by rfl⟩ : syracuseStep 240451 = 360677) B360677
theorem B240467 : Blo 239816 240467 := bstep (se 1 (by rfl) ⟨180350, by rfl⟩ : syracuseStep 240467 = 360701) B360701
theorem B273235 : Blo 239816 273235 := bstep (se 1 (by rfl) ⟨204926, by rfl⟩ : syracuseStep 273235 = 409853) B409853
theorem B240483 : Blo 239816 240483 := bstep (se 1 (by rfl) ⟨180362, by rfl⟩ : syracuseStep 240483 = 360725) B360725
theorem B240499 : Blo 239816 240499 := bstep (se 1 (by rfl) ⟨180374, by rfl⟩ : syracuseStep 240499 = 360749) B360749
theorem B240515 : Blo 239816 240515 := bstep (se 1 (by rfl) ⟨180386, by rfl⟩ : syracuseStep 240515 = 360773) B360773
theorem B240531 : Blo 239816 240531 := bstep (se 1 (by rfl) ⟨180398, by rfl⟩ : syracuseStep 240531 = 360797) B360797
theorem B240547 : Blo 239816 240547 := bstep (se 1 (by rfl) ⟨180410, by rfl⟩ : syracuseStep 240547 = 360821) B360821
theorem B699313 : Blo 239816 699313 := bstep (se 2 (by rfl) ⟨262242, by rfl⟩ : syracuseStep 699313 = 524485) B524485
theorem B240563 : Blo 239816 240563 := bstep (se 1 (by rfl) ⟨180422, by rfl⟩ : syracuseStep 240563 = 360845) B360845
theorem B240579 : Blo 239816 240579 := bstep (se 1 (by rfl) ⟨180434, by rfl⟩ : syracuseStep 240579 = 360869) B360869
theorem B1387469 : Blo 239816 1387469 := bstep (se 3 (by rfl) ⟨260150, by rfl⟩ : syracuseStep 1387469 = 520301) B520301
theorem B240595 : Blo 239816 240595 := bstep (se 1 (by rfl) ⟨180446, by rfl⟩ : syracuseStep 240595 = 360893) B360893
theorem B240611 : Blo 239816 240611 := bstep (se 1 (by rfl) ⟨180458, by rfl⟩ : syracuseStep 240611 = 360917) B360917
theorem B273379 : Blo 239816 273379 := bstep (se 1 (by rfl) ⟨205034, by rfl⟩ : syracuseStep 273379 = 410069) B410069
theorem B240627 : Blo 239816 240627 := bstep (se 1 (by rfl) ⟨180470, by rfl⟩ : syracuseStep 240627 = 360941) B360941
theorem B240643 : Blo 239816 240643 := bstep (se 1 (by rfl) ⟨180482, by rfl⟩ : syracuseStep 240643 = 360965) B360965
theorem B240659 : Blo 239816 240659 := bstep (se 1 (by rfl) ⟨180494, by rfl⟩ : syracuseStep 240659 = 360989) B360989
theorem B240675 : Blo 239816 240675 := bstep (se 1 (by rfl) ⟨180506, by rfl⟩ : syracuseStep 240675 = 361013) B361013
theorem B240691 : Blo 239816 240691 := bstep (se 1 (by rfl) ⟨180518, by rfl⟩ : syracuseStep 240691 = 361037) B361037
theorem B240707 : Blo 239816 240707 := bstep (se 1 (by rfl) ⟨180530, by rfl⟩ : syracuseStep 240707 = 361061) B361061
theorem B240723 : Blo 239816 240723 := bstep (se 1 (by rfl) ⟨180542, by rfl⟩ : syracuseStep 240723 = 361085) B361085
theorem B240739 : Blo 239816 240739 := bstep (se 1 (by rfl) ⟨180554, by rfl⟩ : syracuseStep 240739 = 361109) B361109
theorem B1551473 : Blo 239816 1551473 := bstep (se 2 (by rfl) ⟨581802, by rfl⟩ : syracuseStep 1551473 = 1163605) B1163605
theorem B240755 : Blo 239816 240755 := bstep (se 1 (by rfl) ⟨180566, by rfl⟩ : syracuseStep 240755 = 361133) B361133
theorem B273523 : Blo 239816 273523 := bstep (se 1 (by rfl) ⟨205142, by rfl⟩ : syracuseStep 273523 = 410285) B410285
theorem B240771 : Blo 239816 240771 := bstep (se 1 (by rfl) ⟨180578, by rfl⟩ : syracuseStep 240771 = 361157) B361157
theorem B240787 : Blo 239816 240787 := bstep (se 1 (by rfl) ⟨180590, by rfl⟩ : syracuseStep 240787 = 361181) B361181
theorem B240803 : Blo 239816 240803 := bstep (se 1 (by rfl) ⟨180602, by rfl⟩ : syracuseStep 240803 = 361205) B361205
theorem B240819 : Blo 239816 240819 := bstep (se 1 (by rfl) ⟨180614, by rfl⟩ : syracuseStep 240819 = 361229) B361229
theorem B240835 : Blo 239816 240835 := bstep (se 1 (by rfl) ⟨180626, by rfl⟩ : syracuseStep 240835 = 361253) B361253
theorem B240851 : Blo 239816 240851 := bstep (se 1 (by rfl) ⟨180638, by rfl⟩ : syracuseStep 240851 = 361277) B361277
theorem B240867 : Blo 239816 240867 := bstep (se 1 (by rfl) ⟨180650, by rfl⟩ : syracuseStep 240867 = 361301) B361301
theorem B404723 : Blo 239816 404723 := bstep (se 1 (by rfl) ⟨303542, by rfl⟩ : syracuseStep 404723 = 607085) B607085
theorem B240883 : Blo 239816 240883 := bstep (se 1 (by rfl) ⟨180662, by rfl⟩ : syracuseStep 240883 = 361325) B361325
theorem B240899 : Blo 239816 240899 := bstep (se 1 (by rfl) ⟨180674, by rfl⟩ : syracuseStep 240899 = 361349) B361349
theorem B273667 : Blo 239816 273667 := bstep (se 1 (by rfl) ⟨205250, by rfl⟩ : syracuseStep 273667 = 410501) B410501
theorem B240915 : Blo 239816 240915 := bstep (se 1 (by rfl) ⟨180686, by rfl⟩ : syracuseStep 240915 = 361373) B361373
theorem B240931 : Blo 239816 240931 := bstep (se 1 (by rfl) ⟨180698, by rfl⟩ : syracuseStep 240931 = 361397) B361397
theorem B240947 : Blo 239816 240947 := bstep (se 1 (by rfl) ⟨180710, by rfl⟩ : syracuseStep 240947 = 361421) B361421
theorem B240963 : Blo 239816 240963 := bstep (se 1 (by rfl) ⟨180722, by rfl⟩ : syracuseStep 240963 = 361445) B361445
theorem B306499 : Blo 239816 306499 := bstep (se 1 (by rfl) ⟨229874, by rfl⟩ : syracuseStep 306499 = 459749) B459749
theorem B240979 : Blo 239816 240979 := bstep (se 1 (by rfl) ⟨180734, by rfl⟩ : syracuseStep 240979 = 361469) B361469
theorem B240995 : Blo 239816 240995 := bstep (se 1 (by rfl) ⟨180746, by rfl⟩ : syracuseStep 240995 = 361493) B361493
theorem B404851 : Blo 239816 404851 := bstep (se 1 (by rfl) ⟨303638, by rfl⟩ : syracuseStep 404851 = 607277) B607277
theorem B241011 : Blo 239816 241011 := bstep (se 1 (by rfl) ⟨180758, by rfl⟩ : syracuseStep 241011 = 361517) B361517
theorem B241027 : Blo 239816 241027 := bstep (se 1 (by rfl) ⟨180770, by rfl⟩ : syracuseStep 241027 = 361541) B361541
theorem B241043 : Blo 239816 241043 := bstep (se 1 (by rfl) ⟨180782, by rfl⟩ : syracuseStep 241043 = 361565) B361565
theorem B273811 : Blo 239816 273811 := bstep (se 1 (by rfl) ⟨205358, by rfl⟩ : syracuseStep 273811 = 410717) B410717
theorem B241059 : Blo 239816 241059 := bstep (se 1 (by rfl) ⟨180794, by rfl⟩ : syracuseStep 241059 = 361589) B361589
theorem B306595 : Blo 239816 306595 := bstep (se 1 (by rfl) ⟨229946, by rfl⟩ : syracuseStep 306595 = 459893) B459893
theorem B241075 : Blo 239816 241075 := bstep (se 1 (by rfl) ⟨180806, by rfl⟩ : syracuseStep 241075 = 361613) B361613
theorem B241091 : Blo 239816 241091 := bstep (se 1 (by rfl) ⟨180818, by rfl⟩ : syracuseStep 241091 = 361637) B361637
theorem B241107 : Blo 239816 241107 := bstep (se 1 (by rfl) ⟨180830, by rfl⟩ : syracuseStep 241107 = 361661) B361661
theorem B241123 : Blo 239816 241123 := bstep (se 1 (by rfl) ⟨180842, by rfl⟩ : syracuseStep 241123 = 361685) B361685
theorem B241139 : Blo 239816 241139 := bstep (se 1 (by rfl) ⟨180854, by rfl⟩ : syracuseStep 241139 = 361709) B361709
theorem B404993 : Blo 239816 404993 := bstep (se 2 (by rfl) ⟨151872, by rfl⟩ : syracuseStep 404993 = 303745) B303745
theorem B241155 : Blo 239816 241155 := bstep (se 1 (by rfl) ⟨180866, by rfl⟩ : syracuseStep 241155 = 361733) B361733
theorem B241171 : Blo 239816 241171 := bstep (se 1 (by rfl) ⟨180878, by rfl⟩ : syracuseStep 241171 = 361757) B361757
theorem B241187 : Blo 239816 241187 := bstep (se 1 (by rfl) ⟨180890, by rfl⟩ : syracuseStep 241187 = 361781) B361781
theorem B273955 : Blo 239816 273955 := bstep (se 1 (by rfl) ⟨205466, by rfl⟩ : syracuseStep 273955 = 410933) B410933
theorem B241203 : Blo 239816 241203 := bstep (se 1 (by rfl) ⟨180902, by rfl⟩ : syracuseStep 241203 = 361805) B361805
theorem B241219 : Blo 239816 241219 := bstep (se 1 (by rfl) ⟨180914, by rfl⟩ : syracuseStep 241219 = 361829) B361829
theorem B831043 : Blo 239816 831043 := bstep (se 1 (by rfl) ⟨623282, by rfl⟩ : syracuseStep 831043 = 1246565) B1246565
theorem B241235 : Blo 239816 241235 := bstep (se 1 (by rfl) ⟨180926, by rfl⟩ : syracuseStep 241235 = 361853) B361853
theorem B241251 : Blo 239816 241251 := bstep (se 1 (by rfl) ⟨180938, by rfl⟩ : syracuseStep 241251 = 361877) B361877
theorem B470641 : Blo 239816 470641 := bstep (se 2 (by rfl) ⟨176490, by rfl⟩ : syracuseStep 470641 = 352981) B352981
theorem B241267 : Blo 239816 241267 := bstep (se 1 (by rfl) ⟨180950, by rfl⟩ : syracuseStep 241267 = 361901) B361901
theorem B405121 : Blo 239816 405121 := bstep (se 2 (by rfl) ⟨151920, by rfl⟩ : syracuseStep 405121 = 303841) B303841
theorem B241283 : Blo 239816 241283 := bstep (se 1 (by rfl) ⟨180962, by rfl⟩ : syracuseStep 241283 = 361925) B361925
theorem B241299 : Blo 239816 241299 := bstep (se 1 (by rfl) ⟨180974, by rfl⟩ : syracuseStep 241299 = 361949) B361949
theorem B405155 : Blo 239816 405155 := bstep (se 1 (by rfl) ⟨303866, by rfl⟩ : syracuseStep 405155 = 607733) B607733
theorem B241315 : Blo 239816 241315 := bstep (se 1 (by rfl) ⟨180986, by rfl⟩ : syracuseStep 241315 = 361973) B361973
theorem B241331 : Blo 239816 241331 := bstep (se 1 (by rfl) ⟨180998, by rfl⟩ : syracuseStep 241331 = 361997) B361997
theorem B274099 : Blo 239816 274099 := bstep (se 1 (by rfl) ⟨205574, by rfl⟩ : syracuseStep 274099 = 411149) B411149
theorem B241347 : Blo 239816 241347 := bstep (se 1 (by rfl) ⟨181010, by rfl⟩ : syracuseStep 241347 = 362021) B362021
theorem B241363 : Blo 239816 241363 := bstep (se 1 (by rfl) ⟨181022, by rfl⟩ : syracuseStep 241363 = 362045) B362045
theorem B241379 : Blo 239816 241379 := bstep (se 1 (by rfl) ⟨181034, by rfl⟩ : syracuseStep 241379 = 362069) B362069
theorem B241395 : Blo 239816 241395 := bstep (se 1 (by rfl) ⟨181046, by rfl⟩ : syracuseStep 241395 = 362093) B362093
theorem B241411 : Blo 239816 241411 := bstep (se 1 (by rfl) ⟨181058, by rfl⟩ : syracuseStep 241411 = 362117) B362117
theorem B241427 : Blo 239816 241427 := bstep (se 1 (by rfl) ⟨181070, by rfl⟩ : syracuseStep 241427 = 362141) B362141
theorem B405283 : Blo 239816 405283 := bstep (se 1 (by rfl) ⟨303962, by rfl⟩ : syracuseStep 405283 = 607925) B607925
theorem B241443 : Blo 239816 241443 := bstep (se 1 (by rfl) ⟨181082, by rfl⟩ : syracuseStep 241443 = 362165) B362165
theorem B1322801 : Blo 239816 1322801 := bstep (se 2 (by rfl) ⟨496050, by rfl⟩ : syracuseStep 1322801 = 992101) B992101
theorem B241459 : Blo 239816 241459 := bstep (se 1 (by rfl) ⟨181094, by rfl⟩ : syracuseStep 241459 = 362189) B362189
theorem B241475 : Blo 239816 241475 := bstep (se 1 (by rfl) ⟨181106, by rfl⟩ : syracuseStep 241475 = 362213) B362213
theorem B274243 : Blo 239816 274243 := bstep (se 1 (by rfl) ⟨205682, by rfl⟩ : syracuseStep 274243 = 411365) B411365
theorem B241491 : Blo 239816 241491 := bstep (se 1 (by rfl) ⟨181118, by rfl⟩ : syracuseStep 241491 = 362237) B362237
theorem B241507 : Blo 239816 241507 := bstep (se 1 (by rfl) ⟨181130, by rfl⟩ : syracuseStep 241507 = 362261) B362261
theorem B241523 : Blo 239816 241523 := bstep (se 1 (by rfl) ⟨181142, by rfl⟩ : syracuseStep 241523 = 362285) B362285
theorem B241539 : Blo 239816 241539 := bstep (se 1 (by rfl) ⟨181154, by rfl⟩ : syracuseStep 241539 = 362309) B362309
theorem B241555 : Blo 239816 241555 := bstep (se 1 (by rfl) ⟨181166, by rfl⟩ : syracuseStep 241555 = 362333) B362333
theorem B307091 : Blo 239816 307091 := bstep (se 1 (by rfl) ⟨230318, by rfl⟩ : syracuseStep 307091 = 460637) B460637
theorem B241571 : Blo 239816 241571 := bstep (se 1 (by rfl) ⟨181178, by rfl⟩ : syracuseStep 241571 = 362357) B362357
theorem B405425 : Blo 239816 405425 := bstep (se 2 (by rfl) ⟨152034, by rfl⟩ : syracuseStep 405425 = 304069) B304069
theorem B241587 : Blo 239816 241587 := bstep (se 1 (by rfl) ⟨181190, by rfl⟩ : syracuseStep 241587 = 362381) B362381
theorem B241603 : Blo 239816 241603 := bstep (se 1 (by rfl) ⟨181202, by rfl⟩ : syracuseStep 241603 = 362405) B362405
theorem B733133 : Blo 239816 733133 := bstep (se 3 (by rfl) ⟨137462, by rfl⟩ : syracuseStep 733133 = 274925) B274925
theorem B241619 : Blo 239816 241619 := bstep (se 1 (by rfl) ⟨181214, by rfl⟩ : syracuseStep 241619 = 362429) B362429
theorem B241635 : Blo 239816 241635 := bstep (se 1 (by rfl) ⟨181226, by rfl⟩ : syracuseStep 241635 = 362453) B362453
theorem B241651 : Blo 239816 241651 := bstep (se 1 (by rfl) ⟨181238, by rfl⟩ : syracuseStep 241651 = 362477) B362477
theorem B241667 : Blo 239816 241667 := bstep (se 1 (by rfl) ⟨181250, by rfl⟩ : syracuseStep 241667 = 362501) B362501
theorem B241683 : Blo 239816 241683 := bstep (se 1 (by rfl) ⟨181262, by rfl⟩ : syracuseStep 241683 = 362525) B362525
theorem B241699 : Blo 239816 241699 := bstep (se 1 (by rfl) ⟨181274, by rfl⟩ : syracuseStep 241699 = 362549) B362549
theorem B405553 : Blo 239816 405553 := bstep (se 2 (by rfl) ⟨152082, by rfl⟩ : syracuseStep 405553 = 304165) B304165
theorem B241715 : Blo 239816 241715 := bstep (se 1 (by rfl) ⟨181286, by rfl⟩ : syracuseStep 241715 = 362573) B362573
theorem B241731 : Blo 239816 241731 := bstep (se 1 (by rfl) ⟨181298, by rfl⟩ : syracuseStep 241731 = 362597) B362597
theorem B405587 : Blo 239816 405587 := bstep (se 1 (by rfl) ⟨304190, by rfl⟩ : syracuseStep 405587 = 608381) B608381
theorem B241747 : Blo 239816 241747 := bstep (se 1 (by rfl) ⟨181310, by rfl⟩ : syracuseStep 241747 = 362621) B362621
theorem B241763 : Blo 239816 241763 := bstep (se 1 (by rfl) ⟨181322, by rfl⟩ : syracuseStep 241763 = 362645) B362645
theorem B241779 : Blo 239816 241779 := bstep (se 1 (by rfl) ⟨181334, by rfl⟩ : syracuseStep 241779 = 362669) B362669
theorem B241795 : Blo 239816 241795 := bstep (se 1 (by rfl) ⟨181346, by rfl⟩ : syracuseStep 241795 = 362693) B362693
theorem B241811 : Blo 239816 241811 := bstep (se 1 (by rfl) ⟨181358, by rfl⟩ : syracuseStep 241811 = 362717) B362717
theorem B241827 : Blo 239816 241827 := bstep (se 1 (by rfl) ⟨181370, by rfl⟩ : syracuseStep 241827 = 362741) B362741
theorem B1224881 : Blo 239816 1224881 := bstep (se 2 (by rfl) ⟨459330, by rfl⟩ : syracuseStep 1224881 = 918661) B918661
theorem B241843 : Blo 239816 241843 := bstep (se 1 (by rfl) ⟨181382, by rfl⟩ : syracuseStep 241843 = 362765) B362765
theorem B241859 : Blo 239816 241859 := bstep (se 1 (by rfl) ⟨181394, by rfl⟩ : syracuseStep 241859 = 362789) B362789
theorem B405715 : Blo 239816 405715 := bstep (se 1 (by rfl) ⟨304286, by rfl⟩ : syracuseStep 405715 = 608573) B608573
theorem B241875 : Blo 239816 241875 := bstep (se 1 (by rfl) ⟨181406, by rfl⟩ : syracuseStep 241875 = 362813) B362813
theorem B241891 : Blo 239816 241891 := bstep (se 1 (by rfl) ⟨181418, by rfl⟩ : syracuseStep 241891 = 362837) B362837
theorem B241907 : Blo 239816 241907 := bstep (se 1 (by rfl) ⟨181430, by rfl⟩ : syracuseStep 241907 = 362861) B362861
theorem B241923 : Blo 239816 241923 := bstep (se 1 (by rfl) ⟨181442, by rfl⟩ : syracuseStep 241923 = 362885) B362885
theorem B2961677 : Blo 239816 2961677 := bstep (se 3 (by rfl) ⟨555314, by rfl⟩ : syracuseStep 2961677 = 1110629) B1110629
theorem B241939 : Blo 239816 241939 := bstep (se 1 (by rfl) ⟨181454, by rfl⟩ : syracuseStep 241939 = 362909) B362909
theorem B733475 : Blo 239816 733475 := bstep (se 1 (by rfl) ⟨550106, by rfl⟩ : syracuseStep 733475 = 1100213) B1100213
theorem B241955 : Blo 239816 241955 := bstep (se 1 (by rfl) ⟨181466, by rfl⟩ : syracuseStep 241955 = 362933) B362933
theorem B241971 : Blo 239816 241971 := bstep (se 1 (by rfl) ⟨181478, by rfl⟩ : syracuseStep 241971 = 362957) B362957
theorem B241987 : Blo 239816 241987 := bstep (se 1 (by rfl) ⟨181490, by rfl⟩ : syracuseStep 241987 = 362981) B362981
theorem B242003 : Blo 239816 242003 := bstep (se 1 (by rfl) ⟨181502, by rfl⟩ : syracuseStep 242003 = 363005) B363005
theorem B405857 : Blo 239816 405857 := bstep (se 2 (by rfl) ⟨152196, by rfl⟩ : syracuseStep 405857 = 304393) B304393
theorem B242019 : Blo 239816 242019 := bstep (se 1 (by rfl) ⟨181514, by rfl⟩ : syracuseStep 242019 = 363029) B363029
theorem B242035 : Blo 239816 242035 := bstep (se 1 (by rfl) ⟨181526, by rfl⟩ : syracuseStep 242035 = 363053) B363053
theorem B242051 : Blo 239816 242051 := bstep (se 1 (by rfl) ⟨181538, by rfl⟩ : syracuseStep 242051 = 363077) B363077
theorem B242067 : Blo 239816 242067 := bstep (se 1 (by rfl) ⟨181550, by rfl⟩ : syracuseStep 242067 = 363101) B363101
theorem B242083 : Blo 239816 242083 := bstep (se 1 (by rfl) ⟨181562, by rfl⟩ : syracuseStep 242083 = 363125) B363125
theorem B242099 : Blo 239816 242099 := bstep (se 1 (by rfl) ⟨181574, by rfl⟩ : syracuseStep 242099 = 363149) B363149
theorem B242115 : Blo 239816 242115 := bstep (se 1 (by rfl) ⟨181586, by rfl⟩ : syracuseStep 242115 = 363173) B363173
theorem B242131 : Blo 239816 242131 := bstep (se 1 (by rfl) ⟨181598, by rfl⟩ : syracuseStep 242131 = 363197) B363197
theorem B405985 : Blo 239816 405985 := bstep (se 2 (by rfl) ⟨152244, by rfl⟩ : syracuseStep 405985 = 304489) B304489
theorem B242147 : Blo 239816 242147 := bstep (se 1 (by rfl) ⟨181610, by rfl⟩ : syracuseStep 242147 = 363221) B363221
theorem B242163 : Blo 239816 242163 := bstep (se 1 (by rfl) ⟨181622, by rfl⟩ : syracuseStep 242163 = 363245) B363245
theorem B406019 : Blo 239816 406019 := bstep (se 1 (by rfl) ⟨304514, by rfl⟩ : syracuseStep 406019 = 609029) B609029
theorem B242179 : Blo 239816 242179 := bstep (se 1 (by rfl) ⟨181634, by rfl⟩ : syracuseStep 242179 = 363269) B363269
theorem B242195 : Blo 239816 242195 := bstep (se 1 (by rfl) ⟨181646, by rfl⟩ : syracuseStep 242195 = 363293) B363293
theorem B242211 : Blo 239816 242211 := bstep (se 1 (by rfl) ⟨181658, by rfl⟩ : syracuseStep 242211 = 363317) B363317
theorem B242227 : Blo 239816 242227 := bstep (se 1 (by rfl) ⟨181670, by rfl⟩ : syracuseStep 242227 = 363341) B363341
theorem B242243 : Blo 239816 242243 := bstep (se 1 (by rfl) ⟨181682, by rfl⟩ : syracuseStep 242243 = 363365) B363365
theorem B242259 : Blo 239816 242259 := bstep (se 1 (by rfl) ⟨181694, by rfl⟩ : syracuseStep 242259 = 363389) B363389
theorem B307795 : Blo 239816 307795 := bstep (se 1 (by rfl) ⟨230846, by rfl⟩ : syracuseStep 307795 = 461693) B461693
theorem B242275 : Blo 239816 242275 := bstep (se 1 (by rfl) ⟨181706, by rfl⟩ : syracuseStep 242275 = 363413) B363413
theorem B242291 : Blo 239816 242291 := bstep (se 1 (by rfl) ⟨181718, by rfl⟩ : syracuseStep 242291 = 363437) B363437
theorem B406147 : Blo 239816 406147 := bstep (se 1 (by rfl) ⟨304610, by rfl⟩ : syracuseStep 406147 = 609221) B609221
theorem B242307 : Blo 239816 242307 := bstep (se 1 (by rfl) ⟨181730, by rfl⟩ : syracuseStep 242307 = 363461) B363461
theorem B242323 : Blo 239816 242323 := bstep (se 1 (by rfl) ⟨181742, by rfl⟩ : syracuseStep 242323 = 363485) B363485
theorem B242339 : Blo 239816 242339 := bstep (se 1 (by rfl) ⟨181754, by rfl⟩ : syracuseStep 242339 = 363509) B363509
theorem B438947 : Blo 239816 438947 := bstep (se 1 (by rfl) ⟨329210, by rfl⟩ : syracuseStep 438947 = 658421) B658421
theorem B242355 : Blo 239816 242355 := bstep (se 1 (by rfl) ⟨181766, by rfl⟩ : syracuseStep 242355 = 363533) B363533
theorem B307891 : Blo 239816 307891 := bstep (se 1 (by rfl) ⟨230918, by rfl⟩ : syracuseStep 307891 = 461837) B461837
theorem B242371 : Blo 239816 242371 := bstep (se 1 (by rfl) ⟨181778, by rfl⟩ : syracuseStep 242371 = 363557) B363557
theorem B242387 : Blo 239816 242387 := bstep (se 1 (by rfl) ⟨181790, by rfl⟩ : syracuseStep 242387 = 363581) B363581
theorem B242403 : Blo 239816 242403 := bstep (se 1 (by rfl) ⟨181802, by rfl⟩ : syracuseStep 242403 = 363605) B363605
theorem B242419 : Blo 239816 242419 := bstep (se 1 (by rfl) ⟨181814, by rfl⟩ : syracuseStep 242419 = 363629) B363629
theorem B242435 : Blo 239816 242435 := bstep (se 1 (by rfl) ⟨181826, by rfl⟩ : syracuseStep 242435 = 363653) B363653
theorem B1553165 : Blo 239816 1553165 := bstep (se 3 (by rfl) ⟨291218, by rfl⟩ : syracuseStep 1553165 = 582437) B582437
theorem B406289 : Blo 239816 406289 := bstep (se 2 (by rfl) ⟨152358, by rfl⟩ : syracuseStep 406289 = 304717) B304717
theorem B242451 : Blo 239816 242451 := bstep (se 1 (by rfl) ⟨181838, by rfl⟩ : syracuseStep 242451 = 363677) B363677
theorem B242467 : Blo 239816 242467 := bstep (se 1 (by rfl) ⟨181850, by rfl⟩ : syracuseStep 242467 = 363701) B363701
theorem B242483 : Blo 239816 242483 := bstep (se 1 (by rfl) ⟨181862, by rfl⟩ : syracuseStep 242483 = 363725) B363725
theorem B242499 : Blo 239816 242499 := bstep (se 1 (by rfl) ⟨181874, by rfl⟩ : syracuseStep 242499 = 363749) B363749
theorem B439121 : Blo 239816 439121 := bstep (se 2 (by rfl) ⟨164670, by rfl⟩ : syracuseStep 439121 = 329341) B329341
theorem B242515 : Blo 239816 242515 := bstep (se 1 (by rfl) ⟨181886, by rfl⟩ : syracuseStep 242515 = 363773) B363773
theorem B242531 : Blo 239816 242531 := bstep (se 1 (by rfl) ⟨181898, by rfl⟩ : syracuseStep 242531 = 363797) B363797
theorem B242547 : Blo 239816 242547 := bstep (se 1 (by rfl) ⟨181910, by rfl⟩ : syracuseStep 242547 = 363821) B363821
theorem B242563 : Blo 239816 242563 := bstep (se 1 (by rfl) ⟨181922, by rfl⟩ : syracuseStep 242563 = 363845) B363845
theorem B406417 : Blo 239816 406417 := bstep (se 2 (by rfl) ⟨152406, by rfl⟩ : syracuseStep 406417 = 304813) B304813
theorem B242579 : Blo 239816 242579 := bstep (se 1 (by rfl) ⟨181934, by rfl⟩ : syracuseStep 242579 = 363869) B363869
theorem B242595 : Blo 239816 242595 := bstep (se 1 (by rfl) ⟨181946, by rfl⟩ : syracuseStep 242595 = 363893) B363893
theorem B406451 : Blo 239816 406451 := bstep (se 1 (by rfl) ⟨304838, by rfl⟩ : syracuseStep 406451 = 609677) B609677
theorem B242611 : Blo 239816 242611 := bstep (se 1 (by rfl) ⟨181958, by rfl⟩ : syracuseStep 242611 = 363917) B363917
theorem B242627 : Blo 239816 242627 := bstep (se 1 (by rfl) ⟨181970, by rfl⟩ : syracuseStep 242627 = 363941) B363941
theorem B242643 : Blo 239816 242643 := bstep (se 1 (by rfl) ⟨181982, by rfl⟩ : syracuseStep 242643 = 363965) B363965
theorem B242659 : Blo 239816 242659 := bstep (se 1 (by rfl) ⟨181994, by rfl⟩ : syracuseStep 242659 = 363989) B363989
theorem B242675 : Blo 239816 242675 := bstep (se 1 (by rfl) ⟨182006, by rfl⟩ : syracuseStep 242675 = 364013) B364013
theorem B242691 : Blo 239816 242691 := bstep (se 1 (by rfl) ⟨182018, by rfl⟩ : syracuseStep 242691 = 364037) B364037
theorem B242707 : Blo 239816 242707 := bstep (se 1 (by rfl) ⟨182030, by rfl⟩ : syracuseStep 242707 = 364061) B364061
theorem B242723 : Blo 239816 242723 := bstep (se 1 (by rfl) ⟨182042, by rfl⟩ : syracuseStep 242723 = 364085) B364085
theorem B832547 : Blo 239816 832547 := bstep (se 1 (by rfl) ⟨624410, by rfl⟩ : syracuseStep 832547 = 1248821) B1248821
theorem B406579 : Blo 239816 406579 := bstep (se 1 (by rfl) ⟨304934, by rfl⟩ : syracuseStep 406579 = 609869) B609869
theorem B242739 : Blo 239816 242739 := bstep (se 1 (by rfl) ⟨182054, by rfl⟩ : syracuseStep 242739 = 364109) B364109
theorem B242755 : Blo 239816 242755 := bstep (se 1 (by rfl) ⟨182066, by rfl⟩ : syracuseStep 242755 = 364133) B364133
theorem B242771 : Blo 239816 242771 := bstep (se 1 (by rfl) ⟨182078, by rfl⟩ : syracuseStep 242771 = 364157) B364157
theorem B242787 : Blo 239816 242787 := bstep (se 1 (by rfl) ⟨182090, by rfl⟩ : syracuseStep 242787 = 364181) B364181
theorem B242803 : Blo 239816 242803 := bstep (se 1 (by rfl) ⟨182102, by rfl⟩ : syracuseStep 242803 = 364205) B364205
theorem B242819 : Blo 239816 242819 := bstep (se 1 (by rfl) ⟨182114, by rfl⟩ : syracuseStep 242819 = 364229) B364229
theorem B242835 : Blo 239816 242835 := bstep (se 1 (by rfl) ⟨182126, by rfl⟩ : syracuseStep 242835 = 364253) B364253
theorem B242851 : Blo 239816 242851 := bstep (se 1 (by rfl) ⟨182138, by rfl⟩ : syracuseStep 242851 = 364277) B364277
theorem B308387 : Blo 239816 308387 := bstep (se 1 (by rfl) ⟨231290, by rfl⟩ : syracuseStep 308387 = 462581) B462581
theorem B242867 : Blo 239816 242867 := bstep (se 1 (by rfl) ⟨182150, by rfl⟩ : syracuseStep 242867 = 364301) B364301
theorem B406721 : Blo 239816 406721 := bstep (se 2 (by rfl) ⟨152520, by rfl⟩ : syracuseStep 406721 = 305041) B305041
theorem B242883 : Blo 239816 242883 := bstep (se 1 (by rfl) ⟨182162, by rfl⟩ : syracuseStep 242883 = 364325) B364325
theorem B242899 : Blo 239816 242899 := bstep (se 1 (by rfl) ⟨182174, by rfl⟩ : syracuseStep 242899 = 364349) B364349
theorem B373987 : Blo 239816 373987 := bstep (se 1 (by rfl) ⟨280490, by rfl⟩ : syracuseStep 373987 = 560981) B560981
theorem B242915 : Blo 239816 242915 := bstep (se 1 (by rfl) ⟨182186, by rfl⟩ : syracuseStep 242915 = 364373) B364373
theorem B242931 : Blo 239816 242931 := bstep (se 1 (by rfl) ⟨182198, by rfl⟩ : syracuseStep 242931 = 364397) B364397
theorem B242947 : Blo 239816 242947 := bstep (se 1 (by rfl) ⟨182210, by rfl⟩ : syracuseStep 242947 = 364421) B364421
theorem B242963 : Blo 239816 242963 := bstep (se 1 (by rfl) ⟨182222, by rfl⟩ : syracuseStep 242963 = 364445) B364445
theorem B242979 : Blo 239816 242979 := bstep (se 1 (by rfl) ⟨182234, by rfl⟩ : syracuseStep 242979 = 364469) B364469
theorem B242995 : Blo 239816 242995 := bstep (se 1 (by rfl) ⟨182246, by rfl⟩ : syracuseStep 242995 = 364493) B364493
theorem B406849 : Blo 239816 406849 := bstep (se 2 (by rfl) ⟨152568, by rfl⟩ : syracuseStep 406849 = 305137) B305137
theorem B243011 : Blo 239816 243011 := bstep (se 1 (by rfl) ⟨182258, by rfl⟩ : syracuseStep 243011 = 364517) B364517
theorem B243027 : Blo 239816 243027 := bstep (se 1 (by rfl) ⟨182270, by rfl⟩ : syracuseStep 243027 = 364541) B364541
theorem B406883 : Blo 239816 406883 := bstep (se 1 (by rfl) ⟨305162, by rfl⟩ : syracuseStep 406883 = 610325) B610325
theorem B243043 : Blo 239816 243043 := bstep (se 1 (by rfl) ⟨182282, by rfl⟩ : syracuseStep 243043 = 364565) B364565
theorem B243059 : Blo 239816 243059 := bstep (se 1 (by rfl) ⟨182294, by rfl⟩ : syracuseStep 243059 = 364589) B364589
theorem B243075 : Blo 239816 243075 := bstep (se 1 (by rfl) ⟨182306, by rfl⟩ : syracuseStep 243075 = 364613) B364613
theorem B243091 : Blo 239816 243091 := bstep (se 1 (by rfl) ⟨182318, by rfl⟩ : syracuseStep 243091 = 364637) B364637
theorem B243107 : Blo 239816 243107 := bstep (se 1 (by rfl) ⟨182330, by rfl⟩ : syracuseStep 243107 = 364661) B364661
theorem B243123 : Blo 239816 243123 := bstep (se 1 (by rfl) ⟨182342, by rfl⟩ : syracuseStep 243123 = 364685) B364685
theorem B243139 : Blo 239816 243139 := bstep (se 1 (by rfl) ⟨182354, by rfl⟩ : syracuseStep 243139 = 364709) B364709
theorem B243155 : Blo 239816 243155 := bstep (se 1 (by rfl) ⟨182366, by rfl⟩ : syracuseStep 243155 = 364733) B364733
theorem B407011 : Blo 239816 407011 := bstep (se 1 (by rfl) ⟨305258, by rfl⟩ : syracuseStep 407011 = 610517) B610517
theorem B243171 : Blo 239816 243171 := bstep (se 1 (by rfl) ⟨182378, by rfl⟩ : syracuseStep 243171 = 364757) B364757
theorem B341491 : Blo 239816 341491 := bstep (se 1 (by rfl) ⟨256118, by rfl⟩ : syracuseStep 341491 = 512237) B512237
theorem B243187 : Blo 239816 243187 := bstep (se 1 (by rfl) ⟨182390, by rfl⟩ : syracuseStep 243187 = 364781) B364781
theorem B243203 : Blo 239816 243203 := bstep (se 1 (by rfl) ⟨182402, by rfl⟩ : syracuseStep 243203 = 364805) B364805
theorem B243219 : Blo 239816 243219 := bstep (se 1 (by rfl) ⟨182414, by rfl⟩ : syracuseStep 243219 = 364829) B364829
theorem B1029667 : Blo 239816 1029667 := bstep (se 1 (by rfl) ⟨772250, by rfl⟩ : syracuseStep 1029667 = 1544501) B1544501
theorem B243235 : Blo 239816 243235 := bstep (se 1 (by rfl) ⟨182426, by rfl⟩ : syracuseStep 243235 = 364853) B364853
theorem B243251 : Blo 239816 243251 := bstep (se 1 (by rfl) ⟨182438, by rfl⟩ : syracuseStep 243251 = 364877) B364877
theorem B243267 : Blo 239816 243267 := bstep (se 1 (by rfl) ⟨182450, by rfl⟩ : syracuseStep 243267 = 364901) B364901
theorem B243283 : Blo 239816 243283 := bstep (se 1 (by rfl) ⟨182462, by rfl⟩ : syracuseStep 243283 = 364925) B364925
theorem B1226339 : Blo 239816 1226339 := bstep (se 1 (by rfl) ⟨919754, by rfl⟩ : syracuseStep 1226339 = 1839509) B1839509
theorem B243299 : Blo 239816 243299 := bstep (se 1 (by rfl) ⟨182474, by rfl⟩ : syracuseStep 243299 = 364949) B364949
theorem B407153 : Blo 239816 407153 := bstep (se 2 (by rfl) ⟨152682, by rfl⟩ : syracuseStep 407153 = 305365) B305365
theorem B243315 : Blo 239816 243315 := bstep (se 1 (by rfl) ⟨182486, by rfl⟩ : syracuseStep 243315 = 364973) B364973
theorem B243331 : Blo 239816 243331 := bstep (se 1 (by rfl) ⟨182498, by rfl⟩ : syracuseStep 243331 = 364997) B364997
theorem B243347 : Blo 239816 243347 := bstep (se 1 (by rfl) ⟨182510, by rfl⟩ : syracuseStep 243347 = 365021) B365021
theorem B243363 : Blo 239816 243363 := bstep (se 1 (by rfl) ⟨182522, by rfl⟩ : syracuseStep 243363 = 365045) B365045
theorem B243379 : Blo 239816 243379 := bstep (se 1 (by rfl) ⟨182534, by rfl⟩ : syracuseStep 243379 = 365069) B365069
theorem B2733749 : Blo 239816 2733749 := bstep (se 5 (by rfl) ⟨128144, by rfl⟩ : syracuseStep 2733749 = 256289) B256289
theorem B243395 : Blo 239816 243395 := bstep (se 1 (by rfl) ⟨182546, by rfl⟩ : syracuseStep 243395 = 365093) B365093
theorem B243411 : Blo 239816 243411 := bstep (se 1 (by rfl) ⟨182558, by rfl⟩ : syracuseStep 243411 = 365117) B365117
theorem B243427 : Blo 239816 243427 := bstep (se 1 (by rfl) ⟨182570, by rfl⟩ : syracuseStep 243427 = 365141) B365141
theorem B407281 : Blo 239816 407281 := bstep (se 2 (by rfl) ⟨152730, by rfl⟩ : syracuseStep 407281 = 305461) B305461
theorem B243443 : Blo 239816 243443 := bstep (se 1 (by rfl) ⟨182582, by rfl⟩ : syracuseStep 243443 = 365165) B365165
theorem B243459 : Blo 239816 243459 := bstep (se 1 (by rfl) ⟨182594, by rfl⟩ : syracuseStep 243459 = 365189) B365189
theorem B407315 : Blo 239816 407315 := bstep (se 1 (by rfl) ⟨305486, by rfl⟩ : syracuseStep 407315 = 610973) B610973
theorem B243475 : Blo 239816 243475 := bstep (se 1 (by rfl) ⟨182606, by rfl⟩ : syracuseStep 243475 = 365213) B365213
theorem B243491 : Blo 239816 243491 := bstep (se 1 (by rfl) ⟨182618, by rfl⟩ : syracuseStep 243491 = 365237) B365237
theorem B243507 : Blo 239816 243507 := bstep (se 1 (by rfl) ⟨182630, by rfl⟩ : syracuseStep 243507 = 365261) B365261
theorem B243523 : Blo 239816 243523 := bstep (se 1 (by rfl) ⟨182642, by rfl⟩ : syracuseStep 243523 = 365285) B365285
theorem B243539 : Blo 239816 243539 := bstep (se 1 (by rfl) ⟨182654, by rfl⟩ : syracuseStep 243539 = 365309) B365309
theorem B243555 : Blo 239816 243555 := bstep (se 1 (by rfl) ⟨182666, by rfl⟩ : syracuseStep 243555 = 365333) B365333
theorem B243571 : Blo 239816 243571 := bstep (se 1 (by rfl) ⟨182678, by rfl⟩ : syracuseStep 243571 = 365357) B365357
theorem B243587 : Blo 239816 243587 := bstep (se 1 (by rfl) ⟨182690, by rfl⟩ : syracuseStep 243587 = 365381) B365381
theorem B866189 : Blo 239816 866189 := bstep (se 3 (by rfl) ⟨162410, by rfl⟩ : syracuseStep 866189 = 324821) B324821
theorem B1849229 : Blo 239816 1849229 := bstep (se 3 (by rfl) ⟨346730, by rfl⟩ : syracuseStep 1849229 = 693461) B693461
theorem B407443 : Blo 239816 407443 := bstep (se 1 (by rfl) ⟨305582, by rfl⟩ : syracuseStep 407443 = 611165) B611165
theorem B243603 : Blo 239816 243603 := bstep (se 1 (by rfl) ⟨182702, by rfl⟩ : syracuseStep 243603 = 365405) B365405
theorem B243619 : Blo 239816 243619 := bstep (se 1 (by rfl) ⟨182714, by rfl⟩ : syracuseStep 243619 = 365429) B365429
theorem B243635 : Blo 239816 243635 := bstep (se 1 (by rfl) ⟨182726, by rfl⟩ : syracuseStep 243635 = 365453) B365453
theorem B243651 : Blo 239816 243651 := bstep (se 1 (by rfl) ⟨182738, by rfl⟩ : syracuseStep 243651 = 365477) B365477
theorem B243667 : Blo 239816 243667 := bstep (se 1 (by rfl) ⟨182750, by rfl⟩ : syracuseStep 243667 = 365501) B365501
theorem B243683 : Blo 239816 243683 := bstep (se 1 (by rfl) ⟨182762, by rfl⟩ : syracuseStep 243683 = 365525) B365525
theorem B243699 : Blo 239816 243699 := bstep (se 1 (by rfl) ⟨182774, by rfl⟩ : syracuseStep 243699 = 365549) B365549
theorem B243715 : Blo 239816 243715 := bstep (se 1 (by rfl) ⟨182786, by rfl⟩ : syracuseStep 243715 = 365573) B365573
theorem B243731 : Blo 239816 243731 := bstep (se 1 (by rfl) ⟨182798, by rfl⟩ : syracuseStep 243731 = 365597) B365597
theorem B407585 : Blo 239816 407585 := bstep (se 2 (by rfl) ⟨152844, by rfl⟩ : syracuseStep 407585 = 305689) B305689
theorem B243747 : Blo 239816 243747 := bstep (se 1 (by rfl) ⟨182810, by rfl⟩ : syracuseStep 243747 = 365621) B365621
theorem B243763 : Blo 239816 243763 := bstep (se 1 (by rfl) ⟨182822, by rfl⟩ : syracuseStep 243763 = 365645) B365645
theorem B243779 : Blo 239816 243779 := bstep (se 1 (by rfl) ⟨182834, by rfl⟩ : syracuseStep 243779 = 365669) B365669
theorem B243795 : Blo 239816 243795 := bstep (se 1 (by rfl) ⟨182846, by rfl⟩ : syracuseStep 243795 = 365693) B365693
theorem B243811 : Blo 239816 243811 := bstep (se 1 (by rfl) ⟨182858, by rfl⟩ : syracuseStep 243811 = 365717) B365717
theorem B407713 : Blo 239816 407713 := bstep (se 2 (by rfl) ⟨152892, by rfl⟩ : syracuseStep 407713 = 305785) B305785
theorem B407747 : Blo 239816 407747 := bstep (se 1 (by rfl) ⟨305810, by rfl⟩ : syracuseStep 407747 = 611621) B611621
theorem B768305 : Blo 239816 768305 := bstep (se 2 (by rfl) ⟨288114, by rfl⟩ : syracuseStep 768305 = 576229) B576229
theorem B407875 : Blo 239816 407875 := bstep (se 1 (by rfl) ⟨305906, by rfl⟩ : syracuseStep 407875 = 611813) B611813
theorem B1227149 : Blo 239816 1227149 := bstep (se 3 (by rfl) ⟨230090, by rfl⟩ : syracuseStep 1227149 = 460181) B460181
theorem B5257669 : Blo 239816 5257669 := bstep (se 4 (by rfl) ⟨492906, by rfl⟩ : syracuseStep 5257669 = 985813) B985813
theorem B408017 : Blo 239816 408017 := bstep (se 2 (by rfl) ⟨153006, by rfl⟩ : syracuseStep 408017 = 306013) B306013
theorem B408145 : Blo 239816 408145 := bstep (se 2 (by rfl) ⟨153054, by rfl⟩ : syracuseStep 408145 = 306109) B306109
theorem B342625 : Blo 239816 342625 := bstep (se 2 (by rfl) ⟨128484, by rfl⟩ : syracuseStep 342625 = 256969) B256969
theorem B703085 : Blo 239816 703085 := bstep (se 3 (by rfl) ⟨131828, by rfl⟩ : syracuseStep 703085 = 263657) B263657
theorem B408179 : Blo 239816 408179 := bstep (se 1 (by rfl) ⟨306134, by rfl⟩ : syracuseStep 408179 = 612269) B612269
theorem B342721 : Blo 239816 342721 := bstep (se 2 (by rfl) ⟨128520, by rfl⟩ : syracuseStep 342721 = 257041) B257041
theorem B1030897 : Blo 239816 1030897 := bstep (se 2 (by rfl) ⟨386586, by rfl⟩ : syracuseStep 1030897 = 773173) B773173
theorem B408307 : Blo 239816 408307 := bstep (se 1 (by rfl) ⟨306230, by rfl⟩ : syracuseStep 408307 = 612461) B612461
theorem B408449 : Blo 239816 408449 := bstep (se 2 (by rfl) ⟨153168, by rfl⟩ : syracuseStep 408449 = 306337) B306337
theorem B408577 : Blo 239816 408577 := bstep (se 2 (by rfl) ⟨153216, by rfl⟩ : syracuseStep 408577 = 306433) B306433
theorem B408611 : Blo 239816 408611 := bstep (se 1 (by rfl) ⟨306458, by rfl⟩ : syracuseStep 408611 = 612917) B612917
theorem B539729 : Blo 239816 539729 := bstep (se 2 (by rfl) ⟨202398, by rfl⟩ : syracuseStep 539729 = 404797) B404797
theorem B539747 : Blo 239816 539747 := bstep (se 1 (by rfl) ⟨404810, by rfl⟩ : syracuseStep 539747 = 809621) B809621
theorem B408739 : Blo 239816 408739 := bstep (se 1 (by rfl) ⟨306554, by rfl⟩ : syracuseStep 408739 = 613109) B613109
theorem B343217 : Blo 239816 343217 := bstep (se 2 (by rfl) ⟨128706, by rfl⟩ : syracuseStep 343217 = 257413) B257413
theorem B408881 : Blo 239816 408881 := bstep (se 2 (by rfl) ⟨153330, by rfl⟩ : syracuseStep 408881 = 306661) B306661
theorem B736589 : Blo 239816 736589 := bstep (se 3 (by rfl) ⟨138110, by rfl⟩ : syracuseStep 736589 = 276221) B276221
theorem B245075 : Blo 239816 245075 := bstep (se 1 (by rfl) ⟨183806, by rfl⟩ : syracuseStep 245075 = 367613) B367613
theorem B540017 : Blo 239816 540017 := bstep (se 2 (by rfl) ⟨202506, by rfl⟩ : syracuseStep 540017 = 405013) B405013
theorem B540035 : Blo 239816 540035 := bstep (se 1 (by rfl) ⟨405026, by rfl⟩ : syracuseStep 540035 = 810053) B810053
theorem B409009 : Blo 239816 409009 := bstep (se 2 (by rfl) ⟨153378, by rfl⟩ : syracuseStep 409009 = 306757) B306757
theorem B409043 : Blo 239816 409043 := bstep (se 1 (by rfl) ⟨306782, by rfl⟩ : syracuseStep 409043 = 613565) B613565
theorem B409171 : Blo 239816 409171 := bstep (se 1 (by rfl) ⟨306878, by rfl⟩ : syracuseStep 409171 = 613757) B613757
theorem B540305 : Blo 239816 540305 := bstep (se 2 (by rfl) ⟨202614, by rfl⟩ : syracuseStep 540305 = 405229) B405229
theorem B540323 : Blo 239816 540323 := bstep (se 1 (by rfl) ⟨405242, by rfl⟩ : syracuseStep 540323 = 810485) B810485
theorem B409313 : Blo 239816 409313 := bstep (se 2 (by rfl) ⟨153492, by rfl⟩ : syracuseStep 409313 = 306985) B306985
theorem B409441 : Blo 239816 409441 := bstep (se 2 (by rfl) ⟨153540, by rfl⟩ : syracuseStep 409441 = 307081) B307081
theorem B409475 : Blo 239816 409475 := bstep (se 1 (by rfl) ⟨307106, by rfl⟩ : syracuseStep 409475 = 614213) B614213
theorem B540593 : Blo 239816 540593 := bstep (se 2 (by rfl) ⟨202722, by rfl⟩ : syracuseStep 540593 = 405445) B405445
theorem B540611 : Blo 239816 540611 := bstep (se 1 (by rfl) ⟨405458, by rfl⟩ : syracuseStep 540611 = 810917) B810917
theorem B737219 : Blo 239816 737219 := bstep (se 1 (by rfl) ⟨552914, by rfl⟩ : syracuseStep 737219 = 1105829) B1105829
theorem B409603 : Blo 239816 409603 := bstep (se 1 (by rfl) ⟨307202, by rfl⟩ : syracuseStep 409603 = 614405) B614405
theorem B344083 : Blo 239816 344083 := bstep (se 1 (by rfl) ⟨258062, by rfl⟩ : syracuseStep 344083 = 516125) B516125
theorem B344179 : Blo 239816 344179 := bstep (se 1 (by rfl) ⟨258134, by rfl⟩ : syracuseStep 344179 = 516269) B516269
theorem B409745 : Blo 239816 409745 := bstep (se 2 (by rfl) ⟨153654, by rfl⟩ : syracuseStep 409745 = 307309) B307309
theorem B540881 : Blo 239816 540881 := bstep (se 2 (by rfl) ⟨202830, by rfl⟩ : syracuseStep 540881 = 405661) B405661
theorem B540899 : Blo 239816 540899 := bstep (se 1 (by rfl) ⟨405674, by rfl⟩ : syracuseStep 540899 = 811349) B811349
theorem B409873 : Blo 239816 409873 := bstep (se 2 (by rfl) ⟨153702, by rfl⟩ : syracuseStep 409873 = 307405) B307405
theorem B409907 : Blo 239816 409907 := bstep (se 1 (by rfl) ⟨307430, by rfl⟩ : syracuseStep 409907 = 614861) B614861
theorem B410035 : Blo 239816 410035 := bstep (se 1 (by rfl) ⟨307526, by rfl⟩ : syracuseStep 410035 = 615053) B615053
theorem B541169 : Blo 239816 541169 := bstep (se 2 (by rfl) ⟨202938, by rfl⟩ : syracuseStep 541169 = 405877) B405877
theorem B541187 : Blo 239816 541187 := bstep (se 1 (by rfl) ⟨405890, by rfl⟩ : syracuseStep 541187 = 811781) B811781
theorem B410177 : Blo 239816 410177 := bstep (se 2 (by rfl) ⟨153816, by rfl⟩ : syracuseStep 410177 = 307633) B307633
theorem B344675 : Blo 239816 344675 := bstep (se 1 (by rfl) ⟨258506, by rfl⟩ : syracuseStep 344675 = 517013) B517013
theorem B410305 : Blo 239816 410305 := bstep (se 2 (by rfl) ⟨153864, by rfl⟩ : syracuseStep 410305 = 307729) B307729
theorem B2081477 : Blo 239816 2081477 := bstep (se 4 (by rfl) ⟨195138, by rfl⟩ : syracuseStep 2081477 = 390277) B390277
theorem B410339 : Blo 239816 410339 := bstep (se 1 (by rfl) ⟨307754, by rfl⟩ : syracuseStep 410339 = 615509) B615509
theorem B541457 : Blo 239816 541457 := bstep (se 2 (by rfl) ⟨203046, by rfl⟩ : syracuseStep 541457 = 406093) B406093
theorem B541475 : Blo 239816 541475 := bstep (se 1 (by rfl) ⟨406106, by rfl⟩ : syracuseStep 541475 = 812213) B812213
theorem B1295153 : Blo 239816 1295153 := bstep (se 2 (by rfl) ⟨485682, by rfl⟩ : syracuseStep 1295153 = 971365) B971365
theorem B410467 : Blo 239816 410467 := bstep (se 1 (by rfl) ⟨307850, by rfl⟩ : syracuseStep 410467 = 615701) B615701
theorem B1491853 : Blo 239816 1491853 := bstep (se 3 (by rfl) ⟨279722, by rfl⟩ : syracuseStep 1491853 = 559445) B559445
theorem B934897 : Blo 239816 934897 := bstep (se 2 (by rfl) ⟨350586, by rfl⟩ : syracuseStep 934897 = 701173) B701173
theorem B410609 : Blo 239816 410609 := bstep (se 2 (by rfl) ⟨153978, by rfl⟩ : syracuseStep 410609 = 307957) B307957
theorem B541745 : Blo 239816 541745 := bstep (se 2 (by rfl) ⟨203154, by rfl⟩ : syracuseStep 541745 = 406309) B406309
theorem B541763 : Blo 239816 541763 := bstep (se 1 (by rfl) ⟨406322, by rfl⟩ : syracuseStep 541763 = 812645) B812645
theorem B410737 : Blo 239816 410737 := bstep (se 2 (by rfl) ⟨154026, by rfl⟩ : syracuseStep 410737 = 308053) B308053
theorem B410771 : Blo 239816 410771 := bstep (se 1 (by rfl) ⟨308078, by rfl⟩ : syracuseStep 410771 = 616157) B616157
theorem B607409 : Blo 239816 607409 := bstep (se 2 (by rfl) ⟨227778, by rfl⟩ : syracuseStep 607409 = 455557) B455557
theorem B771277 : Blo 239816 771277 := bstep (se 3 (by rfl) ⟨144614, by rfl⟩ : syracuseStep 771277 = 289229) B289229
theorem B345313 : Blo 239816 345313 := bstep (se 2 (by rfl) ⟨129492, by rfl⟩ : syracuseStep 345313 = 258985) B258985
theorem B607459 : Blo 239816 607459 := bstep (se 1 (by rfl) ⟨455594, by rfl⟩ : syracuseStep 607459 = 911189) B911189
theorem B1230065 : Blo 239816 1230065 := bstep (se 2 (by rfl) ⟨461274, by rfl⟩ : syracuseStep 1230065 = 922549) B922549
theorem B410899 : Blo 239816 410899 := bstep (se 1 (by rfl) ⟨308174, by rfl⟩ : syracuseStep 410899 = 616349) B616349
theorem B542033 : Blo 239816 542033 := bstep (se 2 (by rfl) ⟨203262, by rfl⟩ : syracuseStep 542033 = 406525) B406525
theorem B2311523 : Blo 239816 2311523 := bstep (se 1 (by rfl) ⟨1733642, by rfl⟩ : syracuseStep 2311523 = 3467285) B3467285
theorem B542051 : Blo 239816 542051 := bstep (se 1 (by rfl) ⟨406538, by rfl⟩ : syracuseStep 542051 = 813077) B813077
theorem B607601 : Blo 239816 607601 := bstep (se 2 (by rfl) ⟨227850, by rfl⟩ : syracuseStep 607601 = 455701) B455701
theorem B411041 : Blo 239816 411041 := bstep (se 2 (by rfl) ⟨154140, by rfl⟩ : syracuseStep 411041 = 308281) B308281
theorem B771533 : Blo 239816 771533 := bstep (se 3 (by rfl) ⟨144662, by rfl⟩ : syracuseStep 771533 = 289325) B289325
theorem B411169 : Blo 239816 411169 := bstep (se 2 (by rfl) ⟨154188, by rfl⟩ : syracuseStep 411169 = 308377) B308377
theorem B345649 : Blo 239816 345649 := bstep (se 2 (by rfl) ⟨129618, by rfl⟩ : syracuseStep 345649 = 259237) B259237
theorem B411203 : Blo 239816 411203 := bstep (se 1 (by rfl) ⟨308402, by rfl⟩ : syracuseStep 411203 = 616805) B616805
theorem B1754693 : Blo 239816 1754693 := bstep (se 4 (by rfl) ⟨164502, by rfl⟩ : syracuseStep 1754693 = 329005) B329005
theorem B542321 : Blo 239816 542321 := bstep (se 2 (by rfl) ⟨203370, by rfl⟩ : syracuseStep 542321 = 406741) B406741
theorem B542339 : Blo 239816 542339 := bstep (se 1 (by rfl) ⟨406754, by rfl⟩ : syracuseStep 542339 = 813509) B813509
theorem B411331 : Blo 239816 411331 := bstep (se 1 (by rfl) ⟨308498, by rfl⟩ : syracuseStep 411331 = 616997) B616997
theorem B411361 : Blo 239816 411361 := bstep (se 2 (by rfl) ⟨154260, by rfl⟩ : syracuseStep 411361 = 308521) B308521
theorem B411473 : Blo 239816 411473 := bstep (se 2 (by rfl) ⟨154302, by rfl⟩ : syracuseStep 411473 = 308605) B308605
theorem B542609 : Blo 239816 542609 := bstep (se 2 (by rfl) ⟨203478, by rfl⟩ : syracuseStep 542609 = 406957) B406957
theorem B542627 : Blo 239816 542627 := bstep (se 1 (by rfl) ⟨406970, by rfl⟩ : syracuseStep 542627 = 813941) B813941
theorem B870385 : Blo 239816 870385 := bstep (se 2 (by rfl) ⟨326394, by rfl⟩ : syracuseStep 870385 = 652789) B652789
theorem B346241 : Blo 239816 346241 := bstep (se 2 (by rfl) ⟨129840, by rfl⟩ : syracuseStep 346241 = 259681) B259681
theorem B739459 : Blo 239816 739459 := bstep (se 1 (by rfl) ⟨554594, by rfl⟩ : syracuseStep 739459 = 1109189) B1109189
theorem B542897 : Blo 239816 542897 := bstep (se 2 (by rfl) ⟨203586, by rfl⟩ : syracuseStep 542897 = 407173) B407173
theorem B542915 : Blo 239816 542915 := bstep (se 1 (by rfl) ⟨407186, by rfl⟩ : syracuseStep 542915 = 814373) B814373
theorem B411889 : Blo 239816 411889 := bstep (se 2 (by rfl) ⟨154458, by rfl⟩ : syracuseStep 411889 = 308917) B308917
theorem B1165603 : Blo 239816 1165603 := bstep (se 1 (by rfl) ⟨874202, by rfl⟩ : syracuseStep 1165603 = 1748405) B1748405
theorem B608593 : Blo 239816 608593 := bstep (se 2 (by rfl) ⟨228222, by rfl⟩ : syracuseStep 608593 = 456445) B456445
theorem B1296773 : Blo 239816 1296773 := bstep (se 4 (by rfl) ⟨121572, by rfl⟩ : syracuseStep 1296773 = 243145) B243145
theorem B2574773 : Blo 239816 2574773 := bstep (se 5 (by rfl) ⟨120692, by rfl⟩ : syracuseStep 2574773 = 241385) B241385
theorem B543185 : Blo 239816 543185 := bstep (se 2 (by rfl) ⟨203694, by rfl⟩ : syracuseStep 543185 = 407389) B407389
theorem B543203 : Blo 239816 543203 := bstep (se 1 (by rfl) ⟨407402, by rfl⟩ : syracuseStep 543203 = 814805) B814805
theorem B510449 : Blo 239816 510449 := bstep (se 2 (by rfl) ⟨191418, by rfl⟩ : syracuseStep 510449 = 382837) B382837
theorem B608867 : Blo 239816 608867 := bstep (se 1 (by rfl) ⟨456650, by rfl⟩ : syracuseStep 608867 = 913301) B913301
theorem B3361421 : Blo 239816 3361421 := bstep (se 3 (by rfl) ⟨630266, by rfl⟩ : syracuseStep 3361421 = 1260533) B1260533
theorem B346771 : Blo 239816 346771 := bstep (se 1 (by rfl) ⟨260078, by rfl⟩ : syracuseStep 346771 = 520157) B520157
theorem B1231523 : Blo 239816 1231523 := bstep (se 1 (by rfl) ⟨923642, by rfl⟩ : syracuseStep 1231523 = 1847285) B1847285
theorem B543473 : Blo 239816 543473 := bstep (se 2 (by rfl) ⟨203802, by rfl⟩ : syracuseStep 543473 = 407605) B407605
theorem B543491 : Blo 239816 543491 := bstep (se 1 (by rfl) ⟨407618, by rfl⟩ : syracuseStep 543491 = 815237) B815237
theorem B609059 : Blo 239816 609059 := bstep (se 1 (by rfl) ⟨456794, by rfl⟩ : syracuseStep 609059 = 913589) B913589
theorem B740141 : Blo 239816 740141 := bstep (se 3 (by rfl) ⟨138776, by rfl⟩ : syracuseStep 740141 = 277553) B277553
theorem B773059 : Blo 239816 773059 := bstep (se 1 (by rfl) ⟨579794, by rfl⟩ : syracuseStep 773059 = 1159589) B1159589
theorem B347107 : Blo 239816 347107 := bstep (se 1 (by rfl) ⟨260330, by rfl⟩ : syracuseStep 347107 = 520661) B520661
theorem B740333 : Blo 239816 740333 := bstep (se 3 (by rfl) ⟨138812, by rfl⟩ : syracuseStep 740333 = 277625) B277625
theorem B576497 : Blo 239816 576497 := bstep (se 2 (by rfl) ⟨216186, by rfl⟩ : syracuseStep 576497 = 432373) B432373
theorem B543761 : Blo 239816 543761 := bstep (se 2 (by rfl) ⟨203910, by rfl⟩ : syracuseStep 543761 = 407821) B407821
theorem B543779 : Blo 239816 543779 := bstep (se 1 (by rfl) ⟨407834, by rfl⟩ : syracuseStep 543779 = 815669) B815669
theorem B1035341 : Blo 239816 1035341 := bstep (se 3 (by rfl) ⟨194126, by rfl⟩ : syracuseStep 1035341 = 388253) B388253
theorem B412771 : Blo 239816 412771 := bstep (se 1 (by rfl) ⟨309578, by rfl⟩ : syracuseStep 412771 = 619157) B619157
theorem B544049 : Blo 239816 544049 := bstep (se 2 (by rfl) ⟨204018, by rfl⟩ : syracuseStep 544049 = 408037) B408037
theorem B544067 : Blo 239816 544067 := bstep (se 1 (by rfl) ⟨408050, by rfl⟩ : syracuseStep 544067 = 816101) B816101
theorem B347537 : Blo 239816 347537 := bstep (se 2 (by rfl) ⟨130326, by rfl⟩ : syracuseStep 347537 = 260653) B260653
theorem B1232333 : Blo 239816 1232333 := bstep (se 3 (by rfl) ⟨231062, by rfl⟩ : syracuseStep 1232333 = 462125) B462125
theorem B1166833 : Blo 239816 1166833 := bstep (se 2 (by rfl) ⟨437562, by rfl⟩ : syracuseStep 1166833 = 875125) B875125
theorem B544337 : Blo 239816 544337 := bstep (se 2 (by rfl) ⟨204126, by rfl⟩ : syracuseStep 544337 = 408253) B408253
theorem B544355 : Blo 239816 544355 := bstep (se 1 (by rfl) ⟨408266, by rfl⟩ : syracuseStep 544355 = 816533) B816533
theorem B610001 : Blo 239816 610001 := bstep (se 2 (by rfl) ⟨228750, by rfl⟩ : syracuseStep 610001 = 457501) B457501
theorem B610051 : Blo 239816 610051 := bstep (se 1 (by rfl) ⟨457538, by rfl⟩ : syracuseStep 610051 = 915077) B915077
theorem B773891 : Blo 239816 773891 := bstep (se 1 (by rfl) ⟨580418, by rfl⟩ : syracuseStep 773891 = 1160837) B1160837
theorem B544625 : Blo 239816 544625 := bstep (se 2 (by rfl) ⟨204234, by rfl⟩ : syracuseStep 544625 = 408469) B408469
theorem B544643 : Blo 239816 544643 := bstep (se 1 (by rfl) ⟨408482, by rfl⟩ : syracuseStep 544643 = 816965) B816965
theorem B1462157 : Blo 239816 1462157 := bstep (se 3 (by rfl) ⟨274154, by rfl⟩ : syracuseStep 1462157 = 548309) B548309
theorem B610193 : Blo 239816 610193 := bstep (se 2 (by rfl) ⟨228822, by rfl⟩ : syracuseStep 610193 = 457645) B457645
theorem B937969 : Blo 239816 937969 := bstep (se 2 (by rfl) ⟨351738, by rfl⟩ : syracuseStep 937969 = 703477) B703477
theorem B774289 : Blo 239816 774289 := bstep (se 2 (by rfl) ⟨290358, by rfl⟩ : syracuseStep 774289 = 580717) B580717
theorem B544913 : Blo 239816 544913 := bstep (se 2 (by rfl) ⟨204342, by rfl⟩ : syracuseStep 544913 = 408685) B408685
theorem B544931 : Blo 239816 544931 := bstep (se 1 (by rfl) ⟨408698, by rfl⟩ : syracuseStep 544931 = 817397) B817397
theorem B774353 : Blo 239816 774353 := bstep (se 2 (by rfl) ⟨290382, by rfl⟩ : syracuseStep 774353 = 580765) B580765
theorem B1364273 : Blo 239816 1364273 := bstep (se 2 (by rfl) ⟨511602, by rfl⟩ : syracuseStep 1364273 = 1023205) B1023205
theorem B545201 : Blo 239816 545201 := bstep (se 2 (by rfl) ⟨204450, by rfl⟩ : syracuseStep 545201 = 408901) B408901
theorem B545219 : Blo 239816 545219 := bstep (se 1 (by rfl) ⟨408914, by rfl⟩ : syracuseStep 545219 = 817829) B817829
theorem B414209 : Blo 239816 414209 := bstep (se 2 (by rfl) ⟨155328, by rfl⟩ : syracuseStep 414209 = 310657) B310657
theorem B1167949 : Blo 239816 1167949 := bstep (se 3 (by rfl) ⟨218990, by rfl⟩ : syracuseStep 1167949 = 437981) B437981
theorem B545489 : Blo 239816 545489 := bstep (se 2 (by rfl) ⟨204558, by rfl⟩ : syracuseStep 545489 = 409117) B409117
theorem B545507 : Blo 239816 545507 := bstep (se 1 (by rfl) ⟨409130, by rfl⟩ : syracuseStep 545507 = 818261) B818261
theorem B611185 : Blo 239816 611185 := bstep (se 2 (by rfl) ⟨229194, by rfl⟩ : syracuseStep 611185 = 458389) B458389
theorem B545777 : Blo 239816 545777 := bstep (se 2 (by rfl) ⟨204666, by rfl⟩ : syracuseStep 545777 = 409333) B409333
theorem B545795 : Blo 239816 545795 := bstep (se 1 (by rfl) ⟨409346, by rfl⟩ : syracuseStep 545795 = 818693) B818693
theorem B513091 : Blo 239816 513091 := bstep (se 1 (by rfl) ⟨384818, by rfl⟩ : syracuseStep 513091 = 769637) B769637
theorem B611459 : Blo 239816 611459 := bstep (se 1 (by rfl) ⟨458594, by rfl⟩ : syracuseStep 611459 = 917189) B917189
theorem B546065 : Blo 239816 546065 := bstep (se 2 (by rfl) ⟨204774, by rfl⟩ : syracuseStep 546065 = 409549) B409549
theorem B546083 : Blo 239816 546083 := bstep (se 1 (by rfl) ⟨409562, by rfl⟩ : syracuseStep 546083 = 819125) B819125
theorem B611651 : Blo 239816 611651 := bstep (se 1 (by rfl) ⟨458738, by rfl⟩ : syracuseStep 611651 = 917477) B917477
theorem B513553 : Blo 239816 513553 := bstep (se 2 (by rfl) ⟨192582, by rfl⟩ : syracuseStep 513553 = 385165) B385165
theorem B546353 : Blo 239816 546353 := bstep (se 2 (by rfl) ⟨204882, by rfl⟩ : syracuseStep 546353 = 409765) B409765
theorem B546371 : Blo 239816 546371 := bstep (se 1 (by rfl) ⟨409778, by rfl⟩ : syracuseStep 546371 = 819557) B819557
theorem B4150925 : Blo 239816 4150925 := bstep (se 3 (by rfl) ⟨778298, by rfl⟩ : syracuseStep 4150925 = 1556597) B1556597
theorem B972515 : Blo 239816 972515 := bstep (se 1 (by rfl) ⟨729386, by rfl⟩ : syracuseStep 972515 = 1458773) B1458773
theorem B3102533 : Blo 239816 3102533 := bstep (se 4 (by rfl) ⟨290862, by rfl⟩ : syracuseStep 3102533 = 581725) B581725
theorem B546641 : Blo 239816 546641 := bstep (se 2 (by rfl) ⟨204990, by rfl⟩ : syracuseStep 546641 = 409981) B409981
theorem B546659 : Blo 239816 546659 := bstep (se 1 (by rfl) ⟨409994, by rfl⟩ : syracuseStep 546659 = 819989) B819989
theorem B546929 : Blo 239816 546929 := bstep (se 2 (by rfl) ⟨205098, by rfl⟩ : syracuseStep 546929 = 410197) B410197
theorem B546947 : Blo 239816 546947 := bstep (se 1 (by rfl) ⟨410210, by rfl⟩ : syracuseStep 546947 = 820421) B820421
theorem B612593 : Blo 239816 612593 := bstep (se 2 (by rfl) ⟨229722, by rfl⟩ : syracuseStep 612593 = 459445) B459445
theorem B1366307 : Blo 239816 1366307 := bstep (se 1 (by rfl) ⟨1024730, by rfl⟩ : syracuseStep 1366307 = 2049461) B2049461
theorem B612643 : Blo 239816 612643 := bstep (se 1 (by rfl) ⟨459482, by rfl⟩ : syracuseStep 612643 = 918965) B918965
theorem B416083 : Blo 239816 416083 := bstep (se 1 (by rfl) ⟨312062, by rfl⟩ : syracuseStep 416083 = 624125) B624125
theorem B547217 : Blo 239816 547217 := bstep (se 2 (by rfl) ⟨205206, by rfl⟩ : syracuseStep 547217 = 410413) B410413
theorem B547235 : Blo 239816 547235 := bstep (se 1 (by rfl) ⟨410426, by rfl⟩ : syracuseStep 547235 = 820853) B820853
theorem B612785 : Blo 239816 612785 := bstep (se 2 (by rfl) ⟨229794, by rfl⟩ : syracuseStep 612785 = 459589) B459589
theorem B514595 : Blo 239816 514595 := bstep (se 1 (by rfl) ⟨385946, by rfl⟩ : syracuseStep 514595 = 771893) B771893
theorem B2939533 : Blo 239816 2939533 := bstep (se 3 (by rfl) ⟨551162, by rfl⟩ : syracuseStep 2939533 = 1102325) B1102325
theorem B547505 : Blo 239816 547505 := bstep (se 2 (by rfl) ⟨205314, by rfl⟩ : syracuseStep 547505 = 410629) B410629
theorem B547523 : Blo 239816 547523 := bstep (se 1 (by rfl) ⟨410642, by rfl⟩ : syracuseStep 547523 = 821285) B821285
theorem B809837 : Blo 239816 809837 := bstep (se 3 (by rfl) ⟨151844, by rfl⟩ : syracuseStep 809837 = 303689) B303689
theorem B809891 : Blo 239816 809891 := bstep (se 1 (by rfl) ⟨607418, by rfl⟩ : syracuseStep 809891 = 1214837) B1214837
theorem B547793 : Blo 239816 547793 := bstep (se 2 (by rfl) ⟨205422, by rfl⟩ : syracuseStep 547793 = 410845) B410845
theorem B547811 : Blo 239816 547811 := bstep (se 1 (by rfl) ⟨410858, by rfl⟩ : syracuseStep 547811 = 821717) B821717
theorem B3300365 : Blo 239816 3300365 := bstep (se 3 (by rfl) ⟨618818, by rfl⟩ : syracuseStep 3300365 = 1237637) B1237637
theorem B515107 : Blo 239816 515107 := bstep (se 1 (by rfl) ⟨386330, by rfl⟩ : syracuseStep 515107 = 772661) B772661
theorem B810161 : Blo 239816 810161 := bstep (se 2 (by rfl) ⟨303810, by rfl⟩ : syracuseStep 810161 = 607621) B607621
theorem B548081 : Blo 239816 548081 := bstep (se 2 (by rfl) ⟨205530, by rfl⟩ : syracuseStep 548081 = 411061) B411061
theorem B548099 : Blo 239816 548099 := bstep (se 1 (by rfl) ⟨411074, by rfl⟩ : syracuseStep 548099 = 822149) B822149
theorem B1039715 : Blo 239816 1039715 := bstep (se 1 (by rfl) ⟨779786, by rfl⟩ : syracuseStep 1039715 = 1559573) B1559573
theorem B613777 : Blo 239816 613777 := bstep (se 2 (by rfl) ⟨230166, by rfl⟩ : syracuseStep 613777 = 460333) B460333
theorem B548369 : Blo 239816 548369 := bstep (se 2 (by rfl) ⟨205638, by rfl⟩ : syracuseStep 548369 = 411277) B411277
theorem B548387 : Blo 239816 548387 := bstep (se 1 (by rfl) ⟨411290, by rfl⟩ : syracuseStep 548387 = 822581) B822581
theorem B384563 : Blo 239816 384563 := bstep (se 1 (by rfl) ⟨288422, by rfl⟩ : syracuseStep 384563 = 576845) B576845
theorem B4677173 : Blo 239816 4677173 := bstep (se 5 (by rfl) ⟨219242, by rfl⟩ : syracuseStep 4677173 = 438485) B438485
theorem B351811 : Blo 239816 351811 := bstep (se 1 (by rfl) ⟨263858, by rfl⟩ : syracuseStep 351811 = 527717) B527717
theorem B614051 : Blo 239816 614051 := bstep (se 1 (by rfl) ⟨460538, by rfl⟩ : syracuseStep 614051 = 921077) B921077
theorem B810701 : Blo 239816 810701 := bstep (se 3 (by rfl) ⟨152006, by rfl⟩ : syracuseStep 810701 = 304013) B304013
theorem B515825 : Blo 239816 515825 := bstep (se 2 (by rfl) ⟨193434, by rfl⟩ : syracuseStep 515825 = 386869) B386869
theorem B810755 : Blo 239816 810755 := bstep (se 1 (by rfl) ⟨608066, by rfl⟩ : syracuseStep 810755 = 1216133) B1216133
theorem B384787 : Blo 239816 384787 := bstep (se 1 (by rfl) ⟨288590, by rfl⟩ : syracuseStep 384787 = 577181) B577181
theorem B614243 : Blo 239816 614243 := bstep (se 1 (by rfl) ⟨460682, by rfl⟩ : syracuseStep 614243 = 921365) B921365
theorem B417793 : Blo 239816 417793 := bstep (se 2 (by rfl) ⟨156672, by rfl⟩ : syracuseStep 417793 = 313345) B313345
theorem B811025 : Blo 239816 811025 := bstep (se 2 (by rfl) ⟨304134, by rfl⟩ : syracuseStep 811025 = 608269) B608269
theorem B1564721 : Blo 239816 1564721 := bstep (se 2 (by rfl) ⟨586770, by rfl⟩ : syracuseStep 1564721 = 1173541) B1173541
theorem B1368197 : Blo 239816 1368197 := bstep (se 4 (by rfl) ⟨128268, by rfl⟩ : syracuseStep 1368197 = 256537) B256537
theorem B778531 : Blo 239816 778531 := bstep (se 1 (by rfl) ⟨583898, by rfl⟩ : syracuseStep 778531 = 1167797) B1167797
theorem B1401229 : Blo 239816 1401229 := bstep (se 3 (by rfl) ⟨262730, by rfl⟩ : syracuseStep 1401229 = 525461) B525461
theorem B516611 : Blo 239816 516611 := bstep (se 1 (by rfl) ⟨387458, by rfl⟩ : syracuseStep 516611 = 774917) B774917
theorem B811565 : Blo 239816 811565 := bstep (se 3 (by rfl) ⟨152168, by rfl⟩ : syracuseStep 811565 = 304337) B304337
theorem B811619 : Blo 239816 811619 := bstep (se 1 (by rfl) ⟨608714, by rfl⟩ : syracuseStep 811619 = 1217429) B1217429
theorem B385793 : Blo 239816 385793 := bstep (se 2 (by rfl) ⟨144672, by rfl⟩ : syracuseStep 385793 = 289345) B289345
theorem B549649 : Blo 239816 549649 := bstep (se 2 (by rfl) ⟨206118, by rfl⟩ : syracuseStep 549649 = 412237) B412237
theorem B615185 : Blo 239816 615185 := bstep (se 2 (by rfl) ⟨230694, by rfl⟩ : syracuseStep 615185 = 461389) B461389
theorem B615235 : Blo 239816 615235 := bstep (se 1 (by rfl) ⟨461426, by rfl⟩ : syracuseStep 615235 = 922853) B922853
theorem B811889 : Blo 239816 811889 := bstep (se 2 (by rfl) ⟨304458, by rfl⟩ : syracuseStep 811889 = 608917) B608917
theorem B385985 : Blo 239816 385985 := bstep (se 2 (by rfl) ⟨144744, by rfl⟩ : syracuseStep 385985 = 289489) B289489
theorem B1467341 : Blo 239816 1467341 := bstep (se 3 (by rfl) ⟨275126, by rfl⟩ : syracuseStep 1467341 = 550253) B550253
theorem B615377 : Blo 239816 615377 := bstep (se 2 (by rfl) ⟨230766, by rfl⟩ : syracuseStep 615377 = 461533) B461533
theorem B1041457 : Blo 239816 1041457 := bstep (se 2 (by rfl) ⟨390546, by rfl⟩ : syracuseStep 1041457 = 781093) B781093
theorem B2745413 : Blo 239816 2745413 := bstep (se 4 (by rfl) ⟨257382, by rfl⟩ : syracuseStep 2745413 = 514765) B514765
theorem B877837 : Blo 239816 877837 := bstep (se 3 (by rfl) ⟨164594, by rfl⟩ : syracuseStep 877837 = 329189) B329189
theorem B812429 : Blo 239816 812429 := bstep (se 3 (by rfl) ⟨152330, by rfl⟩ : syracuseStep 812429 = 304661) B304661
theorem B812483 : Blo 239816 812483 := bstep (se 1 (by rfl) ⟨609362, by rfl⟩ : syracuseStep 812483 = 1218725) B1218725
theorem B517585 : Blo 239816 517585 := bstep (se 2 (by rfl) ⟨194094, by rfl⟩ : syracuseStep 517585 = 388189) B388189
theorem B288451 : Blo 239816 288451 := bstep (se 1 (by rfl) ⟨216338, by rfl⟩ : syracuseStep 288451 = 432677) B432677
theorem B812753 : Blo 239816 812753 := bstep (se 2 (by rfl) ⟨304782, by rfl⟩ : syracuseStep 812753 = 609565) B609565
theorem B517841 : Blo 239816 517841 := bstep (se 2 (by rfl) ⟨194190, by rfl⟩ : syracuseStep 517841 = 388381) B388381
theorem B616369 : Blo 239816 616369 := bstep (se 2 (by rfl) ⟨231138, by rfl⟩ : syracuseStep 616369 = 462277) B462277
theorem B616529 : Blo 239816 616529 := bstep (se 2 (by rfl) ⟨231198, by rfl⟩ : syracuseStep 616529 = 462397) B462397
theorem B3106997 : Blo 239816 3106997 := bstep (se 5 (by rfl) ⟨145640, by rfl⟩ : syracuseStep 3106997 = 291281) B291281
theorem B616643 : Blo 239816 616643 := bstep (se 1 (by rfl) ⟨462482, by rfl⟩ : syracuseStep 616643 = 924965) B924965
theorem B813293 : Blo 239816 813293 := bstep (se 3 (by rfl) ⟨152492, by rfl⟩ : syracuseStep 813293 = 304985) B304985
theorem B813347 : Blo 239816 813347 := bstep (se 1 (by rfl) ⟨610010, by rfl⟩ : syracuseStep 813347 = 1220021) B1220021
theorem B616835 : Blo 239816 616835 := bstep (se 1 (by rfl) ⟨462626, by rfl⟩ : syracuseStep 616835 = 925253) B925253
theorem B780749 : Blo 239816 780749 := bstep (se 3 (by rfl) ⟨146390, by rfl⟩ : syracuseStep 780749 = 292781) B292781
theorem B911843 : Blo 239816 911843 := bstep (se 1 (by rfl) ⟨683882, by rfl⟩ : syracuseStep 911843 = 1367765) B1367765
theorem B911857 : Blo 239816 911857 := bstep (se 2 (by rfl) ⟨341946, by rfl⟩ : syracuseStep 911857 = 683893) B683893
theorem B387587 : Blo 239816 387587 := bstep (se 1 (by rfl) ⟨290690, by rfl⟩ : syracuseStep 387587 = 581381) B581381
theorem B813617 : Blo 239816 813617 := bstep (se 2 (by rfl) ⟨305106, by rfl⟩ : syracuseStep 813617 = 610213) B610213
theorem B1305229 : Blo 239816 1305229 := bstep (se 3 (by rfl) ⟨244730, by rfl⟩ : syracuseStep 1305229 = 489461) B489461
theorem B256819 : Blo 239816 256819 := bstep (se 1 (by rfl) ⟨192614, by rfl⟩ : syracuseStep 256819 = 385229) B385229
theorem B387971 : Blo 239816 387971 := bstep (se 1 (by rfl) ⟨290978, by rfl⟩ : syracuseStep 387971 = 581957) B581957
theorem B3533765 : Blo 239816 3533765 := bstep (se 4 (by rfl) ⟨331290, by rfl⟩ : syracuseStep 3533765 = 662581) B662581
theorem B519139 : Blo 239816 519139 := bstep (se 1 (by rfl) ⟨389354, by rfl⟩ : syracuseStep 519139 = 778709) B778709
theorem B388099 : Blo 239816 388099 := bstep (se 1 (by rfl) ⟨291074, by rfl⟩ : syracuseStep 388099 = 582149) B582149
theorem B2190349 : Blo 239816 2190349 := bstep (se 3 (by rfl) ⟨410690, by rfl⟩ : syracuseStep 2190349 = 821381) B821381
theorem B814157 : Blo 239816 814157 := bstep (se 3 (by rfl) ⟨152654, by rfl⟩ : syracuseStep 814157 = 305309) B305309
theorem B814211 : Blo 239816 814211 := bstep (se 1 (by rfl) ⟨610658, by rfl⟩ : syracuseStep 814211 = 1221317) B1221317
theorem B552113 : Blo 239816 552113 := bstep (se 2 (by rfl) ⟨207042, by rfl⟩ : syracuseStep 552113 = 414085) B414085
theorem B519473 : Blo 239816 519473 := bstep (se 2 (by rfl) ⟨194802, by rfl⟩ : syracuseStep 519473 = 389605) B389605
theorem B1305989 : Blo 239816 1305989 := bstep (se 4 (by rfl) ⟨122436, by rfl⟩ : syracuseStep 1305989 = 244873) B244873
theorem B814481 : Blo 239816 814481 := bstep (se 2 (by rfl) ⟨305430, by rfl⟩ : syracuseStep 814481 = 610861) B610861
theorem B748945 : Blo 239816 748945 := bstep (se 2 (by rfl) ⟨280854, by rfl⟩ : syracuseStep 748945 = 561709) B561709
theorem B257699 : Blo 239816 257699 := bstep (se 1 (by rfl) ⟨193274, by rfl⟩ : syracuseStep 257699 = 386549) B386549
theorem B388817 : Blo 239816 388817 := bstep (se 2 (by rfl) ⟨145806, by rfl⟩ : syracuseStep 388817 = 291613) B291613
theorem B257827 : Blo 239816 257827 := bstep (se 1 (by rfl) ⟨193370, by rfl⟩ : syracuseStep 257827 = 386741) B386741
theorem B5926769 : Blo 239816 5926769 := bstep (se 2 (by rfl) ⟨2222538, by rfl⟩ : syracuseStep 5926769 = 4445077) B4445077
theorem B389009 : Blo 239816 389009 := bstep (se 2 (by rfl) ⟨145878, by rfl⟩ : syracuseStep 389009 = 291757) B291757
theorem B683939 : Blo 239816 683939 := bstep (se 1 (by rfl) ⟨512954, by rfl⟩ : syracuseStep 683939 = 1025909) B1025909
theorem B913315 : Blo 239816 913315 := bstep (se 1 (by rfl) ⟨684986, by rfl⟩ : syracuseStep 913315 = 1369973) B1369973
theorem B815021 : Blo 239816 815021 := bstep (se 3 (by rfl) ⟨152816, by rfl⟩ : syracuseStep 815021 = 305633) B305633
theorem B1732549 : Blo 239816 1732549 := bstep (se 4 (by rfl) ⟨162426, by rfl⟩ : syracuseStep 1732549 = 324853) B324853
theorem B815075 : Blo 239816 815075 := bstep (se 1 (by rfl) ⟨611306, by rfl⟩ : syracuseStep 815075 = 1222613) B1222613
theorem B815345 : Blo 239816 815345 := bstep (se 2 (by rfl) ⟨305754, by rfl⟩ : syracuseStep 815345 = 611509) B611509
theorem B880931 : Blo 239816 880931 := bstep (se 1 (by rfl) ⟨660698, by rfl⟩ : syracuseStep 880931 = 1321397) B1321397
theorem B4714805 : Blo 239816 4714805 := bstep (se 5 (by rfl) ⟨221006, by rfl⟩ : syracuseStep 4714805 = 442013) B442013
theorem B520643 : Blo 239816 520643 := bstep (se 1 (by rfl) ⟨390482, by rfl⟩ : syracuseStep 520643 = 780965) B780965
theorem B258643 : Blo 239816 258643 := bstep (se 1 (by rfl) ⟨193982, by rfl⟩ : syracuseStep 258643 = 387965) B387965
theorem B488035 : Blo 239816 488035 := bstep (se 1 (by rfl) ⟨366026, by rfl⟩ : syracuseStep 488035 = 732053) B732053
theorem B815885 : Blo 239816 815885 := bstep (se 3 (by rfl) ⟨152978, by rfl⟩ : syracuseStep 815885 = 305957) B305957
theorem B1700621 : Blo 239816 1700621 := bstep (se 3 (by rfl) ⟨318866, by rfl⟩ : syracuseStep 1700621 = 637733) B637733
theorem B455473 : Blo 239816 455473 := bstep (se 2 (by rfl) ⟨170802, by rfl⟩ : syracuseStep 455473 = 341605) B341605
theorem B5206837 : Blo 239816 5206837 := bstep (se 5 (by rfl) ⟨244070, by rfl⟩ : syracuseStep 5206837 = 488141) B488141
theorem B815939 : Blo 239816 815939 := bstep (se 1 (by rfl) ⟨611954, by rfl⟩ : syracuseStep 815939 = 1223909) B1223909
theorem B816209 : Blo 239816 816209 := bstep (se 2 (by rfl) ⟨306078, by rfl⟩ : syracuseStep 816209 = 612157) B612157
theorem B685169 : Blo 239816 685169 := bstep (se 2 (by rfl) ⟨256938, by rfl⟩ : syracuseStep 685169 = 513877) B513877
theorem B324929 : Blo 239816 324929 := bstep (se 2 (by rfl) ⟨121848, by rfl⟩ : syracuseStep 324929 = 243697) B243697
theorem B1537379 : Blo 239816 1537379 := bstep (se 1 (by rfl) ⟨1153034, by rfl⟩ : syracuseStep 1537379 = 2306069) B2306069
theorem B783857 : Blo 239816 783857 := bstep (se 2 (by rfl) ⟨293946, by rfl⟩ : syracuseStep 783857 = 587893) B587893
theorem B816749 : Blo 239816 816749 := bstep (se 3 (by rfl) ⟨153140, by rfl⟩ : syracuseStep 816749 = 306281) B306281
theorem B816803 : Blo 239816 816803 := bstep (se 1 (by rfl) ⟨612602, by rfl⟩ : syracuseStep 816803 = 1225205) B1225205
theorem B1374029 : Blo 239816 1374029 := bstep (se 3 (by rfl) ⟨257630, by rfl⟩ : syracuseStep 1374029 = 515261) B515261
theorem B456529 : Blo 239816 456529 := bstep (se 2 (by rfl) ⟨171198, by rfl⟩ : syracuseStep 456529 = 342397) B342397
theorem B325459 : Blo 239816 325459 := bstep (se 1 (by rfl) ⟨244094, by rfl⟩ : syracuseStep 325459 = 488189) B488189
theorem B817073 : Blo 239816 817073 := bstep (se 2 (by rfl) ⟨306402, by rfl⟩ : syracuseStep 817073 = 612805) B612805
theorem B292819 : Blo 239816 292819 := bstep (se 1 (by rfl) ⟨219614, by rfl⟩ : syracuseStep 292819 = 439229) B439229
theorem B915533 : Blo 239816 915533 := bstep (se 3 (by rfl) ⟨171662, by rfl⟩ : syracuseStep 915533 = 343325) B343325
theorem B7108721 : Blo 239816 7108721 := bstep (se 2 (by rfl) ⟨2665770, by rfl⟩ : syracuseStep 7108721 = 5331541) B5331541
theorem B1734797 : Blo 239816 1734797 := bstep (se 3 (by rfl) ⟨325274, by rfl⟩ : syracuseStep 1734797 = 650549) B650549
theorem B456931 : Blo 239816 456931 := bstep (se 1 (by rfl) ⟨342698, by rfl⟩ : syracuseStep 456931 = 685397) B685397
theorem B456977 : Blo 239816 456977 := bstep (se 2 (by rfl) ⟨171366, by rfl⟩ : syracuseStep 456977 = 342733) B342733
theorem B391475 : Blo 239816 391475 := bstep (se 1 (by rfl) ⟨293606, by rfl⟩ : syracuseStep 391475 = 587213) B587213
theorem B817613 : Blo 239816 817613 := bstep (se 3 (by rfl) ⟨153302, by rfl⟩ : syracuseStep 817613 = 306605) B306605
theorem B653795 : Blo 239816 653795 := bstep (se 1 (by rfl) ⟨490346, by rfl⟩ : syracuseStep 653795 = 980693) B980693
theorem B817667 : Blo 239816 817667 := bstep (se 1 (by rfl) ⟨613250, by rfl⟩ : syracuseStep 817667 = 1226501) B1226501
theorem B686627 : Blo 239816 686627 := bstep (se 1 (by rfl) ⟨514970, by rfl⟩ : syracuseStep 686627 = 1029941) B1029941
theorem B457265 : Blo 239816 457265 := bstep (se 2 (by rfl) ⟨171474, by rfl⟩ : syracuseStep 457265 = 342949) B342949
theorem B391889 : Blo 239816 391889 := bstep (se 2 (by rfl) ⟨146958, by rfl⟩ : syracuseStep 391889 = 293917) B293917
theorem B2751245 : Blo 239816 2751245 := bstep (se 3 (by rfl) ⟨515858, by rfl⟩ : syracuseStep 2751245 = 1031717) B1031717
theorem B817937 : Blo 239816 817937 := bstep (se 2 (by rfl) ⟨306726, by rfl⟩ : syracuseStep 817937 = 613453) B613453
theorem B555875 : Blo 239816 555875 := bstep (se 1 (by rfl) ⟨416906, by rfl⟩ : syracuseStep 555875 = 833813) B833813
theorem B326659 : Blo 239816 326659 := bstep (se 1 (by rfl) ⟨244994, by rfl⟩ : syracuseStep 326659 = 489989) B489989
theorem B457987 : Blo 239816 457987 := bstep (se 1 (by rfl) ⟨343490, by rfl⟩ : syracuseStep 457987 = 686981) B686981
theorem B818477 : Blo 239816 818477 := bstep (se 3 (by rfl) ⟨153464, by rfl⟩ : syracuseStep 818477 = 306929) B306929
theorem B359729 : Blo 239816 359729 := bstep (se 2 (by rfl) ⟨134898, by rfl⟩ : syracuseStep 359729 = 269797) B269797
theorem B359747 : Blo 239816 359747 := bstep (se 1 (by rfl) ⟨269810, by rfl⟩ : syracuseStep 359747 = 539621) B539621
theorem B687437 : Blo 239816 687437 := bstep (se 3 (by rfl) ⟨128894, by rfl⟩ : syracuseStep 687437 = 257789) B257789
theorem B359777 : Blo 239816 359777 := bstep (se 2 (by rfl) ⟨134916, by rfl⟩ : syracuseStep 359777 = 269833) B269833
theorem B818531 : Blo 239816 818531 := bstep (se 1 (by rfl) ⟨613898, by rfl⟩ : syracuseStep 818531 = 1227797) B1227797
theorem B4423025 : Blo 239816 4423025 := bstep (se 2 (by rfl) ⟨1658634, by rfl⟩ : syracuseStep 4423025 = 3317269) B3317269
theorem B359795 : Blo 239816 359795 := bstep (se 1 (by rfl) ⟨269846, by rfl⟩ : syracuseStep 359795 = 539693) B539693
theorem B359825 : Blo 239816 359825 := bstep (se 2 (by rfl) ⟨134934, by rfl⟩ : syracuseStep 359825 = 269869) B269869
theorem B359843 : Blo 239816 359843 := bstep (se 1 (by rfl) ⟨269882, by rfl⟩ : syracuseStep 359843 = 539765) B539765
theorem B1244593 : Blo 239816 1244593 := bstep (se 2 (by rfl) ⟨466722, by rfl⟩ : syracuseStep 1244593 = 933445) B933445
theorem B359873 : Blo 239816 359873 := bstep (se 2 (by rfl) ⟨134952, by rfl⟩ : syracuseStep 359873 = 269905) B269905
theorem B490961 : Blo 239816 490961 := bstep (se 2 (by rfl) ⟨184110, by rfl⟩ : syracuseStep 490961 = 368221) B368221
theorem B359891 : Blo 239816 359891 := bstep (se 1 (by rfl) ⟨269918, by rfl⟩ : syracuseStep 359891 = 539837) B539837
theorem B359921 : Blo 239816 359921 := bstep (se 2 (by rfl) ⟨134970, by rfl⟩ : syracuseStep 359921 = 269941) B269941
theorem B359939 : Blo 239816 359939 := bstep (se 1 (by rfl) ⟨269954, by rfl⟩ : syracuseStep 359939 = 539909) B539909
theorem B687629 : Blo 239816 687629 := bstep (se 3 (by rfl) ⟨128930, by rfl⟩ : syracuseStep 687629 = 257861) B257861
theorem B359969 : Blo 239816 359969 := bstep (se 2 (by rfl) ⟨134988, by rfl⟩ : syracuseStep 359969 = 269977) B269977
theorem B261667 : Blo 239816 261667 := bstep (se 1 (by rfl) ⟨196250, by rfl⟩ : syracuseStep 261667 = 392501) B392501
theorem B359987 : Blo 239816 359987 := bstep (se 1 (by rfl) ⟨269990, by rfl⟩ : syracuseStep 359987 = 539981) B539981
theorem B360017 : Blo 239816 360017 := bstep (se 2 (by rfl) ⟨135006, by rfl⟩ : syracuseStep 360017 = 270013) B270013
theorem B360035 : Blo 239816 360035 := bstep (se 1 (by rfl) ⟨270026, by rfl⟩ : syracuseStep 360035 = 540053) B540053
theorem B818801 : Blo 239816 818801 := bstep (se 2 (by rfl) ⟨307050, by rfl⟩ : syracuseStep 818801 = 614101) B614101
theorem B360065 : Blo 239816 360065 := bstep (se 2 (by rfl) ⟨135024, by rfl⟩ : syracuseStep 360065 = 270049) B270049
theorem B360083 : Blo 239816 360083 := bstep (se 1 (by rfl) ⟨270062, by rfl⟩ : syracuseStep 360083 = 540125) B540125
theorem B360113 : Blo 239816 360113 := bstep (se 2 (by rfl) ⟨135042, by rfl⟩ : syracuseStep 360113 = 270085) B270085
theorem B360131 : Blo 239816 360131 := bstep (se 1 (by rfl) ⟨270098, by rfl⟩ : syracuseStep 360131 = 540197) B540197
theorem B458435 : Blo 239816 458435 := bstep (se 1 (by rfl) ⟨343826, by rfl⟩ : syracuseStep 458435 = 687653) B687653
theorem B360161 : Blo 239816 360161 := bstep (se 2 (by rfl) ⟨135060, by rfl⟩ : syracuseStep 360161 = 270121) B270121
theorem B360179 : Blo 239816 360179 := bstep (se 1 (by rfl) ⟨270134, by rfl⟩ : syracuseStep 360179 = 540269) B540269
theorem B360209 : Blo 239816 360209 := bstep (se 2 (by rfl) ⟨135078, by rfl⟩ : syracuseStep 360209 = 270157) B270157
theorem B360227 : Blo 239816 360227 := bstep (se 1 (by rfl) ⟨270170, by rfl⟩ : syracuseStep 360227 = 540341) B540341
theorem B2817845 : Blo 239816 2817845 := bstep (se 5 (by rfl) ⟨132086, by rfl⟩ : syracuseStep 2817845 = 264173) B264173
theorem B360257 : Blo 239816 360257 := bstep (se 2 (by rfl) ⟨135096, by rfl⟩ : syracuseStep 360257 = 270193) B270193
theorem B360275 : Blo 239816 360275 := bstep (se 1 (by rfl) ⟨270206, by rfl⟩ : syracuseStep 360275 = 540413) B540413
theorem B360305 : Blo 239816 360305 := bstep (se 2 (by rfl) ⟨135114, by rfl⟩ : syracuseStep 360305 = 270229) B270229
theorem B360323 : Blo 239816 360323 := bstep (se 1 (by rfl) ⟨270242, by rfl⟩ : syracuseStep 360323 = 540485) B540485
theorem B360353 : Blo 239816 360353 := bstep (se 2 (by rfl) ⟨135132, by rfl⟩ : syracuseStep 360353 = 270265) B270265
theorem B360371 : Blo 239816 360371 := bstep (se 1 (by rfl) ⟨270278, by rfl⟩ : syracuseStep 360371 = 540557) B540557
theorem B360401 : Blo 239816 360401 := bstep (se 2 (by rfl) ⟨135150, by rfl⟩ : syracuseStep 360401 = 270301) B270301
theorem B360419 : Blo 239816 360419 := bstep (se 1 (by rfl) ⟨270314, by rfl⟩ : syracuseStep 360419 = 540629) B540629
theorem B458723 : Blo 239816 458723 := bstep (se 1 (by rfl) ⟨344042, by rfl⟩ : syracuseStep 458723 = 688085) B688085
theorem B557057 : Blo 239816 557057 := bstep (se 2 (by rfl) ⟨208896, by rfl⟩ : syracuseStep 557057 = 417793) B417793
theorem B917507 : Blo 239816 917507 := bstep (se 1 (by rfl) ⟨688130, by rfl⟩ : syracuseStep 917507 = 1376261) B1376261
theorem B360473 : Blo 239816 360473 := bstep (se 2 (by rfl) ⟨135177, by rfl⟩ : syracuseStep 360473 = 270355) B270355
theorem B458777 : Blo 239816 458777 := bstep (se 2 (by rfl) ⟨172041, by rfl⟩ : syracuseStep 458777 = 344083) B344083
theorem B360587 : Blo 239816 360587 := bstep (se 1 (by rfl) ⟨270440, by rfl⟩ : syracuseStep 360587 = 540881) B540881
theorem B360599 : Blo 239816 360599 := bstep (se 1 (by rfl) ⟨270449, by rfl⟩ : syracuseStep 360599 = 540899) B540899
theorem B360665 : Blo 239816 360665 := bstep (se 2 (by rfl) ⟨135249, by rfl⟩ : syracuseStep 360665 = 270499) B270499
theorem B360779 : Blo 239816 360779 := bstep (se 1 (by rfl) ⟨270584, by rfl⟩ : syracuseStep 360779 = 541169) B541169
theorem B360791 : Blo 239816 360791 := bstep (se 1 (by rfl) ⟨270593, by rfl⟩ : syracuseStep 360791 = 541187) B541187
theorem B360857 : Blo 239816 360857 := bstep (se 2 (by rfl) ⟨135321, by rfl⟩ : syracuseStep 360857 = 270643) B270643
theorem B917963 : Blo 239816 917963 := bstep (se 1 (by rfl) ⟨688472, by rfl⟩ : syracuseStep 917963 = 1376945) B1376945
theorem B328151 : Blo 239816 328151 := bstep (se 1 (by rfl) ⟨246113, by rfl⟩ : syracuseStep 328151 = 492227) B492227
theorem B360971 : Blo 239816 360971 := bstep (se 1 (by rfl) ⟨270728, by rfl⟩ : syracuseStep 360971 = 541457) B541457
theorem B360983 : Blo 239816 360983 := bstep (se 1 (by rfl) ⟨270737, by rfl⟩ : syracuseStep 360983 = 541475) B541475
theorem B361049 : Blo 239816 361049 := bstep (se 2 (by rfl) ⟨135393, by rfl⟩ : syracuseStep 361049 = 270787) B270787
theorem B1835621 : Blo 239816 1835621 := bstep (se 4 (by rfl) ⟨172089, by rfl⟩ : syracuseStep 1835621 = 344179) B344179
theorem B918161 : Blo 239816 918161 := bstep (se 2 (by rfl) ⟨344310, by rfl⟩ : syracuseStep 918161 = 688621) B688621
theorem B361163 : Blo 239816 361163 := bstep (se 1 (by rfl) ⟨270872, by rfl⟩ : syracuseStep 361163 = 541745) B541745
theorem B656075 : Blo 239816 656075 := bstep (se 1 (by rfl) ⟨492056, by rfl⟩ : syracuseStep 656075 = 984113) B984113
theorem B361175 : Blo 239816 361175 := bstep (se 1 (by rfl) ⟨270881, by rfl⟩ : syracuseStep 361175 = 541763) B541763
theorem B361241 : Blo 239816 361241 := bstep (se 2 (by rfl) ⟨135465, by rfl⟩ : syracuseStep 361241 = 270931) B270931
theorem B820043 : Blo 239816 820043 := bstep (se 1 (by rfl) ⟨615032, by rfl⟩ : syracuseStep 820043 = 1230065) B1230065
theorem B361355 : Blo 239816 361355 := bstep (se 1 (by rfl) ⟨271016, by rfl⟩ : syracuseStep 361355 = 542033) B542033
theorem B1541015 : Blo 239816 1541015 := bstep (se 1 (by rfl) ⟨1155761, by rfl⟩ : syracuseStep 1541015 = 2311523) B2311523
theorem B361367 : Blo 239816 361367 := bstep (se 1 (by rfl) ⟨271025, by rfl⟩ : syracuseStep 361367 = 542051) B542051
theorem B361433 : Blo 239816 361433 := bstep (se 2 (by rfl) ⟨135537, by rfl⟩ : syracuseStep 361433 = 271075) B271075
theorem B361547 : Blo 239816 361547 := bstep (se 1 (by rfl) ⟨271160, by rfl⟩ : syracuseStep 361547 = 542321) B542321
theorem B1836107 : Blo 239816 1836107 := bstep (se 1 (by rfl) ⟨1377080, by rfl⟩ : syracuseStep 1836107 = 2754161) B2754161
theorem B361559 : Blo 239816 361559 := bstep (se 1 (by rfl) ⟨271169, by rfl⟩ : syracuseStep 361559 = 542339) B542339
theorem B820313 : Blo 239816 820313 := bstep (se 2 (by rfl) ⟨307617, by rfl⟩ : syracuseStep 820313 = 615235) B615235
theorem B361625 : Blo 239816 361625 := bstep (se 2 (by rfl) ⟨135609, by rfl⟩ : syracuseStep 361625 = 271219) B271219
theorem B361739 : Blo 239816 361739 := bstep (se 1 (by rfl) ⟨271304, by rfl⟩ : syracuseStep 361739 = 542609) B542609
theorem B361751 : Blo 239816 361751 := bstep (se 1 (by rfl) ⟨271313, by rfl⟩ : syracuseStep 361751 = 542627) B542627
theorem B1246529 : Blo 239816 1246529 := bstep (se 2 (by rfl) ⟨467448, by rfl⟩ : syracuseStep 1246529 = 934897) B934897
theorem B361817 : Blo 239816 361817 := bstep (se 2 (by rfl) ⟨135681, by rfl⟩ : syracuseStep 361817 = 271363) B271363
theorem B918935 : Blo 239816 918935 := bstep (se 1 (by rfl) ⟨689201, by rfl⟩ : syracuseStep 918935 = 1378403) B1378403
theorem B361931 : Blo 239816 361931 := bstep (se 1 (by rfl) ⟨271448, by rfl⟩ : syracuseStep 361931 = 542897) B542897
theorem B460235 : Blo 239816 460235 := bstep (se 1 (by rfl) ⟨345176, by rfl⟩ : syracuseStep 460235 = 690353) B690353
theorem B361943 : Blo 239816 361943 := bstep (se 1 (by rfl) ⟨271457, by rfl⟩ : syracuseStep 361943 = 542915) B542915
theorem B362009 : Blo 239816 362009 := bstep (se 2 (by rfl) ⟨135753, by rfl⟩ : syracuseStep 362009 = 271507) B271507
theorem B919133 : Blo 239816 919133 := bstep (se 3 (by rfl) ⟨172337, by rfl⟩ : syracuseStep 919133 = 344675) B344675
theorem B460417 : Blo 239816 460417 := bstep (se 2 (by rfl) ⟨172656, by rfl⟩ : syracuseStep 460417 = 345313) B345313
theorem B362123 : Blo 239816 362123 := bstep (se 1 (by rfl) ⟨271592, by rfl⟩ : syracuseStep 362123 = 543185) B543185
theorem B362135 : Blo 239816 362135 := bstep (se 1 (by rfl) ⟨271601, by rfl⟩ : syracuseStep 362135 = 543203) B543203
theorem B1377971 : Blo 239816 1377971 := bstep (se 1 (by rfl) ⟨1033478, by rfl⟩ : syracuseStep 1377971 = 2066957) B2066957
theorem B493249 : Blo 239816 493249 := bstep (se 2 (by rfl) ⟨184968, by rfl⟩ : syracuseStep 493249 = 369937) B369937
theorem B362201 : Blo 239816 362201 := bstep (se 2 (by rfl) ⟨135825, by rfl⟩ : syracuseStep 362201 = 271651) B271651
theorem B821015 : Blo 239816 821015 := bstep (se 1 (by rfl) ⟨615761, by rfl⟩ : syracuseStep 821015 = 1231523) B1231523
theorem B362315 : Blo 239816 362315 := bstep (se 1 (by rfl) ⟨271736, by rfl⟩ : syracuseStep 362315 = 543473) B543473
theorem B362327 : Blo 239816 362327 := bstep (se 1 (by rfl) ⟨271745, by rfl⟩ : syracuseStep 362327 = 543491) B543491
theorem B493427 : Blo 239816 493427 := bstep (se 1 (by rfl) ⟨370070, by rfl⟩ : syracuseStep 493427 = 740141) B740141
theorem B362393 : Blo 239816 362393 := bstep (se 2 (by rfl) ⟨135897, by rfl⟩ : syracuseStep 362393 = 271795) B271795
theorem B690113 : Blo 239816 690113 := bstep (se 2 (by rfl) ⟨258792, by rfl⟩ : syracuseStep 690113 = 517585) B517585
theorem B362507 : Blo 239816 362507 := bstep (se 1 (by rfl) ⟨271880, by rfl⟩ : syracuseStep 362507 = 543761) B543761
theorem B362519 : Blo 239816 362519 := bstep (se 1 (by rfl) ⟨271889, by rfl⟩ : syracuseStep 362519 = 543779) B543779
theorem B690227 : Blo 239816 690227 := bstep (se 1 (by rfl) ⟨517670, by rfl⟩ : syracuseStep 690227 = 1035341) B1035341
theorem B460865 : Blo 239816 460865 := bstep (se 2 (by rfl) ⟨172824, by rfl⟩ : syracuseStep 460865 = 345649) B345649
theorem B7473221 : Blo 239816 7473221 := bstep (se 4 (by rfl) ⟨700614, by rfl⟩ : syracuseStep 7473221 = 1401229) B1401229
theorem B362585 : Blo 239816 362585 := bstep (se 2 (by rfl) ⟨135969, by rfl⟩ : syracuseStep 362585 = 271939) B271939
theorem B1312861 : Blo 239816 1312861 := bstep (se 3 (by rfl) ⟨246161, by rfl⟩ : syracuseStep 1312861 = 492323) B492323
theorem B362699 : Blo 239816 362699 := bstep (se 1 (by rfl) ⟨272024, by rfl⟩ : syracuseStep 362699 = 544049) B544049
theorem B362711 : Blo 239816 362711 := bstep (se 1 (by rfl) ⟨272033, by rfl⟩ : syracuseStep 362711 = 544067) B544067
theorem B362777 : Blo 239816 362777 := bstep (se 2 (by rfl) ⟨136041, by rfl⟩ : syracuseStep 362777 = 272083) B272083
theorem B821555 : Blo 239816 821555 := bstep (se 1 (by rfl) ⟨616166, by rfl⟩ : syracuseStep 821555 = 1232333) B1232333
theorem B362891 : Blo 239816 362891 := bstep (se 1 (by rfl) ⟨272168, by rfl⟩ : syracuseStep 362891 = 544337) B544337
theorem B362903 : Blo 239816 362903 := bstep (se 1 (by rfl) ⟨272177, by rfl⟩ : syracuseStep 362903 = 544355) B544355
theorem B461207 : Blo 239816 461207 := bstep (se 1 (by rfl) ⟨345905, by rfl⟩ : syracuseStep 461207 = 691811) B691811
theorem B1182131 : Blo 239816 1182131 := bstep (se 1 (by rfl) ⟨886598, by rfl⟩ : syracuseStep 1182131 = 1773197) B1773197
theorem B362969 : Blo 239816 362969 := bstep (se 2 (by rfl) ⟨136113, by rfl⟩ : syracuseStep 362969 = 272227) B272227
theorem B821825 : Blo 239816 821825 := bstep (se 2 (by rfl) ⟨308184, by rfl⟩ : syracuseStep 821825 = 616369) B616369
theorem B363083 : Blo 239816 363083 := bstep (se 1 (by rfl) ⟨272312, by rfl⟩ : syracuseStep 363083 = 544625) B544625
theorem B363095 : Blo 239816 363095 := bstep (se 1 (by rfl) ⟨272321, by rfl⟩ : syracuseStep 363095 = 544643) B544643
theorem B4983389 : Blo 239816 4983389 := bstep (se 3 (by rfl) ⟨934385, by rfl⟩ : syracuseStep 4983389 = 1868771) B1868771
theorem B363161 : Blo 239816 363161 := bstep (se 2 (by rfl) ⟨136185, by rfl⟩ : syracuseStep 363161 = 272371) B272371
theorem B363275 : Blo 239816 363275 := bstep (se 1 (by rfl) ⟨272456, by rfl⟩ : syracuseStep 363275 = 544913) B544913
theorem B363287 : Blo 239816 363287 := bstep (se 1 (by rfl) ⟨272465, by rfl⟩ : syracuseStep 363287 = 544931) B544931
theorem B363353 : Blo 239816 363353 := bstep (se 2 (by rfl) ⟨136257, by rfl⟩ : syracuseStep 363353 = 272515) B272515
theorem B985945 : Blo 239816 985945 := bstep (se 2 (by rfl) ⟨369729, by rfl⟩ : syracuseStep 985945 = 739459) B739459
theorem B363467 : Blo 239816 363467 := bstep (se 1 (by rfl) ⟨272600, by rfl⟩ : syracuseStep 363467 = 545201) B545201
theorem B363479 : Blo 239816 363479 := bstep (se 1 (by rfl) ⟨272609, by rfl⟩ : syracuseStep 363479 = 545219) B545219
theorem B363545 : Blo 239816 363545 := bstep (se 2 (by rfl) ⟨136329, by rfl⟩ : syracuseStep 363545 = 272659) B272659
theorem B2755619 : Blo 239816 2755619 := bstep (se 1 (by rfl) ⟨2066714, by rfl⟩ : syracuseStep 2755619 = 4133429) B4133429
theorem B461875 : Blo 239816 461875 := bstep (se 1 (by rfl) ⟨346406, by rfl⟩ : syracuseStep 461875 = 692813) B692813
theorem B822365 : Blo 239816 822365 := bstep (se 3 (by rfl) ⟨154193, by rfl⟩ : syracuseStep 822365 = 308387) B308387
theorem B1379429 : Blo 239816 1379429 := bstep (se 4 (by rfl) ⟨129321, by rfl⟩ : syracuseStep 1379429 = 258643) B258643
theorem B363659 : Blo 239816 363659 := bstep (se 1 (by rfl) ⟨272744, by rfl⟩ : syracuseStep 363659 = 545489) B545489
theorem B363671 : Blo 239816 363671 := bstep (se 1 (by rfl) ⟨272753, by rfl⟩ : syracuseStep 363671 = 545507) B545507
theorem B363737 : Blo 239816 363737 := bstep (se 2 (by rfl) ⟨136401, by rfl⟩ : syracuseStep 363737 = 272803) B272803
theorem B1215809 : Blo 239816 1215809 := bstep (se 2 (by rfl) ⟨455928, by rfl⟩ : syracuseStep 1215809 = 911857) B911857
theorem B363851 : Blo 239816 363851 := bstep (se 1 (by rfl) ⟨272888, by rfl⟩ : syracuseStep 363851 = 545777) B545777
theorem B363863 : Blo 239816 363863 := bstep (se 1 (by rfl) ⟨272897, by rfl⟩ : syracuseStep 363863 = 545795) B545795
theorem B363929 : Blo 239816 363929 := bstep (se 2 (by rfl) ⟨136473, by rfl⟩ : syracuseStep 363929 = 272947) B272947
theorem B462323 : Blo 239816 462323 := bstep (se 1 (by rfl) ⟨346742, by rfl⟩ : syracuseStep 462323 = 693485) B693485
theorem B921091 : Blo 239816 921091 := bstep (se 1 (by rfl) ⟨690818, by rfl⟩ : syracuseStep 921091 = 1381637) B1381637
theorem B364043 : Blo 239816 364043 := bstep (se 1 (by rfl) ⟨273032, by rfl⟩ : syracuseStep 364043 = 546065) B546065
theorem B1740305 : Blo 239816 1740305 := bstep (se 2 (by rfl) ⟨652614, by rfl⟩ : syracuseStep 1740305 = 1305229) B1305229
theorem B364055 : Blo 239816 364055 := bstep (se 1 (by rfl) ⟨273041, by rfl⟩ : syracuseStep 364055 = 546083) B546083
theorem B462361 : Blo 239816 462361 := bstep (se 2 (by rfl) ⟨173385, by rfl⟩ : syracuseStep 462361 = 346771) B346771
theorem B364121 : Blo 239816 364121 := bstep (se 2 (by rfl) ⟨136545, by rfl⟩ : syracuseStep 364121 = 273091) B273091
theorem B364235 : Blo 239816 364235 := bstep (se 1 (by rfl) ⟨273176, by rfl⟩ : syracuseStep 364235 = 546353) B546353
theorem B364247 : Blo 239816 364247 := bstep (se 1 (by rfl) ⟨273185, by rfl⟩ : syracuseStep 364247 = 546371) B546371
theorem B364313 : Blo 239816 364313 := bstep (se 2 (by rfl) ⟨136617, by rfl⟩ : syracuseStep 364313 = 273235) B273235
theorem B921395 : Blo 239816 921395 := bstep (se 1 (by rfl) ⟨691046, by rfl⟩ : syracuseStep 921395 = 1382093) B1382093
theorem B2068355 : Blo 239816 2068355 := bstep (se 1 (by rfl) ⟨1551266, by rfl⟩ : syracuseStep 2068355 = 3102533) B3102533
theorem B364427 : Blo 239816 364427 := bstep (se 1 (by rfl) ⟨273320, by rfl⟩ : syracuseStep 364427 = 546641) B546641
theorem B364439 : Blo 239816 364439 := bstep (se 1 (by rfl) ⟨273329, by rfl⟩ : syracuseStep 364439 = 546659) B546659
theorem B364505 : Blo 239816 364505 := bstep (se 2 (by rfl) ⟨136689, by rfl⟩ : syracuseStep 364505 = 273379) B273379
theorem B462809 : Blo 239816 462809 := bstep (se 2 (by rfl) ⟨173553, by rfl⟩ : syracuseStep 462809 = 347107) B347107
theorem B2920465 : Blo 239816 2920465 := bstep (se 2 (by rfl) ⟨1095174, by rfl⟩ : syracuseStep 2920465 = 2190349) B2190349
theorem B5279813 : Blo 239816 5279813 := bstep (se 4 (by rfl) ⟨494982, by rfl⟩ : syracuseStep 5279813 = 989965) B989965
theorem B364619 : Blo 239816 364619 := bstep (se 1 (by rfl) ⟨273464, by rfl⟩ : syracuseStep 364619 = 546929) B546929
theorem B364631 : Blo 239816 364631 := bstep (se 1 (by rfl) ⟨273473, by rfl⟩ : syracuseStep 364631 = 546947) B546947
theorem B364697 : Blo 239816 364697 := bstep (se 2 (by rfl) ⟨136761, by rfl⟩ : syracuseStep 364697 = 273523) B273523
theorem B364811 : Blo 239816 364811 := bstep (se 1 (by rfl) ⟨273608, by rfl⟩ : syracuseStep 364811 = 547217) B547217
theorem B364823 : Blo 239816 364823 := bstep (se 1 (by rfl) ⟨273617, by rfl⟩ : syracuseStep 364823 = 547235) B547235
theorem B364889 : Blo 239816 364889 := bstep (se 2 (by rfl) ⟨136833, by rfl⟩ : syracuseStep 364889 = 273667) B273667
theorem B922049 : Blo 239816 922049 := bstep (se 2 (by rfl) ⟨345768, by rfl⟩ : syracuseStep 922049 = 691537) B691537
theorem B365003 : Blo 239816 365003 := bstep (se 1 (by rfl) ⟨273752, by rfl⟩ : syracuseStep 365003 = 547505) B547505
theorem B365015 : Blo 239816 365015 := bstep (se 1 (by rfl) ⟨273761, by rfl⟩ : syracuseStep 365015 = 547523) B547523
theorem B365081 : Blo 239816 365081 := bstep (se 2 (by rfl) ⟨136905, by rfl⟩ : syracuseStep 365081 = 273811) B273811
theorem B365195 : Blo 239816 365195 := bstep (se 1 (by rfl) ⟨273896, by rfl⟩ : syracuseStep 365195 = 547793) B547793
theorem B365207 : Blo 239816 365207 := bstep (se 1 (by rfl) ⟨273905, by rfl⟩ : syracuseStep 365207 = 547811) B547811
theorem B2200243 : Blo 239816 2200243 := bstep (se 1 (by rfl) ⟨1650182, by rfl⟩ : syracuseStep 2200243 = 3300365) B3300365
theorem B365273 : Blo 239816 365273 := bstep (se 2 (by rfl) ⟨136977, by rfl⟩ : syracuseStep 365273 = 273955) B273955
theorem B627521 : Blo 239816 627521 := bstep (se 2 (by rfl) ⟨235320, by rfl⟩ : syracuseStep 627521 = 470641) B470641
theorem B365387 : Blo 239816 365387 := bstep (se 1 (by rfl) ⟨274040, by rfl⟩ : syracuseStep 365387 = 548081) B548081
theorem B365399 : Blo 239816 365399 := bstep (se 1 (by rfl) ⟨274049, by rfl⟩ : syracuseStep 365399 = 548099) B548099
theorem B693143 : Blo 239816 693143 := bstep (se 1 (by rfl) ⟨519857, by rfl⟩ : syracuseStep 693143 = 1039715) B1039715
theorem B365465 : Blo 239816 365465 := bstep (se 2 (by rfl) ⟨137049, by rfl⟩ : syracuseStep 365465 = 274099) B274099
theorem B365579 : Blo 239816 365579 := bstep (se 1 (by rfl) ⟨274184, by rfl⟩ : syracuseStep 365579 = 548369) B548369
theorem B365591 : Blo 239816 365591 := bstep (se 1 (by rfl) ⟨274193, by rfl⟩ : syracuseStep 365591 = 548387) B548387
theorem B3118115 : Blo 239816 3118115 := bstep (se 1 (by rfl) ⟨2338586, by rfl⟩ : syracuseStep 3118115 = 4677173) B4677173
theorem B365657 : Blo 239816 365657 := bstep (se 2 (by rfl) ⟨137121, by rfl⟩ : syracuseStep 365657 = 274243) B274243
theorem B1217753 : Blo 239816 1217753 := bstep (se 2 (by rfl) ⟨456657, by rfl⟩ : syracuseStep 1217753 = 913315) B913315
theorem B1644077 : Blo 239816 1644077 := bstep (se 3 (by rfl) ⟨308264, by rfl⟩ : syracuseStep 1644077 = 616529) B616529
theorem B923309 : Blo 239816 923309 := bstep (se 3 (by rfl) ⟨173120, by rfl⟩ : syracuseStep 923309 = 346241) B346241
theorem B923339 : Blo 239816 923339 := bstep (se 1 (by rfl) ⟨692504, by rfl⟩ : syracuseStep 923339 = 1385009) B1385009
theorem B1841453 : Blo 239816 1841453 := bstep (se 3 (by rfl) ⟨345272, by rfl⟩ : syracuseStep 1841453 = 690545) B690545
theorem B923993 : Blo 239816 923993 := bstep (se 2 (by rfl) ⟨346497, by rfl⟩ : syracuseStep 923993 = 692995) B692995
theorem B924311 : Blo 239816 924311 := bstep (se 1 (by rfl) ⟨693233, by rfl⟩ : syracuseStep 924311 = 1386467) B1386467
theorem B2071331 : Blo 239816 2071331 := bstep (se 1 (by rfl) ⟨1553498, by rfl⟩ : syracuseStep 2071331 = 3106997) B3106997
theorem B1219373 : Blo 239816 1219373 := bstep (se 3 (by rfl) ⟨228632, by rfl⟩ : syracuseStep 1219373 = 457265) B457265
theorem B1317707 : Blo 239816 1317707 := bstep (se 1 (by rfl) ⟨988280, by rfl⟩ : syracuseStep 1317707 = 1976561) B1976561
theorem B498649 : Blo 239816 498649 := bstep (se 2 (by rfl) ⟨186993, by rfl⟩ : syracuseStep 498649 = 373987) B373987
theorem B2628683 : Blo 239816 2628683 := bstep (se 1 (by rfl) ⟨1971512, by rfl⟩ : syracuseStep 2628683 = 3943025) B3943025
theorem B924979 : Blo 239816 924979 := bstep (se 1 (by rfl) ⟨693734, by rfl⟩ : syracuseStep 924979 = 1387469) B1387469
theorem B368075 : Blo 239816 368075 := bstep (se 1 (by rfl) ⟨276056, by rfl⟩ : syracuseStep 368075 = 552113) B552113
theorem B269815 : Blo 239816 269815 := bstep (se 1 (by rfl) ⟨202361, by rfl⟩ : syracuseStep 269815 = 404723) B404723
theorem B269995 : Blo 239816 269995 := bstep (se 1 (by rfl) ⟨202496, by rfl⟩ : syracuseStep 269995 = 404993) B404993
theorem B270103 : Blo 239816 270103 := bstep (se 1 (by rfl) ⟨202577, by rfl⟩ : syracuseStep 270103 = 405155) B405155
theorem B433945 : Blo 239816 433945 := bstep (se 2 (by rfl) ⟨162729, by rfl⟩ : syracuseStep 433945 = 325459) B325459
theorem B270283 : Blo 239816 270283 := bstep (se 1 (by rfl) ⟨202712, by rfl⟩ : syracuseStep 270283 = 405425) B405425
theorem B1974221 : Blo 239816 1974221 := bstep (se 3 (by rfl) ⟨370166, by rfl⟩ : syracuseStep 1974221 = 740333) B740333
theorem B270391 : Blo 239816 270391 := bstep (se 1 (by rfl) ⟨202793, by rfl⟩ : syracuseStep 270391 = 405587) B405587
theorem B1974451 : Blo 239816 1974451 := bstep (se 1 (by rfl) ⟨1480838, by rfl⟩ : syracuseStep 1974451 = 2961677) B2961677
theorem B270571 : Blo 239816 270571 := bstep (se 1 (by rfl) ⟨202928, by rfl⟩ : syracuseStep 270571 = 405857) B405857
theorem B270679 : Blo 239816 270679 := bstep (se 1 (by rfl) ⟨203009, by rfl⟩ : syracuseStep 270679 = 406019) B406019
theorem B4432229 : Blo 239816 4432229 := bstep (se 4 (by rfl) ⟨415521, by rfl⟩ : syracuseStep 4432229 = 831043) B831043
theorem B270859 : Blo 239816 270859 := bstep (se 1 (by rfl) ⟨203144, by rfl⟩ : syracuseStep 270859 = 406289) B406289
theorem B270967 : Blo 239816 270967 := bstep (se 1 (by rfl) ⟨203225, by rfl⟩ : syracuseStep 270967 = 406451) B406451
theorem B271147 : Blo 239816 271147 := bstep (se 1 (by rfl) ⟨203360, by rfl⟩ : syracuseStep 271147 = 406721) B406721
theorem B1385261 : Blo 239816 1385261 := bstep (se 3 (by rfl) ⟨259736, by rfl⟩ : syracuseStep 1385261 = 519473) B519473
theorem B1024919 : Blo 239816 1024919 := bstep (se 1 (by rfl) ⟨768689, by rfl⟩ : syracuseStep 1024919 = 1537379) B1537379
theorem B271255 : Blo 239816 271255 := bstep (se 1 (by rfl) ⟨203441, by rfl⟩ : syracuseStep 271255 = 406883) B406883
theorem B926765 : Blo 239816 926765 := bstep (se 3 (by rfl) ⟨173768, by rfl⟩ : syracuseStep 926765 = 347537) B347537
theorem B271435 : Blo 239816 271435 := bstep (se 1 (by rfl) ⟨203576, by rfl⟩ : syracuseStep 271435 = 407153) B407153
theorem B271543 : Blo 239816 271543 := bstep (se 1 (by rfl) ⟨203657, by rfl⟩ : syracuseStep 271543 = 407315) B407315
theorem B435545 : Blo 239816 435545 := bstep (se 2 (by rfl) ⟨163329, by rfl⟩ : syracuseStep 435545 = 326659) B326659
theorem B271723 : Blo 239816 271723 := bstep (se 1 (by rfl) ⟨203792, by rfl⟩ : syracuseStep 271723 = 407585) B407585
theorem B927121 : Blo 239816 927121 := bstep (se 2 (by rfl) ⟨347670, by rfl⟩ : syracuseStep 927121 = 695341) B695341
theorem B1156531 : Blo 239816 1156531 := bstep (se 1 (by rfl) ⟨867398, by rfl⟩ : syracuseStep 1156531 = 1734797) B1734797
theorem B271831 : Blo 239816 271831 := bstep (se 1 (by rfl) ⟨203873, by rfl⟩ : syracuseStep 271831 = 407747) B407747
theorem B304651 : Blo 239816 304651 := bstep (se 1 (by rfl) ⟨228488, by rfl⟩ : syracuseStep 304651 = 456977) B456977
theorem B272011 : Blo 239816 272011 := bstep (se 1 (by rfl) ⟨204008, by rfl⟩ : syracuseStep 272011 = 408017) B408017
theorem B435863 : Blo 239816 435863 := bstep (se 1 (by rfl) ⟨326897, by rfl⟩ : syracuseStep 435863 = 653795) B653795
theorem B272119 : Blo 239816 272119 := bstep (se 1 (by rfl) ⟨204089, by rfl⟩ : syracuseStep 272119 = 408179) B408179
theorem B370583 : Blo 239816 370583 := bstep (se 1 (by rfl) ⟨277937, by rfl⟩ : syracuseStep 370583 = 555875) B555875
theorem B272299 : Blo 239816 272299 := bstep (se 1 (by rfl) ⟨204224, by rfl⟩ : syracuseStep 272299 = 408449) B408449
theorem B272407 : Blo 239816 272407 := bstep (se 1 (by rfl) ⟨204305, by rfl⟩ : syracuseStep 272407 = 408611) B408611
theorem B469081 : Blo 239816 469081 := bstep (se 2 (by rfl) ⟨175905, by rfl⟩ : syracuseStep 469081 = 351811) B351811
theorem B1845341 : Blo 239816 1845341 := bstep (se 3 (by rfl) ⟨346001, by rfl⟩ : syracuseStep 1845341 = 692003) B692003
theorem B239819 : Blo 239816 239819 := bstep (se 1 (by rfl) ⟨179864, by rfl⟩ : syracuseStep 239819 = 359729) B359729
theorem B272587 : Blo 239816 272587 := bstep (se 1 (by rfl) ⟨204440, by rfl⟩ : syracuseStep 272587 = 408881) B408881
theorem B239831 : Blo 239816 239831 := bstep (se 1 (by rfl) ⟨179873, by rfl⟩ : syracuseStep 239831 = 359747) B359747
theorem B239851 : Blo 239816 239851 := bstep (se 1 (by rfl) ⟨179888, by rfl⟩ : syracuseStep 239851 = 359777) B359777
theorem B239863 : Blo 239816 239863 := bstep (se 1 (by rfl) ⟨179897, by rfl⟩ : syracuseStep 239863 = 359795) B359795
theorem B239883 : Blo 239816 239883 := bstep (se 1 (by rfl) ⟨179912, by rfl⟩ : syracuseStep 239883 = 359825) B359825
theorem B239895 : Blo 239816 239895 := bstep (se 1 (by rfl) ⟨179921, by rfl⟩ : syracuseStep 239895 = 359843) B359843
theorem B239915 : Blo 239816 239915 := bstep (se 1 (by rfl) ⟨179936, by rfl⟩ : syracuseStep 239915 = 359873) B359873
theorem B239927 : Blo 239816 239927 := bstep (se 1 (by rfl) ⟨179945, by rfl⟩ : syracuseStep 239927 = 359891) B359891
theorem B272695 : Blo 239816 272695 := bstep (se 1 (by rfl) ⟨204521, by rfl⟩ : syracuseStep 272695 = 409043) B409043
theorem B1583425 : Blo 239816 1583425 := bstep (se 2 (by rfl) ⟨593784, by rfl⟩ : syracuseStep 1583425 = 1187569) B1187569
theorem B239947 : Blo 239816 239947 := bstep (se 1 (by rfl) ⟨179960, by rfl⟩ : syracuseStep 239947 = 359921) B359921
theorem B239959 : Blo 239816 239959 := bstep (se 1 (by rfl) ⟨179969, by rfl⟩ : syracuseStep 239959 = 359939) B359939
theorem B239979 : Blo 239816 239979 := bstep (se 1 (by rfl) ⟨179984, by rfl⟩ : syracuseStep 239979 = 359969) B359969
theorem B239991 : Blo 239816 239991 := bstep (se 1 (by rfl) ⟨179993, by rfl⟩ : syracuseStep 239991 = 359987) B359987
theorem B240011 : Blo 239816 240011 := bstep (se 1 (by rfl) ⟨180008, by rfl⟩ : syracuseStep 240011 = 360017) B360017
theorem B240023 : Blo 239816 240023 := bstep (se 1 (by rfl) ⟨180017, by rfl⟩ : syracuseStep 240023 = 360035) B360035
theorem B240043 : Blo 239816 240043 := bstep (se 1 (by rfl) ⟨180032, by rfl⟩ : syracuseStep 240043 = 360065) B360065
theorem B240055 : Blo 239816 240055 := bstep (se 1 (by rfl) ⟨180041, by rfl⟩ : syracuseStep 240055 = 360083) B360083
theorem B240075 : Blo 239816 240075 := bstep (se 1 (by rfl) ⟨180056, by rfl⟩ : syracuseStep 240075 = 360113) B360113
theorem B240087 : Blo 239816 240087 := bstep (se 1 (by rfl) ⟨180065, by rfl⟩ : syracuseStep 240087 = 360131) B360131
theorem B305623 : Blo 239816 305623 := bstep (se 1 (by rfl) ⟨229217, by rfl⟩ : syracuseStep 305623 = 458435) B458435
theorem B240107 : Blo 239816 240107 := bstep (se 1 (by rfl) ⟨180080, by rfl⟩ : syracuseStep 240107 = 360161) B360161
theorem B272875 : Blo 239816 272875 := bstep (se 1 (by rfl) ⟨204656, by rfl⟩ : syracuseStep 272875 = 409313) B409313
theorem B240119 : Blo 239816 240119 := bstep (se 1 (by rfl) ⟨180089, by rfl⟩ : syracuseStep 240119 = 360179) B360179
theorem B240139 : Blo 239816 240139 := bstep (se 1 (by rfl) ⟨180104, by rfl⟩ : syracuseStep 240139 = 360209) B360209
theorem B240151 : Blo 239816 240151 := bstep (se 1 (by rfl) ⟨180113, by rfl⟩ : syracuseStep 240151 = 360227) B360227
theorem B1878563 : Blo 239816 1878563 := bstep (se 1 (by rfl) ⟨1408922, by rfl⟩ : syracuseStep 1878563 = 2817845) B2817845
theorem B240171 : Blo 239816 240171 := bstep (se 1 (by rfl) ⟨180128, by rfl⟩ : syracuseStep 240171 = 360257) B360257
theorem B240183 : Blo 239816 240183 := bstep (se 1 (by rfl) ⟨180137, by rfl⟩ : syracuseStep 240183 = 360275) B360275
theorem B240203 : Blo 239816 240203 := bstep (se 1 (by rfl) ⟨180152, by rfl⟩ : syracuseStep 240203 = 360305) B360305
theorem B240215 : Blo 239816 240215 := bstep (se 1 (by rfl) ⟨180161, by rfl⟩ : syracuseStep 240215 = 360323) B360323
theorem B272983 : Blo 239816 272983 := bstep (se 1 (by rfl) ⟨204737, by rfl⟩ : syracuseStep 272983 = 409475) B409475
theorem B1223261 : Blo 239816 1223261 := bstep (se 3 (by rfl) ⟨229361, by rfl⟩ : syracuseStep 1223261 = 458723) B458723
theorem B240235 : Blo 239816 240235 := bstep (se 1 (by rfl) ⟨180176, by rfl⟩ : syracuseStep 240235 = 360353) B360353
theorem B240247 : Blo 239816 240247 := bstep (se 1 (by rfl) ⟨180185, by rfl⟩ : syracuseStep 240247 = 360371) B360371
theorem B240267 : Blo 239816 240267 := bstep (se 1 (by rfl) ⟨180200, by rfl⟩ : syracuseStep 240267 = 360401) B360401
theorem B240279 : Blo 239816 240279 := bstep (se 1 (by rfl) ⟨180209, by rfl⟩ : syracuseStep 240279 = 360419) B360419
theorem B240299 : Blo 239816 240299 := bstep (se 1 (by rfl) ⟨180224, by rfl⟩ : syracuseStep 240299 = 360449) B360449
theorem B240311 : Blo 239816 240311 := bstep (se 1 (by rfl) ⟨180233, by rfl⟩ : syracuseStep 240311 = 360467) B360467
theorem B240331 : Blo 239816 240331 := bstep (se 1 (by rfl) ⟨180248, by rfl⟩ : syracuseStep 240331 = 360497) B360497
theorem B240343 : Blo 239816 240343 := bstep (se 1 (by rfl) ⟨180257, by rfl⟩ : syracuseStep 240343 = 360515) B360515
theorem B240363 : Blo 239816 240363 := bstep (se 1 (by rfl) ⟨180272, by rfl⟩ : syracuseStep 240363 = 360545) B360545
theorem B240375 : Blo 239816 240375 := bstep (se 1 (by rfl) ⟨180281, by rfl⟩ : syracuseStep 240375 = 360563) B360563
theorem B240395 : Blo 239816 240395 := bstep (se 1 (by rfl) ⟨180296, by rfl⟩ : syracuseStep 240395 = 360593) B360593
theorem B273163 : Blo 239816 273163 := bstep (se 1 (by rfl) ⟨204872, by rfl⟩ : syracuseStep 273163 = 409745) B409745
theorem B240407 : Blo 239816 240407 := bstep (se 1 (by rfl) ⟨180305, by rfl⟩ : syracuseStep 240407 = 360611) B360611
theorem B240427 : Blo 239816 240427 := bstep (se 1 (by rfl) ⟨180320, by rfl⟩ : syracuseStep 240427 = 360641) B360641
theorem B240439 : Blo 239816 240439 := bstep (se 1 (by rfl) ⟨180329, by rfl⟩ : syracuseStep 240439 = 360659) B360659
theorem B240459 : Blo 239816 240459 := bstep (se 1 (by rfl) ⟨180344, by rfl⟩ : syracuseStep 240459 = 360689) B360689
theorem B240471 : Blo 239816 240471 := bstep (se 1 (by rfl) ⟨180353, by rfl⟩ : syracuseStep 240471 = 360707) B360707
theorem B240491 : Blo 239816 240491 := bstep (se 1 (by rfl) ⟨180368, by rfl⟩ : syracuseStep 240491 = 360737) B360737
theorem B240503 : Blo 239816 240503 := bstep (se 1 (by rfl) ⟨180377, by rfl⟩ : syracuseStep 240503 = 360755) B360755
theorem B273271 : Blo 239816 273271 := bstep (se 1 (by rfl) ⟨204953, by rfl⟩ : syracuseStep 273271 = 409907) B409907
theorem B240523 : Blo 239816 240523 := bstep (se 1 (by rfl) ⟨180392, by rfl⟩ : syracuseStep 240523 = 360785) B360785
theorem B240535 : Blo 239816 240535 := bstep (se 1 (by rfl) ⟨180401, by rfl⟩ : syracuseStep 240535 = 360803) B360803
theorem B240555 : Blo 239816 240555 := bstep (se 1 (by rfl) ⟨180416, by rfl⟩ : syracuseStep 240555 = 360833) B360833
theorem B4107185 : Blo 239816 4107185 := bstep (se 2 (by rfl) ⟨1540194, by rfl⟩ : syracuseStep 4107185 = 3080389) B3080389
theorem B240567 : Blo 239816 240567 := bstep (se 1 (by rfl) ⟨180425, by rfl⟩ : syracuseStep 240567 = 360851) B360851
theorem B240587 : Blo 239816 240587 := bstep (se 1 (by rfl) ⟨180440, by rfl⟩ : syracuseStep 240587 = 360881) B360881
theorem B240599 : Blo 239816 240599 := bstep (se 1 (by rfl) ⟨180449, by rfl⟩ : syracuseStep 240599 = 360899) B360899
theorem B240619 : Blo 239816 240619 := bstep (se 1 (by rfl) ⟨180464, by rfl⟩ : syracuseStep 240619 = 360929) B360929
theorem B240631 : Blo 239816 240631 := bstep (se 1 (by rfl) ⟨180473, by rfl⟩ : syracuseStep 240631 = 360947) B360947
theorem B240651 : Blo 239816 240651 := bstep (se 1 (by rfl) ⟨180488, by rfl⟩ : syracuseStep 240651 = 360977) B360977
theorem B240663 : Blo 239816 240663 := bstep (se 1 (by rfl) ⟨180497, by rfl⟩ : syracuseStep 240663 = 360995) B360995
theorem B240683 : Blo 239816 240683 := bstep (se 1 (by rfl) ⟨180512, by rfl⟩ : syracuseStep 240683 = 361025) B361025
theorem B273451 : Blo 239816 273451 := bstep (se 1 (by rfl) ⟨205088, by rfl⟩ : syracuseStep 273451 = 410177) B410177
theorem B240695 : Blo 239816 240695 := bstep (se 1 (by rfl) ⟨180521, by rfl⟩ : syracuseStep 240695 = 361043) B361043
theorem B240715 : Blo 239816 240715 := bstep (se 1 (by rfl) ⟨180536, by rfl⟩ : syracuseStep 240715 = 361073) B361073
theorem B240727 : Blo 239816 240727 := bstep (se 1 (by rfl) ⟨180545, by rfl⟩ : syracuseStep 240727 = 361091) B361091
theorem B240747 : Blo 239816 240747 := bstep (se 1 (by rfl) ⟨180560, by rfl⟩ : syracuseStep 240747 = 361121) B361121
theorem B240759 : Blo 239816 240759 := bstep (se 1 (by rfl) ⟨180569, by rfl⟩ : syracuseStep 240759 = 361139) B361139
theorem B1387651 : Blo 239816 1387651 := bstep (se 1 (by rfl) ⟨1040738, by rfl⟩ : syracuseStep 1387651 = 2081477) B2081477
theorem B240779 : Blo 239816 240779 := bstep (se 1 (by rfl) ⟨180584, by rfl⟩ : syracuseStep 240779 = 361169) B361169
theorem B240791 : Blo 239816 240791 := bstep (se 1 (by rfl) ⟨180593, by rfl⟩ : syracuseStep 240791 = 361187) B361187
theorem B273559 : Blo 239816 273559 := bstep (se 1 (by rfl) ⟨205169, by rfl⟩ : syracuseStep 273559 = 410339) B410339
theorem B240811 : Blo 239816 240811 := bstep (se 1 (by rfl) ⟨180608, by rfl⟩ : syracuseStep 240811 = 361217) B361217
theorem B240823 : Blo 239816 240823 := bstep (se 1 (by rfl) ⟨180617, by rfl⟩ : syracuseStep 240823 = 361235) B361235
theorem B240843 : Blo 239816 240843 := bstep (se 1 (by rfl) ⟨180632, by rfl⟩ : syracuseStep 240843 = 361265) B361265
theorem B863435 : Blo 239816 863435 := bstep (se 1 (by rfl) ⟨647576, by rfl⟩ : syracuseStep 863435 = 1295153) B1295153
theorem B240855 : Blo 239816 240855 := bstep (se 1 (by rfl) ⟨180641, by rfl⟩ : syracuseStep 240855 = 361283) B361283
theorem B240875 : Blo 239816 240875 := bstep (se 1 (by rfl) ⟨180656, by rfl⟩ : syracuseStep 240875 = 361313) B361313
theorem B240887 : Blo 239816 240887 := bstep (se 1 (by rfl) ⟨180665, by rfl⟩ : syracuseStep 240887 = 361331) B361331
theorem B240907 : Blo 239816 240907 := bstep (se 1 (by rfl) ⟨180680, by rfl⟩ : syracuseStep 240907 = 361361) B361361
theorem B306443 : Blo 239816 306443 := bstep (se 1 (by rfl) ⟨229832, by rfl⟩ : syracuseStep 306443 = 459665) B459665
theorem B240919 : Blo 239816 240919 := bstep (se 1 (by rfl) ⟨180689, by rfl⟩ : syracuseStep 240919 = 361379) B361379
theorem B240939 : Blo 239816 240939 := bstep (se 1 (by rfl) ⟨180704, by rfl⟩ : syracuseStep 240939 = 361409) B361409
theorem B240951 : Blo 239816 240951 := bstep (se 1 (by rfl) ⟨180713, by rfl⟩ : syracuseStep 240951 = 361427) B361427
theorem B240971 : Blo 239816 240971 := bstep (se 1 (by rfl) ⟨180728, by rfl⟩ : syracuseStep 240971 = 361457) B361457
theorem B273739 : Blo 239816 273739 := bstep (se 1 (by rfl) ⟨205304, by rfl⟩ : syracuseStep 273739 = 410609) B410609
theorem B240983 : Blo 239816 240983 := bstep (se 1 (by rfl) ⟨180737, by rfl⟩ : syracuseStep 240983 = 361475) B361475
theorem B241003 : Blo 239816 241003 := bstep (se 1 (by rfl) ⟨180752, by rfl⟩ : syracuseStep 241003 = 361505) B361505
theorem B241015 : Blo 239816 241015 := bstep (se 1 (by rfl) ⟨180761, by rfl⟩ : syracuseStep 241015 = 361523) B361523
theorem B241035 : Blo 239816 241035 := bstep (se 1 (by rfl) ⟨180776, by rfl⟩ : syracuseStep 241035 = 361553) B361553
theorem B241047 : Blo 239816 241047 := bstep (se 1 (by rfl) ⟨180785, by rfl⟩ : syracuseStep 241047 = 361571) B361571
theorem B241067 : Blo 239816 241067 := bstep (se 1 (by rfl) ⟨180800, by rfl⟩ : syracuseStep 241067 = 361601) B361601
theorem B241079 : Blo 239816 241079 := bstep (se 1 (by rfl) ⟨180809, by rfl⟩ : syracuseStep 241079 = 361619) B361619
theorem B273847 : Blo 239816 273847 := bstep (se 1 (by rfl) ⟨205385, by rfl⟩ : syracuseStep 273847 = 410771) B410771
theorem B404939 : Blo 239816 404939 := bstep (se 1 (by rfl) ⟨303704, by rfl⟩ : syracuseStep 404939 = 607409) B607409
theorem B241099 : Blo 239816 241099 := bstep (se 1 (by rfl) ⟨180824, by rfl⟩ : syracuseStep 241099 = 361649) B361649
theorem B241111 : Blo 239816 241111 := bstep (se 1 (by rfl) ⟨180833, by rfl⟩ : syracuseStep 241111 = 361667) B361667
theorem B241131 : Blo 239816 241131 := bstep (se 1 (by rfl) ⟨180848, by rfl⟩ : syracuseStep 241131 = 361697) B361697
theorem B241143 : Blo 239816 241143 := bstep (se 1 (by rfl) ⟨180857, by rfl⟩ : syracuseStep 241143 = 361715) B361715
theorem B241163 : Blo 239816 241163 := bstep (se 1 (by rfl) ⟨180872, by rfl⟩ : syracuseStep 241163 = 361745) B361745
theorem B241175 : Blo 239816 241175 := bstep (se 1 (by rfl) ⟨180881, by rfl⟩ : syracuseStep 241175 = 361763) B361763
theorem B3517987 : Blo 239816 3517987 := bstep (se 1 (by rfl) ⟨2638490, by rfl⟩ : syracuseStep 3517987 = 5276981) B5276981
theorem B241195 : Blo 239816 241195 := bstep (se 1 (by rfl) ⟨180896, by rfl⟩ : syracuseStep 241195 = 361793) B361793
theorem B1945133 : Blo 239816 1945133 := bstep (se 3 (by rfl) ⟨364712, by rfl⟩ : syracuseStep 1945133 = 729425) B729425
theorem B241207 : Blo 239816 241207 := bstep (se 1 (by rfl) ⟨180905, by rfl⟩ : syracuseStep 241207 = 361811) B361811
theorem B405067 : Blo 239816 405067 := bstep (se 1 (by rfl) ⟨303800, by rfl⟩ : syracuseStep 405067 = 607601) B607601
theorem B241227 : Blo 239816 241227 := bstep (se 1 (by rfl) ⟨180920, by rfl⟩ : syracuseStep 241227 = 361841) B361841
theorem B241239 : Blo 239816 241239 := bstep (se 1 (by rfl) ⟨180929, by rfl⟩ : syracuseStep 241239 = 361859) B361859
theorem B241259 : Blo 239816 241259 := bstep (se 1 (by rfl) ⟨180944, by rfl⟩ : syracuseStep 241259 = 361889) B361889
theorem B274027 : Blo 239816 274027 := bstep (se 1 (by rfl) ⟨205520, by rfl⟩ : syracuseStep 274027 = 411041) B411041
theorem B241271 : Blo 239816 241271 := bstep (se 1 (by rfl) ⟨180953, by rfl⟩ : syracuseStep 241271 = 361907) B361907
theorem B241291 : Blo 239816 241291 := bstep (se 1 (by rfl) ⟨180968, by rfl⟩ : syracuseStep 241291 = 361937) B361937
theorem B241303 : Blo 239816 241303 := bstep (se 1 (by rfl) ⟨180977, by rfl⟩ : syracuseStep 241303 = 361955) B361955
theorem B241323 : Blo 239816 241323 := bstep (se 1 (by rfl) ⟨180992, by rfl⟩ : syracuseStep 241323 = 361985) B361985
theorem B241335 : Blo 239816 241335 := bstep (se 1 (by rfl) ⟨181001, by rfl⟩ : syracuseStep 241335 = 362003) B362003
theorem B241355 : Blo 239816 241355 := bstep (se 1 (by rfl) ⟨181016, by rfl⟩ : syracuseStep 241355 = 362033) B362033
theorem B241367 : Blo 239816 241367 := bstep (se 1 (by rfl) ⟨181025, by rfl⟩ : syracuseStep 241367 = 362051) B362051
theorem B274135 : Blo 239816 274135 := bstep (se 1 (by rfl) ⟨205601, by rfl⟩ : syracuseStep 274135 = 411203) B411203
theorem B405209 : Blo 239816 405209 := bstep (se 2 (by rfl) ⟨151953, by rfl⟩ : syracuseStep 405209 = 303907) B303907
theorem B241387 : Blo 239816 241387 := bstep (se 1 (by rfl) ⟨181040, by rfl⟩ : syracuseStep 241387 = 362081) B362081
theorem B241399 : Blo 239816 241399 := bstep (se 1 (by rfl) ⟨181049, by rfl⟩ : syracuseStep 241399 = 362099) B362099
theorem B241419 : Blo 239816 241419 := bstep (se 1 (by rfl) ⟨181064, by rfl⟩ : syracuseStep 241419 = 362129) B362129
theorem B241431 : Blo 239816 241431 := bstep (se 1 (by rfl) ⟨181073, by rfl⟩ : syracuseStep 241431 = 362147) B362147
theorem B241451 : Blo 239816 241451 := bstep (se 1 (by rfl) ⟨181088, by rfl⟩ : syracuseStep 241451 = 362177) B362177
theorem B241463 : Blo 239816 241463 := bstep (se 1 (by rfl) ⟨181097, by rfl⟩ : syracuseStep 241463 = 362195) B362195
theorem B241483 : Blo 239816 241483 := bstep (se 1 (by rfl) ⟨181112, by rfl⟩ : syracuseStep 241483 = 362225) B362225
theorem B241495 : Blo 239816 241495 := bstep (se 1 (by rfl) ⟨181121, by rfl⟩ : syracuseStep 241495 = 362243) B362243
theorem B405337 : Blo 239816 405337 := bstep (se 2 (by rfl) ⟨152001, by rfl⟩ : syracuseStep 405337 = 304003) B304003
theorem B241515 : Blo 239816 241515 := bstep (se 1 (by rfl) ⟨181136, by rfl⟩ : syracuseStep 241515 = 362273) B362273
theorem B241527 : Blo 239816 241527 := bstep (se 1 (by rfl) ⟨181145, by rfl⟩ : syracuseStep 241527 = 362291) B362291
theorem B274315 : Blo 239816 274315 := bstep (se 1 (by rfl) ⟨205736, by rfl⟩ : syracuseStep 274315 = 411473) B411473
theorem B241547 : Blo 239816 241547 := bstep (se 1 (by rfl) ⟨181160, by rfl⟩ : syracuseStep 241547 = 362321) B362321
theorem B241559 : Blo 239816 241559 := bstep (se 1 (by rfl) ⟨181169, by rfl⟩ : syracuseStep 241559 = 362339) B362339
theorem B241579 : Blo 239816 241579 := bstep (se 1 (by rfl) ⟨181184, by rfl⟩ : syracuseStep 241579 = 362369) B362369
theorem B241591 : Blo 239816 241591 := bstep (se 1 (by rfl) ⟨181193, by rfl⟩ : syracuseStep 241591 = 362387) B362387
theorem B241611 : Blo 239816 241611 := bstep (se 1 (by rfl) ⟨181208, by rfl⟩ : syracuseStep 241611 = 362417) B362417
theorem B307147 : Blo 239816 307147 := bstep (se 1 (by rfl) ⟨230360, by rfl⟩ : syracuseStep 307147 = 460721) B460721
theorem B241623 : Blo 239816 241623 := bstep (se 1 (by rfl) ⟨181217, by rfl⟩ : syracuseStep 241623 = 362435) B362435
theorem B241643 : Blo 239816 241643 := bstep (se 1 (by rfl) ⟨181232, by rfl⟩ : syracuseStep 241643 = 362465) B362465
theorem B241655 : Blo 239816 241655 := bstep (se 1 (by rfl) ⟨181241, by rfl⟩ : syracuseStep 241655 = 362483) B362483
theorem B241675 : Blo 239816 241675 := bstep (se 1 (by rfl) ⟨181256, by rfl⟩ : syracuseStep 241675 = 362513) B362513
theorem B241687 : Blo 239816 241687 := bstep (se 1 (by rfl) ⟨181265, by rfl⟩ : syracuseStep 241687 = 362531) B362531
theorem B241707 : Blo 239816 241707 := bstep (se 1 (by rfl) ⟨181280, by rfl⟩ : syracuseStep 241707 = 362561) B362561
theorem B241719 : Blo 239816 241719 := bstep (se 1 (by rfl) ⟨181289, by rfl⟩ : syracuseStep 241719 = 362579) B362579
theorem B1388609 : Blo 239816 1388609 := bstep (se 2 (by rfl) ⟨520728, by rfl⟩ : syracuseStep 1388609 = 1041457) B1041457
theorem B241739 : Blo 239816 241739 := bstep (se 1 (by rfl) ⟨181304, by rfl⟩ : syracuseStep 241739 = 362609) B362609
theorem B241751 : Blo 239816 241751 := bstep (se 1 (by rfl) ⟨181313, by rfl⟩ : syracuseStep 241751 = 362627) B362627
theorem B241771 : Blo 239816 241771 := bstep (se 1 (by rfl) ⟨181328, by rfl⟩ : syracuseStep 241771 = 362657) B362657
theorem B241783 : Blo 239816 241783 := bstep (se 1 (by rfl) ⟨181337, by rfl⟩ : syracuseStep 241783 = 362675) B362675
theorem B241803 : Blo 239816 241803 := bstep (se 1 (by rfl) ⟨181352, by rfl⟩ : syracuseStep 241803 = 362705) B362705
theorem B241815 : Blo 239816 241815 := bstep (se 1 (by rfl) ⟨181361, by rfl⟩ : syracuseStep 241815 = 362723) B362723
theorem B241835 : Blo 239816 241835 := bstep (se 1 (by rfl) ⟨181376, by rfl⟩ : syracuseStep 241835 = 362753) B362753
theorem B241847 : Blo 239816 241847 := bstep (se 1 (by rfl) ⟨181385, by rfl⟩ : syracuseStep 241847 = 362771) B362771
theorem B241867 : Blo 239816 241867 := bstep (se 1 (by rfl) ⟨181400, by rfl⟩ : syracuseStep 241867 = 362801) B362801
theorem B241879 : Blo 239816 241879 := bstep (se 1 (by rfl) ⟨181409, by rfl⟩ : syracuseStep 241879 = 362819) B362819
theorem B307415 : Blo 239816 307415 := bstep (se 1 (by rfl) ⟨230561, by rfl⟩ : syracuseStep 307415 = 461123) B461123
theorem B241899 : Blo 239816 241899 := bstep (se 1 (by rfl) ⟨181424, by rfl⟩ : syracuseStep 241899 = 362849) B362849
theorem B241911 : Blo 239816 241911 := bstep (se 1 (by rfl) ⟨181433, by rfl⟩ : syracuseStep 241911 = 362867) B362867
theorem B864515 : Blo 239816 864515 := bstep (se 1 (by rfl) ⟨648386, by rfl⟩ : syracuseStep 864515 = 1296773) B1296773
theorem B241931 : Blo 239816 241931 := bstep (se 1 (by rfl) ⟨181448, by rfl⟩ : syracuseStep 241931 = 362897) B362897
theorem B1028369 : Blo 239816 1028369 := bstep (se 2 (by rfl) ⟨385638, by rfl⟩ : syracuseStep 1028369 = 771277) B771277
theorem B241943 : Blo 239816 241943 := bstep (se 1 (by rfl) ⟨181457, by rfl⟩ : syracuseStep 241943 = 362915) B362915
theorem B1716515 : Blo 239816 1716515 := bstep (se 1 (by rfl) ⟨1287386, by rfl⟩ : syracuseStep 1716515 = 2574773) B2574773
theorem B241963 : Blo 239816 241963 := bstep (se 1 (by rfl) ⟨181472, by rfl⟩ : syracuseStep 241963 = 362945) B362945
theorem B241975 : Blo 239816 241975 := bstep (se 1 (by rfl) ⟨181481, by rfl⟩ : syracuseStep 241975 = 362963) B362963
theorem B241995 : Blo 239816 241995 := bstep (se 1 (by rfl) ⟨181496, by rfl⟩ : syracuseStep 241995 = 362993) B362993
theorem B242007 : Blo 239816 242007 := bstep (se 1 (by rfl) ⟨181505, by rfl⟩ : syracuseStep 242007 = 363011) B363011
theorem B242027 : Blo 239816 242027 := bstep (se 1 (by rfl) ⟨181520, by rfl⟩ : syracuseStep 242027 = 363041) B363041
theorem B242039 : Blo 239816 242039 := bstep (se 1 (by rfl) ⟨181529, by rfl⟩ : syracuseStep 242039 = 363059) B363059
theorem B242059 : Blo 239816 242059 := bstep (se 1 (by rfl) ⟨181544, by rfl⟩ : syracuseStep 242059 = 363089) B363089
theorem B405911 : Blo 239816 405911 := bstep (se 1 (by rfl) ⟨304433, by rfl⟩ : syracuseStep 405911 = 608867) B608867
theorem B242071 : Blo 239816 242071 := bstep (se 1 (by rfl) ⟨181553, by rfl⟩ : syracuseStep 242071 = 363107) B363107
theorem B700823 : Blo 239816 700823 := bstep (se 1 (by rfl) ⟨525617, by rfl⟩ : syracuseStep 700823 = 1051235) B1051235
theorem B242091 : Blo 239816 242091 := bstep (se 1 (by rfl) ⟨181568, by rfl⟩ : syracuseStep 242091 = 363137) B363137
theorem B2240947 : Blo 239816 2240947 := bstep (se 1 (by rfl) ⟨1680710, by rfl⟩ : syracuseStep 2240947 = 3361421) B3361421
theorem B242103 : Blo 239816 242103 := bstep (se 1 (by rfl) ⟨181577, by rfl⟩ : syracuseStep 242103 = 363155) B363155
theorem B242123 : Blo 239816 242123 := bstep (se 1 (by rfl) ⟨181592, by rfl⟩ : syracuseStep 242123 = 363185) B363185
theorem B242135 : Blo 239816 242135 := bstep (se 1 (by rfl) ⟨181601, by rfl⟩ : syracuseStep 242135 = 363203) B363203
theorem B242155 : Blo 239816 242155 := bstep (se 1 (by rfl) ⟨181616, by rfl⟩ : syracuseStep 242155 = 363233) B363233
theorem B242167 : Blo 239816 242167 := bstep (se 1 (by rfl) ⟨181625, by rfl⟩ : syracuseStep 242167 = 363251) B363251
theorem B242187 : Blo 239816 242187 := bstep (se 1 (by rfl) ⟨181640, by rfl⟩ : syracuseStep 242187 = 363281) B363281
theorem B406039 : Blo 239816 406039 := bstep (se 1 (by rfl) ⟨304529, by rfl⟩ : syracuseStep 406039 = 609059) B609059
theorem B242199 : Blo 239816 242199 := bstep (se 1 (by rfl) ⟨181649, by rfl⟩ : syracuseStep 242199 = 363299) B363299
theorem B242219 : Blo 239816 242219 := bstep (se 1 (by rfl) ⟨181664, by rfl⟩ : syracuseStep 242219 = 363329) B363329
theorem B242231 : Blo 239816 242231 := bstep (se 1 (by rfl) ⟨181673, by rfl⟩ : syracuseStep 242231 = 363347) B363347
theorem B242251 : Blo 239816 242251 := bstep (se 1 (by rfl) ⟨181688, by rfl⟩ : syracuseStep 242251 = 363377) B363377
theorem B242263 : Blo 239816 242263 := bstep (se 1 (by rfl) ⟨181697, by rfl⟩ : syracuseStep 242263 = 363395) B363395
theorem B242283 : Blo 239816 242283 := bstep (se 1 (by rfl) ⟨181712, by rfl⟩ : syracuseStep 242283 = 363425) B363425
theorem B242295 : Blo 239816 242295 := bstep (se 1 (by rfl) ⟨181721, by rfl⟩ : syracuseStep 242295 = 363443) B363443
theorem B242315 : Blo 239816 242315 := bstep (se 1 (by rfl) ⟨181736, by rfl⟩ : syracuseStep 242315 = 363473) B363473
theorem B1225367 : Blo 239816 1225367 := bstep (se 1 (by rfl) ⟨919025, by rfl⟩ : syracuseStep 1225367 = 1838051) B1838051
theorem B242327 : Blo 239816 242327 := bstep (se 1 (by rfl) ⟨181745, by rfl⟩ : syracuseStep 242327 = 363491) B363491
theorem B242347 : Blo 239816 242347 := bstep (se 1 (by rfl) ⟨181760, by rfl⟩ : syracuseStep 242347 = 363521) B363521
theorem B4207285 : Blo 239816 4207285 := bstep (se 5 (by rfl) ⟨197216, by rfl⟩ : syracuseStep 4207285 = 394433) B394433
theorem B242359 : Blo 239816 242359 := bstep (se 1 (by rfl) ⟨181769, by rfl⟩ : syracuseStep 242359 = 363539) B363539
theorem B242379 : Blo 239816 242379 := bstep (se 1 (by rfl) ⟨181784, by rfl⟩ : syracuseStep 242379 = 363569) B363569
theorem B242391 : Blo 239816 242391 := bstep (se 1 (by rfl) ⟨181793, by rfl⟩ : syracuseStep 242391 = 363587) B363587
theorem B242411 : Blo 239816 242411 := bstep (se 1 (by rfl) ⟨181808, by rfl⟩ : syracuseStep 242411 = 363617) B363617
theorem B242423 : Blo 239816 242423 := bstep (se 1 (by rfl) ⟨181817, by rfl⟩ : syracuseStep 242423 = 363635) B363635
theorem B242443 : Blo 239816 242443 := bstep (se 1 (by rfl) ⟨181832, by rfl⟩ : syracuseStep 242443 = 363665) B363665
theorem B242455 : Blo 239816 242455 := bstep (se 1 (by rfl) ⟨181841, by rfl⟩ : syracuseStep 242455 = 363683) B363683
theorem B242475 : Blo 239816 242475 := bstep (se 1 (by rfl) ⟨181856, by rfl⟩ : syracuseStep 242475 = 363713) B363713
theorem B242487 : Blo 239816 242487 := bstep (se 1 (by rfl) ⟨181865, by rfl⟩ : syracuseStep 242487 = 363731) B363731
theorem B242507 : Blo 239816 242507 := bstep (se 1 (by rfl) ⟨181880, by rfl⟩ : syracuseStep 242507 = 363761) B363761
theorem B242519 : Blo 239816 242519 := bstep (se 1 (by rfl) ⟨181889, by rfl⟩ : syracuseStep 242519 = 363779) B363779
theorem B242539 : Blo 239816 242539 := bstep (se 1 (by rfl) ⟨181904, by rfl⟩ : syracuseStep 242539 = 363809) B363809
theorem B242551 : Blo 239816 242551 := bstep (se 1 (by rfl) ⟨181913, by rfl⟩ : syracuseStep 242551 = 363827) B363827
theorem B242571 : Blo 239816 242571 := bstep (se 1 (by rfl) ⟨181928, by rfl⟩ : syracuseStep 242571 = 363857) B363857
theorem B242583 : Blo 239816 242583 := bstep (se 1 (by rfl) ⟨181937, by rfl⟩ : syracuseStep 242583 = 363875) B363875
theorem B308119 : Blo 239816 308119 := bstep (se 1 (by rfl) ⟨231089, by rfl⟩ : syracuseStep 308119 = 462179) B462179
theorem B242603 : Blo 239816 242603 := bstep (se 1 (by rfl) ⟨181952, by rfl⟩ : syracuseStep 242603 = 363905) B363905
theorem B8827825 : Blo 239816 8827825 := bstep (se 2 (by rfl) ⟨3310434, by rfl⟩ : syracuseStep 8827825 = 6620869) B6620869
theorem B242615 : Blo 239816 242615 := bstep (se 1 (by rfl) ⟨181961, by rfl⟩ : syracuseStep 242615 = 363923) B363923
theorem B242635 : Blo 239816 242635 := bstep (se 1 (by rfl) ⟨181976, by rfl⟩ : syracuseStep 242635 = 363953) B363953
theorem B242647 : Blo 239816 242647 := bstep (se 1 (by rfl) ⟨181985, by rfl⟩ : syracuseStep 242647 = 363971) B363971
theorem B701405 : Blo 239816 701405 := bstep (se 3 (by rfl) ⟨131513, by rfl⟩ : syracuseStep 701405 = 263027) B263027
theorem B242667 : Blo 239816 242667 := bstep (se 1 (by rfl) ⟨182000, by rfl⟩ : syracuseStep 242667 = 364001) B364001
theorem B242679 : Blo 239816 242679 := bstep (se 1 (by rfl) ⟨182009, by rfl⟩ : syracuseStep 242679 = 364019) B364019
theorem B242699 : Blo 239816 242699 := bstep (se 1 (by rfl) ⟨182024, by rfl⟩ : syracuseStep 242699 = 364049) B364049
theorem B242711 : Blo 239816 242711 := bstep (se 1 (by rfl) ⟨182033, by rfl⟩ : syracuseStep 242711 = 364067) B364067
theorem B242731 : Blo 239816 242731 := bstep (se 1 (by rfl) ⟨182048, by rfl⟩ : syracuseStep 242731 = 364097) B364097
theorem B242743 : Blo 239816 242743 := bstep (se 1 (by rfl) ⟨182057, by rfl⟩ : syracuseStep 242743 = 364115) B364115
theorem B242763 : Blo 239816 242763 := bstep (se 1 (by rfl) ⟨182072, by rfl⟩ : syracuseStep 242763 = 364145) B364145
theorem B242775 : Blo 239816 242775 := bstep (se 1 (by rfl) ⟨182081, by rfl⟩ : syracuseStep 242775 = 364163) B364163
theorem B242795 : Blo 239816 242795 := bstep (se 1 (by rfl) ⟨182096, by rfl⟩ : syracuseStep 242795 = 364193) B364193
theorem B242807 : Blo 239816 242807 := bstep (se 1 (by rfl) ⟨182105, by rfl⟩ : syracuseStep 242807 = 364211) B364211
theorem B406667 : Blo 239816 406667 := bstep (se 1 (by rfl) ⟨305000, by rfl⟩ : syracuseStep 406667 = 610001) B610001
theorem B242827 : Blo 239816 242827 := bstep (se 1 (by rfl) ⟨182120, by rfl⟩ : syracuseStep 242827 = 364241) B364241
theorem B242839 : Blo 239816 242839 := bstep (se 1 (by rfl) ⟨182129, by rfl⟩ : syracuseStep 242839 = 364259) B364259
theorem B242859 : Blo 239816 242859 := bstep (se 1 (by rfl) ⟨182144, by rfl⟩ : syracuseStep 242859 = 364289) B364289
theorem B1029293 : Blo 239816 1029293 := bstep (se 3 (by rfl) ⟨192992, by rfl⟩ : syracuseStep 1029293 = 385985) B385985
theorem B242871 : Blo 239816 242871 := bstep (se 1 (by rfl) ⟨182153, by rfl⟩ : syracuseStep 242871 = 364307) B364307
theorem B242891 : Blo 239816 242891 := bstep (se 1 (by rfl) ⟨182168, by rfl⟩ : syracuseStep 242891 = 364337) B364337
theorem B242903 : Blo 239816 242903 := bstep (se 1 (by rfl) ⟨182177, by rfl⟩ : syracuseStep 242903 = 364355) B364355
theorem B242923 : Blo 239816 242923 := bstep (se 1 (by rfl) ⟨182192, by rfl⟩ : syracuseStep 242923 = 364385) B364385
theorem B242935 : Blo 239816 242935 := bstep (se 1 (by rfl) ⟨182201, by rfl⟩ : syracuseStep 242935 = 364403) B364403
theorem B406795 : Blo 239816 406795 := bstep (se 1 (by rfl) ⟨305096, by rfl⟩ : syracuseStep 406795 = 610193) B610193
theorem B242955 : Blo 239816 242955 := bstep (se 1 (by rfl) ⟨182216, by rfl⟩ : syracuseStep 242955 = 364433) B364433
theorem B242967 : Blo 239816 242967 := bstep (se 1 (by rfl) ⟨182225, by rfl⟩ : syracuseStep 242967 = 364451) B364451
theorem B242987 : Blo 239816 242987 := bstep (se 1 (by rfl) ⟨182240, by rfl⟩ : syracuseStep 242987 = 364481) B364481
theorem B242999 : Blo 239816 242999 := bstep (se 1 (by rfl) ⟨182249, by rfl⟩ : syracuseStep 242999 = 364499) B364499
theorem B1160513 : Blo 239816 1160513 := bstep (se 2 (by rfl) ⟨435192, by rfl⟩ : syracuseStep 1160513 = 870385) B870385
theorem B243019 : Blo 239816 243019 := bstep (se 1 (by rfl) ⟨182264, by rfl⟩ : syracuseStep 243019 = 364529) B364529
theorem B243031 : Blo 239816 243031 := bstep (se 1 (by rfl) ⟨182273, by rfl⟩ : syracuseStep 243031 = 364547) B364547
theorem B243051 : Blo 239816 243051 := bstep (se 1 (by rfl) ⟨182288, by rfl⟩ : syracuseStep 243051 = 364577) B364577
theorem B243063 : Blo 239816 243063 := bstep (se 1 (by rfl) ⟨182297, by rfl⟩ : syracuseStep 243063 = 364595) B364595
theorem B243083 : Blo 239816 243083 := bstep (se 1 (by rfl) ⟨182312, by rfl⟩ : syracuseStep 243083 = 364625) B364625
theorem B243095 : Blo 239816 243095 := bstep (se 1 (by rfl) ⟨182321, by rfl⟩ : syracuseStep 243095 = 364643) B364643
theorem B406937 : Blo 239816 406937 := bstep (se 2 (by rfl) ⟨152601, by rfl⟩ : syracuseStep 406937 = 305203) B305203
theorem B243115 : Blo 239816 243115 := bstep (se 1 (by rfl) ⟨182336, by rfl⟩ : syracuseStep 243115 = 364673) B364673
theorem B243127 : Blo 239816 243127 := bstep (se 1 (by rfl) ⟨182345, by rfl⟩ : syracuseStep 243127 = 364691) B364691
theorem B243147 : Blo 239816 243147 := bstep (se 1 (by rfl) ⟨182360, by rfl⟩ : syracuseStep 243147 = 364721) B364721
theorem B243159 : Blo 239816 243159 := bstep (se 1 (by rfl) ⟨182369, by rfl⟩ : syracuseStep 243159 = 364739) B364739
theorem B243179 : Blo 239816 243179 := bstep (se 1 (by rfl) ⟨182384, by rfl⟩ : syracuseStep 243179 = 364769) B364769
theorem B243191 : Blo 239816 243191 := bstep (se 1 (by rfl) ⟨182393, by rfl⟩ : syracuseStep 243191 = 364787) B364787
theorem B243211 : Blo 239816 243211 := bstep (se 1 (by rfl) ⟨182408, by rfl⟩ : syracuseStep 243211 = 364817) B364817
theorem B243223 : Blo 239816 243223 := bstep (se 1 (by rfl) ⟨182417, by rfl⟩ : syracuseStep 243223 = 364835) B364835
theorem B407065 : Blo 239816 407065 := bstep (se 2 (by rfl) ⟨152649, by rfl⟩ : syracuseStep 407065 = 305299) B305299
theorem B243243 : Blo 239816 243243 := bstep (se 1 (by rfl) ⟨182432, by rfl⟩ : syracuseStep 243243 = 364865) B364865
theorem B243255 : Blo 239816 243255 := bstep (se 1 (by rfl) ⟨182441, by rfl⟩ : syracuseStep 243255 = 364883) B364883
theorem B243275 : Blo 239816 243275 := bstep (se 1 (by rfl) ⟨182456, by rfl⟩ : syracuseStep 243275 = 364913) B364913
theorem B243287 : Blo 239816 243287 := bstep (se 1 (by rfl) ⟨182465, by rfl⟩ : syracuseStep 243287 = 364931) B364931
theorem B243307 : Blo 239816 243307 := bstep (se 1 (by rfl) ⟨182480, by rfl⟩ : syracuseStep 243307 = 364961) B364961
theorem B243319 : Blo 239816 243319 := bstep (se 1 (by rfl) ⟨182489, by rfl⟩ : syracuseStep 243319 = 364979) B364979
theorem B243339 : Blo 239816 243339 := bstep (se 1 (by rfl) ⟨182504, by rfl⟩ : syracuseStep 243339 = 365009) B365009
theorem B243351 : Blo 239816 243351 := bstep (se 1 (by rfl) ⟨182513, by rfl⟩ : syracuseStep 243351 = 365027) B365027
theorem B276139 : Blo 239816 276139 := bstep (se 1 (by rfl) ⟨207104, by rfl⟩ : syracuseStep 276139 = 414209) B414209
theorem B243371 : Blo 239816 243371 := bstep (se 1 (by rfl) ⟨182528, by rfl⟩ : syracuseStep 243371 = 365057) B365057
theorem B243383 : Blo 239816 243383 := bstep (se 1 (by rfl) ⟨182537, by rfl⟩ : syracuseStep 243383 = 365075) B365075
theorem B243403 : Blo 239816 243403 := bstep (se 1 (by rfl) ⟨182552, by rfl⟩ : syracuseStep 243403 = 365105) B365105
theorem B243415 : Blo 239816 243415 := bstep (se 1 (by rfl) ⟨182561, by rfl⟩ : syracuseStep 243415 = 365123) B365123
theorem B1554137 : Blo 239816 1554137 := bstep (se 2 (by rfl) ⟨582801, by rfl⟩ : syracuseStep 1554137 = 1165603) B1165603
theorem B243435 : Blo 239816 243435 := bstep (se 1 (by rfl) ⟨182576, by rfl⟩ : syracuseStep 243435 = 365153) B365153
theorem B243447 : Blo 239816 243447 := bstep (se 1 (by rfl) ⟨182585, by rfl⟩ : syracuseStep 243447 = 365171) B365171
theorem B243467 : Blo 239816 243467 := bstep (se 1 (by rfl) ⟨182600, by rfl⟩ : syracuseStep 243467 = 365201) B365201
theorem B243479 : Blo 239816 243479 := bstep (se 1 (by rfl) ⟨182609, by rfl⟩ : syracuseStep 243479 = 365219) B365219
theorem B243499 : Blo 239816 243499 := bstep (se 1 (by rfl) ⟨182624, by rfl⟩ : syracuseStep 243499 = 365249) B365249
theorem B243511 : Blo 239816 243511 := bstep (se 1 (by rfl) ⟨182633, by rfl⟩ : syracuseStep 243511 = 365267) B365267
theorem B243531 : Blo 239816 243531 := bstep (se 1 (by rfl) ⟨182648, by rfl⟩ : syracuseStep 243531 = 365297) B365297
theorem B243543 : Blo 239816 243543 := bstep (se 1 (by rfl) ⟨182657, by rfl⟩ : syracuseStep 243543 = 365315) B365315
theorem B243563 : Blo 239816 243563 := bstep (se 1 (by rfl) ⟨182672, by rfl⟩ : syracuseStep 243563 = 365345) B365345
theorem B243575 : Blo 239816 243575 := bstep (se 1 (by rfl) ⟨182681, by rfl⟩ : syracuseStep 243575 = 365363) B365363
theorem B243595 : Blo 239816 243595 := bstep (se 1 (by rfl) ⟨182696, by rfl⟩ : syracuseStep 243595 = 365393) B365393
theorem B243607 : Blo 239816 243607 := bstep (se 1 (by rfl) ⟨182705, by rfl⟩ : syracuseStep 243607 = 365411) B365411
theorem B243627 : Blo 239816 243627 := bstep (se 1 (by rfl) ⟨182720, by rfl⟩ : syracuseStep 243627 = 365441) B365441
theorem B243639 : Blo 239816 243639 := bstep (se 1 (by rfl) ⟨182729, by rfl⟩ : syracuseStep 243639 = 365459) B365459
theorem B243659 : Blo 239816 243659 := bstep (se 1 (by rfl) ⟨182744, by rfl⟩ : syracuseStep 243659 = 365489) B365489
theorem B243671 : Blo 239816 243671 := bstep (se 1 (by rfl) ⟨182753, by rfl⟩ : syracuseStep 243671 = 365507) B365507
theorem B243691 : Blo 239816 243691 := bstep (se 1 (by rfl) ⟨182768, by rfl⟩ : syracuseStep 243691 = 365537) B365537
theorem B243703 : Blo 239816 243703 := bstep (se 1 (by rfl) ⟨182777, by rfl⟩ : syracuseStep 243703 = 365555) B365555
theorem B243723 : Blo 239816 243723 := bstep (se 1 (by rfl) ⟨182792, by rfl⟩ : syracuseStep 243723 = 365585) B365585
theorem B243735 : Blo 239816 243735 := bstep (se 1 (by rfl) ⟨182801, by rfl⟩ : syracuseStep 243735 = 365603) B365603
theorem B243755 : Blo 239816 243755 := bstep (se 1 (by rfl) ⟨182816, by rfl⟩ : syracuseStep 243755 = 365633) B365633
theorem B243767 : Blo 239816 243767 := bstep (se 1 (by rfl) ⟨182825, by rfl⟩ : syracuseStep 243767 = 365651) B365651
theorem B15677509 : Blo 239816 15677509 := bstep (se 4 (by rfl) ⟨1469766, by rfl⟩ : syracuseStep 15677509 = 2939533) B2939533
theorem B243787 : Blo 239816 243787 := bstep (se 1 (by rfl) ⟨182840, by rfl⟩ : syracuseStep 243787 = 365681) B365681
theorem B407639 : Blo 239816 407639 := bstep (se 1 (by rfl) ⟨305729, by rfl⟩ : syracuseStep 407639 = 611459) B611459
theorem B243799 : Blo 239816 243799 := bstep (se 1 (by rfl) ⟨182849, by rfl⟩ : syracuseStep 243799 = 365699) B365699
theorem B866477 : Blo 239816 866477 := bstep (se 3 (by rfl) ⟨162464, by rfl⟩ : syracuseStep 866477 = 324929) B324929
theorem B407767 : Blo 239816 407767 := bstep (se 1 (by rfl) ⟨305825, by rfl⟩ : syracuseStep 407767 = 611651) B611651
theorem B342425 : Blo 239816 342425 := bstep (se 2 (by rfl) ⟨128409, by rfl⟩ : syracuseStep 342425 = 256819) B256819
theorem B2767283 : Blo 239816 2767283 := bstep (se 1 (by rfl) ⟨2075462, by rfl⟩ : syracuseStep 2767283 = 4150925) B4150925
theorem B244183 : Blo 239816 244183 := bstep (se 1 (by rfl) ⟨183137, by rfl⟩ : syracuseStep 244183 = 366275) B366275
theorem B932417 : Blo 239816 932417 := bstep (se 2 (by rfl) ⟨349656, by rfl⟩ : syracuseStep 932417 = 699313) B699313
theorem B1030745 : Blo 239816 1030745 := bstep (se 2 (by rfl) ⟨386529, by rfl⟩ : syracuseStep 1030745 = 773059) B773059
theorem B2931461 : Blo 239816 2931461 := bstep (se 4 (by rfl) ⟨274824, by rfl⟩ : syracuseStep 2931461 = 549649) B549649
theorem B768791 : Blo 239816 768791 := bstep (se 1 (by rfl) ⟨576593, by rfl⟩ : syracuseStep 768791 = 1153187) B1153187
theorem B408395 : Blo 239816 408395 := bstep (se 1 (by rfl) ⟨306296, by rfl⟩ : syracuseStep 408395 = 612593) B612593
theorem B408523 : Blo 239816 408523 := bstep (se 1 (by rfl) ⟨306392, by rfl⟩ : syracuseStep 408523 = 612785) B612785
theorem B343063 : Blo 239816 343063 := bstep (se 1 (by rfl) ⟨257297, by rfl⟩ : syracuseStep 343063 = 514595) B514595
theorem B408665 : Blo 239816 408665 := bstep (se 2 (by rfl) ⟨153249, by rfl⟩ : syracuseStep 408665 = 306499) B306499
theorem B539801 : Blo 239816 539801 := bstep (se 2 (by rfl) ⟨202425, by rfl⟩ : syracuseStep 539801 = 404851) B404851
theorem B408793 : Blo 239816 408793 := bstep (se 2 (by rfl) ⟨153297, by rfl⟩ : syracuseStep 408793 = 306595) B306595
theorem B539891 : Blo 239816 539891 := bstep (se 1 (by rfl) ⟨404918, by rfl⟩ : syracuseStep 539891 = 809837) B809837
theorem B539927 : Blo 239816 539927 := bstep (se 1 (by rfl) ⟨404945, by rfl⟩ : syracuseStep 539927 = 809891) B809891
theorem B1555777 : Blo 239816 1555777 := bstep (se 2 (by rfl) ⟨583416, by rfl⟩ : syracuseStep 1555777 = 1166833) B1166833
theorem B540107 : Blo 239816 540107 := bstep (se 1 (by rfl) ⟨405080, by rfl⟩ : syracuseStep 540107 = 810161) B810161
theorem B540161 : Blo 239816 540161 := bstep (se 2 (by rfl) ⟨202560, by rfl⟩ : syracuseStep 540161 = 405121) B405121
theorem B1949285 : Blo 239816 1949285 := bstep (se 4 (by rfl) ⟨182745, by rfl⟩ : syracuseStep 1949285 = 365491) B365491
theorem B1752677 : Blo 239816 1752677 := bstep (se 4 (by rfl) ⟨164313, by rfl⟩ : syracuseStep 1752677 = 328627) B328627
theorem B540377 : Blo 239816 540377 := bstep (se 2 (by rfl) ⟨202641, by rfl⟩ : syracuseStep 540377 = 405283) B405283
theorem B343769 : Blo 239816 343769 := bstep (se 2 (by rfl) ⟨128913, by rfl⟩ : syracuseStep 343769 = 257827) B257827
theorem B409367 : Blo 239816 409367 := bstep (se 1 (by rfl) ⟨307025, by rfl⟩ : syracuseStep 409367 = 614051) B614051
theorem B540467 : Blo 239816 540467 := bstep (se 1 (by rfl) ⟨405350, by rfl⟩ : syracuseStep 540467 = 810701) B810701
theorem B343883 : Blo 239816 343883 := bstep (se 1 (by rfl) ⟨257912, by rfl⟩ : syracuseStep 343883 = 515825) B515825
theorem B540503 : Blo 239816 540503 := bstep (se 1 (by rfl) ⟨405377, by rfl⟩ : syracuseStep 540503 = 810755) B810755
theorem B2768741 : Blo 239816 2768741 := bstep (se 4 (by rfl) ⟨259569, by rfl⟩ : syracuseStep 2768741 = 519139) B519139
theorem B409495 : Blo 239816 409495 := bstep (se 1 (by rfl) ⟨307121, by rfl⟩ : syracuseStep 409495 = 614243) B614243
theorem B245675 : Blo 239816 245675 := bstep (se 1 (by rfl) ⟨184256, by rfl⟩ : syracuseStep 245675 = 368513) B368513
theorem B2310065 : Blo 239816 2310065 := bstep (se 2 (by rfl) ⟨866274, by rfl⟩ : syracuseStep 2310065 = 1732549) B1732549
theorem B540683 : Blo 239816 540683 := bstep (se 1 (by rfl) ⟨405512, by rfl⟩ : syracuseStep 540683 = 811025) B811025
theorem B540737 : Blo 239816 540737 := bstep (se 2 (by rfl) ⟨202776, by rfl⟩ : syracuseStep 540737 = 405553) B405553
theorem B1228931 : Blo 239816 1228931 := bstep (se 1 (by rfl) ⟨921698, by rfl⟩ : syracuseStep 1228931 = 1843397) B1843397
theorem B1032385 : Blo 239816 1032385 := bstep (se 2 (by rfl) ⟨387144, by rfl⟩ : syracuseStep 1032385 = 774289) B774289
theorem B540953 : Blo 239816 540953 := bstep (se 2 (by rfl) ⟨202857, by rfl⟩ : syracuseStep 540953 = 405715) B405715
theorem B344407 : Blo 239816 344407 := bstep (se 1 (by rfl) ⟨258305, by rfl⟩ : syracuseStep 344407 = 516611) B516611
theorem B541043 : Blo 239816 541043 := bstep (se 1 (by rfl) ⟨405782, by rfl⟩ : syracuseStep 541043 = 811565) B811565
theorem B541079 : Blo 239816 541079 := bstep (se 1 (by rfl) ⟨405809, by rfl⟩ : syracuseStep 541079 = 811619) B811619
theorem B410123 : Blo 239816 410123 := bstep (se 1 (by rfl) ⟨307592, by rfl⟩ : syracuseStep 410123 = 615185) B615185
theorem B541259 : Blo 239816 541259 := bstep (se 1 (by rfl) ⟨405944, by rfl⟩ : syracuseStep 541259 = 811889) B811889
theorem B541313 : Blo 239816 541313 := bstep (se 2 (by rfl) ⟨202992, by rfl⟩ : syracuseStep 541313 = 405985) B405985
theorem B410251 : Blo 239816 410251 := bstep (se 1 (by rfl) ⟨307688, by rfl⟩ : syracuseStep 410251 = 615377) B615377
theorem B1557265 : Blo 239816 1557265 := bstep (se 2 (by rfl) ⟨583974, by rfl⟩ : syracuseStep 1557265 = 1167949) B1167949
theorem B1032983 : Blo 239816 1032983 := bstep (se 1 (by rfl) ⟨774737, by rfl⟩ : syracuseStep 1032983 = 1549475) B1549475
theorem B410393 : Blo 239816 410393 := bstep (se 2 (by rfl) ⟨153897, by rfl⟩ : syracuseStep 410393 = 307795) B307795
theorem B770867 : Blo 239816 770867 := bstep (se 1 (by rfl) ⟨578150, by rfl⟩ : syracuseStep 770867 = 1156301) B1156301
theorem B541529 : Blo 239816 541529 := bstep (se 2 (by rfl) ⟨203073, by rfl⟩ : syracuseStep 541529 = 406147) B406147
theorem B410521 : Blo 239816 410521 := bstep (se 2 (by rfl) ⟨153945, by rfl⟩ : syracuseStep 410521 = 307891) B307891
theorem B541619 : Blo 239816 541619 := bstep (se 1 (by rfl) ⟨406214, by rfl⟩ : syracuseStep 541619 = 812429) B812429
theorem B541655 : Blo 239816 541655 := bstep (se 1 (by rfl) ⟨406241, by rfl⟩ : syracuseStep 541655 = 812483) B812483
theorem B607297 : Blo 239816 607297 := bstep (se 2 (by rfl) ⟨227736, by rfl⟩ : syracuseStep 607297 = 455473) B455473
theorem B541835 : Blo 239816 541835 := bstep (se 1 (by rfl) ⟨406376, by rfl⟩ : syracuseStep 541835 = 812753) B812753
theorem B345227 : Blo 239816 345227 := bstep (se 1 (by rfl) ⟨258920, by rfl⟩ : syracuseStep 345227 = 517841) B517841
theorem B541889 : Blo 239816 541889 := bstep (se 2 (by rfl) ⟨203208, by rfl⟩ : syracuseStep 541889 = 406417) B406417
theorem B1361197 : Blo 239816 1361197 := bstep (se 3 (by rfl) ⟨255224, by rfl⟩ : syracuseStep 1361197 = 510449) B510449
theorem B542105 : Blo 239816 542105 := bstep (se 2 (by rfl) ⟨203289, by rfl⟩ : syracuseStep 542105 = 406579) B406579
theorem B411095 : Blo 239816 411095 := bstep (se 1 (by rfl) ⟨308321, by rfl⟩ : syracuseStep 411095 = 616643) B616643
theorem B542195 : Blo 239816 542195 := bstep (se 1 (by rfl) ⟨406646, by rfl⟩ : syracuseStep 542195 = 813293) B813293
theorem B542231 : Blo 239816 542231 := bstep (se 1 (by rfl) ⟨406673, by rfl⟩ : syracuseStep 542231 = 813347) B813347
theorem B411223 : Blo 239816 411223 := bstep (se 1 (by rfl) ⟨308417, by rfl⟩ : syracuseStep 411223 = 616835) B616835
theorem B607895 : Blo 239816 607895 := bstep (se 1 (by rfl) ⟨455921, by rfl⟩ : syracuseStep 607895 = 911843) B911843
theorem B542411 : Blo 239816 542411 := bstep (se 1 (by rfl) ⟨406808, by rfl⟩ : syracuseStep 542411 = 813617) B813617
theorem B542465 : Blo 239816 542465 := bstep (se 2 (by rfl) ⟨203424, by rfl⟩ : syracuseStep 542465 = 406849) B406849
theorem B542681 : Blo 239816 542681 := bstep (se 2 (by rfl) ⟨203505, by rfl⟩ : syracuseStep 542681 = 407011) B407011
theorem B542771 : Blo 239816 542771 := bstep (se 1 (by rfl) ⟨407078, by rfl⟩ : syracuseStep 542771 = 814157) B814157
theorem B1034315 : Blo 239816 1034315 := bstep (se 1 (by rfl) ⟨775736, by rfl⟩ : syracuseStep 1034315 = 1551473) B1551473
theorem B542807 : Blo 239816 542807 := bstep (se 1 (by rfl) ⟨407105, by rfl⟩ : syracuseStep 542807 = 814211) B814211
theorem B870659 : Blo 239816 870659 := bstep (se 1 (by rfl) ⟨652994, by rfl⟩ : syracuseStep 870659 = 1305989) B1305989
theorem B542987 : Blo 239816 542987 := bstep (se 1 (by rfl) ⟨407240, by rfl⟩ : syracuseStep 542987 = 814481) B814481
theorem B543041 : Blo 239816 543041 := bstep (se 2 (by rfl) ⟨203640, by rfl⟩ : syracuseStep 543041 = 407281) B407281
theorem B608705 : Blo 239816 608705 := bstep (se 2 (by rfl) ⟨228264, by rfl⟩ : syracuseStep 608705 = 456529) B456529
theorem B9423373 : Blo 239816 9423373 := bstep (se 3 (by rfl) ⟨1766882, by rfl⟩ : syracuseStep 9423373 = 3533765) B3533765
theorem B543257 : Blo 239816 543257 := bstep (se 2 (by rfl) ⟨203721, by rfl⟩ : syracuseStep 543257 = 407443) B407443
theorem B3951179 : Blo 239816 3951179 := bstep (se 1 (by rfl) ⟨2963384, by rfl⟩ : syracuseStep 3951179 = 5926769) B5926769
theorem B543347 : Blo 239816 543347 := bstep (se 1 (by rfl) ⟨407510, by rfl⟩ : syracuseStep 543347 = 815021) B815021
theorem B543383 : Blo 239816 543383 := bstep (se 1 (by rfl) ⟨407537, by rfl⟩ : syracuseStep 543383 = 815075) B815075
theorem B543563 : Blo 239816 543563 := bstep (se 1 (by rfl) ⟨407672, by rfl⟩ : syracuseStep 543563 = 815345) B815345
theorem B543617 : Blo 239816 543617 := bstep (se 2 (by rfl) ⟨203856, by rfl⟩ : syracuseStep 543617 = 407713) B407713
theorem B347095 : Blo 239816 347095 := bstep (se 1 (by rfl) ⟨260321, by rfl⟩ : syracuseStep 347095 = 520643) B520643
theorem B609241 : Blo 239816 609241 := bstep (se 2 (by rfl) ⟨228465, by rfl⟩ : syracuseStep 609241 = 456931) B456931
theorem B543833 : Blo 239816 543833 := bstep (se 2 (by rfl) ⟨203937, by rfl⟩ : syracuseStep 543833 = 407875) B407875
theorem B543923 : Blo 239816 543923 := bstep (se 1 (by rfl) ⟨407942, by rfl⟩ : syracuseStep 543923 = 815885) B815885
theorem B1133747 : Blo 239816 1133747 := bstep (se 1 (by rfl) ⟨850310, by rfl⟩ : syracuseStep 1133747 = 1700621) B1700621
theorem B1035443 : Blo 239816 1035443 := bstep (se 1 (by rfl) ⟨776582, by rfl⟩ : syracuseStep 1035443 = 1553165) B1553165
theorem B543959 : Blo 239816 543959 := bstep (se 1 (by rfl) ⟨407969, by rfl⟩ : syracuseStep 543959 = 815939) B815939
theorem B544139 : Blo 239816 544139 := bstep (se 1 (by rfl) ⟨408104, by rfl⟩ : syracuseStep 544139 = 816209) B816209
theorem B544193 : Blo 239816 544193 := bstep (se 2 (by rfl) ⟨204072, by rfl⟩ : syracuseStep 544193 = 408145) B408145
theorem B544409 : Blo 239816 544409 := bstep (se 2 (by rfl) ⟨204153, by rfl⟩ : syracuseStep 544409 = 408307) B408307
theorem B544499 : Blo 239816 544499 := bstep (se 1 (by rfl) ⟨408374, by rfl⟩ : syracuseStep 544499 = 816749) B816749
theorem B1232657 : Blo 239816 1232657 := bstep (se 2 (by rfl) ⟨462246, by rfl⟩ : syracuseStep 1232657 = 924493) B924493
theorem B544535 : Blo 239816 544535 := bstep (se 1 (by rfl) ⟨408401, by rfl⟩ : syracuseStep 544535 = 816803) B816803
theorem B1822499 : Blo 239816 1822499 := bstep (se 1 (by rfl) ⟨1366874, by rfl⟩ : syracuseStep 1822499 = 2733749) B2733749
theorem B577459 : Blo 239816 577459 := bstep (se 1 (by rfl) ⟨433094, by rfl⟩ : syracuseStep 577459 = 866189) B866189
theorem B1232819 : Blo 239816 1232819 := bstep (se 1 (by rfl) ⟨924614, by rfl⟩ : syracuseStep 1232819 = 1849229) B1849229
theorem B544715 : Blo 239816 544715 := bstep (se 1 (by rfl) ⟨408536, by rfl⟩ : syracuseStep 544715 = 817073) B817073
theorem B544769 : Blo 239816 544769 := bstep (se 2 (by rfl) ⟨204288, by rfl⟩ : syracuseStep 544769 = 408577) B408577
theorem B610355 : Blo 239816 610355 := bstep (se 1 (by rfl) ⟨457766, by rfl⟩ : syracuseStep 610355 = 915533) B915533
theorem B4739147 : Blo 239816 4739147 := bstep (se 1 (by rfl) ⟨3554360, by rfl⟩ : syracuseStep 4739147 = 7108721) B7108721
theorem B512203 : Blo 239816 512203 := bstep (se 1 (by rfl) ⟨384152, by rfl⟩ : syracuseStep 512203 = 768305) B768305
theorem B544985 : Blo 239816 544985 := bstep (se 2 (by rfl) ⟨204369, by rfl⟩ : syracuseStep 544985 = 408739) B408739
theorem B545075 : Blo 239816 545075 := bstep (se 1 (by rfl) ⟨408806, by rfl⟩ : syracuseStep 545075 = 817613) B817613
theorem B545111 : Blo 239816 545111 := bstep (se 1 (by rfl) ⟨408833, by rfl⟩ : syracuseStep 545111 = 817667) B817667
theorem B610649 : Blo 239816 610649 := bstep (se 2 (by rfl) ⟨228993, by rfl⟩ : syracuseStep 610649 = 457987) B457987
theorem B545291 : Blo 239816 545291 := bstep (se 1 (by rfl) ⟨408968, by rfl⟩ : syracuseStep 545291 = 817937) B817937
theorem B545345 : Blo 239816 545345 := bstep (se 2 (by rfl) ⟨204504, by rfl⟩ : syracuseStep 545345 = 409009) B409009
theorem B1659457 : Blo 239816 1659457 := bstep (se 2 (by rfl) ⟨622296, by rfl⟩ : syracuseStep 1659457 = 1244593) B1244593
theorem B348889 : Blo 239816 348889 := bstep (se 2 (by rfl) ⟨130833, by rfl⟩ : syracuseStep 348889 = 261667) B261667
theorem B545561 : Blo 239816 545561 := bstep (se 2 (by rfl) ⟨204585, by rfl⟩ : syracuseStep 545561 = 409171) B409171
theorem B545651 : Blo 239816 545651 := bstep (se 1 (by rfl) ⟨409238, by rfl⟩ : syracuseStep 545651 = 818477) B818477
theorem B545687 : Blo 239816 545687 := bstep (se 1 (by rfl) ⟨409265, by rfl⟩ : syracuseStep 545687 = 818531) B818531
theorem B513049 : Blo 239816 513049 := bstep (se 2 (by rfl) ⟨192393, by rfl⟩ : syracuseStep 513049 = 384787) B384787
theorem B1037357 : Blo 239816 1037357 := bstep (se 3 (by rfl) ⟨194504, by rfl⟩ : syracuseStep 1037357 = 389009) B389009
theorem B545867 : Blo 239816 545867 := bstep (se 1 (by rfl) ⟨409400, by rfl⟩ : syracuseStep 545867 = 818801) B818801
theorem B545921 : Blo 239816 545921 := bstep (se 2 (by rfl) ⟨204720, by rfl⟩ : syracuseStep 545921 = 409441) B409441
theorem B5002501 : Blo 239816 5002501 := bstep (se 4 (by rfl) ⟨468984, by rfl⟩ : syracuseStep 5002501 = 937969) B937969
theorem B546137 : Blo 239816 546137 := bstep (se 2 (by rfl) ⟨204801, by rfl⟩ : syracuseStep 546137 = 409603) B409603
theorem B546227 : Blo 239816 546227 := bstep (se 1 (by rfl) ⟨409670, by rfl⟩ : syracuseStep 546227 = 819341) B819341
theorem B546263 : Blo 239816 546263 := bstep (se 1 (by rfl) ⟨409697, by rfl⟩ : syracuseStep 546263 = 819395) B819395
theorem B546443 : Blo 239816 546443 := bstep (se 1 (by rfl) ⟨409832, by rfl⟩ : syracuseStep 546443 = 819665) B819665
theorem B546497 : Blo 239816 546497 := bstep (se 2 (by rfl) ⟨204936, by rfl⟩ : syracuseStep 546497 = 409873) B409873
theorem B1038041 : Blo 239816 1038041 := bstep (se 2 (by rfl) ⟨389265, by rfl⟩ : syracuseStep 1038041 = 778531) B778531
theorem B546713 : Blo 239816 546713 := bstep (se 2 (by rfl) ⟨205017, by rfl⟩ : syracuseStep 546713 = 410035) B410035
theorem B874433 : Blo 239816 874433 := bstep (se 2 (by rfl) ⟨327912, by rfl⟩ : syracuseStep 874433 = 655825) B655825
theorem B612299 : Blo 239816 612299 := bstep (se 1 (by rfl) ⟨459224, by rfl⟩ : syracuseStep 612299 = 918449) B918449
theorem B546803 : Blo 239816 546803 := bstep (se 1 (by rfl) ⟨410102, by rfl⟩ : syracuseStep 546803 = 820205) B820205
theorem B546839 : Blo 239816 546839 := bstep (se 1 (by rfl) ⟨410129, by rfl⟩ : syracuseStep 546839 = 820259) B820259
theorem B12572813 : Blo 239816 12572813 := bstep (se 3 (by rfl) ⟨2357402, by rfl⟩ : syracuseStep 12572813 = 4714805) B4714805
theorem B547019 : Blo 239816 547019 := bstep (se 1 (by rfl) ⟨410264, by rfl⟩ : syracuseStep 547019 = 820529) B820529
theorem B547073 : Blo 239816 547073 := bstep (se 2 (by rfl) ⟨205152, by rfl⟩ : syracuseStep 547073 = 410305) B410305
theorem B2283821 : Blo 239816 2283821 := bstep (se 3 (by rfl) ⟨428216, by rfl⟩ : syracuseStep 2283821 = 856433) B856433
theorem B514355 : Blo 239816 514355 := bstep (se 1 (by rfl) ⟨385766, by rfl⟩ : syracuseStep 514355 = 771533) B771533
theorem B1169795 : Blo 239816 1169795 := bstep (se 1 (by rfl) ⟨877346, by rfl⟩ : syracuseStep 1169795 = 1754693) B1754693
theorem B547289 : Blo 239816 547289 := bstep (se 2 (by rfl) ⟨205233, by rfl⟩ : syracuseStep 547289 = 410467) B410467
theorem B1989137 : Blo 239816 1989137 := bstep (se 2 (by rfl) ⟨745926, by rfl⟩ : syracuseStep 1989137 = 1491853) B1491853
theorem B547379 : Blo 239816 547379 := bstep (se 1 (by rfl) ⟨410534, by rfl⟩ : syracuseStep 547379 = 821069) B821069
theorem B547415 : Blo 239816 547415 := bstep (se 1 (by rfl) ⟨410561, by rfl⟩ : syracuseStep 547415 = 821123) B821123
theorem B7494275 : Blo 239816 7494275 := bstep (se 1 (by rfl) ⟨5620706, by rfl⟩ : syracuseStep 7494275 = 11241413) B11241413
theorem B809675 : Blo 239816 809675 := bstep (se 1 (by rfl) ⟨607256, by rfl⟩ : syracuseStep 809675 = 1214513) B1214513
theorem B547595 : Blo 239816 547595 := bstep (se 1 (by rfl) ⟨410696, by rfl⟩ : syracuseStep 547595 = 821393) B821393
theorem B547649 : Blo 239816 547649 := bstep (se 2 (by rfl) ⟨205368, by rfl⟩ : syracuseStep 547649 = 410737) B410737
theorem B875357 : Blo 239816 875357 := bstep (se 3 (by rfl) ⟨164129, by rfl⟩ : syracuseStep 875357 = 328259) B328259
theorem B613271 : Blo 239816 613271 := bstep (se 1 (by rfl) ⟨459953, by rfl⟩ : syracuseStep 613271 = 919907) B919907
theorem B809945 : Blo 239816 809945 := bstep (se 2 (by rfl) ⟨303729, by rfl⟩ : syracuseStep 809945 = 607459) B607459
theorem B1367057 : Blo 239816 1367057 := bstep (se 2 (by rfl) ⟨512646, by rfl⟩ : syracuseStep 1367057 = 1025293) B1025293
theorem B1170449 : Blo 239816 1170449 := bstep (se 2 (by rfl) ⟨438918, by rfl⟩ : syracuseStep 1170449 = 877837) B877837
theorem B547865 : Blo 239816 547865 := bstep (se 2 (by rfl) ⟨205449, by rfl⟩ : syracuseStep 547865 = 410899) B410899
theorem B2055233 : Blo 239816 2055233 := bstep (se 2 (by rfl) ⟨770712, by rfl⟩ : syracuseStep 2055233 = 1541425) B1541425
theorem B547955 : Blo 239816 547955 := bstep (se 1 (by rfl) ⟨410966, by rfl⟩ : syracuseStep 547955 = 821933) B821933
theorem B547991 : Blo 239816 547991 := bstep (se 1 (by rfl) ⟨410993, by rfl⟩ : syracuseStep 547991 = 821987) B821987
theorem B548171 : Blo 239816 548171 := bstep (se 1 (by rfl) ⟨411128, by rfl⟩ : syracuseStep 548171 = 822257) B822257
theorem B548225 : Blo 239816 548225 := bstep (se 2 (by rfl) ⟨205584, by rfl⟩ : syracuseStep 548225 = 411169) B411169
theorem B417239 : Blo 239816 417239 := bstep (se 1 (by rfl) ⟨312929, by rfl⟩ : syracuseStep 417239 = 625859) B625859
theorem B1367513 : Blo 239816 1367513 := bstep (se 2 (by rfl) ⟨512817, by rfl⟩ : syracuseStep 1367513 = 1025635) B1025635
theorem B613939 : Blo 239816 613939 := bstep (se 1 (by rfl) ⟨460454, by rfl⟩ : syracuseStep 613939 = 920909) B920909
theorem B384601 : Blo 239816 384601 := bstep (se 2 (by rfl) ⟨144225, by rfl⟩ : syracuseStep 384601 = 288451) B288451
theorem B548441 : Blo 239816 548441 := bstep (se 2 (by rfl) ⟨205665, by rfl⟩ : syracuseStep 548441 = 411331) B411331
theorem B810647 : Blo 239816 810647 := bstep (se 1 (by rfl) ⟨607985, by rfl⟩ : syracuseStep 810647 = 1215971) B1215971
theorem B548531 : Blo 239816 548531 := bstep (se 1 (by rfl) ⟨411398, by rfl⟩ : syracuseStep 548531 = 822797) B822797
theorem B614081 : Blo 239816 614081 := bstep (se 2 (by rfl) ⟨230280, by rfl⟩ : syracuseStep 614081 = 460561) B460561
theorem B548567 : Blo 239816 548567 := bstep (se 1 (by rfl) ⟨411425, by rfl⟩ : syracuseStep 548567 = 822851) B822851
theorem B515927 : Blo 239816 515927 := bstep (se 1 (by rfl) ⟨386945, by rfl⟩ : syracuseStep 515927 = 773891) B773891
theorem B974771 : Blo 239816 974771 := bstep (se 1 (by rfl) ⟨731078, by rfl⟩ : syracuseStep 974771 = 1462157) B1462157
theorem B876509 : Blo 239816 876509 := bstep (se 3 (by rfl) ⟨164345, by rfl⟩ : syracuseStep 876509 = 328691) B328691
theorem B516235 : Blo 239816 516235 := bstep (se 1 (by rfl) ⟨387176, by rfl⟩ : syracuseStep 516235 = 774353) B774353
theorem B811187 : Blo 239816 811187 := bstep (se 1 (by rfl) ⟨608390, by rfl⟩ : syracuseStep 811187 = 1216781) B1216781
theorem B909515 : Blo 239816 909515 := bstep (se 1 (by rfl) ⟨682136, by rfl⟩ : syracuseStep 909515 = 1364273) B1364273
theorem B93184277 : Blo 239816 93184277 := bstep (se 6 (by rfl) ⟨2184006, by rfl⟩ : syracuseStep 93184277 = 4368013) B4368013
theorem B549185 : Blo 239816 549185 := bstep (se 2 (by rfl) ⟨205944, by rfl⟩ : syracuseStep 549185 = 411889) B411889
theorem B811457 : Blo 239816 811457 := bstep (se 2 (by rfl) ⟨304296, by rfl⟩ : syracuseStep 811457 = 608593) B608593
theorem B2614133 : Blo 239816 2614133 := bstep (se 5 (by rfl) ⟨122537, by rfl⟩ : syracuseStep 2614133 = 245075) B245075
theorem B8479667 : Blo 239816 8479667 := bstep (se 1 (by rfl) ⟨6359750, by rfl⟩ : syracuseStep 8479667 = 12719501) B12719501
theorem B615347 : Blo 239816 615347 := bstep (se 1 (by rfl) ⟨461510, by rfl⟩ : syracuseStep 615347 = 923021) B923021
theorem B975809 : Blo 239816 975809 := bstep (se 2 (by rfl) ⟨365928, by rfl⟩ : syracuseStep 975809 = 731857) B731857
theorem B811997 : Blo 239816 811997 := bstep (se 3 (by rfl) ⟨152249, by rfl⟩ : syracuseStep 811997 = 304499) B304499
theorem B1827845 : Blo 239816 1827845 := bstep (se 4 (by rfl) ⟨171360, by rfl⟩ : syracuseStep 1827845 = 342721) B342721
theorem B648343 : Blo 239816 648343 := bstep (se 1 (by rfl) ⟨486257, by rfl⟩ : syracuseStep 648343 = 972515) B972515
theorem B1959173 : Blo 239816 1959173 := bstep (se 4 (by rfl) ⟨183672, by rfl⟩ : syracuseStep 1959173 = 367345) B367345
theorem B2090285 : Blo 239816 2090285 := bstep (se 3 (by rfl) ⟨391928, by rfl⟩ : syracuseStep 2090285 = 783857) B783857
theorem B517465 : Blo 239816 517465 := bstep (se 2 (by rfl) ⟨194049, by rfl⟩ : syracuseStep 517465 = 388099) B388099
theorem B615883 : Blo 239816 615883 := bstep (se 1 (by rfl) ⟨461912, by rfl⟩ : syracuseStep 615883 = 923825) B923825
theorem B550361 : Blo 239816 550361 := bstep (se 2 (by rfl) ⟨206385, by rfl⟩ : syracuseStep 550361 = 412771) B412771
theorem B910871 : Blo 239816 910871 := bstep (se 1 (by rfl) ⟨683153, by rfl⟩ : syracuseStep 910871 = 1366307) B1366307
theorem B616025 : Blo 239816 616025 := bstep (se 2 (by rfl) ⟨231009, by rfl⟩ : syracuseStep 616025 = 462019) B462019
theorem B550579 : Blo 239816 550579 := bstep (se 1 (by rfl) ⟨412934, by rfl⟩ : syracuseStep 550579 = 825869) B825869
theorem B8775701 : Blo 239816 8775701 := bstep (se 6 (by rfl) ⟨205680, by rfl⟩ : syracuseStep 8775701 = 411361) B411361
theorem B813131 : Blo 239816 813131 := bstep (se 1 (by rfl) ⟨609848, by rfl⟩ : syracuseStep 813131 = 1219697) B1219697
theorem B813401 : Blo 239816 813401 := bstep (se 2 (by rfl) ⟨305025, by rfl⟩ : syracuseStep 813401 = 610051) B610051
theorem B256375 : Blo 239816 256375 := bstep (se 1 (by rfl) ⟨192281, by rfl⟩ : syracuseStep 256375 = 384563) B384563
theorem B616855 : Blo 239816 616855 := bstep (se 1 (by rfl) ⟨462641, by rfl⟩ : syracuseStep 616855 = 925283) B925283
theorem B354775 : Blo 239816 354775 := bstep (se 1 (by rfl) ⟨266081, by rfl⟩ : syracuseStep 354775 = 532163) B532163
theorem B551603 : Blo 239816 551603 := bstep (se 1 (by rfl) ⟨413702, by rfl⟩ : syracuseStep 551603 = 827405) B827405
theorem B1043147 : Blo 239816 1043147 := bstep (se 1 (by rfl) ⟨782360, by rfl⟩ : syracuseStep 1043147 = 1564721) B1564721
theorem B912131 : Blo 239816 912131 := bstep (se 1 (by rfl) ⟨684098, by rfl⟩ : syracuseStep 912131 = 1368197) B1368197
theorem B814103 : Blo 239816 814103 := bstep (se 1 (by rfl) ⟨610577, by rfl⟩ : syracuseStep 814103 = 1221155) B1221155
theorem B257195 : Blo 239816 257195 := bstep (se 1 (by rfl) ⟨192896, by rfl⟩ : syracuseStep 257195 = 385793) B385793
theorem B486679 : Blo 239816 486679 := bstep (se 1 (by rfl) ⟨365009, by rfl⟩ : syracuseStep 486679 = 730019) B730019
theorem B978227 : Blo 239816 978227 := bstep (se 1 (by rfl) ⟨733670, by rfl⟩ : syracuseStep 978227 = 1467341) B1467341
theorem B1830275 : Blo 239816 1830275 := bstep (se 1 (by rfl) ⟨1372706, by rfl⟩ : syracuseStep 1830275 = 2745413) B2745413
theorem B650713 : Blo 239816 650713 := bstep (se 2 (by rfl) ⟨244017, by rfl⟩ : syracuseStep 650713 = 488035) B488035
theorem B814643 : Blo 239816 814643 := bstep (se 1 (by rfl) ⟨610982, by rfl⟩ : syracuseStep 814643 = 1221965) B1221965
theorem B487127 : Blo 239816 487127 := bstep (se 1 (by rfl) ⟨365345, by rfl⟩ : syracuseStep 487127 = 730691) B730691
theorem B6942449 : Blo 239816 6942449 := bstep (se 2 (by rfl) ⟨2603418, by rfl⟩ : syracuseStep 6942449 = 5206837) B5206837
theorem B7499573 : Blo 239816 7499573 := bstep (se 5 (by rfl) ⟨351542, by rfl⟩ : syracuseStep 7499573 = 703085) B703085
theorem B814913 : Blo 239816 814913 := bstep (se 2 (by rfl) ⟨305592, by rfl⟩ : syracuseStep 814913 = 611185) B611185
theorem B684121 : Blo 239816 684121 := bstep (se 2 (by rfl) ⟨256545, by rfl⟩ : syracuseStep 684121 = 513091) B513091
theorem B1339523 : Blo 239816 1339523 := bstep (se 1 (by rfl) ⟨1004642, by rfl⟩ : syracuseStep 1339523 = 2009285) B2009285
theorem B520499 : Blo 239816 520499 := bstep (se 1 (by rfl) ⟨390374, by rfl⟩ : syracuseStep 520499 = 780749) B780749
theorem B258391 : Blo 239816 258391 := bstep (se 1 (by rfl) ⟨193793, by rfl⟩ : syracuseStep 258391 = 387587) B387587
theorem B815453 : Blo 239816 815453 := bstep (se 3 (by rfl) ⟨152897, by rfl⟩ : syracuseStep 815453 = 305795) B305795
theorem B1045037 : Blo 239816 1045037 := bstep (se 3 (by rfl) ⟨195944, by rfl⟩ : syracuseStep 1045037 = 391889) B391889
theorem B258647 : Blo 239816 258647 := bstep (se 1 (by rfl) ⟨193985, by rfl⟩ : syracuseStep 258647 = 387971) B387971
theorem B455321 : Blo 239816 455321 := bstep (se 2 (by rfl) ⟨170745, by rfl⟩ : syracuseStep 455321 = 341491) B341491
theorem B684737 : Blo 239816 684737 := bstep (se 2 (by rfl) ⟨256776, by rfl⟩ : syracuseStep 684737 = 513553) B513553
theorem B1372889 : Blo 239816 1372889 := bstep (se 2 (by rfl) ⟨514833, by rfl⟩ : syracuseStep 1372889 = 1029667) B1029667
theorem B3994373 : Blo 239816 3994373 := bstep (se 4 (by rfl) ⟨374472, by rfl⟩ : syracuseStep 3994373 = 748945) B748945
theorem B259211 : Blo 239816 259211 := bstep (se 1 (by rfl) ⟨194408, by rfl⟩ : syracuseStep 259211 = 388817) B388817
theorem B881867 : Blo 239816 881867 := bstep (se 1 (by rfl) ⟨661400, by rfl⟩ : syracuseStep 881867 = 1322801) B1322801
theorem B455959 : Blo 239816 455959 := bstep (se 1 (by rfl) ⟨341969, by rfl⟩ : syracuseStep 455959 = 683939) B683939
theorem B390425 : Blo 239816 390425 := bstep (se 2 (by rfl) ⟨146409, by rfl⟩ : syracuseStep 390425 = 292819) B292819
theorem B1537325 : Blo 239816 1537325 := bstep (se 3 (by rfl) ⟨288248, by rfl⟩ : syracuseStep 1537325 = 576497) B576497
theorem B488755 : Blo 239816 488755 := bstep (se 1 (by rfl) ⟨366566, by rfl⟩ : syracuseStep 488755 = 733133) B733133
theorem B816587 : Blo 239816 816587 := bstep (se 1 (by rfl) ⟨612440, by rfl⟩ : syracuseStep 816587 = 1224881) B1224881
theorem B587287 : Blo 239816 587287 := bstep (se 1 (by rfl) ⟨440465, by rfl⟩ : syracuseStep 587287 = 880931) B880931
theorem B488983 : Blo 239816 488983 := bstep (se 1 (by rfl) ⟨366737, by rfl⟩ : syracuseStep 488983 = 733475) B733475
theorem B816857 : Blo 239816 816857 := bstep (se 2 (by rfl) ⟨306321, by rfl⟩ : syracuseStep 816857 = 612643) B612643
theorem B292631 : Blo 239816 292631 := bstep (se 1 (by rfl) ⟨219473, by rfl⟩ : syracuseStep 292631 = 438947) B438947
theorem B554777 : Blo 239816 554777 := bstep (se 2 (by rfl) ⟨208041, by rfl⟩ : syracuseStep 554777 = 416083) B416083
theorem B915245 : Blo 239816 915245 := bstep (se 3 (by rfl) ⟨171608, by rfl⟩ : syracuseStep 915245 = 343217) B343217
theorem B292747 : Blo 239816 292747 := bstep (se 1 (by rfl) ⟨219560, by rfl⟩ : syracuseStep 292747 = 439121) B439121
theorem B7010225 : Blo 239816 7010225 := bstep (se 2 (by rfl) ⟨2628834, by rfl⟩ : syracuseStep 7010225 = 5257669) B5257669
theorem B555031 : Blo 239816 555031 := bstep (se 1 (by rfl) ⟨416273, by rfl⟩ : syracuseStep 555031 = 832547) B832547
theorem B456779 : Blo 239816 456779 := bstep (se 1 (by rfl) ⟨342584, by rfl⟩ : syracuseStep 456779 = 685169) B685169
theorem B456833 : Blo 239816 456833 := bstep (se 2 (by rfl) ⟨171312, by rfl⟩ : syracuseStep 456833 = 342625) B342625
theorem B11794733 : Blo 239816 11794733 := bstep (se 3 (by rfl) ⟨2211512, by rfl⟩ : syracuseStep 11794733 = 4423025) B4423025
theorem B1374529 : Blo 239816 1374529 := bstep (se 2 (by rfl) ⟨515448, by rfl⟩ : syracuseStep 1374529 = 1030897) B1030897
theorem B817559 : Blo 239816 817559 := bstep (se 1 (by rfl) ⟨613169, by rfl⟩ : syracuseStep 817559 = 1226339) B1226339
theorem B3504653 : Blo 239816 3504653 := bstep (se 3 (by rfl) ⟨657122, by rfl⟩ : syracuseStep 3504653 = 1314245) B1314245
theorem B916019 : Blo 239816 916019 := bstep (se 1 (by rfl) ⟨687014, by rfl⟩ : syracuseStep 916019 = 1374029) B1374029
theorem B3078749 : Blo 239816 3078749 := bstep (se 3 (by rfl) ⟨577265, by rfl⟩ : syracuseStep 3078749 = 1154531) B1154531
theorem B1833677 : Blo 239816 1833677 := bstep (se 3 (by rfl) ⟨343814, by rfl⟩ : syracuseStep 1833677 = 687629) B687629
theorem B686809 : Blo 239816 686809 := bstep (se 2 (by rfl) ⟨257553, by rfl⟩ : syracuseStep 686809 = 515107) B515107
theorem B260983 : Blo 239816 260983 := bstep (se 1 (by rfl) ⟨195737, by rfl⟩ : syracuseStep 260983 = 391475) B391475
theorem B818099 : Blo 239816 818099 := bstep (se 1 (by rfl) ⟨613574, by rfl⟩ : syracuseStep 818099 = 1227149) B1227149
theorem B457751 : Blo 239816 457751 := bstep (se 1 (by rfl) ⟨343313, by rfl⟩ : syracuseStep 457751 = 686627) B686627
theorem B687197 : Blo 239816 687197 := bstep (se 3 (by rfl) ⟨128849, by rfl⟩ : syracuseStep 687197 = 257699) B257699
theorem B1834163 : Blo 239816 1834163 := bstep (se 1 (by rfl) ⟨1375622, by rfl⟩ : syracuseStep 1834163 = 2751245) B2751245
theorem B818369 : Blo 239816 818369 := bstep (se 2 (by rfl) ⟨306888, by rfl⟩ : syracuseStep 818369 = 613777) B613777
theorem B359819 : Blo 239816 359819 := bstep (se 1 (by rfl) ⟨269864, by rfl⟩ : syracuseStep 359819 = 539729) B539729
theorem B359831 : Blo 239816 359831 := bstep (se 1 (by rfl) ⟨269873, by rfl⟩ : syracuseStep 359831 = 539747) B539747
theorem B359897 : Blo 239816 359897 := bstep (se 2 (by rfl) ⟨134961, by rfl⟩ : syracuseStep 359897 = 269923) B269923
theorem B458291 : Blo 239816 458291 := bstep (se 1 (by rfl) ⟨343718, by rfl⟩ : syracuseStep 458291 = 687437) B687437
theorem B491059 : Blo 239816 491059 := bstep (se 1 (by rfl) ⟨368294, by rfl⟩ : syracuseStep 491059 = 736589) B736589
theorem B360011 : Blo 239816 360011 := bstep (se 1 (by rfl) ⟨270008, by rfl⟩ : syracuseStep 360011 = 540017) B540017
theorem B360023 : Blo 239816 360023 := bstep (se 1 (by rfl) ⟨270017, by rfl⟩ : syracuseStep 360023 = 540035) B540035
theorem B327307 : Blo 239816 327307 := bstep (se 1 (by rfl) ⟨245480, by rfl⟩ : syracuseStep 327307 = 490961) B490961
theorem B360089 : Blo 239816 360089 := bstep (se 2 (by rfl) ⟨135033, by rfl⟩ : syracuseStep 360089 = 270067) B270067
theorem B818909 : Blo 239816 818909 := bstep (se 3 (by rfl) ⟨153545, by rfl⟩ : syracuseStep 818909 = 307091) B307091
theorem B360203 : Blo 239816 360203 := bstep (se 1 (by rfl) ⟨270152, by rfl⟩ : syracuseStep 360203 = 540305) B540305
theorem B360215 : Blo 239816 360215 := bstep (se 1 (by rfl) ⟨270161, by rfl⟩ : syracuseStep 360215 = 540323) B540323
theorem B360281 : Blo 239816 360281 := bstep (se 2 (by rfl) ⟨135105, by rfl⟩ : syracuseStep 360281 = 270211) B270211
theorem B1965917 : Blo 239816 1965917 := bstep (se 3 (by rfl) ⟨368609, by rfl⟩ : syracuseStep 1965917 = 737219) B737219
theorem B360395 : Blo 239816 360395 := bstep (se 1 (by rfl) ⟨270296, by rfl⟩ : syracuseStep 360395 = 540593) B540593
theorem B360407 : Blo 239816 360407 := bstep (se 1 (by rfl) ⟨270305, by rfl⟩ : syracuseStep 360407 = 540611) B540611
theorem B360455 : Blo 239816 360455 := bstep (se 1 (by rfl) ⟨270341, by rfl⟩ : syracuseStep 360455 = 540683) B540683
theorem B360491 : Blo 239816 360491 := bstep (se 1 (by rfl) ⟨270368, by rfl⟩ : syracuseStep 360491 = 540737) B540737
theorem B360521 : Blo 239816 360521 := bstep (se 2 (by rfl) ⟨135195, by rfl⟩ : syracuseStep 360521 = 270391) B270391
theorem B819287 : Blo 239816 819287 := bstep (se 1 (by rfl) ⟨614465, by rfl⟩ : syracuseStep 819287 = 1228931) B1228931
theorem B688313 : Blo 239816 688313 := bstep (se 2 (by rfl) ⟨258117, by rfl⟩ : syracuseStep 688313 = 516235) B516235
theorem B360635 : Blo 239816 360635 := bstep (se 1 (by rfl) ⟨270476, by rfl⟩ : syracuseStep 360635 = 540953) B540953
theorem B360695 : Blo 239816 360695 := bstep (se 1 (by rfl) ⟨270521, by rfl⟩ : syracuseStep 360695 = 541043) B541043
theorem B1376513 : Blo 239816 1376513 := bstep (se 2 (by rfl) ⟨516192, by rfl⟩ : syracuseStep 1376513 = 1032385) B1032385
theorem B360719 : Blo 239816 360719 := bstep (se 1 (by rfl) ⟨270539, by rfl⟩ : syracuseStep 360719 = 541079) B541079
theorem B360761 : Blo 239816 360761 := bstep (se 2 (by rfl) ⟨135285, by rfl⟩ : syracuseStep 360761 = 270571) B270571
theorem B360839 : Blo 239816 360839 := bstep (se 1 (by rfl) ⟨270629, by rfl⟩ : syracuseStep 360839 = 541259) B541259
theorem B360875 : Blo 239816 360875 := bstep (se 1 (by rfl) ⟨270656, by rfl⟩ : syracuseStep 360875 = 541313) B541313
theorem B360905 : Blo 239816 360905 := bstep (se 2 (by rfl) ⟨135339, by rfl⟩ : syracuseStep 360905 = 270679) B270679
theorem B459209 : Blo 239816 459209 := bstep (se 2 (by rfl) ⟨172203, by rfl⟩ : syracuseStep 459209 = 344407) B344407
theorem B688655 : Blo 239816 688655 := bstep (se 1 (by rfl) ⟨516491, by rfl⟩ : syracuseStep 688655 = 1032983) B1032983
theorem B2425373 : Blo 239816 2425373 := bstep (se 3 (by rfl) ⟨454757, by rfl⟩ : syracuseStep 2425373 = 909515) B909515
theorem B361019 : Blo 239816 361019 := bstep (se 1 (by rfl) ⟨270764, by rfl⟩ : syracuseStep 361019 = 541529) B541529
theorem B819773 : Blo 239816 819773 := bstep (se 3 (by rfl) ⟨153707, by rfl⟩ : syracuseStep 819773 = 307415) B307415
theorem B361079 : Blo 239816 361079 := bstep (se 1 (by rfl) ⟨270809, by rfl⟩ : syracuseStep 361079 = 541619) B541619
theorem B361103 : Blo 239816 361103 := bstep (se 1 (by rfl) ⟨270827, by rfl⟩ : syracuseStep 361103 = 541655) B541655
theorem B361145 : Blo 239816 361145 := bstep (se 2 (by rfl) ⟨135429, by rfl⟩ : syracuseStep 361145 = 270859) B270859
theorem B361223 : Blo 239816 361223 := bstep (se 1 (by rfl) ⟨270917, by rfl⟩ : syracuseStep 361223 = 541835) B541835
theorem B361259 : Blo 239816 361259 := bstep (se 1 (by rfl) ⟨270944, by rfl⟩ : syracuseStep 361259 = 541889) B541889
theorem B361289 : Blo 239816 361289 := bstep (se 2 (by rfl) ⟨135483, by rfl⟩ : syracuseStep 361289 = 270967) B270967
theorem B361403 : Blo 239816 361403 := bstep (se 1 (by rfl) ⟨271052, by rfl⟩ : syracuseStep 361403 = 542105) B542105
theorem B361463 : Blo 239816 361463 := bstep (se 1 (by rfl) ⟨271097, by rfl⟩ : syracuseStep 361463 = 542195) B542195
theorem B361487 : Blo 239816 361487 := bstep (se 1 (by rfl) ⟨271115, by rfl⟩ : syracuseStep 361487 = 542231) B542231
theorem B361529 : Blo 239816 361529 := bstep (se 2 (by rfl) ⟨135573, by rfl⟩ : syracuseStep 361529 = 271147) B271147
theorem B918647 : Blo 239816 918647 := bstep (se 1 (by rfl) ⟨688985, by rfl⟩ : syracuseStep 918647 = 1377971) B1377971
theorem B361607 : Blo 239816 361607 := bstep (se 1 (by rfl) ⟨271205, by rfl⟩ : syracuseStep 361607 = 542411) B542411
theorem B361643 : Blo 239816 361643 := bstep (se 1 (by rfl) ⟨271232, by rfl⟩ : syracuseStep 361643 = 542465) B542465
theorem B361673 : Blo 239816 361673 := bstep (se 2 (by rfl) ⟨135627, by rfl⟩ : syracuseStep 361673 = 271255) B271255
theorem B328951 : Blo 239816 328951 := bstep (se 1 (by rfl) ⟨246713, by rfl⟩ : syracuseStep 328951 = 493427) B493427
theorem B460075 : Blo 239816 460075 := bstep (se 1 (by rfl) ⟨345056, by rfl⟩ : syracuseStep 460075 = 690113) B690113
theorem B361787 : Blo 239816 361787 := bstep (se 1 (by rfl) ⟨271340, by rfl⟩ : syracuseStep 361787 = 542681) B542681
theorem B361847 : Blo 239816 361847 := bstep (se 1 (by rfl) ⟨271385, by rfl⟩ : syracuseStep 361847 = 542771) B542771
theorem B460151 : Blo 239816 460151 := bstep (se 1 (by rfl) ⟨345113, by rfl⟩ : syracuseStep 460151 = 690227) B690227
theorem B4982147 : Blo 239816 4982147 := bstep (se 1 (by rfl) ⟨3736610, by rfl⟩ : syracuseStep 4982147 = 7473221) B7473221
theorem B689543 : Blo 239816 689543 := bstep (se 1 (by rfl) ⟨517157, by rfl⟩ : syracuseStep 689543 = 1034315) B1034315
theorem B361871 : Blo 239816 361871 := bstep (se 1 (by rfl) ⟨271403, by rfl⟩ : syracuseStep 361871 = 542807) B542807
theorem B361913 : Blo 239816 361913 := bstep (se 2 (by rfl) ⟨135717, by rfl⟩ : syracuseStep 361913 = 271435) B271435
theorem B361991 : Blo 239816 361991 := bstep (se 1 (by rfl) ⟨271493, by rfl⟩ : syracuseStep 361991 = 542987) B542987
theorem B362027 : Blo 239816 362027 := bstep (se 1 (by rfl) ⟨271520, by rfl⟩ : syracuseStep 362027 = 543041) B543041
theorem B689725 : Blo 239816 689725 := bstep (se 3 (by rfl) ⟨129323, by rfl⟩ : syracuseStep 689725 = 258647) B258647
theorem B362057 : Blo 239816 362057 := bstep (se 2 (by rfl) ⟨135771, by rfl⟩ : syracuseStep 362057 = 271543) B271543
theorem B788087 : Blo 239816 788087 := bstep (se 1 (by rfl) ⟨591065, by rfl⟩ : syracuseStep 788087 = 1182131) B1182131
theorem B362171 : Blo 239816 362171 := bstep (se 1 (by rfl) ⟨271628, by rfl⟩ : syracuseStep 362171 = 543257) B543257
theorem B1214189 : Blo 239816 1214189 := bstep (se 3 (by rfl) ⟨227660, by rfl⟩ : syracuseStep 1214189 = 455321) B455321
theorem B362231 : Blo 239816 362231 := bstep (se 1 (by rfl) ⟨271673, by rfl⟩ : syracuseStep 362231 = 543347) B543347
theorem B362255 : Blo 239816 362255 := bstep (se 1 (by rfl) ⟨271691, by rfl⟩ : syracuseStep 362255 = 543383) B543383
theorem B689953 : Blo 239816 689953 := bstep (se 2 (by rfl) ⟨258732, by rfl⟩ : syracuseStep 689953 = 517465) B517465
theorem B362297 : Blo 239816 362297 := bstep (se 2 (by rfl) ⟨135861, by rfl⟩ : syracuseStep 362297 = 271723) B271723
theorem B362375 : Blo 239816 362375 := bstep (se 1 (by rfl) ⟨271781, by rfl⟩ : syracuseStep 362375 = 543563) B543563
theorem B1542041 : Blo 239816 1542041 := bstep (se 2 (by rfl) ⟨578265, by rfl⟩ : syracuseStep 1542041 = 1156531) B1156531
theorem B362411 : Blo 239816 362411 := bstep (se 1 (by rfl) ⟨271808, by rfl⟩ : syracuseStep 362411 = 543617) B543617
theorem B821177 : Blo 239816 821177 := bstep (se 2 (by rfl) ⟨307941, by rfl⟩ : syracuseStep 821177 = 615883) B615883
theorem B362441 : Blo 239816 362441 := bstep (se 2 (by rfl) ⟨135915, by rfl⟩ : syracuseStep 362441 = 271831) B271831
theorem B10651661 : Blo 239816 10651661 := bstep (se 3 (by rfl) ⟨1997186, by rfl⟩ : syracuseStep 10651661 = 3994373) B3994373
theorem B1837079 : Blo 239816 1837079 := bstep (se 1 (by rfl) ⟨1377809, by rfl⟩ : syracuseStep 1837079 = 2755619) B2755619
theorem B362555 : Blo 239816 362555 := bstep (se 1 (by rfl) ⟨271916, by rfl⟩ : syracuseStep 362555 = 543833) B543833
theorem B919619 : Blo 239816 919619 := bstep (se 1 (by rfl) ⟨689714, by rfl⟩ : syracuseStep 919619 = 1379429) B1379429
theorem B362615 : Blo 239816 362615 := bstep (se 1 (by rfl) ⟨271961, by rfl⟩ : syracuseStep 362615 = 543923) B543923
theorem B755831 : Blo 239816 755831 := bstep (se 1 (by rfl) ⟨566873, by rfl⟩ : syracuseStep 755831 = 1133747) B1133747
theorem B690295 : Blo 239816 690295 := bstep (se 1 (by rfl) ⟨517721, by rfl⟩ : syracuseStep 690295 = 1035443) B1035443
theorem B362639 : Blo 239816 362639 := bstep (se 1 (by rfl) ⟨271979, by rfl⟩ : syracuseStep 362639 = 543959) B543959
theorem B1673389 : Blo 239816 1673389 := bstep (se 3 (by rfl) ⟨313760, by rfl⟩ : syracuseStep 1673389 = 627521) B627521
theorem B362681 : Blo 239816 362681 := bstep (se 2 (by rfl) ⟨136005, by rfl⟩ : syracuseStep 362681 = 272011) B272011
theorem B657665 : Blo 239816 657665 := bstep (se 2 (by rfl) ⟨246624, by rfl⟩ : syracuseStep 657665 = 493249) B493249
theorem B362759 : Blo 239816 362759 := bstep (se 1 (by rfl) ⟨272069, by rfl⟩ : syracuseStep 362759 = 544139) B544139
theorem B362795 : Blo 239816 362795 := bstep (se 1 (by rfl) ⟨272096, by rfl⟩ : syracuseStep 362795 = 544193) B544193
theorem B362825 : Blo 239816 362825 := bstep (se 2 (by rfl) ⟨136059, by rfl⟩ : syracuseStep 362825 = 272119) B272119
theorem B362939 : Blo 239816 362939 := bstep (se 1 (by rfl) ⟨272204, by rfl⟩ : syracuseStep 362939 = 544409) B544409
theorem B362999 : Blo 239816 362999 := bstep (se 1 (by rfl) ⟨272249, by rfl⟩ : syracuseStep 362999 = 544499) B544499
theorem B821771 : Blo 239816 821771 := bstep (se 1 (by rfl) ⟨616328, by rfl⟩ : syracuseStep 821771 = 1232657) B1232657
theorem B363023 : Blo 239816 363023 := bstep (se 1 (by rfl) ⟨272267, by rfl⟩ : syracuseStep 363023 = 544535) B544535
theorem B1214999 : Blo 239816 1214999 := bstep (se 1 (by rfl) ⟨911249, by rfl⟩ : syracuseStep 1214999 = 1822499) B1822499
theorem B363065 : Blo 239816 363065 := bstep (se 2 (by rfl) ⟨136149, by rfl⟩ : syracuseStep 363065 = 272299) B272299
theorem B1378903 : Blo 239816 1378903 := bstep (se 1 (by rfl) ⟨1034177, by rfl⟩ : syracuseStep 1378903 = 2068355) B2068355
theorem B821879 : Blo 239816 821879 := bstep (se 1 (by rfl) ⟨616409, by rfl⟩ : syracuseStep 821879 = 1232819) B1232819
theorem B363143 : Blo 239816 363143 := bstep (se 1 (by rfl) ⟨272357, by rfl⟩ : syracuseStep 363143 = 544715) B544715
theorem B363179 : Blo 239816 363179 := bstep (se 1 (by rfl) ⟨272384, by rfl⟩ : syracuseStep 363179 = 544769) B544769
theorem B363209 : Blo 239816 363209 := bstep (se 2 (by rfl) ⟨136203, by rfl⟩ : syracuseStep 363209 = 272407) B272407
theorem B625441 : Blo 239816 625441 := bstep (se 2 (by rfl) ⟨234540, by rfl⟩ : syracuseStep 625441 = 469081) B469081
theorem B363323 : Blo 239816 363323 := bstep (se 1 (by rfl) ⟨272492, by rfl⟩ : syracuseStep 363323 = 544985) B544985
theorem B363383 : Blo 239816 363383 := bstep (se 1 (by rfl) ⟨272537, by rfl⟩ : syracuseStep 363383 = 545075) B545075
theorem B363407 : Blo 239816 363407 := bstep (se 1 (by rfl) ⟨272555, by rfl⟩ : syracuseStep 363407 = 545111) B545111
theorem B363449 : Blo 239816 363449 := bstep (se 2 (by rfl) ⟨136293, by rfl⟩ : syracuseStep 363449 = 272587) B272587
theorem B363527 : Blo 239816 363527 := bstep (se 1 (by rfl) ⟨272645, by rfl⟩ : syracuseStep 363527 = 545291) B545291
theorem B920605 : Blo 239816 920605 := bstep (se 3 (by rfl) ⟨172613, by rfl⟩ : syracuseStep 920605 = 345227) B345227
theorem B691229 : Blo 239816 691229 := bstep (se 3 (by rfl) ⟨129605, by rfl⟩ : syracuseStep 691229 = 259211) B259211
theorem B363563 : Blo 239816 363563 := bstep (se 1 (by rfl) ⟨272672, by rfl⟩ : syracuseStep 363563 = 545345) B545345
theorem B363593 : Blo 239816 363593 := bstep (se 2 (by rfl) ⟨136347, by rfl⟩ : syracuseStep 363593 = 272695) B272695
theorem B363707 : Blo 239816 363707 := bstep (se 1 (by rfl) ⟨272780, by rfl⟩ : syracuseStep 363707 = 545561) B545561
theorem B822473 : Blo 239816 822473 := bstep (se 2 (by rfl) ⟨308427, by rfl⟩ : syracuseStep 822473 = 616855) B616855
theorem B363767 : Blo 239816 363767 := bstep (se 1 (by rfl) ⟨272825, by rfl⟩ : syracuseStep 363767 = 545651) B545651
theorem B363791 : Blo 239816 363791 := bstep (se 1 (by rfl) ⟨272843, by rfl⟩ : syracuseStep 363791 = 545687) B545687
theorem B462095 : Blo 239816 462095 := bstep (se 1 (by rfl) ⟨346571, by rfl⟩ : syracuseStep 462095 = 693143) B693143
theorem B363833 : Blo 239816 363833 := bstep (se 2 (by rfl) ⟨136437, by rfl⟩ : syracuseStep 363833 = 272875) B272875
theorem B691571 : Blo 239816 691571 := bstep (se 1 (by rfl) ⟨518678, by rfl⟩ : syracuseStep 691571 = 1037357) B1037357
theorem B363911 : Blo 239816 363911 := bstep (se 1 (by rfl) ⟨272933, by rfl⟩ : syracuseStep 363911 = 545867) B545867
theorem B363947 : Blo 239816 363947 := bstep (se 1 (by rfl) ⟨272960, by rfl⟩ : syracuseStep 363947 = 545921) B545921
theorem B363977 : Blo 239816 363977 := bstep (se 2 (by rfl) ⟨136491, by rfl⟩ : syracuseStep 363977 = 272983) B272983
theorem B364091 : Blo 239816 364091 := bstep (se 1 (by rfl) ⟨273068, by rfl⟩ : syracuseStep 364091 = 546137) B546137
theorem B364151 : Blo 239816 364151 := bstep (se 1 (by rfl) ⟨273113, by rfl⟩ : syracuseStep 364151 = 546227) B546227
theorem B364175 : Blo 239816 364175 := bstep (se 1 (by rfl) ⟨273131, by rfl⟩ : syracuseStep 364175 = 546263) B546263
theorem B364217 : Blo 239816 364217 := bstep (se 2 (by rfl) ⟨136581, by rfl⟩ : syracuseStep 364217 = 273163) B273163
theorem B364295 : Blo 239816 364295 := bstep (se 1 (by rfl) ⟨273221, by rfl⟩ : syracuseStep 364295 = 546443) B546443
theorem B1314593 : Blo 239816 1314593 := bstep (se 2 (by rfl) ⟨492972, by rfl⟩ : syracuseStep 1314593 = 985945) B985945
theorem B364331 : Blo 239816 364331 := bstep (se 1 (by rfl) ⟨273248, by rfl⟩ : syracuseStep 364331 = 546497) B546497
theorem B692027 : Blo 239816 692027 := bstep (se 1 (by rfl) ⟨519020, by rfl⟩ : syracuseStep 692027 = 1038041) B1038041
theorem B364361 : Blo 239816 364361 := bstep (se 2 (by rfl) ⟨136635, by rfl⟩ : syracuseStep 364361 = 273271) B273271
theorem B364475 : Blo 239816 364475 := bstep (se 1 (by rfl) ⟨273356, by rfl⟩ : syracuseStep 364475 = 546713) B546713
theorem B364535 : Blo 239816 364535 := bstep (se 1 (by rfl) ⟨273401, by rfl⟩ : syracuseStep 364535 = 546803) B546803
theorem B364559 : Blo 239816 364559 := bstep (se 1 (by rfl) ⟨273419, by rfl⟩ : syracuseStep 364559 = 546839) B546839
theorem B364601 : Blo 239816 364601 := bstep (se 2 (by rfl) ⟨136725, by rfl⟩ : syracuseStep 364601 = 273451) B273451
theorem B364679 : Blo 239816 364679 := bstep (se 1 (by rfl) ⟨273509, by rfl⟩ : syracuseStep 364679 = 547019) B547019
theorem B364715 : Blo 239816 364715 := bstep (se 1 (by rfl) ⟨273536, by rfl⟩ : syracuseStep 364715 = 547073) B547073
theorem B364745 : Blo 239816 364745 := bstep (se 2 (by rfl) ⟨136779, by rfl⟩ : syracuseStep 364745 = 273559) B273559
theorem B364859 : Blo 239816 364859 := bstep (se 1 (by rfl) ⟨273644, by rfl⟩ : syracuseStep 364859 = 547289) B547289
theorem B364919 : Blo 239816 364919 := bstep (se 1 (by rfl) ⟨273689, by rfl⟩ : syracuseStep 364919 = 547379) B547379
theorem B364943 : Blo 239816 364943 := bstep (se 1 (by rfl) ⟨273707, by rfl⟩ : syracuseStep 364943 = 547415) B547415
theorem B364985 : Blo 239816 364985 := bstep (se 2 (by rfl) ⟨136869, by rfl⟩ : syracuseStep 364985 = 273739) B273739
theorem B365063 : Blo 239816 365063 := bstep (se 1 (by rfl) ⟨273797, by rfl⟩ : syracuseStep 365063 = 547595) B547595
theorem B1380887 : Blo 239816 1380887 := bstep (se 1 (by rfl) ⟨1035665, by rfl⟩ : syracuseStep 1380887 = 2071331) B2071331
theorem B365099 : Blo 239816 365099 := bstep (se 1 (by rfl) ⟨273824, by rfl⟩ : syracuseStep 365099 = 547649) B547649
theorem B365129 : Blo 239816 365129 := bstep (se 2 (by rfl) ⟨136923, by rfl⟩ : syracuseStep 365129 = 273847) B273847
theorem B365243 : Blo 239816 365243 := bstep (se 1 (by rfl) ⟨273932, by rfl⟩ : syracuseStep 365243 = 547865) B547865
theorem B4690649 : Blo 239816 4690649 := bstep (se 2 (by rfl) ⟨1758993, by rfl⟩ : syracuseStep 4690649 = 3517987) B3517987
theorem B365303 : Blo 239816 365303 := bstep (se 1 (by rfl) ⟨273977, by rfl⟩ : syracuseStep 365303 = 547955) B547955
theorem B365327 : Blo 239816 365327 := bstep (se 1 (by rfl) ⟨273995, by rfl⟩ : syracuseStep 365327 = 547991) B547991
theorem B365369 : Blo 239816 365369 := bstep (se 2 (by rfl) ⟨137013, by rfl⟩ : syracuseStep 365369 = 274027) B274027
theorem B365447 : Blo 239816 365447 := bstep (se 1 (by rfl) ⟨274085, by rfl⟩ : syracuseStep 365447 = 548171) B548171
theorem B365483 : Blo 239816 365483 := bstep (se 1 (by rfl) ⟨274112, by rfl⟩ : syracuseStep 365483 = 548225) B548225
theorem B365513 : Blo 239816 365513 := bstep (se 2 (by rfl) ⟨137067, by rfl⟩ : syracuseStep 365513 = 274135) B274135
theorem B365627 : Blo 239816 365627 := bstep (se 1 (by rfl) ⟨274220, by rfl⟩ : syracuseStep 365627 = 548441) B548441
theorem B365687 : Blo 239816 365687 := bstep (se 1 (by rfl) ⟨274265, by rfl⟩ : syracuseStep 365687 = 548531) B548531
theorem B365711 : Blo 239816 365711 := bstep (se 1 (by rfl) ⟨274283, by rfl⟩ : syracuseStep 365711 = 548567) B548567
theorem B2331821 : Blo 239816 2331821 := bstep (se 3 (by rfl) ⟨437216, by rfl⟩ : syracuseStep 2331821 = 874433) B874433
theorem B365753 : Blo 239816 365753 := bstep (se 2 (by rfl) ⟨137157, by rfl⟩ : syracuseStep 365753 = 274315) B274315
theorem B1316147 : Blo 239816 1316147 := bstep (se 1 (by rfl) ⟨987110, by rfl⟩ : syracuseStep 1316147 = 1974221) B1974221
theorem B1218077 : Blo 239816 1218077 := bstep (se 3 (by rfl) ⟨228389, by rfl⟩ : syracuseStep 1218077 = 456779) B456779
theorem B2954819 : Blo 239816 2954819 := bstep (se 1 (by rfl) ⟨2216114, by rfl⟩ : syracuseStep 2954819 = 4432229) B4432229
theorem B923507 : Blo 239816 923507 := bstep (se 1 (by rfl) ⟨692630, by rfl⟩ : syracuseStep 923507 = 1385261) B1385261
theorem B2987929 : Blo 239816 2987929 := bstep (se 2 (by rfl) ⟨1120473, by rfl⟩ : syracuseStep 2987929 = 2240947) B2240947
theorem B1742755 : Blo 239816 1742755 := bstep (se 1 (by rfl) ⟨1307066, by rfl⟩ : syracuseStep 1742755 = 2614133) B2614133
theorem B1218563 : Blo 239816 1218563 := bstep (se 1 (by rfl) ⟨913922, by rfl⟩ : syracuseStep 1218563 = 1827845) B1827845
theorem B465185 : Blo 239816 465185 := bstep (se 2 (by rfl) ⟨174444, by rfl⟩ : syracuseStep 465185 = 348889) B348889
theorem B11770433 : Blo 239816 11770433 := bstep (se 2 (by rfl) ⟨4413912, by rfl⟩ : syracuseStep 11770433 = 8827825) B8827825
theorem B367735 : Blo 239816 367735 := bstep (se 1 (by rfl) ⟨275801, by rfl⟩ : syracuseStep 367735 = 551603) B551603
theorem B695431 : Blo 239816 695431 := bstep (se 1 (by rfl) ⟨521573, by rfl⟩ : syracuseStep 695431 = 1043147) B1043147
theorem B1220183 : Blo 239816 1220183 := bstep (se 1 (by rfl) ⟨915137, by rfl⟩ : syracuseStep 1220183 = 1830275) B1830275
theorem B269959 : Blo 239816 269959 := bstep (se 1 (by rfl) ⟨202469, by rfl⟩ : syracuseStep 269959 = 404939) B404939
theorem B270139 : Blo 239816 270139 := bstep (se 1 (by rfl) ⟨202604, by rfl⟩ : syracuseStep 270139 = 405209) B405209
theorem B925739 : Blo 239816 925739 := bstep (se 1 (by rfl) ⟨694304, by rfl⟩ : syracuseStep 925739 = 1388609) B1388609
theorem B1220669 : Blo 239816 1220669 := bstep (se 3 (by rfl) ⟨228875, by rfl⟩ : syracuseStep 1220669 = 457751) B457751
theorem B893015 : Blo 239816 893015 := bstep (se 1 (by rfl) ⟨669761, by rfl⟩ : syracuseStep 893015 = 1339523) B1339523
theorem B270607 : Blo 239816 270607 := bstep (se 1 (by rfl) ⟨202955, by rfl⟩ : syracuseStep 270607 = 405911) B405911
theorem B467215 : Blo 239816 467215 := bstep (se 1 (by rfl) ⟨350411, by rfl⟩ : syracuseStep 467215 = 700823) B700823
theorem B696691 : Blo 239816 696691 := bstep (se 1 (by rfl) ⟨522518, by rfl⟩ : syracuseStep 696691 = 1045037) B1045037
theorem B467603 : Blo 239816 467603 := bstep (se 1 (by rfl) ⟨350702, by rfl⟩ : syracuseStep 467603 = 701405) B701405
theorem B271111 : Blo 239816 271111 := bstep (se 1 (by rfl) ⟨203333, by rfl⟩ : syracuseStep 271111 = 406667) B406667
theorem B1024883 : Blo 239816 1024883 := bstep (se 1 (by rfl) ⟨768662, by rfl⟩ : syracuseStep 1024883 = 1537325) B1537325
theorem B271291 : Blo 239816 271291 := bstep (se 1 (by rfl) ⟨203468, by rfl⟩ : syracuseStep 271291 = 406937) B406937
theorem B369851 : Blo 239816 369851 := bstep (se 1 (by rfl) ⟨277388, by rfl⟩ : syracuseStep 369851 = 554777) B554777
theorem B664865 : Blo 239816 664865 := bstep (se 2 (by rfl) ⟨249324, by rfl⟩ : syracuseStep 664865 = 498649) B498649
theorem B271759 : Blo 239816 271759 := bstep (se 1 (by rfl) ⟨203819, by rfl⟩ : syracuseStep 271759 = 407639) B407639
theorem B304555 : Blo 239816 304555 := bstep (se 1 (by rfl) ⟨228416, by rfl⟩ : syracuseStep 304555 = 456833) B456833
theorem B1844855 : Blo 239816 1844855 := bstep (se 1 (by rfl) ⟨1383641, by rfl⟩ : syracuseStep 1844855 = 2767283) B2767283
theorem B2336435 : Blo 239816 2336435 := bstep (se 1 (by rfl) ⟨1752326, by rfl⟩ : syracuseStep 2336435 = 3504653) B3504653
theorem B2074369 : Blo 239816 2074369 := bstep (se 2 (by rfl) ⟨777888, by rfl⟩ : syracuseStep 2074369 = 1555777) B1555777
theorem B1222451 : Blo 239816 1222451 := bstep (se 1 (by rfl) ⟨916838, by rfl⟩ : syracuseStep 1222451 = 1833677) B1833677
theorem B272263 : Blo 239816 272263 := bstep (se 1 (by rfl) ⟨204197, by rfl⟩ : syracuseStep 272263 = 408395) B408395
theorem B272443 : Blo 239816 272443 := bstep (se 1 (by rfl) ⟨204332, by rfl⟩ : syracuseStep 272443 = 408665) B408665
theorem B1222775 : Blo 239816 1222775 := bstep (se 1 (by rfl) ⟨917081, by rfl⟩ : syracuseStep 1222775 = 1834163) B1834163
theorem B436409 : Blo 239816 436409 := bstep (se 2 (by rfl) ⟨163653, by rfl⟩ : syracuseStep 436409 = 327307) B327307
theorem B239879 : Blo 239816 239879 := bstep (se 1 (by rfl) ⟨179909, by rfl⟩ : syracuseStep 239879 = 359819) B359819
theorem B239887 : Blo 239816 239887 := bstep (se 1 (by rfl) ⟨179915, by rfl⟩ : syracuseStep 239887 = 359831) B359831
theorem B239931 : Blo 239816 239931 := bstep (se 1 (by rfl) ⟨179948, by rfl⟩ : syracuseStep 239931 = 359897) B359897
theorem B305527 : Blo 239816 305527 := bstep (se 1 (by rfl) ⟨229145, by rfl⟩ : syracuseStep 305527 = 458291) B458291
theorem B240007 : Blo 239816 240007 := bstep (se 1 (by rfl) ⟨180005, by rfl⟩ : syracuseStep 240007 = 360011) B360011
theorem B240015 : Blo 239816 240015 := bstep (se 1 (by rfl) ⟨180011, by rfl⟩ : syracuseStep 240015 = 360023) B360023
theorem B240059 : Blo 239816 240059 := bstep (se 1 (by rfl) ⟨180044, by rfl⟩ : syracuseStep 240059 = 360089) B360089
theorem B240135 : Blo 239816 240135 := bstep (se 1 (by rfl) ⟨180101, by rfl⟩ : syracuseStep 240135 = 360203) B360203
theorem B240143 : Blo 239816 240143 := bstep (se 1 (by rfl) ⟨180107, by rfl⟩ : syracuseStep 240143 = 360215) B360215
theorem B272911 : Blo 239816 272911 := bstep (se 1 (by rfl) ⟨204683, by rfl⟩ : syracuseStep 272911 = 409367) B409367
theorem B240187 : Blo 239816 240187 := bstep (se 1 (by rfl) ⟨180140, by rfl⟩ : syracuseStep 240187 = 360281) B360281
theorem B1845827 : Blo 239816 1845827 := bstep (se 1 (by rfl) ⟨1384370, by rfl⟩ : syracuseStep 1845827 = 2768741) B2768741
theorem B240263 : Blo 239816 240263 := bstep (se 1 (by rfl) ⟨180197, by rfl⟩ : syracuseStep 240263 = 360395) B360395
theorem B240271 : Blo 239816 240271 := bstep (se 1 (by rfl) ⟨180203, by rfl⟩ : syracuseStep 240271 = 360407) B360407
theorem B1485485 : Blo 239816 1485485 := bstep (se 3 (by rfl) ⟨278528, by rfl⟩ : syracuseStep 1485485 = 557057) B557057
theorem B240315 : Blo 239816 240315 := bstep (se 1 (by rfl) ⟨180236, by rfl⟩ : syracuseStep 240315 = 360473) B360473
theorem B305851 : Blo 239816 305851 := bstep (se 1 (by rfl) ⟨229388, by rfl⟩ : syracuseStep 305851 = 458777) B458777
theorem B240391 : Blo 239816 240391 := bstep (se 1 (by rfl) ⟨180293, by rfl⟩ : syracuseStep 240391 = 360587) B360587
theorem B240399 : Blo 239816 240399 := bstep (se 1 (by rfl) ⟨180299, by rfl⟩ : syracuseStep 240399 = 360599) B360599
theorem B2960165 : Blo 239816 2960165 := bstep (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) B555031
theorem B240443 : Blo 239816 240443 := bstep (se 1 (by rfl) ⟨180332, by rfl⟩ : syracuseStep 240443 = 360665) B360665
theorem B240519 : Blo 239816 240519 := bstep (se 1 (by rfl) ⟨180389, by rfl⟩ : syracuseStep 240519 = 360779) B360779
theorem B240527 : Blo 239816 240527 := bstep (se 1 (by rfl) ⟨180395, by rfl⟩ : syracuseStep 240527 = 360791) B360791
theorem B2632601 : Blo 239816 2632601 := bstep (se 2 (by rfl) ⟨987225, by rfl⟩ : syracuseStep 2632601 = 1974451) B1974451
theorem B240571 : Blo 239816 240571 := bstep (se 1 (by rfl) ⟨180428, by rfl⟩ : syracuseStep 240571 = 360857) B360857
theorem B240647 : Blo 239816 240647 := bstep (se 1 (by rfl) ⟨180485, by rfl⟩ : syracuseStep 240647 = 360971) B360971
theorem B273415 : Blo 239816 273415 := bstep (se 1 (by rfl) ⟨205061, by rfl⟩ : syracuseStep 273415 = 410123) B410123
theorem B240655 : Blo 239816 240655 := bstep (se 1 (by rfl) ⟨180491, by rfl⟩ : syracuseStep 240655 = 360983) B360983
theorem B240699 : Blo 239816 240699 := bstep (se 1 (by rfl) ⟨180524, by rfl⟩ : syracuseStep 240699 = 361049) B361049
theorem B1223747 : Blo 239816 1223747 := bstep (se 1 (by rfl) ⟨917810, by rfl⟩ : syracuseStep 1223747 = 1835621) B1835621
theorem B240775 : Blo 239816 240775 := bstep (se 1 (by rfl) ⟨180581, by rfl⟩ : syracuseStep 240775 = 361163) B361163
theorem B437383 : Blo 239816 437383 := bstep (se 1 (by rfl) ⟨328037, by rfl⟩ : syracuseStep 437383 = 656075) B656075
theorem B240783 : Blo 239816 240783 := bstep (se 1 (by rfl) ⟨180587, by rfl⟩ : syracuseStep 240783 = 361175) B361175
theorem B240827 : Blo 239816 240827 := bstep (se 1 (by rfl) ⟨180620, by rfl⟩ : syracuseStep 240827 = 361241) B361241
theorem B273595 : Blo 239816 273595 := bstep (se 1 (by rfl) ⟨205196, by rfl⟩ : syracuseStep 273595 = 410393) B410393
theorem B240903 : Blo 239816 240903 := bstep (se 1 (by rfl) ⟨180677, by rfl⟩ : syracuseStep 240903 = 361355) B361355
theorem B1027343 : Blo 239816 1027343 := bstep (se 1 (by rfl) ⟨770507, by rfl⟩ : syracuseStep 1027343 = 1541015) B1541015
theorem B240911 : Blo 239816 240911 := bstep (se 1 (by rfl) ⟨180683, by rfl⟩ : syracuseStep 240911 = 361367) B361367
theorem B240955 : Blo 239816 240955 := bstep (se 1 (by rfl) ⟨180716, by rfl⟩ : syracuseStep 240955 = 361433) B361433
theorem B241031 : Blo 239816 241031 := bstep (se 1 (by rfl) ⟨180773, by rfl⟩ : syracuseStep 241031 = 361547) B361547
theorem B1224071 : Blo 239816 1224071 := bstep (se 1 (by rfl) ⟨918053, by rfl⟩ : syracuseStep 1224071 = 1836107) B1836107
theorem B248491405 : Blo 239816 248491405 := bstep (se 3 (by rfl) ⟨46592138, by rfl⟩ : syracuseStep 248491405 = 93184277) B93184277
theorem B241039 : Blo 239816 241039 := bstep (se 1 (by rfl) ⟨180779, by rfl⟩ : syracuseStep 241039 = 361559) B361559
theorem B241083 : Blo 239816 241083 := bstep (se 1 (by rfl) ⟨180812, by rfl⟩ : syracuseStep 241083 = 361625) B361625
theorem B241159 : Blo 239816 241159 := bstep (se 1 (by rfl) ⟨180869, by rfl⟩ : syracuseStep 241159 = 361739) B361739
theorem B241167 : Blo 239816 241167 := bstep (se 1 (by rfl) ⟨180875, by rfl⟩ : syracuseStep 241167 = 361751) B361751
theorem B831019 : Blo 239816 831019 := bstep (se 1 (by rfl) ⟨623264, by rfl⟩ : syracuseStep 831019 = 1246529) B1246529
theorem B241211 : Blo 239816 241211 := bstep (se 1 (by rfl) ⟨180908, by rfl⟩ : syracuseStep 241211 = 361817) B361817
theorem B241287 : Blo 239816 241287 := bstep (se 1 (by rfl) ⟨180965, by rfl⟩ : syracuseStep 241287 = 361931) B361931
theorem B306823 : Blo 239816 306823 := bstep (se 1 (by rfl) ⟨230117, by rfl⟩ : syracuseStep 306823 = 460235) B460235
theorem B241295 : Blo 239816 241295 := bstep (se 1 (by rfl) ⟨180971, by rfl⟩ : syracuseStep 241295 = 361943) B361943
theorem B274063 : Blo 239816 274063 := bstep (se 1 (by rfl) ⟨205547, by rfl⟩ : syracuseStep 274063 = 411095) B411095
theorem B241339 : Blo 239816 241339 := bstep (se 1 (by rfl) ⟨181004, by rfl⟩ : syracuseStep 241339 = 362009) B362009
theorem B2076353 : Blo 239816 2076353 := bstep (se 2 (by rfl) ⟨778632, by rfl⟩ : syracuseStep 2076353 = 1557265) B1557265
theorem B241415 : Blo 239816 241415 := bstep (se 1 (by rfl) ⟨181061, by rfl⟩ : syracuseStep 241415 = 362123) B362123
theorem B405263 : Blo 239816 405263 := bstep (se 1 (by rfl) ⟨303947, by rfl⟩ : syracuseStep 405263 = 607895) B607895
theorem B241423 : Blo 239816 241423 := bstep (se 1 (by rfl) ⟨181067, by rfl⟩ : syracuseStep 241423 = 362135) B362135
theorem B241467 : Blo 239816 241467 := bstep (se 1 (by rfl) ⟨181100, by rfl⟩ : syracuseStep 241467 = 362201) B362201
theorem B241543 : Blo 239816 241543 := bstep (se 1 (by rfl) ⟨181157, by rfl⟩ : syracuseStep 241543 = 362315) B362315
theorem B241551 : Blo 239816 241551 := bstep (se 1 (by rfl) ⟨181163, by rfl⟩ : syracuseStep 241551 = 362327) B362327
theorem B241595 : Blo 239816 241595 := bstep (se 1 (by rfl) ⟨181196, by rfl⟩ : syracuseStep 241595 = 362393) B362393
theorem B241671 : Blo 239816 241671 := bstep (se 1 (by rfl) ⟨181253, by rfl⟩ : syracuseStep 241671 = 362507) B362507
theorem B241679 : Blo 239816 241679 := bstep (se 1 (by rfl) ⟨181259, by rfl⟩ : syracuseStep 241679 = 362519) B362519
theorem B307243 : Blo 239816 307243 := bstep (se 1 (by rfl) ⟨230432, by rfl⟩ : syracuseStep 307243 = 460865) B460865
theorem B241723 : Blo 239816 241723 := bstep (se 1 (by rfl) ⟨181292, by rfl⟩ : syracuseStep 241723 = 362585) B362585
theorem B241799 : Blo 239816 241799 := bstep (se 1 (by rfl) ⟨181349, by rfl⟩ : syracuseStep 241799 = 362699) B362699
theorem B241807 : Blo 239816 241807 := bstep (se 1 (by rfl) ⟨181355, by rfl⟩ : syracuseStep 241807 = 362711) B362711
theorem B241851 : Blo 239816 241851 := bstep (se 1 (by rfl) ⟨181388, by rfl⟩ : syracuseStep 241851 = 362777) B362777
theorem B241927 : Blo 239816 241927 := bstep (se 1 (by rfl) ⟨181445, by rfl⟩ : syracuseStep 241927 = 362891) B362891
theorem B241935 : Blo 239816 241935 := bstep (se 1 (by rfl) ⟨181451, by rfl⟩ : syracuseStep 241935 = 362903) B362903
theorem B307471 : Blo 239816 307471 := bstep (se 1 (by rfl) ⟨230603, by rfl⟩ : syracuseStep 307471 = 461207) B461207
theorem B405803 : Blo 239816 405803 := bstep (se 1 (by rfl) ⟨304352, by rfl⟩ : syracuseStep 405803 = 608705) B608705
theorem B241979 : Blo 239816 241979 := bstep (se 1 (by rfl) ⟨181484, by rfl⟩ : syracuseStep 241979 = 362969) B362969
theorem B242055 : Blo 239816 242055 := bstep (se 1 (by rfl) ⟨181541, by rfl⟩ : syracuseStep 242055 = 363083) B363083
theorem B2634119 : Blo 239816 2634119 := bstep (se 1 (by rfl) ⟨1975589, by rfl⟩ : syracuseStep 2634119 = 3951179) B3951179
theorem B242063 : Blo 239816 242063 := bstep (se 1 (by rfl) ⟨181547, by rfl⟩ : syracuseStep 242063 = 363095) B363095
theorem B1814929 : Blo 239816 1814929 := bstep (se 2 (by rfl) ⟨680598, by rfl⟩ : syracuseStep 1814929 = 1361197) B1361197
theorem B3322259 : Blo 239816 3322259 := bstep (se 1 (by rfl) ⟨2491694, by rfl⟩ : syracuseStep 3322259 = 4983389) B4983389
theorem B242107 : Blo 239816 242107 := bstep (se 1 (by rfl) ⟨181580, by rfl⟩ : syracuseStep 242107 = 363161) B363161
theorem B242183 : Blo 239816 242183 := bstep (se 1 (by rfl) ⟨181637, by rfl⟩ : syracuseStep 242183 = 363275) B363275
theorem B242191 : Blo 239816 242191 := bstep (se 1 (by rfl) ⟨181643, by rfl⟩ : syracuseStep 242191 = 363287) B363287
theorem B242235 : Blo 239816 242235 := bstep (se 1 (by rfl) ⟨181676, by rfl⟩ : syracuseStep 242235 = 363353) B363353
theorem B242311 : Blo 239816 242311 := bstep (se 1 (by rfl) ⟨181733, by rfl⟩ : syracuseStep 242311 = 363467) B363467
theorem B242319 : Blo 239816 242319 := bstep (se 1 (by rfl) ⟨181739, by rfl⟩ : syracuseStep 242319 = 363479) B363479
theorem B406201 : Blo 239816 406201 := bstep (se 2 (by rfl) ⟨152325, by rfl⟩ : syracuseStep 406201 = 304651) B304651
theorem B242363 : Blo 239816 242363 := bstep (se 1 (by rfl) ⟨181772, by rfl⟩ : syracuseStep 242363 = 363545) B363545
theorem B242439 : Blo 239816 242439 := bstep (se 1 (by rfl) ⟨181829, by rfl⟩ : syracuseStep 242439 = 363659) B363659
theorem B242447 : Blo 239816 242447 := bstep (se 1 (by rfl) ⟨181835, by rfl⟩ : syracuseStep 242447 = 363671) B363671
theorem B242491 : Blo 239816 242491 := bstep (se 1 (by rfl) ⟨181868, by rfl⟩ : syracuseStep 242491 = 363737) B363737
theorem B242567 : Blo 239816 242567 := bstep (se 1 (by rfl) ⟨181925, by rfl⟩ : syracuseStep 242567 = 363851) B363851
theorem B242575 : Blo 239816 242575 := bstep (se 1 (by rfl) ⟨181931, by rfl⟩ : syracuseStep 242575 = 363863) B363863
theorem B734105 : Blo 239816 734105 := bstep (se 2 (by rfl) ⟨275289, by rfl⟩ : syracuseStep 734105 = 550579) B550579
theorem B242619 : Blo 239816 242619 := bstep (se 1 (by rfl) ⟨181964, by rfl⟩ : syracuseStep 242619 = 363929) B363929
theorem B308215 : Blo 239816 308215 := bstep (se 1 (by rfl) ⟨231161, by rfl⟩ : syracuseStep 308215 = 462323) B462323
theorem B242695 : Blo 239816 242695 := bstep (se 1 (by rfl) ⟨182021, by rfl⟩ : syracuseStep 242695 = 364043) B364043
theorem B242703 : Blo 239816 242703 := bstep (se 1 (by rfl) ⟨182027, by rfl⟩ : syracuseStep 242703 = 364055) B364055
theorem B242747 : Blo 239816 242747 := bstep (se 1 (by rfl) ⟨182060, by rfl⟩ : syracuseStep 242747 = 364121) B364121
theorem B242823 : Blo 239816 242823 := bstep (se 1 (by rfl) ⟨182117, by rfl⟩ : syracuseStep 242823 = 364235) B364235
theorem B242831 : Blo 239816 242831 := bstep (se 1 (by rfl) ⟨182123, by rfl⟩ : syracuseStep 242831 = 364247) B364247
theorem B242875 : Blo 239816 242875 := bstep (se 1 (by rfl) ⟨182156, by rfl⟩ : syracuseStep 242875 = 364313) B364313
theorem B242951 : Blo 239816 242951 := bstep (se 1 (by rfl) ⟨182213, by rfl⟩ : syracuseStep 242951 = 364427) B364427
theorem B242959 : Blo 239816 242959 := bstep (se 1 (by rfl) ⟨182219, by rfl⟩ : syracuseStep 242959 = 364439) B364439
theorem B243003 : Blo 239816 243003 := bstep (se 1 (by rfl) ⟨182252, by rfl⟩ : syracuseStep 243003 = 364505) B364505
theorem B308539 : Blo 239816 308539 := bstep (se 1 (by rfl) ⟨231404, by rfl⟩ : syracuseStep 308539 = 462809) B462809
theorem B406903 : Blo 239816 406903 := bstep (se 1 (by rfl) ⟨305177, by rfl⟩ : syracuseStep 406903 = 610355) B610355
theorem B3519875 : Blo 239816 3519875 := bstep (se 1 (by rfl) ⟨2639906, by rfl⟩ : syracuseStep 3519875 = 5279813) B5279813
theorem B243079 : Blo 239816 243079 := bstep (se 1 (by rfl) ⟨182309, by rfl⟩ : syracuseStep 243079 = 364619) B364619
theorem B3159431 : Blo 239816 3159431 := bstep (se 1 (by rfl) ⟨2369573, by rfl⟩ : syracuseStep 3159431 = 4739147) B4739147
theorem B243087 : Blo 239816 243087 := bstep (se 1 (by rfl) ⟨182315, by rfl⟩ : syracuseStep 243087 = 364631) B364631
theorem B243131 : Blo 239816 243131 := bstep (se 1 (by rfl) ⟨182348, by rfl⟩ : syracuseStep 243131 = 364697) B364697
theorem B1750481 : Blo 239816 1750481 := bstep (se 2 (by rfl) ⟨656430, by rfl⟩ : syracuseStep 1750481 = 1312861) B1312861
theorem B243207 : Blo 239816 243207 := bstep (se 1 (by rfl) ⟨182405, by rfl⟩ : syracuseStep 243207 = 364811) B364811
theorem B243215 : Blo 239816 243215 := bstep (se 1 (by rfl) ⟨182411, by rfl⟩ : syracuseStep 243215 = 364823) B364823
theorem B407099 : Blo 239816 407099 := bstep (se 1 (by rfl) ⟨305324, by rfl⟩ : syracuseStep 407099 = 610649) B610649
theorem B243259 : Blo 239816 243259 := bstep (se 1 (by rfl) ⟨182444, by rfl⟩ : syracuseStep 243259 = 364889) B364889
theorem B243335 : Blo 239816 243335 := bstep (se 1 (by rfl) ⟨182501, by rfl⟩ : syracuseStep 243335 = 365003) B365003
theorem B243343 : Blo 239816 243343 := bstep (se 1 (by rfl) ⟨182507, by rfl⟩ : syracuseStep 243343 = 365015) B365015
theorem B243387 : Blo 239816 243387 := bstep (se 1 (by rfl) ⟨182540, by rfl⟩ : syracuseStep 243387 = 365081) B365081
theorem B2111233 : Blo 239816 2111233 := bstep (se 2 (by rfl) ⟨791712, by rfl⟩ : syracuseStep 2111233 = 1583425) B1583425
theorem B243463 : Blo 239816 243463 := bstep (se 1 (by rfl) ⟨182597, by rfl⟩ : syracuseStep 243463 = 365195) B365195
theorem B243471 : Blo 239816 243471 := bstep (se 1 (by rfl) ⟨182603, by rfl⟩ : syracuseStep 243471 = 365207) B365207
theorem B243515 : Blo 239816 243515 := bstep (se 1 (by rfl) ⟨182636, by rfl⟩ : syracuseStep 243515 = 365273) B365273
theorem B341833 : Blo 239816 341833 := bstep (se 2 (by rfl) ⟨128187, by rfl⟩ : syracuseStep 341833 = 256375) B256375
theorem B243591 : Blo 239816 243591 := bstep (se 1 (by rfl) ⟨182693, by rfl⟩ : syracuseStep 243591 = 365387) B365387
theorem B243599 : Blo 239816 243599 := bstep (se 1 (by rfl) ⟨182699, by rfl⟩ : syracuseStep 243599 = 365399) B365399
theorem B243643 : Blo 239816 243643 := bstep (se 1 (by rfl) ⟨182732, by rfl⟩ : syracuseStep 243643 = 365465) B365465
theorem B407497 : Blo 239816 407497 := bstep (se 2 (by rfl) ⟨152811, by rfl⟩ : syracuseStep 407497 = 305623) B305623
theorem B473033 : Blo 239816 473033 := bstep (se 2 (by rfl) ⟨177387, by rfl⟩ : syracuseStep 473033 = 354775) B354775
theorem B243719 : Blo 239816 243719 := bstep (se 1 (by rfl) ⟨182789, by rfl⟩ : syracuseStep 243719 = 365579) B365579
theorem B243727 : Blo 239816 243727 := bstep (se 1 (by rfl) ⟨182795, by rfl⟩ : syracuseStep 243727 = 365591) B365591
theorem B12564497 : Blo 239816 12564497 := bstep (se 2 (by rfl) ⟨4711686, by rfl⟩ : syracuseStep 12564497 = 9423373) B9423373
theorem B2078743 : Blo 239816 2078743 := bstep (se 1 (by rfl) ⟨1559057, by rfl⟩ : syracuseStep 2078743 = 3118115) B3118115
theorem B243771 : Blo 239816 243771 := bstep (se 1 (by rfl) ⟨182828, by rfl⟩ : syracuseStep 243771 = 365657) B365657
theorem B408199 : Blo 239816 408199 := bstep (se 1 (by rfl) ⟨306149, by rfl⟩ : syracuseStep 408199 = 612299) B612299
theorem B1850201 : Blo 239816 1850201 := bstep (se 2 (by rfl) ⟨693825, by rfl⟩ : syracuseStep 1850201 = 1387651) B1387651
theorem B1522547 : Blo 239816 1522547 := bstep (se 1 (by rfl) ⟨1141910, by rfl⟩ : syracuseStep 1522547 = 2283821) B2283821
theorem B1227635 : Blo 239816 1227635 := bstep (se 1 (by rfl) ⟨920726, by rfl⟩ : syracuseStep 1227635 = 1841453) B1841453
theorem B4996183 : Blo 239816 4996183 := bstep (se 1 (by rfl) ⟨3747137, by rfl⟩ : syracuseStep 4996183 = 7494275) B7494275
theorem B539783 : Blo 239816 539783 := bstep (se 1 (by rfl) ⟨404837, by rfl⟩ : syracuseStep 539783 = 809675) B809675
theorem B408847 : Blo 239816 408847 := bstep (se 1 (by rfl) ⟨306635, by rfl⟩ : syracuseStep 408847 = 613271) B613271
theorem B867617 : Blo 239816 867617 := bstep (se 2 (by rfl) ⟨325356, by rfl⟩ : syracuseStep 867617 = 650713) B650713
theorem B539963 : Blo 239816 539963 := bstep (se 1 (by rfl) ⟨404972, by rfl⟩ : syracuseStep 539963 = 809945) B809945
theorem B1228121 : Blo 239816 1228121 := bstep (se 2 (by rfl) ⟨460545, by rfl⟩ : syracuseStep 1228121 = 921091) B921091
theorem B1752455 : Blo 239816 1752455 := bstep (se 1 (by rfl) ⟨1314341, by rfl⟩ : syracuseStep 1752455 = 2628683) B2628683
theorem B540089 : Blo 239816 540089 := bstep (se 2 (by rfl) ⟨202533, by rfl⟩ : syracuseStep 540089 = 405067) B405067
theorem B278159 : Blo 239816 278159 := bstep (se 1 (by rfl) ⟨208619, by rfl⟩ : syracuseStep 278159 = 417239) B417239
theorem B540431 : Blo 239816 540431 := bstep (se 1 (by rfl) ⟨405323, by rfl⟩ : syracuseStep 540431 = 810647) B810647
theorem B540449 : Blo 239816 540449 := bstep (se 2 (by rfl) ⟨202668, by rfl⟩ : syracuseStep 540449 = 405337) B405337
theorem B1851173 : Blo 239816 1851173 := bstep (se 4 (by rfl) ⟨173547, by rfl⟩ : syracuseStep 1851173 = 347095) B347095
theorem B409387 : Blo 239816 409387 := bstep (se 1 (by rfl) ⟨307040, by rfl⟩ : syracuseStep 409387 = 614081) B614081
theorem B769945 : Blo 239816 769945 := bstep (se 2 (by rfl) ⟨288729, by rfl⟩ : syracuseStep 769945 = 577459) B577459
theorem B409529 : Blo 239816 409529 := bstep (se 2 (by rfl) ⟨153573, by rfl⟩ : syracuseStep 409529 = 307147) B307147
theorem B540791 : Blo 239816 540791 := bstep (se 1 (by rfl) ⟨405593, by rfl⟩ : syracuseStep 540791 = 811187) B811187
theorem B540971 : Blo 239816 540971 := bstep (se 1 (by rfl) ⟨405728, by rfl⟩ : syracuseStep 540971 = 811457) B811457
theorem B344521 : Blo 239816 344521 := bstep (se 2 (by rfl) ⟨129195, by rfl⟩ : syracuseStep 344521 = 258391) B258391
theorem B5653111 : Blo 239816 5653111 := bstep (se 1 (by rfl) ⟨4239833, by rfl⟩ : syracuseStep 5653111 = 8479667) B8479667
theorem B410231 : Blo 239816 410231 := bstep (se 1 (by rfl) ⟨307673, by rfl⟩ : syracuseStep 410231 = 615347) B615347
theorem B541331 : Blo 239816 541331 := bstep (se 1 (by rfl) ⟨405998, by rfl⟩ : syracuseStep 541331 = 811997) B811997
theorem B541385 : Blo 239816 541385 := bstep (se 2 (by rfl) ⟨203019, by rfl⟩ : syracuseStep 541385 = 406039) B406039
theorem B2212609 : Blo 239816 2212609 := bstep (se 2 (by rfl) ⟨829728, by rfl⟩ : syracuseStep 2212609 = 1659457) B1659457
theorem B3457829 : Blo 239816 3457829 := bstep (se 4 (by rfl) ⟨324171, by rfl⟩ : syracuseStep 3457829 = 648343) B648343
theorem B1393523 : Blo 239816 1393523 := bstep (se 1 (by rfl) ⟨1045142, by rfl⟩ : syracuseStep 1393523 = 2090285) B2090285
theorem B2933657 : Blo 239816 2933657 := bstep (se 2 (by rfl) ⟨1100121, by rfl⟩ : syracuseStep 2933657 = 2200243) B2200243
theorem B607247 : Blo 239816 607247 := bstep (se 1 (by rfl) ⟨455435, by rfl⟩ : syracuseStep 607247 = 910871) B910871
theorem B410683 : Blo 239816 410683 := bstep (se 1 (by rfl) ⟨308012, by rfl⟩ : syracuseStep 410683 = 616025) B616025
theorem B410825 : Blo 239816 410825 := bstep (se 2 (by rfl) ⟨154059, by rfl⟩ : syracuseStep 410825 = 308119) B308119
theorem B247055 : Blo 239816 247055 := bstep (se 1 (by rfl) ⟨185291, by rfl⟩ : syracuseStep 247055 = 370583) B370583
theorem B5850467 : Blo 239816 5850467 := bstep (se 1 (by rfl) ⟨4387850, by rfl⟩ : syracuseStep 5850467 = 8775701) B8775701
theorem B542087 : Blo 239816 542087 := bstep (se 1 (by rfl) ⟨406565, by rfl⟩ : syracuseStep 542087 = 813131) B813131
theorem B1230227 : Blo 239816 1230227 := bstep (se 1 (by rfl) ⟨922670, by rfl⟩ : syracuseStep 1230227 = 1845341) B1845341
theorem B542267 : Blo 239816 542267 := bstep (se 1 (by rfl) ⟨406700, by rfl⟩ : syracuseStep 542267 = 813401) B813401
theorem B6670001 : Blo 239816 6670001 := bstep (se 2 (by rfl) ⟨2501250, by rfl⟩ : syracuseStep 6670001 = 5002501) B5002501
theorem B542393 : Blo 239816 542393 := bstep (se 2 (by rfl) ⟨203397, by rfl⟩ : syracuseStep 542393 = 406795) B406795
theorem B607945 : Blo 239816 607945 := bstep (se 2 (by rfl) ⟨227979, by rfl⟩ : syracuseStep 607945 = 455959) B455959
theorem B608087 : Blo 239816 608087 := bstep (se 1 (by rfl) ⟨456065, by rfl⟩ : syracuseStep 608087 = 912131) B912131
theorem B2738123 : Blo 239816 2738123 := bstep (se 1 (by rfl) ⟨2053592, by rfl⟩ : syracuseStep 2738123 = 4107185) B4107185
theorem B542735 : Blo 239816 542735 := bstep (se 1 (by rfl) ⟨407051, by rfl⟩ : syracuseStep 542735 = 814103) B814103
theorem B542753 : Blo 239816 542753 := bstep (se 2 (by rfl) ⟨203532, by rfl⟩ : syracuseStep 542753 = 407065) B407065
theorem B2050109 : Blo 239816 2050109 := bstep (se 3 (by rfl) ⟨384395, by rfl⟩ : syracuseStep 2050109 = 768791) B768791
theorem B575623 : Blo 239816 575623 := bstep (se 1 (by rfl) ⟨431717, by rfl⟩ : syracuseStep 575623 = 863435) B863435
theorem B1296755 : Blo 239816 1296755 := bstep (se 1 (by rfl) ⟨972566, by rfl⟩ : syracuseStep 1296755 = 1945133) B1945133
theorem B543095 : Blo 239816 543095 := bstep (se 1 (by rfl) ⟨407321, by rfl⟩ : syracuseStep 543095 = 814643) B814643
theorem B4999715 : Blo 239816 4999715 := bstep (se 1 (by rfl) ⟨3749786, by rfl⟩ : syracuseStep 4999715 = 7499573) B7499573
theorem B543275 : Blo 239816 543275 := bstep (se 1 (by rfl) ⟨407456, by rfl⟩ : syracuseStep 543275 = 814913) B814913
theorem B576343 : Blo 239816 576343 := bstep (se 1 (by rfl) ⟨432257, by rfl⟩ : syracuseStep 576343 = 864515) B864515
theorem B346999 : Blo 239816 346999 := bstep (se 1 (by rfl) ⟨260249, by rfl⟩ : syracuseStep 346999 = 520499) B520499
theorem B543635 : Blo 239816 543635 := bstep (se 1 (by rfl) ⟨407726, by rfl⟩ : syracuseStep 543635 = 815453) B815453
theorem B543689 : Blo 239816 543689 := bstep (se 2 (by rfl) ⟨203883, by rfl⟩ : syracuseStep 543689 = 407767) B407767
theorem B773675 : Blo 239816 773675 := bstep (se 1 (by rfl) ⟨580256, by rfl⟩ : syracuseStep 773675 = 1160513) B1160513
theorem B544391 : Blo 239816 544391 := bstep (se 1 (by rfl) ⟨408293, by rfl⟩ : syracuseStep 544391 = 816587) B816587
theorem B544571 : Blo 239816 544571 := bstep (se 1 (by rfl) ⟨408428, by rfl⟩ : syracuseStep 544571 = 816857) B816857
theorem B1036091 : Blo 239816 1036091 := bstep (se 1 (by rfl) ⟨777068, by rfl⟩ : syracuseStep 1036091 = 1554137) B1554137
theorem B347977 : Blo 239816 347977 := bstep (se 2 (by rfl) ⟨130491, by rfl⟩ : syracuseStep 347977 = 260983) B260983
theorem B610163 : Blo 239816 610163 := bstep (se 1 (by rfl) ⟨457622, by rfl⟩ : syracuseStep 610163 = 915245) B915245
theorem B544697 : Blo 239816 544697 := bstep (se 2 (by rfl) ⟨204261, by rfl⟩ : syracuseStep 544697 = 408523) B408523
theorem B4673483 : Blo 239816 4673483 := bstep (se 1 (by rfl) ⟨3505112, by rfl⟩ : syracuseStep 4673483 = 7010225) B7010225
theorem B4640813 : Blo 239816 4640813 := bstep (se 3 (by rfl) ⟨870152, by rfl⟩ : syracuseStep 4640813 = 1740305) B1740305
theorem B577651 : Blo 239816 577651 := bstep (se 1 (by rfl) ⟨433238, by rfl⟩ : syracuseStep 577651 = 866477) B866477
theorem B545039 : Blo 239816 545039 := bstep (se 1 (by rfl) ⟨408779, by rfl⟩ : syracuseStep 545039 = 817559) B817559
theorem B545057 : Blo 239816 545057 := bstep (se 2 (by rfl) ⟨204396, by rfl⟩ : syracuseStep 545057 = 408793) B408793
theorem B610679 : Blo 239816 610679 := bstep (se 1 (by rfl) ⟨458009, by rfl⟩ : syracuseStep 610679 = 916019) B916019
theorem B2052499 : Blo 239816 2052499 := bstep (se 1 (by rfl) ⟨1539374, by rfl⟩ : syracuseStep 2052499 = 3078749) B3078749
theorem B1233305 : Blo 239816 1233305 := bstep (se 2 (by rfl) ⟨462489, by rfl⟩ : syracuseStep 1233305 = 924979) B924979
theorem B1954307 : Blo 239816 1954307 := bstep (se 1 (by rfl) ⟨1465730, by rfl⟩ : syracuseStep 1954307 = 2931461) B2931461
theorem B545399 : Blo 239816 545399 := bstep (se 1 (by rfl) ⟨409049, by rfl⟩ : syracuseStep 545399 = 818099) B818099
theorem B512801 : Blo 239816 512801 := bstep (se 2 (by rfl) ⟨192300, by rfl⟩ : syracuseStep 512801 = 384601) B384601
theorem B545579 : Blo 239816 545579 := bstep (se 1 (by rfl) ⟨409184, by rfl⟩ : syracuseStep 545579 = 818369) B818369
theorem B578593 : Blo 239816 578593 := bstep (se 2 (by rfl) ⟨216972, by rfl⟩ : syracuseStep 578593 = 433945) B433945
theorem B1299523 : Blo 239816 1299523 := bstep (se 1 (by rfl) ⟨974642, by rfl⟩ : syracuseStep 1299523 = 1949285) B1949285
theorem B1168451 : Blo 239816 1168451 := bstep (se 1 (by rfl) ⟨876338, by rfl⟩ : syracuseStep 1168451 = 1752677) B1752677
theorem B545939 : Blo 239816 545939 := bstep (se 1 (by rfl) ⟨409454, by rfl⟩ : syracuseStep 545939 = 818909) B818909
theorem B545993 : Blo 239816 545993 := bstep (se 2 (by rfl) ⟨204747, by rfl⟩ : syracuseStep 545993 = 409495) B409495
theorem B611671 : Blo 239816 611671 := bstep (se 1 (by rfl) ⟨458753, by rfl⟩ : syracuseStep 611671 = 917507) B917507
theorem B611975 : Blo 239816 611975 := bstep (se 1 (by rfl) ⟨458981, by rfl⟩ : syracuseStep 611975 = 917963) B917963
theorem B612107 : Blo 239816 612107 := bstep (se 1 (by rfl) ⟨459080, by rfl⟩ : syracuseStep 612107 = 918161) B918161
theorem B513911 : Blo 239816 513911 := bstep (se 1 (by rfl) ⟨385433, by rfl⟩ : syracuseStep 513911 = 770867) B770867
theorem B546695 : Blo 239816 546695 := bstep (se 1 (by rfl) ⟨410021, by rfl⟩ : syracuseStep 546695 = 820043) B820043
theorem B546875 : Blo 239816 546875 := bstep (se 1 (by rfl) ⟨410156, by rfl⟩ : syracuseStep 546875 = 820313) B820313
theorem B1464493 : Blo 239816 1464493 := bstep (se 3 (by rfl) ⟨274592, by rfl⟩ : syracuseStep 1464493 = 549185) B549185
theorem B547001 : Blo 239816 547001 := bstep (se 2 (by rfl) ⟨205125, by rfl⟩ : syracuseStep 547001 = 410251) B410251
theorem B612623 : Blo 239816 612623 := bstep (se 1 (by rfl) ⟨459467, by rfl⟩ : syracuseStep 612623 = 918935) B918935
theorem B612755 : Blo 239816 612755 := bstep (se 1 (by rfl) ⟨459566, by rfl⟩ : syracuseStep 612755 = 919133) B919133
theorem B547343 : Blo 239816 547343 := bstep (se 1 (by rfl) ⟨410507, by rfl⟩ : syracuseStep 547343 = 821015) B821015
theorem B547361 : Blo 239816 547361 := bstep (se 2 (by rfl) ⟨205260, by rfl⟩ : syracuseStep 547361 = 410521) B410521
theorem B875069 : Blo 239816 875069 := bstep (se 3 (by rfl) ⟨164075, by rfl⟩ : syracuseStep 875069 = 328151) B328151
theorem B809729 : Blo 239816 809729 := bstep (se 2 (by rfl) ⟨303648, by rfl⟩ : syracuseStep 809729 = 607297) B607297
theorem B580439 : Blo 239816 580439 := bstep (se 1 (by rfl) ⟨435329, by rfl⟩ : syracuseStep 580439 = 870659) B870659
theorem B547703 : Blo 239816 547703 := bstep (se 1 (by rfl) ⟨410777, by rfl⟩ : syracuseStep 547703 = 821555) B821555
theorem B547883 : Blo 239816 547883 := bstep (se 1 (by rfl) ⟨410912, by rfl⟩ : syracuseStep 547883 = 821825) B821825
theorem B1236161 : Blo 239816 1236161 := bstep (se 2 (by rfl) ⟨463560, by rfl⟩ : syracuseStep 1236161 = 927121) B927121
theorem B548243 : Blo 239816 548243 := bstep (se 1 (by rfl) ⟨411182, by rfl⟩ : syracuseStep 548243 = 822365) B822365
theorem B548297 : Blo 239816 548297 := bstep (se 2 (by rfl) ⟨205611, by rfl⟩ : syracuseStep 548297 = 411223) B411223
theorem B613889 : Blo 239816 613889 := bstep (se 2 (by rfl) ⟨230208, by rfl⟩ : syracuseStep 613889 = 460417) B460417
theorem B810539 : Blo 239816 810539 := bstep (se 1 (by rfl) ⟨607904, by rfl⟩ : syracuseStep 810539 = 1215809) B1215809
theorem B614263 : Blo 239816 614263 := bstep (se 1 (by rfl) ⟨460697, by rfl⟩ : syracuseStep 614263 = 921395) B921395
theorem B614699 : Blo 239816 614699 := bstep (se 1 (by rfl) ⟨461024, by rfl⟩ : syracuseStep 614699 = 922049) B922049
theorem B1041133 : Blo 239816 1041133 := bstep (se 3 (by rfl) ⟨195212, by rfl⟩ : syracuseStep 1041133 = 390425) B390425
theorem B811835 : Blo 239816 811835 := bstep (se 1 (by rfl) ⟨608876, by rfl⟩ : syracuseStep 811835 = 1217753) B1217753
theorem B22438853 : Blo 239816 22438853 := bstep (se 4 (by rfl) ⟨2103642, by rfl⟩ : syracuseStep 22438853 = 4207285) B4207285
theorem B615539 : Blo 239816 615539 := bstep (se 1 (by rfl) ⟨461654, by rfl⟩ : syracuseStep 615539 = 923309) B923309
theorem B615559 : Blo 239816 615559 := bstep (se 1 (by rfl) ⟨461669, by rfl⟩ : syracuseStep 615559 = 923339) B923339
theorem B1467629 : Blo 239816 1467629 := bstep (se 3 (by rfl) ⟨275180, by rfl⟩ : syracuseStep 1467629 = 550361) B550361
theorem B812321 : Blo 239816 812321 := bstep (se 2 (by rfl) ⟨304620, by rfl⟩ : syracuseStep 812321 = 609241) B609241
theorem B615833 : Blo 239816 615833 := bstep (se 2 (by rfl) ⟨230937, by rfl⟩ : syracuseStep 615833 = 461875) B461875
theorem B8381875 : Blo 239816 8381875 := bstep (se 1 (by rfl) ⟨6286406, by rfl⟩ : syracuseStep 8381875 = 12572813) B12572813
theorem B4384205 : Blo 239816 4384205 := bstep (se 3 (by rfl) ⟨822038, by rfl⟩ : syracuseStep 4384205 = 1644077) B1644077
theorem B615995 : Blo 239816 615995 := bstep (se 1 (by rfl) ⟨461996, by rfl⟩ : syracuseStep 615995 = 923993) B923993
theorem B779863 : Blo 239816 779863 := bstep (se 1 (by rfl) ⟨584897, by rfl⟩ : syracuseStep 779863 = 1169795) B1169795
theorem B648905 : Blo 239816 648905 := bstep (se 2 (by rfl) ⟨243339, by rfl⟩ : syracuseStep 648905 = 486679) B486679
theorem B616207 : Blo 239816 616207 := bstep (se 1 (by rfl) ⟨462155, by rfl⟩ : syracuseStep 616207 = 924311) B924311
theorem B812915 : Blo 239816 812915 := bstep (se 1 (by rfl) ⟨609686, by rfl⟩ : syracuseStep 812915 = 1219373) B1219373
theorem B878471 : Blo 239816 878471 := bstep (se 1 (by rfl) ⟨658853, by rfl⟩ : syracuseStep 878471 = 1317707) B1317707
theorem B583571 : Blo 239816 583571 := bstep (se 1 (by rfl) ⟨437678, by rfl⟩ : syracuseStep 583571 = 875357) B875357
theorem B911371 : Blo 239816 911371 := bstep (se 1 (by rfl) ⟨683528, by rfl⟩ : syracuseStep 911371 = 1367057) B1367057
theorem B780299 : Blo 239816 780299 := bstep (se 1 (by rfl) ⟨585224, by rfl⟩ : syracuseStep 780299 = 1170449) B1170449
theorem B616481 : Blo 239816 616481 := bstep (se 2 (by rfl) ⟨231180, by rfl⟩ : syracuseStep 616481 = 462361) B462361
theorem B1370155 : Blo 239816 1370155 := bstep (se 1 (by rfl) ⟨1027616, by rfl⟩ : syracuseStep 1370155 = 2055233) B2055233
theorem B780349 : Blo 239816 780349 := bstep (se 3 (by rfl) ⟨146315, by rfl⟩ : syracuseStep 780349 = 292631) B292631
theorem B911675 : Blo 239816 911675 := bstep (se 1 (by rfl) ⟨683756, by rfl⟩ : syracuseStep 911675 = 1367513) B1367513
theorem B649847 : Blo 239816 649847 := bstep (se 1 (by rfl) ⟨487385, by rfl⟩ : syracuseStep 649847 = 974771) B974771
theorem B584339 : Blo 239816 584339 := bstep (se 1 (by rfl) ⟨438254, by rfl⟩ : syracuseStep 584339 = 876509) B876509
theorem B3893953 : Blo 239816 3893953 := bstep (se 2 (by rfl) ⟨1460232, by rfl⟩ : syracuseStep 3893953 = 2920465) B2920465
theorem B912161 : Blo 239816 912161 := bstep (se 2 (by rfl) ⟨342060, by rfl⟩ : syracuseStep 912161 = 684121) B684121
theorem B682937 : Blo 239816 682937 := bstep (se 2 (by rfl) ⟨256101, by rfl⟩ : syracuseStep 682937 = 512203) B512203
theorem B683279 : Blo 239816 683279 := bstep (se 1 (by rfl) ⟨512459, by rfl⟩ : syracuseStep 683279 = 1024919) B1024919
theorem B650539 : Blo 239816 650539 := bstep (se 1 (by rfl) ⟨487904, by rfl⟩ : syracuseStep 650539 = 975809) B975809
theorem B617843 : Blo 239816 617843 := bstep (se 1 (by rfl) ⟨463382, by rfl⟩ : syracuseStep 617843 = 926765) B926765
theorem B1371613 : Blo 239816 1371613 := bstep (se 3 (by rfl) ⟨257177, by rfl⟩ : syracuseStep 1371613 = 514355) B514355
theorem B1306115 : Blo 239816 1306115 := bstep (se 1 (by rfl) ⟨979586, by rfl⟩ : syracuseStep 1306115 = 1959173) B1959173
theorem B290363 : Blo 239816 290363 := bstep (se 1 (by rfl) ⟨217772, by rfl⟩ : syracuseStep 290363 = 435545) B435545
theorem B913133 : Blo 239816 913133 := bstep (se 3 (by rfl) ⟨171212, by rfl⟩ : syracuseStep 913133 = 342425) B342425
theorem B290575 : Blo 239816 290575 := bstep (se 1 (by rfl) ⟨217931, by rfl⟩ : syracuseStep 290575 = 435863) B435863
theorem B684065 : Blo 239816 684065 := bstep (se 2 (by rfl) ⟨256524, by rfl⟩ : syracuseStep 684065 = 513049) B513049
theorem B5304365 : Blo 239816 5304365 := bstep (se 3 (by rfl) ⟨994568, by rfl⟩ : syracuseStep 5304365 = 1989137) B1989137
theorem B5009501 : Blo 239816 5009501 := bstep (se 3 (by rfl) ⟨939281, by rfl⟩ : syracuseStep 5009501 = 1878563) B1878563
theorem B815507 : Blo 239816 815507 := bstep (se 1 (by rfl) ⟨611630, by rfl⟩ : syracuseStep 815507 = 1223261) B1223261
theorem B651673 : Blo 239816 651673 := bstep (se 2 (by rfl) ⟨244377, by rfl⟩ : syracuseStep 651673 = 488755) B488755
theorem B783049 : Blo 239816 783049 := bstep (se 2 (by rfl) ⟨293643, by rfl⟩ : syracuseStep 783049 = 587287) B587287
theorem B651977 : Blo 239816 651977 := bstep (se 2 (by rfl) ⟨244491, by rfl⟩ : syracuseStep 651977 = 488983) B488983
theorem B652151 : Blo 239816 652151 := bstep (se 1 (by rfl) ⟨489113, by rfl⟩ : syracuseStep 652151 = 978227) B978227
theorem B324751 : Blo 239816 324751 := bstep (se 1 (by rfl) ⟨243563, by rfl⟩ : syracuseStep 324751 = 487127) B487127
theorem B390329 : Blo 239816 390329 := bstep (se 2 (by rfl) ⟨146373, by rfl⟩ : syracuseStep 390329 = 292747) B292747
theorem B20903345 : Blo 239816 20903345 := bstep (se 2 (by rfl) ⟨7838754, by rfl⟩ : syracuseStep 20903345 = 15677509) B15677509
theorem B685579 : Blo 239816 685579 := bstep (se 1 (by rfl) ⟨514184, by rfl⟩ : syracuseStep 685579 = 1028369) B1028369
theorem B1144343 : Blo 239816 1144343 := bstep (se 1 (by rfl) ⟨858257, by rfl⟩ : syracuseStep 1144343 = 1716515) B1716515
theorem B1832705 : Blo 239816 1832705 := bstep (se 2 (by rfl) ⟨687264, by rfl⟩ : syracuseStep 1832705 = 1374529) B1374529
theorem B816911 : Blo 239816 816911 := bstep (se 1 (by rfl) ⟨612683, by rfl⟩ : syracuseStep 816911 = 1225367) B1225367
theorem B685853 : Blo 239816 685853 := bstep (se 3 (by rfl) ⟨128597, by rfl⟩ : syracuseStep 685853 = 257195) B257195
theorem B456491 : Blo 239816 456491 := bstep (se 1 (by rfl) ⟨342368, by rfl⟩ : syracuseStep 456491 = 684737) B684737
theorem B915259 : Blo 239816 915259 := bstep (se 1 (by rfl) ⟨686444, by rfl⟩ : syracuseStep 915259 = 1372889) B1372889
theorem B325577 : Blo 239816 325577 := bstep (se 2 (by rfl) ⟨122091, by rfl⟩ : syracuseStep 325577 = 244183) B244183
theorem B817181 : Blo 239816 817181 := bstep (se 3 (by rfl) ⟨153221, by rfl⟩ : syracuseStep 817181 = 306443) B306443
theorem B686195 : Blo 239816 686195 := bstep (se 1 (by rfl) ⟨514646, by rfl⟩ : syracuseStep 686195 = 1029293) B1029293
theorem B587911 : Blo 239816 587911 := bstep (se 1 (by rfl) ⟨440933, by rfl⟩ : syracuseStep 587911 = 881867) B881867
theorem B1472741 : Blo 239816 1472741 := bstep (se 4 (by rfl) ⟨138069, by rfl⟩ : syracuseStep 1472741 = 276139) B276139
theorem B915745 : Blo 239816 915745 := bstep (se 2 (by rfl) ⟨343404, by rfl⟩ : syracuseStep 915745 = 686809) B686809
theorem B981533 : Blo 239816 981533 := bstep (se 3 (by rfl) ⟨184037, by rfl⟩ : syracuseStep 981533 = 368075) B368075
theorem B457417 : Blo 239816 457417 := bstep (se 2 (by rfl) ⟨171531, by rfl⟩ : syracuseStep 457417 = 343063) B343063
theorem B7863155 : Blo 239816 7863155 := bstep (se 1 (by rfl) ⟨5897366, by rfl⟩ : syracuseStep 7863155 = 11794733) B11794733
theorem B621611 : Blo 239816 621611 := bstep (se 1 (by rfl) ⟨466208, by rfl⟩ : syracuseStep 621611 = 932417) B932417
theorem B687163 : Blo 239816 687163 := bstep (se 1 (by rfl) ⟨515372, by rfl⟩ : syracuseStep 687163 = 1030745) B1030745
theorem B916717 : Blo 239816 916717 := bstep (se 3 (by rfl) ⟨171884, by rfl⟩ : syracuseStep 916717 = 343769) B343769
theorem B18513197 : Blo 239816 18513197 := bstep (se 3 (by rfl) ⟨3471224, by rfl⟩ : syracuseStep 18513197 = 6942449) B6942449
theorem B359753 : Blo 239816 359753 := bstep (se 2 (by rfl) ⟨134907, by rfl⟩ : syracuseStep 359753 = 269815) B269815
theorem B458131 : Blo 239816 458131 := bstep (se 1 (by rfl) ⟨343598, by rfl⟩ : syracuseStep 458131 = 687197) B687197
theorem B654745 : Blo 239816 654745 := bstep (se 2 (by rfl) ⟨245529, by rfl⟩ : syracuseStep 654745 = 491059) B491059
theorem B818585 : Blo 239816 818585 := bstep (se 2 (by rfl) ⟨306969, by rfl⟩ : syracuseStep 818585 = 613939) B613939
theorem B359867 : Blo 239816 359867 := bstep (se 1 (by rfl) ⟨269900, by rfl⟩ : syracuseStep 359867 = 539801) B539801
theorem B359927 : Blo 239816 359927 := bstep (se 1 (by rfl) ⟨269945, by rfl⟩ : syracuseStep 359927 = 539891) B539891
theorem B359951 : Blo 239816 359951 := bstep (se 1 (by rfl) ⟨269963, by rfl⟩ : syracuseStep 359951 = 539927) B539927
theorem B917021 : Blo 239816 917021 := bstep (se 3 (by rfl) ⟨171941, by rfl⟩ : syracuseStep 917021 = 343883) B343883
theorem B359993 : Blo 239816 359993 := bstep (se 2 (by rfl) ⟨134997, by rfl⟩ : syracuseStep 359993 = 269995) B269995
theorem B1375805 : Blo 239816 1375805 := bstep (se 3 (by rfl) ⟨257963, by rfl⟩ : syracuseStep 1375805 = 515927) B515927
theorem B5242445 : Blo 239816 5242445 := bstep (se 3 (by rfl) ⟨982958, by rfl⟩ : syracuseStep 5242445 = 1965917) B1965917
theorem B360071 : Blo 239816 360071 := bstep (se 1 (by rfl) ⟨270053, by rfl⟩ : syracuseStep 360071 = 540107) B540107
theorem B360107 : Blo 239816 360107 := bstep (se 1 (by rfl) ⟨270080, by rfl⟩ : syracuseStep 360107 = 540161) B540161
theorem B360137 : Blo 239816 360137 := bstep (se 2 (by rfl) ⟨135051, by rfl⟩ : syracuseStep 360137 = 270103) B270103
theorem B655133 : Blo 239816 655133 := bstep (se 3 (by rfl) ⟨122837, by rfl⟩ : syracuseStep 655133 = 245675) B245675
theorem B360251 : Blo 239816 360251 := bstep (se 1 (by rfl) ⟨270188, by rfl⟩ : syracuseStep 360251 = 540377) B540377
theorem B360311 : Blo 239816 360311 := bstep (se 1 (by rfl) ⟨270233, by rfl⟩ : syracuseStep 360311 = 540467) B540467
theorem B360335 : Blo 239816 360335 := bstep (se 1 (by rfl) ⟨270251, by rfl⟩ : syracuseStep 360335 = 540503) B540503
theorem B360377 : Blo 239816 360377 := bstep (se 2 (by rfl) ⟨135141, by rfl⟩ : syracuseStep 360377 = 270283) B270283
theorem B1540043 : Blo 239816 1540043 := bstep (se 1 (by rfl) ⟨1155032, by rfl⟩ : syracuseStep 1540043 = 2310065) B2310065
theorem B360527 : Blo 239816 360527 := bstep (se 1 (by rfl) ⟨270395, by rfl⟩ : syracuseStep 360527 = 540791) B540791
theorem B458875 : Blo 239816 458875 := bstep (se 1 (by rfl) ⟨344156, by rfl⟩ : syracuseStep 458875 = 688313) B688313
theorem B917675 : Blo 239816 917675 := bstep (se 1 (by rfl) ⟨688256, by rfl⟩ : syracuseStep 917675 = 1376513) B1376513
theorem B360647 : Blo 239816 360647 := bstep (se 1 (by rfl) ⟨270485, by rfl⟩ : syracuseStep 360647 = 540971) B540971
theorem B459103 : Blo 239816 459103 := bstep (se 1 (by rfl) ⟨344327, by rfl⟩ : syracuseStep 459103 = 688655) B688655
theorem B360809 : Blo 239816 360809 := bstep (se 2 (by rfl) ⟨135303, by rfl⟩ : syracuseStep 360809 = 270607) B270607
theorem B360887 : Blo 239816 360887 := bstep (se 1 (by rfl) ⟨270665, by rfl⟩ : syracuseStep 360887 = 541331) B541331
theorem B360923 : Blo 239816 360923 := bstep (se 1 (by rfl) ⟨270692, by rfl⟩ : syracuseStep 360923 = 541385) B541385
theorem B459361 : Blo 239816 459361 := bstep (se 2 (by rfl) ⟨172260, by rfl⟩ : syracuseStep 459361 = 344521) B344521
theorem B7537481 : Blo 239816 7537481 := bstep (se 2 (by rfl) ⟨2826555, by rfl⟩ : syracuseStep 7537481 = 5653111) B5653111
theorem B3900311 : Blo 239816 3900311 := bstep (se 1 (by rfl) ⟨2925233, by rfl⟩ : syracuseStep 3900311 = 5850467) B5850467
theorem B361391 : Blo 239816 361391 := bstep (se 1 (by rfl) ⟨271043, by rfl⟩ : syracuseStep 361391 = 542087) B542087
theorem B459695 : Blo 239816 459695 := bstep (se 1 (by rfl) ⟨344771, by rfl⟩ : syracuseStep 459695 = 689543) B689543
theorem B820151 : Blo 239816 820151 := bstep (se 1 (by rfl) ⟨615113, by rfl⟩ : syracuseStep 820151 = 1230227) B1230227
theorem B2950145 : Blo 239816 2950145 := bstep (se 2 (by rfl) ⟨1106304, by rfl⟩ : syracuseStep 2950145 = 2212609) B2212609
theorem B361481 : Blo 239816 361481 := bstep (se 2 (by rfl) ⟨135555, by rfl⟩ : syracuseStep 361481 = 271111) B271111
theorem B361511 : Blo 239816 361511 := bstep (se 1 (by rfl) ⟨271133, by rfl⟩ : syracuseStep 361511 = 542267) B542267
theorem B361595 : Blo 239816 361595 := bstep (se 1 (by rfl) ⟨271196, by rfl⟩ : syracuseStep 361595 = 542393) B542393
theorem B361721 : Blo 239816 361721 := bstep (se 2 (by rfl) ⟨135645, by rfl⟩ : syracuseStep 361721 = 271291) B271291
theorem B5211485 : Blo 239816 5211485 := bstep (se 3 (by rfl) ⟨977153, by rfl⟩ : syracuseStep 5211485 = 1954307) B1954307
theorem B361823 : Blo 239816 361823 := bstep (se 1 (by rfl) ⟨271367, by rfl⟩ : syracuseStep 361823 = 542735) B542735
theorem B361835 : Blo 239816 361835 := bstep (se 1 (by rfl) ⟨271376, by rfl⟩ : syracuseStep 361835 = 542753) B542753
theorem B2491813 : Blo 239816 2491813 := bstep (se 4 (by rfl) ⟨233607, by rfl⟩ : syracuseStep 2491813 = 467215) B467215
theorem B820745 : Blo 239816 820745 := bstep (se 2 (by rfl) ⟨307779, by rfl⟩ : syracuseStep 820745 = 615559) B615559
theorem B362063 : Blo 239816 362063 := bstep (se 1 (by rfl) ⟨271547, by rfl⟩ : syracuseStep 362063 = 543095) B543095
theorem B362183 : Blo 239816 362183 := bstep (se 1 (by rfl) ⟨271637, by rfl⟩ : syracuseStep 362183 = 543275) B543275
theorem B362345 : Blo 239816 362345 := bstep (se 2 (by rfl) ⟨135879, by rfl⟩ : syracuseStep 362345 = 271759) B271759
theorem B11175833 : Blo 239816 11175833 := bstep (se 2 (by rfl) ⟨4190937, by rfl⟩ : syracuseStep 11175833 = 8381875) B8381875
theorem B4655029 : Blo 239816 4655029 := bstep (se 5 (by rfl) ⟨218204, by rfl⟩ : syracuseStep 4655029 = 436409) B436409
theorem B362423 : Blo 239816 362423 := bstep (se 1 (by rfl) ⟨271817, by rfl⟩ : syracuseStep 362423 = 543635) B543635
theorem B362459 : Blo 239816 362459 := bstep (se 1 (by rfl) ⟨271844, by rfl⟩ : syracuseStep 362459 = 543689) B543689
theorem B460819 : Blo 239816 460819 := bstep (se 1 (by rfl) ⟨345614, by rfl⟩ : syracuseStep 460819 = 691229) B691229
theorem B919633 : Blo 239816 919633 := bstep (se 2 (by rfl) ⟨344862, by rfl⟩ : syracuseStep 919633 = 689725) B689725
theorem B461047 : Blo 239816 461047 := bstep (se 1 (by rfl) ⟨345785, by rfl⟩ : syracuseStep 461047 = 691571) B691571
theorem B821609 : Blo 239816 821609 := bstep (se 2 (by rfl) ⟨308103, by rfl⟩ : syracuseStep 821609 = 616207) B616207
theorem B919937 : Blo 239816 919937 := bstep (se 2 (by rfl) ⟨344976, by rfl⟩ : syracuseStep 919937 = 689953) B689953
theorem B362927 : Blo 239816 362927 := bstep (se 1 (by rfl) ⟨272195, by rfl⟩ : syracuseStep 362927 = 544391) B544391
theorem B363017 : Blo 239816 363017 := bstep (se 2 (by rfl) ⟨136131, by rfl⟩ : syracuseStep 363017 = 272263) B272263
theorem B363047 : Blo 239816 363047 := bstep (se 1 (by rfl) ⟨272285, by rfl⟩ : syracuseStep 363047 = 544571) B544571
theorem B461351 : Blo 239816 461351 := bstep (se 1 (by rfl) ⟨346013, by rfl⟩ : syracuseStep 461351 = 692027) B692027
theorem B363131 : Blo 239816 363131 := bstep (se 1 (by rfl) ⟨272348, by rfl⟩ : syracuseStep 363131 = 544697) B544697
theorem B3115655 : Blo 239816 3115655 := bstep (se 1 (by rfl) ⟨2336741, by rfl⟩ : syracuseStep 3115655 = 4673483) B4673483
theorem B1215161 : Blo 239816 1215161 := bstep (se 2 (by rfl) ⟨455685, by rfl⟩ : syracuseStep 1215161 = 911371) B911371
theorem B363257 : Blo 239816 363257 := bstep (se 2 (by rfl) ⟨136221, by rfl⟩ : syracuseStep 363257 = 272443) B272443
theorem B920393 : Blo 239816 920393 := bstep (se 2 (by rfl) ⟨345147, by rfl⟩ : syracuseStep 920393 = 690295) B690295
theorem B363359 : Blo 239816 363359 := bstep (se 1 (by rfl) ⟨272519, by rfl⟩ : syracuseStep 363359 = 545039) B545039
theorem B363371 : Blo 239816 363371 := bstep (se 1 (by rfl) ⟨272528, by rfl⟩ : syracuseStep 363371 = 545057) B545057
theorem B2231185 : Blo 239816 2231185 := bstep (se 2 (by rfl) ⟨836694, by rfl⟩ : syracuseStep 2231185 = 1673389) B1673389
theorem B822203 : Blo 239816 822203 := bstep (se 1 (by rfl) ⟨616652, by rfl⟩ : syracuseStep 822203 = 1233305) B1233305
theorem B920591 : Blo 239816 920591 := bstep (se 1 (by rfl) ⟨690443, by rfl⟩ : syracuseStep 920591 = 1380887) B1380887
theorem B363599 : Blo 239816 363599 := bstep (se 1 (by rfl) ⟨272699, by rfl⟩ : syracuseStep 363599 = 545399) B545399
theorem B986269 : Blo 239816 986269 := bstep (se 3 (by rfl) ⟨184925, by rfl⟩ : syracuseStep 986269 = 369851) B369851
theorem B363719 : Blo 239816 363719 := bstep (se 1 (by rfl) ⟨272789, by rfl⟩ : syracuseStep 363719 = 545579) B545579
theorem B363881 : Blo 239816 363881 := bstep (se 2 (by rfl) ⟨136455, by rfl⟩ : syracuseStep 363881 = 272911) B272911
theorem B363959 : Blo 239816 363959 := bstep (se 1 (by rfl) ⟨272969, by rfl⟩ : syracuseStep 363959 = 545939) B545939
theorem B1838537 : Blo 239816 1838537 := bstep (se 2 (by rfl) ⟨689451, by rfl⟩ : syracuseStep 1838537 = 1378903) B1378903
theorem B363995 : Blo 239816 363995 := bstep (se 1 (by rfl) ⟨272996, by rfl⟩ : syracuseStep 363995 = 545993) B545993
theorem B3509725 : Blo 239816 3509725 := bstep (se 3 (by rfl) ⟨658073, by rfl⟩ : syracuseStep 3509725 = 1316147) B1316147
theorem B1969879 : Blo 239816 1969879 := bstep (se 1 (by rfl) ⟨1477409, by rfl⟩ : syracuseStep 1969879 = 2954819) B2954819
theorem B462665 : Blo 239816 462665 := bstep (se 2 (by rfl) ⟨173499, by rfl⟩ : syracuseStep 462665 = 346999) B346999
theorem B364463 : Blo 239816 364463 := bstep (se 1 (by rfl) ⟨273347, by rfl⟩ : syracuseStep 364463 = 546695) B546695
theorem B364553 : Blo 239816 364553 := bstep (se 2 (by rfl) ⟨136707, by rfl⟩ : syracuseStep 364553 = 273415) B273415
theorem B364583 : Blo 239816 364583 := bstep (se 1 (by rfl) ⟨273437, by rfl⟩ : syracuseStep 364583 = 546875) B546875
theorem B364667 : Blo 239816 364667 := bstep (se 1 (by rfl) ⟨273500, by rfl⟩ : syracuseStep 364667 = 547001) B547001
theorem B364793 : Blo 239816 364793 := bstep (se 2 (by rfl) ⟨136797, by rfl⟩ : syracuseStep 364793 = 273595) B273595
theorem B2101565 : Blo 239816 2101565 := bstep (se 3 (by rfl) ⟨394043, by rfl⟩ : syracuseStep 2101565 = 788087) B788087
theorem B364895 : Blo 239816 364895 := bstep (se 1 (by rfl) ⟨273671, by rfl⟩ : syracuseStep 364895 = 547343) B547343
theorem B364907 : Blo 239816 364907 := bstep (se 1 (by rfl) ⟨273680, by rfl⟩ : syracuseStep 364907 = 547361) B547361
theorem B331321873 : Blo 239816 331321873 := bstep (se 2 (by rfl) ⟨124245702, by rfl⟩ : syracuseStep 331321873 = 248491405) B248491405
theorem B365135 : Blo 239816 365135 := bstep (se 1 (by rfl) ⟨273851, by rfl⟩ : syracuseStep 365135 = 547703) B547703
theorem B365255 : Blo 239816 365255 := bstep (se 1 (by rfl) ⟨273941, by rfl⟩ : syracuseStep 365255 = 547883) B547883
theorem B824107 : Blo 239816 824107 := bstep (se 1 (by rfl) ⟨618080, by rfl⟩ : syracuseStep 824107 = 1236161) B1236161
theorem B365417 : Blo 239816 365417 := bstep (se 2 (by rfl) ⟨137031, by rfl⟩ : syracuseStep 365417 = 274063) B274063
theorem B365495 : Blo 239816 365495 := bstep (se 1 (by rfl) ⟨274121, by rfl⟩ : syracuseStep 365495 = 548243) B548243
theorem B365531 : Blo 239816 365531 := bstep (se 1 (by rfl) ⟨274148, by rfl⟩ : syracuseStep 365531 = 548297) B548297
theorem B463969 : Blo 239816 463969 := bstep (se 2 (by rfl) ⟨173988, by rfl⟩ : syracuseStep 463969 = 347977) B347977
theorem B595343 : Blo 239816 595343 := bstep (se 1 (by rfl) ⟨446507, by rfl⟩ : syracuseStep 595343 = 893015) B893015
theorem B3708965 : Blo 239816 3708965 := bstep (se 4 (by rfl) ⟨347715, by rfl⟩ : syracuseStep 3708965 = 695431) B695431
theorem B2332709 : Blo 239816 2332709 := bstep (se 4 (by rfl) ⟨218691, by rfl⟩ : syracuseStep 2332709 = 437383) B437383
theorem B2922803 : Blo 239816 2922803 := bstep (se 1 (by rfl) ⟨2192102, by rfl⟩ : syracuseStep 2922803 = 4384205) B4384205
theorem B433001 : Blo 239816 433001 := bstep (se 2 (by rfl) ⟨162375, by rfl⟩ : syracuseStep 433001 = 324751) B324751
theorem B6232949 : Blo 239816 6232949 := bstep (se 5 (by rfl) ⟨292169, by rfl⟩ : syracuseStep 6232949 = 584339) B584339
theorem B433231 : Blo 239816 433231 := bstep (se 1 (by rfl) ⟨324923, by rfl⟩ : syracuseStep 433231 = 649847) B649847
theorem B990323 : Blo 239816 990323 := bstep (se 1 (by rfl) ⟨742742, by rfl⟩ : syracuseStep 990323 = 1485485) B1485485
theorem B7020269 : Blo 239816 7020269 := bstep (se 3 (by rfl) ⟨1316300, by rfl⟩ : syracuseStep 7020269 = 2632601) B2632601
theorem B1220345 : Blo 239816 1220345 := bstep (se 2 (by rfl) ⟨457629, by rfl⟩ : syracuseStep 1220345 = 915259) B915259
theorem B1384235 : Blo 239816 1384235 := bstep (se 1 (by rfl) ⟨1038176, by rfl⟩ : syracuseStep 1384235 = 2076353) B2076353
theorem B270175 : Blo 239816 270175 := bstep (se 1 (by rfl) ⟨202631, by rfl⟩ : syracuseStep 270175 = 405263) B405263
theorem B270535 : Blo 239816 270535 := bstep (se 1 (by rfl) ⟨202901, by rfl⟩ : syracuseStep 270535 = 405803) B405803
theorem B1220993 : Blo 239816 1220993 := bstep (se 2 (by rfl) ⟨457872, by rfl⟩ : syracuseStep 1220993 = 915745) B915745
theorem B434651 : Blo 239816 434651 := bstep (se 1 (by rfl) ⟨325988, by rfl⟩ : syracuseStep 434651 = 651977) B651977
theorem B434767 : Blo 239816 434767 := bstep (se 1 (by rfl) ⟨326075, by rfl⟩ : syracuseStep 434767 = 652151) B652151
theorem B2106287 : Blo 239816 2106287 := bstep (se 1 (by rfl) ⟨1579715, by rfl⟩ : syracuseStep 2106287 = 3159431) B3159431
theorem B13935563 : Blo 239816 13935563 := bstep (se 1 (by rfl) ⟨10451672, by rfl⟩ : syracuseStep 13935563 = 20903345) B20903345
theorem B762895 : Blo 239816 762895 := bstep (se 1 (by rfl) ⟨572171, by rfl⟩ : syracuseStep 762895 = 1144343) B1144343
theorem B271399 : Blo 239816 271399 := bstep (se 1 (by rfl) ⟨203549, by rfl⟩ : syracuseStep 271399 = 407099) B407099
theorem B1221803 : Blo 239816 1221803 := bstep (se 1 (by rfl) ⟨916352, by rfl⟩ : syracuseStep 1221803 = 1832705) B1832705
theorem B304327 : Blo 239816 304327 := bstep (se 1 (by rfl) ⟨228245, by rfl⟩ : syracuseStep 304327 = 456491) B456491
theorem B6661577 : Blo 239816 6661577 := bstep (se 2 (by rfl) ⟨2498091, by rfl⟩ : syracuseStep 6661577 = 4996183) B4996183
theorem B2598389 : Blo 239816 2598389 := bstep (se 5 (by rfl) ⟨121799, by rfl⟩ : syracuseStep 2598389 = 243599) B243599
theorem B1222289 : Blo 239816 1222289 := bstep (se 2 (by rfl) ⟨458358, by rfl⟩ : syracuseStep 1222289 = 916717) B916717
theorem B1747021 : Blo 239816 1747021 := bstep (se 3 (by rfl) ⟨327566, by rfl⟩ : syracuseStep 1747021 = 655133) B655133
theorem B2762909 : Blo 239816 2762909 := bstep (se 3 (by rfl) ⟨518045, by rfl⟩ : syracuseStep 2762909 = 1036091) B1036091
theorem B239835 : Blo 239816 239835 := bstep (se 1 (by rfl) ⟨179876, by rfl⟩ : syracuseStep 239835 = 359753) B359753
theorem B239911 : Blo 239816 239911 := bstep (se 1 (by rfl) ⟨179933, by rfl⟩ : syracuseStep 239911 = 359867) B359867
theorem B239951 : Blo 239816 239951 := bstep (se 1 (by rfl) ⟨179963, by rfl⟩ : syracuseStep 239951 = 359927) B359927
theorem B239967 : Blo 239816 239967 := bstep (se 1 (by rfl) ⟨179975, by rfl⟩ : syracuseStep 239967 = 359951) B359951
theorem B239995 : Blo 239816 239995 := bstep (se 1 (by rfl) ⟨179996, by rfl⟩ : syracuseStep 239995 = 359993) B359993
theorem B240047 : Blo 239816 240047 := bstep (se 1 (by rfl) ⟨180035, by rfl⟩ : syracuseStep 240047 = 360071) B360071
theorem B240071 : Blo 239816 240071 := bstep (se 1 (by rfl) ⟨180053, by rfl⟩ : syracuseStep 240071 = 360107) B360107
theorem B240091 : Blo 239816 240091 := bstep (se 1 (by rfl) ⟨180068, by rfl⟩ : syracuseStep 240091 = 360137) B360137
theorem B1026593 : Blo 239816 1026593 := bstep (se 2 (by rfl) ⟨384972, by rfl⟩ : syracuseStep 1026593 = 769945) B769945
theorem B240167 : Blo 239816 240167 := bstep (se 1 (by rfl) ⟨180125, by rfl⟩ : syracuseStep 240167 = 360251) B360251
theorem B240207 : Blo 239816 240207 := bstep (se 1 (by rfl) ⟨180155, by rfl⟩ : syracuseStep 240207 = 360311) B360311
theorem B240223 : Blo 239816 240223 := bstep (se 1 (by rfl) ⟨180167, by rfl⟩ : syracuseStep 240223 = 360335) B360335
theorem B240251 : Blo 239816 240251 := bstep (se 1 (by rfl) ⟨180188, by rfl⟩ : syracuseStep 240251 = 360377) B360377
theorem B273019 : Blo 239816 273019 := bstep (se 1 (by rfl) ⟨204764, by rfl⟩ : syracuseStep 273019 = 409529) B409529
theorem B1026695 : Blo 239816 1026695 := bstep (se 1 (by rfl) ⟨770021, by rfl⟩ : syracuseStep 1026695 = 1540043) B1540043
theorem B240303 : Blo 239816 240303 := bstep (se 1 (by rfl) ⟨180227, by rfl⟩ : syracuseStep 240303 = 360455) B360455
theorem B240327 : Blo 239816 240327 := bstep (se 1 (by rfl) ⟨180245, by rfl⟩ : syracuseStep 240327 = 360491) B360491
theorem B240347 : Blo 239816 240347 := bstep (se 1 (by rfl) ⟨180260, by rfl⟩ : syracuseStep 240347 = 360521) B360521
theorem B240423 : Blo 239816 240423 := bstep (se 1 (by rfl) ⟨180317, by rfl⟩ : syracuseStep 240423 = 360635) B360635
theorem B240463 : Blo 239816 240463 := bstep (se 1 (by rfl) ⟨180347, by rfl⟩ : syracuseStep 240463 = 360695) B360695
theorem B240479 : Blo 239816 240479 := bstep (se 1 (by rfl) ⟨180359, by rfl⟩ : syracuseStep 240479 = 360719) B360719
theorem B240507 : Blo 239816 240507 := bstep (se 1 (by rfl) ⟨180380, by rfl⟩ : syracuseStep 240507 = 360761) B360761
theorem B240559 : Blo 239816 240559 := bstep (se 1 (by rfl) ⟨180419, by rfl⟩ : syracuseStep 240559 = 360839) B360839
theorem B240583 : Blo 239816 240583 := bstep (se 1 (by rfl) ⟨180437, by rfl⟩ : syracuseStep 240583 = 360875) B360875
theorem B240603 : Blo 239816 240603 := bstep (se 1 (by rfl) ⟨180452, by rfl⟩ : syracuseStep 240603 = 360905) B360905
theorem B1616915 : Blo 239816 1616915 := bstep (se 1 (by rfl) ⟨1212686, by rfl⟩ : syracuseStep 1616915 = 2425373) B2425373
theorem B240679 : Blo 239816 240679 := bstep (se 1 (by rfl) ⟨180509, by rfl⟩ : syracuseStep 240679 = 361019) B361019
theorem B240719 : Blo 239816 240719 := bstep (se 1 (by rfl) ⟨180539, by rfl⟩ : syracuseStep 240719 = 361079) B361079
theorem B273487 : Blo 239816 273487 := bstep (se 1 (by rfl) ⟨205115, by rfl⟩ : syracuseStep 273487 = 410231) B410231
theorem B240735 : Blo 239816 240735 := bstep (se 1 (by rfl) ⟨180551, by rfl⟩ : syracuseStep 240735 = 361103) B361103
theorem B240763 : Blo 239816 240763 := bstep (se 1 (by rfl) ⟨180572, by rfl⟩ : syracuseStep 240763 = 361145) B361145
theorem B928921 : Blo 239816 928921 := bstep (se 2 (by rfl) ⟨348345, by rfl⟩ : syracuseStep 928921 = 696691) B696691
theorem B240815 : Blo 239816 240815 := bstep (se 1 (by rfl) ⟨180611, by rfl⟩ : syracuseStep 240815 = 361223) B361223
theorem B2305219 : Blo 239816 2305219 := bstep (se 1 (by rfl) ⟨1728914, by rfl⟩ : syracuseStep 2305219 = 3457829) B3457829
theorem B240839 : Blo 239816 240839 := bstep (se 1 (by rfl) ⟨180629, by rfl⟩ : syracuseStep 240839 = 361259) B361259
theorem B240859 : Blo 239816 240859 := bstep (se 1 (by rfl) ⟨180644, by rfl⟩ : syracuseStep 240859 = 361289) B361289
theorem B929015 : Blo 239816 929015 := bstep (se 1 (by rfl) ⟨696761, by rfl⟩ : syracuseStep 929015 = 1393523) B1393523
theorem B240935 : Blo 239816 240935 := bstep (se 1 (by rfl) ⟨180701, by rfl⟩ : syracuseStep 240935 = 361403) B361403
theorem B240975 : Blo 239816 240975 := bstep (se 1 (by rfl) ⟨180731, by rfl⟩ : syracuseStep 240975 = 361463) B361463
theorem B404831 : Blo 239816 404831 := bstep (se 1 (by rfl) ⟨303623, by rfl⟩ : syracuseStep 404831 = 607247) B607247
theorem B240991 : Blo 239816 240991 := bstep (se 1 (by rfl) ⟨180743, by rfl⟩ : syracuseStep 240991 = 361487) B361487
theorem B241019 : Blo 239816 241019 := bstep (se 1 (by rfl) ⟨180764, by rfl⟩ : syracuseStep 241019 = 361529) B361529
theorem B241071 : Blo 239816 241071 := bstep (se 1 (by rfl) ⟨180803, by rfl⟩ : syracuseStep 241071 = 361607) B361607
theorem B241095 : Blo 239816 241095 := bstep (se 1 (by rfl) ⟨180821, by rfl⟩ : syracuseStep 241095 = 361643) B361643
theorem B241115 : Blo 239816 241115 := bstep (se 1 (by rfl) ⟨180836, by rfl⟩ : syracuseStep 241115 = 361673) B361673
theorem B273883 : Blo 239816 273883 := bstep (se 1 (by rfl) ⟨205412, by rfl⟩ : syracuseStep 273883 = 410825) B410825
theorem B241191 : Blo 239816 241191 := bstep (se 1 (by rfl) ⟨180893, by rfl⟩ : syracuseStep 241191 = 361787) B361787
theorem B241231 : Blo 239816 241231 := bstep (se 1 (by rfl) ⟨180923, by rfl⟩ : syracuseStep 241231 = 361847) B361847
theorem B306767 : Blo 239816 306767 := bstep (se 1 (by rfl) ⟨230075, by rfl⟩ : syracuseStep 306767 = 460151) B460151
theorem B3321431 : Blo 239816 3321431 := bstep (se 1 (by rfl) ⟨2491073, by rfl⟩ : syracuseStep 3321431 = 4982147) B4982147
theorem B241247 : Blo 239816 241247 := bstep (se 1 (by rfl) ⟨180935, by rfl⟩ : syracuseStep 241247 = 361871) B361871
theorem B241275 : Blo 239816 241275 := bstep (se 1 (by rfl) ⟨180956, by rfl⟩ : syracuseStep 241275 = 361913) B361913
theorem B1388177 : Blo 239816 1388177 := bstep (se 2 (by rfl) ⟨520566, by rfl⟩ : syracuseStep 1388177 = 1041133) B1041133
theorem B241327 : Blo 239816 241327 := bstep (se 1 (by rfl) ⟨180995, by rfl⟩ : syracuseStep 241327 = 361991) B361991
theorem B241351 : Blo 239816 241351 := bstep (se 1 (by rfl) ⟨181013, by rfl⟩ : syracuseStep 241351 = 362027) B362027
theorem B241371 : Blo 239816 241371 := bstep (se 1 (by rfl) ⟨181028, by rfl⟩ : syracuseStep 241371 = 362057) B362057
theorem B241447 : Blo 239816 241447 := bstep (se 1 (by rfl) ⟨181085, by rfl⟩ : syracuseStep 241447 = 362171) B362171
theorem B241487 : Blo 239816 241487 := bstep (se 1 (by rfl) ⟨181115, by rfl⟩ : syracuseStep 241487 = 362231) B362231
theorem B241503 : Blo 239816 241503 := bstep (se 1 (by rfl) ⟨181127, by rfl⟩ : syracuseStep 241503 = 362255) B362255
theorem B1224557 : Blo 239816 1224557 := bstep (se 3 (by rfl) ⟨229604, by rfl⟩ : syracuseStep 1224557 = 459209) B459209
theorem B241531 : Blo 239816 241531 := bstep (se 1 (by rfl) ⟨181148, by rfl⟩ : syracuseStep 241531 = 362297) B362297
theorem B405391 : Blo 239816 405391 := bstep (se 1 (by rfl) ⟨304043, by rfl⟩ : syracuseStep 405391 = 608087) B608087
theorem B241583 : Blo 239816 241583 := bstep (se 1 (by rfl) ⟨181187, by rfl⟩ : syracuseStep 241583 = 362375) B362375
theorem B1028027 : Blo 239816 1028027 := bstep (se 1 (by rfl) ⟨771020, by rfl⟩ : syracuseStep 1028027 = 1542041) B1542041
theorem B241607 : Blo 239816 241607 := bstep (se 1 (by rfl) ⟨181205, by rfl⟩ : syracuseStep 241607 = 362411) B362411
theorem B241627 : Blo 239816 241627 := bstep (se 1 (by rfl) ⟨181220, by rfl⟩ : syracuseStep 241627 = 362441) B362441
theorem B1224719 : Blo 239816 1224719 := bstep (se 1 (by rfl) ⟨918539, by rfl⟩ : syracuseStep 1224719 = 1837079) B1837079
theorem B241703 : Blo 239816 241703 := bstep (se 1 (by rfl) ⟨181277, by rfl⟩ : syracuseStep 241703 = 362555) B362555
theorem B241743 : Blo 239816 241743 := bstep (se 1 (by rfl) ⟨181307, by rfl⟩ : syracuseStep 241743 = 362615) B362615
theorem B241759 : Blo 239816 241759 := bstep (se 1 (by rfl) ⟨181319, by rfl⟩ : syracuseStep 241759 = 362639) B362639
theorem B241787 : Blo 239816 241787 := bstep (se 1 (by rfl) ⟨181340, by rfl⟩ : syracuseStep 241787 = 362681) B362681
theorem B438443 : Blo 239816 438443 := bstep (se 1 (by rfl) ⟨328832, by rfl⟩ : syracuseStep 438443 = 657665) B657665
theorem B241839 : Blo 239816 241839 := bstep (se 1 (by rfl) ⟨181379, by rfl⟩ : syracuseStep 241839 = 362759) B362759
theorem B241863 : Blo 239816 241863 := bstep (se 1 (by rfl) ⟨181397, by rfl⟩ : syracuseStep 241863 = 362795) B362795
theorem B241883 : Blo 239816 241883 := bstep (se 1 (by rfl) ⟨181412, by rfl⟩ : syracuseStep 241883 = 362825) B362825
theorem B864503 : Blo 239816 864503 := bstep (se 1 (by rfl) ⟨648377, by rfl⟩ : syracuseStep 864503 = 1296755) B1296755
theorem B241959 : Blo 239816 241959 := bstep (se 1 (by rfl) ⟨181469, by rfl⟩ : syracuseStep 241959 = 362939) B362939
theorem B438601 : Blo 239816 438601 := bstep (se 2 (by rfl) ⟨164475, by rfl⟩ : syracuseStep 438601 = 328951) B328951
theorem B241999 : Blo 239816 241999 := bstep (se 1 (by rfl) ⟨181499, by rfl⟩ : syracuseStep 241999 = 362999) B362999
theorem B242015 : Blo 239816 242015 := bstep (se 1 (by rfl) ⟨181511, by rfl⟩ : syracuseStep 242015 = 363023) B363023
theorem B242043 : Blo 239816 242043 := bstep (se 1 (by rfl) ⟨181532, by rfl⟩ : syracuseStep 242043 = 363065) B363065
theorem B242095 : Blo 239816 242095 := bstep (se 1 (by rfl) ⟨181571, by rfl⟩ : syracuseStep 242095 = 363143) B363143
theorem B242119 : Blo 239816 242119 := bstep (se 1 (by rfl) ⟨181589, by rfl⟩ : syracuseStep 242119 = 363179) B363179
theorem B242139 : Blo 239816 242139 := bstep (se 1 (by rfl) ⟨181604, by rfl⟩ : syracuseStep 242139 = 363209) B363209
theorem B242215 : Blo 239816 242215 := bstep (se 1 (by rfl) ⟨181661, by rfl⟩ : syracuseStep 242215 = 363323) B363323
theorem B406073 : Blo 239816 406073 := bstep (se 2 (by rfl) ⟨152277, by rfl⟩ : syracuseStep 406073 = 304555) B304555
theorem B242255 : Blo 239816 242255 := bstep (se 1 (by rfl) ⟨181691, by rfl⟩ : syracuseStep 242255 = 363383) B363383
theorem B242271 : Blo 239816 242271 := bstep (se 1 (by rfl) ⟨181703, by rfl⟩ : syracuseStep 242271 = 363407) B363407
theorem B242299 : Blo 239816 242299 := bstep (se 1 (by rfl) ⟨181724, by rfl⟩ : syracuseStep 242299 = 363449) B363449
theorem B242351 : Blo 239816 242351 := bstep (se 1 (by rfl) ⟨181763, by rfl⟩ : syracuseStep 242351 = 363527) B363527
theorem B242375 : Blo 239816 242375 := bstep (se 1 (by rfl) ⟨181781, by rfl⟩ : syracuseStep 242375 = 363563) B363563
theorem B242395 : Blo 239816 242395 := bstep (se 1 (by rfl) ⟨181796, by rfl⟩ : syracuseStep 242395 = 363593) B363593
theorem B9679621 : Blo 239816 9679621 := bstep (se 4 (by rfl) ⟨907464, by rfl⟩ : syracuseStep 9679621 = 1814929) B1814929
theorem B242471 : Blo 239816 242471 := bstep (se 1 (by rfl) ⟨181853, by rfl⟩ : syracuseStep 242471 = 363707) B363707
theorem B242511 : Blo 239816 242511 := bstep (se 1 (by rfl) ⟨181883, by rfl⟩ : syracuseStep 242511 = 363767) B363767
theorem B242527 : Blo 239816 242527 := bstep (se 1 (by rfl) ⟨181895, by rfl⟩ : syracuseStep 242527 = 363791) B363791
theorem B308063 : Blo 239816 308063 := bstep (se 1 (by rfl) ⟨231047, by rfl⟩ : syracuseStep 308063 = 462095) B462095
theorem B242555 : Blo 239816 242555 := bstep (se 1 (by rfl) ⟨181916, by rfl⟩ : syracuseStep 242555 = 363833) B363833
theorem B242607 : Blo 239816 242607 := bstep (se 1 (by rfl) ⟨181955, by rfl⟩ : syracuseStep 242607 = 363911) B363911
theorem B242631 : Blo 239816 242631 := bstep (se 1 (by rfl) ⟨181973, by rfl⟩ : syracuseStep 242631 = 363947) B363947
theorem B242651 : Blo 239816 242651 := bstep (se 1 (by rfl) ⟨181988, by rfl⟩ : syracuseStep 242651 = 363977) B363977
theorem B2765825 : Blo 239816 2765825 := bstep (se 2 (by rfl) ⟨1037184, by rfl⟩ : syracuseStep 2765825 = 2074369) B2074369
theorem B242727 : Blo 239816 242727 := bstep (se 1 (by rfl) ⟨182045, by rfl⟩ : syracuseStep 242727 = 364091) B364091
theorem B242767 : Blo 239816 242767 := bstep (se 1 (by rfl) ⟨182075, by rfl⟩ : syracuseStep 242767 = 364151) B364151
theorem B242783 : Blo 239816 242783 := bstep (se 1 (by rfl) ⟨182087, by rfl⟩ : syracuseStep 242783 = 364175) B364175
theorem B242811 : Blo 239816 242811 := bstep (se 1 (by rfl) ⟨182108, by rfl⟩ : syracuseStep 242811 = 364217) B364217
theorem B242863 : Blo 239816 242863 := bstep (se 1 (by rfl) ⟨182147, by rfl⟩ : syracuseStep 242863 = 364295) B364295
theorem B242887 : Blo 239816 242887 := bstep (se 1 (by rfl) ⟨182165, by rfl⟩ : syracuseStep 242887 = 364331) B364331
theorem B242907 : Blo 239816 242907 := bstep (se 1 (by rfl) ⟨182180, by rfl⟩ : syracuseStep 242907 = 364361) B364361
theorem B406775 : Blo 239816 406775 := bstep (se 1 (by rfl) ⟨305081, by rfl⟩ : syracuseStep 406775 = 610163) B610163
theorem B242983 : Blo 239816 242983 := bstep (se 1 (by rfl) ⟨182237, by rfl⟩ : syracuseStep 242983 = 364475) B364475
theorem B243023 : Blo 239816 243023 := bstep (se 1 (by rfl) ⟨182267, by rfl⟩ : syracuseStep 243023 = 364535) B364535
theorem B243039 : Blo 239816 243039 := bstep (se 1 (by rfl) ⟨182279, by rfl⟩ : syracuseStep 243039 = 364559) B364559
theorem B3093875 : Blo 239816 3093875 := bstep (se 1 (by rfl) ⟨2320406, by rfl⟩ : syracuseStep 3093875 = 4640813) B4640813
theorem B243067 : Blo 239816 243067 := bstep (se 1 (by rfl) ⟨182300, by rfl⟩ : syracuseStep 243067 = 364601) B364601
theorem B243119 : Blo 239816 243119 := bstep (se 1 (by rfl) ⟨182339, by rfl⟩ : syracuseStep 243119 = 364679) B364679
theorem B243143 : Blo 239816 243143 := bstep (se 1 (by rfl) ⟨182357, by rfl⟩ : syracuseStep 243143 = 364715) B364715
theorem B243163 : Blo 239816 243163 := bstep (se 1 (by rfl) ⟨182372, by rfl⟩ : syracuseStep 243163 = 364745) B364745
theorem B2635253 : Blo 239816 2635253 := bstep (se 5 (by rfl) ⟨123527, by rfl⟩ : syracuseStep 2635253 = 247055) B247055
theorem B767497 : Blo 239816 767497 := bstep (se 2 (by rfl) ⟨287811, by rfl⟩ : syracuseStep 767497 = 575623) B575623
theorem B243239 : Blo 239816 243239 := bstep (se 1 (by rfl) ⟨182429, by rfl⟩ : syracuseStep 243239 = 364859) B364859
theorem B407119 : Blo 239816 407119 := bstep (se 1 (by rfl) ⟨305339, by rfl⟩ : syracuseStep 407119 = 610679) B610679
theorem B243279 : Blo 239816 243279 := bstep (se 1 (by rfl) ⟨182459, by rfl⟩ : syracuseStep 243279 = 364919) B364919
theorem B243295 : Blo 239816 243295 := bstep (se 1 (by rfl) ⟨182471, by rfl⟩ : syracuseStep 243295 = 364943) B364943
theorem B243323 : Blo 239816 243323 := bstep (se 1 (by rfl) ⟨182492, by rfl⟩ : syracuseStep 243323 = 364985) B364985
theorem B243375 : Blo 239816 243375 := bstep (se 1 (by rfl) ⟨182531, by rfl⟩ : syracuseStep 243375 = 365063) B365063
theorem B243399 : Blo 239816 243399 := bstep (se 1 (by rfl) ⟨182549, by rfl⟩ : syracuseStep 243399 = 365099) B365099
theorem B243419 : Blo 239816 243419 := bstep (se 1 (by rfl) ⟨182564, by rfl⟩ : syracuseStep 243419 = 365129) B365129
theorem B243495 : Blo 239816 243495 := bstep (se 1 (by rfl) ⟨182621, by rfl⟩ : syracuseStep 243495 = 365243) B365243
theorem B3127099 : Blo 239816 3127099 := bstep (se 1 (by rfl) ⟨2345324, by rfl⟩ : syracuseStep 3127099 = 4690649) B4690649
theorem B407369 : Blo 239816 407369 := bstep (se 2 (by rfl) ⟨152763, by rfl⟩ : syracuseStep 407369 = 305527) B305527
theorem B243535 : Blo 239816 243535 := bstep (se 1 (by rfl) ⟨182651, by rfl⟩ : syracuseStep 243535 = 365303) B365303
theorem B243551 : Blo 239816 243551 := bstep (se 1 (by rfl) ⟨182663, by rfl⟩ : syracuseStep 243551 = 365327) B365327
theorem B341867 : Blo 239816 341867 := bstep (se 1 (by rfl) ⟨256400, by rfl⟩ : syracuseStep 341867 = 512801) B512801
theorem B243579 : Blo 239816 243579 := bstep (se 1 (by rfl) ⟨182684, by rfl⟩ : syracuseStep 243579 = 365369) B365369
theorem B243631 : Blo 239816 243631 := bstep (se 1 (by rfl) ⟨182723, by rfl⟩ : syracuseStep 243631 = 365447) B365447
theorem B243655 : Blo 239816 243655 := bstep (se 1 (by rfl) ⟨182741, by rfl⟩ : syracuseStep 243655 = 365483) B365483
theorem B243675 : Blo 239816 243675 := bstep (se 1 (by rfl) ⟨182756, by rfl⟩ : syracuseStep 243675 = 365513) B365513
theorem B243751 : Blo 239816 243751 := bstep (se 1 (by rfl) ⟨182813, by rfl⟩ : syracuseStep 243751 = 365627) B365627
theorem B243791 : Blo 239816 243791 := bstep (se 1 (by rfl) ⟨182843, by rfl⟩ : syracuseStep 243791 = 365687) B365687
theorem B243807 : Blo 239816 243807 := bstep (se 1 (by rfl) ⟨182855, by rfl⟩ : syracuseStep 243807 = 365711) B365711
theorem B1554547 : Blo 239816 1554547 := bstep (se 1 (by rfl) ⟨1165910, by rfl⟩ : syracuseStep 1554547 = 2331821) B2331821
theorem B407801 : Blo 239816 407801 := bstep (se 2 (by rfl) ⟨152925, by rfl⟩ : syracuseStep 407801 = 305851) B305851
theorem B5191937 : Blo 239816 5191937 := bstep (se 2 (by rfl) ⟨1946976, by rfl⟩ : syracuseStep 5191937 = 3893953) B3893953
theorem B833921 : Blo 239816 833921 := bstep (se 2 (by rfl) ⟨312720, by rfl⟩ : syracuseStep 833921 = 625441) B625441
theorem B407983 : Blo 239816 407983 := bstep (se 1 (by rfl) ⟨305987, by rfl⟩ : syracuseStep 407983 = 611975) B611975
theorem B768457 : Blo 239816 768457 := bstep (se 2 (by rfl) ⟨288171, by rfl⟩ : syracuseStep 768457 = 576343) B576343
theorem B408071 : Blo 239816 408071 := bstep (se 1 (by rfl) ⟨306053, by rfl⟩ : syracuseStep 408071 = 612107) B612107
theorem B1227473 : Blo 239816 1227473 := bstep (se 2 (by rfl) ⟨460302, by rfl⟩ : syracuseStep 1227473 = 920605) B920605
theorem B408415 : Blo 239816 408415 := bstep (se 1 (by rfl) ⟨306311, by rfl⟩ : syracuseStep 408415 = 612623) B612623
theorem B310123 : Blo 239816 310123 := bstep (se 1 (by rfl) ⟨232592, by rfl⟩ : syracuseStep 310123 = 465185) B465185
theorem B408503 : Blo 239816 408503 := bstep (se 1 (by rfl) ⟨306377, by rfl⟩ : syracuseStep 408503 = 612755) B612755
theorem B7846955 : Blo 239816 7846955 := bstep (se 1 (by rfl) ⟨5885216, by rfl⟩ : syracuseStep 7846955 = 11770433) B11770433
theorem B867385 : Blo 239816 867385 := bstep (se 2 (by rfl) ⟨325269, by rfl⟩ : syracuseStep 867385 = 650539) B650539
theorem B539819 : Blo 239816 539819 := bstep (se 1 (by rfl) ⟨404864, by rfl⟩ : syracuseStep 539819 = 809729) B809729
theorem B409097 : Blo 239816 409097 := bstep (se 2 (by rfl) ⟨153411, by rfl⟩ : syracuseStep 409097 = 306823) B306823
theorem B409259 : Blo 239816 409259 := bstep (se 1 (by rfl) ⟨306944, by rfl⟩ : syracuseStep 409259 = 613889) B613889
theorem B540359 : Blo 239816 540359 := bstep (se 1 (by rfl) ⟨405269, by rfl⟩ : syracuseStep 540359 = 810539) B810539
theorem B868205 : Blo 239816 868205 := bstep (se 3 (by rfl) ⟨162788, by rfl⟩ : syracuseStep 868205 = 325577) B325577
theorem B409657 : Blo 239816 409657 := bstep (se 2 (by rfl) ⟨153621, by rfl⟩ : syracuseStep 409657 = 307243) B307243
theorem B770201 : Blo 239816 770201 := bstep (se 2 (by rfl) ⟨288825, by rfl⟩ : syracuseStep 770201 = 577651) B577651
theorem B409799 : Blo 239816 409799 := bstep (se 1 (by rfl) ⟨307349, by rfl⟩ : syracuseStep 409799 = 614699) B614699
theorem B2015549 : Blo 239816 2015549 := bstep (se 3 (by rfl) ⟨377915, by rfl⟩ : syracuseStep 2015549 = 755831) B755831
theorem B409961 : Blo 239816 409961 := bstep (se 2 (by rfl) ⟨153735, by rfl⟩ : syracuseStep 409961 = 307471) B307471
theorem B311735 : Blo 239816 311735 := bstep (se 1 (by rfl) ⟨233801, by rfl⟩ : syracuseStep 311735 = 467603) B467603
theorem B2736665 : Blo 239816 2736665 := bstep (se 2 (by rfl) ⟨1026249, by rfl⟩ : syracuseStep 2736665 = 2052499) B2052499
theorem B868897 : Blo 239816 868897 := bstep (se 2 (by rfl) ⟨325836, by rfl⟩ : syracuseStep 868897 = 651673) B651673
theorem B541223 : Blo 239816 541223 := bstep (se 1 (by rfl) ⟨405917, by rfl⟩ : syracuseStep 541223 = 811835) B811835
theorem B14959235 : Blo 239816 14959235 := bstep (se 1 (by rfl) ⟨11219426, by rfl⟩ : syracuseStep 14959235 = 22438853) B22438853
theorem B410359 : Blo 239816 410359 := bstep (se 1 (by rfl) ⟨307769, by rfl⟩ : syracuseStep 410359 = 615539) B615539
theorem B541547 : Blo 239816 541547 := bstep (se 1 (by rfl) ⟨406160, by rfl⟩ : syracuseStep 541547 = 812321) B812321
theorem B443243 : Blo 239816 443243 := bstep (se 1 (by rfl) ⟨332432, by rfl⟩ : syracuseStep 443243 = 664865) B664865
theorem B541601 : Blo 239816 541601 := bstep (se 2 (by rfl) ⟨203100, by rfl⟩ : syracuseStep 541601 = 406201) B406201
theorem B410555 : Blo 239816 410555 := bstep (se 1 (by rfl) ⟨307916, by rfl⟩ : syracuseStep 410555 = 615833) B615833
theorem B410663 : Blo 239816 410663 := bstep (se 1 (by rfl) ⟨307997, by rfl⟩ : syracuseStep 410663 = 615995) B615995
theorem B1229903 : Blo 239816 1229903 := bstep (se 1 (by rfl) ⟨922427, by rfl⟩ : syracuseStep 1229903 = 1844855) B1844855
theorem B1557623 : Blo 239816 1557623 := bstep (se 1 (by rfl) ⟨1168217, by rfl⟩ : syracuseStep 1557623 = 2336435) B2336435
theorem B541943 : Blo 239816 541943 := bstep (se 1 (by rfl) ⟨406457, by rfl⟩ : syracuseStep 541943 = 812915) B812915
theorem B410953 : Blo 239816 410953 := bstep (se 2 (by rfl) ⟨154107, by rfl⟩ : syracuseStep 410953 = 308215) B308215
theorem B410987 : Blo 239816 410987 := bstep (se 1 (by rfl) ⟨308240, by rfl⟩ : syracuseStep 410987 = 616481) B616481
theorem B771457 : Blo 239816 771457 := bstep (se 2 (by rfl) ⟨289296, by rfl⟩ : syracuseStep 771457 = 578593) B578593
theorem B2967029 : Blo 239816 2967029 := bstep (se 5 (by rfl) ⟨139079, by rfl⟩ : syracuseStep 2967029 = 278159) B278159
theorem B607783 : Blo 239816 607783 := bstep (se 1 (by rfl) ⟨455837, by rfl⟩ : syracuseStep 607783 = 911675) B911675
theorem B1230551 : Blo 239816 1230551 := bstep (se 1 (by rfl) ⟨922913, by rfl⟩ : syracuseStep 1230551 = 1845827) B1845827
theorem B411385 : Blo 239816 411385 := bstep (se 2 (by rfl) ⟨154269, by rfl⟩ : syracuseStep 411385 = 308539) B308539
theorem B542537 : Blo 239816 542537 := bstep (se 2 (by rfl) ⟨203451, by rfl⟩ : syracuseStep 542537 = 406903) B406903
theorem B608107 : Blo 239816 608107 := bstep (se 1 (by rfl) ⟨456080, by rfl⟩ : syracuseStep 608107 = 912161) B912161
theorem B411895 : Blo 239816 411895 := bstep (se 1 (by rfl) ⟨308921, by rfl⟩ : syracuseStep 411895 = 617843) B617843
theorem B870743 : Blo 239816 870743 := bstep (se 1 (by rfl) ⟨653057, by rfl⟩ : syracuseStep 870743 = 1306115) B1306115
theorem B608755 : Blo 239816 608755 := bstep (se 1 (by rfl) ⟨456566, by rfl⟩ : syracuseStep 608755 = 913133) B913133
theorem B3983905 : Blo 239816 3983905 := bstep (se 2 (by rfl) ⟨1493964, by rfl⟩ : syracuseStep 3983905 = 2987929) B2987929
theorem B543329 : Blo 239816 543329 := bstep (se 2 (by rfl) ⟨203748, by rfl⟩ : syracuseStep 543329 = 407497) B407497
theorem B2771657 : Blo 239816 2771657 := bstep (se 2 (by rfl) ⟨1039371, by rfl⟩ : syracuseStep 2771657 = 2078743) B2078743
theorem B1952657 : Blo 239816 1952657 := bstep (se 2 (by rfl) ⟨732246, by rfl⟩ : syracuseStep 1952657 = 1464493) B1464493
theorem B1756079 : Blo 239816 1756079 := bstep (se 1 (by rfl) ⟨1317059, by rfl⟩ : syracuseStep 1756079 = 2634119) B2634119
theorem B543671 : Blo 239816 543671 := bstep (se 1 (by rfl) ⟨407753, by rfl⟩ : syracuseStep 543671 = 815507) B815507
theorem B2214839 : Blo 239816 2214839 := bstep (se 1 (by rfl) ⟨1661129, by rfl⟩ : syracuseStep 2214839 = 3322259) B3322259
theorem B2739581 : Blo 239816 2739581 := bstep (se 3 (by rfl) ⟨513671, by rfl⟩ : syracuseStep 2739581 = 1027343) B1027343
theorem B544265 : Blo 239816 544265 := bstep (se 2 (by rfl) ⟨204099, by rfl⟩ : syracuseStep 544265 = 408199) B408199
theorem B2346583 : Blo 239816 2346583 := bstep (se 1 (by rfl) ⟨1759937, by rfl⟩ : syracuseStep 2346583 = 3519875) B3519875
theorem B609889 : Blo 239816 609889 := bstep (se 2 (by rfl) ⟨228708, by rfl⟩ : syracuseStep 609889 = 457417) B457417
theorem B1166987 : Blo 239816 1166987 := bstep (se 1 (by rfl) ⟨875240, by rfl⟩ : syracuseStep 1166987 = 1750481) B1750481
theorem B544607 : Blo 239816 544607 := bstep (se 1 (by rfl) ⟨408455, by rfl⟩ : syracuseStep 544607 = 816911) B816911
theorem B315355 : Blo 239816 315355 := bstep (se 1 (by rfl) ⟨236516, by rfl⟩ : syracuseStep 315355 = 473033) B473033
theorem B8376331 : Blo 239816 8376331 := bstep (se 1 (by rfl) ⟨6282248, by rfl⟩ : syracuseStep 8376331 = 12564497) B12564497
theorem B544787 : Blo 239816 544787 := bstep (se 1 (by rfl) ⟨408590, by rfl⟩ : syracuseStep 544787 = 817181) B817181
theorem B774301 : Blo 239816 774301 := bstep (se 3 (by rfl) ⟨145181, by rfl⟩ : syracuseStep 774301 = 290363) B290363
theorem B545129 : Blo 239816 545129 := bstep (se 2 (by rfl) ⟨204423, by rfl⟩ : syracuseStep 545129 = 408847) B408847
theorem B610841 : Blo 239816 610841 := bstep (se 2 (by rfl) ⟨229065, by rfl⟩ : syracuseStep 610841 = 458131) B458131
theorem B872993 : Blo 239816 872993 := bstep (se 2 (by rfl) ⟨327372, by rfl⟩ : syracuseStep 872993 = 654745) B654745
theorem B1233467 : Blo 239816 1233467 := bstep (se 1 (by rfl) ⟨925100, by rfl⟩ : syracuseStep 1233467 = 1850201) B1850201
theorem B414407 : Blo 239816 414407 := bstep (se 1 (by rfl) ⟨310805, by rfl⟩ : syracuseStep 414407 = 621611) B621611
theorem B578411 : Blo 239816 578411 := bstep (se 1 (by rfl) ⟨433808, by rfl⟩ : syracuseStep 578411 = 867617) B867617
theorem B12342131 : Blo 239816 12342131 := bstep (se 1 (by rfl) ⟨9256598, by rfl⟩ : syracuseStep 12342131 = 18513197) B18513197
theorem B1168303 : Blo 239816 1168303 := bstep (se 1 (by rfl) ⟨876227, by rfl⟩ : syracuseStep 1168303 = 1752455) B1752455
theorem B545723 : Blo 239816 545723 := bstep (se 1 (by rfl) ⟨409292, by rfl⟩ : syracuseStep 545723 = 818585) B818585
theorem B611347 : Blo 239816 611347 := bstep (se 1 (by rfl) ⟨458510, by rfl⟩ : syracuseStep 611347 = 917021) B917021
theorem B3494963 : Blo 239816 3494963 := bstep (se 1 (by rfl) ⟨2621222, by rfl⟩ : syracuseStep 3494963 = 5242445) B5242445
theorem B545849 : Blo 239816 545849 := bstep (se 2 (by rfl) ⟨204693, by rfl⟩ : syracuseStep 545849 = 409387) B409387
theorem B1234115 : Blo 239816 1234115 := bstep (se 1 (by rfl) ⟨925586, by rfl⟩ : syracuseStep 1234115 = 1851173) B1851173
theorem B546191 : Blo 239816 546191 := bstep (se 1 (by rfl) ⟨409643, by rfl⟩ : syracuseStep 546191 = 819287) B819287
theorem B546515 : Blo 239816 546515 := bstep (se 1 (by rfl) ⟨409886, by rfl⟩ : syracuseStep 546515 = 819773) B819773
theorem B1955771 : Blo 239816 1955771 := bstep (se 1 (by rfl) ⟨1466828, by rfl⟩ : syracuseStep 1955771 = 2933657) B2933657
theorem B612431 : Blo 239816 612431 := bstep (se 1 (by rfl) ⟨459323, by rfl⟩ : syracuseStep 612431 = 918647) B918647
theorem B4446667 : Blo 239816 4446667 := bstep (se 1 (by rfl) ⟨3335000, by rfl⟩ : syracuseStep 4446667 = 6670001) B6670001
theorem B809459 : Blo 239816 809459 := bstep (se 1 (by rfl) ⟨607094, by rfl⟩ : syracuseStep 809459 = 1214189) B1214189
theorem B547451 : Blo 239816 547451 := bstep (se 1 (by rfl) ⟨410588, by rfl⟩ : syracuseStep 547451 = 821177) B821177
theorem B1825415 : Blo 239816 1825415 := bstep (se 1 (by rfl) ⟨1369061, by rfl⟩ : syracuseStep 1825415 = 2738123) B2738123
theorem B7101107 : Blo 239816 7101107 := bstep (se 1 (by rfl) ⟨5325830, by rfl⟩ : syracuseStep 7101107 = 10651661) B10651661
theorem B1366739 : Blo 239816 1366739 := bstep (se 1 (by rfl) ⟨1025054, by rfl⟩ : syracuseStep 1366739 = 2050109) B2050109
theorem B613079 : Blo 239816 613079 := bstep (se 1 (by rfl) ⟨459809, by rfl⟩ : syracuseStep 613079 = 919619) B919619
theorem B547577 : Blo 239816 547577 := bstep (se 2 (by rfl) ⟨205341, by rfl⟩ : syracuseStep 547577 = 410683) B410683
theorem B547847 : Blo 239816 547847 := bstep (se 1 (by rfl) ⟨410885, by rfl⟩ : syracuseStep 547847 = 821771) B821771
theorem B809999 : Blo 239816 809999 := bstep (se 1 (by rfl) ⟨607499, by rfl⟩ : syracuseStep 809999 = 1214999) B1214999
theorem B3333143 : Blo 239816 3333143 := bstep (se 1 (by rfl) ⟨2499857, by rfl⟩ : syracuseStep 3333143 = 4999715) B4999715
theorem B613433 : Blo 239816 613433 := bstep (se 2 (by rfl) ⟨230037, by rfl⟩ : syracuseStep 613433 = 460075) B460075
theorem B547919 : Blo 239816 547919 := bstep (se 1 (by rfl) ⟨410939, by rfl⟩ : syracuseStep 547919 = 821879) B821879
theorem B1039817 : Blo 239816 1039817 := bstep (se 2 (by rfl) ⟨389931, by rfl⟩ : syracuseStep 1039817 = 779863) B779863
theorem B548315 : Blo 239816 548315 := bstep (se 1 (by rfl) ⟨411236, by rfl⟩ : syracuseStep 548315 = 822473) B822473
theorem B810593 : Blo 239816 810593 := bstep (se 2 (by rfl) ⟨303972, by rfl⟩ : syracuseStep 810593 = 607945) B607945
theorem B515783 : Blo 239816 515783 := bstep (se 1 (by rfl) ⟨386837, by rfl⟩ : syracuseStep 515783 = 773675) B773675
theorem B1957613 : Blo 239816 1957613 := bstep (se 3 (by rfl) ⟨367052, by rfl⟩ : syracuseStep 1957613 = 734105) B734105
theorem B876395 : Blo 239816 876395 := bstep (se 1 (by rfl) ⟨657296, by rfl⟩ : syracuseStep 876395 = 1314593) B1314593
theorem B1826873 : Blo 239816 1826873 := bstep (se 2 (by rfl) ⟨685077, by rfl⟩ : syracuseStep 1826873 = 1370155) B1370155
theorem B1040465 : Blo 239816 1040465 := bstep (se 2 (by rfl) ⟨390174, by rfl⟩ : syracuseStep 1040465 = 780349) B780349
theorem B975341 : Blo 239816 975341 := bstep (se 3 (by rfl) ⟨182876, by rfl⟩ : syracuseStep 975341 = 365753) B365753
theorem B778967 : Blo 239816 778967 := bstep (se 1 (by rfl) ⟨584225, by rfl⟩ : syracuseStep 778967 = 1168451) B1168451
theorem B812051 : Blo 239816 812051 := bstep (se 1 (by rfl) ⟨609038, by rfl⟩ : syracuseStep 812051 = 1218077) B1218077
theorem B615671 : Blo 239816 615671 := bstep (se 1 (by rfl) ⟨461753, by rfl⟩ : syracuseStep 615671 = 923507) B923507
theorem B812375 : Blo 239816 812375 := bstep (se 1 (by rfl) ⟨609281, by rfl⟩ : syracuseStep 812375 = 1218563) B1218563
theorem B583379 : Blo 239816 583379 := bstep (se 1 (by rfl) ⟨437534, by rfl⟩ : syracuseStep 583379 = 875069) B875069
theorem B1730413 : Blo 239816 1730413 := bstep (se 3 (by rfl) ⟨324452, by rfl⟩ : syracuseStep 1730413 = 648905) B648905
theorem B386959 : Blo 239816 386959 := bstep (se 1 (by rfl) ⟨290219, by rfl⟩ : syracuseStep 386959 = 580439) B580439
theorem B1828817 : Blo 239816 1828817 := bstep (se 2 (by rfl) ⟨685806, by rfl⟩ : syracuseStep 1828817 = 1371613) B1371613
theorem B1108025 : Blo 239816 1108025 := bstep (se 2 (by rfl) ⟨415509, by rfl⟩ : syracuseStep 1108025 = 831019) B831019
theorem B1370429 : Blo 239816 1370429 := bstep (se 3 (by rfl) ⟨256955, by rfl⟩ : syracuseStep 1370429 = 513911) B513911
theorem B387433 : Blo 239816 387433 := bstep (se 2 (by rfl) ⟨145287, by rfl⟩ : syracuseStep 387433 = 290575) B290575
theorem B813455 : Blo 239816 813455 := bstep (se 1 (by rfl) ⟨610091, by rfl⟩ : syracuseStep 813455 = 1220183) B1220183
theorem B617159 : Blo 239816 617159 := bstep (se 1 (by rfl) ⟨462869, by rfl⟩ : syracuseStep 617159 = 925739) B925739
theorem B813779 : Blo 239816 813779 := bstep (se 1 (by rfl) ⟨610334, by rfl⟩ : syracuseStep 813779 = 1220669) B1220669
theorem B683255 : Blo 239816 683255 := bstep (se 1 (by rfl) ⟨512441, by rfl⟩ : syracuseStep 683255 = 1024883) B1024883
theorem B978419 : Blo 239816 978419 := bstep (se 1 (by rfl) ⟨733814, by rfl⟩ : syracuseStep 978419 = 1467629) B1467629
theorem B1044065 : Blo 239816 1044065 := bstep (se 2 (by rfl) ⟨391524, by rfl⟩ : syracuseStep 1044065 = 783049) B783049
theorem B814967 : Blo 239816 814967 := bstep (se 1 (by rfl) ⟨611225, by rfl⟩ : syracuseStep 814967 = 1222451) B1222451
theorem B585647 : Blo 239816 585647 := bstep (se 1 (by rfl) ⟨439235, by rfl⟩ : syracuseStep 585647 = 878471) B878471
theorem B389047 : Blo 239816 389047 := bstep (se 1 (by rfl) ⟨291785, by rfl⟩ : syracuseStep 389047 = 583571) B583571
theorem B520199 : Blo 239816 520199 := bstep (se 1 (by rfl) ⟨390149, by rfl⟩ : syracuseStep 520199 = 780299) B780299
theorem B815183 : Blo 239816 815183 := bstep (se 1 (by rfl) ⟨611387, by rfl⟩ : syracuseStep 815183 = 1222775) B1222775
theorem B1732697 : Blo 239816 1732697 := bstep (se 2 (by rfl) ⟨649761, by rfl⟩ : syracuseStep 1732697 = 1299523) B1299523
theorem B815561 : Blo 239816 815561 := bstep (se 2 (by rfl) ⟨305835, by rfl⟩ : syracuseStep 815561 = 611671) B611671
theorem B455291 : Blo 239816 455291 := bstep (se 1 (by rfl) ⟨341468, by rfl⟩ : syracuseStep 455291 = 682937) B682937
theorem B914105 : Blo 239816 914105 := bstep (se 2 (by rfl) ⟨342789, by rfl⟩ : syracuseStep 914105 = 685579) B685579
theorem B815831 : Blo 239816 815831 := bstep (se 1 (by rfl) ⟨611873, by rfl⟩ : syracuseStep 815831 = 1223747) B1223747
theorem B7893773 : Blo 239816 7893773 := bstep (se 3 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 7893773 = 2960165) B2960165
theorem B455519 : Blo 239816 455519 := bstep (se 1 (by rfl) ⟨341639, by rfl⟩ : syracuseStep 455519 = 683279) B683279
theorem B816047 : Blo 239816 816047 := bstep (se 1 (by rfl) ⟨612035, by rfl⟩ : syracuseStep 816047 = 1224071) B1224071
theorem B2814977 : Blo 239816 2814977 := bstep (se 2 (by rfl) ⟨1055616, by rfl⟩ : syracuseStep 2814977 = 2111233) B2111233
theorem B455777 : Blo 239816 455777 := bstep (se 2 (by rfl) ⟨170916, by rfl⟩ : syracuseStep 455777 = 341833) B341833
theorem B2323673 : Blo 239816 2323673 := bstep (se 2 (by rfl) ⟨871377, by rfl⟩ : syracuseStep 2323673 = 1742755) B1742755
theorem B456043 : Blo 239816 456043 := bstep (se 1 (by rfl) ⟨342032, by rfl⟩ : syracuseStep 456043 = 684065) B684065
theorem B3536243 : Blo 239816 3536243 := bstep (se 1 (by rfl) ⟨2652182, by rfl⟩ : syracuseStep 3536243 = 5304365) B5304365
theorem B3339667 : Blo 239816 3339667 := bstep (se 1 (by rfl) ⟨2504750, by rfl⟩ : syracuseStep 3339667 = 5009501) B5009501
theorem B783881 : Blo 239816 783881 := bstep (se 2 (by rfl) ⟨293955, by rfl⟩ : syracuseStep 783881 = 587911) B587911
theorem B260219 : Blo 239816 260219 := bstep (se 1 (by rfl) ⟨195164, by rfl⟩ : syracuseStep 260219 = 390329) B390329
theorem B457235 : Blo 239816 457235 := bstep (se 1 (by rfl) ⟨342926, by rfl⟩ : syracuseStep 457235 = 685853) B685853
theorem B457463 : Blo 239816 457463 := bstep (se 1 (by rfl) ⟨343097, by rfl⟩ : syracuseStep 457463 = 686195) B686195
theorem B916217 : Blo 239816 916217 := bstep (se 2 (by rfl) ⟨343581, by rfl⟩ : syracuseStep 916217 = 687163) B687163
theorem B981827 : Blo 239816 981827 := bstep (se 1 (by rfl) ⟨736370, by rfl⟩ : syracuseStep 981827 = 1472741) B1472741
theorem B490313 : Blo 239816 490313 := bstep (se 2 (by rfl) ⟨183867, by rfl⟩ : syracuseStep 490313 = 367735) B367735
theorem B654355 : Blo 239816 654355 := bstep (se 1 (by rfl) ⟨490766, by rfl⟩ : syracuseStep 654355 = 981533) B981533
theorem B1015031 : Blo 239816 1015031 := bstep (se 1 (by rfl) ⟨761273, by rfl⟩ : syracuseStep 1015031 = 1522547) B1522547
theorem B5242103 : Blo 239816 5242103 := bstep (se 1 (by rfl) ⟨3931577, by rfl⟩ : syracuseStep 5242103 = 7863155) B7863155
theorem B818423 : Blo 239816 818423 := bstep (se 1 (by rfl) ⟨613817, by rfl⟩ : syracuseStep 818423 = 1227635) B1227635
theorem B359855 : Blo 239816 359855 := bstep (se 1 (by rfl) ⟨269891, by rfl⟩ : syracuseStep 359855 = 539783) B539783
theorem B359945 : Blo 239816 359945 := bstep (se 2 (by rfl) ⟨134979, by rfl⟩ : syracuseStep 359945 = 269959) B269959
theorem B359975 : Blo 239816 359975 := bstep (se 1 (by rfl) ⟨269981, by rfl⟩ : syracuseStep 359975 = 539963) B539963
theorem B818747 : Blo 239816 818747 := bstep (se 1 (by rfl) ⟨614060, by rfl⟩ : syracuseStep 818747 = 1228121) B1228121
theorem B360059 : Blo 239816 360059 := bstep (se 1 (by rfl) ⟨270044, by rfl⟩ : syracuseStep 360059 = 540089) B540089
theorem B917203 : Blo 239816 917203 := bstep (se 1 (by rfl) ⟨687902, by rfl⟩ : syracuseStep 917203 = 1375805) B1375805
theorem B360185 : Blo 239816 360185 := bstep (se 2 (by rfl) ⟨135069, by rfl⟩ : syracuseStep 360185 = 270139) B270139
theorem B819017 : Blo 239816 819017 := bstep (se 2 (by rfl) ⟨307131, by rfl⟩ : syracuseStep 819017 = 614263) B614263
theorem B360287 : Blo 239816 360287 := bstep (se 1 (by rfl) ⟨270215, by rfl⟩ : syracuseStep 360287 = 540431) B540431
theorem B360299 : Blo 239816 360299 := bstep (se 1 (by rfl) ⟨270224, by rfl⟩ : syracuseStep 360299 = 540449) B540449
theorem B1343699 : Blo 239816 1343699 := bstep (se 1 (by rfl) ⟨1007774, by rfl⟩ : syracuseStep 1343699 = 2015549) B2015549
theorem B360713 : Blo 239816 360713 := bstep (se 2 (by rfl) ⟨135267, by rfl⟩ : syracuseStep 360713 = 270535) B270535
theorem B360815 : Blo 239816 360815 := bstep (se 1 (by rfl) ⟨270611, by rfl⟩ : syracuseStep 360815 = 541223) B541223
theorem B361031 : Blo 239816 361031 := bstep (se 1 (by rfl) ⟨270773, by rfl⟩ : syracuseStep 361031 = 541547) B541547
theorem B295495 : Blo 239816 295495 := bstep (se 1 (by rfl) ⟨221621, by rfl⟩ : syracuseStep 295495 = 443243) B443243
theorem B361067 : Blo 239816 361067 := bstep (se 1 (by rfl) ⟨270800, by rfl⟩ : syracuseStep 361067 = 541601) B541601
theorem B1966763 : Blo 239816 1966763 := bstep (se 1 (by rfl) ⟨1475072, by rfl⟩ : syracuseStep 1966763 = 2950145) B2950145
theorem B819935 : Blo 239816 819935 := bstep (se 1 (by rfl) ⟨614951, by rfl⟩ : syracuseStep 819935 = 1229903) B1229903
theorem B5604173 : Blo 239816 5604173 := bstep (se 3 (by rfl) ⟨1050782, by rfl⟩ : syracuseStep 5604173 = 2101565) B2101565
theorem B361295 : Blo 239816 361295 := bstep (se 1 (by rfl) ⟨270971, by rfl⟩ : syracuseStep 361295 = 541943) B541943
theorem B3474323 : Blo 239816 3474323 := bstep (se 1 (by rfl) ⟨2605742, by rfl⟩ : syracuseStep 3474323 = 5211485) B5211485
theorem B820367 : Blo 239816 820367 := bstep (se 1 (by rfl) ⟨615275, by rfl⟩ : syracuseStep 820367 = 1230551) B1230551
theorem B361691 : Blo 239816 361691 := bstep (se 1 (by rfl) ⟨271268, by rfl⟩ : syracuseStep 361691 = 542537) B542537
theorem B1017193 : Blo 239816 1017193 := bstep (se 2 (by rfl) ⟨381447, by rfl⟩ : syracuseStep 1017193 = 762895) B762895
theorem B361865 : Blo 239816 361865 := bstep (se 2 (by rfl) ⟨135699, by rfl⟩ : syracuseStep 361865 = 271399) B271399
theorem B362219 : Blo 239816 362219 := bstep (se 1 (by rfl) ⟨271664, by rfl⟩ : syracuseStep 362219 = 543329) B543329
theorem B362447 : Blo 239816 362447 := bstep (se 1 (by rfl) ⟨271835, by rfl⟩ : syracuseStep 362447 = 543671) B543671
theorem B1476559 : Blo 239816 1476559 := bstep (se 1 (by rfl) ⟨1107419, by rfl⟩ : syracuseStep 1476559 = 2214839) B2214839
theorem B821501 : Blo 239816 821501 := bstep (se 3 (by rfl) ⟨154031, by rfl⟩ : syracuseStep 821501 = 308063) B308063
theorem B362843 : Blo 239816 362843 := bstep (se 1 (by rfl) ⟨272132, by rfl⟩ : syracuseStep 362843 = 544265) B544265
theorem B4098437 : Blo 239816 4098437 := bstep (se 4 (by rfl) ⟨384228, by rfl⟩ : syracuseStep 4098437 = 768457) B768457
theorem B363071 : Blo 239816 363071 := bstep (se 1 (by rfl) ⟨272303, by rfl⟩ : syracuseStep 363071 = 544607) B544607
theorem B363191 : Blo 239816 363191 := bstep (se 1 (by rfl) ⟨272393, by rfl⟩ : syracuseStep 363191 = 544787) B544787
theorem B2329361 : Blo 239816 2329361 := bstep (se 2 (by rfl) ⟨873510, by rfl⟩ : syracuseStep 2329361 = 1747021) B1747021
theorem B363419 : Blo 239816 363419 := bstep (se 1 (by rfl) ⟨272564, by rfl⟩ : syracuseStep 363419 = 545129) B545129
theorem B822311 : Blo 239816 822311 := bstep (se 1 (by rfl) ⟨616733, by rfl⟩ : syracuseStep 822311 = 1233467) B1233467
theorem B8228087 : Blo 239816 8228087 := bstep (se 1 (by rfl) ⟨6171065, by rfl⟩ : syracuseStep 8228087 = 12342131) B12342131
theorem B363815 : Blo 239816 363815 := bstep (se 1 (by rfl) ⟨272861, by rfl⟩ : syracuseStep 363815 = 545723) B545723
theorem B2329975 : Blo 239816 2329975 := bstep (se 1 (by rfl) ⟨1747481, by rfl⟩ : syracuseStep 2329975 = 3494963) B3494963
theorem B363899 : Blo 239816 363899 := bstep (se 1 (by rfl) ⟨272924, by rfl⟩ : syracuseStep 363899 = 545849) B545849
theorem B5311873 : Blo 239816 5311873 := bstep (se 2 (by rfl) ⟨1991952, by rfl⟩ : syracuseStep 5311873 = 3983905) B3983905
theorem B822743 : Blo 239816 822743 := bstep (se 1 (by rfl) ⟨617057, by rfl⟩ : syracuseStep 822743 = 1234115) B1234115
theorem B364025 : Blo 239816 364025 := bstep (se 2 (by rfl) ⟨136509, by rfl⟩ : syracuseStep 364025 = 273019) B273019
theorem B396895 : Blo 239816 396895 := bstep (se 1 (by rfl) ⟨297671, by rfl⟩ : syracuseStep 396895 = 595343) B595343
theorem B364127 : Blo 239816 364127 := bstep (se 1 (by rfl) ⟨273095, by rfl⟩ : syracuseStep 364127 = 546191) B546191
theorem B364343 : Blo 239816 364343 := bstep (se 1 (by rfl) ⟨273257, by rfl⟩ : syracuseStep 364343 = 546515) B546515
theorem B364649 : Blo 239816 364649 := bstep (se 2 (by rfl) ⟨136743, by rfl⟩ : syracuseStep 364649 = 273487) B273487
theorem B1315025 : Blo 239816 1315025 := bstep (se 2 (by rfl) ⟨493134, by rfl⟩ : syracuseStep 1315025 = 986269) B986269
theorem B364967 : Blo 239816 364967 := bstep (se 1 (by rfl) ⟨273725, by rfl⟩ : syracuseStep 364967 = 547451) B547451
theorem B1216943 : Blo 239816 1216943 := bstep (se 1 (by rfl) ⟨912707, by rfl⟩ : syracuseStep 1216943 = 1825415) B1825415
theorem B365051 : Blo 239816 365051 := bstep (se 1 (by rfl) ⟨273788, by rfl⟩ : syracuseStep 365051 = 547577) B547577
theorem B365177 : Blo 239816 365177 := bstep (se 2 (by rfl) ⟨136941, by rfl⟩ : syracuseStep 365177 = 273883) B273883
theorem B365231 : Blo 239816 365231 := bstep (se 1 (by rfl) ⟨273923, by rfl⟩ : syracuseStep 365231 = 547847) B547847
theorem B365279 : Blo 239816 365279 := bstep (se 1 (by rfl) ⟨273959, by rfl⟩ : syracuseStep 365279 = 547919) B547919
theorem B660215 : Blo 239816 660215 := bstep (se 1 (by rfl) ⟨495161, by rfl⟩ : syracuseStep 660215 = 990323) B990323
theorem B2626505 : Blo 239816 2626505 := bstep (se 2 (by rfl) ⟨984939, by rfl⟩ : syracuseStep 2626505 = 1969879) B1969879
theorem B693211 : Blo 239816 693211 := bstep (se 1 (by rfl) ⟨519908, by rfl⟩ : syracuseStep 693211 = 1039817) B1039817
theorem B365543 : Blo 239816 365543 := bstep (se 1 (by rfl) ⟨274157, by rfl⟩ : syracuseStep 365543 = 548315) B548315
theorem B922823 : Blo 239816 922823 := bstep (se 1 (by rfl) ⟨692117, by rfl⟩ : syracuseStep 922823 = 1384235) B1384235
theorem B1217915 : Blo 239816 1217915 := bstep (se 1 (by rfl) ⟨913436, by rfl⟩ : syracuseStep 1217915 = 1826873) B1826873
theorem B693917 : Blo 239816 693917 := bstep (se 3 (by rfl) ⟨130109, by rfl⟩ : syracuseStep 693917 = 260219) B260219
theorem B1219211 : Blo 239816 1219211 := bstep (se 1 (by rfl) ⟨914408, by rfl⟩ : syracuseStep 1219211 = 1828817) B1828817
theorem B1841939 : Blo 239816 1841939 := bstep (se 1 (by rfl) ⟨1381454, by rfl⟩ : syracuseStep 1841939 = 2762909) B2762909
theorem B1023329 : Blo 239816 1023329 := bstep (se 2 (by rfl) ⟨383748, by rfl⟩ : syracuseStep 1023329 = 767497) B767497
theorem B269887 : Blo 239816 269887 := bstep (se 1 (by rfl) ⟨202415, by rfl⟩ : syracuseStep 269887 = 404831) B404831
theorem B696043 : Blo 239816 696043 := bstep (se 1 (by rfl) ⟨522032, by rfl⟩ : syracuseStep 696043 = 1044065) B1044065
theorem B4169465 : Blo 239816 4169465 := bstep (se 2 (by rfl) ⟨1563549, by rfl⟩ : syracuseStep 4169465 = 3127099) B3127099
theorem B925451 : Blo 239816 925451 := bstep (se 1 (by rfl) ⟨694088, by rfl⟩ : syracuseStep 925451 = 1388177) B1388177
theorem B1155131 : Blo 239816 1155131 := bstep (se 1 (by rfl) ⟨866348, by rfl⟩ : syracuseStep 1155131 = 1732697) B1732697
theorem B2072729 : Blo 239816 2072729 := bstep (se 2 (by rfl) ⟨777273, by rfl⟩ : syracuseStep 2072729 = 1554547) B1554547
theorem B270715 : Blo 239816 270715 := bstep (se 1 (by rfl) ⟨203036, by rfl⟩ : syracuseStep 270715 = 406073) B406073
theorem B303527 : Blo 239816 303527 := bstep (se 1 (by rfl) ⟨227645, by rfl⟩ : syracuseStep 303527 = 455291) B455291
theorem B303679 : Blo 239816 303679 := bstep (se 1 (by rfl) ⟨227759, by rfl⟩ : syracuseStep 303679 = 455519) B455519
theorem B1843883 : Blo 239816 1843883 := bstep (se 1 (by rfl) ⟨1382912, by rfl⟩ : syracuseStep 1843883 = 2765825) B2765825
theorem B1876651 : Blo 239816 1876651 := bstep (se 1 (by rfl) ⟨1407488, by rfl⟩ : syracuseStep 1876651 = 2814977) B2814977
theorem B303851 : Blo 239816 303851 := bstep (se 1 (by rfl) ⟨227888, by rfl⟩ : syracuseStep 303851 = 455777) B455777
theorem B1549115 : Blo 239816 1549115 := bstep (se 1 (by rfl) ⟨1161836, by rfl⟩ : syracuseStep 1549115 = 2323673) B2323673
theorem B271183 : Blo 239816 271183 := bstep (se 1 (by rfl) ⟨203387, by rfl⟩ : syracuseStep 271183 = 406775) B406775
theorem B271579 : Blo 239816 271579 := bstep (se 1 (by rfl) ⟨203684, by rfl⟩ : syracuseStep 271579 = 407369) B407369
theorem B1156513 : Blo 239816 1156513 := bstep (se 2 (by rfl) ⟨433692, by rfl⟩ : syracuseStep 1156513 = 867385) B867385
theorem B271867 : Blo 239816 271867 := bstep (se 1 (by rfl) ⟨203900, by rfl⟩ : syracuseStep 271867 = 407801) B407801
theorem B272047 : Blo 239816 272047 := bstep (se 1 (by rfl) ⟨204035, by rfl⟩ : syracuseStep 272047 = 408071) B408071
theorem B304823 : Blo 239816 304823 := bstep (se 1 (by rfl) ⟨228617, by rfl⟩ : syracuseStep 304823 = 457235) B457235
theorem B304975 : Blo 239816 304975 := bstep (se 1 (by rfl) ⟨228731, by rfl⟩ : syracuseStep 304975 = 457463) B457463
theorem B5220301 : Blo 239816 5220301 := bstep (se 3 (by rfl) ⟨978806, by rfl⟩ : syracuseStep 5220301 = 1957613) B1957613
theorem B272335 : Blo 239816 272335 := bstep (se 1 (by rfl) ⟨204251, by rfl⟩ : syracuseStep 272335 = 408503) B408503
theorem B1222937 : Blo 239816 1222937 := bstep (se 2 (by rfl) ⟨458601, by rfl⟩ : syracuseStep 1222937 = 917203) B917203
theorem B239903 : Blo 239816 239903 := bstep (se 1 (by rfl) ⟨179927, by rfl⟩ : syracuseStep 239903 = 359855) B359855
theorem B239963 : Blo 239816 239963 := bstep (se 1 (by rfl) ⟨179972, by rfl⟩ : syracuseStep 239963 = 359945) B359945
theorem B272731 : Blo 239816 272731 := bstep (se 1 (by rfl) ⟨204548, by rfl⟩ : syracuseStep 272731 = 409097) B409097
theorem B239983 : Blo 239816 239983 := bstep (se 1 (by rfl) ⟨179987, by rfl⟩ : syracuseStep 239983 = 359975) B359975
theorem B240039 : Blo 239816 240039 := bstep (se 1 (by rfl) ⟨180029, by rfl⟩ : syracuseStep 240039 = 360059) B360059
theorem B272839 : Blo 239816 272839 := bstep (se 1 (by rfl) ⟨204629, by rfl⟩ : syracuseStep 272839 = 409259) B409259
theorem B240123 : Blo 239816 240123 := bstep (se 1 (by rfl) ⟨180092, by rfl⟩ : syracuseStep 240123 = 360185) B360185
theorem B240191 : Blo 239816 240191 := bstep (se 1 (by rfl) ⟨180143, by rfl⟩ : syracuseStep 240191 = 360287) B360287
theorem B240199 : Blo 239816 240199 := bstep (se 1 (by rfl) ⟨180149, by rfl⟩ : syracuseStep 240199 = 360299) B360299
theorem B240351 : Blo 239816 240351 := bstep (se 1 (by rfl) ⟨180263, by rfl⟩ : syracuseStep 240351 = 360527) B360527
theorem B240431 : Blo 239816 240431 := bstep (se 1 (by rfl) ⟨180323, by rfl⟩ : syracuseStep 240431 = 360647) B360647
theorem B273199 : Blo 239816 273199 := bstep (se 1 (by rfl) ⟨204899, by rfl⟩ : syracuseStep 273199 = 409799) B409799
theorem B240539 : Blo 239816 240539 := bstep (se 1 (by rfl) ⟨180404, by rfl⟩ : syracuseStep 240539 = 360809) B360809
theorem B273307 : Blo 239816 273307 := bstep (se 1 (by rfl) ⟨204980, by rfl⟩ : syracuseStep 273307 = 409961) B409961
theorem B240591 : Blo 239816 240591 := bstep (se 1 (by rfl) ⟨180443, by rfl⟩ : syracuseStep 240591 = 360887) B360887
theorem B240615 : Blo 239816 240615 := bstep (se 1 (by rfl) ⟨180461, by rfl⟩ : syracuseStep 240615 = 360923) B360923
theorem B9972823 : Blo 239816 9972823 := bstep (se 1 (by rfl) ⟨7479617, by rfl⟩ : syracuseStep 9972823 = 14959235) B14959235
theorem B5024987 : Blo 239816 5024987 := bstep (se 1 (by rfl) ⟨3768740, by rfl⟩ : syracuseStep 5024987 = 7537481) B7537481
theorem B2600207 : Blo 239816 2600207 := bstep (se 1 (by rfl) ⟨1950155, by rfl⟩ : syracuseStep 2600207 = 3900311) B3900311
theorem B240927 : Blo 239816 240927 := bstep (se 1 (by rfl) ⟨180695, by rfl⟩ : syracuseStep 240927 = 361391) B361391
theorem B273703 : Blo 239816 273703 := bstep (se 1 (by rfl) ⟨205277, by rfl⟩ : syracuseStep 273703 = 410555) B410555
theorem B240987 : Blo 239816 240987 := bstep (se 1 (by rfl) ⟨180740, by rfl⟩ : syracuseStep 240987 = 361481) B361481
theorem B241007 : Blo 239816 241007 := bstep (se 1 (by rfl) ⟨180755, by rfl⟩ : syracuseStep 241007 = 361511) B361511
theorem B273775 : Blo 239816 273775 := bstep (se 1 (by rfl) ⟨205331, by rfl⟩ : syracuseStep 273775 = 410663) B410663
theorem B241063 : Blo 239816 241063 := bstep (se 1 (by rfl) ⟨180797, by rfl⟩ : syracuseStep 241063 = 361595) B361595
theorem B241147 : Blo 239816 241147 := bstep (se 1 (by rfl) ⟨180860, by rfl⟩ : syracuseStep 241147 = 361721) B361721
theorem B241215 : Blo 239816 241215 := bstep (se 1 (by rfl) ⟨180911, by rfl⟩ : syracuseStep 241215 = 361823) B361823
theorem B241223 : Blo 239816 241223 := bstep (se 1 (by rfl) ⟨180917, by rfl⟩ : syracuseStep 241223 = 361835) B361835
theorem B273991 : Blo 239816 273991 := bstep (se 1 (by rfl) ⟨205493, by rfl⟩ : syracuseStep 273991 = 410987) B410987
theorem B1978019 : Blo 239816 1978019 := bstep (se 1 (by rfl) ⟨1483514, by rfl⟩ : syracuseStep 1978019 = 2967029) B2967029
theorem B241375 : Blo 239816 241375 := bstep (se 1 (by rfl) ⟨181031, by rfl⟩ : syracuseStep 241375 = 362063) B362063
theorem B241455 : Blo 239816 241455 := bstep (se 1 (by rfl) ⟨181091, by rfl⟩ : syracuseStep 241455 = 362183) B362183
theorem B831293 : Blo 239816 831293 := bstep (se 3 (by rfl) ⟨155867, by rfl⟩ : syracuseStep 831293 = 311735) B311735
theorem B241563 : Blo 239816 241563 := bstep (se 1 (by rfl) ⟨181172, by rfl⟩ : syracuseStep 241563 = 362345) B362345
theorem B1159069 : Blo 239816 1159069 := bstep (se 3 (by rfl) ⟨217325, by rfl⟩ : syracuseStep 1159069 = 434651) B434651
theorem B7450555 : Blo 239816 7450555 := bstep (se 1 (by rfl) ⟨5587916, by rfl⟩ : syracuseStep 7450555 = 11175833) B11175833
theorem B241615 : Blo 239816 241615 := bstep (se 1 (by rfl) ⟨181211, by rfl⟩ : syracuseStep 241615 = 362423) B362423
theorem B241639 : Blo 239816 241639 := bstep (se 1 (by rfl) ⟨181229, by rfl⟩ : syracuseStep 241639 = 362459) B362459
theorem B405769 : Blo 239816 405769 := bstep (se 2 (by rfl) ⟨152163, by rfl⟩ : syracuseStep 405769 = 304327) B304327
theorem B241951 : Blo 239816 241951 := bstep (se 1 (by rfl) ⟨181463, by rfl⟩ : syracuseStep 241951 = 362927) B362927
theorem B242011 : Blo 239816 242011 := bstep (se 1 (by rfl) ⟨181508, by rfl⟩ : syracuseStep 242011 = 363017) B363017
theorem B242031 : Blo 239816 242031 := bstep (se 1 (by rfl) ⟨181523, by rfl⟩ : syracuseStep 242031 = 363047) B363047
theorem B307567 : Blo 239816 307567 := bstep (se 1 (by rfl) ⟨230675, by rfl⟩ : syracuseStep 307567 = 461351) B461351
theorem B242087 : Blo 239816 242087 := bstep (se 1 (by rfl) ⟨181565, by rfl⟩ : syracuseStep 242087 = 363131) B363131
theorem B2077103 : Blo 239816 2077103 := bstep (se 1 (by rfl) ⟨1557827, by rfl⟩ : syracuseStep 2077103 = 3115655) B3115655
theorem B1847771 : Blo 239816 1847771 := bstep (se 1 (by rfl) ⟨1385828, by rfl⟩ : syracuseStep 1847771 = 2771657) B2771657
theorem B242171 : Blo 239816 242171 := bstep (se 1 (by rfl) ⟨181628, by rfl⟩ : syracuseStep 242171 = 363257) B363257
theorem B1028609 : Blo 239816 1028609 := bstep (se 2 (by rfl) ⟨385728, by rfl⟩ : syracuseStep 1028609 = 771457) B771457
theorem B242239 : Blo 239816 242239 := bstep (se 1 (by rfl) ⟨181679, by rfl⟩ : syracuseStep 242239 = 363359) B363359
theorem B242247 : Blo 239816 242247 := bstep (se 1 (by rfl) ⟨181685, by rfl⟩ : syracuseStep 242247 = 363371) B363371
theorem B242399 : Blo 239816 242399 := bstep (se 1 (by rfl) ⟨181799, by rfl⟩ : syracuseStep 242399 = 363599) B363599
theorem B242479 : Blo 239816 242479 := bstep (se 1 (by rfl) ⟨181859, by rfl⟩ : syracuseStep 242479 = 363719) B363719
theorem B242587 : Blo 239816 242587 := bstep (se 1 (by rfl) ⟨181940, by rfl⟩ : syracuseStep 242587 = 363881) B363881
theorem B242639 : Blo 239816 242639 := bstep (se 1 (by rfl) ⟨181979, by rfl⟩ : syracuseStep 242639 = 363959) B363959
theorem B1225691 : Blo 239816 1225691 := bstep (se 1 (by rfl) ⟨919268, by rfl⟩ : syracuseStep 1225691 = 1838537) B1838537
theorem B242663 : Blo 239816 242663 := bstep (se 1 (by rfl) ⟨181997, by rfl⟩ : syracuseStep 242663 = 363995) B363995
theorem B1225853 : Blo 239816 1225853 := bstep (se 3 (by rfl) ⟨229847, by rfl⟩ : syracuseStep 1225853 = 459695) B459695
theorem B2307217 : Blo 239816 2307217 := bstep (se 2 (by rfl) ⟨865206, by rfl⟩ : syracuseStep 2307217 = 1730413) B1730413
theorem B308443 : Blo 239816 308443 := bstep (se 1 (by rfl) ⟨231332, by rfl⟩ : syracuseStep 308443 = 462665) B462665
theorem B6206705 : Blo 239816 6206705 := bstep (se 2 (by rfl) ⟨2327514, by rfl⟩ : syracuseStep 6206705 = 4655029) B4655029
theorem B242975 : Blo 239816 242975 := bstep (se 1 (by rfl) ⟨182231, by rfl⟩ : syracuseStep 242975 = 364463) B364463
theorem B243035 : Blo 239816 243035 := bstep (se 1 (by rfl) ⟨182276, by rfl⟩ : syracuseStep 243035 = 364553) B364553
theorem B243055 : Blo 239816 243055 := bstep (se 1 (by rfl) ⟨182291, by rfl⟩ : syracuseStep 243055 = 364583) B364583
theorem B243111 : Blo 239816 243111 := bstep (se 1 (by rfl) ⟨182333, by rfl⟩ : syracuseStep 243111 = 364667) B364667
theorem B1226177 : Blo 239816 1226177 := bstep (se 2 (by rfl) ⟨459816, by rfl⟩ : syracuseStep 1226177 = 919633) B919633
theorem B243195 : Blo 239816 243195 := bstep (se 1 (by rfl) ⟨182396, by rfl⟩ : syracuseStep 243195 = 364793) B364793
theorem B4634117 : Blo 239816 4634117 := bstep (se 4 (by rfl) ⟨434448, by rfl⟩ : syracuseStep 4634117 = 868897) B868897
theorem B243263 : Blo 239816 243263 := bstep (se 1 (by rfl) ⟨182447, by rfl⟩ : syracuseStep 243263 = 364895) B364895
theorem B243271 : Blo 239816 243271 := bstep (se 1 (by rfl) ⟨182453, by rfl⟩ : syracuseStep 243271 = 364907) B364907
theorem B407227 : Blo 239816 407227 := bstep (se 1 (by rfl) ⟨305420, by rfl⟩ : syracuseStep 407227 = 610841) B610841
theorem B243423 : Blo 239816 243423 := bstep (se 1 (by rfl) ⟨182567, by rfl⟩ : syracuseStep 243423 = 365135) B365135
theorem B243503 : Blo 239816 243503 := bstep (se 1 (by rfl) ⟨182627, by rfl⟩ : syracuseStep 243503 = 365255) B365255
theorem B243611 : Blo 239816 243611 := bstep (se 1 (by rfl) ⟨182708, by rfl⟩ : syracuseStep 243611 = 365417) B365417
theorem B243663 : Blo 239816 243663 := bstep (se 1 (by rfl) ⟨182747, by rfl⟩ : syracuseStep 243663 = 365495) B365495
theorem B243687 : Blo 239816 243687 := bstep (se 1 (by rfl) ⟨182765, by rfl⟩ : syracuseStep 243687 = 365531) B365531
theorem B2472643 : Blo 239816 2472643 := bstep (se 1 (by rfl) ⟨1854482, by rfl⟩ : syracuseStep 2472643 = 3708965) B3708965
theorem B1555139 : Blo 239816 1555139 := bstep (se 1 (by rfl) ⟨1166354, by rfl⟩ : syracuseStep 1555139 = 2332709) B2332709
theorem B408287 : Blo 239816 408287 := bstep (se 1 (by rfl) ⟨306215, by rfl⟩ : syracuseStep 408287 = 612431) B612431
theorem B1948535 : Blo 239816 1948535 := bstep (se 1 (by rfl) ⟨1461401, by rfl⟩ : syracuseStep 1948535 = 2922803) B2922803
theorem B539639 : Blo 239816 539639 := bstep (se 1 (by rfl) ⟨404729, by rfl⟩ : syracuseStep 539639 = 809459) B809459
theorem B4734071 : Blo 239816 4734071 := bstep (se 1 (by rfl) ⟨3550553, by rfl⟩ : syracuseStep 4734071 = 7101107) B7101107
theorem B408719 : Blo 239816 408719 := bstep (se 1 (by rfl) ⟨306539, by rfl⟩ : syracuseStep 408719 = 613079) B613079
theorem B539999 : Blo 239816 539999 := bstep (se 1 (by rfl) ⟨404999, by rfl⟩ : syracuseStep 539999 = 809999) B809999
theorem B408955 : Blo 239816 408955 := bstep (se 1 (by rfl) ⟨306716, by rfl⟩ : syracuseStep 408955 = 613433) B613433
theorem B3128777 : Blo 239816 3128777 := bstep (se 2 (by rfl) ⟨1173291, by rfl⟩ : syracuseStep 3128777 = 2346583) B2346583
theorem B540395 : Blo 239816 540395 := bstep (se 1 (by rfl) ⟨405296, by rfl⟩ : syracuseStep 540395 = 810593) B810593
theorem B343855 : Blo 239816 343855 := bstep (se 1 (by rfl) ⟨257891, by rfl⟩ : syracuseStep 343855 = 515783) B515783
theorem B540521 : Blo 239816 540521 := bstep (se 2 (by rfl) ⟨202695, by rfl⟩ : syracuseStep 540521 = 405391) B405391
theorem B1032401 : Blo 239816 1032401 := bstep (se 2 (by rfl) ⟨387150, by rfl⟩ : syracuseStep 1032401 = 774301) B774301
theorem B2310565 : Blo 239816 2310565 := bstep (se 4 (by rfl) ⟨216615, by rfl⟩ : syracuseStep 2310565 = 433231) B433231
theorem B9290375 : Blo 239816 9290375 := bstep (se 1 (by rfl) ⟨6967781, by rfl⟩ : syracuseStep 9290375 = 13935563) B13935563
theorem B541367 : Blo 239816 541367 := bstep (se 1 (by rfl) ⟨406025, by rfl⟩ : syracuseStep 541367 = 812051) B812051
theorem B441762497 : Blo 239816 441762497 := bstep (se 2 (by rfl) ⟨165660936, by rfl⟩ : syracuseStep 441762497 = 331321873) B331321873
theorem B410447 : Blo 239816 410447 := bstep (se 1 (by rfl) ⟨307835, by rfl⟩ : syracuseStep 410447 = 615671) B615671
theorem B541583 : Blo 239816 541583 := bstep (se 1 (by rfl) ⟨406187, by rfl⟩ : syracuseStep 541583 = 812375) B812375
theorem B4441051 : Blo 239816 4441051 := bstep (se 1 (by rfl) ⟨3330788, by rfl⟩ : syracuseStep 4441051 = 6661577) B6661577
theorem B1098809 : Blo 239816 1098809 := bstep (se 2 (by rfl) ⟨412053, by rfl⟩ : syracuseStep 1098809 = 824107) B824107
theorem B1557737 : Blo 239816 1557737 := bstep (se 2 (by rfl) ⟨584151, by rfl⟩ : syracuseStep 1557737 = 1168303) B1168303
theorem B738683 : Blo 239816 738683 := bstep (se 1 (by rfl) ⟨554012, by rfl⟩ : syracuseStep 738683 = 1108025) B1108025
theorem B542303 : Blo 239816 542303 := bstep (se 1 (by rfl) ⟨406727, by rfl⟩ : syracuseStep 542303 = 813455) B813455
theorem B411439 : Blo 239816 411439 := bstep (se 1 (by rfl) ⟨308579, by rfl⟩ : syracuseStep 411439 = 617159) B617159
theorem B542519 : Blo 239816 542519 := bstep (se 1 (by rfl) ⟨406889, by rfl⟩ : syracuseStep 542519 = 813779) B813779
theorem B608057 : Blo 239816 608057 := bstep (se 2 (by rfl) ⟨228021, by rfl⟩ : syracuseStep 608057 = 456043) B456043
theorem B542825 : Blo 239816 542825 := bstep (se 2 (by rfl) ⟨203559, by rfl⟩ : syracuseStep 542825 = 407119) B407119
theorem B13289669 : Blo 239816 13289669 := bstep (se 4 (by rfl) ⟨1245906, by rfl⟩ : syracuseStep 13289669 = 2491813) B2491813
theorem B2214287 : Blo 239816 2214287 := bstep (se 1 (by rfl) ⟨1660715, by rfl⟩ : syracuseStep 2214287 = 3321431) B3321431
theorem B543311 : Blo 239816 543311 := bstep (se 1 (by rfl) ⟨407483, by rfl⟩ : syracuseStep 543311 = 814967) B814967
theorem B346799 : Blo 239816 346799 := bstep (se 1 (by rfl) ⟨260099, by rfl⟩ : syracuseStep 346799 = 520199) B520199
theorem B543455 : Blo 239816 543455 := bstep (se 1 (by rfl) ⟨407591, by rfl⟩ : syracuseStep 543455 = 815183) B815183
theorem B576335 : Blo 239816 576335 := bstep (se 1 (by rfl) ⟨432251, by rfl⟩ : syracuseStep 576335 = 864503) B864503
theorem B543707 : Blo 239816 543707 := bstep (se 1 (by rfl) ⟨407780, by rfl⟩ : syracuseStep 543707 = 815561) B815561
theorem B609403 : Blo 239816 609403 := bstep (se 1 (by rfl) ⟨457052, by rfl⟩ : syracuseStep 609403 = 914105) B914105
theorem B543887 : Blo 239816 543887 := bstep (se 1 (by rfl) ⟨407915, by rfl⟩ : syracuseStep 543887 = 815831) B815831
theorem B5262515 : Blo 239816 5262515 := bstep (se 1 (by rfl) ⟨3946886, by rfl⟩ : syracuseStep 5262515 = 7893773) B7893773
theorem B543977 : Blo 239816 543977 := bstep (se 2 (by rfl) ⟨203991, by rfl⟩ : syracuseStep 543977 = 407983) B407983
theorem B544031 : Blo 239816 544031 := bstep (se 1 (by rfl) ⟨408023, by rfl⟩ : syracuseStep 544031 = 816047) B816047
theorem B1822013 : Blo 239816 1822013 := bstep (se 3 (by rfl) ⟨341627, by rfl⟩ : syracuseStep 1822013 = 683255) B683255
theorem B1756835 : Blo 239816 1756835 := bstep (se 1 (by rfl) ⟨1317626, by rfl⟩ : syracuseStep 1756835 = 2635253) B2635253
theorem B544553 : Blo 239816 544553 := bstep (se 2 (by rfl) ⟨204207, by rfl⟩ : syracuseStep 544553 = 408415) B408415
theorem B413497 : Blo 239816 413497 := bstep (se 2 (by rfl) ⟨155061, by rfl⟩ : syracuseStep 413497 = 310123) B310123
theorem B872473 : Blo 239816 872473 := bstep (se 2 (by rfl) ⟨327177, by rfl⟩ : syracuseStep 872473 = 654355) B654355
theorem B3461291 : Blo 239816 3461291 := bstep (se 1 (by rfl) ⟨2595968, by rfl⟩ : syracuseStep 3461291 = 5191937) B5191937
theorem B610811 : Blo 239816 610811 := bstep (se 1 (by rfl) ⟨458108, by rfl⟩ : syracuseStep 610811 = 916217) B916217
theorem B5231303 : Blo 239816 5231303 := bstep (se 1 (by rfl) ⟨3923477, by rfl⟩ : syracuseStep 5231303 = 7846955) B7846955
theorem B676687 : Blo 239816 676687 := bstep (se 1 (by rfl) ⟨507515, by rfl⟩ : syracuseStep 676687 = 1015031) B1015031
theorem B3494735 : Blo 239816 3494735 := bstep (se 1 (by rfl) ⟨2621051, by rfl⟩ : syracuseStep 3494735 = 5242103) B5242103
theorem B545615 : Blo 239816 545615 := bstep (se 1 (by rfl) ⟨409211, by rfl⟩ : syracuseStep 545615 = 818423) B818423
theorem B2315213 : Blo 239816 2315213 := bstep (se 3 (by rfl) ⟨434102, by rfl⟩ : syracuseStep 2315213 = 868205) B868205
theorem B545831 : Blo 239816 545831 := bstep (se 1 (by rfl) ⟨409373, by rfl⟩ : syracuseStep 545831 = 818747) B818747
theorem B546011 : Blo 239816 546011 := bstep (se 1 (by rfl) ⟨409508, by rfl⟩ : syracuseStep 546011 = 819017) B819017
theorem B546209 : Blo 239816 546209 := bstep (se 2 (by rfl) ⟨204828, by rfl⟩ : syracuseStep 546209 = 409657) B409657
theorem B513467 : Blo 239816 513467 := bstep (se 1 (by rfl) ⟨385100, by rfl⟩ : syracuseStep 513467 = 770201) B770201
theorem B611783 : Blo 239816 611783 := bstep (se 1 (by rfl) ⟨458837, by rfl⟩ : syracuseStep 611783 = 917675) B917675
theorem B611833 : Blo 239816 611833 := bstep (se 2 (by rfl) ⟨229437, by rfl⟩ : syracuseStep 611833 = 458875) B458875
theorem B2774573 : Blo 239816 2774573 := bstep (se 3 (by rfl) ⟨520232, by rfl⟩ : syracuseStep 2774573 = 1040465) B1040465
theorem B1824443 : Blo 239816 1824443 := bstep (se 1 (by rfl) ⟨1368332, by rfl⟩ : syracuseStep 1824443 = 2736665) B2736665
theorem B612137 : Blo 239816 612137 := bstep (se 2 (by rfl) ⟨229551, by rfl⟩ : syracuseStep 612137 = 459103) B459103
theorem B546767 : Blo 239816 546767 := bstep (se 1 (by rfl) ⟨410075, by rfl⟩ : syracuseStep 546767 = 820151) B820151
theorem B1038415 : Blo 239816 1038415 := bstep (se 1 (by rfl) ⟨778811, by rfl⟩ : syracuseStep 1038415 = 1557623) B1557623
theorem B579689 : Blo 239816 579689 := bstep (se 2 (by rfl) ⟨217383, by rfl⟩ : syracuseStep 579689 = 434767) B434767
theorem B612481 : Blo 239816 612481 := bstep (se 2 (by rfl) ⟨229680, by rfl⟩ : syracuseStep 612481 = 459361) B459361
theorem B547145 : Blo 239816 547145 := bstep (se 2 (by rfl) ⟨205179, by rfl⟩ : syracuseStep 547145 = 410359) B410359
theorem B547163 : Blo 239816 547163 := bstep (se 1 (by rfl) ⟨410372, by rfl⟩ : syracuseStep 547163 = 820745) B820745
theorem B580495 : Blo 239816 580495 := bstep (se 1 (by rfl) ⟨435371, by rfl⟩ : syracuseStep 580495 = 870743) B870743
theorem B547739 : Blo 239816 547739 := bstep (se 1 (by rfl) ⟨410804, by rfl⟩ : syracuseStep 547739 = 821609) B821609
theorem B613291 : Blo 239816 613291 := bstep (se 1 (by rfl) ⟨459968, by rfl⟩ : syracuseStep 613291 = 919937) B919937
theorem B547937 : Blo 239816 547937 := bstep (se 2 (by rfl) ⟨205476, by rfl⟩ : syracuseStep 547937 = 410953) B410953
theorem B810107 : Blo 239816 810107 := bstep (se 1 (by rfl) ⟨607580, by rfl⟩ : syracuseStep 810107 = 1215161) B1215161
theorem B1105085 : Blo 239816 1105085 := bstep (se 3 (by rfl) ⟨207203, by rfl⟩ : syracuseStep 1105085 = 414407) B414407
theorem B613595 : Blo 239816 613595 := bstep (se 1 (by rfl) ⟨460196, by rfl⟩ : syracuseStep 613595 = 920393) B920393
theorem B1301771 : Blo 239816 1301771 := bstep (se 1 (by rfl) ⟨976328, by rfl⟩ : syracuseStep 1301771 = 1952657) B1952657
theorem B1170719 : Blo 239816 1170719 := bstep (se 1 (by rfl) ⟨878039, by rfl⟩ : syracuseStep 1170719 = 1756079) B1756079
theorem B548135 : Blo 239816 548135 := bstep (se 1 (by rfl) ⟨411101, by rfl⟩ : syracuseStep 548135 = 822203) B822203
theorem B613727 : Blo 239816 613727 := bstep (se 1 (by rfl) ⟨460295, by rfl⟩ : syracuseStep 613727 = 920591) B920591
theorem B810377 : Blo 239816 810377 := bstep (se 2 (by rfl) ⟨303891, by rfl⟩ : syracuseStep 810377 = 607783) B607783
theorem B1826387 : Blo 239816 1826387 := bstep (se 1 (by rfl) ⟨1369790, by rfl⟩ : syracuseStep 1826387 = 2739581) B2739581
theorem B548513 : Blo 239816 548513 := bstep (se 2 (by rfl) ⟨205692, by rfl⟩ : syracuseStep 548513 = 411385) B411385
theorem B810809 : Blo 239816 810809 := bstep (se 2 (by rfl) ⟨304053, by rfl⟩ : syracuseStep 810809 = 608107) B608107
theorem B515945 : Blo 239816 515945 := bstep (se 2 (by rfl) ⟨193479, by rfl⟩ : syracuseStep 515945 = 386959) B386959
theorem B614425 : Blo 239816 614425 := bstep (se 2 (by rfl) ⟨230409, by rfl⟩ : syracuseStep 614425 = 460819) B460819
theorem B549193 : Blo 239816 549193 := bstep (se 2 (by rfl) ⟨205947, by rfl⟩ : syracuseStep 549193 = 411895) B411895
theorem B614729 : Blo 239816 614729 := bstep (se 2 (by rfl) ⟨230523, by rfl⟩ : syracuseStep 614729 = 461047) B461047
theorem B581995 : Blo 239816 581995 := bstep (se 1 (by rfl) ⟨436496, by rfl⟩ : syracuseStep 581995 = 872993) B872993
theorem B516577 : Blo 239816 516577 := bstep (se 2 (by rfl) ⟨193716, by rfl⟩ : syracuseStep 516577 = 387433) B387433
theorem B385607 : Blo 239816 385607 := bstep (se 1 (by rfl) ⟨289205, by rfl⟩ : syracuseStep 385607 = 578411) B578411
theorem B811673 : Blo 239816 811673 := bstep (se 2 (by rfl) ⟨304377, by rfl⟩ : syracuseStep 811673 = 608755) B608755
theorem B2974913 : Blo 239816 2974913 := bstep (se 2 (by rfl) ⟨1115592, by rfl⟩ : syracuseStep 2974913 = 2231185) B2231185
theorem B1303847 : Blo 239816 1303847 := bstep (se 1 (by rfl) ⟨977885, by rfl⟩ : syracuseStep 1303847 = 1955771) B1955771
theorem B1238561 : Blo 239816 1238561 := bstep (se 2 (by rfl) ⟨464460, by rfl⟩ : syracuseStep 1238561 = 928921) B928921
theorem B3073625 : Blo 239816 3073625 := bstep (se 2 (by rfl) ⟨1152609, by rfl⟩ : syracuseStep 3073625 = 2305219) B2305219
theorem B911159 : Blo 239816 911159 := bstep (se 1 (by rfl) ⟨683369, by rfl⟩ : syracuseStep 911159 = 1366739) B1366739
theorem B288667 : Blo 239816 288667 := bstep (se 1 (by rfl) ⟨216500, by rfl⟩ : syracuseStep 288667 = 433001) B433001
theorem B4155299 : Blo 239816 4155299 := bstep (se 1 (by rfl) ⟨3116474, by rfl⟩ : syracuseStep 4155299 = 6232949) B6232949
theorem B4679633 : Blo 239816 4679633 := bstep (se 2 (by rfl) ⟨1754862, by rfl⟩ : syracuseStep 4679633 = 3509725) B3509725
theorem B2222095 : Blo 239816 2222095 := bstep (se 1 (by rfl) ⟨1666571, by rfl⟩ : syracuseStep 2222095 = 3333143) B3333143
theorem B813185 : Blo 239816 813185 := bstep (se 2 (by rfl) ⟨304944, by rfl⟩ : syracuseStep 813185 = 609889) B609889
theorem B911645 : Blo 239816 911645 := bstep (se 3 (by rfl) ⟨170933, by rfl⟩ : syracuseStep 911645 = 341867) B341867
theorem B4680179 : Blo 239816 4680179 := bstep (se 1 (by rfl) ⟨3510134, by rfl⟩ : syracuseStep 4680179 = 7020269) B7020269
theorem B813563 : Blo 239816 813563 := bstep (se 1 (by rfl) ⟨610172, by rfl⟩ : syracuseStep 813563 = 1220345) B1220345
theorem B584263 : Blo 239816 584263 := bstep (se 1 (by rfl) ⟨438197, by rfl⟩ : syracuseStep 584263 = 876395) B876395
theorem B518729 : Blo 239816 518729 := bstep (se 2 (by rfl) ⟨194523, by rfl⟩ : syracuseStep 518729 = 389047) B389047
theorem B420473 : Blo 239816 420473 := bstep (se 2 (by rfl) ⟨157677, by rfl⟩ : syracuseStep 420473 = 315355) B315355
theorem B11168441 : Blo 239816 11168441 := bstep (se 2 (by rfl) ⟨4188165, by rfl⟩ : syracuseStep 11168441 = 8376331) B8376331
theorem B813995 : Blo 239816 813995 := bstep (se 1 (by rfl) ⟨610496, by rfl⟩ : syracuseStep 813995 = 1220993) B1220993
theorem B650227 : Blo 239816 650227 := bstep (se 1 (by rfl) ⟨487670, by rfl⟩ : syracuseStep 650227 = 975341) B975341
theorem B584801 : Blo 239816 584801 := bstep (se 2 (by rfl) ⟨219300, by rfl⟩ : syracuseStep 584801 = 438601) B438601
theorem B519311 : Blo 239816 519311 := bstep (se 1 (by rfl) ⟨389483, by rfl⟩ : syracuseStep 519311 = 778967) B778967
theorem B1404191 : Blo 239816 1404191 := bstep (se 1 (by rfl) ⟨1053143, by rfl⟩ : syracuseStep 1404191 = 2106287) B2106287
theorem B814535 : Blo 239816 814535 := bstep (se 1 (by rfl) ⟨610901, by rfl⟩ : syracuseStep 814535 = 1221803) B1221803
theorem B1732259 : Blo 239816 1732259 := bstep (se 1 (by rfl) ⟨1299194, by rfl⟩ : syracuseStep 1732259 = 2598389) B2598389
theorem B12906161 : Blo 239816 12906161 := bstep (se 2 (by rfl) ⟨4839810, by rfl⟩ : syracuseStep 12906161 = 9679621) B9679621
theorem B814859 : Blo 239816 814859 := bstep (se 1 (by rfl) ⟨611144, by rfl⟩ : syracuseStep 814859 = 1222289) B1222289
theorem B388919 : Blo 239816 388919 := bstep (se 1 (by rfl) ⟨291689, by rfl⟩ : syracuseStep 388919 = 583379) B583379
theorem B815129 : Blo 239816 815129 := bstep (se 2 (by rfl) ⟨305673, by rfl⟩ : syracuseStep 815129 = 611347) B611347
theorem B618625 : Blo 239816 618625 := bstep (se 2 (by rfl) ⟨231984, by rfl⟩ : syracuseStep 618625 = 463969) B463969
theorem B913619 : Blo 239816 913619 := bstep (se 1 (by rfl) ⟨685214, by rfl⟩ : syracuseStep 913619 = 1370429) B1370429
theorem B684395 : Blo 239816 684395 := bstep (se 1 (by rfl) ⟨513296, by rfl⟩ : syracuseStep 684395 = 1026593) B1026593
theorem B684463 : Blo 239816 684463 := bstep (se 1 (by rfl) ⟨513347, by rfl⟩ : syracuseStep 684463 = 1026695) B1026695
theorem B4452889 : Blo 239816 4452889 := bstep (se 2 (by rfl) ⟨1669833, by rfl⟩ : syracuseStep 4452889 = 3339667) B3339667
theorem B1077943 : Blo 239816 1077943 := bstep (se 1 (by rfl) ⟨808457, by rfl⟩ : syracuseStep 1077943 = 1616915) B1616915
theorem B619343 : Blo 239816 619343 := bstep (se 1 (by rfl) ⟨464507, by rfl⟩ : syracuseStep 619343 = 929015) B929015
theorem B1307501 : Blo 239816 1307501 := bstep (se 3 (by rfl) ⟨245156, by rfl⟩ : syracuseStep 1307501 = 490313) B490313
theorem B652279 : Blo 239816 652279 := bstep (se 1 (by rfl) ⟨489209, by rfl⟩ : syracuseStep 652279 = 978419) B978419
theorem B816371 : Blo 239816 816371 := bstep (se 1 (by rfl) ⟨612278, by rfl⟩ : syracuseStep 816371 = 1224557) B1224557
theorem B390431 : Blo 239816 390431 := bstep (se 1 (by rfl) ⟨292823, by rfl⟩ : syracuseStep 390431 = 585647) B585647
theorem B685351 : Blo 239816 685351 := bstep (se 1 (by rfl) ⟨514013, by rfl⟩ : syracuseStep 685351 = 1028027) B1028027
theorem B816479 : Blo 239816 816479 := bstep (se 1 (by rfl) ⟨612359, by rfl⟩ : syracuseStep 816479 = 1224719) B1224719
theorem B292295 : Blo 239816 292295 := bstep (se 1 (by rfl) ⟨219221, by rfl⟩ : syracuseStep 292295 = 438443) B438443
theorem B5928889 : Blo 239816 5928889 := bstep (se 2 (by rfl) ⟨2223333, by rfl⟩ : syracuseStep 5928889 = 4446667) B4446667
theorem B2062583 : Blo 239816 2062583 := bstep (se 1 (by rfl) ⟨1546937, by rfl⟩ : syracuseStep 2062583 = 3093875) B3093875
theorem B2357495 : Blo 239816 2357495 := bstep (se 1 (by rfl) ⟨1768121, by rfl⟩ : syracuseStep 2357495 = 3536243) B3536243
theorem B522587 : Blo 239816 522587 := bstep (se 1 (by rfl) ⟨391940, by rfl⟩ : syracuseStep 522587 = 783881) B783881
theorem B818045 : Blo 239816 818045 := bstep (se 3 (by rfl) ⟨153383, by rfl⟩ : syracuseStep 818045 = 306767) B306767
theorem B555947 : Blo 239816 555947 := bstep (se 1 (by rfl) ⟨416960, by rfl⟩ : syracuseStep 555947 = 833921) B833921
theorem B3111965 : Blo 239816 3111965 := bstep (se 3 (by rfl) ⟨583493, by rfl⟩ : syracuseStep 3111965 = 1166987) B1166987
theorem B818315 : Blo 239816 818315 := bstep (se 1 (by rfl) ⟨613736, by rfl⟩ : syracuseStep 818315 = 1227473) B1227473
theorem B654551 : Blo 239816 654551 := bstep (se 1 (by rfl) ⟨490913, by rfl⟩ : syracuseStep 654551 = 981827) B981827
theorem B359879 : Blo 239816 359879 := bstep (se 1 (by rfl) ⟨269909, by rfl⟩ : syracuseStep 359879 = 539819) B539819
theorem B360233 : Blo 239816 360233 := bstep (se 2 (by rfl) ⟨135087, by rfl⟩ : syracuseStep 360233 = 270175) B270175
theorem B360239 : Blo 239816 360239 := bstep (se 1 (by rfl) ⟨270179, by rfl⟩ : syracuseStep 360239 = 540359) B540359
theorem B819233 : Blo 239816 819233 := bstep (se 2 (by rfl) ⟨307212, by rfl⟩ : syracuseStep 819233 = 614425) B614425
theorem B688267 : Blo 239816 688267 := bstep (se 1 (by rfl) ⟨516200, by rfl⟩ : syracuseStep 688267 = 1032401) B1032401
theorem B6193583 : Blo 239816 6193583 := bstep (se 1 (by rfl) ⟨4645187, by rfl⟩ : syracuseStep 6193583 = 9290375) B9290375
theorem B1311175 : Blo 239816 1311175 := bstep (se 1 (by rfl) ⟨983381, by rfl⟩ : syracuseStep 1311175 = 1966763) B1966763
theorem B360911 : Blo 239816 360911 := bstep (se 1 (by rfl) ⟨270683, by rfl⟩ : syracuseStep 360911 = 541367) B541367
theorem B360953 : Blo 239816 360953 := bstep (se 2 (by rfl) ⟨135357, by rfl⟩ : syracuseStep 360953 = 270715) B270715
theorem B3080753 : Blo 239816 3080753 := bstep (se 2 (by rfl) ⟨1155282, by rfl⟩ : syracuseStep 3080753 = 2310565) B2310565
theorem B3736115 : Blo 239816 3736115 := bstep (se 1 (by rfl) ⟨2802086, by rfl⟩ : syracuseStep 3736115 = 5604173) B5604173
theorem B361055 : Blo 239816 361055 := bstep (se 1 (by rfl) ⟨270791, by rfl⟩ : syracuseStep 361055 = 541583) B541583
theorem B688769 : Blo 239816 688769 := bstep (se 2 (by rfl) ⟨258288, by rfl⟩ : syracuseStep 688769 = 516577) B516577
theorem B492455 : Blo 239816 492455 := bstep (se 1 (by rfl) ⟨369341, by rfl⟩ : syracuseStep 492455 = 738683) B738683
theorem B361535 : Blo 239816 361535 := bstep (se 1 (by rfl) ⟨271151, by rfl⟩ : syracuseStep 361535 = 542303) B542303
theorem B361577 : Blo 239816 361577 := bstep (se 2 (by rfl) ⟨135591, by rfl⟩ : syracuseStep 361577 = 271183) B271183
theorem B361679 : Blo 239816 361679 := bstep (se 1 (by rfl) ⟨271259, by rfl⟩ : syracuseStep 361679 = 542519) B542519
theorem B361883 : Blo 239816 361883 := bstep (se 1 (by rfl) ⟨271412, by rfl⟩ : syracuseStep 361883 = 542825) B542825
theorem B1476191 : Blo 239816 1476191 := bstep (se 1 (by rfl) ⟨1107143, by rfl⟩ : syracuseStep 1476191 = 2214287) B2214287
theorem B362105 : Blo 239816 362105 := bstep (se 2 (by rfl) ⟨135789, by rfl⟩ : syracuseStep 362105 = 271579) B271579
theorem B362207 : Blo 239816 362207 := bstep (se 1 (by rfl) ⟨271655, by rfl⟩ : syracuseStep 362207 = 543311) B543311
theorem B362303 : Blo 239816 362303 := bstep (se 1 (by rfl) ⟨271727, by rfl⟩ : syracuseStep 362303 = 543455) B543455
theorem B1542017 : Blo 239816 1542017 := bstep (se 2 (by rfl) ⟨578256, by rfl⟩ : syracuseStep 1542017 = 1156513) B1156513
theorem B362471 : Blo 239816 362471 := bstep (se 1 (by rfl) ⟨271853, by rfl⟩ : syracuseStep 362471 = 543707) B543707
theorem B362489 : Blo 239816 362489 := bstep (se 2 (by rfl) ⟨135933, by rfl⟩ : syracuseStep 362489 = 271867) B271867
theorem B362591 : Blo 239816 362591 := bstep (se 1 (by rfl) ⟨271943, by rfl⟩ : syracuseStep 362591 = 543887) B543887
theorem B3508343 : Blo 239816 3508343 := bstep (se 1 (by rfl) ⟨2631257, by rfl⟩ : syracuseStep 3508343 = 5262515) B5262515
theorem B362651 : Blo 239816 362651 := bstep (se 1 (by rfl) ⟨271988, by rfl⟩ : syracuseStep 362651 = 543977) B543977
theorem B362687 : Blo 239816 362687 := bstep (se 1 (by rfl) ⟨272015, by rfl⟩ : syracuseStep 362687 = 544031) B544031
theorem B1214675 : Blo 239816 1214675 := bstep (se 1 (by rfl) ⟨911006, by rfl⟩ : syracuseStep 1214675 = 1822013) B1822013
theorem B362729 : Blo 239816 362729 := bstep (se 2 (by rfl) ⟨136023, by rfl⟩ : syracuseStep 362729 = 272047) B272047
theorem B363035 : Blo 239816 363035 := bstep (se 1 (by rfl) ⟨272276, by rfl⟩ : syracuseStep 363035 = 544553) B544553
theorem B363113 : Blo 239816 363113 := bstep (se 2 (by rfl) ⟨136167, by rfl⟩ : syracuseStep 363113 = 272335) B272335
theorem B1968745 : Blo 239816 1968745 := bstep (se 2 (by rfl) ⟨738279, by rfl⟩ : syracuseStep 1968745 = 1476559) B1476559
theorem B1575973 : Blo 239816 1575973 := bstep (se 4 (by rfl) ⟨147747, by rfl⟩ : syracuseStep 1575973 = 295495) B295495
theorem B363641 : Blo 239816 363641 := bstep (se 2 (by rfl) ⟨136365, by rfl⟩ : syracuseStep 363641 = 272731) B272731
theorem B2329823 : Blo 239816 2329823 := bstep (se 1 (by rfl) ⟨1747367, by rfl⟩ : syracuseStep 2329823 = 3494735) B3494735
theorem B363743 : Blo 239816 363743 := bstep (se 1 (by rfl) ⟨272807, by rfl⟩ : syracuseStep 363743 = 545615) B545615
theorem B363785 : Blo 239816 363785 := bstep (se 2 (by rfl) ⟨136419, by rfl⟩ : syracuseStep 363785 = 272839) B272839
theorem B1543475 : Blo 239816 1543475 := bstep (se 1 (by rfl) ⟨1157606, by rfl⟩ : syracuseStep 1543475 = 2315213) B2315213
theorem B363887 : Blo 239816 363887 := bstep (se 1 (by rfl) ⟨272915, by rfl⟩ : syracuseStep 363887 = 545831) B545831
theorem B364007 : Blo 239816 364007 := bstep (se 1 (by rfl) ⟨273005, by rfl⟩ : syracuseStep 364007 = 546011) B546011
theorem B364139 : Blo 239816 364139 := bstep (se 1 (by rfl) ⟨273104, by rfl⟩ : syracuseStep 364139 = 546209) B546209
theorem B364265 : Blo 239816 364265 := bstep (se 2 (by rfl) ⟨136599, by rfl⟩ : syracuseStep 364265 = 273199) B273199
theorem B462611 : Blo 239816 462611 := bstep (se 1 (by rfl) ⟨346958, by rfl⟩ : syracuseStep 462611 = 693917) B693917
theorem B1216295 : Blo 239816 1216295 := bstep (se 1 (by rfl) ⟨912221, by rfl⟩ : syracuseStep 1216295 = 1824443) B1824443
theorem B364409 : Blo 239816 364409 := bstep (se 2 (by rfl) ⟨136653, by rfl⟩ : syracuseStep 364409 = 273307) B273307
theorem B364511 : Blo 239816 364511 := bstep (se 1 (by rfl) ⟨273383, by rfl⟩ : syracuseStep 364511 = 546767) B546767
theorem B364763 : Blo 239816 364763 := bstep (se 1 (by rfl) ⟨273572, by rfl⟩ : syracuseStep 364763 = 547145) B547145
theorem B364775 : Blo 239816 364775 := bstep (se 1 (by rfl) ⟨273581, by rfl⟩ : syracuseStep 364775 = 547163) B547163
theorem B364937 : Blo 239816 364937 := bstep (se 2 (by rfl) ⟨136851, by rfl⟩ : syracuseStep 364937 = 273703) B273703
theorem B365033 : Blo 239816 365033 := bstep (se 2 (by rfl) ⟨136887, by rfl⟩ : syracuseStep 365033 = 273775) B273775
theorem B7082497 : Blo 239816 7082497 := bstep (se 2 (by rfl) ⟨2655936, by rfl⟩ : syracuseStep 7082497 = 5311873) B5311873
theorem B365159 : Blo 239816 365159 := bstep (se 1 (by rfl) ⟨273869, by rfl⟩ : syracuseStep 365159 = 547739) B547739
theorem B365291 : Blo 239816 365291 := bstep (se 1 (by rfl) ⟨273968, by rfl⟩ : syracuseStep 365291 = 547937) B547937
theorem B365321 : Blo 239816 365321 := bstep (se 2 (by rfl) ⟨136995, by rfl⟩ : syracuseStep 365321 = 273991) B273991
theorem B529193 : Blo 239816 529193 := bstep (se 2 (by rfl) ⟨198447, by rfl⟩ : syracuseStep 529193 = 396895) B396895
theorem B365423 : Blo 239816 365423 := bstep (se 1 (by rfl) ⟨274067, by rfl⟩ : syracuseStep 365423 = 548135) B548135
theorem B1217591 : Blo 239816 1217591 := bstep (se 1 (by rfl) ⟨913193, by rfl⟩ : syracuseStep 1217591 = 1826387) B1826387
theorem B365675 : Blo 239816 365675 := bstep (se 1 (by rfl) ⟨274256, by rfl⟩ : syracuseStep 365675 = 548513) B548513
theorem B1545425 : Blo 239816 1545425 := bstep (se 2 (by rfl) ⟨579534, by rfl⟩ : syracuseStep 1545425 = 1159069) B1159069
theorem B9934073 : Blo 239816 9934073 := bstep (se 2 (by rfl) ⟨3725277, by rfl⟩ : syracuseStep 9934073 = 7450555) B7450555
theorem B1381819 : Blo 239816 1381819 := bstep (se 1 (by rfl) ⟨1036364, by rfl⟩ : syracuseStep 1381819 = 2072729) B2072729
theorem B824833 : Blo 239816 824833 := bstep (se 2 (by rfl) ⟨309312, by rfl⟩ : syracuseStep 824833 = 618625) B618625
theorem B5937185 : Blo 239816 5937185 := bstep (se 2 (by rfl) ⟨2226444, by rfl⟩ : syracuseStep 5937185 = 4452889) B4452889
theorem B825707 : Blo 239816 825707 := bstep (se 1 (by rfl) ⟨619280, by rfl⟩ : syracuseStep 825707 = 1238561) B1238561
theorem B924281 : Blo 239816 924281 := bstep (se 2 (by rfl) ⟨346605, by rfl⟩ : syracuseStep 924281 = 693211) B693211
theorem B3119755 : Blo 239816 3119755 := bstep (se 1 (by rfl) ⟨2339816, by rfl⟩ : syracuseStep 3119755 = 4679633) B4679633
theorem B1383277 : Blo 239816 1383277 := bstep (se 3 (by rfl) ⟨259364, by rfl⟩ : syracuseStep 1383277 = 518729) B518729
theorem B3120119 : Blo 239816 3120119 := bstep (se 1 (by rfl) ⟨2340089, by rfl⟩ : syracuseStep 3120119 = 4680179) B4680179
theorem B7445627 : Blo 239816 7445627 := bstep (se 1 (by rfl) ⟨5584220, by rfl⟩ : syracuseStep 7445627 = 11168441) B11168441
theorem B924797 : Blo 239816 924797 := bstep (se 3 (by rfl) ⟨173399, by rfl⟩ : syracuseStep 924797 = 346799) B346799
theorem B3349991 : Blo 239816 3349991 := bstep (se 1 (by rfl) ⟨2512493, by rfl⟩ : syracuseStep 3349991 = 5024987) B5024987
theorem B1154839 : Blo 239816 1154839 := bstep (se 1 (by rfl) ⟨866129, by rfl⟩ : syracuseStep 1154839 = 1732259) B1732259
theorem B1318679 : Blo 239816 1318679 := bstep (se 1 (by rfl) ⟨989009, by rfl⟩ : syracuseStep 1318679 = 1978019) B1978019
theorem B7905185 : Blo 239816 7905185 := bstep (se 2 (by rfl) ⟨2964444, by rfl⟩ : syracuseStep 7905185 = 5928889) B5928889
theorem B1384553 : Blo 239816 1384553 := bstep (se 2 (by rfl) ⟨519207, by rfl⟩ : syracuseStep 1384553 = 1038415) B1038415
theorem B1384735 : Blo 239816 1384735 := bstep (se 1 (by rfl) ⟨1038551, by rfl⟩ : syracuseStep 1384735 = 2077103) B2077103
theorem B4137803 : Blo 239816 4137803 := bstep (se 1 (by rfl) ⟨3103352, by rfl⟩ : syracuseStep 4137803 = 6206705) B6206705
theorem B3089411 : Blo 239816 3089411 := bstep (se 1 (by rfl) ⟨2317058, by rfl⟩ : syracuseStep 3089411 = 4634117) B4634117
theorem B3712229 : Blo 239816 3712229 := bstep (se 4 (by rfl) ⟨348021, by rfl⟩ : syracuseStep 3712229 = 696043) B696043
theorem B272191 : Blo 239816 272191 := bstep (se 1 (by rfl) ⟨204143, by rfl⟩ : syracuseStep 272191 = 408287) B408287
theorem B370631 : Blo 239816 370631 := bstep (se 1 (by rfl) ⟨277973, by rfl⟩ : syracuseStep 370631 = 555947) B555947
theorem B2074643 : Blo 239816 2074643 := bstep (se 1 (by rfl) ⟨1555982, by rfl⟩ : syracuseStep 2074643 = 3111965) B3111965
theorem B3156047 : Blo 239816 3156047 := bstep (se 1 (by rfl) ⟨2367035, by rfl⟩ : syracuseStep 3156047 = 4734071) B4734071
theorem B272479 : Blo 239816 272479 := bstep (se 1 (by rfl) ⟨204359, by rfl⟩ : syracuseStep 272479 = 408719) B408719
theorem B436367 : Blo 239816 436367 := bstep (se 1 (by rfl) ⟨327275, by rfl⟩ : syracuseStep 436367 = 654551) B654551
theorem B239919 : Blo 239816 239919 := bstep (se 1 (by rfl) ⟨179939, by rfl⟩ : syracuseStep 239919 = 359879) B359879
theorem B240155 : Blo 239816 240155 := bstep (se 1 (by rfl) ⟨180116, by rfl⟩ : syracuseStep 240155 = 360233) B360233
theorem B240159 : Blo 239816 240159 := bstep (se 1 (by rfl) ⟨180119, by rfl⟩ : syracuseStep 240159 = 360239) B360239
theorem B895799 : Blo 239816 895799 := bstep (se 1 (by rfl) ⟨671849, by rfl⟩ : syracuseStep 895799 = 1343699) B1343699
theorem B240475 : Blo 239816 240475 := bstep (se 1 (by rfl) ⟨180356, by rfl⟩ : syracuseStep 240475 = 360713) B360713
theorem B240543 : Blo 239816 240543 := bstep (se 1 (by rfl) ⟨180407, by rfl⟩ : syracuseStep 240543 = 360815) B360815
theorem B240687 : Blo 239816 240687 := bstep (se 1 (by rfl) ⟨180515, by rfl⟩ : syracuseStep 240687 = 361031) B361031
theorem B240711 : Blo 239816 240711 := bstep (se 1 (by rfl) ⟨180533, by rfl⟩ : syracuseStep 240711 = 361067) B361067
theorem B732257 : Blo 239816 732257 := bstep (se 2 (by rfl) ⟨274596, by rfl⟩ : syracuseStep 732257 = 549193) B549193
theorem B240863 : Blo 239816 240863 := bstep (se 1 (by rfl) ⟨180647, by rfl⟩ : syracuseStep 240863 = 361295) B361295
theorem B273631 : Blo 239816 273631 := bstep (se 1 (by rfl) ⟨205223, by rfl⟩ : syracuseStep 273631 = 410447) B410447
theorem B732539 : Blo 239816 732539 := bstep (se 1 (by rfl) ⟨549404, by rfl⟩ : syracuseStep 732539 = 1098809) B1098809
theorem B404905 : Blo 239816 404905 := bstep (se 2 (by rfl) ⟨151839, by rfl⟩ : syracuseStep 404905 = 303679) B303679
theorem B241127 : Blo 239816 241127 := bstep (se 1 (by rfl) ⟨180845, by rfl⟩ : syracuseStep 241127 = 361691) B361691
theorem B241243 : Blo 239816 241243 := bstep (se 1 (by rfl) ⟨180932, by rfl⟩ : syracuseStep 241243 = 361865) B361865
theorem B241479 : Blo 239816 241479 := bstep (se 1 (by rfl) ⟨181109, by rfl⟩ : syracuseStep 241479 = 362219) B362219
theorem B405371 : Blo 239816 405371 := bstep (se 1 (by rfl) ⟨304028, by rfl⟩ : syracuseStep 405371 = 608057) B608057
theorem B241631 : Blo 239816 241631 := bstep (se 1 (by rfl) ⟨181223, by rfl⟩ : syracuseStep 241631 = 362447) B362447
theorem B8859779 : Blo 239816 8859779 := bstep (se 1 (by rfl) ⟨6644834, by rfl⟩ : syracuseStep 8859779 = 13289669) B13289669
theorem B1028285 : Blo 239816 1028285 := bstep (se 3 (by rfl) ⟨192803, by rfl⟩ : syracuseStep 1028285 = 385607) B385607
theorem B241895 : Blo 239816 241895 := bstep (se 1 (by rfl) ⟨181421, by rfl⟩ : syracuseStep 241895 = 362843) B362843
theorem B2732291 : Blo 239816 2732291 := bstep (se 1 (by rfl) ⟨2049218, by rfl⟩ : syracuseStep 2732291 = 4098437) B4098437
theorem B242047 : Blo 239816 242047 := bstep (se 1 (by rfl) ⟨181535, by rfl⟩ : syracuseStep 242047 = 363071) B363071
theorem B242127 : Blo 239816 242127 := bstep (se 1 (by rfl) ⟨181595, by rfl⟩ : syracuseStep 242127 = 363191) B363191
theorem B1356257 : Blo 239816 1356257 := bstep (se 2 (by rfl) ⟨508596, by rfl⟩ : syracuseStep 1356257 = 1017193) B1017193
theorem B1552907 : Blo 239816 1552907 := bstep (se 1 (by rfl) ⟨1164680, by rfl⟩ : syracuseStep 1552907 = 2329361) B2329361
theorem B242279 : Blo 239816 242279 := bstep (se 1 (by rfl) ⟨181709, by rfl⟩ : syracuseStep 242279 = 363419) B363419
theorem B5485391 : Blo 239816 5485391 := bstep (se 1 (by rfl) ⟨4114043, by rfl⟩ : syracuseStep 5485391 = 8228087) B8228087
theorem B242543 : Blo 239816 242543 := bstep (se 1 (by rfl) ⟨181907, by rfl⟩ : syracuseStep 242543 = 363815) B363815
theorem B242599 : Blo 239816 242599 := bstep (se 1 (by rfl) ⟨181949, by rfl⟩ : syracuseStep 242599 = 363899) B363899
theorem B242683 : Blo 239816 242683 := bstep (se 1 (by rfl) ⟨182012, by rfl⟩ : syracuseStep 242683 = 364025) B364025
theorem B242751 : Blo 239816 242751 := bstep (se 1 (by rfl) ⟨182063, by rfl⟩ : syracuseStep 242751 = 364127) B364127
theorem B406633 : Blo 239816 406633 := bstep (se 2 (by rfl) ⟨152487, by rfl⟩ : syracuseStep 406633 = 304975) B304975
theorem B242895 : Blo 239816 242895 := bstep (se 1 (by rfl) ⟨182171, by rfl⟩ : syracuseStep 242895 = 364343) B364343
theorem B6960401 : Blo 239816 6960401 := bstep (se 2 (by rfl) ⟨2610150, by rfl⟩ : syracuseStep 6960401 = 5220301) B5220301
theorem B2962793 : Blo 239816 2962793 := bstep (se 2 (by rfl) ⟨1111047, by rfl⟩ : syracuseStep 2962793 = 2222095) B2222095
theorem B243099 : Blo 239816 243099 := bstep (se 1 (by rfl) ⟨182324, by rfl⟩ : syracuseStep 243099 = 364649) B364649
theorem B2307527 : Blo 239816 2307527 := bstep (se 1 (by rfl) ⟨1730645, by rfl⟩ : syracuseStep 2307527 = 3461291) B3461291
theorem B243311 : Blo 239816 243311 := bstep (se 1 (by rfl) ⟨182483, by rfl⟩ : syracuseStep 243311 = 364967) B364967
theorem B407207 : Blo 239816 407207 := bstep (se 1 (by rfl) ⟨305405, by rfl⟩ : syracuseStep 407207 = 610811) B610811
theorem B243367 : Blo 239816 243367 := bstep (se 1 (by rfl) ⟨182525, by rfl⟩ : syracuseStep 243367 = 365051) B365051
theorem B243451 : Blo 239816 243451 := bstep (se 1 (by rfl) ⟨182588, by rfl⟩ : syracuseStep 243451 = 365177) B365177
theorem B243487 : Blo 239816 243487 := bstep (se 1 (by rfl) ⟨182615, by rfl⟩ : syracuseStep 243487 = 365231) B365231
theorem B3487535 : Blo 239816 3487535 := bstep (se 1 (by rfl) ⟨2615651, by rfl⟩ : syracuseStep 3487535 = 5231303) B5231303
theorem B243519 : Blo 239816 243519 := bstep (se 1 (by rfl) ⟨182639, by rfl⟩ : syracuseStep 243519 = 365279) B365279
theorem B440143 : Blo 239816 440143 := bstep (se 1 (by rfl) ⟨330107, by rfl⟩ : syracuseStep 440143 = 660215) B660215
theorem B1751003 : Blo 239816 1751003 := bstep (se 1 (by rfl) ⟨1313252, by rfl⟩ : syracuseStep 1751003 = 2626505) B2626505
theorem B243695 : Blo 239816 243695 := bstep (se 1 (by rfl) ⟨182771, by rfl⟩ : syracuseStep 243695 = 365543) B365543
theorem B342311 : Blo 239816 342311 := bstep (se 1 (by rfl) ⟨256733, by rfl⟩ : syracuseStep 342311 = 513467) B513467
theorem B407855 : Blo 239816 407855 := bstep (se 1 (by rfl) ⟨305891, by rfl⟩ : syracuseStep 407855 = 611783) B611783
theorem B1849715 : Blo 239816 1849715 := bstep (se 1 (by rfl) ⟨1387286, by rfl⟩ : syracuseStep 1849715 = 2774573) B2774573
theorem B408091 : Blo 239816 408091 := bstep (se 1 (by rfl) ⟨306068, by rfl⟩ : syracuseStep 408091 = 612137) B612137
theorem B866969 : Blo 239816 866969 := bstep (se 2 (by rfl) ⟨325113, by rfl⟩ : syracuseStep 866969 = 650227) B650227
theorem B1227959 : Blo 239816 1227959 := bstep (se 1 (by rfl) ⟨920969, by rfl⟩ : syracuseStep 1227959 = 1841939) B1841939
theorem B540071 : Blo 239816 540071 := bstep (se 1 (by rfl) ⟨405053, by rfl⟩ : syracuseStep 540071 = 810107) B810107
theorem B736723 : Blo 239816 736723 := bstep (se 1 (by rfl) ⟨552542, by rfl⟩ : syracuseStep 736723 = 1105085) B1105085
theorem B409063 : Blo 239816 409063 := bstep (se 1 (by rfl) ⟨306797, by rfl⟩ : syracuseStep 409063 = 613595) B613595
theorem B867847 : Blo 239816 867847 := bstep (se 1 (by rfl) ⟨650885, by rfl⟩ : syracuseStep 867847 = 1301771) B1301771
theorem B409151 : Blo 239816 409151 := bstep (se 1 (by rfl) ⟨306863, by rfl⟩ : syracuseStep 409151 = 613727) B613727
theorem B540251 : Blo 239816 540251 := bstep (se 1 (by rfl) ⟨405188, by rfl⟩ : syracuseStep 540251 = 810377) B810377
theorem B540539 : Blo 239816 540539 := bstep (se 1 (by rfl) ⟨405404, by rfl⟩ : syracuseStep 540539 = 810809) B810809
theorem B343963 : Blo 239816 343963 := bstep (se 1 (by rfl) ⟨257972, by rfl⟩ : syracuseStep 343963 = 515945) B515945
theorem B1163297 : Blo 239816 1163297 := bstep (se 2 (by rfl) ⟨436236, by rfl⟩ : syracuseStep 1163297 = 872473) B872473
theorem B770087 : Blo 239816 770087 := bstep (se 1 (by rfl) ⟨577565, by rfl⟩ : syracuseStep 770087 = 1155131) B1155131
theorem B409819 : Blo 239816 409819 := bstep (se 1 (by rfl) ⟨307364, by rfl⟩ : syracuseStep 409819 = 614729) B614729
theorem B541025 : Blo 239816 541025 := bstep (se 2 (by rfl) ⟨202884, by rfl⟩ : syracuseStep 541025 = 405769) B405769
theorem B541115 : Blo 239816 541115 := bstep (se 1 (by rfl) ⟨405836, by rfl⟩ : syracuseStep 541115 = 811673) B811673
theorem B1229255 : Blo 239816 1229255 := bstep (se 1 (by rfl) ⟨921941, by rfl⟩ : syracuseStep 1229255 = 1843883) B1843883
theorem B410089 : Blo 239816 410089 := bstep (se 2 (by rfl) ⟨153783, by rfl⟩ : syracuseStep 410089 = 307567) B307567
theorem B1032743 : Blo 239816 1032743 := bstep (se 1 (by rfl) ⟨774557, by rfl⟩ : syracuseStep 1032743 = 1549115) B1549115
theorem B1983275 : Blo 239816 1983275 := bstep (se 1 (by rfl) ⟨1487456, by rfl⟩ : syracuseStep 1983275 = 2974913) B2974913
theorem B869231 : Blo 239816 869231 := bstep (se 1 (by rfl) ⟨651923, by rfl⟩ : syracuseStep 869231 = 1303847) B1303847
theorem B2049083 : Blo 239816 2049083 := bstep (se 1 (by rfl) ⟨1536812, by rfl⟩ : syracuseStep 2049083 = 3073625) B3073625
theorem B902249 : Blo 239816 902249 := bstep (se 2 (by rfl) ⟨338343, by rfl⟩ : syracuseStep 902249 = 676687) B676687
theorem B607439 : Blo 239816 607439 := bstep (se 1 (by rfl) ⟨455579, by rfl⟩ : syracuseStep 607439 = 911159) B911159
theorem B2770199 : Blo 239816 2770199 := bstep (se 1 (by rfl) ⟨2077649, by rfl⟩ : syracuseStep 2770199 = 4155299) B4155299
theorem B869705 : Blo 239816 869705 := bstep (se 2 (by rfl) ⟨326139, by rfl⟩ : syracuseStep 869705 = 652279) B652279
theorem B542123 : Blo 239816 542123 := bstep (se 1 (by rfl) ⟨406592, by rfl⟩ : syracuseStep 542123 = 813185) B813185
theorem B607763 : Blo 239816 607763 := bstep (se 1 (by rfl) ⟨455822, by rfl⟩ : syracuseStep 607763 = 911645) B911645
theorem B411257 : Blo 239816 411257 := bstep (se 2 (by rfl) ⟨154221, by rfl⟩ : syracuseStep 411257 = 308443) B308443
theorem B542375 : Blo 239816 542375 := bstep (se 1 (by rfl) ⟨406781, by rfl⟩ : syracuseStep 542375 = 813563) B813563
theorem B280315 : Blo 239816 280315 := bstep (se 1 (by rfl) ⟨210236, by rfl⟩ : syracuseStep 280315 = 420473) B420473
theorem B542663 : Blo 239816 542663 := bstep (se 1 (by rfl) ⟨406997, by rfl⟩ : syracuseStep 542663 = 813995) B813995
theorem B346207 : Blo 239816 346207 := bstep (se 1 (by rfl) ⟨259655, by rfl⟩ : syracuseStep 346207 = 519311) B519311
theorem B936127 : Blo 239816 936127 := bstep (se 1 (by rfl) ⟨702095, by rfl⟩ : syracuseStep 936127 = 1404191) B1404191
theorem B542969 : Blo 239816 542969 := bstep (se 2 (by rfl) ⟨203613, by rfl⟩ : syracuseStep 542969 = 407227) B407227
theorem B543023 : Blo 239816 543023 := bstep (se 1 (by rfl) ⟨407267, by rfl⟩ : syracuseStep 543023 = 814535) B814535
theorem B8604107 : Blo 239816 8604107 := bstep (se 1 (by rfl) ⟨6453080, by rfl⟩ : syracuseStep 8604107 = 12906161) B12906161
theorem B543239 : Blo 239816 543239 := bstep (se 1 (by rfl) ⟨407429, by rfl⟩ : syracuseStep 543239 = 814859) B814859
theorem B543419 : Blo 239816 543419 := bstep (se 1 (by rfl) ⟨407564, by rfl⟩ : syracuseStep 543419 = 815129) B815129
theorem B609079 : Blo 239816 609079 := bstep (se 1 (by rfl) ⟨456809, by rfl⟩ : syracuseStep 609079 = 913619) B913619
theorem B1231847 : Blo 239816 1231847 := bstep (se 1 (by rfl) ⟨923885, by rfl⟩ : syracuseStep 1231847 = 1847771) B1847771
theorem B412895 : Blo 239816 412895 := bstep (se 1 (by rfl) ⟨309671, by rfl⟩ : syracuseStep 412895 = 619343) B619343
theorem B871667 : Blo 239816 871667 := bstep (se 1 (by rfl) ⟨653750, by rfl⟩ : syracuseStep 871667 = 1307501) B1307501
theorem B544247 : Blo 239816 544247 := bstep (se 1 (by rfl) ⟨408185, by rfl⟩ : syracuseStep 544247 = 816371) B816371
theorem B544319 : Blo 239816 544319 := bstep (se 1 (by rfl) ⟨408239, by rfl⟩ : syracuseStep 544319 = 816479) B816479
theorem B3296857 : Blo 239816 3296857 := bstep (se 2 (by rfl) ⟨1236321, by rfl⟩ : syracuseStep 3296857 = 2472643) B2472643
theorem B773993 : Blo 239816 773993 := bstep (se 2 (by rfl) ⟨290247, by rfl⟩ : syracuseStep 773993 = 580495) B580495
theorem B348391 : Blo 239816 348391 := bstep (se 1 (by rfl) ⟨261293, by rfl⟩ : syracuseStep 348391 = 522587) B522587
theorem B1036759 : Blo 239816 1036759 := bstep (se 1 (by rfl) ⟨777569, by rfl⟩ : syracuseStep 1036759 = 1555139) B1555139
theorem B545273 : Blo 239816 545273 := bstep (se 2 (by rfl) ⟨204477, by rfl⟩ : syracuseStep 545273 = 408955) B408955
theorem B1299023 : Blo 239816 1299023 := bstep (se 1 (by rfl) ⟨974267, by rfl⟩ : syracuseStep 1299023 = 1948535) B1948535
theorem B545363 : Blo 239816 545363 := bstep (se 1 (by rfl) ⟨409022, by rfl⟩ : syracuseStep 545363 = 818045) B818045
theorem B545543 : Blo 239816 545543 := bstep (se 1 (by rfl) ⟨409157, by rfl⟩ : syracuseStep 545543 = 818315) B818315
theorem B1037117 : Blo 239816 1037117 := bstep (se 3 (by rfl) ⟨194459, by rfl⟩ : syracuseStep 1037117 = 388919) B388919
theorem B2085851 : Blo 239816 2085851 := bstep (se 1 (by rfl) ⟨1564388, by rfl⟩ : syracuseStep 2085851 = 3128777) B3128777
theorem B294508331 : Blo 239816 294508331 := bstep (se 1 (by rfl) ⟨220881248, by rfl⟩ : syracuseStep 294508331 = 441762497) B441762497
theorem B775993 : Blo 239816 775993 := bstep (se 2 (by rfl) ⟨290997, by rfl⟩ : syracuseStep 775993 = 581995) B581995
theorem B546623 : Blo 239816 546623 := bstep (se 1 (by rfl) ⟨409967, by rfl⟩ : syracuseStep 546623 = 819935) B819935
theorem B2316215 : Blo 239816 2316215 := bstep (se 1 (by rfl) ⟨1737161, by rfl⟩ : syracuseStep 2316215 = 3474323) B3474323
theorem B546911 : Blo 239816 546911 := bstep (se 1 (by rfl) ⟨410183, by rfl⟩ : syracuseStep 546911 = 820367) B820367
theorem B1038491 : Blo 239816 1038491 := bstep (se 1 (by rfl) ⟨778868, by rfl⟩ : syracuseStep 1038491 = 1557737) B1557737
theorem B809405 : Blo 239816 809405 := bstep (se 3 (by rfl) ⟨151763, by rfl⟩ : syracuseStep 809405 = 303527) B303527
theorem B547667 : Blo 239816 547667 := bstep (se 1 (by rfl) ⟨410750, by rfl⟩ : syracuseStep 547667 = 821501) B821501
theorem B810269 : Blo 239816 810269 := bstep (se 3 (by rfl) ⟨151925, by rfl⟩ : syracuseStep 810269 = 303851) B303851
theorem B548207 : Blo 239816 548207 := bstep (se 1 (by rfl) ⟨411155, by rfl⟩ : syracuseStep 548207 = 822311) B822311
theorem B548495 : Blo 239816 548495 := bstep (se 1 (by rfl) ⟨411371, by rfl⟩ : syracuseStep 548495 = 822743) B822743
theorem B548585 : Blo 239816 548585 := bstep (se 2 (by rfl) ⟨205719, by rfl⟩ : syracuseStep 548585 = 411439) B411439
theorem B1171223 : Blo 239816 1171223 := bstep (se 1 (by rfl) ⟨878417, by rfl⟩ : syracuseStep 1171223 = 1756835) B1756835
theorem B876683 : Blo 239816 876683 := bstep (se 1 (by rfl) ⟨657512, by rfl⟩ : syracuseStep 876683 = 1315025) B1315025
theorem B811295 : Blo 239816 811295 := bstep (se 1 (by rfl) ⟨608471, by rfl⟩ : syracuseStep 811295 = 1216943) B1216943
theorem B1041149 : Blo 239816 1041149 := bstep (se 3 (by rfl) ⟨195215, by rfl⟩ : syracuseStep 1041149 = 390431) B390431
theorem B779017 : Blo 239816 779017 := bstep (se 2 (by rfl) ⟨292131, by rfl⟩ : syracuseStep 779017 = 584263) B584263
theorem B615215 : Blo 239816 615215 := bstep (se 1 (by rfl) ⟨461411, by rfl⟩ : syracuseStep 615215 = 922823) B922823
theorem B40035221 : Blo 239816 40035221 := bstep (se 6 (by rfl) ⟨938325, by rfl⟩ : syracuseStep 40035221 = 1876651) B1876651
theorem B811943 : Blo 239816 811943 := bstep (se 1 (by rfl) ⟨608957, by rfl⟩ : syracuseStep 811943 = 1217915) B1217915
theorem B779453 : Blo 239816 779453 := bstep (se 3 (by rfl) ⟨146147, by rfl⟩ : syracuseStep 779453 = 292295) B292295
theorem B386459 : Blo 239816 386459 := bstep (se 1 (by rfl) ⟨289844, by rfl⟩ : syracuseStep 386459 = 579689) B579689
theorem B13297097 : Blo 239816 13297097 := bstep (se 2 (by rfl) ⟨4986411, by rfl⟩ : syracuseStep 13297097 = 9972823) B9972823
theorem B812537 : Blo 239816 812537 := bstep (se 2 (by rfl) ⟨304701, by rfl⟩ : syracuseStep 812537 = 609403) B609403
theorem B812807 : Blo 239816 812807 := bstep (se 1 (by rfl) ⟨609605, by rfl⟩ : syracuseStep 812807 = 1219211) B1219211
theorem B812861 : Blo 239816 812861 := bstep (se 3 (by rfl) ⟨152411, by rfl⟩ : syracuseStep 812861 = 304823) B304823
theorem B3106633 : Blo 239816 3106633 := bstep (se 2 (by rfl) ⟨1164987, by rfl⟩ : syracuseStep 3106633 = 2329975) B2329975
theorem B780479 : Blo 239816 780479 := bstep (se 1 (by rfl) ⟨585359, by rfl⟩ : syracuseStep 780479 = 1170719) B1170719
theorem B682219 : Blo 239816 682219 := bstep (se 1 (by rfl) ⟨511664, by rfl⟩ : syracuseStep 682219 = 1023329) B1023329
theorem B551329 : Blo 239816 551329 := bstep (se 2 (by rfl) ⟨206748, by rfl⟩ : syracuseStep 551329 = 413497) B413497
theorem B23685605 : Blo 239816 23685605 := bstep (se 4 (by rfl) ⟨2220525, by rfl⟩ : syracuseStep 23685605 = 4441051) B4441051
theorem B2779643 : Blo 239816 2779643 := bstep (se 1 (by rfl) ⟨2084732, by rfl⟩ : syracuseStep 2779643 = 4169465) B4169465
theorem B616967 : Blo 239816 616967 := bstep (se 1 (by rfl) ⟨462725, by rfl⟩ : syracuseStep 616967 = 925451) B925451
theorem B912617 : Blo 239816 912617 := bstep (se 2 (by rfl) ⟨342231, by rfl⟩ : syracuseStep 912617 = 684463) B684463
theorem B1437257 : Blo 239816 1437257 := bstep (se 2 (by rfl) ⟨538971, by rfl⟩ : syracuseStep 1437257 = 1077943) B1077943
theorem B815291 : Blo 239816 815291 := bstep (se 1 (by rfl) ⟨611468, by rfl⟩ : syracuseStep 815291 = 1222937) B1222937
theorem B3076289 : Blo 239816 3076289 := bstep (se 2 (by rfl) ⟨1153608, by rfl⟩ : syracuseStep 3076289 = 2307217) B2307217
theorem B913801 : Blo 239816 913801 := bstep (se 2 (by rfl) ⟨342675, by rfl⟩ : syracuseStep 913801 = 685351) B685351
theorem B815777 : Blo 239816 815777 := bstep (se 2 (by rfl) ⟨305916, by rfl⟩ : syracuseStep 815777 = 611833) B611833
theorem B389867 : Blo 239816 389867 := bstep (se 1 (by rfl) ⟨292400, by rfl⟩ : syracuseStep 389867 = 584801) B584801
theorem B1733471 : Blo 239816 1733471 := bstep (se 1 (by rfl) ⟨1300103, by rfl⟩ : syracuseStep 1733471 = 2600207) B2600207
theorem B1536893 : Blo 239816 1536893 := bstep (se 3 (by rfl) ⟨288167, by rfl⟩ : syracuseStep 1536893 = 576335) B576335
theorem B554195 : Blo 239816 554195 := bstep (se 1 (by rfl) ⟨415646, by rfl⟩ : syracuseStep 554195 = 831293) B831293
theorem B816641 : Blo 239816 816641 := bstep (se 2 (by rfl) ⟨306240, by rfl⟩ : syracuseStep 816641 = 612481) B612481
theorem B456263 : Blo 239816 456263 := bstep (se 1 (by rfl) ⟨342197, by rfl⟩ : syracuseStep 456263 = 684395) B684395
theorem B685739 : Blo 239816 685739 := bstep (se 1 (by rfl) ⟨514304, by rfl⟩ : syracuseStep 685739 = 1028609) B1028609
theorem B817127 : Blo 239816 817127 := bstep (se 1 (by rfl) ⟨612845, by rfl⟩ : syracuseStep 817127 = 1225691) B1225691
theorem B817235 : Blo 239816 817235 := bstep (se 1 (by rfl) ⟨612926, by rfl⟩ : syracuseStep 817235 = 1225853) B1225853
theorem B817451 : Blo 239816 817451 := bstep (se 1 (by rfl) ⟨613088, by rfl⟩ : syracuseStep 817451 = 1226177) B1226177
theorem B817721 : Blo 239816 817721 := bstep (se 2 (by rfl) ⟨306645, by rfl⟩ : syracuseStep 817721 = 613291) B613291
theorem B1375055 : Blo 239816 1375055 := bstep (se 1 (by rfl) ⟨1031291, by rfl⟩ : syracuseStep 1375055 = 2062583) B2062583
theorem B1571663 : Blo 239816 1571663 := bstep (se 1 (by rfl) ⟨1178747, by rfl⟩ : syracuseStep 1571663 = 2357495) B2357495
theorem B359759 : Blo 239816 359759 := bstep (se 1 (by rfl) ⟨269819, by rfl⟩ : syracuseStep 359759 = 539639) B539639
theorem B359849 : Blo 239816 359849 := bstep (se 2 (by rfl) ⟨134943, by rfl⟩ : syracuseStep 359849 = 269887) B269887
theorem B1539557 : Blo 239816 1539557 := bstep (se 4 (by rfl) ⟨144333, by rfl⟩ : syracuseStep 1539557 = 288667) B288667
theorem B359999 : Blo 239816 359999 := bstep (se 1 (by rfl) ⟨269999, by rfl⟩ : syracuseStep 359999 = 539999) B539999
theorem B458473 : Blo 239816 458473 := bstep (se 2 (by rfl) ⟨171927, by rfl⟩ : syracuseStep 458473 = 343855) B343855
theorem B360263 : Blo 239816 360263 := bstep (se 1 (by rfl) ⟨270197, by rfl⟩ : syracuseStep 360263 = 540395) B540395
theorem B360347 : Blo 239816 360347 := bstep (se 1 (by rfl) ⟨270260, by rfl⟩ : syracuseStep 360347 = 540521) B540521
theorem B917689 : Blo 239816 917689 := bstep (se 2 (by rfl) ⟨344133, by rfl⟩ : syracuseStep 917689 = 688267) B688267
theorem B360683 : Blo 239816 360683 := bstep (se 1 (by rfl) ⟨270512, by rfl⟩ : syracuseStep 360683 = 541025) B541025
theorem B4129055 : Blo 239816 4129055 := bstep (se 1 (by rfl) ⟨3096791, by rfl⟩ : syracuseStep 4129055 = 6193583) B6193583
theorem B360743 : Blo 239816 360743 := bstep (se 1 (by rfl) ⟨270557, by rfl⟩ : syracuseStep 360743 = 541115) B541115
theorem B819503 : Blo 239816 819503 := bstep (se 1 (by rfl) ⟨614627, by rfl⟩ : syracuseStep 819503 = 1229255) B1229255
theorem B688495 : Blo 239816 688495 := bstep (se 1 (by rfl) ⟨516371, by rfl⟩ : syracuseStep 688495 = 1032743) B1032743
theorem B2490743 : Blo 239816 2490743 := bstep (se 1 (by rfl) ⟨1868057, by rfl⟩ : syracuseStep 2490743 = 3736115) B3736115
theorem B459179 : Blo 239816 459179 := bstep (se 1 (by rfl) ⟨344384, by rfl⟩ : syracuseStep 459179 = 688769) B688769
theorem B328303 : Blo 239816 328303 := bstep (se 1 (by rfl) ⟨246227, by rfl⟩ : syracuseStep 328303 = 492455) B492455
theorem B361415 : Blo 239816 361415 := bstep (se 1 (by rfl) ⟨271061, by rfl⟩ : syracuseStep 361415 = 542123) B542123
theorem B361583 : Blo 239816 361583 := bstep (se 1 (by rfl) ⟨271187, by rfl⟩ : syracuseStep 361583 = 542375) B542375
theorem B361775 : Blo 239816 361775 := bstep (se 1 (by rfl) ⟨271331, by rfl⟩ : syracuseStep 361775 = 542663) B542663
theorem B361979 : Blo 239816 361979 := bstep (se 1 (by rfl) ⟨271484, by rfl⟩ : syracuseStep 361979 = 542969) B542969
theorem B362015 : Blo 239816 362015 := bstep (se 1 (by rfl) ⟨271511, by rfl⟩ : syracuseStep 362015 = 543023) B543023
theorem B5736071 : Blo 239816 5736071 := bstep (se 1 (by rfl) ⟨4302053, by rfl⟩ : syracuseStep 5736071 = 8604107) B8604107
theorem B362159 : Blo 239816 362159 := bstep (se 1 (by rfl) ⟨271619, by rfl⟩ : syracuseStep 362159 = 543239) B543239
theorem B362279 : Blo 239816 362279 := bstep (se 1 (by rfl) ⟨271709, by rfl⟩ : syracuseStep 362279 = 543419) B543419
theorem B821231 : Blo 239816 821231 := bstep (se 1 (by rfl) ⟨615923, by rfl⟩ : syracuseStep 821231 = 1231847) B1231847
theorem B1411181 : Blo 239816 1411181 := bstep (se 3 (by rfl) ⟨264596, by rfl⟩ : syracuseStep 1411181 = 529193) B529193
theorem B362831 : Blo 239816 362831 := bstep (se 1 (by rfl) ⟨272123, by rfl⟩ : syracuseStep 362831 = 544247) B544247
theorem B362879 : Blo 239816 362879 := bstep (se 1 (by rfl) ⟨272159, by rfl⟩ : syracuseStep 362879 = 544319) B544319
theorem B362921 : Blo 239816 362921 := bstep (se 2 (by rfl) ⟨136095, by rfl⟩ : syracuseStep 362921 = 272191) B272191
theorem B363305 : Blo 239816 363305 := bstep (se 2 (by rfl) ⟨136239, by rfl⟩ : syracuseStep 363305 = 272479) B272479
theorem B461609 : Blo 239816 461609 := bstep (se 2 (by rfl) ⟨173103, by rfl⟩ : syracuseStep 461609 = 346207) B346207
theorem B1248169 : Blo 239816 1248169 := bstep (se 2 (by rfl) ⟨468063, by rfl⟩ : syracuseStep 1248169 = 936127) B936127
theorem B363515 : Blo 239816 363515 := bstep (se 1 (by rfl) ⟨272636, by rfl⟩ : syracuseStep 363515 = 545273) B545273
theorem B363575 : Blo 239816 363575 := bstep (se 1 (by rfl) ⟨272681, by rfl⟩ : syracuseStep 363575 = 545363) B545363
theorem B363695 : Blo 239816 363695 := bstep (se 1 (by rfl) ⟨272771, by rfl⟩ : syracuseStep 363695 = 545543) B545543
theorem B691411 : Blo 239816 691411 := bstep (se 1 (by rfl) ⟨518558, by rfl⟩ : syracuseStep 691411 = 1037117) B1037117
theorem B2624993 : Blo 239816 2624993 := bstep (se 2 (by rfl) ⟨984372, by rfl⟩ : syracuseStep 2624993 = 1968745) B1968745
theorem B6622715 : Blo 239816 6622715 := bstep (se 1 (by rfl) ⟨4967036, by rfl⟩ : syracuseStep 6622715 = 9934073) B9934073
theorem B364415 : Blo 239816 364415 := bstep (se 1 (by rfl) ⟨273311, by rfl⟩ : syracuseStep 364415 = 546623) B546623
theorem B1544143 : Blo 239816 1544143 := bstep (se 1 (by rfl) ⟨1158107, by rfl⟩ : syracuseStep 1544143 = 2316215) B2316215
theorem B2101297 : Blo 239816 2101297 := bstep (se 2 (by rfl) ⟨787986, by rfl⟩ : syracuseStep 2101297 = 1575973) B1575973
theorem B364607 : Blo 239816 364607 := bstep (se 1 (by rfl) ⟨273455, by rfl⟩ : syracuseStep 364607 = 546911) B546911
theorem B692327 : Blo 239816 692327 := bstep (se 1 (by rfl) ⟨519245, by rfl⟩ : syracuseStep 692327 = 1038491) B1038491
theorem B3936509 : Blo 239816 3936509 := bstep (se 3 (by rfl) ⟨738095, by rfl⟩ : syracuseStep 3936509 = 1476191) B1476191
theorem B364841 : Blo 239816 364841 := bstep (se 2 (by rfl) ⟨136815, by rfl⟩ : syracuseStep 364841 = 273631) B273631
theorem B365111 : Blo 239816 365111 := bstep (se 1 (by rfl) ⟨273833, by rfl⟩ : syracuseStep 365111 = 547667) B547667
theorem B4395809 : Blo 239816 4395809 := bstep (se 2 (by rfl) ⟨1648428, by rfl⟩ : syracuseStep 4395809 = 3296857) B3296857
theorem B365471 : Blo 239816 365471 := bstep (se 1 (by rfl) ⟨274103, by rfl⟩ : syracuseStep 365471 = 548207) B548207
theorem B2233327 : Blo 239816 2233327 := bstep (se 1 (by rfl) ⟨1674995, by rfl⟩ : syracuseStep 2233327 = 3349991) B3349991
theorem B365663 : Blo 239816 365663 := bstep (se 1 (by rfl) ⟨274247, by rfl⟩ : syracuseStep 365663 = 548495) B548495
theorem B365723 : Blo 239816 365723 := bstep (se 1 (by rfl) ⟨274292, by rfl⟩ : syracuseStep 365723 = 548585) B548585
theorem B923035 : Blo 239816 923035 := bstep (se 1 (by rfl) ⟨692276, by rfl⟩ : syracuseStep 923035 = 1384553) B1384553
theorem B15832493 : Blo 239816 15832493 := bstep (se 3 (by rfl) ⟨2968592, by rfl⟩ : syracuseStep 15832493 = 5937185) B5937185
theorem B694099 : Blo 239816 694099 := bstep (se 1 (by rfl) ⟨520574, by rfl⟩ : syracuseStep 694099 = 1041149) B1041149
theorem B1218401 : Blo 239816 1218401 := bstep (se 2 (by rfl) ⟨456900, by rfl⟩ : syracuseStep 1218401 = 913801) B913801
theorem B2758535 : Blo 239816 2758535 := bstep (se 1 (by rfl) ⟨2068901, by rfl⟩ : syracuseStep 2758535 = 4137803) B4137803
theorem B1382345 : Blo 239816 1382345 := bstep (se 2 (by rfl) ⟨518379, by rfl⟩ : syracuseStep 1382345 = 1036759) B1036759
theorem B7412381 : Blo 239816 7412381 := bstep (se 3 (by rfl) ⟨1389821, by rfl⟩ : syracuseStep 7412381 = 2779643) B2779643
theorem B1383095 : Blo 239816 1383095 := bstep (se 1 (by rfl) ⟨1037321, by rfl⟩ : syracuseStep 1383095 = 2074643) B2074643
theorem B2104031 : Blo 239816 2104031 := bstep (se 1 (by rfl) ⟨1578023, by rfl⟩ : syracuseStep 2104031 = 3156047) B3156047
theorem B1842425 : Blo 239816 1842425 := bstep (se 2 (by rfl) ⟨690909, by rfl⟩ : syracuseStep 1842425 = 1381819) B1381819
theorem B958171 : Blo 239816 958171 := bstep (se 1 (by rfl) ⟨718628, by rfl⟩ : syracuseStep 958171 = 1437257) B1437257
theorem B270247 : Blo 239816 270247 := bstep (se 1 (by rfl) ⟨202685, by rfl⟩ : syracuseStep 270247 = 405371) B405371
theorem B5906519 : Blo 239816 5906519 := bstep (se 1 (by rfl) ⟨4429889, by rfl⟩ : syracuseStep 5906519 = 8859779) B8859779
theorem B1155647 : Blo 239816 1155647 := bstep (se 1 (by rfl) ⟨866735, by rfl⟩ : syracuseStep 1155647 = 1733471) B1733471
theorem B1024595 : Blo 239816 1024595 := bstep (se 1 (by rfl) ⟨768446, by rfl⟩ : syracuseStep 1024595 = 1536893) B1536893
theorem B369463 : Blo 239816 369463 := bstep (se 1 (by rfl) ⟨277097, by rfl⟩ : syracuseStep 369463 = 554195) B554195
theorem B1975195 : Blo 239816 1975195 := bstep (se 1 (by rfl) ⟨1481396, by rfl⟩ : syracuseStep 1975195 = 2962793) B2962793
theorem B304175 : Blo 239816 304175 := bstep (se 1 (by rfl) ⟨228131, by rfl⟩ : syracuseStep 304175 = 456263) B456263
theorem B271471 : Blo 239816 271471 := bstep (se 1 (by rfl) ⟨203603, by rfl⟩ : syracuseStep 271471 = 407207) B407207
theorem B1844369 : Blo 239816 1844369 := bstep (se 2 (by rfl) ⟨691638, by rfl⟩ : syracuseStep 1844369 = 1383277) B1383277
theorem B271903 : Blo 239816 271903 := bstep (se 1 (by rfl) ⟨203927, by rfl⟩ : syracuseStep 271903 = 407855) B407855
theorem B1157129 : Blo 239816 1157129 := bstep (se 2 (by rfl) ⟨433923, by rfl⟩ : syracuseStep 1157129 = 867847) B867847
theorem B239839 : Blo 239816 239839 := bstep (se 1 (by rfl) ⟨179879, by rfl⟩ : syracuseStep 239839 = 359759) B359759
theorem B239899 : Blo 239816 239899 := bstep (se 1 (by rfl) ⟨179924, by rfl⟩ : syracuseStep 239899 = 359849) B359849
theorem B1026371 : Blo 239816 1026371 := bstep (se 1 (by rfl) ⟨769778, by rfl⟩ : syracuseStep 1026371 = 1539557) B1539557
theorem B239999 : Blo 239816 239999 := bstep (se 1 (by rfl) ⟨179999, by rfl⟩ : syracuseStep 239999 = 359999) B359999
theorem B272767 : Blo 239816 272767 := bstep (se 1 (by rfl) ⟨204575, by rfl⟩ : syracuseStep 272767 = 409151) B409151
theorem B240175 : Blo 239816 240175 := bstep (se 1 (by rfl) ⟨180131, by rfl⟩ : syracuseStep 240175 = 360263) B360263
theorem B240231 : Blo 239816 240231 := bstep (se 1 (by rfl) ⟨180173, by rfl⟩ : syracuseStep 240231 = 360347) B360347
theorem B240607 : Blo 239816 240607 := bstep (se 1 (by rfl) ⟨180455, by rfl⟩ : syracuseStep 240607 = 360911) B360911
theorem B240635 : Blo 239816 240635 := bstep (se 1 (by rfl) ⟨180476, by rfl⟩ : syracuseStep 240635 = 360953) B360953
theorem B2337821 : Blo 239816 2337821 := bstep (se 3 (by rfl) ⟨438341, by rfl⟩ : syracuseStep 2337821 = 876683) B876683
theorem B1846313 : Blo 239816 1846313 := bstep (se 2 (by rfl) ⟨692367, by rfl⟩ : syracuseStep 1846313 = 1384735) B1384735
theorem B240703 : Blo 239816 240703 := bstep (se 1 (by rfl) ⟨180527, by rfl⟩ : syracuseStep 240703 = 361055) B361055
theorem B1322183 : Blo 239816 1322183 := bstep (se 1 (by rfl) ⟨991637, by rfl⟩ : syracuseStep 1322183 = 1983275) B1983275
theorem B1748233 : Blo 239816 1748233 := bstep (se 2 (by rfl) ⟨655587, by rfl⟩ : syracuseStep 1748233 = 1311175) B1311175
theorem B241023 : Blo 239816 241023 := bstep (se 1 (by rfl) ⟨180767, by rfl⟩ : syracuseStep 241023 = 361535) B361535
theorem B601499 : Blo 239816 601499 := bstep (se 1 (by rfl) ⟨451124, by rfl⟩ : syracuseStep 601499 = 902249) B902249
theorem B241051 : Blo 239816 241051 := bstep (se 1 (by rfl) ⟨180788, by rfl⟩ : syracuseStep 241051 = 361577) B361577
theorem B404959 : Blo 239816 404959 := bstep (se 1 (by rfl) ⟨303719, by rfl⟩ : syracuseStep 404959 = 607439) B607439
theorem B241119 : Blo 239816 241119 := bstep (se 1 (by rfl) ⟨180839, by rfl⟩ : syracuseStep 241119 = 361679) B361679
theorem B1846799 : Blo 239816 1846799 := bstep (se 1 (by rfl) ⟨1385099, by rfl⟩ : syracuseStep 1846799 = 2770199) B2770199
theorem B241255 : Blo 239816 241255 := bstep (se 1 (by rfl) ⟨180941, by rfl⟩ : syracuseStep 241255 = 361883) B361883
theorem B405175 : Blo 239816 405175 := bstep (se 1 (by rfl) ⟨303881, by rfl⟩ : syracuseStep 405175 = 607763) B607763
theorem B241403 : Blo 239816 241403 := bstep (se 1 (by rfl) ⟨181052, by rfl⟩ : syracuseStep 241403 = 362105) B362105
theorem B274171 : Blo 239816 274171 := bstep (se 1 (by rfl) ⟨205628, by rfl⟩ : syracuseStep 274171 = 411257) B411257
theorem B241471 : Blo 239816 241471 := bstep (se 1 (by rfl) ⟨181103, by rfl⟩ : syracuseStep 241471 = 362207) B362207
theorem B241535 : Blo 239816 241535 := bstep (se 1 (by rfl) ⟨181151, by rfl⟩ : syracuseStep 241535 = 362303) B362303
theorem B1028011 : Blo 239816 1028011 := bstep (se 1 (by rfl) ⟨771008, by rfl⟩ : syracuseStep 1028011 = 1542017) B1542017
theorem B241647 : Blo 239816 241647 := bstep (se 1 (by rfl) ⟨181235, by rfl⟩ : syracuseStep 241647 = 362471) B362471
theorem B241659 : Blo 239816 241659 := bstep (se 1 (by rfl) ⟨181244, by rfl⟩ : syracuseStep 241659 = 362489) B362489
theorem B241727 : Blo 239816 241727 := bstep (se 1 (by rfl) ⟨181295, by rfl⟩ : syracuseStep 241727 = 362591) B362591
theorem B2338895 : Blo 239816 2338895 := bstep (se 1 (by rfl) ⟨1754171, by rfl⟩ : syracuseStep 2338895 = 3508343) B3508343
theorem B241767 : Blo 239816 241767 := bstep (se 1 (by rfl) ⟨181325, by rfl⟩ : syracuseStep 241767 = 362651) B362651
theorem B241791 : Blo 239816 241791 := bstep (se 1 (by rfl) ⟨181343, by rfl⟩ : syracuseStep 241791 = 362687) B362687
theorem B241819 : Blo 239816 241819 := bstep (se 1 (by rfl) ⟨181364, by rfl⟩ : syracuseStep 241819 = 362729) B362729
theorem B242023 : Blo 239816 242023 := bstep (se 1 (by rfl) ⟨181517, by rfl⟩ : syracuseStep 242023 = 363035) B363035
theorem B242075 : Blo 239816 242075 := bstep (se 1 (by rfl) ⟨181556, by rfl⟩ : syracuseStep 242075 = 363113) B363113
theorem B242427 : Blo 239816 242427 := bstep (se 1 (by rfl) ⟨181820, by rfl⟩ : syracuseStep 242427 = 363641) B363641
theorem B1553215 : Blo 239816 1553215 := bstep (se 1 (by rfl) ⟨1164911, by rfl⟩ : syracuseStep 1553215 = 2329823) B2329823
theorem B242495 : Blo 239816 242495 := bstep (se 1 (by rfl) ⟨181871, by rfl⟩ : syracuseStep 242495 = 363743) B363743
theorem B242523 : Blo 239816 242523 := bstep (se 1 (by rfl) ⟨181892, by rfl⟩ : syracuseStep 242523 = 363785) B363785
theorem B242591 : Blo 239816 242591 := bstep (se 1 (by rfl) ⟨181943, by rfl⟩ : syracuseStep 242591 = 363887) B363887
theorem B242671 : Blo 239816 242671 := bstep (se 1 (by rfl) ⟨182003, by rfl⟩ : syracuseStep 242671 = 364007) B364007
theorem B373753 : Blo 239816 373753 := bstep (se 2 (by rfl) ⟨140157, by rfl⟩ : syracuseStep 373753 = 280315) B280315
theorem B242759 : Blo 239816 242759 := bstep (se 1 (by rfl) ⟨182069, by rfl⟩ : syracuseStep 242759 = 364139) B364139
theorem B4142177 : Blo 239816 4142177 := bstep (se 2 (by rfl) ⟨1553316, by rfl⟩ : syracuseStep 4142177 = 3106633) B3106633
theorem B242843 : Blo 239816 242843 := bstep (se 1 (by rfl) ⟨182132, by rfl⟩ : syracuseStep 242843 = 364265) B364265
theorem B242939 : Blo 239816 242939 := bstep (se 1 (by rfl) ⟨182204, by rfl⟩ : syracuseStep 242939 = 364409) B364409
theorem B243007 : Blo 239816 243007 := bstep (se 1 (by rfl) ⟨182255, by rfl⟩ : syracuseStep 243007 = 364511) B364511
theorem B243175 : Blo 239816 243175 := bstep (se 1 (by rfl) ⟨182381, by rfl⟩ : syracuseStep 243175 = 364763) B364763
theorem B243183 : Blo 239816 243183 := bstep (se 1 (by rfl) ⟨182387, by rfl⟩ : syracuseStep 243183 = 364775) B364775
theorem B243291 : Blo 239816 243291 := bstep (se 1 (by rfl) ⟨182468, by rfl⟩ : syracuseStep 243291 = 364937) B364937
theorem B243355 : Blo 239816 243355 := bstep (se 1 (by rfl) ⟨182516, by rfl⟩ : syracuseStep 243355 = 365033) B365033
theorem B866015 : Blo 239816 866015 := bstep (se 1 (by rfl) ⟨649511, by rfl⟩ : syracuseStep 866015 = 1299023) B1299023
theorem B243439 : Blo 239816 243439 := bstep (se 1 (by rfl) ⟨182579, by rfl⟩ : syracuseStep 243439 = 365159) B365159
theorem B243527 : Blo 239816 243527 := bstep (se 1 (by rfl) ⟨182645, by rfl⟩ : syracuseStep 243527 = 365291) B365291
theorem B243547 : Blo 239816 243547 := bstep (se 1 (by rfl) ⟨182660, by rfl⟩ : syracuseStep 243547 = 365321) B365321
theorem B243615 : Blo 239816 243615 := bstep (se 1 (by rfl) ⟨182711, by rfl⟩ : syracuseStep 243615 = 365423) B365423
theorem B1390567 : Blo 239816 1390567 := bstep (se 1 (by rfl) ⟨1042925, by rfl⟩ : syracuseStep 1390567 = 2085851) B2085851
theorem B243783 : Blo 239816 243783 := bstep (se 1 (by rfl) ⟨182837, by rfl⟩ : syracuseStep 243783 = 365675) B365675
theorem B1030283 : Blo 239816 1030283 := bstep (se 1 (by rfl) ⟨772712, by rfl⟩ : syracuseStep 1030283 = 1545425) B1545425
theorem B539603 : Blo 239816 539603 := bstep (se 1 (by rfl) ⟨404702, by rfl⟩ : syracuseStep 539603 = 809405) B809405
theorem B539873 : Blo 239816 539873 := bstep (se 2 (by rfl) ⟨202452, by rfl⟩ : syracuseStep 539873 = 404905) B404905
theorem B2080079 : Blo 239816 2080079 := bstep (se 1 (by rfl) ⟨1560059, by rfl⟩ : syracuseStep 2080079 = 3120119) B3120119
theorem B4963751 : Blo 239816 4963751 := bstep (se 1 (by rfl) ⟨3722813, by rfl⟩ : syracuseStep 4963751 = 7445627) B7445627
theorem B540179 : Blo 239816 540179 := bstep (se 1 (by rfl) ⟨405134, by rfl⟩ : syracuseStep 540179 = 810269) B810269
theorem B540863 : Blo 239816 540863 := bstep (se 1 (by rfl) ⟨405647, by rfl⟩ : syracuseStep 540863 = 811295) B811295
theorem B1163645 : Blo 239816 1163645 := bstep (se 3 (by rfl) ⟨218183, by rfl⟩ : syracuseStep 1163645 = 436367) B436367
theorem B410143 : Blo 239816 410143 := bstep (se 1 (by rfl) ⟨307607, by rfl⟩ : syracuseStep 410143 = 615215) B615215
theorem B26690147 : Blo 239816 26690147 := bstep (se 1 (by rfl) ⟨20017610, by rfl⟩ : syracuseStep 26690147 = 40035221) B40035221
theorem B541295 : Blo 239816 541295 := bstep (se 1 (by rfl) ⟨405971, by rfl⟩ : syracuseStep 541295 = 811943) B811943
theorem B2474819 : Blo 239816 2474819 := bstep (se 1 (by rfl) ⟨1856114, by rfl⟩ : syracuseStep 2474819 = 3712229) B3712229
theorem B8864731 : Blo 239816 8864731 := bstep (se 1 (by rfl) ⟨6648548, by rfl⟩ : syracuseStep 8864731 = 13297097) B13297097
theorem B541691 : Blo 239816 541691 := bstep (se 1 (by rfl) ⟨406268, by rfl⟩ : syracuseStep 541691 = 812537) B812537
theorem B541871 : Blo 239816 541871 := bstep (se 1 (by rfl) ⟨406403, by rfl⟩ : syracuseStep 541871 = 812807) B812807
theorem B541907 : Blo 239816 541907 := bstep (se 1 (by rfl) ⟨406430, by rfl⟩ : syracuseStep 541907 = 812861) B812861
theorem B247087 : Blo 239816 247087 := bstep (se 1 (by rfl) ⟨185315, by rfl⟩ : syracuseStep 247087 = 370631) B370631
theorem B542177 : Blo 239816 542177 := bstep (se 2 (by rfl) ⟨203316, by rfl⟩ : syracuseStep 542177 = 406633) B406633
theorem B411311 : Blo 239816 411311 := bstep (se 1 (by rfl) ⟨308483, by rfl⟩ : syracuseStep 411311 = 616967) B616967
theorem B1099777 : Blo 239816 1099777 := bstep (se 2 (by rfl) ⟨412416, by rfl⟩ : syracuseStep 1099777 = 824833) B824833
theorem B608411 : Blo 239816 608411 := bstep (se 1 (by rfl) ⟨456308, by rfl⟩ : syracuseStep 608411 = 912617) B912617
theorem B1034657 : Blo 239816 1034657 := bstep (se 2 (by rfl) ⟨387996, by rfl⟩ : syracuseStep 1034657 = 775993) B775993
theorem B543527 : Blo 239816 543527 := bstep (se 1 (by rfl) ⟨407645, by rfl⟩ : syracuseStep 543527 = 815291) B815291
theorem B2050859 : Blo 239816 2050859 := bstep (se 1 (by rfl) ⟨1538144, by rfl⟩ : syracuseStep 2050859 = 3076289) B3076289
theorem B1821527 : Blo 239816 1821527 := bstep (se 1 (by rfl) ⟨1366145, by rfl⟩ : syracuseStep 1821527 = 2732291) B2732291
theorem B904171 : Blo 239816 904171 := bstep (se 1 (by rfl) ⟨678128, by rfl⟩ : syracuseStep 904171 = 1356257) B1356257
theorem B1035271 : Blo 239816 1035271 := bstep (se 1 (by rfl) ⟨776453, by rfl⟩ : syracuseStep 1035271 = 1552907) B1552907
theorem B543851 : Blo 239816 543851 := bstep (se 1 (by rfl) ⟨407888, by rfl⟩ : syracuseStep 543851 = 815777) B815777
theorem B3656927 : Blo 239816 3656927 := bstep (se 1 (by rfl) ⟨2742695, by rfl⟩ : syracuseStep 3656927 = 5485391) B5485391
theorem B1101053 : Blo 239816 1101053 := bstep (se 3 (by rfl) ⟨206447, by rfl⟩ : syracuseStep 1101053 = 412895) B412895
theorem B544121 : Blo 239816 544121 := bstep (se 2 (by rfl) ⟨204045, by rfl⟩ : syracuseStep 544121 = 408091) B408091
theorem B4115933 : Blo 239816 4115933 := bstep (se 3 (by rfl) ⟨771737, by rfl⟩ : syracuseStep 4115933 = 1543475) B1543475
theorem B4640267 : Blo 239816 4640267 := bstep (se 1 (by rfl) ⟨3480200, by rfl⟩ : syracuseStep 4640267 = 6960401) B6960401
theorem B544427 : Blo 239816 544427 := bstep (se 1 (by rfl) ⟨408320, by rfl⟩ : syracuseStep 544427 = 816641) B816641
theorem B1167335 : Blo 239816 1167335 := bstep (se 1 (by rfl) ⟨875501, by rfl⟩ : syracuseStep 1167335 = 1751003) B1751003
theorem B544751 : Blo 239816 544751 := bstep (se 1 (by rfl) ⟨408563, by rfl⟩ : syracuseStep 544751 = 817127) B817127
theorem B544823 : Blo 239816 544823 := bstep (se 1 (by rfl) ⟨408617, by rfl⟩ : syracuseStep 544823 = 817235) B817235
theorem B544967 : Blo 239816 544967 := bstep (se 1 (by rfl) ⟨408725, by rfl⟩ : syracuseStep 544967 = 817451) B817451
theorem B1233143 : Blo 239816 1233143 := bstep (se 1 (by rfl) ⟨924857, by rfl⟩ : syracuseStep 1233143 = 1849715) B1849715
theorem B545147 : Blo 239816 545147 := bstep (se 1 (by rfl) ⟨408860, by rfl⟩ : syracuseStep 545147 = 817721) B817721
theorem B2347429 : Blo 239816 2347429 := bstep (se 4 (by rfl) ⟨220071, by rfl⟩ : syracuseStep 2347429 = 440143) B440143
theorem B577979 : Blo 239816 577979 := bstep (se 1 (by rfl) ⟨433484, by rfl⟩ : syracuseStep 577979 = 866969) B866969
theorem B545417 : Blo 239816 545417 := bstep (se 2 (by rfl) ⟨204531, by rfl⟩ : syracuseStep 545417 = 409063) B409063
theorem B1233629 : Blo 239816 1233629 := bstep (se 3 (by rfl) ⟨231305, by rfl⟩ : syracuseStep 1233629 = 462611) B462611
theorem B611297 : Blo 239816 611297 := bstep (se 2 (by rfl) ⟨229236, by rfl⟩ : syracuseStep 611297 = 458473) B458473
theorem B775531 : Blo 239816 775531 := bstep (se 1 (by rfl) ⟨581648, by rfl⟩ : syracuseStep 775531 = 1163297) B1163297
theorem B546155 : Blo 239816 546155 := bstep (se 1 (by rfl) ⟨409616, by rfl⟩ : syracuseStep 546155 = 819233) B819233
theorem B513391 : Blo 239816 513391 := bstep (se 1 (by rfl) ⟨385043, by rfl⟩ : syracuseStep 513391 = 770087) B770087
theorem B546425 : Blo 239816 546425 := bstep (se 2 (by rfl) ⟨204909, by rfl⟩ : syracuseStep 546425 = 409819) B409819
theorem B2053835 : Blo 239816 2053835 := bstep (se 1 (by rfl) ⟨1540376, by rfl⟩ : syracuseStep 2053835 = 3080753) B3080753
theorem B579487 : Blo 239816 579487 := bstep (se 1 (by rfl) ⟨434615, by rfl⟩ : syracuseStep 579487 = 869231) B869231
theorem B546785 : Blo 239816 546785 := bstep (se 2 (by rfl) ⟨205044, by rfl⟩ : syracuseStep 546785 = 410089) B410089
theorem B1366055 : Blo 239816 1366055 := bstep (se 1 (by rfl) ⟨1024541, by rfl⟩ : syracuseStep 1366055 = 2049083) B2049083
theorem B579803 : Blo 239816 579803 := bstep (se 1 (by rfl) ⟨434852, by rfl⟩ : syracuseStep 579803 = 869705) B869705
theorem B1038689 : Blo 239816 1038689 := bstep (se 2 (by rfl) ⟨389508, by rfl⟩ : syracuseStep 1038689 = 779017) B779017
theorem B1858085 : Blo 239816 1858085 := bstep (se 4 (by rfl) ⟨174195, by rfl⟩ : syracuseStep 1858085 = 348391) B348391
theorem B809783 : Blo 239816 809783 := bstep (se 1 (by rfl) ⟨607337, by rfl⟩ : syracuseStep 809783 = 1214675) B1214675
theorem B1039645 : Blo 239816 1039645 := bstep (se 3 (by rfl) ⟨194933, by rfl⟩ : syracuseStep 1039645 = 389867) B389867
theorem B581111 : Blo 239816 581111 := bstep (se 1 (by rfl) ⟨435833, by rfl⟩ : syracuseStep 581111 = 871667) B871667
theorem B2940421 : Blo 239816 2940421 := bstep (se 4 (by rfl) ⟨275664, by rfl⟩ : syracuseStep 2940421 = 551329) B551329
theorem B810863 : Blo 239816 810863 := bstep (se 1 (by rfl) ⟨608147, by rfl⟩ : syracuseStep 810863 = 1216295) B1216295
theorem B37773317 : Blo 239816 37773317 := bstep (se 4 (by rfl) ⟨3541248, by rfl⟩ : syracuseStep 37773317 = 7082497) B7082497
theorem B909625 : Blo 239816 909625 := bstep (se 2 (by rfl) ⟨341109, by rfl⟩ : syracuseStep 909625 = 682219) B682219
theorem B811727 : Blo 239816 811727 := bstep (se 1 (by rfl) ⟨608795, by rfl⟩ : syracuseStep 811727 = 1217591) B1217591
theorem B812105 : Blo 239816 812105 := bstep (se 2 (by rfl) ⟨304539, by rfl⟩ : syracuseStep 812105 = 609079) B609079
theorem B196338887 : Blo 239816 196338887 := bstep (se 1 (by rfl) ⟨147254165, by rfl⟩ : syracuseStep 196338887 = 294508331) B294508331
theorem B550471 : Blo 239816 550471 := bstep (se 1 (by rfl) ⟨412853, by rfl⟩ : syracuseStep 550471 = 825707) B825707
theorem B616187 : Blo 239816 616187 := bstep (se 1 (by rfl) ⟨462140, by rfl⟩ : syracuseStep 616187 = 924281) B924281
theorem B616531 : Blo 239816 616531 := bstep (se 1 (by rfl) ⟨462398, by rfl⟩ : syracuseStep 616531 = 924797) B924797
theorem B780815 : Blo 239816 780815 := bstep (se 1 (by rfl) ⟨585611, by rfl⟩ : syracuseStep 780815 = 1171223) B1171223
theorem B879119 : Blo 239816 879119 := bstep (se 1 (by rfl) ⟨659339, by rfl⟩ : syracuseStep 879119 = 1318679) B1318679
theorem B5270123 : Blo 239816 5270123 := bstep (se 1 (by rfl) ⟨3952592, by rfl⟩ : syracuseStep 5270123 = 7905185) B7905185
theorem B2059607 : Blo 239816 2059607 := bstep (se 1 (by rfl) ⟨1544705, by rfl⟩ : syracuseStep 2059607 = 3089411) B3089411
theorem B912829 : Blo 239816 912829 := bstep (se 3 (by rfl) ⟨171155, by rfl⟩ : syracuseStep 912829 = 342311) B342311
theorem B519635 : Blo 239816 519635 := bstep (se 1 (by rfl) ⟨389726, by rfl⟩ : syracuseStep 519635 = 779453) B779453
theorem B257639 : Blo 239816 257639 := bstep (se 1 (by rfl) ⟨193229, by rfl⟩ : syracuseStep 257639 = 386459) B386459
theorem B520319 : Blo 239816 520319 := bstep (se 1 (by rfl) ⟨390239, by rfl⟩ : syracuseStep 520319 = 780479) B780479
theorem B15790403 : Blo 239816 15790403 := bstep (se 1 (by rfl) ⟨11842802, by rfl⟩ : syracuseStep 15790403 = 23685605) B23685605
theorem B488171 : Blo 239816 488171 := bstep (se 1 (by rfl) ⟨366128, by rfl⟩ : syracuseStep 488171 = 732257) B732257
theorem B2388797 : Blo 239816 2388797 := bstep (se 3 (by rfl) ⟨447899, by rfl⟩ : syracuseStep 2388797 = 895799) B895799
theorem B488359 : Blo 239816 488359 := bstep (se 1 (by rfl) ⟨366269, by rfl⟩ : syracuseStep 488359 = 732539) B732539
theorem B685523 : Blo 239816 685523 := bstep (se 1 (by rfl) ⟨514142, by rfl⟩ : syracuseStep 685523 = 1028285) B1028285
theorem B4159673 : Blo 239816 4159673 := bstep (se 2 (by rfl) ⟨1559877, by rfl⟩ : syracuseStep 4159673 = 3119755) B3119755
theorem B1538351 : Blo 239816 1538351 := bstep (se 1 (by rfl) ⟨1153763, by rfl⟩ : syracuseStep 1538351 = 2307527) B2307527
theorem B457159 : Blo 239816 457159 := bstep (se 1 (by rfl) ⟨342869, by rfl⟩ : syracuseStep 457159 = 685739) B685739
theorem B2325023 : Blo 239816 2325023 := bstep (se 1 (by rfl) ⟨1743767, by rfl⟩ : syracuseStep 2325023 = 3487535) B3487535
theorem B916703 : Blo 239816 916703 := bstep (se 1 (by rfl) ⟨687527, by rfl⟩ : syracuseStep 916703 = 1375055) B1375055
theorem B1047775 : Blo 239816 1047775 := bstep (se 1 (by rfl) ⟨785831, by rfl⟩ : syracuseStep 1047775 = 1571663) B1571663
theorem B982297 : Blo 239816 982297 := bstep (se 2 (by rfl) ⟨368361, by rfl⟩ : syracuseStep 982297 = 736723) B736723
theorem B818639 : Blo 239816 818639 := bstep (se 1 (by rfl) ⟨613979, by rfl⟩ : syracuseStep 818639 = 1227959) B1227959
theorem B2063981 : Blo 239816 2063981 := bstep (se 3 (by rfl) ⟨386996, by rfl⟩ : syracuseStep 2063981 = 773993) B773993
theorem B360047 : Blo 239816 360047 := bstep (se 1 (by rfl) ⟨270035, by rfl⟩ : syracuseStep 360047 = 540071) B540071
theorem B1539785 : Blo 239816 1539785 := bstep (se 2 (by rfl) ⟨577419, by rfl⟩ : syracuseStep 1539785 = 1154839) B1154839
theorem B360167 : Blo 239816 360167 := bstep (se 1 (by rfl) ⟨270125, by rfl⟩ : syracuseStep 360167 = 540251) B540251
theorem B458617 : Blo 239816 458617 := bstep (se 2 (by rfl) ⟨171981, by rfl⟩ : syracuseStep 458617 = 343963) B343963
theorem B360359 : Blo 239816 360359 := bstep (se 1 (by rfl) ⟨270269, by rfl⟩ : syracuseStep 360359 = 540539) B540539
theorem B360575 : Blo 239816 360575 := bstep (se 1 (by rfl) ⟨270431, by rfl⟩ : syracuseStep 360575 = 540863) B540863
theorem B2752703 : Blo 239816 2752703 := bstep (se 1 (by rfl) ⟨2064527, by rfl⟩ : syracuseStep 2752703 = 4129055) B4129055
theorem B17793431 : Blo 239816 17793431 := bstep (se 1 (by rfl) ⟨13345073, by rfl⟩ : syracuseStep 17793431 = 26690147) B26690147
theorem B360863 : Blo 239816 360863 := bstep (se 1 (by rfl) ⟨270647, by rfl⟩ : syracuseStep 360863 = 541295) B541295
theorem B1212833 : Blo 239816 1212833 := bstep (se 2 (by rfl) ⟨454812, by rfl⟩ : syracuseStep 1212833 = 909625) B909625
theorem B917993 : Blo 239816 917993 := bstep (se 2 (by rfl) ⟨344247, by rfl⟩ : syracuseStep 917993 = 688495) B688495
theorem B361127 : Blo 239816 361127 := bstep (se 1 (by rfl) ⟨270845, by rfl⟩ : syracuseStep 361127 = 541691) B541691
theorem B361247 : Blo 239816 361247 := bstep (se 1 (by rfl) ⟨270935, by rfl⟩ : syracuseStep 361247 = 541871) B541871
theorem B361271 : Blo 239816 361271 := bstep (se 1 (by rfl) ⟨270953, by rfl⟩ : syracuseStep 361271 = 541907) B541907
theorem B361451 : Blo 239816 361451 := bstep (se 1 (by rfl) ⟨271088, by rfl⟩ : syracuseStep 361451 = 542177) B542177
theorem B492617 : Blo 239816 492617 := bstep (se 2 (by rfl) ⟨184731, by rfl⟩ : syracuseStep 492617 = 369463) B369463
theorem B361961 : Blo 239816 361961 := bstep (se 2 (by rfl) ⟨135735, by rfl⟩ : syracuseStep 361961 = 271471) B271471
theorem B3081725 : Blo 239816 3081725 := bstep (se 3 (by rfl) ⟨577823, by rfl⟩ : syracuseStep 3081725 = 1155647) B1155647
theorem B689771 : Blo 239816 689771 := bstep (se 1 (by rfl) ⟨517328, by rfl⟩ : syracuseStep 689771 = 1034657) B1034657
theorem B329449 : Blo 239816 329449 := bstep (se 2 (by rfl) ⟨123543, by rfl⟩ : syracuseStep 329449 = 247087) B247087
theorem B362351 : Blo 239816 362351 := bstep (se 1 (by rfl) ⟨271763, by rfl⟩ : syracuseStep 362351 = 543527) B543527
theorem B1214351 : Blo 239816 1214351 := bstep (se 1 (by rfl) ⟨910763, by rfl⟩ : syracuseStep 1214351 = 1821527) B1821527
theorem B362537 : Blo 239816 362537 := bstep (se 2 (by rfl) ⟨135951, by rfl⟩ : syracuseStep 362537 = 271903) B271903
theorem B362567 : Blo 239816 362567 := bstep (se 1 (by rfl) ⟨271925, by rfl⟩ : syracuseStep 362567 = 543851) B543851
theorem B362747 : Blo 239816 362747 := bstep (se 1 (by rfl) ⟨272060, by rfl⟩ : syracuseStep 362747 = 544121) B544121
theorem B362951 : Blo 239816 362951 := bstep (se 1 (by rfl) ⟨272213, by rfl⟩ : syracuseStep 362951 = 544427) B544427
theorem B363167 : Blo 239816 363167 := bstep (se 1 (by rfl) ⟨272375, by rfl⟩ : syracuseStep 363167 = 544751) B544751
theorem B363215 : Blo 239816 363215 := bstep (se 1 (by rfl) ⟨272411, by rfl⟩ : syracuseStep 363215 = 544823) B544823
theorem B822041 : Blo 239816 822041 := bstep (se 2 (by rfl) ⟨308265, by rfl⟩ : syracuseStep 822041 = 616531) B616531
theorem B363311 : Blo 239816 363311 := bstep (se 1 (by rfl) ⟨272483, by rfl⟩ : syracuseStep 363311 = 544967) B544967
theorem B822095 : Blo 239816 822095 := bstep (se 1 (by rfl) ⟨616571, by rfl⟩ : syracuseStep 822095 = 1233143) B1233143
theorem B2624339 : Blo 239816 2624339 := bstep (se 1 (by rfl) ⟨1968254, by rfl⟩ : syracuseStep 2624339 = 3936509) B3936509
theorem B363431 : Blo 239816 363431 := bstep (se 1 (by rfl) ⟨272573, by rfl⟩ : syracuseStep 363431 = 545147) B545147
theorem B363611 : Blo 239816 363611 := bstep (se 1 (by rfl) ⟨272708, by rfl⟩ : syracuseStep 363611 = 545417) B545417
theorem B822419 : Blo 239816 822419 := bstep (se 1 (by rfl) ⟨616814, by rfl⟩ : syracuseStep 822419 = 1233629) B1233629
theorem B363689 : Blo 239816 363689 := bstep (se 2 (by rfl) ⟨136383, by rfl⟩ : syracuseStep 363689 = 272767) B272767
theorem B364103 : Blo 239816 364103 := bstep (se 1 (by rfl) ⟨273077, by rfl⟩ : syracuseStep 364103 = 546155) B546155
theorem B10554995 : Blo 239816 10554995 := bstep (se 1 (by rfl) ⟨7916246, by rfl⟩ : syracuseStep 10554995 = 15832493) B15832493
theorem B364283 : Blo 239816 364283 := bstep (se 1 (by rfl) ⟨273212, by rfl⟩ : syracuseStep 364283 = 546425) B546425
theorem B1839023 : Blo 239816 1839023 := bstep (se 1 (by rfl) ⟨1379267, by rfl⟩ : syracuseStep 1839023 = 2758535) B2758535
theorem B921563 : Blo 239816 921563 := bstep (se 1 (by rfl) ⟨691172, by rfl⟩ : syracuseStep 921563 = 1382345) B1382345
theorem B364523 : Blo 239816 364523 := bstep (se 1 (by rfl) ⟨273392, by rfl⟩ : syracuseStep 364523 = 546785) B546785
theorem B1380361 : Blo 239816 1380361 := bstep (se 2 (by rfl) ⟨517635, by rfl⟩ : syracuseStep 1380361 = 1035271) B1035271
theorem B692459 : Blo 239816 692459 := bstep (se 1 (by rfl) ⟨519344, by rfl⟩ : syracuseStep 692459 = 1038689) B1038689
theorem B921881 : Blo 239816 921881 := bstep (se 2 (by rfl) ⟨345705, by rfl⟩ : syracuseStep 921881 = 691411) B691411
theorem B2330977 : Blo 239816 2330977 := bstep (se 2 (by rfl) ⟨874116, by rfl⟩ : syracuseStep 2330977 = 1748233) B1748233
theorem B922063 : Blo 239816 922063 := bstep (se 1 (by rfl) ⟨691547, by rfl⟩ : syracuseStep 922063 = 1383095) B1383095
theorem B1217105 : Blo 239816 1217105 := bstep (se 2 (by rfl) ⟨456414, by rfl⟩ : syracuseStep 1217105 = 912829) B912829
theorem B365561 : Blo 239816 365561 := bstep (se 2 (by rfl) ⟨137085, by rfl⟩ : syracuseStep 365561 = 274171) B274171
theorem B3937679 : Blo 239816 3937679 := bstep (se 1 (by rfl) ⟨2953259, by rfl⟩ : syracuseStep 3937679 = 5906519) B5906519
theorem B1546141 : Blo 239816 1546141 := bstep (se 3 (by rfl) ⟨289901, by rfl⟩ : syracuseStep 1546141 = 579803) B579803
theorem B2070953 : Blo 239816 2070953 := bstep (se 2 (by rfl) ⟨776607, by rfl⟩ : syracuseStep 2070953 = 1553215) B1553215
theorem B925465 : Blo 239816 925465 := bstep (se 2 (by rfl) ⟨347049, by rfl⟩ : syracuseStep 925465 = 694099) B694099
theorem B10526935 : Blo 239816 10526935 := bstep (se 1 (by rfl) ⟨7895201, by rfl⟩ : syracuseStep 10526935 = 15790403) B15790403
theorem B2761451 : Blo 239816 2761451 := bstep (se 1 (by rfl) ⟨2071088, by rfl⟩ : syracuseStep 2761451 = 4142177) B4142177
theorem B1385693 : Blo 239816 1385693 := bstep (se 3 (by rfl) ⟨259817, by rfl⟩ : syracuseStep 1385693 = 519635) B519635
theorem B1025567 : Blo 239816 1025567 := bstep (se 1 (by rfl) ⟨769175, by rfl⟩ : syracuseStep 1025567 = 1538351) B1538351
theorem B1550015 : Blo 239816 1550015 := bstep (se 1 (by rfl) ⟨1162511, by rfl⟩ : syracuseStep 1550015 = 2325023) B2325023
theorem B1386193 : Blo 239816 1386193 := bstep (se 2 (by rfl) ⟨519822, by rfl⟩ : syracuseStep 1386193 = 1039645) B1039645
theorem B1386719 : Blo 239816 1386719 := bstep (se 1 (by rfl) ⟨1040039, by rfl⟩ : syracuseStep 1386719 = 2080079) B2080079
theorem B240031 : Blo 239816 240031 := bstep (se 1 (by rfl) ⟨180023, by rfl⟩ : syracuseStep 240031 = 360047) B360047
theorem B1026523 : Blo 239816 1026523 := bstep (se 1 (by rfl) ⟨769892, by rfl⟩ : syracuseStep 1026523 = 1539785) B1539785
theorem B240111 : Blo 239816 240111 := bstep (se 1 (by rfl) ⟨180083, by rfl⟩ : syracuseStep 240111 = 360167) B360167
theorem B240239 : Blo 239816 240239 := bstep (se 1 (by rfl) ⟨180179, by rfl⟩ : syracuseStep 240239 = 360359) B360359
theorem B240455 : Blo 239816 240455 := bstep (se 1 (by rfl) ⟨180341, by rfl⟩ : syracuseStep 240455 = 360683) B360683
theorem B240495 : Blo 239816 240495 := bstep (se 1 (by rfl) ⟨180371, by rfl⟩ : syracuseStep 240495 = 360743) B360743
theorem B1223585 : Blo 239816 1223585 := bstep (se 2 (by rfl) ⟨458844, by rfl⟩ : syracuseStep 1223585 = 917689) B917689
theorem B1846205 : Blo 239816 1846205 := bstep (se 3 (by rfl) ⟨346163, by rfl⟩ : syracuseStep 1846205 = 692327) B692327
theorem B306119 : Blo 239816 306119 := bstep (se 1 (by rfl) ⟨229589, by rfl⟩ : syracuseStep 306119 = 459179) B459179
theorem B1649879 : Blo 239816 1649879 := bstep (se 1 (by rfl) ⟨1237409, by rfl⟩ : syracuseStep 1649879 = 2474819) B2474819
theorem B240943 : Blo 239816 240943 := bstep (se 1 (by rfl) ⟨180707, by rfl⟩ : syracuseStep 240943 = 361415) B361415
theorem B241055 : Blo 239816 241055 := bstep (se 1 (by rfl) ⟨180791, by rfl⟩ : syracuseStep 241055 = 361583) B361583
theorem B437737 : Blo 239816 437737 := bstep (se 2 (by rfl) ⟨164151, by rfl⟩ : syracuseStep 437737 = 328303) B328303
theorem B241183 : Blo 239816 241183 := bstep (se 1 (by rfl) ⟨180887, by rfl⟩ : syracuseStep 241183 = 361775) B361775
theorem B241319 : Blo 239816 241319 := bstep (se 1 (by rfl) ⟨180989, by rfl⟩ : syracuseStep 241319 = 361979) B361979
theorem B241343 : Blo 239816 241343 := bstep (se 1 (by rfl) ⟨181007, by rfl⟩ : syracuseStep 241343 = 362015) B362015
theorem B241439 : Blo 239816 241439 := bstep (se 1 (by rfl) ⟨181079, by rfl⟩ : syracuseStep 241439 = 362159) B362159
theorem B274207 : Blo 239816 274207 := bstep (se 1 (by rfl) ⟨205655, by rfl⟩ : syracuseStep 274207 = 411311) B411311
theorem B241519 : Blo 239816 241519 := bstep (se 1 (by rfl) ⟨181139, by rfl⟩ : syracuseStep 241519 = 362279) B362279
theorem B2633593 : Blo 239816 2633593 := bstep (se 2 (by rfl) ⟨987597, by rfl⟩ : syracuseStep 2633593 = 1975195) B1975195
theorem B405607 : Blo 239816 405607 := bstep (se 1 (by rfl) ⟨304205, by rfl⟩ : syracuseStep 405607 = 608411) B608411
theorem B241887 : Blo 239816 241887 := bstep (se 1 (by rfl) ⟨181415, by rfl⟩ : syracuseStep 241887 = 362831) B362831
theorem B241919 : Blo 239816 241919 := bstep (se 1 (by rfl) ⟨181439, by rfl⟩ : syracuseStep 241919 = 362879) B362879
theorem B241947 : Blo 239816 241947 := bstep (se 1 (by rfl) ⟨181460, by rfl⟩ : syracuseStep 241947 = 362921) B362921
theorem B242203 : Blo 239816 242203 := bstep (se 1 (by rfl) ⟨181652, by rfl⟩ : syracuseStep 242203 = 363305) B363305
theorem B307739 : Blo 239816 307739 := bstep (se 1 (by rfl) ⟨230804, by rfl⟩ : syracuseStep 307739 = 461609) B461609
theorem B242343 : Blo 239816 242343 := bstep (se 1 (by rfl) ⟨181757, by rfl⟩ : syracuseStep 242343 = 363515) B363515
theorem B242383 : Blo 239816 242383 := bstep (se 1 (by rfl) ⟨181787, by rfl⟩ : syracuseStep 242383 = 363575) B363575
theorem B733961 : Blo 239816 733961 := bstep (se 2 (by rfl) ⟨275235, by rfl⟩ : syracuseStep 733961 = 550471) B550471
theorem B242463 : Blo 239816 242463 := bstep (se 1 (by rfl) ⟨181847, by rfl⟩ : syracuseStep 242463 = 363695) B363695
theorem B2437951 : Blo 239816 2437951 := bstep (se 1 (by rfl) ⟨1828463, by rfl⟩ : syracuseStep 2437951 = 3656927) B3656927
theorem B734035 : Blo 239816 734035 := bstep (se 1 (by rfl) ⟨550526, by rfl⟩ : syracuseStep 734035 = 1101053) B1101053
theorem B1749995 : Blo 239816 1749995 := bstep (se 1 (by rfl) ⟨1312496, by rfl⟩ : syracuseStep 1749995 = 2624993) B2624993
theorem B3093511 : Blo 239816 3093511 := bstep (se 1 (by rfl) ⟨2320133, by rfl⟩ : syracuseStep 3093511 = 4640267) B4640267
theorem B242943 : Blo 239816 242943 := bstep (se 1 (by rfl) ⟨182207, by rfl⟩ : syracuseStep 242943 = 364415) B364415
theorem B243071 : Blo 239816 243071 := bstep (se 1 (by rfl) ⟨182303, by rfl⟩ : syracuseStep 243071 = 364607) B364607
theorem B243227 : Blo 239816 243227 := bstep (se 1 (by rfl) ⟨182420, by rfl⟩ : syracuseStep 243227 = 364841) B364841
theorem B243407 : Blo 239816 243407 := bstep (se 1 (by rfl) ⟨182555, by rfl⟩ : syracuseStep 243407 = 365111) B365111
theorem B2930539 : Blo 239816 2930539 := bstep (se 1 (by rfl) ⟨2197904, by rfl⟩ : syracuseStep 2930539 = 4395809) B4395809
theorem B243647 : Blo 239816 243647 := bstep (se 1 (by rfl) ⟨182735, by rfl⟩ : syracuseStep 243647 = 365471) B365471
theorem B407531 : Blo 239816 407531 := bstep (se 1 (by rfl) ⟨305648, by rfl⟩ : syracuseStep 407531 = 611297) B611297
theorem B243775 : Blo 239816 243775 := bstep (se 1 (by rfl) ⟨182831, by rfl⟩ : syracuseStep 243775 = 365663) B365663
theorem B243815 : Blo 239816 243815 := bstep (se 1 (by rfl) ⟨182861, by rfl⟩ : syracuseStep 243815 = 365723) B365723
theorem B539855 : Blo 239816 539855 := bstep (se 1 (by rfl) ⟨404891, by rfl⟩ : syracuseStep 539855 = 809783) B809783
theorem B539945 : Blo 239816 539945 := bstep (se 2 (by rfl) ⟨202479, by rfl⟩ : syracuseStep 539945 = 404959) B404959
theorem B1228283 : Blo 239816 1228283 := bstep (se 1 (by rfl) ⟨921212, by rfl⟩ : syracuseStep 1228283 = 1842425) B1842425
theorem B2604581 : Blo 239816 2604581 := bstep (se 4 (by rfl) ⟨244179, by rfl⟩ : syracuseStep 2604581 = 488359) B488359
theorem B540233 : Blo 239816 540233 := bstep (se 2 (by rfl) ⟨202587, by rfl⟩ : syracuseStep 540233 = 405175) B405175
theorem B540575 : Blo 239816 540575 := bstep (se 1 (by rfl) ⟨405431, by rfl⟩ : syracuseStep 540575 = 810863) B810863
theorem B25182211 : Blo 239816 25182211 := bstep (se 1 (by rfl) ⟨18886658, by rfl⟩ : syracuseStep 25182211 = 37773317) B37773317
theorem B2801729 : Blo 239816 2801729 := bstep (se 2 (by rfl) ⟨1050648, by rfl⟩ : syracuseStep 2801729 = 2101297) B2101297
theorem B541151 : Blo 239816 541151 := bstep (se 1 (by rfl) ⟨405863, by rfl⟩ : syracuseStep 541151 = 811727) B811727
theorem B3129905 : Blo 239816 3129905 := bstep (se 2 (by rfl) ⟨1173714, by rfl⟩ : syracuseStep 3129905 = 2347429) B2347429
theorem B541403 : Blo 239816 541403 := bstep (se 1 (by rfl) ⟨406052, by rfl⟩ : syracuseStep 541403 = 812105) B812105
theorem B1229579 : Blo 239816 1229579 := bstep (se 1 (by rfl) ⟨922184, by rfl⟩ : syracuseStep 1229579 = 1844369) B1844369
theorem B130892591 : Blo 239816 130892591 := bstep (se 1 (by rfl) ⟨98169443, by rfl⟩ : syracuseStep 130892591 = 196338887) B196338887
theorem B410791 : Blo 239816 410791 := bstep (se 1 (by rfl) ⟨308093, by rfl⟩ : syracuseStep 410791 = 616187) B616187
theorem B771419 : Blo 239816 771419 := bstep (se 1 (by rfl) ⟨578564, by rfl⟩ : syracuseStep 771419 = 1157129) B1157129
theorem B1034041 : Blo 239816 1034041 := bstep (se 2 (by rfl) ⟨387765, by rfl⟩ : syracuseStep 1034041 = 775531) B775531
theorem B1230713 : Blo 239816 1230713 := bstep (se 2 (by rfl) ⟨461517, by rfl⟩ : syracuseStep 1230713 = 923035) B923035
theorem B1558547 : Blo 239816 1558547 := bstep (se 1 (by rfl) ⟨1168910, by rfl⟩ : syracuseStep 1558547 = 2337821) B2337821
theorem B1230875 : Blo 239816 1230875 := bstep (se 1 (by rfl) ⟨923156, by rfl⟩ : syracuseStep 1230875 = 1846313) B1846313
theorem B346423 : Blo 239816 346423 := bstep (se 1 (by rfl) ⟨259817, by rfl⟩ : syracuseStep 346423 = 519635) B519635
theorem B1231199 : Blo 239816 1231199 := bstep (se 1 (by rfl) ⟨923399, by rfl⟩ : syracuseStep 1231199 = 1846799) B1846799
theorem B772649 : Blo 239816 772649 := bstep (se 2 (by rfl) ⟨289743, by rfl⟩ : syracuseStep 772649 = 579487) B579487
theorem B1854089 : Blo 239816 1854089 := bstep (se 2 (by rfl) ⟨695283, by rfl⟩ : syracuseStep 1854089 = 1390567) B1390567
theorem B1559263 : Blo 239816 1559263 := bstep (se 1 (by rfl) ⟨1169447, by rfl⟩ : syracuseStep 1559263 = 2338895) B2338895
theorem B346879 : Blo 239816 346879 := bstep (se 1 (by rfl) ⟨260159, by rfl⟩ : syracuseStep 346879 = 520319) B520319
theorem B1592531 : Blo 239816 1592531 := bstep (se 1 (by rfl) ⟨1194398, by rfl⟩ : syracuseStep 1592531 = 2388797) B2388797
theorem B609545 : Blo 239816 609545 := bstep (se 2 (by rfl) ⟨228579, by rfl⟩ : syracuseStep 609545 = 457159) B457159
theorem B577343 : Blo 239816 577343 := bstep (se 1 (by rfl) ⟨433007, by rfl⟩ : syracuseStep 577343 = 866015) B866015
theorem B2773115 : Blo 239816 2773115 := bstep (se 1 (by rfl) ⟨2079836, by rfl⟩ : syracuseStep 2773115 = 4159673) B4159673
theorem B1397033 : Blo 239816 1397033 := bstep (se 2 (by rfl) ⟨523887, by rfl⟩ : syracuseStep 1397033 = 1047775) B1047775
theorem B3920561 : Blo 239816 3920561 := bstep (se 2 (by rfl) ⟨1470210, by rfl⟩ : syracuseStep 3920561 = 2940421) B2940421
theorem B611135 : Blo 239816 611135 := bstep (se 1 (by rfl) ⟨458351, by rfl⟩ : syracuseStep 611135 = 916703) B916703
theorem B545759 : Blo 239816 545759 := bstep (se 1 (by rfl) ⟨409319, by rfl⟩ : syracuseStep 545759 = 818639) B818639
theorem B611489 : Blo 239816 611489 := bstep (se 2 (by rfl) ⟨229308, by rfl⟩ : syracuseStep 611489 = 458617) B458617
theorem B546335 : Blo 239816 546335 := bstep (se 1 (by rfl) ⟨409751, by rfl⟩ : syracuseStep 546335 = 819503) B819503
theorem B1660495 : Blo 239816 1660495 := bstep (se 1 (by rfl) ⟨1245371, by rfl⟩ : syracuseStep 1660495 = 2490743) B2490743
theorem B775763 : Blo 239816 775763 := bstep (se 1 (by rfl) ⟨581822, by rfl⟩ : syracuseStep 775763 = 1163645) B1163645
theorem B546857 : Blo 239816 546857 := bstep (se 2 (by rfl) ⟨205071, by rfl⟩ : syracuseStep 546857 = 410143) B410143
theorem B3824047 : Blo 239816 3824047 := bstep (se 1 (by rfl) ⟨2868035, by rfl⟩ : syracuseStep 3824047 = 5736071) B5736071
theorem B11819641 : Blo 239816 11819641 := bstep (se 2 (by rfl) ⟨4432365, by rfl⟩ : syracuseStep 11819641 = 8864731) B8864731
theorem B547487 : Blo 239816 547487 := bstep (se 1 (by rfl) ⟨410615, by rfl⟩ : syracuseStep 547487 = 821231) B821231
theorem B940787 : Blo 239816 940787 := bstep (se 1 (by rfl) ⟨705590, by rfl⟩ : syracuseStep 940787 = 1411181) B1411181
theorem B1367239 : Blo 239816 1367239 := bstep (se 1 (by rfl) ⟨1025429, by rfl⟩ : syracuseStep 1367239 = 2050859) B2050859
theorem B1301789 : Blo 239816 1301789 := bstep (se 3 (by rfl) ⟨244085, by rfl⟩ : syracuseStep 1301789 = 488171) B488171
theorem B2743955 : Blo 239816 2743955 := bstep (se 1 (by rfl) ⟨2057966, by rfl⟩ : syracuseStep 2743955 = 4115933) B4115933
theorem B4415143 : Blo 239816 4415143 := bstep (se 1 (by rfl) ⟨3311357, by rfl⟩ : syracuseStep 4415143 = 6622715) B6622715
theorem B778223 : Blo 239816 778223 := bstep (se 1 (by rfl) ⟨583667, by rfl⟩ : syracuseStep 778223 = 1167335) B1167335
theorem B1466369 : Blo 239816 1466369 := bstep (se 2 (by rfl) ⟨549888, by rfl⟩ : syracuseStep 1466369 = 1099777) B1099777
theorem B811133 : Blo 239816 811133 := bstep (se 3 (by rfl) ⟨152087, by rfl⟩ : syracuseStep 811133 = 304175) B304175
theorem B385319 : Blo 239816 385319 := bstep (se 1 (by rfl) ⟨288989, by rfl⟩ : syracuseStep 385319 = 577979) B577979
theorem B1369223 : Blo 239816 1369223 := bstep (se 1 (by rfl) ⟨1026917, by rfl⟩ : syracuseStep 1369223 = 2053835) B2053835
theorem B1664225 : Blo 239816 1664225 := bstep (se 2 (by rfl) ⟨624084, by rfl⟩ : syracuseStep 1664225 = 1248169) B1248169
theorem B812267 : Blo 239816 812267 := bstep (se 1 (by rfl) ⟨609200, by rfl⟩ : syracuseStep 812267 = 1218401) B1218401
theorem B1205561 : Blo 239816 1205561 := bstep (se 2 (by rfl) ⟨452085, by rfl⟩ : syracuseStep 1205561 = 904171) B904171
theorem B910703 : Blo 239816 910703 := bstep (se 1 (by rfl) ⟨683027, by rfl⟩ : syracuseStep 910703 = 1366055) B1366055
theorem B1238723 : Blo 239816 1238723 := bstep (se 1 (by rfl) ⟨929042, by rfl⟩ : syracuseStep 1238723 = 1858085) B1858085
theorem B4941587 : Blo 239816 4941587 := bstep (se 1 (by rfl) ⟨3706190, by rfl⟩ : syracuseStep 4941587 = 7412381) B7412381
theorem B1402687 : Blo 239816 1402687 := bstep (se 1 (by rfl) ⟨1052015, by rfl⟩ : syracuseStep 1402687 = 2104031) B2104031
theorem B387407 : Blo 239816 387407 := bstep (se 1 (by rfl) ⟨290555, by rfl⟩ : syracuseStep 387407 = 581111) B581111
theorem B1370681 : Blo 239816 1370681 := bstep (se 2 (by rfl) ⟨514005, by rfl⟩ : syracuseStep 1370681 = 1028011) B1028011
theorem B2058857 : Blo 239816 2058857 := bstep (se 2 (by rfl) ⟨772071, by rfl⟩ : syracuseStep 2058857 = 1544143) B1544143
theorem B1993349 : Blo 239816 1993349 := bstep (se 4 (by rfl) ⟨186876, by rfl⟩ : syracuseStep 1993349 = 373753) B373753
theorem B683063 : Blo 239816 683063 := bstep (se 1 (by rfl) ⟨512297, by rfl⟩ : syracuseStep 683063 = 1024595) B1024595
theorem B2977769 : Blo 239816 2977769 := bstep (se 2 (by rfl) ⟨1116663, by rfl⟩ : syracuseStep 2977769 = 2233327) B2233327
theorem B684247 : Blo 239816 684247 := bstep (se 1 (by rfl) ⟨513185, by rfl⟩ : syracuseStep 684247 = 1026371) B1026371
theorem B14053661 : Blo 239816 14053661 := bstep (se 3 (by rfl) ⟨2635061, by rfl⟩ : syracuseStep 14053661 = 5270123) B5270123
theorem B520543 : Blo 239816 520543 := bstep (se 1 (by rfl) ⟨390407, by rfl⟩ : syracuseStep 520543 = 780815) B780815
theorem B586079 : Blo 239816 586079 := bstep (se 1 (by rfl) ⟨439559, by rfl⟩ : syracuseStep 586079 = 879119) B879119
theorem B684521 : Blo 239816 684521 := bstep (se 2 (by rfl) ⟨256695, by rfl⟩ : syracuseStep 684521 = 513391) B513391
theorem B881455 : Blo 239816 881455 := bstep (se 1 (by rfl) ⟨661091, by rfl⟩ : syracuseStep 881455 = 1322183) B1322183
theorem B1373071 : Blo 239816 1373071 := bstep (se 1 (by rfl) ⟨1029803, by rfl⟩ : syracuseStep 1373071 = 2059607) B2059607
theorem B457015 : Blo 239816 457015 := bstep (se 1 (by rfl) ⟨342761, by rfl⟩ : syracuseStep 457015 = 685523) B685523
theorem B1603997 : Blo 239816 1603997 := bstep (se 3 (by rfl) ⟨300749, by rfl⟩ : syracuseStep 1603997 = 601499) B601499
theorem B686855 : Blo 239816 686855 := bstep (se 1 (by rfl) ⟨515141, by rfl⟩ : syracuseStep 686855 = 1030283) B1030283
theorem B687037 : Blo 239816 687037 := bstep (se 3 (by rfl) ⟨128819, by rfl⟩ : syracuseStep 687037 = 257639) B257639
theorem B1309729 : Blo 239816 1309729 := bstep (se 2 (by rfl) ⟨491148, by rfl⟩ : syracuseStep 1309729 = 982297) B982297
theorem B359735 : Blo 239816 359735 := bstep (se 1 (by rfl) ⟨269801, by rfl⟩ : syracuseStep 359735 = 539603) B539603
theorem B359915 : Blo 239816 359915 := bstep (se 1 (by rfl) ⟨269936, by rfl⟩ : syracuseStep 359915 = 539873) B539873
theorem B3309167 : Blo 239816 3309167 := bstep (se 1 (by rfl) ⟨2481875, by rfl⟩ : syracuseStep 3309167 = 4963751) B4963751
theorem B1277561 : Blo 239816 1277561 := bstep (se 2 (by rfl) ⟨479085, by rfl⟩ : syracuseStep 1277561 = 958171) B958171
theorem B360119 : Blo 239816 360119 := bstep (se 1 (by rfl) ⟨270089, by rfl⟩ : syracuseStep 360119 = 540179) B540179
theorem B1375987 : Blo 239816 1375987 := bstep (se 1 (by rfl) ⟨1031990, by rfl⟩ : syracuseStep 1375987 = 2063981) B2063981
theorem B360329 : Blo 239816 360329 := bstep (se 2 (by rfl) ⟨135123, by rfl⟩ : syracuseStep 360329 = 270247) B270247
theorem B1867819 : Blo 239816 1867819 := bstep (se 1 (by rfl) ⟨1400864, by rfl⟩ : syracuseStep 1867819 = 2801729) B2801729
theorem B1835135 : Blo 239816 1835135 := bstep (se 1 (by rfl) ⟨1376351, by rfl⟩ : syracuseStep 1835135 = 2752703) B2752703
theorem B11862287 : Blo 239816 11862287 := bstep (se 1 (by rfl) ⟨8896715, by rfl⟩ : syracuseStep 11862287 = 17793431) B17793431
theorem B360767 : Blo 239816 360767 := bstep (se 1 (by rfl) ⟨270575, by rfl⟩ : syracuseStep 360767 = 541151) B541151
theorem B360935 : Blo 239816 360935 := bstep (se 1 (by rfl) ⟨270701, by rfl⟩ : syracuseStep 360935 = 541403) B541403
theorem B819719 : Blo 239816 819719 := bstep (se 1 (by rfl) ⟨614789, by rfl⟩ : syracuseStep 819719 = 1229579) B1229579
theorem B328411 : Blo 239816 328411 := bstep (se 1 (by rfl) ⟨246308, by rfl⟩ : syracuseStep 328411 = 492617) B492617
theorem B459847 : Blo 239816 459847 := bstep (se 1 (by rfl) ⟨344885, by rfl⟩ : syracuseStep 459847 = 689771) B689771
theorem B820475 : Blo 239816 820475 := bstep (se 1 (by rfl) ⟨615356, by rfl⟩ : syracuseStep 820475 = 1230713) B1230713
theorem B820583 : Blo 239816 820583 := bstep (se 1 (by rfl) ⟨615437, by rfl⟩ : syracuseStep 820583 = 1230875) B1230875
theorem B820637 : Blo 239816 820637 := bstep (se 3 (by rfl) ⟨153869, by rfl⟩ : syracuseStep 820637 = 307739) B307739
theorem B820799 : Blo 239816 820799 := bstep (se 1 (by rfl) ⟨615599, by rfl⟩ : syracuseStep 820799 = 1231199) B1231199
theorem B349046909 : Blo 239816 349046909 := bstep (se 3 (by rfl) ⟨65446295, by rfl⟩ : syracuseStep 349046909 = 130892591) B130892591
theorem B1378721 : Blo 239816 1378721 := bstep (se 2 (by rfl) ⟨517020, by rfl⟩ : syracuseStep 1378721 = 1034041) B1034041
theorem B1870249 : Blo 239816 1870249 := bstep (se 2 (by rfl) ⟨701343, by rfl⟩ : syracuseStep 1870249 = 1402687) B1402687
theorem B461639 : Blo 239816 461639 := bstep (se 1 (by rfl) ⟨346229, by rfl⟩ : syracuseStep 461639 = 692459) B692459
theorem B461897 : Blo 239816 461897 := bstep (se 2 (by rfl) ⟨173211, by rfl⟩ : syracuseStep 461897 = 346423) B346423
theorem B363839 : Blo 239816 363839 := bstep (se 1 (by rfl) ⟨272879, by rfl⟩ : syracuseStep 363839 = 545759) B545759
theorem B3214829 : Blo 239816 3214829 := bstep (se 3 (by rfl) ⟨602780, by rfl⟩ : syracuseStep 3214829 = 1205561) B1205561
theorem B2625119 : Blo 239816 2625119 := bstep (se 1 (by rfl) ⟨1968839, by rfl⟩ : syracuseStep 2625119 = 3937679) B3937679
theorem B462505 : Blo 239816 462505 := bstep (se 2 (by rfl) ⟨173439, by rfl⟩ : syracuseStep 462505 = 346879) B346879
theorem B364223 : Blo 239816 364223 := bstep (se 1 (by rfl) ⟨273167, by rfl⟩ : syracuseStep 364223 = 546335) B546335
theorem B364571 : Blo 239816 364571 := bstep (se 1 (by rfl) ⟨273428, by rfl⟩ : syracuseStep 364571 = 546857) B546857
theorem B1380635 : Blo 239816 1380635 := bstep (se 1 (by rfl) ⟨1035476, by rfl⟩ : syracuseStep 1380635 = 2070953) B2070953
theorem B364991 : Blo 239816 364991 := bstep (se 1 (by rfl) ⟨273743, by rfl⟩ : syracuseStep 364991 = 547487) B547487
theorem B627191 : Blo 239816 627191 := bstep (se 1 (by rfl) ⟨470393, by rfl⟩ : syracuseStep 627191 = 940787) B940787
theorem B13177565 : Blo 239816 13177565 := bstep (se 3 (by rfl) ⟨2470793, by rfl⟩ : syracuseStep 13177565 = 4941587) B4941587
theorem B365609 : Blo 239816 365609 := bstep (se 2 (by rfl) ⟨137103, by rfl⟩ : syracuseStep 365609 = 274207) B274207
theorem B3511457 : Blo 239816 3511457 := bstep (se 2 (by rfl) ⟨1316796, by rfl⟩ : syracuseStep 3511457 = 2633593) B2633593
theorem B1840481 : Blo 239816 1840481 := bstep (se 2 (by rfl) ⟨690180, by rfl⟩ : syracuseStep 1840481 = 1380361) B1380361
theorem B694057 : Blo 239816 694057 := bstep (se 2 (by rfl) ⟨260271, by rfl⟩ : syracuseStep 694057 = 520543) B520543
theorem B1840967 : Blo 239816 1840967 := bstep (se 1 (by rfl) ⟨1380725, by rfl⟩ : syracuseStep 1840967 = 2761451) B2761451
theorem B923795 : Blo 239816 923795 := bstep (se 1 (by rfl) ⟨692846, by rfl⟩ : syracuseStep 923795 = 1385693) B1385693
theorem B3250601 : Blo 239816 3250601 := bstep (se 2 (by rfl) ⟨1218975, by rfl⟩ : syracuseStep 3250601 = 2437951) B2437951
theorem B825815 : Blo 239816 825815 := bstep (se 1 (by rfl) ⟨619361, by rfl⟩ : syracuseStep 825815 = 1238723) B1238723
theorem B924479 : Blo 239816 924479 := bstep (se 1 (by rfl) ⟨693359, by rfl⟩ : syracuseStep 924479 = 1386719) B1386719
theorem B3907385 : Blo 239816 3907385 := bstep (se 2 (by rfl) ⟨1465269, by rfl⟩ : syracuseStep 3907385 = 2930539) B2930539
theorem B271687 : Blo 239816 271687 := bstep (se 1 (by rfl) ⟨203765, by rfl⟩ : syracuseStep 271687 = 407531) B407531
theorem B1746305 : Blo 239816 1746305 := bstep (se 2 (by rfl) ⟨654864, by rfl⟩ : syracuseStep 1746305 = 1309729) B1309729
theorem B239823 : Blo 239816 239823 := bstep (se 1 (by rfl) ⟨179867, by rfl⟩ : syracuseStep 239823 = 359735) B359735
theorem B239943 : Blo 239816 239943 := bstep (se 1 (by rfl) ⟨179957, by rfl⟩ : syracuseStep 239943 = 359915) B359915
theorem B2206111 : Blo 239816 2206111 := bstep (se 1 (by rfl) ⟨1654583, by rfl⟩ : syracuseStep 2206111 = 3309167) B3309167
theorem B240079 : Blo 239816 240079 := bstep (se 1 (by rfl) ⟨180059, by rfl⟩ : syracuseStep 240079 = 360119) B360119
theorem B240219 : Blo 239816 240219 := bstep (se 1 (by rfl) ⟨180164, by rfl⟩ : syracuseStep 240219 = 360329) B360329
theorem B7940717 : Blo 239816 7940717 := bstep (se 3 (by rfl) ⟨1488884, by rfl⟩ : syracuseStep 7940717 = 2977769) B2977769
theorem B240383 : Blo 239816 240383 := bstep (se 1 (by rfl) ⟨180287, by rfl⟩ : syracuseStep 240383 = 360575) B360575
theorem B240575 : Blo 239816 240575 := bstep (se 1 (by rfl) ⟨180431, by rfl⟩ : syracuseStep 240575 = 360863) B360863
theorem B14035913 : Blo 239816 14035913 := bstep (se 2 (by rfl) ⟨5263467, by rfl⟩ : syracuseStep 14035913 = 10526935) B10526935
theorem B240751 : Blo 239816 240751 := bstep (se 1 (by rfl) ⟨180563, by rfl⟩ : syracuseStep 240751 = 361127) B361127
theorem B240831 : Blo 239816 240831 := bstep (se 1 (by rfl) ⟨180623, by rfl⟩ : syracuseStep 240831 = 361247) B361247
theorem B240847 : Blo 239816 240847 := bstep (se 1 (by rfl) ⟨180635, by rfl⟩ : syracuseStep 240847 = 361271) B361271
theorem B240967 : Blo 239816 240967 := bstep (se 1 (by rfl) ⟨180725, by rfl⟩ : syracuseStep 240967 = 361451) B361451
theorem B241307 : Blo 239816 241307 := bstep (se 1 (by rfl) ⟨180980, by rfl⟩ : syracuseStep 241307 = 361961) B361961
theorem B241567 : Blo 239816 241567 := bstep (se 1 (by rfl) ⟨181175, by rfl⟩ : syracuseStep 241567 = 362351) B362351
theorem B241691 : Blo 239816 241691 := bstep (se 1 (by rfl) ⟨181268, by rfl⟩ : syracuseStep 241691 = 362537) B362537
theorem B241711 : Blo 239816 241711 := bstep (se 1 (by rfl) ⟨181283, by rfl⟩ : syracuseStep 241711 = 362567) B362567
theorem B241831 : Blo 239816 241831 := bstep (se 1 (by rfl) ⟨181373, by rfl⟩ : syracuseStep 241831 = 362747) B362747
theorem B241967 : Blo 239816 241967 := bstep (se 1 (by rfl) ⟨181475, by rfl⟩ : syracuseStep 241967 = 362951) B362951
theorem B242111 : Blo 239816 242111 := bstep (se 1 (by rfl) ⟨181583, by rfl⟩ : syracuseStep 242111 = 363167) B363167
theorem B242143 : Blo 239816 242143 := bstep (se 1 (by rfl) ⟨181607, by rfl⟩ : syracuseStep 242143 = 363215) B363215
theorem B242207 : Blo 239816 242207 := bstep (se 1 (by rfl) ⟨181655, by rfl⟩ : syracuseStep 242207 = 363311) B363311
theorem B1749559 : Blo 239816 1749559 := bstep (se 1 (by rfl) ⟨1312169, by rfl⟩ : syracuseStep 1749559 = 2624339) B2624339
theorem B242287 : Blo 239816 242287 := bstep (se 1 (by rfl) ⟨181715, by rfl⟩ : syracuseStep 242287 = 363431) B363431
theorem B242407 : Blo 239816 242407 := bstep (se 1 (by rfl) ⟨181805, by rfl⟩ : syracuseStep 242407 = 363611) B363611
theorem B242459 : Blo 239816 242459 := bstep (se 1 (by rfl) ⟨181844, by rfl⟩ : syracuseStep 242459 = 363689) B363689
theorem B1061687 : Blo 239816 1061687 := bstep (se 1 (by rfl) ⟨796265, by rfl⟩ : syracuseStep 1061687 = 1592531) B1592531
theorem B406363 : Blo 239816 406363 := bstep (se 1 (by rfl) ⟨304772, by rfl⟩ : syracuseStep 406363 = 609545) B609545
theorem B1848257 : Blo 239816 1848257 := bstep (se 2 (by rfl) ⟨693096, by rfl⟩ : syracuseStep 1848257 = 1386193) B1386193
theorem B439265 : Blo 239816 439265 := bstep (se 2 (by rfl) ⟨164724, by rfl⟩ : syracuseStep 439265 = 329449) B329449
theorem B242735 : Blo 239816 242735 := bstep (se 1 (by rfl) ⟨182051, by rfl⟩ : syracuseStep 242735 = 364103) B364103
theorem B242855 : Blo 239816 242855 := bstep (se 1 (by rfl) ⟨182141, by rfl⟩ : syracuseStep 242855 = 364283) B364283
theorem B1226015 : Blo 239816 1226015 := bstep (se 1 (by rfl) ⟨919511, by rfl⟩ : syracuseStep 1226015 = 1839023) B1839023
theorem B243015 : Blo 239816 243015 := bstep (se 1 (by rfl) ⟨182261, by rfl⟩ : syracuseStep 243015 = 364523) B364523
theorem B1848743 : Blo 239816 1848743 := bstep (se 1 (by rfl) ⟨1386557, by rfl⟩ : syracuseStep 1848743 = 2773115) B2773115
theorem B931355 : Blo 239816 931355 := bstep (se 1 (by rfl) ⟨698516, by rfl⟩ : syracuseStep 931355 = 1397033) B1397033
theorem B407423 : Blo 239816 407423 := bstep (se 1 (by rfl) ⟨305567, by rfl⟩ : syracuseStep 407423 = 611135) B611135
theorem B243707 : Blo 239816 243707 := bstep (se 1 (by rfl) ⟨182780, by rfl⟩ : syracuseStep 243707 = 365561) B365561
theorem B407659 : Blo 239816 407659 := bstep (se 1 (by rfl) ⟨305744, by rfl⟩ : syracuseStep 407659 = 611489) B611489
theorem B2079017 : Blo 239816 2079017 := bstep (se 2 (by rfl) ⟨779631, by rfl⟩ : syracuseStep 2079017 = 1559263) B1559263
theorem B540755 : Blo 239816 540755 := bstep (se 1 (by rfl) ⟨405566, by rfl⟩ : syracuseStep 540755 = 811133) B811133
theorem B540809 : Blo 239816 540809 := bstep (se 2 (by rfl) ⟨202803, by rfl⟩ : syracuseStep 540809 = 405607) B405607
theorem B1229417 : Blo 239816 1229417 := bstep (se 2 (by rfl) ⟨461031, by rfl⟩ : syracuseStep 1229417 = 922063) B922063
theorem B541511 : Blo 239816 541511 := bstep (se 1 (by rfl) ⟨406133, by rfl⟩ : syracuseStep 541511 = 812267) B812267
theorem B607135 : Blo 239816 607135 := bstep (se 1 (by rfl) ⟨455351, by rfl⟩ : syracuseStep 607135 = 910703) B910703
theorem B1033343 : Blo 239816 1033343 := bstep (se 1 (by rfl) ⟨775007, by rfl⟩ : syracuseStep 1033343 = 1550015) B1550015
theorem B1328899 : Blo 239816 1328899 := bstep (se 1 (by rfl) ⟨996674, by rfl⟩ : syracuseStep 1328899 = 1993349) B1993349
theorem B1230803 : Blo 239816 1230803 := bstep (se 1 (by rfl) ⟨923102, by rfl⟩ : syracuseStep 1230803 = 1846205) B1846205
theorem B2213993 : Blo 239816 2213993 := bstep (se 2 (by rfl) ⟨830247, by rfl⟩ : syracuseStep 2213993 = 1660495) B1660495
theorem B1099919 : Blo 239816 1099919 := bstep (se 1 (by rfl) ⟨824939, by rfl⟩ : syracuseStep 1099919 = 1649879) B1649879
theorem B609353 : Blo 239816 609353 := bstep (se 2 (by rfl) ⟨228507, by rfl⟩ : syracuseStep 609353 = 457015) B457015
theorem B5098729 : Blo 239816 5098729 := bstep (se 2 (by rfl) ⟨1912023, by rfl⟩ : syracuseStep 5098729 = 3824047) B3824047
theorem B1166663 : Blo 239816 1166663 := bstep (se 1 (by rfl) ⟨874997, by rfl⟩ : syracuseStep 1166663 = 1749995) B1749995
theorem B1822985 : Blo 239816 1822985 := bstep (se 2 (by rfl) ⟨683619, by rfl⟩ : syracuseStep 1822985 = 1367239) B1367239
theorem B1069331 : Blo 239816 1069331 := bstep (se 1 (by rfl) ⟨801998, by rfl⟩ : syracuseStep 1069331 = 1603997) B1603997
theorem B5886857 : Blo 239816 5886857 := bstep (se 2 (by rfl) ⟨2207571, by rfl⟩ : syracuseStep 5886857 = 4415143) B4415143
theorem B1233953 : Blo 239816 1233953 := bstep (se 2 (by rfl) ⟨462732, by rfl⟩ : syracuseStep 1233953 = 925465) B925465
theorem B33576281 : Blo 239816 33576281 := bstep (se 2 (by rfl) ⟨12591105, by rfl⟩ : syracuseStep 33576281 = 25182211) B25182211
theorem B808555 : Blo 239816 808555 := bstep (se 1 (by rfl) ⟨606416, by rfl⟩ : syracuseStep 808555 = 1212833) B1212833
theorem B611995 : Blo 239816 611995 := bstep (se 1 (by rfl) ⟨458996, by rfl⟩ : syracuseStep 611995 = 917993) B917993
theorem B2086603 : Blo 239816 2086603 := bstep (se 1 (by rfl) ⟨1564952, by rfl⟩ : syracuseStep 2086603 = 3129905) B3129905
theorem B514279 : Blo 239816 514279 := bstep (se 1 (by rfl) ⟨385709, by rfl⟩ : syracuseStep 514279 = 771419) B771419
theorem B2054483 : Blo 239816 2054483 := bstep (se 1 (by rfl) ⟨1540862, by rfl⟩ : syracuseStep 2054483 = 3081725) B3081725
theorem B809567 : Blo 239816 809567 := bstep (se 1 (by rfl) ⟨607175, by rfl⟩ : syracuseStep 809567 = 1214351) B1214351
theorem B1039031 : Blo 239816 1039031 := bstep (se 1 (by rfl) ⟨779273, by rfl⟩ : syracuseStep 1039031 = 1558547) B1558547
theorem B547721 : Blo 239816 547721 := bstep (se 2 (by rfl) ⟨205395, by rfl⟩ : syracuseStep 547721 = 410791) B410791
theorem B515099 : Blo 239816 515099 := bstep (se 1 (by rfl) ⟨386324, by rfl⟩ : syracuseStep 515099 = 772649) B772649
theorem B1236059 : Blo 239816 1236059 := bstep (se 1 (by rfl) ⟨927044, by rfl⟩ : syracuseStep 1236059 = 1854089) B1854089
theorem B548027 : Blo 239816 548027 := bstep (se 1 (by rfl) ⟨411020, by rfl⟩ : syracuseStep 548027 = 822041) B822041
theorem B548063 : Blo 239816 548063 := bstep (se 1 (by rfl) ⟨411047, by rfl⟩ : syracuseStep 548063 = 822095) B822095
theorem B1957229 : Blo 239816 1957229 := bstep (se 3 (by rfl) ⟨366980, by rfl⟩ : syracuseStep 1957229 = 733961) B733961
theorem B548279 : Blo 239816 548279 := bstep (se 1 (by rfl) ⟨411209, by rfl⟩ : syracuseStep 548279 = 822419) B822419
theorem B384895 : Blo 239816 384895 := bstep (se 1 (by rfl) ⟨288671, by rfl⟩ : syracuseStep 384895 = 577343) B577343
theorem B614375 : Blo 239816 614375 := bstep (se 1 (by rfl) ⟨460781, by rfl⟩ : syracuseStep 614375 = 921563) B921563
theorem B614587 : Blo 239816 614587 := bstep (se 1 (by rfl) ⟨460940, by rfl⟩ : syracuseStep 614587 = 921881) B921881
theorem B811403 : Blo 239816 811403 := bstep (se 1 (by rfl) ⟨608552, by rfl⟩ : syracuseStep 811403 = 1217105) B1217105
theorem B2613707 : Blo 239816 2613707 := bstep (se 1 (by rfl) ⟨1960280, by rfl⟩ : syracuseStep 2613707 = 3920561) B3920561
theorem B1368697 : Blo 239816 1368697 := bstep (se 2 (by rfl) ⟨513261, by rfl⟩ : syracuseStep 1368697 = 1026523) B1026523
theorem B517175 : Blo 239816 517175 := bstep (se 1 (by rfl) ⟨387881, by rfl⟩ : syracuseStep 517175 = 775763) B775763
theorem B583649 : Blo 239816 583649 := bstep (se 2 (by rfl) ⟨218868, by rfl⟩ : syracuseStep 583649 = 437737) B437737
theorem B1829303 : Blo 239816 1829303 := bstep (se 1 (by rfl) ⟨1371977, by rfl⟩ : syracuseStep 1829303 = 2743955) B2743955
theorem B518815 : Blo 239816 518815 := bstep (se 1 (by rfl) ⟨389111, by rfl⟩ : syracuseStep 518815 = 778223) B778223
theorem B977579 : Blo 239816 977579 := bstep (se 1 (by rfl) ⟨733184, by rfl⟩ : syracuseStep 977579 = 1466369) B1466369
theorem B256879 : Blo 239816 256879 := bstep (se 1 (by rfl) ⟨192659, by rfl⟩ : syracuseStep 256879 = 385319) B385319
theorem B912329 : Blo 239816 912329 := bstep (se 2 (by rfl) ⟨342123, by rfl⟩ : syracuseStep 912329 = 684247) B684247
theorem B3107969 : Blo 239816 3107969 := bstep (se 2 (by rfl) ⟨1165488, by rfl⟩ : syracuseStep 3107969 = 2330977) B2330977
theorem B912815 : Blo 239816 912815 := bstep (se 1 (by rfl) ⟨684611, by rfl⟩ : syracuseStep 912815 = 1369223) B1369223
theorem B1109483 : Blo 239816 1109483 := bstep (se 1 (by rfl) ⟨832112, by rfl⟩ : syracuseStep 1109483 = 1664225) B1664225
theorem B683711 : Blo 239816 683711 := bstep (se 1 (by rfl) ⟨512783, by rfl⟩ : syracuseStep 683711 = 1025567) B1025567
theorem B1175273 : Blo 239816 1175273 := bstep (se 2 (by rfl) ⟨440727, by rfl⟩ : syracuseStep 1175273 = 881455) B881455
theorem B978713 : Blo 239816 978713 := bstep (se 2 (by rfl) ⟨367017, by rfl⟩ : syracuseStep 978713 = 734035) B734035
theorem B1830761 : Blo 239816 1830761 := bstep (se 2 (by rfl) ⟨686535, by rfl⟩ : syracuseStep 1830761 = 1373071) B1373071
theorem B4124681 : Blo 239816 4124681 := bstep (se 2 (by rfl) ⟨1546755, by rfl⟩ : syracuseStep 4124681 = 3093511) B3093511
theorem B258271 : Blo 239816 258271 := bstep (se 1 (by rfl) ⟨193703, by rfl⟩ : syracuseStep 258271 = 387407) B387407
theorem B913787 : Blo 239816 913787 := bstep (se 1 (by rfl) ⟨685340, by rfl⟩ : syracuseStep 913787 = 1370681) B1370681
theorem B1372571 : Blo 239816 1372571 := bstep (se 1 (by rfl) ⟨1029428, by rfl⟩ : syracuseStep 1372571 = 2058857) B2058857
theorem B815723 : Blo 239816 815723 := bstep (se 1 (by rfl) ⟨611792, by rfl⟩ : syracuseStep 815723 = 1223585) B1223585
theorem B455375 : Blo 239816 455375 := bstep (se 1 (by rfl) ⟨341531, by rfl⟩ : syracuseStep 455375 = 683063) B683063
theorem B816317 : Blo 239816 816317 := bstep (se 3 (by rfl) ⟨153059, by rfl⟩ : syracuseStep 816317 = 306119) B306119
theorem B2061521 : Blo 239816 2061521 := bstep (se 2 (by rfl) ⟨773070, by rfl⟩ : syracuseStep 2061521 = 1546141) B1546141
theorem B9369107 : Blo 239816 9369107 := bstep (se 1 (by rfl) ⟨7026830, by rfl⟩ : syracuseStep 9369107 = 14053661) B14053661
theorem B390719 : Blo 239816 390719 := bstep (se 1 (by rfl) ⟨293039, by rfl⟩ : syracuseStep 390719 = 586079) B586079
theorem B456347 : Blo 239816 456347 := bstep (se 1 (by rfl) ⟨342260, by rfl⟩ : syracuseStep 456347 = 684521) B684521
theorem B3471437 : Blo 239816 3471437 := bstep (se 3 (by rfl) ⟨650894, by rfl⟩ : syracuseStep 3471437 = 1301789) B1301789
theorem B15759521 : Blo 239816 15759521 := bstep (se 2 (by rfl) ⟨5909820, by rfl⟩ : syracuseStep 15759521 = 11819641) B11819641
theorem B916049 : Blo 239816 916049 := bstep (se 2 (by rfl) ⟨343518, by rfl⟩ : syracuseStep 916049 = 687037) B687037
theorem B28146653 : Blo 239816 28146653 := bstep (se 3 (by rfl) ⟨5277497, by rfl⟩ : syracuseStep 28146653 = 10554995) B10554995
theorem B457903 : Blo 239816 457903 := bstep (se 1 (by rfl) ⟨343427, by rfl⟩ : syracuseStep 457903 = 686855) B686855
theorem B359903 : Blo 239816 359903 := bstep (se 1 (by rfl) ⟨269927, by rfl⟩ : syracuseStep 359903 = 539855) B539855
theorem B359963 : Blo 239816 359963 := bstep (se 1 (by rfl) ⟨269972, by rfl⟩ : syracuseStep 359963 = 539945) B539945
theorem B1834649 : Blo 239816 1834649 := bstep (se 2 (by rfl) ⟨687993, by rfl⟩ : syracuseStep 1834649 = 1375987) B1375987
theorem B818855 : Blo 239816 818855 := bstep (se 1 (by rfl) ⟨614141, by rfl⟩ : syracuseStep 818855 = 1228283) B1228283
theorem B1736387 : Blo 239816 1736387 := bstep (se 1 (by rfl) ⟨1302290, by rfl⟩ : syracuseStep 1736387 = 2604581) B2604581
theorem B360155 : Blo 239816 360155 := bstep (se 1 (by rfl) ⟨270116, by rfl⟩ : syracuseStep 360155 = 540233) B540233
theorem B851707 : Blo 239816 851707 := bstep (se 1 (by rfl) ⟨638780, by rfl⟩ : syracuseStep 851707 = 1277561) B1277561
theorem B360383 : Blo 239816 360383 := bstep (se 1 (by rfl) ⟨270287, by rfl⟩ : syracuseStep 360383 = 540575) B540575
theorem B360503 : Blo 239816 360503 := bstep (se 1 (by rfl) ⟨270377, by rfl⟩ : syracuseStep 360503 = 540755) B540755
theorem B2490425 : Blo 239816 2490425 := bstep (se 2 (by rfl) ⟨933909, by rfl⟩ : syracuseStep 2490425 = 1867819) B1867819
theorem B360539 : Blo 239816 360539 := bstep (se 1 (by rfl) ⟨270404, by rfl⟩ : syracuseStep 360539 = 540809) B540809
theorem B819449 : Blo 239816 819449 := bstep (se 2 (by rfl) ⟨307293, by rfl⟩ : syracuseStep 819449 = 614587) B614587
theorem B819611 : Blo 239816 819611 := bstep (se 1 (by rfl) ⟨614708, by rfl⟩ : syracuseStep 819611 = 1229417) B1229417
theorem B361007 : Blo 239816 361007 := bstep (se 1 (by rfl) ⟨270755, by rfl⟩ : syracuseStep 361007 = 541511) B541511
theorem B2851549 : Blo 239816 2851549 := bstep (se 3 (by rfl) ⟨534665, by rfl⟩ : syracuseStep 2851549 = 1069331) B1069331
theorem B688895 : Blo 239816 688895 := bstep (se 1 (by rfl) ⟨516671, by rfl⟩ : syracuseStep 688895 = 1033343) B1033343
theorem B1377445 : Blo 239816 1377445 := bstep (se 4 (by rfl) ⟨129135, by rfl⟩ : syracuseStep 1377445 = 258271) B258271
theorem B820535 : Blo 239816 820535 := bstep (se 1 (by rfl) ⟨615401, by rfl⟩ : syracuseStep 820535 = 1230803) B1230803
theorem B1475995 : Blo 239816 1475995 := bstep (se 1 (by rfl) ⟨1106996, by rfl⟩ : syracuseStep 1475995 = 2213993) B2213993
theorem B919147 : Blo 239816 919147 := bstep (se 1 (by rfl) ⟨689360, by rfl⟩ : syracuseStep 919147 = 1378721) B1378721
theorem B362249 : Blo 239816 362249 := bstep (se 2 (by rfl) ⟨135843, by rfl⟩ : syracuseStep 362249 = 271687) B271687
theorem B1771865 : Blo 239816 1771865 := bstep (se 2 (by rfl) ⟨664449, by rfl⟩ : syracuseStep 1771865 = 1328899) B1328899
theorem B1215323 : Blo 239816 1215323 := bstep (se 1 (by rfl) ⟨911492, by rfl⟩ : syracuseStep 1215323 = 1822985) B1822985
theorem B920423 : Blo 239816 920423 := bstep (se 1 (by rfl) ⟨690317, by rfl⟩ : syracuseStep 920423 = 1380635) B1380635
theorem B8785043 : Blo 239816 8785043 := bstep (se 1 (by rfl) ⟨6588782, by rfl⟩ : syracuseStep 8785043 = 13177565) B13177565
theorem B2493665 : Blo 239816 2493665 := bstep (se 2 (by rfl) ⟨935124, by rfl⟩ : syracuseStep 2493665 = 1870249) B1870249
theorem B822635 : Blo 239816 822635 := bstep (se 1 (by rfl) ⟨616976, by rfl⟩ : syracuseStep 822635 = 1233953) B1233953
theorem B691753 : Blo 239816 691753 := bstep (se 2 (by rfl) ⟨259407, by rfl⟩ : syracuseStep 691753 = 518815) B518815
theorem B22384187 : Blo 239816 22384187 := bstep (se 1 (by rfl) ⟨16788140, by rfl⟩ : syracuseStep 22384187 = 33576281) B33576281
theorem B2167067 : Blo 239816 2167067 := bstep (se 1 (by rfl) ⟨1625300, by rfl⟩ : syracuseStep 2167067 = 3250601) B3250601
theorem B692687 : Blo 239816 692687 := bstep (se 1 (by rfl) ⟨519515, by rfl⟩ : syracuseStep 692687 = 1039031) B1039031
theorem B365147 : Blo 239816 365147 := bstep (se 1 (by rfl) ⟨273860, by rfl⟩ : syracuseStep 365147 = 547721) B547721
theorem B824039 : Blo 239816 824039 := bstep (se 1 (by rfl) ⟨618029, by rfl⟩ : syracuseStep 824039 = 1236059) B1236059
theorem B365351 : Blo 239816 365351 := bstep (se 1 (by rfl) ⟨274013, by rfl⟩ : syracuseStep 365351 = 548027) B548027
theorem B365375 : Blo 239816 365375 := bstep (se 1 (by rfl) ⟨274031, by rfl⟩ : syracuseStep 365375 = 548063) B548063
theorem B365519 : Blo 239816 365519 := bstep (se 1 (by rfl) ⟨274139, by rfl⟩ : syracuseStep 365519 = 548279) B548279
theorem B1742471 : Blo 239816 1742471 := bstep (se 1 (by rfl) ⟨1306853, by rfl⟩ : syracuseStep 1742471 = 2613707) B2613707
theorem B2332745 : Blo 239816 2332745 := bstep (se 2 (by rfl) ⟨874779, by rfl⟩ : syracuseStep 2332745 = 1749559) B1749559
theorem B2202173 : Blo 239816 2202173 := bstep (se 3 (by rfl) ⟨412907, by rfl⟩ : syracuseStep 2202173 = 825815) B825815
theorem B1219535 : Blo 239816 1219535 := bstep (se 1 (by rfl) ⟨914651, by rfl⟩ : syracuseStep 1219535 = 1829303) B1829303
theorem B2071979 : Blo 239816 2071979 := bstep (se 1 (by rfl) ⟨1553984, by rfl⟩ : syracuseStep 2071979 = 3107969) B3107969
theorem B925409 : Blo 239816 925409 := bstep (se 2 (by rfl) ⟨347028, by rfl⟩ : syracuseStep 925409 = 694057) B694057
theorem B1220507 : Blo 239816 1220507 := bstep (se 1 (by rfl) ⟨915380, by rfl⟩ : syracuseStep 1220507 = 1830761) B1830761
theorem B303583 : Blo 239816 303583 := bstep (se 1 (by rfl) ⟨227687, by rfl⟩ : syracuseStep 303583 = 455375) B455375
theorem B304231 : Blo 239816 304231 := bstep (se 1 (by rfl) ⟨228173, by rfl⟩ : syracuseStep 304231 = 456347) B456347
theorem B271615 : Blo 239816 271615 := bstep (se 1 (by rfl) ⟨203711, by rfl⟩ : syracuseStep 271615 = 407423) B407423
theorem B1386011 : Blo 239816 1386011 := bstep (se 1 (by rfl) ⟨1039508, by rfl⟩ : syracuseStep 1386011 = 2079017) B2079017
theorem B239935 : Blo 239816 239935 := bstep (se 1 (by rfl) ⟨179951, by rfl⟩ : syracuseStep 239935 = 359903) B359903
theorem B239975 : Blo 239816 239975 := bstep (se 1 (by rfl) ⟨179981, by rfl⟩ : syracuseStep 239975 = 359963) B359963
theorem B1223099 : Blo 239816 1223099 := bstep (se 1 (by rfl) ⟨917324, by rfl⟩ : syracuseStep 1223099 = 1834649) B1834649
theorem B1157591 : Blo 239816 1157591 := bstep (se 1 (by rfl) ⟨868193, by rfl⟩ : syracuseStep 1157591 = 1736387) B1736387
theorem B240103 : Blo 239816 240103 := bstep (se 1 (by rfl) ⟨180077, by rfl⟩ : syracuseStep 240103 = 360155) B360155
theorem B240255 : Blo 239816 240255 := bstep (se 1 (by rfl) ⟨180191, by rfl⟩ : syracuseStep 240255 = 360383) B360383
theorem B1223423 : Blo 239816 1223423 := bstep (se 1 (by rfl) ⟨917567, by rfl⟩ : syracuseStep 1223423 = 1835135) B1835135
theorem B7908191 : Blo 239816 7908191 := bstep (se 1 (by rfl) ⟨5931143, by rfl⟩ : syracuseStep 7908191 = 11862287) B11862287
theorem B240511 : Blo 239816 240511 := bstep (se 1 (by rfl) ⟨180383, by rfl⟩ : syracuseStep 240511 = 360767) B360767
theorem B240623 : Blo 239816 240623 := bstep (se 1 (by rfl) ⟨180467, by rfl⟩ : syracuseStep 240623 = 360935) B360935
theorem B4926901 : Blo 239816 4926901 := bstep (se 5 (by rfl) ⟨230948, by rfl⟩ : syracuseStep 4926901 = 461897) B461897
theorem B437881 : Blo 239816 437881 := bstep (se 2 (by rfl) ⟨164205, by rfl⟩ : syracuseStep 437881 = 328411) B328411
theorem B232697939 : Blo 239816 232697939 := bstep (se 1 (by rfl) ⟨174523454, by rfl⟩ : syracuseStep 232697939 = 349046909) B349046909
theorem B406235 : Blo 239816 406235 := bstep (se 1 (by rfl) ⟨304676, by rfl⟩ : syracuseStep 406235 = 609353) B609353
theorem B242559 : Blo 239816 242559 := bstep (se 1 (by rfl) ⟨181919, by rfl⟩ : syracuseStep 242559 = 363839) B363839
theorem B2143219 : Blo 239816 2143219 := bstep (se 1 (by rfl) ⟨1607414, by rfl⟩ : syracuseStep 2143219 = 3214829) B3214829
theorem B1750079 : Blo 239816 1750079 := bstep (se 1 (by rfl) ⟨1312559, by rfl⟩ : syracuseStep 1750079 = 2625119) B2625119
theorem B242815 : Blo 239816 242815 := bstep (se 1 (by rfl) ⟨182111, by rfl⟩ : syracuseStep 242815 = 364223) B364223
theorem B243047 : Blo 239816 243047 := bstep (se 1 (by rfl) ⟨182285, by rfl⟩ : syracuseStep 243047 = 364571) B364571
theorem B243327 : Blo 239816 243327 := bstep (se 1 (by rfl) ⟨182495, by rfl⟩ : syracuseStep 243327 = 364991) B364991
theorem B243739 : Blo 239816 243739 := bstep (se 1 (by rfl) ⟨182804, by rfl⟩ : syracuseStep 243739 = 365609) B365609
theorem B2340971 : Blo 239816 2340971 := bstep (se 1 (by rfl) ⟨1755728, by rfl⟩ : syracuseStep 2340971 = 3511457) B3511457
theorem B1226987 : Blo 239816 1226987 := bstep (se 1 (by rfl) ⟨920240, by rfl⟩ : syracuseStep 1226987 = 1840481) B1840481
theorem B342505 : Blo 239816 342505 := bstep (se 2 (by rfl) ⟨128439, by rfl⟩ : syracuseStep 342505 = 256879) B256879
theorem B1227311 : Blo 239816 1227311 := bstep (se 1 (by rfl) ⟨920483, by rfl⟩ : syracuseStep 1227311 = 1840967) B1840967
theorem B6798305 : Blo 239816 6798305 := bstep (se 2 (by rfl) ⟨2549364, by rfl⟩ : syracuseStep 6798305 = 5098729) B5098729
theorem B539711 : Blo 239816 539711 := bstep (se 1 (by rfl) ⟨404783, by rfl⟩ : syracuseStep 539711 = 809567) B809567
theorem B2604923 : Blo 239816 2604923 := bstep (se 1 (by rfl) ⟨1953692, by rfl⟩ : syracuseStep 2604923 = 3907385) B3907385
theorem B409583 : Blo 239816 409583 := bstep (se 1 (by rfl) ⟨307187, by rfl⟩ : syracuseStep 409583 = 614375) B614375
theorem B540935 : Blo 239816 540935 := bstep (se 1 (by rfl) ⟨405701, by rfl⟩ : syracuseStep 540935 = 811403) B811403
theorem B2933117 : Blo 239816 2933117 := bstep (se 3 (by rfl) ⟨549959, by rfl⟩ : syracuseStep 2933117 = 1099919) B1099919
theorem B344783 : Blo 239816 344783 := bstep (se 1 (by rfl) ⟨258587, by rfl⟩ : syracuseStep 344783 = 517175) B517175
theorem B1164203 : Blo 239816 1164203 := bstep (se 1 (by rfl) ⟨873152, by rfl⟩ : syracuseStep 1164203 = 1746305) B1746305
theorem B541817 : Blo 239816 541817 := bstep (se 2 (by rfl) ⟨203181, by rfl⟩ : syracuseStep 541817 = 406363) B406363
theorem B5293811 : Blo 239816 5293811 := bstep (se 1 (by rfl) ⟨3970358, by rfl⟩ : syracuseStep 5293811 = 7940717) B7940717
theorem B9357275 : Blo 239816 9357275 := bstep (se 1 (by rfl) ⟨7017956, by rfl⟩ : syracuseStep 9357275 = 14035913) B14035913
theorem B608219 : Blo 239816 608219 := bstep (se 1 (by rfl) ⟨456164, by rfl⟩ : syracuseStep 608219 = 912329) B912329
theorem B1231037 : Blo 239816 1231037 := bstep (se 3 (by rfl) ⟨230819, by rfl⟩ : syracuseStep 1231037 = 461639) B461639
theorem B608543 : Blo 239816 608543 := bstep (se 1 (by rfl) ⟨456407, by rfl⟩ : syracuseStep 608543 = 912815) B912815
theorem B739655 : Blo 239816 739655 := bstep (se 1 (by rfl) ⟨554741, by rfl⟩ : syracuseStep 739655 = 1109483) B1109483
theorem B543545 : Blo 239816 543545 := bstep (se 2 (by rfl) ⟨203829, by rfl⟩ : syracuseStep 543545 = 407659) B407659
theorem B609191 : Blo 239816 609191 := bstep (se 1 (by rfl) ⟨456893, by rfl⟩ : syracuseStep 609191 = 913787) B913787
theorem B543815 : Blo 239816 543815 := bstep (se 1 (by rfl) ⟨407861, by rfl⟩ : syracuseStep 543815 = 815723) B815723
theorem B707791 : Blo 239816 707791 := bstep (se 1 (by rfl) ⟨530843, by rfl⟩ : syracuseStep 707791 = 1061687) B1061687
theorem B1232171 : Blo 239816 1232171 := bstep (se 1 (by rfl) ⟨924128, by rfl⟩ : syracuseStep 1232171 = 1848257) B1848257
theorem B544211 : Blo 239816 544211 := bstep (se 1 (by rfl) ⟨408158, by rfl⟩ : syracuseStep 544211 = 816317) B816317
theorem B1232495 : Blo 239816 1232495 := bstep (se 1 (by rfl) ⟨924371, by rfl⟩ : syracuseStep 1232495 = 1848743) B1848743
theorem B6246071 : Blo 239816 6246071 := bstep (se 1 (by rfl) ⟨4684553, by rfl⟩ : syracuseStep 6246071 = 9369107) B9369107
theorem B11128549 : Blo 239816 11128549 := bstep (se 4 (by rfl) ⟨1043301, by rfl⟩ : syracuseStep 11128549 = 2086603) B2086603
theorem B4542437 : Blo 239816 4542437 := bstep (se 4 (by rfl) ⟨425853, by rfl⟩ : syracuseStep 4542437 = 851707) B851707
theorem B2314291 : Blo 239816 2314291 := bstep (se 1 (by rfl) ⟨1735718, by rfl⟩ : syracuseStep 2314291 = 3471437) B3471437
theorem B10506347 : Blo 239816 10506347 := bstep (se 1 (by rfl) ⟨7879760, by rfl⟩ : syracuseStep 10506347 = 15759521) B15759521
theorem B610537 : Blo 239816 610537 := bstep (se 2 (by rfl) ⟨228951, by rfl⟩ : syracuseStep 610537 = 457903) B457903
theorem B610699 : Blo 239816 610699 := bstep (se 1 (by rfl) ⟨458024, by rfl⟩ : syracuseStep 610699 = 916049) B916049
theorem B18764435 : Blo 239816 18764435 := bstep (se 1 (by rfl) ⟨14073326, by rfl⟩ : syracuseStep 18764435 = 28146653) B28146653
theorem B2052773 : Blo 239816 2052773 := bstep (se 4 (by rfl) ⟨192447, by rfl⟩ : syracuseStep 2052773 = 384895) B384895
theorem B545903 : Blo 239816 545903 := bstep (se 1 (by rfl) ⟨409427, by rfl⟩ : syracuseStep 545903 = 818855) B818855
theorem B546479 : Blo 239816 546479 := bstep (se 1 (by rfl) ⟨409859, by rfl⟩ : syracuseStep 546479 = 819719) B819719
theorem B1824929 : Blo 239816 1824929 := bstep (se 2 (by rfl) ⟨684348, by rfl⟩ : syracuseStep 1824929 = 1368697) B1368697
theorem B546983 : Blo 239816 546983 := bstep (se 1 (by rfl) ⟨410237, by rfl⟩ : syracuseStep 546983 = 820475) B820475
theorem B547055 : Blo 239816 547055 := bstep (se 1 (by rfl) ⟨410291, by rfl⟩ : syracuseStep 547055 = 820583) B820583
theorem B547091 : Blo 239816 547091 := bstep (se 1 (by rfl) ⟨410318, by rfl⟩ : syracuseStep 547091 = 820637) B820637
theorem B547199 : Blo 239816 547199 := bstep (se 1 (by rfl) ⟨410399, by rfl⟩ : syracuseStep 547199 = 820799) B820799
theorem B809513 : Blo 239816 809513 := bstep (se 2 (by rfl) ⟨303567, by rfl⟩ : syracuseStep 809513 = 607135) B607135
theorem B613129 : Blo 239816 613129 := bstep (se 2 (by rfl) ⟨229923, by rfl⟩ : syracuseStep 613129 = 459847) B459847
theorem B777775 : Blo 239816 777775 := bstep (se 1 (by rfl) ⟨583331, by rfl⟩ : syracuseStep 777775 = 1166663) B1166663
theorem B418127 : Blo 239816 418127 := bstep (se 1 (by rfl) ⟨313595, by rfl⟩ : syracuseStep 418127 = 627191) B627191
theorem B2941481 : Blo 239816 2941481 := bstep (se 2 (by rfl) ⟨1103055, by rfl⟩ : syracuseStep 2941481 = 2206111) B2206111
theorem B3924571 : Blo 239816 3924571 := bstep (se 1 (by rfl) ⟨2943428, by rfl⟩ : syracuseStep 3924571 = 5886857) B5886857
theorem B615863 : Blo 239816 615863 := bstep (se 1 (by rfl) ⟨461897, by rfl⟩ : syracuseStep 615863 = 923795) B923795
theorem B1369655 : Blo 239816 1369655 := bstep (se 1 (by rfl) ⟨1027241, by rfl⟩ : syracuseStep 1369655 = 2054483) B2054483
theorem B616319 : Blo 239816 616319 := bstep (se 1 (by rfl) ⟨462239, by rfl⟩ : syracuseStep 616319 = 924479) B924479
theorem B616673 : Blo 239816 616673 := bstep (se 2 (by rfl) ⟨231252, by rfl⟩ : syracuseStep 616673 = 462505) B462505
theorem B1304819 : Blo 239816 1304819 := bstep (se 1 (by rfl) ⟨978614, by rfl⟩ : syracuseStep 1304819 = 1957229) B1957229
theorem B389099 : Blo 239816 389099 := bstep (se 1 (by rfl) ⟨291824, by rfl⟩ : syracuseStep 389099 = 583649) B583649
theorem B651719 : Blo 239816 651719 := bstep (se 1 (by rfl) ⟨488789, by rfl⟩ : syracuseStep 651719 = 977579) B977579
theorem B1078073 : Blo 239816 1078073 := bstep (se 2 (by rfl) ⟨404277, by rfl⟩ : syracuseStep 1078073 = 808555) B808555
theorem B815993 : Blo 239816 815993 := bstep (se 2 (by rfl) ⟨305997, by rfl⟩ : syracuseStep 815993 = 611995) B611995
theorem B455807 : Blo 239816 455807 := bstep (se 1 (by rfl) ⟨341855, by rfl⟩ : syracuseStep 455807 = 683711) B683711
theorem B783515 : Blo 239816 783515 := bstep (se 1 (by rfl) ⟨587636, by rfl⟩ : syracuseStep 783515 = 1175273) B1175273
theorem B652475 : Blo 239816 652475 := bstep (se 1 (by rfl) ⟨489356, by rfl⟩ : syracuseStep 652475 = 978713) B978713
theorem B2749787 : Blo 239816 2749787 := bstep (se 1 (by rfl) ⟨2062340, by rfl⟩ : syracuseStep 2749787 = 4124681) B4124681
theorem B1373597 : Blo 239816 1373597 := bstep (se 3 (by rfl) ⟨257549, by rfl⟩ : syracuseStep 1373597 = 515099) B515099
theorem B915047 : Blo 239816 915047 := bstep (se 1 (by rfl) ⟨686285, by rfl⟩ : syracuseStep 915047 = 1372571) B1372571
theorem B685705 : Blo 239816 685705 := bstep (se 2 (by rfl) ⟨257139, by rfl⟩ : syracuseStep 685705 = 514279) B514279
theorem B292843 : Blo 239816 292843 := bstep (se 1 (by rfl) ⟨219632, by rfl⟩ : syracuseStep 292843 = 439265) B439265
theorem B1374347 : Blo 239816 1374347 := bstep (se 1 (by rfl) ⟨1030760, by rfl⟩ : syracuseStep 1374347 = 2061521) B2061521
theorem B817343 : Blo 239816 817343 := bstep (se 1 (by rfl) ⟨613007, by rfl⟩ : syracuseStep 817343 = 1226015) B1226015
theorem B620903 : Blo 239816 620903 := bstep (se 1 (by rfl) ⟨465677, by rfl⟩ : syracuseStep 620903 = 931355) B931355
theorem B260479 : Blo 239816 260479 := bstep (se 1 (by rfl) ⟨195359, by rfl⟩ : syracuseStep 260479 = 390719) B390719
theorem B360623 : Blo 239816 360623 := bstep (se 1 (by rfl) ⟨270467, by rfl⟩ : syracuseStep 360623 = 540935) B540935
theorem B620527837 : Blo 239816 620527837 := bstep (se 3 (by rfl) ⟨116348969, by rfl⟩ : syracuseStep 620527837 = 232697939) B232697939
theorem B459263 : Blo 239816 459263 := bstep (se 1 (by rfl) ⟨344447, by rfl⟩ : syracuseStep 459263 = 688895) B688895
theorem B361211 : Blo 239816 361211 := bstep (se 1 (by rfl) ⟨270908, by rfl⟩ : syracuseStep 361211 = 541817) B541817
theorem B1115005 : Blo 239816 1115005 := bstep (se 3 (by rfl) ⟨209063, by rfl⟩ : syracuseStep 1115005 = 418127) B418127
theorem B820691 : Blo 239816 820691 := bstep (se 1 (by rfl) ⟨615518, by rfl⟩ : syracuseStep 820691 = 1231037) B1231037
theorem B493103 : Blo 239816 493103 := bstep (se 1 (by rfl) ⟨369827, by rfl⟩ : syracuseStep 493103 = 739655) B739655
theorem B1836593 : Blo 239816 1836593 := bstep (se 2 (by rfl) ⟨688722, by rfl⟩ : syracuseStep 1836593 = 1377445) B1377445
theorem B1181243 : Blo 239816 1181243 := bstep (se 1 (by rfl) ⟨885932, by rfl⟩ : syracuseStep 1181243 = 1771865) B1771865
theorem B362153 : Blo 239816 362153 := bstep (se 2 (by rfl) ⟨135807, by rfl⟩ : syracuseStep 362153 = 271615) B271615
theorem B1967993 : Blo 239816 1967993 := bstep (se 2 (by rfl) ⟨737997, by rfl⟩ : syracuseStep 1967993 = 1475995) B1475995
theorem B362363 : Blo 239816 362363 := bstep (se 1 (by rfl) ⟨271772, by rfl⟩ : syracuseStep 362363 = 543545) B543545
theorem B919421 : Blo 239816 919421 := bstep (se 3 (by rfl) ⟨172391, by rfl⟩ : syracuseStep 919421 = 344783) B344783
theorem B362543 : Blo 239816 362543 := bstep (se 1 (by rfl) ⟨271907, by rfl⟩ : syracuseStep 362543 = 543815) B543815
theorem B821447 : Blo 239816 821447 := bstep (se 1 (by rfl) ⟨616085, by rfl⟩ : syracuseStep 821447 = 1232171) B1232171
theorem B362807 : Blo 239816 362807 := bstep (se 1 (by rfl) ⟨272105, by rfl⟩ : syracuseStep 362807 = 544211) B544211
theorem B821663 : Blo 239816 821663 := bstep (se 1 (by rfl) ⟨616247, by rfl⟩ : syracuseStep 821663 = 1232495) B1232495
theorem B4164047 : Blo 239816 4164047 := bstep (se 1 (by rfl) ⟨3123035, by rfl⟩ : syracuseStep 4164047 = 6246071) B6246071
theorem B1444711 : Blo 239816 1444711 := bstep (se 1 (by rfl) ⟨1083533, by rfl⟩ : syracuseStep 1444711 = 2167067) B2167067
theorem B461791 : Blo 239816 461791 := bstep (se 1 (by rfl) ⟨346343, by rfl⟩ : syracuseStep 461791 = 692687) B692687
theorem B1215485 : Blo 239816 1215485 := bstep (se 3 (by rfl) ⟨227903, by rfl⟩ : syracuseStep 1215485 = 455807) B455807
theorem B363935 : Blo 239816 363935 := bstep (se 1 (by rfl) ⟨272951, by rfl⟩ : syracuseStep 363935 = 545903) B545903
theorem B364319 : Blo 239816 364319 := bstep (se 1 (by rfl) ⟨273239, by rfl⟩ : syracuseStep 364319 = 546479) B546479
theorem B1216619 : Blo 239816 1216619 := bstep (se 1 (by rfl) ⟨912464, by rfl⟩ : syracuseStep 1216619 = 1824929) B1824929
theorem B364655 : Blo 239816 364655 := bstep (se 1 (by rfl) ⟨273491, by rfl⟩ : syracuseStep 364655 = 546983) B546983
theorem B364703 : Blo 239816 364703 := bstep (se 1 (by rfl) ⟨273527, by rfl⟩ : syracuseStep 364703 = 547055) B547055
theorem B364727 : Blo 239816 364727 := bstep (se 1 (by rfl) ⟨273545, by rfl⟩ : syracuseStep 364727 = 547091) B547091
theorem B364799 : Blo 239816 364799 := bstep (se 1 (by rfl) ⟨273599, by rfl⟩ : syracuseStep 364799 = 547199) B547199
theorem B922337 : Blo 239816 922337 := bstep (se 2 (by rfl) ⟨345876, by rfl⟩ : syracuseStep 922337 = 691753) B691753
theorem B1381319 : Blo 239816 1381319 := bstep (se 1 (by rfl) ⟨1035989, by rfl⟩ : syracuseStep 1381319 = 2071979) B2071979
theorem B3085721 : Blo 239816 3085721 := bstep (se 2 (by rfl) ⟨1157145, by rfl⟩ : syracuseStep 3085721 = 2314291) B2314291
theorem B924007 : Blo 239816 924007 := bstep (se 1 (by rfl) ⟨693005, by rfl⟩ : syracuseStep 924007 = 1386011) B1386011
theorem B2857625 : Blo 239816 2857625 := bstep (se 2 (by rfl) ⟨1071609, by rfl⟩ : syracuseStep 2857625 = 2143219) B2143219
theorem B434479 : Blo 239816 434479 := bstep (se 1 (by rfl) ⟨325859, by rfl⟩ : syracuseStep 434479 = 651719) B651719
theorem B270823 : Blo 239816 270823 := bstep (se 1 (by rfl) ⟨203117, by rfl⟩ : syracuseStep 270823 = 406235) B406235
theorem B434983 : Blo 239816 434983 := bstep (se 1 (by rfl) ⟨326237, by rfl⟩ : syracuseStep 434983 = 652475) B652475
theorem B4532203 : Blo 239816 4532203 := bstep (se 1 (by rfl) ⟨3399152, by rfl⟩ : syracuseStep 4532203 = 6798305) B6798305
theorem B273055 : Blo 239816 273055 := bstep (se 1 (by rfl) ⟨204791, by rfl⟩ : syracuseStep 273055 = 409583) B409583
theorem B240335 : Blo 239816 240335 := bstep (se 1 (by rfl) ⟨180251, by rfl⟩ : syracuseStep 240335 = 360503) B360503
theorem B240359 : Blo 239816 240359 := bstep (se 1 (by rfl) ⟨180269, by rfl⟩ : syracuseStep 240359 = 360539) B360539
theorem B240671 : Blo 239816 240671 := bstep (se 1 (by rfl) ⟨180503, by rfl⟩ : syracuseStep 240671 = 361007) B361007
theorem B404777 : Blo 239816 404777 := bstep (se 2 (by rfl) ⟨151791, by rfl⟩ : syracuseStep 404777 = 303583) B303583
theorem B241499 : Blo 239816 241499 := bstep (se 1 (by rfl) ⟨181124, by rfl⟩ : syracuseStep 241499 = 362249) B362249
theorem B6238183 : Blo 239816 6238183 := bstep (se 1 (by rfl) ⟨4678637, by rfl⟩ : syracuseStep 6238183 = 9357275) B9357275
theorem B405479 : Blo 239816 405479 := bstep (se 1 (by rfl) ⟨304109, by rfl⟩ : syracuseStep 405479 = 608219) B608219
theorem B7843949 : Blo 239816 7843949 := bstep (se 3 (by rfl) ⟨1470740, by rfl⟩ : syracuseStep 7843949 = 2941481) B2941481
theorem B405641 : Blo 239816 405641 := bstep (se 2 (by rfl) ⟨152115, by rfl⟩ : syracuseStep 405641 = 304231) B304231
theorem B405695 : Blo 239816 405695 := bstep (se 1 (by rfl) ⟨304271, by rfl⟩ : syracuseStep 405695 = 608543) B608543
theorem B406127 : Blo 239816 406127 := bstep (se 1 (by rfl) ⟨304595, by rfl⟩ : syracuseStep 406127 = 609191) B609191
theorem B1389221 : Blo 239816 1389221 := bstep (se 4 (by rfl) ⟨130239, by rfl⟩ : syracuseStep 1389221 = 260479) B260479
theorem B1225529 : Blo 239816 1225529 := bstep (se 2 (by rfl) ⟨459573, by rfl⟩ : syracuseStep 1225529 = 919147) B919147
theorem B14922791 : Blo 239816 14922791 := bstep (se 1 (by rfl) ⟨11192093, by rfl⟩ : syracuseStep 14922791 = 22384187) B22384187
theorem B3028291 : Blo 239816 3028291 := bstep (se 1 (by rfl) ⟨2271218, by rfl⟩ : syracuseStep 3028291 = 4542437) B4542437
theorem B243431 : Blo 239816 243431 := bstep (se 1 (by rfl) ⟨182573, by rfl⟩ : syracuseStep 243431 = 365147) B365147
theorem B243567 : Blo 239816 243567 := bstep (se 1 (by rfl) ⟨182675, by rfl⟩ : syracuseStep 243567 = 365351) B365351
theorem B243583 : Blo 239816 243583 := bstep (se 1 (by rfl) ⟨182687, by rfl⟩ : syracuseStep 243583 = 365375) B365375
theorem B243679 : Blo 239816 243679 := bstep (se 1 (by rfl) ⟨182759, by rfl⟩ : syracuseStep 243679 = 365519) B365519
theorem B1161647 : Blo 239816 1161647 := bstep (se 1 (by rfl) ⟨871235, by rfl⟩ : syracuseStep 1161647 = 1742471) B1742471
theorem B1555163 : Blo 239816 1555163 := bstep (se 1 (by rfl) ⟨1166372, by rfl⟩ : syracuseStep 1555163 = 2332745) B2332745
theorem B539675 : Blo 239816 539675 := bstep (se 1 (by rfl) ⟨404756, by rfl⟩ : syracuseStep 539675 = 809513) B809513
theorem B6569201 : Blo 239816 6569201 := bstep (se 2 (by rfl) ⟨2463450, by rfl⟩ : syracuseStep 6569201 = 4926901) B4926901
theorem B60833045 : Blo 239816 60833045 := bstep (se 6 (by rfl) ⟨1425774, by rfl⟩ : syracuseStep 60833045 = 2851549) B2851549
theorem B1655741 : Blo 239816 1655741 := bstep (se 3 (by rfl) ⟨310451, by rfl⟩ : syracuseStep 1655741 = 620903) B620903
theorem B410575 : Blo 239816 410575 := bstep (se 1 (by rfl) ⟨307931, by rfl⟩ : syracuseStep 410575 = 615863) B615863
theorem B410879 : Blo 239816 410879 := bstep (se 1 (by rfl) ⟨308159, by rfl⟩ : syracuseStep 410879 = 616319) B616319
theorem B411115 : Blo 239816 411115 := bstep (se 1 (by rfl) ⟨308336, by rfl⟩ : syracuseStep 411115 = 616673) B616673
theorem B869879 : Blo 239816 869879 := bstep (se 1 (by rfl) ⟨652409, by rfl⟩ : syracuseStep 869879 = 1304819) B1304819
theorem B771727 : Blo 239816 771727 := bstep (se 1 (by rfl) ⟨578795, by rfl⟩ : syracuseStep 771727 = 1157591) B1157591
theorem B543995 : Blo 239816 543995 := bstep (se 1 (by rfl) ⟨407996, by rfl⟩ : syracuseStep 543995 = 815993) B815993
theorem B1166719 : Blo 239816 1166719 := bstep (se 1 (by rfl) ⟨875039, by rfl⟩ : syracuseStep 1166719 = 1750079) B1750079
theorem B610031 : Blo 239816 610031 := bstep (se 1 (by rfl) ⟨457523, by rfl⟩ : syracuseStep 610031 = 915047) B915047
theorem B1560647 : Blo 239816 1560647 := bstep (se 1 (by rfl) ⟨1170485, by rfl⟩ : syracuseStep 1560647 = 2340971) B2340971
theorem B544895 : Blo 239816 544895 := bstep (se 1 (by rfl) ⟨408671, by rfl⟩ : syracuseStep 544895 = 817343) B817343
theorem B1037033 : Blo 239816 1037033 := bstep (se 2 (by rfl) ⟨388887, by rfl⟩ : syracuseStep 1037033 = 777775) B777775
theorem B1660283 : Blo 239816 1660283 := bstep (se 1 (by rfl) ⟨1245212, by rfl⟩ : syracuseStep 1660283 = 2490425) B2490425
theorem B546299 : Blo 239816 546299 := bstep (se 1 (by rfl) ⟨409724, by rfl⟩ : syracuseStep 546299 = 819449) B819449
theorem B1955411 : Blo 239816 1955411 := bstep (se 1 (by rfl) ⟨1466558, by rfl⟩ : syracuseStep 1955411 = 2933117) B2933117
theorem B546407 : Blo 239816 546407 := bstep (se 1 (by rfl) ⟨409805, by rfl⟩ : syracuseStep 546407 = 819611) B819611
theorem B776135 : Blo 239816 776135 := bstep (se 1 (by rfl) ⟨582101, by rfl⟩ : syracuseStep 776135 = 1164203) B1164203
theorem B5232761 : Blo 239816 5232761 := bstep (se 2 (by rfl) ⟨1962285, by rfl⟩ : syracuseStep 5232761 = 3924571) B3924571
theorem B3529207 : Blo 239816 3529207 := bstep (se 1 (by rfl) ⟨2646905, by rfl⟩ : syracuseStep 3529207 = 5293811) B5293811
theorem B810215 : Blo 239816 810215 := bstep (se 1 (by rfl) ⟨607661, by rfl⟩ : syracuseStep 810215 = 1215323) B1215323
theorem B613615 : Blo 239816 613615 := bstep (se 1 (by rfl) ⟨460211, by rfl⟩ : syracuseStep 613615 = 920423) B920423
theorem B5856695 : Blo 239816 5856695 := bstep (se 1 (by rfl) ⟨4392521, by rfl⟩ : syracuseStep 5856695 = 8785043) B8785043
theorem B1662443 : Blo 239816 1662443 := bstep (se 1 (by rfl) ⟨1246832, by rfl⟩ : syracuseStep 1662443 = 2493665) B2493665
theorem B548423 : Blo 239816 548423 := bstep (se 1 (by rfl) ⟨411317, by rfl⟩ : syracuseStep 548423 = 822635) B822635
theorem B7004231 : Blo 239816 7004231 := bstep (se 1 (by rfl) ⟨5253173, by rfl⟩ : syracuseStep 7004231 = 10506347) B10506347
theorem B12509623 : Blo 239816 12509623 := bstep (se 1 (by rfl) ⟨9382217, by rfl⟩ : syracuseStep 12509623 = 18764435) B18764435
theorem B1368515 : Blo 239816 1368515 := bstep (se 1 (by rfl) ⟨1026386, by rfl⟩ : syracuseStep 1368515 = 2052773) B2052773
theorem B549359 : Blo 239816 549359 := bstep (se 1 (by rfl) ⟨412019, by rfl⟩ : syracuseStep 549359 = 824039) B824039
theorem B2188093 : Blo 239816 2188093 := bstep (se 3 (by rfl) ⟨410267, by rfl⟩ : syracuseStep 2188093 = 820535) B820535
theorem B943721 : Blo 239816 943721 := bstep (se 2 (by rfl) ⟨353895, by rfl⟩ : syracuseStep 943721 = 707791) B707791
theorem B1468115 : Blo 239816 1468115 := bstep (se 1 (by rfl) ⟨1101086, by rfl⟩ : syracuseStep 1468115 = 2202173) B2202173
theorem B813023 : Blo 239816 813023 := bstep (se 1 (by rfl) ⟨609767, by rfl⟩ : syracuseStep 813023 = 1219535) B1219535
theorem B583841 : Blo 239816 583841 := bstep (se 2 (by rfl) ⟨218940, by rfl⟩ : syracuseStep 583841 = 437881) B437881
theorem B14838065 : Blo 239816 14838065 := bstep (se 2 (by rfl) ⟨5564274, by rfl⟩ : syracuseStep 14838065 = 11128549) B11128549
theorem B616939 : Blo 239816 616939 := bstep (se 1 (by rfl) ⟨462704, by rfl⟩ : syracuseStep 616939 = 925409) B925409
theorem B813671 : Blo 239816 813671 := bstep (se 1 (by rfl) ⟨610253, by rfl⟩ : syracuseStep 813671 = 1220507) B1220507
theorem B814049 : Blo 239816 814049 := bstep (se 2 (by rfl) ⟨305268, by rfl⟩ : syracuseStep 814049 = 610537) B610537
theorem B814265 : Blo 239816 814265 := bstep (se 2 (by rfl) ⟨305349, by rfl⟩ : syracuseStep 814265 = 610699) B610699
theorem B913103 : Blo 239816 913103 := bstep (se 1 (by rfl) ⟨684827, by rfl⟩ : syracuseStep 913103 = 1369655) B1369655
theorem B815399 : Blo 239816 815399 := bstep (se 1 (by rfl) ⟨611549, by rfl⟩ : syracuseStep 815399 = 1223099) B1223099
theorem B815615 : Blo 239816 815615 := bstep (se 1 (by rfl) ⟨611711, by rfl⟩ : syracuseStep 815615 = 1223423) B1223423
theorem B5272127 : Blo 239816 5272127 := bstep (se 1 (by rfl) ⟨3954095, by rfl⟩ : syracuseStep 5272127 = 7908191) B7908191
theorem B914273 : Blo 239816 914273 := bstep (se 2 (by rfl) ⟨342852, by rfl⟩ : syracuseStep 914273 = 685705) B685705
theorem B390457 : Blo 239816 390457 := bstep (se 2 (by rfl) ⟨146421, by rfl⟩ : syracuseStep 390457 = 292843) B292843
theorem B259399 : Blo 239816 259399 := bstep (se 1 (by rfl) ⟨194549, by rfl⟩ : syracuseStep 259399 = 389099) B389099
theorem B718715 : Blo 239816 718715 := bstep (se 1 (by rfl) ⟨539036, by rfl⟩ : syracuseStep 718715 = 1078073) B1078073
theorem B456673 : Blo 239816 456673 := bstep (se 2 (by rfl) ⟨171252, by rfl⟩ : syracuseStep 456673 = 342505) B342505
theorem B522343 : Blo 239816 522343 := bstep (se 1 (by rfl) ⟨391757, by rfl⟩ : syracuseStep 522343 = 783515) B783515
theorem B1833191 : Blo 239816 1833191 := bstep (se 1 (by rfl) ⟨1374893, by rfl⟩ : syracuseStep 1833191 = 2749787) B2749787
theorem B915731 : Blo 239816 915731 := bstep (se 1 (by rfl) ⟨686798, by rfl⟩ : syracuseStep 915731 = 1373597) B1373597
theorem B817505 : Blo 239816 817505 := bstep (se 2 (by rfl) ⟨306564, by rfl⟩ : syracuseStep 817505 = 613129) B613129
theorem B916231 : Blo 239816 916231 := bstep (se 1 (by rfl) ⟨687173, by rfl⟩ : syracuseStep 916231 = 1374347) B1374347
theorem B817991 : Blo 239816 817991 := bstep (se 1 (by rfl) ⟨613493, by rfl⟩ : syracuseStep 817991 = 1226987) B1226987
theorem B818207 : Blo 239816 818207 := bstep (se 1 (by rfl) ⟨613655, by rfl⟩ : syracuseStep 818207 = 1227311) B1227311
theorem B359807 : Blo 239816 359807 := bstep (se 1 (by rfl) ⟨269855, by rfl⟩ : syracuseStep 359807 = 539711) B539711
theorem B1736615 : Blo 239816 1736615 := bstep (se 1 (by rfl) ⟨1302461, by rfl⟩ : syracuseStep 1736615 = 2604923) B2604923
theorem B4161725 : Blo 239816 4161725 := bstep (se 3 (by rfl) ⟨780323, by rfl⟩ : syracuseStep 4161725 = 1560647) B1560647
theorem B361097 : Blo 239816 361097 := bstep (se 2 (by rfl) ⟨135411, by rfl⟩ : syracuseStep 361097 = 270823) B270823
theorem B328735 : Blo 239816 328735 := bstep (se 1 (by rfl) ⟨246551, by rfl⟩ : syracuseStep 328735 = 493103) B493103
theorem B787495 : Blo 239816 787495 := bstep (se 1 (by rfl) ⟨590621, by rfl⟩ : syracuseStep 787495 = 1181243) B1181243
theorem B2917457 : Blo 239816 2917457 := bstep (se 2 (by rfl) ⟨1094046, by rfl⟩ : syracuseStep 2917457 = 2188093) B2188093
theorem B1311995 : Blo 239816 1311995 := bstep (se 1 (by rfl) ⟨983996, by rfl⟩ : syracuseStep 1311995 = 1967993) B1967993
theorem B362663 : Blo 239816 362663 := bstep (se 1 (by rfl) ⟨271997, by rfl⟩ : syracuseStep 362663 = 543995) B543995
theorem B66717989 : Blo 239816 66717989 := bstep (se 4 (by rfl) ⟨6254811, by rfl⟩ : syracuseStep 66717989 = 12509623) B12509623
theorem B363263 : Blo 239816 363263 := bstep (se 1 (by rfl) ⟨272447, by rfl⟩ : syracuseStep 363263 = 544895) B544895
theorem B691355 : Blo 239816 691355 := bstep (se 1 (by rfl) ⟨518516, by rfl⟩ : syracuseStep 691355 = 1037033) B1037033
theorem B920879 : Blo 239816 920879 := bstep (se 1 (by rfl) ⟨690659, by rfl⟩ : syracuseStep 920879 = 1381319) B1381319
theorem B364073 : Blo 239816 364073 := bstep (se 2 (by rfl) ⟨136527, by rfl⟩ : syracuseStep 364073 = 273055) B273055
theorem B364199 : Blo 239816 364199 := bstep (se 1 (by rfl) ⟨273149, by rfl⟩ : syracuseStep 364199 = 546299) B546299
theorem B364271 : Blo 239816 364271 := bstep (se 1 (by rfl) ⟨273203, by rfl⟩ : syracuseStep 364271 = 546407) B546407
theorem B1905083 : Blo 239816 1905083 := bstep (se 1 (by rfl) ⟨1428812, by rfl⟩ : syracuseStep 1905083 = 2857625) B2857625
theorem B3904463 : Blo 239816 3904463 := bstep (se 1 (by rfl) ⟨2928347, by rfl⟩ : syracuseStep 3904463 = 5856695) B5856695
theorem B365615 : Blo 239816 365615 := bstep (se 1 (by rfl) ⟨274211, by rfl⟩ : syracuseStep 365615 = 548423) B548423
theorem B366239 : Blo 239816 366239 := bstep (se 1 (by rfl) ⟨274679, by rfl⟩ : syracuseStep 366239 = 549359) B549359
theorem B629147 : Blo 239816 629147 := bstep (se 1 (by rfl) ⟨471860, by rfl⟩ : syracuseStep 629147 = 943721) B943721
theorem B269851 : Blo 239816 269851 := bstep (se 1 (by rfl) ⟨202388, by rfl⟩ : syracuseStep 269851 = 404777) B404777
theorem B270319 : Blo 239816 270319 := bstep (se 1 (by rfl) ⟨202739, by rfl⟩ : syracuseStep 270319 = 405479) B405479
theorem B270427 : Blo 239816 270427 := bstep (se 1 (by rfl) ⟨202820, by rfl⟩ : syracuseStep 270427 = 405641) B405641
theorem B270463 : Blo 239816 270463 := bstep (se 1 (by rfl) ⟨202847, by rfl⟩ : syracuseStep 270463 = 405695) B405695
theorem B696457 : Blo 239816 696457 := bstep (se 2 (by rfl) ⟨261171, by rfl⟩ : syracuseStep 696457 = 522343) B522343
theorem B3514751 : Blo 239816 3514751 := bstep (se 1 (by rfl) ⟨2636063, by rfl⟩ : syracuseStep 3514751 = 5272127) B5272127
theorem B270751 : Blo 239816 270751 := bstep (se 1 (by rfl) ⟨203063, by rfl⟩ : syracuseStep 270751 = 406127) B406127
theorem B926147 : Blo 239816 926147 := bstep (se 1 (by rfl) ⟨694610, by rfl⟩ : syracuseStep 926147 = 1389221) B1389221
theorem B1221641 : Blo 239816 1221641 := bstep (se 2 (by rfl) ⟨458115, by rfl⟩ : syracuseStep 1221641 = 916231) B916231
theorem B1222127 : Blo 239816 1222127 := bstep (se 1 (by rfl) ⟨916595, by rfl⟩ : syracuseStep 1222127 = 1833191) B1833191
theorem B239871 : Blo 239816 239871 := bstep (se 1 (by rfl) ⟨179903, by rfl⟩ : syracuseStep 239871 = 359807) B359807
theorem B1157743 : Blo 239816 1157743 := bstep (se 1 (by rfl) ⟨868307, by rfl⟩ : syracuseStep 1157743 = 1736615) B1736615
theorem B240415 : Blo 239816 240415 := bstep (se 1 (by rfl) ⟨180311, by rfl⟩ : syracuseStep 240415 = 360623) B360623
theorem B827370449 : Blo 239816 827370449 := bstep (se 2 (by rfl) ⟨310263918, by rfl⟩ : syracuseStep 827370449 = 620527837) B620527837
theorem B306175 : Blo 239816 306175 := bstep (se 1 (by rfl) ⟨229631, by rfl⟩ : syracuseStep 306175 = 459263) B459263
theorem B240807 : Blo 239816 240807 := bstep (se 1 (by rfl) ⟨180605, by rfl⟩ : syracuseStep 240807 = 361211) B361211
theorem B273919 : Blo 239816 273919 := bstep (se 1 (by rfl) ⟨205439, by rfl⟩ : syracuseStep 273919 = 410879) B410879
theorem B1224395 : Blo 239816 1224395 := bstep (se 1 (by rfl) ⟨918296, by rfl⟩ : syracuseStep 1224395 = 1836593) B1836593
theorem B241435 : Blo 239816 241435 := bstep (se 1 (by rfl) ⟨181076, by rfl⟩ : syracuseStep 241435 = 362153) B362153
theorem B1486673 : Blo 239816 1486673 := bstep (se 2 (by rfl) ⟨557502, by rfl⟩ : syracuseStep 1486673 = 1115005) B1115005
theorem B241575 : Blo 239816 241575 := bstep (se 1 (by rfl) ⟨181181, by rfl⟩ : syracuseStep 241575 = 362363) B362363
theorem B241695 : Blo 239816 241695 := bstep (se 1 (by rfl) ⟨181271, by rfl⟩ : syracuseStep 241695 = 362543) B362543
theorem B241871 : Blo 239816 241871 := bstep (se 1 (by rfl) ⟨181403, by rfl⟩ : syracuseStep 241871 = 362807) B362807
theorem B1028969 : Blo 239816 1028969 := bstep (se 2 (by rfl) ⟨385863, by rfl⟩ : syracuseStep 1028969 = 771727) B771727
theorem B242623 : Blo 239816 242623 := bstep (se 1 (by rfl) ⟨181967, by rfl⟩ : syracuseStep 242623 = 363935) B363935
theorem B406687 : Blo 239816 406687 := bstep (se 1 (by rfl) ⟨305015, by rfl⟩ : syracuseStep 406687 = 610031) B610031
theorem B242879 : Blo 239816 242879 := bstep (se 1 (by rfl) ⟨182159, by rfl⟩ : syracuseStep 242879 = 364319) B364319
theorem B6042937 : Blo 239816 6042937 := bstep (se 2 (by rfl) ⟨2266101, by rfl⟩ : syracuseStep 6042937 = 4532203) B4532203
theorem B243103 : Blo 239816 243103 := bstep (se 1 (by rfl) ⟨182327, by rfl⟩ : syracuseStep 243103 = 364655) B364655
theorem B243135 : Blo 239816 243135 := bstep (se 1 (by rfl) ⟨182351, by rfl⟩ : syracuseStep 243135 = 364703) B364703
theorem B243151 : Blo 239816 243151 := bstep (se 1 (by rfl) ⟨182363, by rfl⟩ : syracuseStep 243151 = 364727) B364727
theorem B243199 : Blo 239816 243199 := bstep (se 1 (by rfl) ⟨182399, by rfl⟩ : syracuseStep 243199 = 364799) B364799
theorem B3488507 : Blo 239816 3488507 := bstep (se 1 (by rfl) ⟨2616380, by rfl⟩ : syracuseStep 3488507 = 5232761) B5232761
theorem B1555625 : Blo 239816 1555625 := bstep (se 2 (by rfl) ⟨583359, by rfl⟩ : syracuseStep 1555625 = 1166719) B1166719
theorem B540143 : Blo 239816 540143 := bstep (se 1 (by rfl) ⟨405107, by rfl⟩ : syracuseStep 540143 = 810215) B810215
theorem B4669487 : Blo 239816 4669487 := bstep (se 1 (by rfl) ⟨3502115, by rfl⟩ : syracuseStep 4669487 = 7004231) B7004231
theorem B542015 : Blo 239816 542015 := bstep (se 1 (by rfl) ⟨406511, by rfl⟩ : syracuseStep 542015 = 813023) B813023
theorem B64603541 : Blo 239816 64603541 := bstep (se 6 (by rfl) ⟨1514145, by rfl⟩ : syracuseStep 64603541 = 3028291) B3028291
theorem B542447 : Blo 239816 542447 := bstep (se 1 (by rfl) ⟨406835, by rfl⟩ : syracuseStep 542447 = 813671) B813671
theorem B345865 : Blo 239816 345865 := bstep (se 2 (by rfl) ⟨129699, by rfl⟩ : syracuseStep 345865 = 259399) B259399
theorem B542699 : Blo 239816 542699 := bstep (se 1 (by rfl) ⟨407024, by rfl⟩ : syracuseStep 542699 = 814049) B814049
theorem B542843 : Blo 239816 542843 := bstep (se 1 (by rfl) ⟨407132, by rfl⟩ : syracuseStep 542843 = 814265) B814265
theorem B608735 : Blo 239816 608735 := bstep (se 1 (by rfl) ⟨456551, by rfl⟩ : syracuseStep 608735 = 913103) B913103
theorem B608897 : Blo 239816 608897 := bstep (se 2 (by rfl) ⟨228336, by rfl⟩ : syracuseStep 608897 = 456673) B456673
theorem B5229299 : Blo 239816 5229299 := bstep (se 1 (by rfl) ⟨3921974, by rfl⟩ : syracuseStep 5229299 = 7843949) B7843949
theorem B543599 : Blo 239816 543599 := bstep (se 1 (by rfl) ⟨407699, by rfl⟩ : syracuseStep 543599 = 815399) B815399
theorem B543743 : Blo 239816 543743 := bstep (se 1 (by rfl) ⟨407807, by rfl⟩ : syracuseStep 543743 = 815615) B815615
theorem B1232009 : Blo 239816 1232009 := bstep (se 2 (by rfl) ⟨462003, by rfl⟩ : syracuseStep 1232009 = 924007) B924007
theorem B609515 : Blo 239816 609515 := bstep (se 1 (by rfl) ⟨457136, by rfl⟩ : syracuseStep 609515 = 914273) B914273
theorem B4705609 : Blo 239816 4705609 := bstep (se 2 (by rfl) ⟨1764603, by rfl⟩ : syracuseStep 4705609 = 3529207) B3529207
theorem B9948527 : Blo 239816 9948527 := bstep (se 1 (by rfl) ⟨7461395, by rfl⟩ : syracuseStep 9948527 = 14922791) B14922791
theorem B479143 : Blo 239816 479143 := bstep (se 1 (by rfl) ⟨359357, by rfl⟩ : syracuseStep 479143 = 718715) B718715
theorem B610487 : Blo 239816 610487 := bstep (se 1 (by rfl) ⟨457865, by rfl⟩ : syracuseStep 610487 = 915731) B915731
theorem B545003 : Blo 239816 545003 := bstep (se 1 (by rfl) ⟨408752, by rfl⟩ : syracuseStep 545003 = 817505) B817505
theorem B774431 : Blo 239816 774431 := bstep (se 1 (by rfl) ⟨580823, by rfl⟩ : syracuseStep 774431 = 1161647) B1161647
theorem B1036775 : Blo 239816 1036775 := bstep (se 1 (by rfl) ⟨777581, by rfl⟩ : syracuseStep 1036775 = 1555163) B1555163
theorem B545327 : Blo 239816 545327 := bstep (se 1 (by rfl) ⟨408995, by rfl⟩ : syracuseStep 545327 = 817991) B817991
theorem B545471 : Blo 239816 545471 := bstep (se 1 (by rfl) ⟨409103, by rfl⟩ : syracuseStep 545471 = 818207) B818207
theorem B4379467 : Blo 239816 4379467 := bstep (se 1 (by rfl) ⟨3284600, by rfl⟩ : syracuseStep 4379467 = 6569201) B6569201
theorem B40555363 : Blo 239816 40555363 := bstep (se 1 (by rfl) ⟨30416522, by rfl⟩ : syracuseStep 40555363 = 60833045) B60833045
theorem B13161365 : Blo 239816 13161365 := bstep (se 6 (by rfl) ⟨308469, by rfl⟩ : syracuseStep 13161365 = 616939) B616939
theorem B579305 : Blo 239816 579305 := bstep (se 2 (by rfl) ⟨217239, by rfl⟩ : syracuseStep 579305 = 434479) B434479
theorem B1103827 : Blo 239816 1103827 := bstep (se 1 (by rfl) ⟨827870, by rfl⟩ : syracuseStep 1103827 = 1655741) B1655741
theorem B547127 : Blo 239816 547127 := bstep (se 1 (by rfl) ⟨410345, by rfl⟩ : syracuseStep 547127 = 820691) B820691
theorem B579977 : Blo 239816 579977 := bstep (se 2 (by rfl) ⟨217491, by rfl⟩ : syracuseStep 579977 = 434983) B434983
theorem B612947 : Blo 239816 612947 := bstep (se 1 (by rfl) ⟨459710, by rfl⟩ : syracuseStep 612947 = 919421) B919421
theorem B547433 : Blo 239816 547433 := bstep (se 2 (by rfl) ⟨205287, by rfl⟩ : syracuseStep 547433 = 410575) B410575
theorem B547631 : Blo 239816 547631 := bstep (se 1 (by rfl) ⟨410723, by rfl⟩ : syracuseStep 547631 = 821447) B821447
theorem B547775 : Blo 239816 547775 := bstep (se 1 (by rfl) ⟨410831, by rfl⟩ : syracuseStep 547775 = 821663) B821663
theorem B2776031 : Blo 239816 2776031 := bstep (se 1 (by rfl) ⟨2082023, by rfl⟩ : syracuseStep 2776031 = 4164047) B4164047
theorem B548153 : Blo 239816 548153 := bstep (se 2 (by rfl) ⟨205557, by rfl⟩ : syracuseStep 548153 = 411115) B411115
theorem B810323 : Blo 239816 810323 := bstep (se 1 (by rfl) ⟨607742, by rfl⟩ : syracuseStep 810323 = 1215485) B1215485
theorem B811079 : Blo 239816 811079 := bstep (se 1 (by rfl) ⟨608309, by rfl⟩ : syracuseStep 811079 = 1216619) B1216619
theorem B614891 : Blo 239816 614891 := bstep (se 1 (by rfl) ⟨461168, by rfl⟩ : syracuseStep 614891 = 922337) B922337
theorem B1106855 : Blo 239816 1106855 := bstep (se 1 (by rfl) ⟨830141, by rfl⟩ : syracuseStep 1106855 = 1660283) B1660283
theorem B2057147 : Blo 239816 2057147 := bstep (se 1 (by rfl) ⟨1542860, by rfl⟩ : syracuseStep 2057147 = 3085721) B3085721
theorem B1303607 : Blo 239816 1303607 := bstep (se 1 (by rfl) ⟨977705, by rfl⟩ : syracuseStep 1303607 = 1955411) B1955411
theorem B1926281 : Blo 239816 1926281 := bstep (se 2 (by rfl) ⟨722355, by rfl⟩ : syracuseStep 1926281 = 1444711) B1444711
theorem B615721 : Blo 239816 615721 := bstep (se 2 (by rfl) ⟨230895, by rfl⟩ : syracuseStep 615721 = 461791) B461791
theorem B517423 : Blo 239816 517423 := bstep (se 1 (by rfl) ⟨388067, by rfl⟩ : syracuseStep 517423 = 776135) B776135
theorem B2319677 : Blo 239816 2319677 := bstep (se 3 (by rfl) ⟨434939, by rfl⟩ : syracuseStep 2319677 = 869879) B869879
theorem B1108295 : Blo 239816 1108295 := bstep (se 1 (by rfl) ⟨831221, by rfl⟩ : syracuseStep 1108295 = 1662443) B1662443
theorem B8317577 : Blo 239816 8317577 := bstep (se 2 (by rfl) ⟨3119091, by rfl⟩ : syracuseStep 8317577 = 6238183) B6238183
theorem B912343 : Blo 239816 912343 := bstep (se 1 (by rfl) ⟨684257, by rfl⟩ : syracuseStep 912343 = 1368515) B1368515
theorem B978743 : Blo 239816 978743 := bstep (se 1 (by rfl) ⟨734057, by rfl⟩ : syracuseStep 978743 = 1468115) B1468115
theorem B389227 : Blo 239816 389227 := bstep (se 1 (by rfl) ⟨291920, by rfl⟩ : syracuseStep 389227 = 583841) B583841
theorem B9892043 : Blo 239816 9892043 := bstep (se 1 (by rfl) ⟨7419032, by rfl⟩ : syracuseStep 9892043 = 14838065) B14838065
theorem B520609 : Blo 239816 520609 := bstep (se 2 (by rfl) ⟨195228, by rfl⟩ : syracuseStep 520609 = 390457) B390457
theorem B817019 : Blo 239816 817019 := bstep (se 1 (by rfl) ⟨612764, by rfl⟩ : syracuseStep 817019 = 1225529) B1225529
theorem B818153 : Blo 239816 818153 := bstep (se 2 (by rfl) ⟨306807, by rfl⟩ : syracuseStep 818153 = 613615) B613615
theorem B359783 : Blo 239816 359783 := bstep (se 1 (by rfl) ⟨269837, by rfl⟩ : syracuseStep 359783 = 539675) B539675
theorem B3112991 : Blo 239816 3112991 := bstep (se 1 (by rfl) ⟨2334743, by rfl⟩ : syracuseStep 3112991 = 4669487) B4669487
theorem B360569 : Blo 239816 360569 := bstep (se 2 (by rfl) ⟨135213, by rfl⟩ : syracuseStep 360569 = 270427) B270427
theorem B360617 : Blo 239816 360617 := bstep (se 2 (by rfl) ⟨135231, by rfl⟩ : syracuseStep 360617 = 270463) B270463
theorem B361001 : Blo 239816 361001 := bstep (se 2 (by rfl) ⟨135375, by rfl⟩ : syracuseStep 361001 = 270751) B270751
theorem B361343 : Blo 239816 361343 := bstep (se 1 (by rfl) ⟨271007, by rfl⟩ : syracuseStep 361343 = 542015) B542015
theorem B361631 : Blo 239816 361631 := bstep (se 1 (by rfl) ⟨271223, by rfl⟩ : syracuseStep 361631 = 542447) B542447
theorem B361799 : Blo 239816 361799 := bstep (se 1 (by rfl) ⟨271349, by rfl⟩ : syracuseStep 361799 = 542699) B542699
theorem B1049993 : Blo 239816 1049993 := bstep (se 2 (by rfl) ⟨393747, by rfl⟩ : syracuseStep 1049993 = 787495) B787495
theorem B361895 : Blo 239816 361895 := bstep (se 1 (by rfl) ⟨271421, by rfl⟩ : syracuseStep 361895 = 542843) B542843
theorem B820961 : Blo 239816 820961 := bstep (se 2 (by rfl) ⟨307860, by rfl⟩ : syracuseStep 820961 = 615721) B615721
theorem B689897 : Blo 239816 689897 := bstep (se 2 (by rfl) ⟨258711, by rfl⟩ : syracuseStep 689897 = 517423) B517423
theorem B362399 : Blo 239816 362399 := bstep (se 1 (by rfl) ⟨271799, by rfl⟩ : syracuseStep 362399 = 543599) B543599
theorem B362495 : Blo 239816 362495 := bstep (se 1 (by rfl) ⟨271871, by rfl⟩ : syracuseStep 362495 = 543743) B543743
theorem B821339 : Blo 239816 821339 := bstep (se 1 (by rfl) ⟨616004, by rfl⟩ : syracuseStep 821339 = 1232009) B1232009
theorem B460903 : Blo 239816 460903 := bstep (se 1 (by rfl) ⟨345677, by rfl⟩ : syracuseStep 460903 = 691355) B691355
theorem B461153 : Blo 239816 461153 := bstep (se 2 (by rfl) ⟨172932, by rfl⟩ : syracuseStep 461153 = 345865) B345865
theorem B363335 : Blo 239816 363335 := bstep (se 1 (by rfl) ⟨272501, by rfl⟩ : syracuseStep 363335 = 545003) B545003
theorem B691183 : Blo 239816 691183 := bstep (se 1 (by rfl) ⟨518387, by rfl⟩ : syracuseStep 691183 = 1036775) B1036775
theorem B363551 : Blo 239816 363551 := bstep (se 1 (by rfl) ⟨272663, by rfl⟩ : syracuseStep 363551 = 545327) B545327
theorem B363647 : Blo 239816 363647 := bstep (se 1 (by rfl) ⟨272735, by rfl⟩ : syracuseStep 363647 = 545471) B545471
theorem B1543657 : Blo 239816 1543657 := bstep (se 2 (by rfl) ⟨578871, by rfl⟩ : syracuseStep 1543657 = 1157743) B1157743
theorem B1216457 : Blo 239816 1216457 := bstep (se 2 (by rfl) ⟨456171, by rfl⟩ : syracuseStep 1216457 = 912343) B912343
theorem B364751 : Blo 239816 364751 := bstep (se 1 (by rfl) ⟨273563, by rfl⟩ : syracuseStep 364751 = 547127) B547127
theorem B364955 : Blo 239816 364955 := bstep (se 1 (by rfl) ⟨273716, by rfl⟩ : syracuseStep 364955 = 547433) B547433
theorem B365087 : Blo 239816 365087 := bstep (se 1 (by rfl) ⟨273815, by rfl⟩ : syracuseStep 365087 = 547631) B547631
theorem B365183 : Blo 239816 365183 := bstep (se 1 (by rfl) ⟨273887, by rfl⟩ : syracuseStep 365183 = 547775) B547775
theorem B365225 : Blo 239816 365225 := bstep (se 2 (by rfl) ⟨136959, by rfl⟩ : syracuseStep 365225 = 273919) B273919
theorem B365435 : Blo 239816 365435 := bstep (se 1 (by rfl) ⟨274076, by rfl⟩ : syracuseStep 365435 = 548153) B548153
theorem B694145 : Blo 239816 694145 := bstep (se 2 (by rfl) ⟨260304, by rfl⟩ : syracuseStep 694145 = 520609) B520609
theorem B1284187 : Blo 239816 1284187 := bstep (se 1 (by rfl) ⟨963140, by rfl⟩ : syracuseStep 1284187 = 1926281) B1926281
theorem B1546451 : Blo 239816 1546451 := bstep (se 1 (by rfl) ⟨1159838, by rfl⟩ : syracuseStep 1546451 = 2319677) B2319677
theorem B5839289 : Blo 239816 5839289 := bstep (se 2 (by rfl) ⟨2189733, by rfl⟩ : syracuseStep 5839289 = 4379467) B4379467
theorem B54073817 : Blo 239816 54073817 := bstep (se 2 (by rfl) ⟨20277681, by rfl⟩ : syracuseStep 54073817 = 40555363) B40555363
theorem B991115 : Blo 239816 991115 := bstep (se 1 (by rfl) ⟨743336, by rfl⟩ : syracuseStep 991115 = 1486673) B1486673
theorem B6594695 : Blo 239816 6594695 := bstep (se 1 (by rfl) ⟨4946021, by rfl⟩ : syracuseStep 6594695 = 9892043) B9892043
theorem B239855 : Blo 239816 239855 := bstep (se 1 (by rfl) ⟨179891, by rfl⟩ : syracuseStep 239855 = 359783) B359783
theorem B928609 : Blo 239816 928609 := bstep (se 2 (by rfl) ⟨348228, by rfl⟩ : syracuseStep 928609 = 696457) B696457
theorem B240731 : Blo 239816 240731 := bstep (se 1 (by rfl) ⟨180548, by rfl⟩ : syracuseStep 240731 = 361097) B361097
theorem B1944971 : Blo 239816 1944971 := bstep (se 1 (by rfl) ⟨1458728, by rfl⟩ : syracuseStep 1944971 = 2917457) B2917457
theorem B43069027 : Blo 239816 43069027 := bstep (se 1 (by rfl) ⟨32301770, by rfl⟩ : syracuseStep 43069027 = 64603541) B64603541
theorem B438313 : Blo 239816 438313 := bstep (se 2 (by rfl) ⟨164367, by rfl⟩ : syracuseStep 438313 = 328735) B328735
theorem B241775 : Blo 239816 241775 := bstep (se 1 (by rfl) ⟨181331, by rfl⟩ : syracuseStep 241775 = 362663) B362663
theorem B44478659 : Blo 239816 44478659 := bstep (se 1 (by rfl) ⟨33358994, by rfl⟩ : syracuseStep 44478659 = 66717989) B66717989
theorem B405823 : Blo 239816 405823 := bstep (se 1 (by rfl) ⟨304367, by rfl⟩ : syracuseStep 405823 = 608735) B608735
theorem B405931 : Blo 239816 405931 := bstep (se 1 (by rfl) ⟨304448, by rfl⟩ : syracuseStep 405931 = 608897) B608897
theorem B3486199 : Blo 239816 3486199 := bstep (se 1 (by rfl) ⟨2614649, by rfl⟩ : syracuseStep 3486199 = 5229299) B5229299
theorem B242175 : Blo 239816 242175 := bstep (se 1 (by rfl) ⟨181631, by rfl⟩ : syracuseStep 242175 = 363263) B363263
theorem B406343 : Blo 239816 406343 := bstep (se 1 (by rfl) ⟨304757, by rfl⟩ : syracuseStep 406343 = 609515) B609515
theorem B6632351 : Blo 239816 6632351 := bstep (se 1 (by rfl) ⟨4974263, by rfl⟩ : syracuseStep 6632351 = 9948527) B9948527
theorem B242715 : Blo 239816 242715 := bstep (se 1 (by rfl) ⟨182036, by rfl⟩ : syracuseStep 242715 = 364073) B364073
theorem B242799 : Blo 239816 242799 := bstep (se 1 (by rfl) ⟨182099, by rfl⟩ : syracuseStep 242799 = 364199) B364199
theorem B242847 : Blo 239816 242847 := bstep (se 1 (by rfl) ⟨182135, by rfl⟩ : syracuseStep 242847 = 364271) B364271
theorem B406991 : Blo 239816 406991 := bstep (se 1 (by rfl) ⟨305243, by rfl⟩ : syracuseStep 406991 = 610487) B610487
theorem B2602975 : Blo 239816 2602975 := bstep (se 1 (by rfl) ⟨1952231, by rfl⟩ : syracuseStep 2602975 = 3904463) B3904463
theorem B243743 : Blo 239816 243743 := bstep (se 1 (by rfl) ⟨182807, by rfl⟩ : syracuseStep 243743 = 365615) B365615
theorem B408233 : Blo 239816 408233 := bstep (se 2 (by rfl) ⟨153087, by rfl⟩ : syracuseStep 408233 = 306175) B306175
theorem B408631 : Blo 239816 408631 := bstep (se 1 (by rfl) ⟨306473, by rfl⟩ : syracuseStep 408631 = 612947) B612947
theorem B6274145 : Blo 239816 6274145 := bstep (se 2 (by rfl) ⟨2352804, by rfl⟩ : syracuseStep 6274145 = 4705609) B4705609
theorem B1850687 : Blo 239816 1850687 := bstep (se 1 (by rfl) ⟨1388015, by rfl⟩ : syracuseStep 1850687 = 2776031) B2776031
theorem B540215 : Blo 239816 540215 := bstep (se 1 (by rfl) ⟨405161, by rfl⟩ : syracuseStep 540215 = 810323) B810323
theorem B638857 : Blo 239816 638857 := bstep (se 2 (by rfl) ⟨239571, by rfl⟩ : syracuseStep 638857 = 479143) B479143
theorem B540719 : Blo 239816 540719 := bstep (se 1 (by rfl) ⟨405539, by rfl⟩ : syracuseStep 540719 = 811079) B811079
theorem B2343167 : Blo 239816 2343167 := bstep (se 1 (by rfl) ⟨1757375, by rfl⟩ : syracuseStep 2343167 = 3514751) B3514751
theorem B409927 : Blo 239816 409927 := bstep (se 1 (by rfl) ⟨307445, by rfl⟩ : syracuseStep 409927 = 614891) B614891
theorem B737903 : Blo 239816 737903 := bstep (se 1 (by rfl) ⟨553427, by rfl⟩ : syracuseStep 737903 = 1106855) B1106855
theorem B869071 : Blo 239816 869071 := bstep (se 1 (by rfl) ⟨651803, by rfl⟩ : syracuseStep 869071 = 1303607) B1303607
theorem B542249 : Blo 239816 542249 := bstep (se 2 (by rfl) ⟨203343, by rfl⟩ : syracuseStep 542249 = 406687) B406687
theorem B738863 : Blo 239816 738863 := bstep (se 1 (by rfl) ⟨554147, by rfl⟩ : syracuseStep 738863 = 1108295) B1108295
theorem B544679 : Blo 239816 544679 := bstep (se 1 (by rfl) ⟨408509, by rfl⟩ : syracuseStep 544679 = 817019) B817019
theorem B545435 : Blo 239816 545435 := bstep (se 1 (by rfl) ⟨409076, by rfl⟩ : syracuseStep 545435 = 818153) B818153
theorem B1037083 : Blo 239816 1037083 := bstep (se 1 (by rfl) ⟨777812, by rfl⟩ : syracuseStep 1037083 = 1555625) B1555625
theorem B2609981 : Blo 239816 2609981 := bstep (se 3 (by rfl) ⟨489371, by rfl⟩ : syracuseStep 2609981 = 978743) B978743
theorem B2774483 : Blo 239816 2774483 := bstep (se 1 (by rfl) ⟨2080862, by rfl⟩ : syracuseStep 2774483 = 4161725) B4161725
theorem B613919 : Blo 239816 613919 := bstep (se 1 (by rfl) ⟨460439, by rfl⟩ : syracuseStep 613919 = 920879) B920879
theorem B516287 : Blo 239816 516287 := bstep (se 1 (by rfl) ⟨387215, by rfl⟩ : syracuseStep 516287 = 774431) B774431
theorem B1270055 : Blo 239816 1270055 := bstep (se 1 (by rfl) ⟨952541, by rfl⟩ : syracuseStep 1270055 = 1905083) B1905083
theorem B8774243 : Blo 239816 8774243 := bstep (se 1 (by rfl) ⟨6580682, by rfl⟩ : syracuseStep 8774243 = 13161365) B13161365
theorem B3498653 : Blo 239816 3498653 := bstep (se 3 (by rfl) ⟨655997, by rfl⟩ : syracuseStep 3498653 = 1311995) B1311995
theorem B386203 : Blo 239816 386203 := bstep (se 1 (by rfl) ⟨289652, by rfl⟩ : syracuseStep 386203 = 579305) B579305
theorem B386651 : Blo 239816 386651 := bstep (se 1 (by rfl) ⟨289988, by rfl⟩ : syracuseStep 386651 = 579977) B579977
theorem B419431 : Blo 239816 419431 := bstep (se 1 (by rfl) ⟨314573, by rfl⟩ : syracuseStep 419431 = 629147) B629147
theorem B976637 : Blo 239816 976637 := bstep (se 3 (by rfl) ⟨183119, by rfl⟩ : syracuseStep 976637 = 366239) B366239
theorem B518969 : Blo 239816 518969 := bstep (se 2 (by rfl) ⟨194613, by rfl⟩ : syracuseStep 518969 = 389227) B389227
theorem B617431 : Blo 239816 617431 := bstep (se 1 (by rfl) ⟨463073, by rfl⟩ : syracuseStep 617431 = 926147) B926147
theorem B1371431 : Blo 239816 1371431 := bstep (se 1 (by rfl) ⟨1028573, by rfl⟩ : syracuseStep 1371431 = 2057147) B2057147
theorem B814427 : Blo 239816 814427 := bstep (se 1 (by rfl) ⟨610820, by rfl⟩ : syracuseStep 814427 = 1221641) B1221641
theorem B814751 : Blo 239816 814751 := bstep (se 1 (by rfl) ⟨611063, by rfl⟩ : syracuseStep 814751 = 1222127) B1222127
theorem B22180205 : Blo 239816 22180205 := bstep (se 3 (by rfl) ⟨4158788, by rfl⟩ : syracuseStep 22180205 = 8317577) B8317577
theorem B8057249 : Blo 239816 8057249 := bstep (se 2 (by rfl) ⟨3021468, by rfl⟩ : syracuseStep 8057249 = 6042937) B6042937
theorem B551580299 : Blo 239816 551580299 := bstep (se 1 (by rfl) ⟨413685224, by rfl⟩ : syracuseStep 551580299 = 827370449) B827370449
theorem B816263 : Blo 239816 816263 := bstep (se 1 (by rfl) ⟨612197, by rfl⟩ : syracuseStep 816263 = 1224395) B1224395
theorem B1471769 : Blo 239816 1471769 := bstep (se 2 (by rfl) ⟨551913, by rfl⟩ : syracuseStep 1471769 = 1103827) B1103827
theorem B685979 : Blo 239816 685979 := bstep (se 1 (by rfl) ⟨514484, by rfl⟩ : syracuseStep 685979 = 1028969) B1028969
theorem B2325671 : Blo 239816 2325671 := bstep (se 1 (by rfl) ⟨1744253, by rfl⟩ : syracuseStep 2325671 = 3488507) B3488507
theorem B359801 : Blo 239816 359801 := bstep (se 2 (by rfl) ⟨134925, by rfl⟩ : syracuseStep 359801 = 269851) B269851
theorem B360095 : Blo 239816 360095 := bstep (se 1 (by rfl) ⟨270071, by rfl⟩ : syracuseStep 360095 = 540143) B540143
theorem B360425 : Blo 239816 360425 := bstep (se 2 (by rfl) ⟨135159, by rfl⟩ : syracuseStep 360425 = 270319) B270319
theorem B360479 : Blo 239816 360479 := bstep (se 1 (by rfl) ⟨270359, by rfl⟩ : syracuseStep 360479 = 540719) B540719
theorem B491935 : Blo 239816 491935 := bstep (se 1 (by rfl) ⟨368951, by rfl⟩ : syracuseStep 491935 = 737903) B737903
theorem B361499 : Blo 239816 361499 := bstep (se 1 (by rfl) ⟨271124, by rfl⟩ : syracuseStep 361499 = 542249) B542249
theorem B492575 : Blo 239816 492575 := bstep (se 1 (by rfl) ⟨369431, by rfl⟩ : syracuseStep 492575 = 738863) B738863
theorem B459931 : Blo 239816 459931 := bstep (se 1 (by rfl) ⟨344948, by rfl⟩ : syracuseStep 459931 = 689897) B689897
theorem B559241 : Blo 239816 559241 := bstep (se 2 (by rfl) ⟨209715, by rfl⟩ : syracuseStep 559241 = 419431) B419431
theorem B363119 : Blo 239816 363119 := bstep (se 1 (by rfl) ⟨272339, by rfl⟩ : syracuseStep 363119 = 544679) B544679
theorem B363623 : Blo 239816 363623 := bstep (se 1 (by rfl) ⟨272717, by rfl⟩ : syracuseStep 363623 = 545435) B545435
theorem B1739987 : Blo 239816 1739987 := bstep (se 1 (by rfl) ⟨1304990, by rfl⟩ : syracuseStep 1739987 = 2609981) B2609981
theorem B462763 : Blo 239816 462763 := bstep (se 1 (by rfl) ⟨347072, by rfl⟩ : syracuseStep 462763 = 694145) B694145
theorem B823241 : Blo 239816 823241 := bstep (se 2 (by rfl) ⟨308715, by rfl⟩ : syracuseStep 823241 = 617431) B617431
theorem B921577 : Blo 239816 921577 := bstep (se 2 (by rfl) ⟨345591, by rfl⟩ : syracuseStep 921577 = 691183) B691183
theorem B36049211 : Blo 239816 36049211 := bstep (se 1 (by rfl) ⟨27036908, by rfl⟩ : syracuseStep 36049211 = 54073817) B54073817
theorem B660743 : Blo 239816 660743 := bstep (se 1 (by rfl) ⟨495557, by rfl⟩ : syracuseStep 660743 = 991115) B991115
theorem B4396463 : Blo 239816 4396463 := bstep (se 1 (by rfl) ⟨3297347, by rfl⟩ : syracuseStep 4396463 = 6594695) B6594695
theorem B1382777 : Blo 239816 1382777 := bstep (se 2 (by rfl) ⟨518541, by rfl⟩ : syracuseStep 1382777 = 1037083) B1037083
theorem B1712249 : Blo 239816 1712249 := bstep (se 2 (by rfl) ⟨642093, by rfl⟩ : syracuseStep 1712249 = 1284187) B1284187
theorem B14786803 : Blo 239816 14786803 := bstep (se 1 (by rfl) ⟨11090102, by rfl⟩ : syracuseStep 14786803 = 22180205) B22180205
theorem B270895 : Blo 239816 270895 := bstep (se 1 (by rfl) ⟨203171, by rfl⟩ : syracuseStep 270895 = 406343) B406343
theorem B271327 : Blo 239816 271327 := bstep (se 1 (by rfl) ⟨203495, by rfl⟩ : syracuseStep 271327 = 406991) B406991
theorem B272155 : Blo 239816 272155 := bstep (se 1 (by rfl) ⟨204116, by rfl⟩ : syracuseStep 272155 = 408233) B408233
theorem B1550447 : Blo 239816 1550447 := bstep (se 1 (by rfl) ⟨1162835, by rfl⟩ : syracuseStep 1550447 = 2325671) B2325671
theorem B239867 : Blo 239816 239867 := bstep (se 1 (by rfl) ⟨179900, by rfl⟩ : syracuseStep 239867 = 359801) B359801
theorem B240063 : Blo 239816 240063 := bstep (se 1 (by rfl) ⟨180047, by rfl⟩ : syracuseStep 240063 = 360095) B360095
theorem B240283 : Blo 239816 240283 := bstep (se 1 (by rfl) ⟨180212, by rfl⟩ : syracuseStep 240283 = 360425) B360425
theorem B2075327 : Blo 239816 2075327 := bstep (se 1 (by rfl) ⟨1556495, by rfl⟩ : syracuseStep 2075327 = 3112991) B3112991
theorem B240379 : Blo 239816 240379 := bstep (se 1 (by rfl) ⟨180284, by rfl⟩ : syracuseStep 240379 = 360569) B360569
theorem B240411 : Blo 239816 240411 := bstep (se 1 (by rfl) ⟨180308, by rfl⟩ : syracuseStep 240411 = 360617) B360617
theorem B240667 : Blo 239816 240667 := bstep (se 1 (by rfl) ⟨180500, by rfl⟩ : syracuseStep 240667 = 361001) B361001
theorem B240895 : Blo 239816 240895 := bstep (se 1 (by rfl) ⟨180671, by rfl⟩ : syracuseStep 240895 = 361343) B361343
theorem B241087 : Blo 239816 241087 := bstep (se 1 (by rfl) ⟨180815, by rfl⟩ : syracuseStep 241087 = 361631) B361631
theorem B241199 : Blo 239816 241199 := bstep (se 1 (by rfl) ⟨180899, by rfl⟩ : syracuseStep 241199 = 361799) B361799
theorem B699995 : Blo 239816 699995 := bstep (se 1 (by rfl) ⟨524996, by rfl⟩ : syracuseStep 699995 = 1049993) B1049993
theorem B1158761 : Blo 239816 1158761 := bstep (se 2 (by rfl) ⟨434535, by rfl⟩ : syracuseStep 1158761 = 869071) B869071
theorem B241263 : Blo 239816 241263 := bstep (se 1 (by rfl) ⟨180947, by rfl⟩ : syracuseStep 241263 = 361895) B361895
theorem B241599 : Blo 239816 241599 := bstep (se 1 (by rfl) ⟨181199, by rfl⟩ : syracuseStep 241599 = 362399) B362399
theorem B241663 : Blo 239816 241663 := bstep (se 1 (by rfl) ⟨181247, by rfl⟩ : syracuseStep 241663 = 362495) B362495
theorem B242223 : Blo 239816 242223 := bstep (se 1 (by rfl) ⟨181667, by rfl⟩ : syracuseStep 242223 = 363335) B363335
theorem B242367 : Blo 239816 242367 := bstep (se 1 (by rfl) ⟨181775, by rfl⟩ : syracuseStep 242367 = 363551) B363551
theorem B242431 : Blo 239816 242431 := bstep (se 1 (by rfl) ⟨181823, by rfl⟩ : syracuseStep 242431 = 363647) B363647
theorem B243167 : Blo 239816 243167 := bstep (se 1 (by rfl) ⟨182375, by rfl⟩ : syracuseStep 243167 = 364751) B364751
theorem B243303 : Blo 239816 243303 := bstep (se 1 (by rfl) ⟨182477, by rfl⟩ : syracuseStep 243303 = 364955) B364955
theorem B243391 : Blo 239816 243391 := bstep (se 1 (by rfl) ⟨182543, by rfl⟩ : syracuseStep 243391 = 365087) B365087
theorem B243455 : Blo 239816 243455 := bstep (se 1 (by rfl) ⟨182591, by rfl⟩ : syracuseStep 243455 = 365183) B365183
theorem B243483 : Blo 239816 243483 := bstep (se 1 (by rfl) ⟨182612, by rfl⟩ : syracuseStep 243483 = 365225) B365225
theorem B243623 : Blo 239816 243623 := bstep (se 1 (by rfl) ⟨182717, by rfl⟩ : syracuseStep 243623 = 365435) B365435
theorem B1849655 : Blo 239816 1849655 := bstep (se 1 (by rfl) ⟨1387241, by rfl⟩ : syracuseStep 1849655 = 2774483) B2774483
theorem B1030967 : Blo 239816 1030967 := bstep (se 1 (by rfl) ⟨773225, by rfl⟩ : syracuseStep 1030967 = 1546451) B1546451
theorem B1031069 : Blo 239816 1031069 := bstep (se 3 (by rfl) ⟨193325, by rfl⟩ : syracuseStep 1031069 = 386651) B386651
theorem B57425369 : Blo 239816 57425369 := bstep (se 2 (by rfl) ⟨21534513, by rfl⟩ : syracuseStep 57425369 = 43069027) B43069027
theorem B409279 : Blo 239816 409279 := bstep (se 1 (by rfl) ⟨306959, by rfl⟩ : syracuseStep 409279 = 613919) B613919
theorem B344191 : Blo 239816 344191 := bstep (se 1 (by rfl) ⟨258143, by rfl⟩ : syracuseStep 344191 = 516287) B516287
theorem B5849495 : Blo 239816 5849495 := bstep (se 1 (by rfl) ⟨4387121, by rfl⟩ : syracuseStep 5849495 = 8774243) B8774243
theorem B541097 : Blo 239816 541097 := bstep (se 2 (by rfl) ⟨202911, by rfl⟩ : syracuseStep 541097 = 405823) B405823
theorem B541241 : Blo 239816 541241 := bstep (se 2 (by rfl) ⟨202965, by rfl⟩ : syracuseStep 541241 = 405931) B405931
theorem B1229741 : Blo 239816 1229741 := bstep (se 3 (by rfl) ⟨230576, by rfl⟩ : syracuseStep 1229741 = 461153) B461153
theorem B345979 : Blo 239816 345979 := bstep (se 1 (by rfl) ⟨259484, by rfl⟩ : syracuseStep 345979 = 518969) B518969
theorem B19810325 : Blo 239816 19810325 := bstep (se 6 (by rfl) ⟨464304, by rfl⟩ : syracuseStep 19810325 = 928609) B928609
theorem B542951 : Blo 239816 542951 := bstep (se 1 (by rfl) ⟨407213, by rfl⟩ : syracuseStep 542951 = 814427) B814427
theorem B1296647 : Blo 239816 1296647 := bstep (se 1 (by rfl) ⟨972485, by rfl⟩ : syracuseStep 1296647 = 1944971) B1944971
theorem B543167 : Blo 239816 543167 := bstep (se 1 (by rfl) ⟨407375, by rfl⟩ : syracuseStep 543167 = 814751) B814751
theorem B544175 : Blo 239816 544175 := bstep (se 1 (by rfl) ⟨408131, by rfl⟩ : syracuseStep 544175 = 816263) B816263
theorem B544841 : Blo 239816 544841 := bstep (se 2 (by rfl) ⟨204315, by rfl⟩ : syracuseStep 544841 = 408631) B408631
theorem B4182763 : Blo 239816 4182763 := bstep (se 1 (by rfl) ⟨3137072, by rfl⟩ : syracuseStep 4182763 = 6274145) B6274145
theorem B1233791 : Blo 239816 1233791 := bstep (se 1 (by rfl) ⟨925343, by rfl⟩ : syracuseStep 1233791 = 1850687) B1850687
theorem B1562111 : Blo 239816 1562111 := bstep (se 1 (by rfl) ⟨1171583, by rfl⟩ : syracuseStep 1562111 = 2343167) B2343167
theorem B546569 : Blo 239816 546569 := bstep (se 2 (by rfl) ⟨204963, by rfl⟩ : syracuseStep 546569 = 409927) B409927
theorem B547307 : Blo 239816 547307 := bstep (se 1 (by rfl) ⟨410480, by rfl⟩ : syracuseStep 547307 = 820961) B820961
theorem B547559 : Blo 239816 547559 := bstep (se 1 (by rfl) ⟨410669, by rfl⟩ : syracuseStep 547559 = 821339) B821339
theorem B514937 : Blo 239816 514937 := bstep (se 2 (by rfl) ⟨193101, by rfl⟩ : syracuseStep 514937 = 386203) B386203
theorem B9329741 : Blo 239816 9329741 := bstep (se 3 (by rfl) ⟨1749326, by rfl⟩ : syracuseStep 9329741 = 3498653) B3498653
theorem B810971 : Blo 239816 810971 := bstep (se 1 (by rfl) ⟨608228, by rfl⟩ : syracuseStep 810971 = 1216457) B1216457
theorem B614537 : Blo 239816 614537 := bstep (se 2 (by rfl) ⟨230451, by rfl⟩ : syracuseStep 614537 = 460903) B460903
theorem B3892859 : Blo 239816 3892859 := bstep (se 1 (by rfl) ⟨2919644, by rfl⟩ : syracuseStep 3892859 = 5839289) B5839289
theorem B2058209 : Blo 239816 2058209 := bstep (se 2 (by rfl) ⟨771828, by rfl⟩ : syracuseStep 2058209 = 1543657) B1543657
theorem B584417 : Blo 239816 584417 := bstep (se 2 (by rfl) ⟨219156, by rfl⟩ : syracuseStep 584417 = 438313) B438313
theorem B846703 : Blo 239816 846703 := bstep (se 1 (by rfl) ⟨635027, by rfl⟩ : syracuseStep 846703 = 1270055) B1270055
theorem B4648265 : Blo 239816 4648265 := bstep (se 2 (by rfl) ⟨1743099, by rfl⟩ : syracuseStep 4648265 = 3486199) B3486199
theorem B651091 : Blo 239816 651091 := bstep (se 1 (by rfl) ⟨488318, by rfl⟩ : syracuseStep 651091 = 976637) B976637
theorem B914287 : Blo 239816 914287 := bstep (se 1 (by rfl) ⟨685715, by rfl⟩ : syracuseStep 914287 = 1371431) B1371431
theorem B3470633 : Blo 239816 3470633 := bstep (se 2 (by rfl) ⟨1301487, by rfl⟩ : syracuseStep 3470633 = 2602975) B2602975
theorem B29652439 : Blo 239816 29652439 := bstep (se 1 (by rfl) ⟨22239329, by rfl⟩ : syracuseStep 29652439 = 44478659) B44478659
theorem B5371499 : Blo 239816 5371499 := bstep (se 1 (by rfl) ⟨4028624, by rfl⟩ : syracuseStep 5371499 = 8057249) B8057249
theorem B367720199 : Blo 239816 367720199 := bstep (se 1 (by rfl) ⟨275790149, by rfl⟩ : syracuseStep 367720199 = 551580299) B551580299
theorem B4421567 : Blo 239816 4421567 := bstep (se 1 (by rfl) ⟨3316175, by rfl⟩ : syracuseStep 4421567 = 6632351) B6632351
theorem B981179 : Blo 239816 981179 := bstep (se 1 (by rfl) ⟨735884, by rfl⟩ : syracuseStep 981179 = 1471769) B1471769
theorem B457319 : Blo 239816 457319 := bstep (se 1 (by rfl) ⟨342989, by rfl⟩ : syracuseStep 457319 = 685979) B685979
theorem B360143 : Blo 239816 360143 := bstep (se 1 (by rfl) ⟨270107, by rfl⟩ : syracuseStep 360143 = 540215) B540215
theorem B851809 : Blo 239816 851809 := bstep (se 2 (by rfl) ⟨319428, by rfl⟩ : syracuseStep 851809 = 638857) B638857
theorem B458921 : Blo 239816 458921 := bstep (se 2 (by rfl) ⟨172095, by rfl⟩ : syracuseStep 458921 = 344191) B344191
theorem B3899663 : Blo 239816 3899663 := bstep (se 1 (by rfl) ⟨2924747, by rfl⟩ : syracuseStep 3899663 = 5849495) B5849495
theorem B360731 : Blo 239816 360731 := bstep (se 1 (by rfl) ⟨270548, by rfl⟩ : syracuseStep 360731 = 541097) B541097
theorem B360827 : Blo 239816 360827 := bstep (se 1 (by rfl) ⟨270620, by rfl⟩ : syracuseStep 360827 = 541241) B541241
theorem B655913 : Blo 239816 655913 := bstep (se 2 (by rfl) ⟨245967, by rfl⟩ : syracuseStep 655913 = 491935) B491935
theorem B819827 : Blo 239816 819827 := bstep (se 1 (by rfl) ⟨614870, by rfl⟩ : syracuseStep 819827 = 1229741) B1229741
theorem B361193 : Blo 239816 361193 := bstep (se 2 (by rfl) ⟨135447, by rfl⟩ : syracuseStep 361193 = 270895) B270895
theorem B361769 : Blo 239816 361769 := bstep (se 2 (by rfl) ⟨135663, by rfl⟩ : syracuseStep 361769 = 271327) B271327
theorem B13206883 : Blo 239816 13206883 := bstep (se 1 (by rfl) ⟨9905162, by rfl⟩ : syracuseStep 13206883 = 19810325) B19810325
theorem B361967 : Blo 239816 361967 := bstep (se 1 (by rfl) ⟨271475, by rfl⟩ : syracuseStep 361967 = 542951) B542951
theorem B362111 : Blo 239816 362111 := bstep (se 1 (by rfl) ⟨271583, by rfl⟩ : syracuseStep 362111 = 543167) B543167
theorem B362783 : Blo 239816 362783 := bstep (se 1 (by rfl) ⟨272087, by rfl⟩ : syracuseStep 362783 = 544175) B544175
theorem B362873 : Blo 239816 362873 := bstep (se 2 (by rfl) ⟨136077, by rfl⟩ : syracuseStep 362873 = 272155) B272155
theorem B461305 : Blo 239816 461305 := bstep (se 2 (by rfl) ⟨172989, by rfl⟩ : syracuseStep 461305 = 345979) B345979
theorem B363227 : Blo 239816 363227 := bstep (se 1 (by rfl) ⟨272420, by rfl⟩ : syracuseStep 363227 = 544841) B544841
theorem B1313533 : Blo 239816 1313533 := bstep (se 3 (by rfl) ⟨246287, by rfl⟩ : syracuseStep 1313533 = 492575) B492575
theorem B822527 : Blo 239816 822527 := bstep (se 1 (by rfl) ⟨616895, by rfl⟩ : syracuseStep 822527 = 1233791) B1233791
theorem B364379 : Blo 239816 364379 := bstep (se 1 (by rfl) ⟨273284, by rfl⟩ : syracuseStep 364379 = 546569) B546569
theorem B921851 : Blo 239816 921851 := bstep (se 1 (by rfl) ⟨691388, by rfl⟩ : syracuseStep 921851 = 1382777) B1382777
theorem B364871 : Blo 239816 364871 := bstep (se 1 (by rfl) ⟨273653, by rfl⟩ : syracuseStep 364871 = 547307) B547307
theorem B365039 : Blo 239816 365039 := bstep (se 1 (by rfl) ⟨273779, by rfl⟩ : syracuseStep 365039 = 547559) B547559
theorem B5577017 : Blo 239816 5577017 := bstep (se 2 (by rfl) ⟨2091381, by rfl⟩ : syracuseStep 5577017 = 4182763) B4182763
theorem B2595239 : Blo 239816 2595239 := bstep (se 1 (by rfl) ⟨1946429, by rfl⟩ : syracuseStep 2595239 = 3892859) B3892859
theorem B1219049 : Blo 239816 1219049 := bstep (se 2 (by rfl) ⟨457143, by rfl⟩ : syracuseStep 1219049 = 914287) B914287
theorem B1383551 : Blo 239816 1383551 := bstep (se 1 (by rfl) ⟨1037663, by rfl⟩ : syracuseStep 1383551 = 2075327) B2075327
theorem B466663 : Blo 239816 466663 := bstep (se 1 (by rfl) ⟨349997, by rfl⟩ : syracuseStep 466663 = 699995) B699995
theorem B3580999 : Blo 239816 3580999 := bstep (se 1 (by rfl) ⟨2685749, by rfl⟩ : syracuseStep 3580999 = 5371499) B5371499
theorem B245146799 : Blo 239816 245146799 := bstep (se 1 (by rfl) ⟨183860099, by rfl⟩ : syracuseStep 245146799 = 367720199) B367720199
theorem B153134317 : Blo 239816 153134317 := bstep (se 3 (by rfl) ⟨28712684, by rfl⟩ : syracuseStep 153134317 = 57425369) B57425369
theorem B304879 : Blo 239816 304879 := bstep (se 1 (by rfl) ⟨228659, by rfl⟩ : syracuseStep 304879 = 457319) B457319
theorem B240095 : Blo 239816 240095 := bstep (se 1 (by rfl) ⟨180071, by rfl⟩ : syracuseStep 240095 = 360143) B360143
theorem B240319 : Blo 239816 240319 := bstep (se 1 (by rfl) ⟨180239, by rfl⟩ : syracuseStep 240319 = 360479) B360479
theorem B240999 : Blo 239816 240999 := bstep (se 1 (by rfl) ⟨180749, by rfl⟩ : syracuseStep 240999 = 361499) B361499
theorem B372827 : Blo 239816 372827 := bstep (se 1 (by rfl) ⟨279620, by rfl⟩ : syracuseStep 372827 = 559241) B559241
theorem B864431 : Blo 239816 864431 := bstep (se 1 (by rfl) ⟨648323, by rfl⟩ : syracuseStep 864431 = 1296647) B1296647
theorem B242079 : Blo 239816 242079 := bstep (se 1 (by rfl) ⟨181559, by rfl⟩ : syracuseStep 242079 = 363119) B363119
theorem B242415 : Blo 239816 242415 := bstep (se 1 (by rfl) ⟨181811, by rfl⟩ : syracuseStep 242415 = 363623) B363623
theorem B1159991 : Blo 239816 1159991 := bstep (se 1 (by rfl) ⟨869993, by rfl⟩ : syracuseStep 1159991 = 1739987) B1739987
theorem B24032807 : Blo 239816 24032807 := bstep (se 1 (by rfl) ⟨18024605, by rfl⟩ : syracuseStep 24032807 = 36049211) B36049211
theorem B440495 : Blo 239816 440495 := bstep (se 1 (by rfl) ⟨330371, by rfl⟩ : syracuseStep 440495 = 660743) B660743
theorem B2930975 : Blo 239816 2930975 := bstep (se 1 (by rfl) ⟨2198231, by rfl⟩ : syracuseStep 2930975 = 4396463) B4396463
theorem B343291 : Blo 239816 343291 := bstep (se 1 (by rfl) ⟨257468, by rfl⟩ : syracuseStep 343291 = 514937) B514937
theorem B868121 : Blo 239816 868121 := bstep (se 2 (by rfl) ⟨325545, by rfl⟩ : syracuseStep 868121 = 651091) B651091
theorem B1228769 : Blo 239816 1228769 := bstep (se 2 (by rfl) ⟨460788, by rfl⟩ : syracuseStep 1228769 = 921577) B921577
theorem B540647 : Blo 239816 540647 := bstep (se 1 (by rfl) ⟨405485, by rfl⟩ : syracuseStep 540647 = 810971) B810971
theorem B409691 : Blo 239816 409691 := bstep (se 1 (by rfl) ⟨307268, by rfl⟩ : syracuseStep 409691 = 614537) B614537
theorem B1033631 : Blo 239816 1033631 := bstep (se 1 (by rfl) ⟨775223, by rfl⟩ : syracuseStep 1033631 = 1550447) B1550447
theorem B39536585 : Blo 239816 39536585 := bstep (se 2 (by rfl) ⟨14826219, by rfl⟩ : syracuseStep 39536585 = 29652439) B29652439
theorem B3098843 : Blo 239816 3098843 := bstep (se 1 (by rfl) ⟨2324132, by rfl⟩ : syracuseStep 3098843 = 4648265) B4648265
theorem B772507 : Blo 239816 772507 := bstep (se 1 (by rfl) ⟨579380, by rfl⟩ : syracuseStep 772507 = 1158761) B1158761
theorem B2313755 : Blo 239816 2313755 := bstep (se 1 (by rfl) ⟨1735316, by rfl⟩ : syracuseStep 2313755 = 3470633) B3470633
theorem B1233103 : Blo 239816 1233103 := bstep (se 1 (by rfl) ⟨924827, by rfl⟩ : syracuseStep 1233103 = 1849655) B1849655
theorem B545705 : Blo 239816 545705 := bstep (se 2 (by rfl) ⟨204639, by rfl⟩ : syracuseStep 545705 = 409279) B409279
theorem B1135745 : Blo 239816 1135745 := bstep (se 2 (by rfl) ⟨425904, by rfl⟩ : syracuseStep 1135745 = 851809) B851809
theorem B19715737 : Blo 239816 19715737 := bstep (se 2 (by rfl) ⟨7393401, by rfl⟩ : syracuseStep 19715737 = 14786803) B14786803
theorem B613241 : Blo 239816 613241 := bstep (se 2 (by rfl) ⟨229965, by rfl⟩ : syracuseStep 613241 = 459931) B459931
theorem B1041407 : Blo 239816 1041407 := bstep (se 1 (by rfl) ⟨781055, by rfl⟩ : syracuseStep 1041407 = 1562111) B1562111
theorem B4515749 : Blo 239816 4515749 := bstep (se 4 (by rfl) ⟨423351, by rfl⟩ : syracuseStep 4515749 = 846703) B846703
theorem B6219827 : Blo 239816 6219827 := bstep (se 1 (by rfl) ⟨4664870, by rfl⟩ : syracuseStep 6219827 = 9329741) B9329741
theorem B617017 : Blo 239816 617017 := bstep (se 2 (by rfl) ⟨231381, by rfl⟩ : syracuseStep 617017 = 462763) B462763
theorem B1141499 : Blo 239816 1141499 := bstep (se 1 (by rfl) ⟨856124, by rfl⟩ : syracuseStep 1141499 = 1712249) B1712249
theorem B1372139 : Blo 239816 1372139 := bstep (se 1 (by rfl) ⟨1029104, by rfl⟩ : syracuseStep 1372139 = 2058209) B2058209
theorem B389611 : Blo 239816 389611 := bstep (se 1 (by rfl) ⟨292208, by rfl⟩ : syracuseStep 389611 = 584417) B584417
theorem B2947711 : Blo 239816 2947711 := bstep (se 1 (by rfl) ⟨2210783, by rfl⟩ : syracuseStep 2947711 = 4421567) B4421567
theorem B654119 : Blo 239816 654119 := bstep (se 1 (by rfl) ⟨490589, by rfl⟩ : syracuseStep 654119 = 981179) B981179
theorem B687311 : Blo 239816 687311 := bstep (se 1 (by rfl) ⟨515483, by rfl⟩ : syracuseStep 687311 = 1030967) B1030967
theorem B687379 : Blo 239816 687379 := bstep (se 1 (by rfl) ⟨515534, by rfl⟩ : syracuseStep 687379 = 1031069) B1031069
theorem B2195309 : Blo 239816 2195309 := bstep (se 3 (by rfl) ⟨411620, by rfl⟩ : syracuseStep 2195309 = 823241) B823241
theorem B689087 : Blo 239816 689087 := bstep (se 1 (by rfl) ⟨516815, by rfl⟩ : syracuseStep 689087 = 1033631) B1033631
theorem B2065895 : Blo 239816 2065895 := bstep (se 1 (by rfl) ⟨1549421, by rfl⟩ : syracuseStep 2065895 = 3098843) B3098843
theorem B1542503 : Blo 239816 1542503 := bstep (se 1 (by rfl) ⟨1156877, by rfl⟩ : syracuseStep 1542503 = 2313755) B2313755
theorem B363803 : Blo 239816 363803 := bstep (se 1 (by rfl) ⟨272852, by rfl⟩ : syracuseStep 363803 = 545705) B545705
theorem B822689 : Blo 239816 822689 := bstep (se 2 (by rfl) ⟨308508, by rfl⟩ : syracuseStep 822689 = 617017) B617017
theorem B922367 : Blo 239816 922367 := bstep (se 1 (by rfl) ⟨691775, by rfl⟩ : syracuseStep 922367 = 1383551) B1383551
theorem B1644137 : Blo 239816 1644137 := bstep (se 2 (by rfl) ⟨616551, by rfl⟩ : syracuseStep 1644137 = 1233103) B1233103
theorem B694271 : Blo 239816 694271 := bstep (se 1 (by rfl) ⟨520703, by rfl⟩ : syracuseStep 694271 = 1041407) B1041407
theorem B816716357 : Blo 239816 816716357 := bstep (se 4 (by rfl) ⟨76567158, by rfl⟩ : syracuseStep 816716357 = 153134317) B153134317
theorem B26287649 : Blo 239816 26287649 := bstep (se 2 (by rfl) ⟨9857868, by rfl⟩ : syracuseStep 26287649 = 19715737) B19715737
theorem B436079 : Blo 239816 436079 := bstep (se 1 (by rfl) ⟨327059, by rfl⟩ : syracuseStep 436079 = 654119) B654119
theorem B273127 : Blo 239816 273127 := bstep (se 1 (by rfl) ⟨204845, by rfl⟩ : syracuseStep 273127 = 409691) B409691
theorem B305947 : Blo 239816 305947 := bstep (se 1 (by rfl) ⟨229460, by rfl⟩ : syracuseStep 305947 = 458921) B458921
theorem B2599775 : Blo 239816 2599775 := bstep (se 1 (by rfl) ⟨1949831, by rfl⟩ : syracuseStep 2599775 = 3899663) B3899663
theorem B240487 : Blo 239816 240487 := bstep (se 1 (by rfl) ⟨180365, by rfl⟩ : syracuseStep 240487 = 360731) B360731
theorem B240551 : Blo 239816 240551 := bstep (se 1 (by rfl) ⟨180413, by rfl⟩ : syracuseStep 240551 = 360827) B360827
theorem B437275 : Blo 239816 437275 := bstep (se 1 (by rfl) ⟨327956, by rfl⟩ : syracuseStep 437275 = 655913) B655913
theorem B240795 : Blo 239816 240795 := bstep (se 1 (by rfl) ⟨180596, by rfl⟩ : syracuseStep 240795 = 361193) B361193
theorem B241179 : Blo 239816 241179 := bstep (se 1 (by rfl) ⟨180884, by rfl⟩ : syracuseStep 241179 = 361769) B361769
theorem B241311 : Blo 239816 241311 := bstep (se 1 (by rfl) ⟨180983, by rfl⟩ : syracuseStep 241311 = 361967) B361967
theorem B241407 : Blo 239816 241407 := bstep (se 1 (by rfl) ⟨181055, by rfl⟩ : syracuseStep 241407 = 362111) B362111
theorem B26357723 : Blo 239816 26357723 := bstep (se 1 (by rfl) ⟨19768292, by rfl⟩ : syracuseStep 26357723 = 39536585) B39536585
theorem B241855 : Blo 239816 241855 := bstep (se 1 (by rfl) ⟨181391, by rfl⟩ : syracuseStep 241855 = 362783) B362783
theorem B241915 : Blo 239816 241915 := bstep (se 1 (by rfl) ⟨181436, by rfl⟩ : syracuseStep 241915 = 362873) B362873
theorem B17609177 : Blo 239816 17609177 := bstep (se 2 (by rfl) ⟨6603441, by rfl⟩ : syracuseStep 17609177 = 13206883) B13206883
theorem B242151 : Blo 239816 242151 := bstep (se 1 (by rfl) ⟨181613, by rfl⟩ : syracuseStep 242151 = 363227) B363227
theorem B406505 : Blo 239816 406505 := bstep (se 2 (by rfl) ⟨152439, by rfl⟩ : syracuseStep 406505 = 304879) B304879
theorem B242919 : Blo 239816 242919 := bstep (se 1 (by rfl) ⟨182189, by rfl⟩ : syracuseStep 242919 = 364379) B364379
theorem B243247 : Blo 239816 243247 := bstep (se 1 (by rfl) ⟨182435, by rfl⟩ : syracuseStep 243247 = 364871) B364871
theorem B243359 : Blo 239816 243359 := bstep (se 1 (by rfl) ⟨182519, by rfl⟩ : syracuseStep 243359 = 365039) B365039
theorem B1030009 : Blo 239816 1030009 := bstep (se 2 (by rfl) ⟨386253, by rfl⟩ : syracuseStep 1030009 = 772507) B772507
theorem B1751377 : Blo 239816 1751377 := bstep (se 2 (by rfl) ⟨656766, by rfl⟩ : syracuseStep 1751377 = 1313533) B1313533
theorem B408827 : Blo 239816 408827 := bstep (se 1 (by rfl) ⟨306620, by rfl⟩ : syracuseStep 408827 = 613241) B613241
theorem B163431199 : Blo 239816 163431199 := bstep (se 1 (by rfl) ⟨122573399, by rfl⟩ : syracuseStep 163431199 = 245146799) B245146799
theorem B4146551 : Blo 239816 4146551 := bstep (se 1 (by rfl) ⟨3109913, by rfl⟩ : syracuseStep 4146551 = 6219827) B6219827
theorem B248551 : Blo 239816 248551 := bstep (se 1 (by rfl) ⟨186413, by rfl⟩ : syracuseStep 248551 = 372827) B372827
theorem B576287 : Blo 239816 576287 := bstep (se 1 (by rfl) ⟨432215, by rfl⟩ : syracuseStep 576287 = 864431) B864431
theorem B773327 : Blo 239816 773327 := bstep (se 1 (by rfl) ⟨579995, by rfl⟩ : syracuseStep 773327 = 1159991) B1159991
theorem B1953983 : Blo 239816 1953983 := bstep (se 1 (by rfl) ⟨1465487, by rfl⟩ : syracuseStep 1953983 = 2930975) B2930975
theorem B578747 : Blo 239816 578747 := bstep (se 1 (by rfl) ⟨434060, by rfl⟩ : syracuseStep 578747 = 868121) B868121
theorem B1463539 : Blo 239816 1463539 := bstep (se 1 (by rfl) ⟨1097654, by rfl⟩ : syracuseStep 1463539 = 2195309) B2195309
theorem B546551 : Blo 239816 546551 := bstep (se 1 (by rfl) ⟨409913, by rfl⟩ : syracuseStep 546551 = 819827) B819827
theorem B12114613 : Blo 239816 12114613 := bstep (se 5 (by rfl) ⟨567872, by rfl⟩ : syracuseStep 12114613 = 1135745) B1135745
theorem B548351 : Blo 239816 548351 := bstep (se 1 (by rfl) ⟨411263, by rfl⟩ : syracuseStep 548351 = 822527) B822527
theorem B614567 : Blo 239816 614567 := bstep (se 1 (by rfl) ⟨460925, by rfl⟩ : syracuseStep 614567 = 921851) B921851
theorem B615073 : Blo 239816 615073 := bstep (se 2 (by rfl) ⟨230652, by rfl⟩ : syracuseStep 615073 = 461305) B461305
theorem B1730159 : Blo 239816 1730159 := bstep (se 1 (by rfl) ⟨1297619, by rfl⟩ : syracuseStep 1730159 = 2595239) B2595239
theorem B812699 : Blo 239816 812699 := bstep (se 1 (by rfl) ⟨609524, by rfl⟩ : syracuseStep 812699 = 1219049) B1219049
theorem B19098661 : Blo 239816 19098661 := bstep (se 4 (by rfl) ⟨1790499, by rfl⟩ : syracuseStep 19098661 = 3580999) B3580999
theorem B519481 : Blo 239816 519481 := bstep (se 2 (by rfl) ⟨194805, by rfl⟩ : syracuseStep 519481 = 389611) B389611
theorem B14872045 : Blo 239816 14872045 := bstep (se 3 (by rfl) ⟨2788508, by rfl⟩ : syracuseStep 14872045 = 5577017) B5577017
theorem B3010499 : Blo 239816 3010499 := bstep (se 1 (by rfl) ⟨2257874, by rfl⟩ : syracuseStep 3010499 = 4515749) B4515749
theorem B3043997 : Blo 239816 3043997 := bstep (se 3 (by rfl) ⟨570749, by rfl⟩ : syracuseStep 3043997 = 1141499) B1141499
theorem B914759 : Blo 239816 914759 := bstep (se 1 (by rfl) ⟨686069, by rfl⟩ : syracuseStep 914759 = 1372139) B1372139
theorem B3930281 : Blo 239816 3930281 := bstep (se 2 (by rfl) ⟨1473855, by rfl⟩ : syracuseStep 3930281 = 2947711) B2947711
theorem B16021871 : Blo 239816 16021871 := bstep (se 1 (by rfl) ⟨12016403, by rfl⟩ : syracuseStep 16021871 = 24032807) B24032807
theorem B293663 : Blo 239816 293663 := bstep (se 1 (by rfl) ⟨220247, by rfl⟩ : syracuseStep 293663 = 440495) B440495
theorem B457721 : Blo 239816 457721 := bstep (se 2 (by rfl) ⟨171645, by rfl⟩ : syracuseStep 457721 = 343291) B343291
theorem B916505 : Blo 239816 916505 := bstep (se 2 (by rfl) ⟨343689, by rfl⟩ : syracuseStep 916505 = 687379) B687379
theorem B458207 : Blo 239816 458207 := bstep (se 1 (by rfl) ⟨343655, by rfl⟩ : syracuseStep 458207 = 687311) B687311
theorem B622217 : Blo 239816 622217 := bstep (se 2 (by rfl) ⟨233331, by rfl⟩ : syracuseStep 622217 = 466663) B466663
theorem B819179 : Blo 239816 819179 := bstep (se 1 (by rfl) ⟨614384, by rfl⟩ : syracuseStep 819179 = 1228769) B1228769
theorem B360431 : Blo 239816 360431 := bstep (se 1 (by rfl) ⟨270323, by rfl⟩ : syracuseStep 360431 = 540647) B540647
theorem B820097 : Blo 239816 820097 := bstep (se 2 (by rfl) ⟨307536, by rfl⟩ : syracuseStep 820097 = 615073) B615073
theorem B1377263 : Blo 239816 1377263 := bstep (se 1 (by rfl) ⟨1032947, by rfl⟩ : syracuseStep 1377263 = 2065895) B2065895
theorem B217908265 : Blo 239816 217908265 := bstep (se 2 (by rfl) ⟨81715599, by rfl⟩ : syracuseStep 217908265 = 163431199) B163431199
theorem B1837565 : Blo 239816 1837565 := bstep (se 3 (by rfl) ⟨344543, by rfl⟩ : syracuseStep 1837565 = 689087) B689087
theorem B364169 : Blo 239816 364169 := bstep (se 2 (by rfl) ⟨136563, by rfl⟩ : syracuseStep 364169 = 273127) B273127
theorem B364367 : Blo 239816 364367 := bstep (se 1 (by rfl) ⟨273275, by rfl⟩ : syracuseStep 364367 = 546551) B546551
theorem B462847 : Blo 239816 462847 := bstep (se 1 (by rfl) ⟨347135, by rfl⟩ : syracuseStep 462847 = 694271) B694271
theorem B25464881 : Blo 239816 25464881 := bstep (se 2 (by rfl) ⟨9549330, by rfl⟩ : syracuseStep 25464881 = 19098661) B19098661
theorem B544477571 : Blo 239816 544477571 := bstep (se 1 (by rfl) ⟨408358178, by rfl⟩ : syracuseStep 544477571 = 816716357) B816716357
theorem B692641 : Blo 239816 692641 := bstep (se 2 (by rfl) ⟨259740, by rfl⟩ : syracuseStep 692641 = 519481) B519481
theorem B19829393 : Blo 239816 19829393 := bstep (se 2 (by rfl) ⟨7436022, by rfl⟩ : syracuseStep 19829393 = 14872045) B14872045
theorem B365567 : Blo 239816 365567 := bstep (se 1 (by rfl) ⟨274175, by rfl⟩ : syracuseStep 365567 = 548351) B548351
theorem B1153439 : Blo 239816 1153439 := bstep (se 1 (by rfl) ⟨865079, by rfl⟩ : syracuseStep 1153439 = 1730159) B1730159
theorem B2006999 : Blo 239816 2006999 := bstep (se 1 (by rfl) ⟨1505249, by rfl⟩ : syracuseStep 2006999 = 3010499) B3010499
theorem B17571815 : Blo 239816 17571815 := bstep (se 1 (by rfl) ⟨13178861, by rfl⟩ : syracuseStep 17571815 = 26357723) B26357723
theorem B11739451 : Blo 239816 11739451 := bstep (se 1 (by rfl) ⟨8804588, by rfl⟩ : syracuseStep 11739451 = 17609177) B17609177
theorem B2335169 : Blo 239816 2335169 := bstep (se 2 (by rfl) ⟨875688, by rfl⟩ : syracuseStep 2335169 = 1751377) B1751377
theorem B271003 : Blo 239816 271003 := bstep (se 1 (by rfl) ⟨203252, by rfl⟩ : syracuseStep 271003 = 406505) B406505
theorem B305147 : Blo 239816 305147 := bstep (se 1 (by rfl) ⟨228860, by rfl⟩ : syracuseStep 305147 = 457721) B457721
theorem B272551 : Blo 239816 272551 := bstep (se 1 (by rfl) ⟨204413, by rfl⟩ : syracuseStep 272551 = 408827) B408827
theorem B305471 : Blo 239816 305471 := bstep (se 1 (by rfl) ⟨229103, by rfl⟩ : syracuseStep 305471 = 458207) B458207
theorem B240287 : Blo 239816 240287 := bstep (se 1 (by rfl) ⟨180215, by rfl⟩ : syracuseStep 240287 = 360431) B360431
theorem B2764367 : Blo 239816 2764367 := bstep (se 1 (by rfl) ⟨2073275, by rfl⟩ : syracuseStep 2764367 = 4146551) B4146551
theorem B1028335 : Blo 239816 1028335 := bstep (se 1 (by rfl) ⟨771251, by rfl⟩ : syracuseStep 1028335 = 1542503) B1542503
theorem B242535 : Blo 239816 242535 := bstep (se 1 (by rfl) ⟨181901, by rfl⟩ : syracuseStep 242535 = 363803) B363803
theorem B407929 : Blo 239816 407929 := bstep (se 2 (by rfl) ⟨152973, by rfl⟩ : syracuseStep 407929 = 305947) B305947
theorem B1096091 : Blo 239816 1096091 := bstep (se 1 (by rfl) ⟨822068, by rfl⟩ : syracuseStep 1096091 = 1644137) B1644137
theorem B1325605 : Blo 239816 1325605 := bstep (se 4 (by rfl) ⟨124275, by rfl⟩ : syracuseStep 1325605 = 248551) B248551
theorem B409711 : Blo 239816 409711 := bstep (se 1 (by rfl) ⟨307283, by rfl⟩ : syracuseStep 409711 = 614567) B614567
theorem B541799 : Blo 239816 541799 := bstep (se 1 (by rfl) ⟨406349, by rfl⟩ : syracuseStep 541799 = 812699) B812699
theorem B1951385 : Blo 239816 1951385 := bstep (se 2 (by rfl) ⟨731769, by rfl⟩ : syracuseStep 1951385 = 1463539) B1463539
theorem B609839 : Blo 239816 609839 := bstep (se 1 (by rfl) ⟨457379, by rfl⟩ : syracuseStep 609839 = 914759) B914759
theorem B611003 : Blo 239816 611003 := bstep (se 1 (by rfl) ⟨458252, by rfl⟩ : syracuseStep 611003 = 916505) B916505
theorem B414811 : Blo 239816 414811 := bstep (se 1 (by rfl) ⟨311108, by rfl⟩ : syracuseStep 414811 = 622217) B622217
theorem B546119 : Blo 239816 546119 := bstep (se 1 (by rfl) ⟨409589, by rfl⟩ : syracuseStep 546119 = 819179) B819179
theorem B384191 : Blo 239816 384191 := bstep (se 1 (by rfl) ⟨288143, by rfl⟩ : syracuseStep 384191 = 576287) B576287
theorem B548459 : Blo 239816 548459 := bstep (se 1 (by rfl) ⟨411344, by rfl⟩ : syracuseStep 548459 = 822689) B822689
theorem B1302655 : Blo 239816 1302655 := bstep (se 1 (by rfl) ⟨976991, by rfl⟩ : syracuseStep 1302655 = 1953983) B1953983
theorem B614911 : Blo 239816 614911 := bstep (se 1 (by rfl) ⟨461183, by rfl⟩ : syracuseStep 614911 = 922367) B922367
theorem B385831 : Blo 239816 385831 := bstep (se 1 (by rfl) ⟨289373, by rfl⟩ : syracuseStep 385831 = 578747) B578747
theorem B583033 : Blo 239816 583033 := bstep (se 2 (by rfl) ⟨218637, by rfl⟩ : syracuseStep 583033 = 437275) B437275
theorem B17525099 : Blo 239816 17525099 := bstep (se 1 (by rfl) ⟨13143824, by rfl⟩ : syracuseStep 17525099 = 26287649) B26287649
theorem B290719 : Blo 239816 290719 := bstep (se 1 (by rfl) ⟨218039, by rfl⟩ : syracuseStep 290719 = 436079) B436079
theorem B1733183 : Blo 239816 1733183 := bstep (se 1 (by rfl) ⟨1299887, by rfl⟩ : syracuseStep 1733183 = 2599775) B2599775
theorem B783101 : Blo 239816 783101 := bstep (se 3 (by rfl) ⟨146831, by rfl⟩ : syracuseStep 783101 = 293663) B293663
theorem B1373345 : Blo 239816 1373345 := bstep (se 2 (by rfl) ⟨515004, by rfl⟩ : syracuseStep 1373345 = 1030009) B1030009
theorem B2029331 : Blo 239816 2029331 := bstep (se 1 (by rfl) ⟨1521998, by rfl⟩ : syracuseStep 2029331 = 3043997) B3043997
theorem B2062205 : Blo 239816 2062205 := bstep (se 3 (by rfl) ⟨386663, by rfl⟩ : syracuseStep 2062205 = 773327) B773327
theorem B16152817 : Blo 239816 16152817 := bstep (se 2 (by rfl) ⟨6057306, by rfl⟩ : syracuseStep 16152817 = 12114613) B12114613
theorem B2620187 : Blo 239816 2620187 := bstep (se 1 (by rfl) ⟨1965140, by rfl⟩ : syracuseStep 2620187 = 3930281) B3930281
theorem B10681247 : Blo 239816 10681247 := bstep (se 1 (by rfl) ⟨8010935, by rfl⟩ : syracuseStep 10681247 = 16021871) B16021871
theorem B1736873 : Blo 239816 1736873 := bstep (se 2 (by rfl) ⟨651327, by rfl⟩ : syracuseStep 1736873 = 1302655) B1302655
theorem B918175 : Blo 239816 918175 := bstep (se 1 (by rfl) ⟨688631, by rfl⟩ : syracuseStep 918175 = 1377263) B1377263
theorem B819881 : Blo 239816 819881 := bstep (se 2 (by rfl) ⟨307455, by rfl⟩ : syracuseStep 819881 = 614911) B614911
theorem B361199 : Blo 239816 361199 := bstep (se 1 (by rfl) ⟨270899, by rfl⟩ : syracuseStep 361199 = 541799) B541799
theorem B361337 : Blo 239816 361337 := bstep (se 2 (by rfl) ⟨135501, by rfl⟩ : syracuseStep 361337 = 271003) B271003
theorem B16976587 : Blo 239816 16976587 := bstep (se 1 (by rfl) ⟨12732440, by rfl⟩ : syracuseStep 16976587 = 25464881) B25464881
theorem B363401 : Blo 239816 363401 := bstep (se 2 (by rfl) ⟨136275, by rfl⟩ : syracuseStep 363401 = 272551) B272551
theorem B364079 : Blo 239816 364079 := bstep (se 1 (by rfl) ⟨273059, by rfl⟩ : syracuseStep 364079 = 546119) B546119
theorem B5411549 : Blo 239816 5411549 := bstep (se 3 (by rfl) ⟨1014665, by rfl⟩ : syracuseStep 5411549 = 2029331) B2029331
theorem B365639 : Blo 239816 365639 := bstep (se 1 (by rfl) ⟨274229, by rfl⟩ : syracuseStep 365639 = 548459) B548459
theorem B923521 : Blo 239816 923521 := bstep (se 2 (by rfl) ⟨346320, by rfl⟩ : syracuseStep 923521 = 692641) B692641
theorem B1842911 : Blo 239816 1842911 := bstep (se 1 (by rfl) ⟨1382183, by rfl⟩ : syracuseStep 1842911 = 2764367) B2764367
theorem B21537089 : Blo 239816 21537089 := bstep (se 2 (by rfl) ⟨8076408, by rfl⟩ : syracuseStep 21537089 = 16152817) B16152817
theorem B1155455 : Blo 239816 1155455 := bstep (se 1 (by rfl) ⟨866591, by rfl⟩ : syracuseStep 1155455 = 1733183) B1733183
theorem B730727 : Blo 239816 730727 := bstep (se 1 (by rfl) ⟨548045, by rfl⟩ : syracuseStep 730727 = 1096091) B1096091
theorem B1746791 : Blo 239816 1746791 := bstep (se 1 (by rfl) ⟨1310093, by rfl⟩ : syracuseStep 1746791 = 2620187) B2620187
theorem B7120831 : Blo 239816 7120831 := bstep (se 1 (by rfl) ⟨5340623, by rfl⟩ : syracuseStep 7120831 = 10681247) B10681247
theorem B1550501 : Blo 239816 1550501 := bstep (se 4 (by rfl) ⟨145359, by rfl⟩ : syracuseStep 1550501 = 290719) B290719
theorem B1225043 : Blo 239816 1225043 := bstep (se 1 (by rfl) ⟨918782, by rfl⟩ : syracuseStep 1225043 = 1837565) B1837565
theorem B406559 : Blo 239816 406559 := bstep (se 1 (by rfl) ⟨304919, by rfl⟩ : syracuseStep 406559 = 609839) B609839
theorem B242779 : Blo 239816 242779 := bstep (se 1 (by rfl) ⟨182084, by rfl⟩ : syracuseStep 242779 = 364169) B364169
theorem B242911 : Blo 239816 242911 := bstep (se 1 (by rfl) ⟨182183, by rfl⟩ : syracuseStep 242911 = 364367) B364367
theorem B362985047 : Blo 239816 362985047 := bstep (se 1 (by rfl) ⟨272238785, by rfl⟩ : syracuseStep 362985047 = 544477571) B544477571
theorem B13219595 : Blo 239816 13219595 := bstep (se 1 (by rfl) ⟨9914696, by rfl⟩ : syracuseStep 13219595 = 19829393) B19829393
theorem B407335 : Blo 239816 407335 := bstep (se 1 (by rfl) ⟨305501, by rfl⟩ : syracuseStep 407335 = 611003) B611003
theorem B243711 : Blo 239816 243711 := bstep (se 1 (by rfl) ⟨182783, by rfl⟩ : syracuseStep 243711 = 365567) B365567
theorem B768959 : Blo 239816 768959 := bstep (se 1 (by rfl) ⟨576719, by rfl⟩ : syracuseStep 768959 = 1153439) B1153439
theorem B11714543 : Blo 239816 11714543 := bstep (se 1 (by rfl) ⟨8785907, by rfl⟩ : syracuseStep 11714543 = 17571815) B17571815
theorem B1556779 : Blo 239816 1556779 := bstep (se 1 (by rfl) ⟨1167584, by rfl⟩ : syracuseStep 1556779 = 2335169) B2335169
theorem B11683399 : Blo 239816 11683399 := bstep (se 1 (by rfl) ⟨8762549, by rfl⟩ : syracuseStep 11683399 = 17525099) B17525099
theorem B543905 : Blo 239816 543905 := bstep (se 2 (by rfl) ⟨203964, by rfl⟩ : syracuseStep 543905 = 407929) B407929
theorem B546281 : Blo 239816 546281 := bstep (se 2 (by rfl) ⟨204855, by rfl⟩ : syracuseStep 546281 = 409711) B409711
theorem B15652601 : Blo 239816 15652601 := bstep (se 2 (by rfl) ⟨5869725, by rfl⟩ : syracuseStep 15652601 = 11739451) B11739451
theorem B546731 : Blo 239816 546731 := bstep (se 1 (by rfl) ⟨410048, by rfl⟩ : syracuseStep 546731 = 820097) B820097
theorem B514441 : Blo 239816 514441 := bstep (se 2 (by rfl) ⟨192915, by rfl⟩ : syracuseStep 514441 = 385831) B385831
theorem B290544353 : Blo 239816 290544353 := bstep (se 2 (by rfl) ⟨108954132, by rfl⟩ : syracuseStep 290544353 = 217908265) B217908265
theorem B777377 : Blo 239816 777377 := bstep (se 2 (by rfl) ⟨291516, by rfl⟩ : syracuseStep 777377 = 583033) B583033
theorem B5203693 : Blo 239816 5203693 := bstep (se 3 (by rfl) ⟨975692, by rfl⟩ : syracuseStep 5203693 = 1951385) B1951385
theorem B256127 : Blo 239816 256127 := bstep (se 1 (by rfl) ⟨192095, by rfl⟩ : syracuseStep 256127 = 384191) B384191
theorem B1337999 : Blo 239816 1337999 := bstep (se 1 (by rfl) ⟨1003499, by rfl⟩ : syracuseStep 1337999 = 2006999) B2006999
theorem B813725 : Blo 239816 813725 := bstep (se 3 (by rfl) ⟨152573, by rfl⟩ : syracuseStep 813725 = 305147) B305147
theorem B617129 : Blo 239816 617129 := bstep (se 2 (by rfl) ⟨231423, by rfl⟩ : syracuseStep 617129 = 462847) B462847
theorem B1371113 : Blo 239816 1371113 := bstep (se 2 (by rfl) ⟨514167, by rfl⟩ : syracuseStep 1371113 = 1028335) B1028335
theorem B814589 : Blo 239816 814589 := bstep (se 3 (by rfl) ⟨152735, by rfl⟩ : syracuseStep 814589 = 305471) B305471
theorem B553081 : Blo 239816 553081 := bstep (se 2 (by rfl) ⟨207405, by rfl⟩ : syracuseStep 553081 = 414811) B414811
theorem B522067 : Blo 239816 522067 := bstep (se 1 (by rfl) ⟨391550, by rfl⟩ : syracuseStep 522067 = 783101) B783101
theorem B1767473 : Blo 239816 1767473 := bstep (se 2 (by rfl) ⟨662802, by rfl⟩ : syracuseStep 1767473 = 1325605) B1325605
theorem B915563 : Blo 239816 915563 := bstep (se 1 (by rfl) ⟨686672, by rfl⟩ : syracuseStep 915563 = 1373345) B1373345
theorem B1374803 : Blo 239816 1374803 := bstep (se 1 (by rfl) ⟨1031102, by rfl⟩ : syracuseStep 1374803 = 2062205) B2062205
theorem B362603 : Blo 239816 362603 := bstep (se 1 (by rfl) ⟨271952, by rfl⟩ : syracuseStep 362603 = 543905) B543905
theorem B364187 : Blo 239816 364187 := bstep (se 1 (by rfl) ⟨273140, by rfl⟩ : syracuseStep 364187 = 546281) B546281
theorem B364487 : Blo 239816 364487 := bstep (se 1 (by rfl) ⟨273365, by rfl⟩ : syracuseStep 364487 = 546731) B546731
theorem B193696235 : Blo 239816 193696235 := bstep (se 1 (by rfl) ⟨145272176, by rfl⟩ : syracuseStep 193696235 = 290544353) B290544353
theorem B14358059 : Blo 239816 14358059 := bstep (se 1 (by rfl) ⟨10768544, by rfl⟩ : syracuseStep 14358059 = 21537089) B21537089
theorem B696089 : Blo 239816 696089 := bstep (se 2 (by rfl) ⟨261033, by rfl⟩ : syracuseStep 696089 = 522067) B522067
theorem B271039 : Blo 239816 271039 := bstep (se 1 (by rfl) ⟨203279, by rfl⟩ : syracuseStep 271039 = 406559) B406559
theorem B7809695 : Blo 239816 7809695 := bstep (se 1 (by rfl) ⟨5857271, by rfl⟩ : syracuseStep 7809695 = 11714543) B11714543
theorem B1157915 : Blo 239816 1157915 := bstep (se 1 (by rfl) ⟨868436, by rfl⟩ : syracuseStep 1157915 = 1736873) B1736873
theorem B2075705 : Blo 239816 2075705 := bstep (se 2 (by rfl) ⟨778389, by rfl⟩ : syracuseStep 2075705 = 1556779) B1556779
theorem B240799 : Blo 239816 240799 := bstep (se 1 (by rfl) ⟨180599, by rfl⟩ : syracuseStep 240799 = 361199) B361199
theorem B240891 : Blo 239816 240891 := bstep (se 1 (by rfl) ⟨180668, by rfl⟩ : syracuseStep 240891 = 361337) B361337
theorem B1224233 : Blo 239816 1224233 := bstep (se 2 (by rfl) ⟨459087, by rfl⟩ : syracuseStep 1224233 = 918175) B918175
theorem B14430797 : Blo 239816 14430797 := bstep (se 3 (by rfl) ⟨2705774, by rfl⟩ : syracuseStep 14430797 = 5411549) B5411549
theorem B242267 : Blo 239816 242267 := bstep (se 1 (by rfl) ⟨181700, by rfl⟩ : syracuseStep 242267 = 363401) B363401
theorem B15577865 : Blo 239816 15577865 := bstep (se 2 (by rfl) ⟨5841699, by rfl⟩ : syracuseStep 15577865 = 11683399) B11683399
theorem B242719 : Blo 239816 242719 := bstep (se 1 (by rfl) ⟨182039, by rfl⟩ : syracuseStep 242719 = 364079) B364079
theorem B243759 : Blo 239816 243759 := bstep (se 1 (by rfl) ⟨182819, by rfl⟩ : syracuseStep 243759 = 365639) B365639
theorem B10435067 : Blo 239816 10435067 := bstep (se 1 (by rfl) ⟨7826300, by rfl⟩ : syracuseStep 10435067 = 15652601) B15652601
theorem B1228607 : Blo 239816 1228607 := bstep (se 1 (by rfl) ⟨921455, by rfl⟩ : syracuseStep 1228607 = 1842911) B1842911
theorem B737441 : Blo 239816 737441 := bstep (se 2 (by rfl) ⟨276540, by rfl⟩ : syracuseStep 737441 = 553081) B553081
theorem B770303 : Blo 239816 770303 := bstep (se 1 (by rfl) ⟨577727, by rfl⟩ : syracuseStep 770303 = 1155455) B1155455
theorem B1164527 : Blo 239816 1164527 := bstep (se 1 (by rfl) ⟨873395, by rfl⟩ : syracuseStep 1164527 = 1746791) B1746791
theorem B1033667 : Blo 239816 1033667 := bstep (se 1 (by rfl) ⟨775250, by rfl⟩ : syracuseStep 1033667 = 1550501) B1550501
theorem B542483 : Blo 239816 542483 := bstep (se 1 (by rfl) ⟨406862, by rfl⟩ : syracuseStep 542483 = 813725) B813725
theorem B411419 : Blo 239816 411419 := bstep (se 1 (by rfl) ⟨308564, by rfl⟩ : syracuseStep 411419 = 617129) B617129
theorem B543059 : Blo 239816 543059 := bstep (se 1 (by rfl) ⟨407294, by rfl⟩ : syracuseStep 543059 = 814589) B814589
theorem B543113 : Blo 239816 543113 := bstep (se 2 (by rfl) ⟨203667, by rfl⟩ : syracuseStep 543113 = 407335) B407335
theorem B1231361 : Blo 239816 1231361 := bstep (se 2 (by rfl) ⟨461760, by rfl⟩ : syracuseStep 1231361 = 923521) B923521
theorem B610375 : Blo 239816 610375 := bstep (se 1 (by rfl) ⟨457781, by rfl⟩ : syracuseStep 610375 = 915563) B915563
theorem B512639 : Blo 239816 512639 := bstep (se 1 (by rfl) ⟨384479, by rfl⟩ : syracuseStep 512639 = 768959) B768959
theorem B546587 : Blo 239816 546587 := bstep (se 1 (by rfl) ⟨409940, by rfl⟩ : syracuseStep 546587 = 819881) B819881
theorem B6938257 : Blo 239816 6938257 := bstep (se 2 (by rfl) ⟨2601846, by rfl⟩ : syracuseStep 6938257 = 5203693) B5203693
theorem B9494441 : Blo 239816 9494441 := bstep (se 2 (by rfl) ⟨3560415, by rfl⟩ : syracuseStep 9494441 = 7120831) B7120831
theorem B22635449 : Blo 239816 22635449 := bstep (se 2 (by rfl) ⟨8488293, by rfl⟩ : syracuseStep 22635449 = 16976587) B16976587
theorem B518251 : Blo 239816 518251 := bstep (se 1 (by rfl) ⟨388688, by rfl⟩ : syracuseStep 518251 = 777377) B777377
theorem B683005 : Blo 239816 683005 := bstep (se 3 (by rfl) ⟨128063, by rfl⟩ : syracuseStep 683005 = 256127) B256127
theorem B487151 : Blo 239816 487151 := bstep (se 1 (by rfl) ⟨365363, by rfl⟩ : syracuseStep 487151 = 730727) B730727
theorem B3567997 : Blo 239816 3567997 := bstep (se 3 (by rfl) ⟨668999, by rfl⟩ : syracuseStep 3567997 = 1337999) B1337999
theorem B914075 : Blo 239816 914075 := bstep (se 1 (by rfl) ⟨685556, by rfl⟩ : syracuseStep 914075 = 1371113) B1371113
theorem B816695 : Blo 239816 816695 := bstep (se 1 (by rfl) ⟨612521, by rfl⟩ : syracuseStep 816695 = 1225043) B1225043
theorem B685921 : Blo 239816 685921 := bstep (se 2 (by rfl) ⟨257220, by rfl⟩ : syracuseStep 685921 = 514441) B514441
theorem B241990031 : Blo 239816 241990031 := bstep (se 1 (by rfl) ⟨181492523, by rfl⟩ : syracuseStep 241990031 = 362985047) B362985047
theorem B8813063 : Blo 239816 8813063 := bstep (se 1 (by rfl) ⟨6609797, by rfl⟩ : syracuseStep 8813063 = 13219595) B13219595
theorem B1178315 : Blo 239816 1178315 := bstep (se 1 (by rfl) ⟨883736, by rfl⟩ : syracuseStep 1178315 = 1767473) B1767473
theorem B916535 : Blo 239816 916535 := bstep (se 1 (by rfl) ⟨687401, by rfl⟩ : syracuseStep 916535 = 1374803) B1374803
theorem B491627 : Blo 239816 491627 := bstep (se 1 (by rfl) ⟨368720, by rfl⟩ : syracuseStep 491627 = 737441) B737441
theorem B361385 : Blo 239816 361385 := bstep (se 2 (by rfl) ⟨135519, by rfl⟩ : syracuseStep 361385 = 271039) B271039
theorem B689111 : Blo 239816 689111 := bstep (se 1 (by rfl) ⟨516833, by rfl⟩ : syracuseStep 689111 = 1033667) B1033667
theorem B361655 : Blo 239816 361655 := bstep (se 1 (by rfl) ⟨271241, by rfl⟩ : syracuseStep 361655 = 542483) B542483
theorem B362039 : Blo 239816 362039 := bstep (se 1 (by rfl) ⟨271529, by rfl⟩ : syracuseStep 362039 = 543059) B543059
theorem B362075 : Blo 239816 362075 := bstep (se 1 (by rfl) ⟨271556, by rfl⟩ : syracuseStep 362075 = 543113) B543113
theorem B820907 : Blo 239816 820907 := bstep (se 1 (by rfl) ⟨615680, by rfl⟩ : syracuseStep 820907 = 1231361) B1231361
theorem B691001 : Blo 239816 691001 := bstep (se 2 (by rfl) ⟨259125, by rfl⟩ : syracuseStep 691001 = 518251) B518251
theorem B9572039 : Blo 239816 9572039 := bstep (se 1 (by rfl) ⟨7179029, by rfl⟩ : syracuseStep 9572039 = 14358059) B14358059
theorem B364391 : Blo 239816 364391 := bstep (se 1 (by rfl) ⟨273293, by rfl⟩ : syracuseStep 364391 = 546587) B546587
theorem B464059 : Blo 239816 464059 := bstep (se 1 (by rfl) ⟨348044, by rfl⟩ : syracuseStep 464059 = 696089) B696089
theorem B6329627 : Blo 239816 6329627 := bstep (se 1 (by rfl) ⟨4747220, by rfl⟩ : syracuseStep 6329627 = 9494441) B9494441
theorem B4757329 : Blo 239816 4757329 := bstep (se 2 (by rfl) ⟨1783998, by rfl⟩ : syracuseStep 4757329 = 3567997) B3567997
theorem B23501501 : Blo 239816 23501501 := bstep (se 3 (by rfl) ⟨4406531, by rfl⟩ : syracuseStep 23501501 = 8813063) B8813063
theorem B1383803 : Blo 239816 1383803 := bstep (se 1 (by rfl) ⟨1037852, by rfl⟩ : syracuseStep 1383803 = 2075705) B2075705
theorem B161326687 : Blo 239816 161326687 := bstep (se 1 (by rfl) ⟨120995015, by rfl⟩ : syracuseStep 161326687 = 241990031) B241990031
theorem B6956711 : Blo 239816 6956711 := bstep (se 1 (by rfl) ⟨5217533, by rfl⟩ : syracuseStep 6956711 = 10435067) B10435067
theorem B9251009 : Blo 239816 9251009 := bstep (se 2 (by rfl) ⟨3469128, by rfl⟩ : syracuseStep 9251009 = 6938257) B6938257
theorem B274279 : Blo 239816 274279 := bstep (se 1 (by rfl) ⟨205709, by rfl⟩ : syracuseStep 274279 = 411419) B411419
theorem B241735 : Blo 239816 241735 := bstep (se 1 (by rfl) ⟨181301, by rfl⟩ : syracuseStep 241735 = 362603) B362603
theorem B242791 : Blo 239816 242791 := bstep (se 1 (by rfl) ⟨182093, by rfl⟩ : syracuseStep 242791 = 364187) B364187
theorem B242991 : Blo 239816 242991 := bstep (se 1 (by rfl) ⟨182243, by rfl⟩ : syracuseStep 242991 = 364487) B364487
theorem B341759 : Blo 239816 341759 := bstep (se 1 (by rfl) ⟨256319, by rfl⟩ : syracuseStep 341759 = 512639) B512639
theorem B15090299 : Blo 239816 15090299 := bstep (se 1 (by rfl) ⟨11317724, by rfl⟩ : syracuseStep 15090299 = 22635449) B22635449
theorem B771943 : Blo 239816 771943 := bstep (se 1 (by rfl) ⟨578957, by rfl⟩ : syracuseStep 771943 = 1157915) B1157915
theorem B9620531 : Blo 239816 9620531 := bstep (se 1 (by rfl) ⟨7215398, by rfl⟩ : syracuseStep 9620531 = 14430797) B14430797
theorem B609383 : Blo 239816 609383 := bstep (se 1 (by rfl) ⟨457037, by rfl⟩ : syracuseStep 609383 = 914075) B914075
theorem B544463 : Blo 239816 544463 := bstep (se 1 (by rfl) ⟨408347, by rfl⟩ : syracuseStep 544463 = 816695) B816695
theorem B611023 : Blo 239816 611023 := bstep (se 1 (by rfl) ⟨458267, by rfl⟩ : syracuseStep 611023 = 916535) B916535
theorem B513535 : Blo 239816 513535 := bstep (se 1 (by rfl) ⟨385151, by rfl⟩ : syracuseStep 513535 = 770303) B770303
theorem B776351 : Blo 239816 776351 := bstep (se 1 (by rfl) ⟨582263, by rfl⟩ : syracuseStep 776351 = 1164527) B1164527
theorem B129130823 : Blo 239816 129130823 := bstep (se 1 (by rfl) ⟨96848117, by rfl⟩ : syracuseStep 129130823 = 193696235) B193696235
theorem B910673 : Blo 239816 910673 := bstep (se 2 (by rfl) ⟨341502, by rfl⟩ : syracuseStep 910673 = 683005) B683005
theorem B813833 : Blo 239816 813833 := bstep (se 2 (by rfl) ⟨305187, by rfl⟩ : syracuseStep 813833 = 610375) B610375
theorem B5206463 : Blo 239816 5206463 := bstep (se 1 (by rfl) ⟨3904847, by rfl⟩ : syracuseStep 5206463 = 7809695) B7809695
theorem B816155 : Blo 239816 816155 := bstep (se 1 (by rfl) ⟨612116, by rfl⟩ : syracuseStep 816155 = 1224233) B1224233
theorem B914561 : Blo 239816 914561 := bstep (se 2 (by rfl) ⟨342960, by rfl⟩ : syracuseStep 914561 = 685921) B685921
theorem B324767 : Blo 239816 324767 := bstep (se 1 (by rfl) ⟨243575, by rfl⟩ : syracuseStep 324767 = 487151) B487151
theorem B10385243 : Blo 239816 10385243 := bstep (se 1 (by rfl) ⟨7788932, by rfl⟩ : syracuseStep 10385243 = 15577865) B15577865
theorem B785543 : Blo 239816 785543 := bstep (se 1 (by rfl) ⟨589157, by rfl⟩ : syracuseStep 785543 = 1178315) B1178315
theorem B819071 : Blo 239816 819071 := bstep (se 1 (by rfl) ⟨614303, by rfl⟩ : syracuseStep 819071 = 1228607) B1228607
theorem B1311005 : Blo 239816 1311005 := bstep (se 3 (by rfl) ⟨245813, by rfl⟩ : syracuseStep 1311005 = 491627) B491627
theorem B10060199 : Blo 239816 10060199 := bstep (se 1 (by rfl) ⟨7545149, by rfl⟩ : syracuseStep 10060199 = 15090299) B15090299
theorem B459407 : Blo 239816 459407 := bstep (se 1 (by rfl) ⟨344555, by rfl⟩ : syracuseStep 459407 = 689111) B689111
theorem B460667 : Blo 239816 460667 := bstep (se 1 (by rfl) ⟨345500, by rfl⟩ : syracuseStep 460667 = 691001) B691001
theorem B362975 : Blo 239816 362975 := bstep (se 1 (by rfl) ⟨272231, by rfl⟩ : syracuseStep 362975 = 544463) B544463
theorem B15667667 : Blo 239816 15667667 := bstep (se 1 (by rfl) ⟨11750750, by rfl⟩ : syracuseStep 15667667 = 23501501) B23501501
theorem B922535 : Blo 239816 922535 := bstep (se 1 (by rfl) ⟨691901, by rfl⟩ : syracuseStep 922535 = 1383803) B1383803
theorem B365705 : Blo 239816 365705 := bstep (se 2 (by rfl) ⟨137139, by rfl⟩ : syracuseStep 365705 = 274279) B274279
theorem B86087215 : Blo 239816 86087215 := bstep (se 1 (by rfl) ⟨64565411, by rfl⟩ : syracuseStep 86087215 = 129130823) B129130823
theorem B2070269 : Blo 239816 2070269 := bstep (se 3 (by rfl) ⟨388175, by rfl⟩ : syracuseStep 2070269 = 776351) B776351
theorem B6167339 : Blo 239816 6167339 := bstep (se 1 (by rfl) ⟨4625504, by rfl⟩ : syracuseStep 6167339 = 9251009) B9251009
theorem B6923495 : Blo 239816 6923495 := bstep (se 1 (by rfl) ⟨5192621, by rfl⟩ : syracuseStep 6923495 = 10385243) B10385243
theorem B240923 : Blo 239816 240923 := bstep (se 1 (by rfl) ⟨180692, by rfl⟩ : syracuseStep 240923 = 361385) B361385
theorem B241103 : Blo 239816 241103 := bstep (se 1 (by rfl) ⟨180827, by rfl⟩ : syracuseStep 241103 = 361655) B361655
theorem B241359 : Blo 239816 241359 := bstep (se 1 (by rfl) ⟨181019, by rfl⟩ : syracuseStep 241359 = 362039) B362039
theorem B241383 : Blo 239816 241383 := bstep (se 1 (by rfl) ⟨181037, by rfl⟩ : syracuseStep 241383 = 362075) B362075
theorem B406255 : Blo 239816 406255 := bstep (se 1 (by rfl) ⟨304691, by rfl⟩ : syracuseStep 406255 = 609383) B609383
theorem B215102249 : Blo 239816 215102249 := bstep (se 2 (by rfl) ⟨80663343, by rfl⟩ : syracuseStep 215102249 = 161326687) B161326687
theorem B1029257 : Blo 239816 1029257 := bstep (se 2 (by rfl) ⟨385971, by rfl⟩ : syracuseStep 1029257 = 771943) B771943
theorem B242927 : Blo 239816 242927 := bstep (se 1 (by rfl) ⟨182195, by rfl⟩ : syracuseStep 242927 = 364391) B364391
theorem B866045 : Blo 239816 866045 := bstep (se 3 (by rfl) ⟨162383, by rfl⟩ : syracuseStep 866045 = 324767) B324767
theorem B607115 : Blo 239816 607115 := bstep (se 1 (by rfl) ⟨455336, by rfl⟩ : syracuseStep 607115 = 910673) B910673
theorem B4637807 : Blo 239816 4637807 := bstep (se 1 (by rfl) ⟨3478355, by rfl⟩ : syracuseStep 4637807 = 6956711) B6956711
theorem B542555 : Blo 239816 542555 := bstep (se 1 (by rfl) ⟨406916, by rfl⟩ : syracuseStep 542555 = 813833) B813833
theorem B6343105 : Blo 239816 6343105 := bstep (se 2 (by rfl) ⟨2378664, by rfl⟩ : syracuseStep 6343105 = 4757329) B4757329
theorem B544103 : Blo 239816 544103 := bstep (se 1 (by rfl) ⟨408077, by rfl⟩ : syracuseStep 544103 = 816155) B816155
theorem B609707 : Blo 239816 609707 := bstep (se 1 (by rfl) ⟨457280, by rfl⟩ : syracuseStep 609707 = 914561) B914561
theorem B546047 : Blo 239816 546047 := bstep (se 1 (by rfl) ⟨409535, by rfl⟩ : syracuseStep 546047 = 819071) B819071
theorem B547271 : Blo 239816 547271 := bstep (se 1 (by rfl) ⟨410453, by rfl⟩ : syracuseStep 547271 = 820907) B820907
theorem B6413687 : Blo 239816 6413687 := bstep (se 1 (by rfl) ⟨4810265, by rfl⟩ : syracuseStep 6413687 = 9620531) B9620531
theorem B6381359 : Blo 239816 6381359 := bstep (se 1 (by rfl) ⟨4786019, by rfl⟩ : syracuseStep 6381359 = 9572039) B9572039
theorem B4219751 : Blo 239816 4219751 := bstep (se 1 (by rfl) ⟨3164813, by rfl⟩ : syracuseStep 4219751 = 6329627) B6329627
theorem B911357 : Blo 239816 911357 := bstep (se 3 (by rfl) ⟨170879, by rfl⟩ : syracuseStep 911357 = 341759) B341759
theorem B814697 : Blo 239816 814697 := bstep (se 2 (by rfl) ⟨305511, by rfl⟩ : syracuseStep 814697 = 611023) B611023
theorem B618745 : Blo 239816 618745 := bstep (se 2 (by rfl) ⟨232029, by rfl⟩ : syracuseStep 618745 = 464059) B464059
theorem B684713 : Blo 239816 684713 := bstep (se 2 (by rfl) ⟨256767, by rfl⟩ : syracuseStep 684713 = 513535) B513535
theorem B3470975 : Blo 239816 3470975 := bstep (se 1 (by rfl) ⟨2603231, by rfl⟩ : syracuseStep 3470975 = 5206463) B5206463
theorem B2094781 : Blo 239816 2094781 := bstep (se 3 (by rfl) ⟨392771, by rfl⟩ : syracuseStep 2094781 = 785543) B785543
theorem B361703 : Blo 239816 361703 := bstep (se 1 (by rfl) ⟨271277, by rfl⟩ : syracuseStep 361703 = 542555) B542555
theorem B362735 : Blo 239816 362735 := bstep (se 1 (by rfl) ⟨272051, by rfl⟩ : syracuseStep 362735 = 544103) B544103
theorem B8457473 : Blo 239816 8457473 := bstep (se 2 (by rfl) ⟨3171552, by rfl⟩ : syracuseStep 8457473 = 6343105) B6343105
theorem B364031 : Blo 239816 364031 := bstep (se 1 (by rfl) ⟨273023, by rfl⟩ : syracuseStep 364031 = 546047) B546047
theorem B1380179 : Blo 239816 1380179 := bstep (se 1 (by rfl) ⟨1035134, by rfl⟩ : syracuseStep 1380179 = 2070269) B2070269
theorem B364847 : Blo 239816 364847 := bstep (se 1 (by rfl) ⟨273635, by rfl⟩ : syracuseStep 364847 = 547271) B547271
theorem B824993 : Blo 239816 824993 := bstep (se 2 (by rfl) ⟨309372, by rfl⟩ : syracuseStep 824993 = 618745) B618745
theorem B2793041 : Blo 239816 2793041 := bstep (se 2 (by rfl) ⟨1047390, by rfl⟩ : syracuseStep 2793041 = 2094781) B2094781
theorem B143401499 : Blo 239816 143401499 := bstep (se 1 (by rfl) ⟨107551124, by rfl⟩ : syracuseStep 143401499 = 215102249) B215102249
theorem B306271 : Blo 239816 306271 := bstep (se 1 (by rfl) ⟨229703, by rfl⟩ : syracuseStep 306271 = 459407) B459407
theorem B404743 : Blo 239816 404743 := bstep (se 1 (by rfl) ⟨303557, by rfl⟩ : syracuseStep 404743 = 607115) B607115
theorem B3091871 : Blo 239816 3091871 := bstep (se 1 (by rfl) ⟨2318903, by rfl⟩ : syracuseStep 3091871 = 4637807) B4637807
theorem B241983 : Blo 239816 241983 := bstep (se 1 (by rfl) ⟨181487, by rfl⟩ : syracuseStep 241983 = 362975) B362975
theorem B406471 : Blo 239816 406471 := bstep (se 1 (by rfl) ⟨304853, by rfl⟩ : syracuseStep 406471 = 609707) B609707
theorem B243803 : Blo 239816 243803 := bstep (se 1 (by rfl) ⟨182852, by rfl⟩ : syracuseStep 243803 = 365705) B365705
theorem B180042709 : Blo 239816 180042709 := bstep (se 7 (by rfl) ⟨2109875, by rfl⟩ : syracuseStep 180042709 = 4219751) B4219751
theorem B4111559 : Blo 239816 4111559 := bstep (se 1 (by rfl) ⟨3083669, by rfl⟩ : syracuseStep 4111559 = 6167339) B6167339
theorem B4275791 : Blo 239816 4275791 := bstep (se 1 (by rfl) ⟨3206843, by rfl⟩ : syracuseStep 4275791 = 6413687) B6413687
theorem B1228445 : Blo 239816 1228445 := bstep (se 3 (by rfl) ⟨230333, by rfl⟩ : syracuseStep 1228445 = 460667) B460667
theorem B541673 : Blo 239816 541673 := bstep (se 2 (by rfl) ⟨203127, by rfl⟩ : syracuseStep 541673 = 406255) B406255
theorem B607571 : Blo 239816 607571 := bstep (se 1 (by rfl) ⟨455678, by rfl⟩ : syracuseStep 607571 = 911357) B911357
theorem B543131 : Blo 239816 543131 := bstep (se 1 (by rfl) ⟨407348, by rfl⟩ : syracuseStep 543131 = 814697) B814697
theorem B2313983 : Blo 239816 2313983 := bstep (se 1 (by rfl) ⟨1735487, by rfl⟩ : syracuseStep 2313983 = 3470975) B3470975
theorem B577363 : Blo 239816 577363 := bstep (se 1 (by rfl) ⟨433022, by rfl⟩ : syracuseStep 577363 = 866045) B866045
theorem B874003 : Blo 239816 874003 := bstep (se 1 (by rfl) ⟨655502, by rfl⟩ : syracuseStep 874003 = 1311005) B1311005
theorem B6706799 : Blo 239816 6706799 := bstep (se 1 (by rfl) ⟨5030099, by rfl⟩ : syracuseStep 6706799 = 10060199) B10060199
theorem B1825901 : Blo 239816 1825901 := bstep (se 3 (by rfl) ⟨342356, by rfl⟩ : syracuseStep 1825901 = 684713) B684713
theorem B10445111 : Blo 239816 10445111 := bstep (se 1 (by rfl) ⟨7833833, by rfl⟩ : syracuseStep 10445111 = 15667667) B15667667
theorem B615023 : Blo 239816 615023 := bstep (se 1 (by rfl) ⟨461267, by rfl⟩ : syracuseStep 615023 = 922535) B922535
theorem B4254239 : Blo 239816 4254239 := bstep (se 1 (by rfl) ⟨3190679, by rfl⟩ : syracuseStep 4254239 = 6381359) B6381359
theorem B4615663 : Blo 239816 4615663 := bstep (se 1 (by rfl) ⟨3461747, by rfl⟩ : syracuseStep 4615663 = 6923495) B6923495
theorem B114782953 : Blo 239816 114782953 := bstep (se 2 (by rfl) ⟨43043607, by rfl⟩ : syracuseStep 114782953 = 86087215) B86087215
theorem B686171 : Blo 239816 686171 := bstep (se 1 (by rfl) ⟨514628, by rfl⟩ : syracuseStep 686171 = 1029257) B1029257
theorem B361115 : Blo 239816 361115 := bstep (se 1 (by rfl) ⟨270836, by rfl⟩ : syracuseStep 361115 = 541673) B541673
theorem B362087 : Blo 239816 362087 := bstep (se 1 (by rfl) ⟨271565, by rfl⟩ : syracuseStep 362087 = 543131) B543131
theorem B1542655 : Blo 239816 1542655 := bstep (se 1 (by rfl) ⟨1156991, by rfl⟩ : syracuseStep 1542655 = 2313983) B2313983
theorem B920119 : Blo 239816 920119 := bstep (se 1 (by rfl) ⟨690089, by rfl⟩ : syracuseStep 920119 = 1380179) B1380179
theorem B1217267 : Blo 239816 1217267 := bstep (se 1 (by rfl) ⟨912950, by rfl⟩ : syracuseStep 1217267 = 1825901) B1825901
theorem B11344637 : Blo 239816 11344637 := bstep (se 3 (by rfl) ⟨2127119, by rfl⟩ : syracuseStep 11344637 = 4254239) B4254239
theorem B22553261 : Blo 239816 22553261 := bstep (se 3 (by rfl) ⟨4228736, by rfl⟩ : syracuseStep 22553261 = 8457473) B8457473
theorem B241135 : Blo 239816 241135 := bstep (se 1 (by rfl) ⟨180851, by rfl⟩ : syracuseStep 241135 = 361703) B361703
theorem B405047 : Blo 239816 405047 := bstep (se 1 (by rfl) ⟨303785, by rfl⟩ : syracuseStep 405047 = 607571) B607571
theorem B241823 : Blo 239816 241823 := bstep (se 1 (by rfl) ⟨181367, by rfl⟩ : syracuseStep 241823 = 362735) B362735
theorem B242687 : Blo 239816 242687 := bstep (se 1 (by rfl) ⟨182015, by rfl⟩ : syracuseStep 242687 = 364031) B364031
theorem B243231 : Blo 239816 243231 := bstep (se 1 (by rfl) ⟨182423, by rfl⟩ : syracuseStep 243231 = 364847) B364847
theorem B4471199 : Blo 239816 4471199 := bstep (se 1 (by rfl) ⟨3353399, by rfl⟩ : syracuseStep 4471199 = 6706799) B6706799
theorem B408361 : Blo 239816 408361 := bstep (se 2 (by rfl) ⟨153135, by rfl⟩ : syracuseStep 408361 = 306271) B306271
theorem B539657 : Blo 239816 539657 := bstep (se 2 (by rfl) ⟨202371, by rfl⟩ : syracuseStep 539657 = 404743) B404743
theorem B769817 : Blo 239816 769817 := bstep (se 2 (by rfl) ⟨288681, by rfl⟩ : syracuseStep 769817 = 577363) B577363
theorem B6963407 : Blo 239816 6963407 := bstep (se 1 (by rfl) ⟨5222555, by rfl⟩ : syracuseStep 6963407 = 10445111) B10445111
theorem B95600999 : Blo 239816 95600999 := bstep (se 1 (by rfl) ⟨71700749, by rfl⟩ : syracuseStep 95600999 = 143401499) B143401499
theorem B410015 : Blo 239816 410015 := bstep (se 1 (by rfl) ⟨307511, by rfl⟩ : syracuseStep 410015 = 615023) B615023
theorem B153043937 : Blo 239816 153043937 := bstep (se 2 (by rfl) ⟨57391476, by rfl⟩ : syracuseStep 153043937 = 114782953) B114782953
theorem B541961 : Blo 239816 541961 := bstep (se 2 (by rfl) ⟨203235, by rfl⟩ : syracuseStep 541961 = 406471) B406471
theorem B1165337 : Blo 239816 1165337 := bstep (se 2 (by rfl) ⟨437001, by rfl⟩ : syracuseStep 1165337 = 874003) B874003
theorem B2741039 : Blo 239816 2741039 := bstep (se 1 (by rfl) ⟨2055779, by rfl⟩ : syracuseStep 2741039 = 4111559) B4111559
theorem B549995 : Blo 239816 549995 := bstep (se 1 (by rfl) ⟨412496, by rfl⟩ : syracuseStep 549995 = 824993) B824993
theorem B6154217 : Blo 239816 6154217 := bstep (se 2 (by rfl) ⟨2307831, by rfl⟩ : syracuseStep 6154217 = 4615663) B4615663
theorem B1862027 : Blo 239816 1862027 := bstep (se 1 (by rfl) ⟨1396520, by rfl⟩ : syracuseStep 1862027 = 2793041) B2793041
theorem B1829789 : Blo 239816 1829789 := bstep (se 3 (by rfl) ⟨343085, by rfl⟩ : syracuseStep 1829789 = 686171) B686171
theorem B2061247 : Blo 239816 2061247 := bstep (se 1 (by rfl) ⟨1545935, by rfl⟩ : syracuseStep 2061247 = 3091871) B3091871
theorem B240056945 : Blo 239816 240056945 := bstep (se 2 (by rfl) ⟨90021354, by rfl⟩ : syracuseStep 240056945 = 180042709) B180042709
theorem B2850527 : Blo 239816 2850527 := bstep (se 1 (by rfl) ⟨2137895, by rfl⟩ : syracuseStep 2850527 = 4275791) B4275791
theorem B818963 : Blo 239816 818963 := bstep (se 1 (by rfl) ⟨614222, by rfl⟩ : syracuseStep 818963 = 1228445) B1228445
theorem B63733999 : Blo 239816 63733999 := bstep (se 1 (by rfl) ⟨47800499, by rfl⟩ : syracuseStep 63733999 = 95600999) B95600999
theorem B361307 : Blo 239816 361307 := bstep (se 1 (by rfl) ⟨270980, by rfl⟩ : syracuseStep 361307 = 541961) B541961
theorem B5866613 : Blo 239816 5866613 := bstep (se 5 (by rfl) ⟨274997, by rfl⟩ : syracuseStep 5866613 = 549995) B549995
theorem B4102811 : Blo 239816 4102811 := bstep (se 1 (by rfl) ⟨3077108, by rfl⟩ : syracuseStep 4102811 = 6154217) B6154217
theorem B1219859 : Blo 239816 1219859 := bstep (se 1 (by rfl) ⟨914894, by rfl⟩ : syracuseStep 1219859 = 1829789) B1829789
theorem B270031 : Blo 239816 270031 := bstep (se 1 (by rfl) ⟨202523, by rfl⟩ : syracuseStep 270031 = 405047) B405047
theorem B273343 : Blo 239816 273343 := bstep (se 1 (by rfl) ⟨205007, by rfl⟩ : syracuseStep 273343 = 410015) B410015
theorem B240743 : Blo 239816 240743 := bstep (se 1 (by rfl) ⟨180557, by rfl⟩ : syracuseStep 240743 = 361115) B361115
theorem B241391 : Blo 239816 241391 := bstep (se 1 (by rfl) ⟨181043, by rfl⟩ : syracuseStep 241391 = 362087) B362087
theorem B1226825 : Blo 239816 1226825 := bstep (se 2 (by rfl) ⟨460059, by rfl⟩ : syracuseStep 1226825 = 920119) B920119
theorem B544481 : Blo 239816 544481 := bstep (se 2 (by rfl) ⟨204180, by rfl⟩ : syracuseStep 544481 = 408361) B408361
theorem B545975 : Blo 239816 545975 := bstep (se 1 (by rfl) ⟨409481, by rfl⟩ : syracuseStep 545975 = 818963) B818963
theorem B513211 : Blo 239816 513211 := bstep (se 1 (by rfl) ⟨384908, by rfl⟩ : syracuseStep 513211 = 769817) B769817
theorem B4642271 : Blo 239816 4642271 := bstep (se 1 (by rfl) ⟨3481703, by rfl⟩ : syracuseStep 4642271 = 6963407) B6963407
theorem B102029291 : Blo 239816 102029291 := bstep (se 1 (by rfl) ⟨76521968, by rfl⟩ : syracuseStep 102029291 = 153043937) B153043937
theorem B776891 : Blo 239816 776891 := bstep (se 1 (by rfl) ⟨582668, by rfl⟩ : syracuseStep 776891 = 1165337) B1165337
theorem B811511 : Blo 239816 811511 := bstep (se 1 (by rfl) ⟨608633, by rfl⟩ : syracuseStep 811511 = 1217267) B1217267
theorem B1827359 : Blo 239816 1827359 := bstep (se 1 (by rfl) ⟨1370519, by rfl⟩ : syracuseStep 1827359 = 2741039) B2741039
theorem B2056873 : Blo 239816 2056873 := bstep (se 2 (by rfl) ⟨771327, by rfl⟩ : syracuseStep 2056873 = 1542655) B1542655
theorem B7563091 : Blo 239816 7563091 := bstep (se 1 (by rfl) ⟨5672318, by rfl⟩ : syracuseStep 7563091 = 11344637) B11344637
theorem B15035507 : Blo 239816 15035507 := bstep (se 1 (by rfl) ⟨11276630, by rfl⟩ : syracuseStep 15035507 = 22553261) B22553261
theorem B2748329 : Blo 239816 2748329 := bstep (se 2 (by rfl) ⟨1030623, by rfl⟩ : syracuseStep 2748329 = 2061247) B2061247
theorem B1241351 : Blo 239816 1241351 := bstep (se 1 (by rfl) ⟨931013, by rfl⟩ : syracuseStep 1241351 = 1862027) B1862027
theorem B2980799 : Blo 239816 2980799 := bstep (se 1 (by rfl) ⟨2235599, by rfl⟩ : syracuseStep 2980799 = 4471199) B4471199
theorem B160037963 : Blo 239816 160037963 := bstep (se 1 (by rfl) ⟨120028472, by rfl⟩ : syracuseStep 160037963 = 240056945) B240056945
theorem B359771 : Blo 239816 359771 := bstep (se 1 (by rfl) ⟨269828, by rfl⟩ : syracuseStep 359771 = 539657) B539657
theorem B1900351 : Blo 239816 1900351 := bstep (se 1 (by rfl) ⟨1425263, by rfl⟩ : syracuseStep 1900351 = 2850527) B2850527
theorem B362987 : Blo 239816 362987 := bstep (se 1 (by rfl) ⟨272240, by rfl⟩ : syracuseStep 362987 = 544481) B544481
theorem B363983 : Blo 239816 363983 := bstep (se 1 (by rfl) ⟨272987, by rfl⟩ : syracuseStep 363983 = 545975) B545975
theorem B364457 : Blo 239816 364457 := bstep (se 2 (by rfl) ⟨136671, by rfl⟩ : syracuseStep 364457 = 273343) B273343
theorem B1218239 : Blo 239816 1218239 := bstep (se 1 (by rfl) ⟨913679, by rfl⟩ : syracuseStep 1218239 = 1827359) B1827359
theorem B827567 : Blo 239816 827567 := bstep (se 1 (by rfl) ⟨620675, by rfl⟩ : syracuseStep 827567 = 1241351) B1241351
theorem B10135205 : Blo 239816 10135205 := bstep (se 4 (by rfl) ⟨950175, by rfl⟩ : syracuseStep 10135205 = 1900351) B1900351
theorem B239847 : Blo 239816 239847 := bstep (se 1 (by rfl) ⟨179885, by rfl⟩ : syracuseStep 239847 = 359771) B359771
theorem B84978665 : Blo 239816 84978665 := bstep (se 2 (by rfl) ⟨31866999, by rfl⟩ : syracuseStep 84978665 = 63733999) B63733999
theorem B240871 : Blo 239816 240871 := bstep (se 1 (by rfl) ⟨180653, by rfl⟩ : syracuseStep 240871 = 361307) B361307
theorem B3911075 : Blo 239816 3911075 := bstep (se 1 (by rfl) ⟨2933306, by rfl⟩ : syracuseStep 3911075 = 5866613) B5866613
theorem B3094847 : Blo 239816 3094847 := bstep (se 1 (by rfl) ⟨2321135, by rfl⟩ : syracuseStep 3094847 = 4642271) B4642271
theorem B2735207 : Blo 239816 2735207 := bstep (se 1 (by rfl) ⟨2051405, by rfl⟩ : syracuseStep 2735207 = 4102811) B4102811
theorem B541007 : Blo 239816 541007 := bstep (se 1 (by rfl) ⟨405755, by rfl⟩ : syracuseStep 541007 = 811511) B811511
theorem B1987199 : Blo 239816 1987199 := bstep (se 1 (by rfl) ⟨1490399, by rfl⟩ : syracuseStep 1987199 = 2980799) B2980799
theorem B2742497 : Blo 239816 2742497 := bstep (se 2 (by rfl) ⟨1028436, by rfl⟩ : syracuseStep 2742497 = 2056873) B2056873
theorem B10084121 : Blo 239816 10084121 := bstep (se 2 (by rfl) ⟨3781545, by rfl⟩ : syracuseStep 10084121 = 7563091) B7563091
theorem B68019527 : Blo 239816 68019527 := bstep (se 1 (by rfl) ⟨51014645, by rfl⟩ : syracuseStep 68019527 = 102029291) B102029291
theorem B517927 : Blo 239816 517927 := bstep (se 1 (by rfl) ⟨388445, by rfl⟩ : syracuseStep 517927 = 776891) B776891
theorem B813239 : Blo 239816 813239 := bstep (se 1 (by rfl) ⟨609929, by rfl⟩ : syracuseStep 813239 = 1219859) B1219859
theorem B684281 : Blo 239816 684281 := bstep (se 2 (by rfl) ⟨256605, by rfl⟩ : syracuseStep 684281 = 513211) B513211
theorem B10023671 : Blo 239816 10023671 := bstep (se 1 (by rfl) ⟨7517753, by rfl⟩ : syracuseStep 10023671 = 15035507) B15035507
theorem B1832219 : Blo 239816 1832219 := bstep (se 1 (by rfl) ⟨1374164, by rfl⟩ : syracuseStep 1832219 = 2748329) B2748329
theorem B817883 : Blo 239816 817883 := bstep (se 1 (by rfl) ⟨613412, by rfl⟩ : syracuseStep 817883 = 1226825) B1226825
theorem B106691975 : Blo 239816 106691975 := bstep (se 1 (by rfl) ⟨80018981, by rfl⟩ : syracuseStep 106691975 = 160037963) B160037963
theorem B360041 : Blo 239816 360041 := bstep (se 2 (by rfl) ⟨135015, by rfl⟩ : syracuseStep 360041 = 270031) B270031
theorem B360671 : Blo 239816 360671 := bstep (se 1 (by rfl) ⟨270503, by rfl⟩ : syracuseStep 360671 = 541007) B541007
theorem B690569 : Blo 239816 690569 := bstep (se 2 (by rfl) ⟨258963, by rfl⟩ : syracuseStep 690569 = 517927) B517927
theorem B6722747 : Blo 239816 6722747 := bstep (se 1 (by rfl) ⟨5042060, by rfl⟩ : syracuseStep 6722747 = 10084121) B10084121
theorem B6756803 : Blo 239816 6756803 := bstep (se 1 (by rfl) ⟨5067602, by rfl⟩ : syracuseStep 6756803 = 10135205) B10135205
theorem B1221479 : Blo 239816 1221479 := bstep (se 1 (by rfl) ⟨916109, by rfl⟩ : syracuseStep 1221479 = 1832219) B1832219
theorem B240027 : Blo 239816 240027 := bstep (se 1 (by rfl) ⟨180020, by rfl⟩ : syracuseStep 240027 = 360041) B360041
theorem B241991 : Blo 239816 241991 := bstep (se 1 (by rfl) ⟨181493, by rfl⟩ : syracuseStep 241991 = 362987) B362987
theorem B242655 : Blo 239816 242655 := bstep (se 1 (by rfl) ⟨181991, by rfl⟩ : syracuseStep 242655 = 363983) B363983
theorem B242971 : Blo 239816 242971 := bstep (se 1 (by rfl) ⟨182228, by rfl⟩ : syracuseStep 242971 = 364457) B364457
theorem B1324799 : Blo 239816 1324799 := bstep (se 1 (by rfl) ⟨993599, by rfl⟩ : syracuseStep 1324799 = 1987199) B1987199
theorem B542159 : Blo 239816 542159 := bstep (se 1 (by rfl) ⟨406619, by rfl⟩ : syracuseStep 542159 = 813239) B813239
theorem B2607383 : Blo 239816 2607383 := bstep (se 1 (by rfl) ⟨1955537, by rfl⟩ : syracuseStep 2607383 = 3911075) B3911075
theorem B545255 : Blo 239816 545255 := bstep (se 1 (by rfl) ⟨408941, by rfl⟩ : syracuseStep 545255 = 817883) B817883
theorem B1823471 : Blo 239816 1823471 := bstep (se 1 (by rfl) ⟨1367603, by rfl⟩ : syracuseStep 1823471 = 2735207) B2735207
theorem B71127983 : Blo 239816 71127983 := bstep (se 1 (by rfl) ⟨53345987, by rfl⟩ : syracuseStep 71127983 = 106691975) B106691975
theorem B812159 : Blo 239816 812159 := bstep (se 1 (by rfl) ⟨609119, by rfl⟩ : syracuseStep 812159 = 1218239) B1218239
theorem B1828331 : Blo 239816 1828331 := bstep (se 1 (by rfl) ⟨1371248, by rfl⟩ : syracuseStep 1828331 = 2742497) B2742497
theorem B551711 : Blo 239816 551711 := bstep (se 1 (by rfl) ⟨413783, by rfl⟩ : syracuseStep 551711 = 827567) B827567
theorem B45346351 : Blo 239816 45346351 := bstep (se 1 (by rfl) ⟨34009763, by rfl⟩ : syracuseStep 45346351 = 68019527) B68019527
theorem B56652443 : Blo 239816 56652443 := bstep (se 1 (by rfl) ⟨42489332, by rfl⟩ : syracuseStep 56652443 = 84978665) B84978665
theorem B456187 : Blo 239816 456187 := bstep (se 1 (by rfl) ⟨342140, by rfl⟩ : syracuseStep 456187 = 684281) B684281
theorem B6682447 : Blo 239816 6682447 := bstep (se 1 (by rfl) ⟨5011835, by rfl⟩ : syracuseStep 6682447 = 10023671) B10023671
theorem B2063231 : Blo 239816 2063231 := bstep (se 1 (by rfl) ⟨1547423, by rfl⟩ : syracuseStep 2063231 = 3094847) B3094847
theorem B361439 : Blo 239816 361439 := bstep (se 1 (by rfl) ⟨271079, by rfl⟩ : syracuseStep 361439 = 542159) B542159
theorem B1738255 : Blo 239816 1738255 := bstep (se 1 (by rfl) ⟨1303691, by rfl⟩ : syracuseStep 1738255 = 2607383) B2607383
theorem B460379 : Blo 239816 460379 := bstep (se 1 (by rfl) ⟨345284, by rfl⟩ : syracuseStep 460379 = 690569) B690569
theorem B363503 : Blo 239816 363503 := bstep (se 1 (by rfl) ⟨272627, by rfl⟩ : syracuseStep 363503 = 545255) B545255
theorem B1215647 : Blo 239816 1215647 := bstep (se 1 (by rfl) ⟨911735, by rfl⟩ : syracuseStep 1215647 = 1823471) B1823471
theorem B47418655 : Blo 239816 47418655 := bstep (se 1 (by rfl) ⟨35563991, by rfl⟩ : syracuseStep 47418655 = 71127983) B71127983
theorem B60461801 : Blo 239816 60461801 := bstep (se 2 (by rfl) ⟨22673175, by rfl⟩ : syracuseStep 60461801 = 45346351) B45346351
theorem B1218887 : Blo 239816 1218887 := bstep (se 1 (by rfl) ⟨914165, by rfl⟩ : syracuseStep 1218887 = 1828331) B1828331
theorem B240447 : Blo 239816 240447 := bstep (se 1 (by rfl) ⟨180335, by rfl⟩ : syracuseStep 240447 = 360671) B360671
theorem B4504535 : Blo 239816 4504535 := bstep (se 1 (by rfl) ⟨3378401, by rfl⟩ : syracuseStep 4504535 = 6756803) B6756803
theorem B541439 : Blo 239816 541439 := bstep (se 1 (by rfl) ⟨406079, by rfl⟩ : syracuseStep 541439 = 812159) B812159
theorem B608249 : Blo 239816 608249 := bstep (se 2 (by rfl) ⟨228093, by rfl⟩ : syracuseStep 608249 = 456187) B456187
theorem B37768295 : Blo 239816 37768295 := bstep (se 1 (by rfl) ⟨28326221, by rfl⟩ : syracuseStep 37768295 = 56652443) B56652443
theorem B4481831 : Blo 239816 4481831 := bstep (se 1 (by rfl) ⟨3361373, by rfl⟩ : syracuseStep 4481831 = 6722747) B6722747
theorem B814319 : Blo 239816 814319 := bstep (se 1 (by rfl) ⟨610739, by rfl⟩ : syracuseStep 814319 = 1221479) B1221479
theorem B1471229 : Blo 239816 1471229 := bstep (se 3 (by rfl) ⟨275855, by rfl⟩ : syracuseStep 1471229 = 551711) B551711
theorem B8909929 : Blo 239816 8909929 := bstep (se 2 (by rfl) ⟨3341223, by rfl⟩ : syracuseStep 8909929 = 6682447) B6682447
theorem B883199 : Blo 239816 883199 := bstep (se 1 (by rfl) ⟨662399, by rfl⟩ : syracuseStep 883199 = 1324799) B1324799
theorem B1375487 : Blo 239816 1375487 := bstep (se 1 (by rfl) ⟨1031615, by rfl⟩ : syracuseStep 1375487 = 2063231) B2063231
theorem B360959 : Blo 239816 360959 := bstep (se 1 (by rfl) ⟨270719, by rfl⟩ : syracuseStep 360959 = 541439) B541439
theorem B40307867 : Blo 239816 40307867 := bstep (se 1 (by rfl) ⟨30230900, by rfl⟩ : syracuseStep 40307867 = 60461801) B60461801
theorem B2987887 : Blo 239816 2987887 := bstep (se 1 (by rfl) ⟨2240915, by rfl⟩ : syracuseStep 2987887 = 4481831) B4481831
theorem B240959 : Blo 239816 240959 := bstep (se 1 (by rfl) ⟨180719, by rfl⟩ : syracuseStep 240959 = 361439) B361439
theorem B306919 : Blo 239816 306919 := bstep (se 1 (by rfl) ⟨230189, by rfl⟩ : syracuseStep 306919 = 460379) B460379
theorem B405499 : Blo 239816 405499 := bstep (se 1 (by rfl) ⟨304124, by rfl⟩ : syracuseStep 405499 = 608249) B608249
theorem B242335 : Blo 239816 242335 := bstep (se 1 (by rfl) ⟨181751, by rfl⟩ : syracuseStep 242335 = 363503) B363503
theorem B25178863 : Blo 239816 25178863 := bstep (se 1 (by rfl) ⟨18884147, by rfl⟩ : syracuseStep 25178863 = 37768295) B37768295
theorem B63224873 : Blo 239816 63224873 := bstep (se 2 (by rfl) ⟨23709327, by rfl⟩ : syracuseStep 63224873 = 47418655) B47418655
theorem B11879905 : Blo 239816 11879905 := bstep (se 2 (by rfl) ⟨4454964, by rfl⟩ : syracuseStep 11879905 = 8909929) B8909929
theorem B542879 : Blo 239816 542879 := bstep (se 1 (by rfl) ⟨407159, by rfl⟩ : syracuseStep 542879 = 814319) B814319
theorem B3003023 : Blo 239816 3003023 := bstep (se 1 (by rfl) ⟨2252267, by rfl⟩ : syracuseStep 3003023 = 4504535) B4504535
theorem B2317673 : Blo 239816 2317673 := bstep (se 2 (by rfl) ⟨869127, by rfl⟩ : syracuseStep 2317673 = 1738255) B1738255
theorem B810431 : Blo 239816 810431 := bstep (se 1 (by rfl) ⟨607823, by rfl⟩ : syracuseStep 810431 = 1215647) B1215647
theorem B812591 : Blo 239816 812591 := bstep (se 1 (by rfl) ⟨609443, by rfl⟩ : syracuseStep 812591 = 1218887) B1218887
theorem B980819 : Blo 239816 980819 := bstep (se 1 (by rfl) ⟨735614, by rfl⟩ : syracuseStep 980819 = 1471229) B1471229
theorem B588799 : Blo 239816 588799 := bstep (se 1 (by rfl) ⟨441599, by rfl⟩ : syracuseStep 588799 = 883199) B883199
theorem B916991 : Blo 239816 916991 := bstep (se 1 (by rfl) ⟨687743, by rfl⟩ : syracuseStep 916991 = 1375487) B1375487
theorem B361919 : Blo 239816 361919 := bstep (se 1 (by rfl) ⟨271439, by rfl⟩ : syracuseStep 361919 = 542879) B542879
theorem B26871911 : Blo 239816 26871911 := bstep (se 1 (by rfl) ⟨20153933, by rfl⟩ : syracuseStep 26871911 = 40307867) B40307867
theorem B2002015 : Blo 239816 2002015 := bstep (se 1 (by rfl) ⟨1501511, by rfl⟩ : syracuseStep 2002015 = 3003023) B3003023
theorem B42149915 : Blo 239816 42149915 := bstep (se 1 (by rfl) ⟨31612436, by rfl⟩ : syracuseStep 42149915 = 63224873) B63224873
theorem B240639 : Blo 239816 240639 := bstep (se 1 (by rfl) ⟨180479, by rfl⟩ : syracuseStep 240639 = 360959) B360959
theorem B15839873 : Blo 239816 15839873 := bstep (se 2 (by rfl) ⟨5939952, by rfl⟩ : syracuseStep 15839873 = 11879905) B11879905
theorem B540287 : Blo 239816 540287 := bstep (se 1 (by rfl) ⟨405215, by rfl⟩ : syracuseStep 540287 = 810431) B810431
theorem B409225 : Blo 239816 409225 := bstep (se 2 (by rfl) ⟨153459, by rfl⟩ : syracuseStep 409225 = 306919) B306919
theorem B540665 : Blo 239816 540665 := bstep (se 2 (by rfl) ⟨202749, by rfl⟩ : syracuseStep 540665 = 405499) B405499
theorem B33571817 : Blo 239816 33571817 := bstep (se 2 (by rfl) ⟨12589431, by rfl⟩ : syracuseStep 33571817 = 25178863) B25178863
theorem B541727 : Blo 239816 541727 := bstep (se 1 (by rfl) ⟨406295, by rfl⟩ : syracuseStep 541727 = 812591) B812591
theorem B3983849 : Blo 239816 3983849 := bstep (se 2 (by rfl) ⟨1493943, by rfl⟩ : syracuseStep 3983849 = 2987887) B2987887
theorem B6180461 : Blo 239816 6180461 := bstep (se 3 (by rfl) ⟨1158836, by rfl⟩ : syracuseStep 6180461 = 2317673) B2317673
theorem B611327 : Blo 239816 611327 := bstep (se 1 (by rfl) ⟨458495, by rfl⟩ : syracuseStep 611327 = 916991) B916991
theorem B653879 : Blo 239816 653879 := bstep (se 1 (by rfl) ⟨490409, by rfl⟩ : syracuseStep 653879 = 980819) B980819
theorem B785065 : Blo 239816 785065 := bstep (se 2 (by rfl) ⟨294399, by rfl⟩ : syracuseStep 785065 = 588799) B588799
theorem B22381211 : Blo 239816 22381211 := bstep (se 1 (by rfl) ⟨16785908, by rfl⟩ : syracuseStep 22381211 = 33571817) B33571817
theorem B361151 : Blo 239816 361151 := bstep (se 1 (by rfl) ⟨270863, by rfl⟩ : syracuseStep 361151 = 541727) B541727
theorem B2655899 : Blo 239816 2655899 := bstep (se 1 (by rfl) ⟨1991924, by rfl⟩ : syracuseStep 2655899 = 3983849) B3983849
theorem B1743677 : Blo 239816 1743677 := bstep (se 3 (by rfl) ⟨326939, by rfl⟩ : syracuseStep 1743677 = 653879) B653879
theorem B10559915 : Blo 239816 10559915 := bstep (se 1 (by rfl) ⟨7919936, by rfl⟩ : syracuseStep 10559915 = 15839873) B15839873
theorem B241279 : Blo 239816 241279 := bstep (se 1 (by rfl) ⟨180959, by rfl⟩ : syracuseStep 241279 = 361919) B361919
theorem B407551 : Blo 239816 407551 := bstep (se 1 (by rfl) ⟨305663, by rfl⟩ : syracuseStep 407551 = 611327) B611327
theorem B28099943 : Blo 239816 28099943 := bstep (se 1 (by rfl) ⟨21074957, by rfl⟩ : syracuseStep 28099943 = 42149915) B42149915
theorem B545633 : Blo 239816 545633 := bstep (se 2 (by rfl) ⟨204612, by rfl⟩ : syracuseStep 545633 = 409225) B409225
theorem B17914607 : Blo 239816 17914607 := bstep (se 1 (by rfl) ⟨13435955, by rfl⟩ : syracuseStep 17914607 = 26871911) B26871911
theorem B4120307 : Blo 239816 4120307 := bstep (se 1 (by rfl) ⟨3090230, by rfl⟩ : syracuseStep 4120307 = 6180461) B6180461
theorem B10677413 : Blo 239816 10677413 := bstep (se 4 (by rfl) ⟨1001007, by rfl⟩ : syracuseStep 10677413 = 2002015) B2002015
theorem B1046753 : Blo 239816 1046753 := bstep (se 2 (by rfl) ⟨392532, by rfl⟩ : syracuseStep 1046753 = 785065) B785065
theorem B360191 : Blo 239816 360191 := bstep (se 1 (by rfl) ⟨270143, by rfl⟩ : syracuseStep 360191 = 540287) B540287
theorem B360443 : Blo 239816 360443 := bstep (se 1 (by rfl) ⟨270332, by rfl⟩ : syracuseStep 360443 = 540665) B540665
theorem B1770599 : Blo 239816 1770599 := bstep (se 1 (by rfl) ⟨1327949, by rfl⟩ : syracuseStep 1770599 = 2655899) B2655899
theorem B363755 : Blo 239816 363755 := bstep (se 1 (by rfl) ⟨272816, by rfl⟩ : syracuseStep 363755 = 545633) B545633
theorem B7118275 : Blo 239816 7118275 := bstep (se 1 (by rfl) ⟨5338706, by rfl⟩ : syracuseStep 7118275 = 10677413) B10677413
theorem B697835 : Blo 239816 697835 := bstep (se 1 (by rfl) ⟨523376, by rfl⟩ : syracuseStep 697835 = 1046753) B1046753
theorem B240127 : Blo 239816 240127 := bstep (se 1 (by rfl) ⟨180095, by rfl⟩ : syracuseStep 240127 = 360191) B360191
theorem B240295 : Blo 239816 240295 := bstep (se 1 (by rfl) ⟨180221, by rfl⟩ : syracuseStep 240295 = 360443) B360443
theorem B14920807 : Blo 239816 14920807 := bstep (se 1 (by rfl) ⟨11190605, by rfl⟩ : syracuseStep 14920807 = 22381211) B22381211
theorem B240767 : Blo 239816 240767 := bstep (se 1 (by rfl) ⟨180575, by rfl⟩ : syracuseStep 240767 = 361151) B361151
theorem B11943071 : Blo 239816 11943071 := bstep (se 1 (by rfl) ⟨8957303, by rfl⟩ : syracuseStep 11943071 = 17914607) B17914607
theorem B1162451 : Blo 239816 1162451 := bstep (se 1 (by rfl) ⟨871838, by rfl⟩ : syracuseStep 1162451 = 1743677) B1743677
theorem B543401 : Blo 239816 543401 := bstep (se 2 (by rfl) ⟨203775, by rfl⟩ : syracuseStep 543401 = 407551) B407551
theorem B18733295 : Blo 239816 18733295 := bstep (se 1 (by rfl) ⟨14049971, by rfl⟩ : syracuseStep 18733295 = 28099943) B28099943
theorem B2746871 : Blo 239816 2746871 := bstep (se 1 (by rfl) ⟨2060153, by rfl⟩ : syracuseStep 2746871 = 4120307) B4120307
theorem B7039943 : Blo 239816 7039943 := bstep (se 1 (by rfl) ⟨5279957, by rfl⟩ : syracuseStep 7039943 = 10559915) B10559915
theorem B362267 : Blo 239816 362267 := bstep (se 1 (by rfl) ⟨271700, by rfl⟩ : syracuseStep 362267 = 543401) B543401
theorem B4721597 : Blo 239816 4721597 := bstep (se 3 (by rfl) ⟨885299, by rfl⟩ : syracuseStep 4721597 = 1770599) B1770599
theorem B19894409 : Blo 239816 19894409 := bstep (se 2 (by rfl) ⟨7460403, by rfl⟩ : syracuseStep 19894409 = 14920807) B14920807
theorem B4693295 : Blo 239816 4693295 := bstep (se 1 (by rfl) ⟨3519971, by rfl⟩ : syracuseStep 4693295 = 7039943) B7039943
theorem B242503 : Blo 239816 242503 := bstep (se 1 (by rfl) ⟨181877, by rfl⟩ : syracuseStep 242503 = 363755) B363755
theorem B49955453 : Blo 239816 49955453 := bstep (se 3 (by rfl) ⟨9366647, by rfl⟩ : syracuseStep 49955453 = 18733295) B18733295
theorem B3099869 : Blo 239816 3099869 := bstep (se 3 (by rfl) ⟨581225, by rfl⟩ : syracuseStep 3099869 = 1162451) B1162451
theorem B9491033 : Blo 239816 9491033 := bstep (se 2 (by rfl) ⟨3559137, by rfl⟩ : syracuseStep 9491033 = 7118275) B7118275
theorem B1860893 : Blo 239816 1860893 := bstep (se 3 (by rfl) ⟨348917, by rfl⟩ : syracuseStep 1860893 = 697835) B697835
theorem B1831247 : Blo 239816 1831247 := bstep (se 1 (by rfl) ⟨1373435, by rfl⟩ : syracuseStep 1831247 = 2746871) B2746871
theorem B7962047 : Blo 239816 7962047 := bstep (se 1 (by rfl) ⟨5971535, by rfl⟩ : syracuseStep 7962047 = 11943071) B11943071
theorem B3147731 : Blo 239816 3147731 := bstep (se 1 (by rfl) ⟨2360798, by rfl⟩ : syracuseStep 3147731 = 4721597) B4721597
theorem B2066579 : Blo 239816 2066579 := bstep (se 1 (by rfl) ⟨1549934, by rfl⟩ : syracuseStep 2066579 = 3099869) B3099869
theorem B1220831 : Blo 239816 1220831 := bstep (se 1 (by rfl) ⟨915623, by rfl⟩ : syracuseStep 1220831 = 1831247) B1831247
theorem B33303635 : Blo 239816 33303635 := bstep (se 1 (by rfl) ⟨24977726, by rfl⟩ : syracuseStep 33303635 = 49955453) B49955453
theorem B241511 : Blo 239816 241511 := bstep (se 1 (by rfl) ⟨181133, by rfl⟩ : syracuseStep 241511 = 362267) B362267
theorem B25309421 : Blo 239816 25309421 := bstep (se 3 (by rfl) ⟨4745516, by rfl⟩ : syracuseStep 25309421 = 9491033) B9491033
theorem B3128863 : Blo 239816 3128863 := bstep (se 1 (by rfl) ⟨2346647, by rfl⟩ : syracuseStep 3128863 = 4693295) B4693295
theorem B13262939 : Blo 239816 13262939 := bstep (se 1 (by rfl) ⟨9947204, by rfl⟩ : syracuseStep 13262939 = 19894409) B19894409
theorem B1240595 : Blo 239816 1240595 := bstep (se 1 (by rfl) ⟨930446, by rfl⟩ : syracuseStep 1240595 = 1860893) B1860893
theorem B5308031 : Blo 239816 5308031 := bstep (se 1 (by rfl) ⟨3981023, by rfl⟩ : syracuseStep 5308031 = 7962047) B7962047
theorem B2098487 : Blo 239816 2098487 := bstep (se 1 (by rfl) ⟨1573865, by rfl⟩ : syracuseStep 2098487 = 3147731) B3147731
theorem B1377719 : Blo 239816 1377719 := bstep (se 1 (by rfl) ⟨1033289, by rfl⟩ : syracuseStep 1377719 = 2066579) B2066579
theorem B827063 : Blo 239816 827063 := bstep (se 1 (by rfl) ⟨620297, by rfl⟩ : syracuseStep 827063 = 1240595) B1240595
theorem B4171817 : Blo 239816 4171817 := bstep (se 2 (by rfl) ⟨1564431, by rfl⟩ : syracuseStep 4171817 = 3128863) B3128863
theorem B22202423 : Blo 239816 22202423 := bstep (se 1 (by rfl) ⟨16651817, by rfl⟩ : syracuseStep 22202423 = 33303635) B33303635
theorem B8841959 : Blo 239816 8841959 := bstep (se 1 (by rfl) ⟨6631469, by rfl⟩ : syracuseStep 8841959 = 13262939) B13262939
theorem B813887 : Blo 239816 813887 := bstep (se 1 (by rfl) ⟨610415, by rfl⟩ : syracuseStep 813887 = 1220831) B1220831
theorem B16872947 : Blo 239816 16872947 := bstep (se 1 (by rfl) ⟨12654710, by rfl⟩ : syracuseStep 16872947 = 25309421) B25309421
theorem B3538687 : Blo 239816 3538687 := bstep (se 1 (by rfl) ⟨2654015, by rfl⟩ : syracuseStep 3538687 = 5308031) B5308031
theorem B918479 : Blo 239816 918479 := bstep (se 1 (by rfl) ⟨688859, by rfl⟩ : syracuseStep 918479 = 1377719) B1377719
theorem B11248631 : Blo 239816 11248631 := bstep (se 1 (by rfl) ⟨8436473, by rfl⟩ : syracuseStep 11248631 = 16872947) B16872947
theorem B542591 : Blo 239816 542591 := bstep (se 1 (by rfl) ⟨406943, by rfl⟩ : syracuseStep 542591 = 813887) B813887
theorem B14801615 : Blo 239816 14801615 := bstep (se 1 (by rfl) ⟨11101211, by rfl⟩ : syracuseStep 14801615 = 22202423) B22202423
theorem B5595965 : Blo 239816 5595965 := bstep (se 3 (by rfl) ⟨1049243, by rfl⟩ : syracuseStep 5595965 = 2098487) B2098487
theorem B551375 : Blo 239816 551375 := bstep (se 1 (by rfl) ⟨413531, by rfl⟩ : syracuseStep 551375 = 827063) B827063
theorem B2781211 : Blo 239816 2781211 := bstep (se 1 (by rfl) ⟨2085908, by rfl⟩ : syracuseStep 2781211 = 4171817) B4171817
theorem B5894639 : Blo 239816 5894639 := bstep (se 1 (by rfl) ⟨4420979, by rfl⟩ : syracuseStep 5894639 = 8841959) B8841959
theorem B4718249 : Blo 239816 4718249 := bstep (se 2 (by rfl) ⟨1769343, by rfl⟩ : syracuseStep 4718249 = 3538687) B3538687
theorem B361727 : Blo 239816 361727 := bstep (se 1 (by rfl) ⟨271295, by rfl⟩ : syracuseStep 361727 = 542591) B542591
theorem B9867743 : Blo 239816 9867743 := bstep (se 1 (by rfl) ⟨7400807, by rfl⟩ : syracuseStep 9867743 = 14801615) B14801615
theorem B3708281 : Blo 239816 3708281 := bstep (se 2 (by rfl) ⟨1390605, by rfl⟩ : syracuseStep 3708281 = 2781211) B2781211
theorem B367583 : Blo 239816 367583 := bstep (se 1 (by rfl) ⟨275687, by rfl⟩ : syracuseStep 367583 = 551375) B551375
theorem B612319 : Blo 239816 612319 := bstep (se 1 (by rfl) ⟨459239, by rfl⟩ : syracuseStep 612319 = 918479) B918479
theorem B3730643 : Blo 239816 3730643 := bstep (se 1 (by rfl) ⟨2797982, by rfl⟩ : syracuseStep 3730643 = 5595965) B5595965
theorem B7499087 : Blo 239816 7499087 := bstep (se 1 (by rfl) ⟨5624315, by rfl⟩ : syracuseStep 7499087 = 11248631) B11248631
theorem B3929759 : Blo 239816 3929759 := bstep (se 1 (by rfl) ⟨2947319, by rfl⟩ : syracuseStep 3929759 = 5894639) B5894639
theorem B3145499 : Blo 239816 3145499 := bstep (se 1 (by rfl) ⟨2359124, by rfl⟩ : syracuseStep 3145499 = 4718249) B4718249
theorem B241151 : Blo 239816 241151 := bstep (se 1 (by rfl) ⟨180863, by rfl⟩ : syracuseStep 241151 = 361727) B361727
theorem B4999391 : Blo 239816 4999391 := bstep (se 1 (by rfl) ⟨3749543, by rfl⟩ : syracuseStep 4999391 = 7499087) B7499087
theorem B6578495 : Blo 239816 6578495 := bstep (se 1 (by rfl) ⟨4933871, by rfl⟩ : syracuseStep 6578495 = 9867743) B9867743
theorem B9888749 : Blo 239816 9888749 := bstep (se 3 (by rfl) ⟨1854140, by rfl⟩ : syracuseStep 9888749 = 3708281) B3708281
theorem B2487095 : Blo 239816 2487095 := bstep (se 1 (by rfl) ⟨1865321, by rfl⟩ : syracuseStep 2487095 = 3730643) B3730643
theorem B980221 : Blo 239816 980221 := bstep (se 3 (by rfl) ⟨183791, by rfl⟩ : syracuseStep 980221 = 367583) B367583
theorem B816425 : Blo 239816 816425 := bstep (se 2 (by rfl) ⟨306159, by rfl⟩ : syracuseStep 816425 = 612319) B612319
theorem B2619839 : Blo 239816 2619839 := bstep (se 1 (by rfl) ⟨1964879, by rfl⟩ : syracuseStep 2619839 = 3929759) B3929759
theorem B2096999 : Blo 239816 2096999 := bstep (se 1 (by rfl) ⟨1572749, by rfl⟩ : syracuseStep 2096999 = 3145499) B3145499
theorem B6592499 : Blo 239816 6592499 := bstep (se 1 (by rfl) ⟨4944374, by rfl⟩ : syracuseStep 6592499 = 9888749) B9888749
theorem B1746559 : Blo 239816 1746559 := bstep (se 1 (by rfl) ⟨1309919, by rfl⟩ : syracuseStep 1746559 = 2619839) B2619839
theorem B1658063 : Blo 239816 1658063 := bstep (se 1 (by rfl) ⟨1243547, by rfl⟩ : syracuseStep 1658063 = 2487095) B2487095
theorem B544283 : Blo 239816 544283 := bstep (se 1 (by rfl) ⟨408212, by rfl⟩ : syracuseStep 544283 = 816425) B816425
theorem B1397999 : Blo 239816 1397999 := bstep (se 1 (by rfl) ⟨1048499, by rfl⟩ : syracuseStep 1397999 = 2096999) B2096999
theorem B3332927 : Blo 239816 3332927 := bstep (se 1 (by rfl) ⟨2499695, by rfl⟩ : syracuseStep 3332927 = 4999391) B4999391
theorem B4385663 : Blo 239816 4385663 := bstep (se 1 (by rfl) ⟨3289247, by rfl⟩ : syracuseStep 4385663 = 6578495) B6578495
theorem B1306961 : Blo 239816 1306961 := bstep (se 2 (by rfl) ⟨490110, by rfl⟩ : syracuseStep 1306961 = 980221) B980221
theorem B2328745 : Blo 239816 2328745 := bstep (se 2 (by rfl) ⟨873279, by rfl⟩ : syracuseStep 2328745 = 1746559) B1746559
theorem B362855 : Blo 239816 362855 := bstep (se 1 (by rfl) ⟨272141, by rfl⟩ : syracuseStep 362855 = 544283) B544283
theorem B4394999 : Blo 239816 4394999 := bstep (se 1 (by rfl) ⟨3296249, by rfl⟩ : syracuseStep 4394999 = 6592499) B6592499
theorem B2923775 : Blo 239816 2923775 := bstep (se 1 (by rfl) ⟨2192831, by rfl⟩ : syracuseStep 2923775 = 4385663) B4385663
theorem B931999 : Blo 239816 931999 := bstep (se 1 (by rfl) ⟨698999, by rfl⟩ : syracuseStep 931999 = 1397999) B1397999
theorem B871307 : Blo 239816 871307 := bstep (se 1 (by rfl) ⟨653480, by rfl⟩ : syracuseStep 871307 = 1306961) B1306961
theorem B1105375 : Blo 239816 1105375 := bstep (se 1 (by rfl) ⟨829031, by rfl⟩ : syracuseStep 1105375 = 1658063) B1658063
theorem B2221951 : Blo 239816 2221951 := bstep (se 1 (by rfl) ⟨1666463, by rfl⟩ : syracuseStep 2221951 = 3332927) B3332927
theorem B241903 : Blo 239816 241903 := bstep (se 1 (by rfl) ⟨181427, by rfl⟩ : syracuseStep 241903 = 362855) B362855
theorem B2962601 : Blo 239816 2962601 := bstep (se 2 (by rfl) ⟨1110975, by rfl⟩ : syracuseStep 2962601 = 2221951) B2221951
theorem B1949183 : Blo 239816 1949183 := bstep (se 1 (by rfl) ⟨1461887, by rfl⟩ : syracuseStep 1949183 = 2923775) B2923775
theorem B11719997 : Blo 239816 11719997 := bstep (se 3 (by rfl) ⟨2197499, by rfl⟩ : syracuseStep 11719997 = 4394999) B4394999
theorem B580871 : Blo 239816 580871 := bstep (se 1 (by rfl) ⟨435653, by rfl⟩ : syracuseStep 580871 = 871307) B871307
theorem B3104993 : Blo 239816 3104993 := bstep (se 2 (by rfl) ⟨1164372, by rfl⟩ : syracuseStep 3104993 = 2328745) B2328745
theorem B1242665 : Blo 239816 1242665 := bstep (se 2 (by rfl) ⟨465999, by rfl⟩ : syracuseStep 1242665 = 931999) B931999
theorem B1473833 : Blo 239816 1473833 := bstep (se 2 (by rfl) ⟨552687, by rfl⟩ : syracuseStep 1473833 = 1105375) B1105375
theorem B2069995 : Blo 239816 2069995 := bstep (se 1 (by rfl) ⟨1552496, by rfl⟩ : syracuseStep 2069995 = 3104993) B3104993
theorem B1548989 : Blo 239816 1548989 := bstep (se 3 (by rfl) ⟨290435, by rfl⟩ : syracuseStep 1548989 = 580871) B580871
theorem B1975067 : Blo 239816 1975067 := bstep (se 1 (by rfl) ⟨1481300, by rfl⟩ : syracuseStep 1975067 = 2962601) B2962601
theorem B828443 : Blo 239816 828443 := bstep (se 1 (by rfl) ⟨621332, by rfl⟩ : syracuseStep 828443 = 1242665) B1242665
theorem B7813331 : Blo 239816 7813331 := bstep (se 1 (by rfl) ⟨5859998, by rfl⟩ : syracuseStep 7813331 = 11719997) B11719997
theorem B1299455 : Blo 239816 1299455 := bstep (se 1 (by rfl) ⟨974591, by rfl⟩ : syracuseStep 1299455 = 1949183) B1949183
theorem B3930221 : Blo 239816 3930221 := bstep (se 3 (by rfl) ⟨736916, by rfl⟩ : syracuseStep 3930221 = 1473833) B1473833
theorem B1316711 : Blo 239816 1316711 := bstep (se 1 (by rfl) ⟨987533, by rfl⟩ : syracuseStep 1316711 = 1975067) B1975067
theorem B2759993 : Blo 239816 2759993 := bstep (se 2 (by rfl) ⟨1034997, by rfl⟩ : syracuseStep 2759993 = 2069995) B2069995
theorem B866303 : Blo 239816 866303 := bstep (se 1 (by rfl) ⟨649727, by rfl⟩ : syracuseStep 866303 = 1299455) B1299455
theorem B1032659 : Blo 239816 1032659 := bstep (se 1 (by rfl) ⟨774494, by rfl⟩ : syracuseStep 1032659 = 1548989) B1548989
theorem B552295 : Blo 239816 552295 := bstep (se 1 (by rfl) ⟨414221, by rfl⟩ : syracuseStep 552295 = 828443) B828443
theorem B2620147 : Blo 239816 2620147 := bstep (se 1 (by rfl) ⟨1965110, by rfl⟩ : syracuseStep 2620147 = 3930221) B3930221
theorem B5208887 : Blo 239816 5208887 := bstep (se 1 (by rfl) ⟨3906665, by rfl⟩ : syracuseStep 5208887 = 7813331) B7813331
theorem B688439 : Blo 239816 688439 := bstep (se 1 (by rfl) ⟨516329, by rfl⟩ : syracuseStep 688439 = 1032659) B1032659
theorem B1839995 : Blo 239816 1839995 := bstep (se 1 (by rfl) ⟨1379996, by rfl⟩ : syracuseStep 1839995 = 2759993) B2759993
theorem B736393 : Blo 239816 736393 := bstep (se 2 (by rfl) ⟨276147, by rfl⟩ : syracuseStep 736393 = 552295) B552295
theorem B3493529 : Blo 239816 3493529 := bstep (se 2 (by rfl) ⟨1310073, by rfl⟩ : syracuseStep 3493529 = 2620147) B2620147
theorem B577535 : Blo 239816 577535 := bstep (se 1 (by rfl) ⟨433151, by rfl⟩ : syracuseStep 577535 = 866303) B866303
theorem B877807 : Blo 239816 877807 := bstep (se 1 (by rfl) ⟨658355, by rfl⟩ : syracuseStep 877807 = 1316711) B1316711
theorem B3472591 : Blo 239816 3472591 := bstep (se 1 (by rfl) ⟨2604443, by rfl⟩ : syracuseStep 3472591 = 5208887) B5208887
theorem B458959 : Blo 239816 458959 := bstep (se 1 (by rfl) ⟨344219, by rfl⟩ : syracuseStep 458959 = 688439) B688439
theorem B2329019 : Blo 239816 2329019 := bstep (se 1 (by rfl) ⟨1746764, by rfl⟩ : syracuseStep 2329019 = 3493529) B3493529
theorem B4630121 : Blo 239816 4630121 := bstep (se 2 (by rfl) ⟨1736295, by rfl⟩ : syracuseStep 4630121 = 3472591) B3472591
theorem B1226663 : Blo 239816 1226663 := bstep (se 1 (by rfl) ⟨919997, by rfl⟩ : syracuseStep 1226663 = 1839995) B1839995
theorem B4681637 : Blo 239816 4681637 := bstep (se 4 (by rfl) ⟨438903, by rfl⟩ : syracuseStep 4681637 = 877807) B877807
theorem B981857 : Blo 239816 981857 := bstep (se 2 (by rfl) ⟨368196, by rfl⟩ : syracuseStep 981857 = 736393) B736393
theorem B1540093 : Blo 239816 1540093 := bstep (se 3 (by rfl) ⟨288767, by rfl⟩ : syracuseStep 1540093 = 577535) B577535
theorem B3086747 : Blo 239816 3086747 := bstep (se 1 (by rfl) ⟨2315060, by rfl⟩ : syracuseStep 3086747 = 4630121) B4630121
theorem B3121091 : Blo 239816 3121091 := bstep (se 1 (by rfl) ⟨2340818, by rfl⟩ : syracuseStep 3121091 = 4681637) B4681637
theorem B1552679 : Blo 239816 1552679 := bstep (se 1 (by rfl) ⟨1164509, by rfl⟩ : syracuseStep 1552679 = 2329019) B2329019
theorem B2053457 : Blo 239816 2053457 := bstep (se 2 (by rfl) ⟨770046, by rfl⟩ : syracuseStep 2053457 = 1540093) B1540093
theorem B611945 : Blo 239816 611945 := bstep (se 2 (by rfl) ⟨229479, by rfl⟩ : syracuseStep 611945 = 458959) B458959
theorem B817775 : Blo 239816 817775 := bstep (se 1 (by rfl) ⟨613331, by rfl⟩ : syracuseStep 817775 = 1226663) B1226663
theorem B654571 : Blo 239816 654571 := bstep (se 1 (by rfl) ⟨490928, by rfl⟩ : syracuseStep 654571 = 981857) B981857
theorem B407963 : Blo 239816 407963 := bstep (se 1 (by rfl) ⟨305972, by rfl⟩ : syracuseStep 407963 = 611945) B611945
theorem B2080727 : Blo 239816 2080727 := bstep (se 1 (by rfl) ⟨1560545, by rfl⟩ : syracuseStep 2080727 = 3121091) B3121091
theorem B3491045 : Blo 239816 3491045 := bstep (se 4 (by rfl) ⟨327285, by rfl⟩ : syracuseStep 3491045 = 654571) B654571
theorem B1035119 : Blo 239816 1035119 := bstep (se 1 (by rfl) ⟨776339, by rfl⟩ : syracuseStep 1035119 = 1552679) B1552679
theorem B545183 : Blo 239816 545183 := bstep (se 1 (by rfl) ⟨408887, by rfl⟩ : syracuseStep 545183 = 817775) B817775
theorem B1368971 : Blo 239816 1368971 := bstep (se 1 (by rfl) ⟨1026728, by rfl⟩ : syracuseStep 1368971 = 2053457) B2053457
theorem B2057831 : Blo 239816 2057831 := bstep (se 1 (by rfl) ⟨1543373, by rfl⟩ : syracuseStep 2057831 = 3086747) B3086747
theorem B2327363 : Blo 239816 2327363 := bstep (se 1 (by rfl) ⟨1745522, by rfl⟩ : syracuseStep 2327363 = 3491045) B3491045
theorem B690079 : Blo 239816 690079 := bstep (se 1 (by rfl) ⟨517559, by rfl⟩ : syracuseStep 690079 = 1035119) B1035119
theorem B363455 : Blo 239816 363455 := bstep (se 1 (by rfl) ⟨272591, by rfl⟩ : syracuseStep 363455 = 545183) B545183
theorem B271975 : Blo 239816 271975 := bstep (se 1 (by rfl) ⟨203981, by rfl⟩ : syracuseStep 271975 = 407963) B407963
theorem B1387151 : Blo 239816 1387151 := bstep (se 1 (by rfl) ⟨1040363, by rfl⟩ : syracuseStep 1387151 = 2080727) B2080727
theorem B912647 : Blo 239816 912647 := bstep (se 1 (by rfl) ⟨684485, by rfl⟩ : syracuseStep 912647 = 1368971) B1368971
theorem B1371887 : Blo 239816 1371887 := bstep (se 1 (by rfl) ⟨1028915, by rfl⟩ : syracuseStep 1371887 = 2057831) B2057831
theorem B362633 : Blo 239816 362633 := bstep (se 2 (by rfl) ⟨135987, by rfl⟩ : syracuseStep 362633 = 271975) B271975
theorem B920105 : Blo 239816 920105 := bstep (se 2 (by rfl) ⟨345039, by rfl⟩ : syracuseStep 920105 = 690079) B690079
theorem B924767 : Blo 239816 924767 := bstep (se 1 (by rfl) ⟨693575, by rfl⟩ : syracuseStep 924767 = 1387151) B1387151
theorem B1551575 : Blo 239816 1551575 := bstep (se 1 (by rfl) ⟨1163681, by rfl⟩ : syracuseStep 1551575 = 2327363) B2327363
theorem B242303 : Blo 239816 242303 := bstep (se 1 (by rfl) ⟨181727, by rfl⟩ : syracuseStep 242303 = 363455) B363455
theorem B608431 : Blo 239816 608431 := bstep (se 1 (by rfl) ⟨456323, by rfl⟩ : syracuseStep 608431 = 912647) B912647
theorem B914591 : Blo 239816 914591 := bstep (se 1 (by rfl) ⟨685943, by rfl⟩ : syracuseStep 914591 = 1371887) B1371887
theorem B241755 : Blo 239816 241755 := bstep (se 1 (by rfl) ⟨181316, by rfl⟩ : syracuseStep 241755 = 362633) B362633
theorem B1034383 : Blo 239816 1034383 := bstep (se 1 (by rfl) ⟨775787, by rfl⟩ : syracuseStep 1034383 = 1551575) B1551575
theorem B609727 : Blo 239816 609727 := bstep (se 1 (by rfl) ⟨457295, by rfl⟩ : syracuseStep 609727 = 914591) B914591
theorem B613403 : Blo 239816 613403 := bstep (se 1 (by rfl) ⟨460052, by rfl⟩ : syracuseStep 613403 = 920105) B920105
theorem B811241 : Blo 239816 811241 := bstep (se 2 (by rfl) ⟨304215, by rfl⟩ : syracuseStep 811241 = 608431) B608431
theorem B616511 : Blo 239816 616511 := bstep (se 1 (by rfl) ⟨462383, by rfl⟩ : syracuseStep 616511 = 924767) B924767
theorem B1379177 : Blo 239816 1379177 := bstep (se 2 (by rfl) ⟨517191, by rfl⟩ : syracuseStep 1379177 = 1034383) B1034383
theorem B408935 : Blo 239816 408935 := bstep (se 1 (by rfl) ⟨306701, by rfl⟩ : syracuseStep 408935 = 613403) B613403
theorem B540827 : Blo 239816 540827 := bstep (se 1 (by rfl) ⟨405620, by rfl⟩ : syracuseStep 540827 = 811241) B811241
theorem B411007 : Blo 239816 411007 := bstep (se 1 (by rfl) ⟨308255, by rfl⟩ : syracuseStep 411007 = 616511) B616511
theorem B812969 : Blo 239816 812969 := bstep (se 2 (by rfl) ⟨304863, by rfl⟩ : syracuseStep 812969 = 609727) B609727
theorem B360551 : Blo 239816 360551 := bstep (se 1 (by rfl) ⟨270413, by rfl⟩ : syracuseStep 360551 = 540827) B540827
theorem B919451 : Blo 239816 919451 := bstep (se 1 (by rfl) ⟨689588, by rfl⟩ : syracuseStep 919451 = 1379177) B1379177
theorem B272623 : Blo 239816 272623 := bstep (se 1 (by rfl) ⟨204467, by rfl⟩ : syracuseStep 272623 = 408935) B408935
theorem B541979 : Blo 239816 541979 := bstep (se 1 (by rfl) ⟨406484, by rfl⟩ : syracuseStep 541979 = 812969) B812969
theorem B548009 : Blo 239816 548009 := bstep (se 2 (by rfl) ⟨205503, by rfl⟩ : syracuseStep 548009 = 411007) B411007
theorem B361319 : Blo 239816 361319 := bstep (se 1 (by rfl) ⟨270989, by rfl⟩ : syracuseStep 361319 = 541979) B541979
theorem B363497 : Blo 239816 363497 := bstep (se 2 (by rfl) ⟨136311, by rfl⟩ : syracuseStep 363497 = 272623) B272623
theorem B365339 : Blo 239816 365339 := bstep (se 1 (by rfl) ⟨274004, by rfl⟩ : syracuseStep 365339 = 548009) B548009
theorem B240367 : Blo 239816 240367 := bstep (se 1 (by rfl) ⟨180275, by rfl⟩ : syracuseStep 240367 = 360551) B360551
theorem B612967 : Blo 239816 612967 := bstep (se 1 (by rfl) ⟨459725, by rfl⟩ : syracuseStep 612967 = 919451) B919451
theorem B240879 : Blo 239816 240879 := bstep (se 1 (by rfl) ⟨180659, by rfl⟩ : syracuseStep 240879 = 361319) B361319
theorem B242331 : Blo 239816 242331 := bstep (se 1 (by rfl) ⟨181748, by rfl⟩ : syracuseStep 242331 = 363497) B363497
theorem B243559 : Blo 239816 243559 := bstep (se 1 (by rfl) ⟨182669, by rfl⟩ : syracuseStep 243559 = 365339) B365339
theorem B817289 : Blo 239816 817289 := bstep (se 2 (by rfl) ⟨306483, by rfl⟩ : syracuseStep 817289 = 612967) B612967
theorem B544859 : Blo 239816 544859 := bstep (se 1 (by rfl) ⟨408644, by rfl⟩ : syracuseStep 544859 = 817289) B817289
theorem B363239 : Blo 239816 363239 := bstep (se 1 (by rfl) ⟨272429, by rfl⟩ : syracuseStep 363239 = 544859) B544859
theorem B242159 : Blo 239816 242159 := bstep (se 1 (by rfl) ⟨181619, by rfl⟩ : syracuseStep 242159 = 363239) B363239

theorem C0 (j : ℕ) (h1 : 59954 ≤ j) (h2 : j ≤ 60653) : Blo 239816 (4 * j + 3) := by
  interval_cases j
  · exact B239819
  · exact B239823
  · exact B239827
  · exact B239831
  · exact B239835
  · exact B239839
  · exact B239843
  · exact B239847
  · exact B239851
  · exact B239855
  · exact B239859
  · exact B239863
  · exact B239867
  · exact B239871
  · exact B239875
  · exact B239879
  · exact B239883
  · exact B239887
  · exact B239891
  · exact B239895
  · exact B239899
  · exact B239903
  · exact B239907
  · exact B239911
  · exact B239915
  · exact B239919
  · exact B239923
  · exact B239927
  · exact B239931
  · exact B239935
  · exact B239939
  · exact B239943
  · exact B239947
  · exact B239951
  · exact B239955
  · exact B239959
  · exact B239963
  · exact B239967
  · exact B239971
  · exact B239975
  · exact B239979
  · exact B239983
  · exact B239987
  · exact B239991
  · exact B239995
  · exact B239999
  · exact B240003
  · exact B240007
  · exact B240011
  · exact B240015
  · exact B240019
  · exact B240023
  · exact B240027
  · exact B240031
  · exact B240035
  · exact B240039
  · exact B240043
  · exact B240047
  · exact B240051
  · exact B240055
  · exact B240059
  · exact B240063
  · exact B240067
  · exact B240071
  · exact B240075
  · exact B240079
  · exact B240083
  · exact B240087
  · exact B240091
  · exact B240095
  · exact B240099
  · exact B240103
  · exact B240107
  · exact B240111
  · exact B240115
  · exact B240119
  · exact B240123
  · exact B240127
  · exact B240131
  · exact B240135
  · exact B240139
  · exact B240143
  · exact B240147
  · exact B240151
  · exact B240155
  · exact B240159
  · exact B240163
  · exact B240167
  · exact B240171
  · exact B240175
  · exact B240179
  · exact B240183
  · exact B240187
  · exact B240191
  · exact B240195
  · exact B240199
  · exact B240203
  · exact B240207
  · exact B240211
  · exact B240215
  · exact B240219
  · exact B240223
  · exact B240227
  · exact B240231
  · exact B240235
  · exact B240239
  · exact B240243
  · exact B240247
  · exact B240251
  · exact B240255
  · exact B240259
  · exact B240263
  · exact B240267
  · exact B240271
  · exact B240275
  · exact B240279
  · exact B240283
  · exact B240287
  · exact B240291
  · exact B240295
  · exact B240299
  · exact B240303
  · exact B240307
  · exact B240311
  · exact B240315
  · exact B240319
  · exact B240323
  · exact B240327
  · exact B240331
  · exact B240335
  · exact B240339
  · exact B240343
  · exact B240347
  · exact B240351
  · exact B240355
  · exact B240359
  · exact B240363
  · exact B240367
  · exact B240371
  · exact B240375
  · exact B240379
  · exact B240383
  · exact B240387
  · exact B240391
  · exact B240395
  · exact B240399
  · exact B240403
  · exact B240407
  · exact B240411
  · exact B240415
  · exact B240419
  · exact B240423
  · exact B240427
  · exact B240431
  · exact B240435
  · exact B240439
  · exact B240443
  · exact B240447
  · exact B240451
  · exact B240455
  · exact B240459
  · exact B240463
  · exact B240467
  · exact B240471
  · exact B240475
  · exact B240479
  · exact B240483
  · exact B240487
  · exact B240491
  · exact B240495
  · exact B240499
  · exact B240503
  · exact B240507
  · exact B240511
  · exact B240515
  · exact B240519
  · exact B240523
  · exact B240527
  · exact B240531
  · exact B240535
  · exact B240539
  · exact B240543
  · exact B240547
  · exact B240551
  · exact B240555
  · exact B240559
  · exact B240563
  · exact B240567
  · exact B240571
  · exact B240575
  · exact B240579
  · exact B240583
  · exact B240587
  · exact B240591
  · exact B240595
  · exact B240599
  · exact B240603
  · exact B240607
  · exact B240611
  · exact B240615
  · exact B240619
  · exact B240623
  · exact B240627
  · exact B240631
  · exact B240635
  · exact B240639
  · exact B240643
  · exact B240647
  · exact B240651
  · exact B240655
  · exact B240659
  · exact B240663
  · exact B240667
  · exact B240671
  · exact B240675
  · exact B240679
  · exact B240683
  · exact B240687
  · exact B240691
  · exact B240695
  · exact B240699
  · exact B240703
  · exact B240707
  · exact B240711
  · exact B240715
  · exact B240719
  · exact B240723
  · exact B240727
  · exact B240731
  · exact B240735
  · exact B240739
  · exact B240743
  · exact B240747
  · exact B240751
  · exact B240755
  · exact B240759
  · exact B240763
  · exact B240767
  · exact B240771
  · exact B240775
  · exact B240779
  · exact B240783
  · exact B240787
  · exact B240791
  · exact B240795
  · exact B240799
  · exact B240803
  · exact B240807
  · exact B240811
  · exact B240815
  · exact B240819
  · exact B240823
  · exact B240827
  · exact B240831
  · exact B240835
  · exact B240839
  · exact B240843
  · exact B240847
  · exact B240851
  · exact B240855
  · exact B240859
  · exact B240863
  · exact B240867
  · exact B240871
  · exact B240875
  · exact B240879
  · exact B240883
  · exact B240887
  · exact B240891
  · exact B240895
  · exact B240899
  · exact B240903
  · exact B240907
  · exact B240911
  · exact B240915
  · exact B240919
  · exact B240923
  · exact B240927
  · exact B240931
  · exact B240935
  · exact B240939
  · exact B240943
  · exact B240947
  · exact B240951
  · exact B240955
  · exact B240959
  · exact B240963
  · exact B240967
  · exact B240971
  · exact B240975
  · exact B240979
  · exact B240983
  · exact B240987
  · exact B240991
  · exact B240995
  · exact B240999
  · exact B241003
  · exact B241007
  · exact B241011
  · exact B241015
  · exact B241019
  · exact B241023
  · exact B241027
  · exact B241031
  · exact B241035
  · exact B241039
  · exact B241043
  · exact B241047
  · exact B241051
  · exact B241055
  · exact B241059
  · exact B241063
  · exact B241067
  · exact B241071
  · exact B241075
  · exact B241079
  · exact B241083
  · exact B241087
  · exact B241091
  · exact B241095
  · exact B241099
  · exact B241103
  · exact B241107
  · exact B241111
  · exact B241115
  · exact B241119
  · exact B241123
  · exact B241127
  · exact B241131
  · exact B241135
  · exact B241139
  · exact B241143
  · exact B241147
  · exact B241151
  · exact B241155
  · exact B241159
  · exact B241163
  · exact B241167
  · exact B241171
  · exact B241175
  · exact B241179
  · exact B241183
  · exact B241187
  · exact B241191
  · exact B241195
  · exact B241199
  · exact B241203
  · exact B241207
  · exact B241211
  · exact B241215
  · exact B241219
  · exact B241223
  · exact B241227
  · exact B241231
  · exact B241235
  · exact B241239
  · exact B241243
  · exact B241247
  · exact B241251
  · exact B241255
  · exact B241259
  · exact B241263
  · exact B241267
  · exact B241271
  · exact B241275
  · exact B241279
  · exact B241283
  · exact B241287
  · exact B241291
  · exact B241295
  · exact B241299
  · exact B241303
  · exact B241307
  · exact B241311
  · exact B241315
  · exact B241319
  · exact B241323
  · exact B241327
  · exact B241331
  · exact B241335
  · exact B241339
  · exact B241343
  · exact B241347
  · exact B241351
  · exact B241355
  · exact B241359
  · exact B241363
  · exact B241367
  · exact B241371
  · exact B241375
  · exact B241379
  · exact B241383
  · exact B241387
  · exact B241391
  · exact B241395
  · exact B241399
  · exact B241403
  · exact B241407
  · exact B241411
  · exact B241415
  · exact B241419
  · exact B241423
  · exact B241427
  · exact B241431
  · exact B241435
  · exact B241439
  · exact B241443
  · exact B241447
  · exact B241451
  · exact B241455
  · exact B241459
  · exact B241463
  · exact B241467
  · exact B241471
  · exact B241475
  · exact B241479
  · exact B241483
  · exact B241487
  · exact B241491
  · exact B241495
  · exact B241499
  · exact B241503
  · exact B241507
  · exact B241511
  · exact B241515
  · exact B241519
  · exact B241523
  · exact B241527
  · exact B241531
  · exact B241535
  · exact B241539
  · exact B241543
  · exact B241547
  · exact B241551
  · exact B241555
  · exact B241559
  · exact B241563
  · exact B241567
  · exact B241571
  · exact B241575
  · exact B241579
  · exact B241583
  · exact B241587
  · exact B241591
  · exact B241595
  · exact B241599
  · exact B241603
  · exact B241607
  · exact B241611
  · exact B241615
  · exact B241619
  · exact B241623
  · exact B241627
  · exact B241631
  · exact B241635
  · exact B241639
  · exact B241643
  · exact B241647
  · exact B241651
  · exact B241655
  · exact B241659
  · exact B241663
  · exact B241667
  · exact B241671
  · exact B241675
  · exact B241679
  · exact B241683
  · exact B241687
  · exact B241691
  · exact B241695
  · exact B241699
  · exact B241703
  · exact B241707
  · exact B241711
  · exact B241715
  · exact B241719
  · exact B241723
  · exact B241727
  · exact B241731
  · exact B241735
  · exact B241739
  · exact B241743
  · exact B241747
  · exact B241751
  · exact B241755
  · exact B241759
  · exact B241763
  · exact B241767
  · exact B241771
  · exact B241775
  · exact B241779
  · exact B241783
  · exact B241787
  · exact B241791
  · exact B241795
  · exact B241799
  · exact B241803
  · exact B241807
  · exact B241811
  · exact B241815
  · exact B241819
  · exact B241823
  · exact B241827
  · exact B241831
  · exact B241835
  · exact B241839
  · exact B241843
  · exact B241847
  · exact B241851
  · exact B241855
  · exact B241859
  · exact B241863
  · exact B241867
  · exact B241871
  · exact B241875
  · exact B241879
  · exact B241883
  · exact B241887
  · exact B241891
  · exact B241895
  · exact B241899
  · exact B241903
  · exact B241907
  · exact B241911
  · exact B241915
  · exact B241919
  · exact B241923
  · exact B241927
  · exact B241931
  · exact B241935
  · exact B241939
  · exact B241943
  · exact B241947
  · exact B241951
  · exact B241955
  · exact B241959
  · exact B241963
  · exact B241967
  · exact B241971
  · exact B241975
  · exact B241979
  · exact B241983
  · exact B241987
  · exact B241991
  · exact B241995
  · exact B241999
  · exact B242003
  · exact B242007
  · exact B242011
  · exact B242015
  · exact B242019
  · exact B242023
  · exact B242027
  · exact B242031
  · exact B242035
  · exact B242039
  · exact B242043
  · exact B242047
  · exact B242051
  · exact B242055
  · exact B242059
  · exact B242063
  · exact B242067
  · exact B242071
  · exact B242075
  · exact B242079
  · exact B242083
  · exact B242087
  · exact B242091
  · exact B242095
  · exact B242099
  · exact B242103
  · exact B242107
  · exact B242111
  · exact B242115
  · exact B242119
  · exact B242123
  · exact B242127
  · exact B242131
  · exact B242135
  · exact B242139
  · exact B242143
  · exact B242147
  · exact B242151
  · exact B242155
  · exact B242159
  · exact B242163
  · exact B242167
  · exact B242171
  · exact B242175
  · exact B242179
  · exact B242183
  · exact B242187
  · exact B242191
  · exact B242195
  · exact B242199
  · exact B242203
  · exact B242207
  · exact B242211
  · exact B242215
  · exact B242219
  · exact B242223
  · exact B242227
  · exact B242231
  · exact B242235
  · exact B242239
  · exact B242243
  · exact B242247
  · exact B242251
  · exact B242255
  · exact B242259
  · exact B242263
  · exact B242267
  · exact B242271
  · exact B242275
  · exact B242279
  · exact B242283
  · exact B242287
  · exact B242291
  · exact B242295
  · exact B242299
  · exact B242303
  · exact B242307
  · exact B242311
  · exact B242315
  · exact B242319
  · exact B242323
  · exact B242327
  · exact B242331
  · exact B242335
  · exact B242339
  · exact B242343
  · exact B242347
  · exact B242351
  · exact B242355
  · exact B242359
  · exact B242363
  · exact B242367
  · exact B242371
  · exact B242375
  · exact B242379
  · exact B242383
  · exact B242387
  · exact B242391
  · exact B242395
  · exact B242399
  · exact B242403
  · exact B242407
  · exact B242411
  · exact B242415
  · exact B242419
  · exact B242423
  · exact B242427
  · exact B242431
  · exact B242435
  · exact B242439
  · exact B242443
  · exact B242447
  · exact B242451
  · exact B242455
  · exact B242459
  · exact B242463
  · exact B242467
  · exact B242471
  · exact B242475
  · exact B242479
  · exact B242483
  · exact B242487
  · exact B242491
  · exact B242495
  · exact B242499
  · exact B242503
  · exact B242507
  · exact B242511
  · exact B242515
  · exact B242519
  · exact B242523
  · exact B242527
  · exact B242531
  · exact B242535
  · exact B242539
  · exact B242543
  · exact B242547
  · exact B242551
  · exact B242555
  · exact B242559
  · exact B242563
  · exact B242567
  · exact B242571
  · exact B242575
  · exact B242579
  · exact B242583
  · exact B242587
  · exact B242591
  · exact B242595
  · exact B242599
  · exact B242603
  · exact B242607
  · exact B242611
  · exact B242615

theorem C1 (j : ℕ) (h1 : 60654 ≤ j) (h2 : j ≤ 60953) : Blo 239816 (4 * j + 3) := by
  interval_cases j
  · exact B242619
  · exact B242623
  · exact B242627
  · exact B242631
  · exact B242635
  · exact B242639
  · exact B242643
  · exact B242647
  · exact B242651
  · exact B242655
  · exact B242659
  · exact B242663
  · exact B242667
  · exact B242671
  · exact B242675
  · exact B242679
  · exact B242683
  · exact B242687
  · exact B242691
  · exact B242695
  · exact B242699
  · exact B242703
  · exact B242707
  · exact B242711
  · exact B242715
  · exact B242719
  · exact B242723
  · exact B242727
  · exact B242731
  · exact B242735
  · exact B242739
  · exact B242743
  · exact B242747
  · exact B242751
  · exact B242755
  · exact B242759
  · exact B242763
  · exact B242767
  · exact B242771
  · exact B242775
  · exact B242779
  · exact B242783
  · exact B242787
  · exact B242791
  · exact B242795
  · exact B242799
  · exact B242803
  · exact B242807
  · exact B242811
  · exact B242815
  · exact B242819
  · exact B242823
  · exact B242827
  · exact B242831
  · exact B242835
  · exact B242839
  · exact B242843
  · exact B242847
  · exact B242851
  · exact B242855
  · exact B242859
  · exact B242863
  · exact B242867
  · exact B242871
  · exact B242875
  · exact B242879
  · exact B242883
  · exact B242887
  · exact B242891
  · exact B242895
  · exact B242899
  · exact B242903
  · exact B242907
  · exact B242911
  · exact B242915
  · exact B242919
  · exact B242923
  · exact B242927
  · exact B242931
  · exact B242935
  · exact B242939
  · exact B242943
  · exact B242947
  · exact B242951
  · exact B242955
  · exact B242959
  · exact B242963
  · exact B242967
  · exact B242971
  · exact B242975
  · exact B242979
  · exact B242983
  · exact B242987
  · exact B242991
  · exact B242995
  · exact B242999
  · exact B243003
  · exact B243007
  · exact B243011
  · exact B243015
  · exact B243019
  · exact B243023
  · exact B243027
  · exact B243031
  · exact B243035
  · exact B243039
  · exact B243043
  · exact B243047
  · exact B243051
  · exact B243055
  · exact B243059
  · exact B243063
  · exact B243067
  · exact B243071
  · exact B243075
  · exact B243079
  · exact B243083
  · exact B243087
  · exact B243091
  · exact B243095
  · exact B243099
  · exact B243103
  · exact B243107
  · exact B243111
  · exact B243115
  · exact B243119
  · exact B243123
  · exact B243127
  · exact B243131
  · exact B243135
  · exact B243139
  · exact B243143
  · exact B243147
  · exact B243151
  · exact B243155
  · exact B243159
  · exact B243163
  · exact B243167
  · exact B243171
  · exact B243175
  · exact B243179
  · exact B243183
  · exact B243187
  · exact B243191
  · exact B243195
  · exact B243199
  · exact B243203
  · exact B243207
  · exact B243211
  · exact B243215
  · exact B243219
  · exact B243223
  · exact B243227
  · exact B243231
  · exact B243235
  · exact B243239
  · exact B243243
  · exact B243247
  · exact B243251
  · exact B243255
  · exact B243259
  · exact B243263
  · exact B243267
  · exact B243271
  · exact B243275
  · exact B243279
  · exact B243283
  · exact B243287
  · exact B243291
  · exact B243295
  · exact B243299
  · exact B243303
  · exact B243307
  · exact B243311
  · exact B243315
  · exact B243319
  · exact B243323
  · exact B243327
  · exact B243331
  · exact B243335
  · exact B243339
  · exact B243343
  · exact B243347
  · exact B243351
  · exact B243355
  · exact B243359
  · exact B243363
  · exact B243367
  · exact B243371
  · exact B243375
  · exact B243379
  · exact B243383
  · exact B243387
  · exact B243391
  · exact B243395
  · exact B243399
  · exact B243403
  · exact B243407
  · exact B243411
  · exact B243415
  · exact B243419
  · exact B243423
  · exact B243427
  · exact B243431
  · exact B243435
  · exact B243439
  · exact B243443
  · exact B243447
  · exact B243451
  · exact B243455
  · exact B243459
  · exact B243463
  · exact B243467
  · exact B243471
  · exact B243475
  · exact B243479
  · exact B243483
  · exact B243487
  · exact B243491
  · exact B243495
  · exact B243499
  · exact B243503
  · exact B243507
  · exact B243511
  · exact B243515
  · exact B243519
  · exact B243523
  · exact B243527
  · exact B243531
  · exact B243535
  · exact B243539
  · exact B243543
  · exact B243547
  · exact B243551
  · exact B243555
  · exact B243559
  · exact B243563
  · exact B243567
  · exact B243571
  · exact B243575
  · exact B243579
  · exact B243583
  · exact B243587
  · exact B243591
  · exact B243595
  · exact B243599
  · exact B243603
  · exact B243607
  · exact B243611
  · exact B243615
  · exact B243619
  · exact B243623
  · exact B243627
  · exact B243631
  · exact B243635
  · exact B243639
  · exact B243643
  · exact B243647
  · exact B243651
  · exact B243655
  · exact B243659
  · exact B243663
  · exact B243667
  · exact B243671
  · exact B243675
  · exact B243679
  · exact B243683
  · exact B243687
  · exact B243691
  · exact B243695
  · exact B243699
  · exact B243703
  · exact B243707
  · exact B243711
  · exact B243715
  · exact B243719
  · exact B243723
  · exact B243727
  · exact B243731
  · exact B243735
  · exact B243739
  · exact B243743
  · exact B243747
  · exact B243751
  · exact B243755
  · exact B243759
  · exact B243763
  · exact B243767
  · exact B243771
  · exact B243775
  · exact B243779
  · exact B243783
  · exact B243787
  · exact B243791
  · exact B243795
  · exact B243799
  · exact B243803
  · exact B243807
  · exact B243811
  · exact B243815

theorem solution (m : ℕ) (hlo : 239816 ≤ m) (hhi : m ≤ 243816) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 59954 ≤ j := by omega
    have hj2 : j ≤ 60953 := by omega
    have hb : Blo 239816 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 60654 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
