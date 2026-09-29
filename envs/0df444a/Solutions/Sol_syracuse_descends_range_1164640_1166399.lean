-- Prove2me | solution 1 for syracuse_descends_range_1164640_1166399
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:50.84251+00:00
-- url     : https://prove2.me/submissions/e593d134-064f-4b62-9193-418de6f2246a

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


theorem B1310737 : Blo 1164640 1310737 := bbase (se 2 (by rfl) ⟨491526, by rfl⟩ : syracuseStep 1310737 = 983053) (by norm_num)
theorem B1400857 : Blo 1164640 1400857 := bbase (se 2 (by rfl) ⟨525321, by rfl⟩ : syracuseStep 1400857 = 1050643) (by norm_num)
theorem B2949149 : Blo 1164640 2949149 := bbase (se 3 (by rfl) ⟨552965, by rfl⟩ : syracuseStep 2949149 = 1105931) (by norm_num)
theorem B2211877 : Blo 1164640 2211877 := bbase (se 4 (by rfl) ⟨207363, by rfl⟩ : syracuseStep 2211877 = 414727) (by norm_num)
theorem B1966133 : Blo 1164640 1966133 := bbase (se 5 (by rfl) ⟨92162, by rfl⟩ : syracuseStep 1966133 = 184325) (by norm_num)
theorem B1310773 : Blo 1164640 1310773 := bbase (se 5 (by rfl) ⟨61442, by rfl⟩ : syracuseStep 1310773 = 122885) (by norm_num)
theorem B2621501 : Blo 1164640 2621501 := bbase (se 3 (by rfl) ⟨491531, by rfl⟩ : syracuseStep 2621501 = 983063) (by norm_num)
theorem B1474625 : Blo 1164640 1474625 := bbase (se 2 (by rfl) ⟨552984, by rfl⟩ : syracuseStep 1474625 = 1105969) (by norm_num)
theorem B1310809 : Blo 1164640 1310809 := bbase (se 2 (by rfl) ⟨491553, by rfl⟩ : syracuseStep 1310809 = 983107) (by norm_num)
theorem B3317861 : Blo 1164640 3317861 := bbase (se 4 (by rfl) ⟨311049, by rfl⟩ : syracuseStep 3317861 = 622099) (by norm_num)
theorem B4259957 : Blo 1164640 4259957 := bbase (se 5 (by rfl) ⟨199685, by rfl⟩ : syracuseStep 4259957 = 399371) (by norm_num)
theorem B1474681 : Blo 1164640 1474681 := bbase (se 2 (by rfl) ⟨553005, by rfl⟩ : syracuseStep 1474681 = 1106011) (by norm_num)
theorem B1310845 : Blo 1164640 1310845 := bbase (se 3 (by rfl) ⟨245783, by rfl⟩ : syracuseStep 1310845 = 491567) (by norm_num)
theorem B2621573 : Blo 1164640 2621573 := bbase (se 4 (by rfl) ⟨245772, by rfl⟩ : syracuseStep 2621573 = 491545) (by norm_num)
theorem B1310881 : Blo 1164640 1310881 := bbase (se 2 (by rfl) ⟨491580, by rfl⟩ : syracuseStep 1310881 = 983161) (by norm_num)
theorem B2875565 : Blo 1164640 2875565 := bbase (se 3 (by rfl) ⟨539168, by rfl⟩ : syracuseStep 2875565 = 1078337) (by norm_num)
theorem B1966261 : Blo 1164640 1966261 := bbase (se 5 (by rfl) ⟨92168, by rfl⟩ : syracuseStep 1966261 = 184337) (by norm_num)
theorem B1310917 : Blo 1164640 1310917 := bbase (se 4 (by rfl) ⟨122898, by rfl⟩ : syracuseStep 1310917 = 245797) (by norm_num)
theorem B2621645 : Blo 1164640 2621645 := bbase (se 3 (by rfl) ⟨491558, by rfl⟩ : syracuseStep 2621645 = 983117) (by norm_num)
theorem B1474777 : Blo 1164640 1474777 := bbase (se 2 (by rfl) ⟨553041, by rfl⟩ : syracuseStep 1474777 = 1106083) (by norm_num)
theorem B1310953 : Blo 1164640 1310953 := bbase (se 2 (by rfl) ⟨491607, by rfl⟩ : syracuseStep 1310953 = 983215) (by norm_num)
theorem B1966349 : Blo 1164640 1966349 := bbase (se 3 (by rfl) ⟨368690, by rfl⟩ : syracuseStep 1966349 = 737381) (by norm_num)
theorem B1310989 : Blo 1164640 1310989 := bbase (se 3 (by rfl) ⟨245810, by rfl⟩ : syracuseStep 1310989 = 491621) (by norm_num)
theorem B2621717 : Blo 1164640 2621717 := bbase (se 6 (by rfl) ⟨61446, by rfl⟩ : syracuseStep 2621717 = 122893) (by norm_num)
theorem B1311025 : Blo 1164640 1311025 := bbase (se 2 (by rfl) ⟨491634, by rfl⟩ : syracuseStep 1311025 = 983269) (by norm_num)
theorem B1245493 : Blo 1164640 1245493 := bbase (se 5 (by rfl) ⟨58382, by rfl⟩ : syracuseStep 1245493 = 116765) (by norm_num)
theorem B5898581 : Blo 1164640 5898581 := bbase (se 10 (by rfl) ⟨8640, by rfl⟩ : syracuseStep 5898581 = 17281) (by norm_num)
theorem B2212181 : Blo 1164640 2212181 := bbase (se 10 (by rfl) ⟨3240, by rfl⟩ : syracuseStep 2212181 = 6481) (by norm_num)
theorem B1311061 : Blo 1164640 1311061 := bbase (se 10 (by rfl) ⟨1920, by rfl⟩ : syracuseStep 1311061 = 3841) (by norm_num)
theorem B2621789 : Blo 1164640 2621789 := bbase (se 3 (by rfl) ⟨491585, by rfl⟩ : syracuseStep 2621789 = 983171) (by norm_num)
theorem B2949493 : Blo 1164640 2949493 := bbase (se 5 (by rfl) ⟨138257, by rfl⟩ : syracuseStep 2949493 = 276515) (by norm_num)
theorem B1311097 : Blo 1164640 1311097 := bbase (se 2 (by rfl) ⟨491661, by rfl⟩ : syracuseStep 1311097 = 983323) (by norm_num)
theorem B1245565 : Blo 1164640 1245565 := bbase (se 3 (by rfl) ⟨233543, by rfl⟩ : syracuseStep 1245565 = 467087) (by norm_num)
theorem B3932549 : Blo 1164640 3932549 := bbase (se 4 (by rfl) ⟨368676, by rfl⟩ : syracuseStep 3932549 = 737353) (by norm_num)
theorem B1474949 : Blo 1164640 1474949 := bbase (se 4 (by rfl) ⟨138276, by rfl⟩ : syracuseStep 1474949 = 276553) (by norm_num)
theorem B1966477 : Blo 1164640 1966477 := bbase (se 3 (by rfl) ⟨368714, by rfl⟩ : syracuseStep 1966477 = 737429) (by norm_num)
theorem B1311133 : Blo 1164640 1311133 := bbase (se 3 (by rfl) ⟨245837, by rfl⟩ : syracuseStep 1311133 = 491675) (by norm_num)
theorem B2621861 : Blo 1164640 2621861 := bbase (se 4 (by rfl) ⟨245799, by rfl⟩ : syracuseStep 2621861 = 491599) (by norm_num)
theorem B1475005 : Blo 1164640 1475005 := bbase (se 3 (by rfl) ⟨276563, by rfl⟩ : syracuseStep 1475005 = 553127) (by norm_num)
theorem B1311169 : Blo 1164640 1311169 := bbase (se 2 (by rfl) ⟨491688, by rfl⟩ : syracuseStep 1311169 = 983377) (by norm_num)
theorem B14942677 : Blo 1164640 14942677 := bbase (se 7 (by rfl) ⟨175109, by rfl⟩ : syracuseStep 14942677 = 350219) (by norm_num)
theorem B8405461 : Blo 1164640 8405461 := bbase (se 7 (by rfl) ⟨98501, by rfl⟩ : syracuseStep 8405461 = 197003) (by norm_num)
theorem B4424165 : Blo 1164640 4424165 := bbase (se 4 (by rfl) ⟨414765, by rfl⟩ : syracuseStep 4424165 = 829531) (by norm_num)
theorem B2949605 : Blo 1164640 2949605 := bbase (se 4 (by rfl) ⟨276525, by rfl⟩ : syracuseStep 2949605 = 553051) (by norm_num)
theorem B1966565 : Blo 1164640 1966565 := bbase (se 4 (by rfl) ⟨184365, by rfl⟩ : syracuseStep 1966565 = 368731) (by norm_num)
theorem B1311205 : Blo 1164640 1311205 := bbase (se 4 (by rfl) ⟨122925, by rfl⟩ : syracuseStep 1311205 = 245851) (by norm_num)
theorem B5317093 : Blo 1164640 5317093 := bbase (se 4 (by rfl) ⟨498477, by rfl⟩ : syracuseStep 5317093 = 996955) (by norm_num)
theorem B5603813 : Blo 1164640 5603813 := bbase (se 4 (by rfl) ⟨525357, by rfl⟩ : syracuseStep 5603813 = 1050715) (by norm_num)
theorem B2621933 : Blo 1164640 2621933 := bbase (se 3 (by rfl) ⟨491612, by rfl⟩ : syracuseStep 2621933 = 983225) (by norm_num)
theorem B1311241 : Blo 1164640 1311241 := bbase (se 2 (by rfl) ⟨491715, by rfl⟩ : syracuseStep 1311241 = 983431) (by norm_num)
theorem B1475101 : Blo 1164640 1475101 := bbase (se 3 (by rfl) ⟨276581, by rfl⟩ : syracuseStep 1475101 = 553163) (by norm_num)
theorem B3031589 : Blo 1164640 3031589 := bbase (se 4 (by rfl) ⟨284211, by rfl⟩ : syracuseStep 3031589 = 568423) (by norm_num)
theorem B1311277 : Blo 1164640 1311277 := bbase (se 3 (by rfl) ⟨245864, by rfl⟩ : syracuseStep 1311277 = 491729) (by norm_num)
theorem B2490925 : Blo 1164640 2490925 := bbase (se 3 (by rfl) ⟨467048, by rfl⟩ : syracuseStep 2490925 = 934097) (by norm_num)
theorem B2622005 : Blo 1164640 2622005 := bbase (se 5 (by rfl) ⟨122906, by rfl⟩ : syracuseStep 2622005 = 245813) (by norm_num)
theorem B1311313 : Blo 1164640 1311313 := bbase (se 2 (by rfl) ⟨491742, by rfl⟩ : syracuseStep 1311313 = 983485) (by norm_num)
theorem B1966693 : Blo 1164640 1966693 := bbase (se 4 (by rfl) ⟨184377, by rfl⟩ : syracuseStep 1966693 = 368755) (by norm_num)
theorem B1311349 : Blo 1164640 1311349 := bbase (se 5 (by rfl) ⟨61469, by rfl⟩ : syracuseStep 1311349 = 122939) (by norm_num)
theorem B2622077 : Blo 1164640 2622077 := bbase (se 3 (by rfl) ⟨491639, by rfl⟩ : syracuseStep 2622077 = 983279) (by norm_num)
theorem B1311385 : Blo 1164640 1311385 := bbase (se 2 (by rfl) ⟨491769, by rfl⟩ : syracuseStep 1311385 = 983539) (by norm_num)
theorem B2949797 : Blo 1164640 2949797 := bbase (se 4 (by rfl) ⟨276543, by rfl⟩ : syracuseStep 2949797 = 553087) (by norm_num)
theorem B5604005 : Blo 1164640 5604005 := bbase (se 4 (by rfl) ⟨525375, by rfl⟩ : syracuseStep 5604005 = 1050751) (by norm_num)
theorem B1966781 : Blo 1164640 1966781 := bbase (se 3 (by rfl) ⟨368771, by rfl⟩ : syracuseStep 1966781 = 737543) (by norm_num)
theorem B1311421 : Blo 1164640 1311421 := bbase (se 3 (by rfl) ⟨245891, by rfl⟩ : syracuseStep 1311421 = 491783) (by norm_num)
theorem B2622149 : Blo 1164640 2622149 := bbase (se 4 (by rfl) ⟨245826, by rfl⟩ : syracuseStep 2622149 = 491653) (by norm_num)
theorem B1475273 : Blo 1164640 1475273 := bbase (se 2 (by rfl) ⟨553227, by rfl⟩ : syracuseStep 1475273 = 1106455) (by norm_num)
theorem B1311457 : Blo 1164640 1311457 := bbase (se 2 (by rfl) ⟨491796, by rfl⟩ : syracuseStep 1311457 = 983593) (by norm_num)
theorem B1475329 : Blo 1164640 1475329 := bbase (se 2 (by rfl) ⟨553248, by rfl⟩ : syracuseStep 1475329 = 1106497) (by norm_num)
theorem B4424453 : Blo 1164640 4424453 := bbase (se 4 (by rfl) ⟨414792, by rfl⟩ : syracuseStep 4424453 = 829585) (by norm_num)
theorem B1311493 : Blo 1164640 1311493 := bbase (se 4 (by rfl) ⟨122952, by rfl⟩ : syracuseStep 1311493 = 245905) (by norm_num)
theorem B2622221 : Blo 1164640 2622221 := bbase (se 3 (by rfl) ⟨491666, by rfl⟩ : syracuseStep 2622221 = 983333) (by norm_num)
theorem B1311529 : Blo 1164640 1311529 := bbase (se 2 (by rfl) ⟨491823, by rfl⟩ : syracuseStep 1311529 = 983647) (by norm_num)
theorem B3932981 : Blo 1164640 3932981 := bbase (se 5 (by rfl) ⟨184358, by rfl⟩ : syracuseStep 3932981 = 368717) (by norm_num)
theorem B1966909 : Blo 1164640 1966909 := bbase (se 3 (by rfl) ⟨368795, by rfl⟩ : syracuseStep 1966909 = 737591) (by norm_num)
theorem B1311565 : Blo 1164640 1311565 := bbase (se 3 (by rfl) ⟨245918, by rfl⟩ : syracuseStep 1311565 = 491837) (by norm_num)
theorem B37798741 : Blo 1164640 37798741 := bbase (se 9 (by rfl) ⟨110738, by rfl⟩ : syracuseStep 37798741 = 221477) (by norm_num)
theorem B2622293 : Blo 1164640 2622293 := bbase (se 9 (by rfl) ⟨7682, by rfl⟩ : syracuseStep 2622293 = 15365) (by norm_num)
theorem B1475425 : Blo 1164640 1475425 := bbase (se 2 (by rfl) ⟨553284, by rfl⟩ : syracuseStep 1475425 = 1106569) (by norm_num)
theorem B1311601 : Blo 1164640 1311601 := bbase (se 2 (by rfl) ⟨491850, by rfl⟩ : syracuseStep 1311601 = 983701) (by norm_num)
theorem B1966997 : Blo 1164640 1966997 := bbase (se 6 (by rfl) ⟨46101, by rfl⟩ : syracuseStep 1966997 = 92203) (by norm_num)
theorem B1311637 : Blo 1164640 1311637 := bbase (se 6 (by rfl) ⟨30741, by rfl⟩ : syracuseStep 1311637 = 61483) (by norm_num)
theorem B2622365 : Blo 1164640 2622365 := bbase (se 3 (by rfl) ⟨491693, by rfl⟩ : syracuseStep 2622365 = 983387) (by norm_num)
theorem B1311673 : Blo 1164640 1311673 := bbase (se 2 (by rfl) ⟨491877, by rfl⟩ : syracuseStep 1311673 = 983755) (by norm_num)
theorem B1311709 : Blo 1164640 1311709 := bbase (se 3 (by rfl) ⟨245945, by rfl⟩ : syracuseStep 1311709 = 491891) (by norm_num)
theorem B2622437 : Blo 1164640 2622437 := bbase (se 4 (by rfl) ⟨245853, by rfl⟩ : syracuseStep 2622437 = 491707) (by norm_num)
theorem B2950141 : Blo 1164640 2950141 := bbase (se 3 (by rfl) ⟨553151, by rfl⟩ : syracuseStep 2950141 = 1106303) (by norm_num)
theorem B1311745 : Blo 1164640 1311745 := bbase (se 2 (by rfl) ⟨491904, by rfl⟩ : syracuseStep 1311745 = 983809) (by norm_num)
theorem B1475597 : Blo 1164640 1475597 := bbase (se 3 (by rfl) ⟨276674, by rfl⟩ : syracuseStep 1475597 = 553349) (by norm_num)
theorem B1967125 : Blo 1164640 1967125 := bbase (se 6 (by rfl) ⟨46104, by rfl⟩ : syracuseStep 1967125 = 92209) (by norm_num)
theorem B1311781 : Blo 1164640 1311781 := bbase (se 4 (by rfl) ⟨122979, by rfl⟩ : syracuseStep 1311781 = 245959) (by norm_num)
theorem B2622509 : Blo 1164640 2622509 := bbase (se 3 (by rfl) ⟨491720, by rfl⟩ : syracuseStep 2622509 = 983441) (by norm_num)
theorem B1180741 : Blo 1164640 1180741 := bbase (se 4 (by rfl) ⟨110694, by rfl⟩ : syracuseStep 1180741 = 221389) (by norm_num)
theorem B3318853 : Blo 1164640 3318853 := bbase (se 4 (by rfl) ⟨311142, by rfl⟩ : syracuseStep 3318853 = 622285) (by norm_num)
theorem B2212933 : Blo 1164640 2212933 := bbase (se 4 (by rfl) ⟨207462, by rfl⟩ : syracuseStep 2212933 = 414925) (by norm_num)
theorem B1475653 : Blo 1164640 1475653 := bbase (se 4 (by rfl) ⟨138342, by rfl⟩ : syracuseStep 1475653 = 276685) (by norm_num)
theorem B1311817 : Blo 1164640 1311817 := bbase (se 2 (by rfl) ⟨491931, by rfl⟩ : syracuseStep 1311817 = 983863) (by norm_num)
theorem B2950253 : Blo 1164640 2950253 := bbase (se 3 (by rfl) ⟨553172, by rfl⟩ : syracuseStep 2950253 = 1106345) (by norm_num)
theorem B1967213 : Blo 1164640 1967213 := bbase (se 3 (by rfl) ⟨368852, by rfl⟩ : syracuseStep 1967213 = 737705) (by norm_num)
theorem B1311853 : Blo 1164640 1311853 := bbase (se 3 (by rfl) ⟨245972, by rfl⟩ : syracuseStep 1311853 = 491945) (by norm_num)
theorem B2622581 : Blo 1164640 2622581 := bbase (se 5 (by rfl) ⟨122933, by rfl⟩ : syracuseStep 2622581 = 245867) (by norm_num)
theorem B1311889 : Blo 1164640 1311889 := bbase (se 2 (by rfl) ⟨491958, by rfl⟩ : syracuseStep 1311889 = 983917) (by norm_num)
theorem B1475749 : Blo 1164640 1475749 := bbase (se 4 (by rfl) ⟨138351, by rfl⟩ : syracuseStep 1475749 = 276703) (by norm_num)
theorem B6636725 : Blo 1164640 6636725 := bbase (se 5 (by rfl) ⟨311096, by rfl⟩ : syracuseStep 6636725 = 622193) (by norm_num)
theorem B1311925 : Blo 1164640 1311925 := bbase (se 5 (by rfl) ⟨61496, by rfl⟩ : syracuseStep 1311925 = 122993) (by norm_num)
theorem B2622653 : Blo 1164640 2622653 := bbase (se 3 (by rfl) ⟨491747, by rfl⟩ : syracuseStep 2622653 = 983495) (by norm_num)
theorem B21251285 : Blo 1164640 21251285 := bbase (se 7 (by rfl) ⟨249038, by rfl⟩ : syracuseStep 21251285 = 498077) (by norm_num)
theorem B2213077 : Blo 1164640 2213077 := bbase (se 7 (by rfl) ⟨25934, by rfl⟩ : syracuseStep 2213077 = 51869) (by norm_num)
theorem B1311961 : Blo 1164640 1311961 := bbase (se 2 (by rfl) ⟨491985, by rfl⟩ : syracuseStep 1311961 = 983971) (by norm_num)
theorem B3933413 : Blo 1164640 3933413 := bbase (se 4 (by rfl) ⟨368757, by rfl⟩ : syracuseStep 3933413 = 737515) (by norm_num)
theorem B1967341 : Blo 1164640 1967341 := bbase (se 3 (by rfl) ⟨368876, by rfl⟩ : syracuseStep 1967341 = 737753) (by norm_num)
theorem B1311997 : Blo 1164640 1311997 := bbase (se 3 (by rfl) ⟨245999, by rfl⟩ : syracuseStep 1311997 = 491999) (by norm_num)
theorem B2622725 : Blo 1164640 2622725 := bbase (se 4 (by rfl) ⟨245880, by rfl⟩ : syracuseStep 2622725 = 491761) (by norm_num)
theorem B1312033 : Blo 1164640 1312033 := bbase (se 2 (by rfl) ⟨492012, by rfl⟩ : syracuseStep 1312033 = 984025) (by norm_num)
theorem B2950445 : Blo 1164640 2950445 := bbase (se 3 (by rfl) ⟨553208, by rfl⟩ : syracuseStep 2950445 = 1106417) (by norm_num)
theorem B1574213 : Blo 1164640 1574213 := bbase (se 4 (by rfl) ⟨147582, by rfl⟩ : syracuseStep 1574213 = 295165) (by norm_num)
theorem B1967429 : Blo 1164640 1967429 := bbase (se 4 (by rfl) ⟨184446, by rfl⟩ : syracuseStep 1967429 = 368893) (by norm_num)
theorem B1312069 : Blo 1164640 1312069 := bbase (se 4 (by rfl) ⟨123006, by rfl⟩ : syracuseStep 1312069 = 246013) (by norm_num)
theorem B2622797 : Blo 1164640 2622797 := bbase (se 3 (by rfl) ⟨491774, by rfl⟩ : syracuseStep 2622797 = 983549) (by norm_num)
theorem B1475921 : Blo 1164640 1475921 := bbase (se 2 (by rfl) ⟨553470, by rfl⟩ : syracuseStep 1475921 = 1106941) (by norm_num)
theorem B1312105 : Blo 1164640 1312105 := bbase (se 2 (by rfl) ⟨492039, by rfl⟩ : syracuseStep 1312105 = 984079) (by norm_num)
theorem B9954677 : Blo 1164640 9954677 := bbase (se 5 (by rfl) ⟨466625, by rfl⟩ : syracuseStep 9954677 = 933251) (by norm_num)
theorem B2213237 : Blo 1164640 2213237 := bbase (se 5 (by rfl) ⟨103745, by rfl⟩ : syracuseStep 2213237 = 207491) (by norm_num)
theorem B1181057 : Blo 1164640 1181057 := bbase (se 2 (by rfl) ⟨442896, by rfl⟩ : syracuseStep 1181057 = 885793) (by norm_num)
theorem B1475977 : Blo 1164640 1475977 := bbase (se 2 (by rfl) ⟨553491, by rfl⟩ : syracuseStep 1475977 = 1106983) (by norm_num)
theorem B1312141 : Blo 1164640 1312141 := bbase (se 3 (by rfl) ⟨246026, by rfl⟩ : syracuseStep 1312141 = 492053) (by norm_num)
theorem B2622869 : Blo 1164640 2622869 := bbase (se 6 (by rfl) ⟨61473, by rfl⟩ : syracuseStep 2622869 = 122947) (by norm_num)
theorem B1967557 : Blo 1164640 1967557 := bbase (se 4 (by rfl) ⟨184458, by rfl⟩ : syracuseStep 1967557 = 368917) (by norm_num)
theorem B2622941 : Blo 1164640 2622941 := bbase (se 3 (by rfl) ⟨491801, by rfl⟩ : syracuseStep 2622941 = 983603) (by norm_num)
theorem B1476073 : Blo 1164640 1476073 := bbase (se 2 (by rfl) ⟨553527, by rfl⟩ : syracuseStep 1476073 = 1107055) (by norm_num)
theorem B2213381 : Blo 1164640 2213381 := bbase (se 4 (by rfl) ⟨207504, by rfl⟩ : syracuseStep 2213381 = 415009) (by norm_num)
theorem B1967645 : Blo 1164640 1967645 := bbase (se 3 (by rfl) ⟨368933, by rfl⟩ : syracuseStep 1967645 = 737867) (by norm_num)
theorem B2623013 : Blo 1164640 2623013 := bbase (se 4 (by rfl) ⟨245907, by rfl⟩ : syracuseStep 2623013 = 491815) (by norm_num)
theorem B5899877 : Blo 1164640 5899877 := bbase (se 4 (by rfl) ⟨553113, by rfl⟩ : syracuseStep 5899877 = 1106227) (by norm_num)
theorem B2623085 : Blo 1164640 2623085 := bbase (se 3 (by rfl) ⟨491828, by rfl⟩ : syracuseStep 2623085 = 983657) (by norm_num)
theorem B1181305 : Blo 1164640 1181305 := bbase (se 2 (by rfl) ⟨442989, by rfl⟩ : syracuseStep 1181305 = 885979) (by norm_num)
theorem B2950789 : Blo 1164640 2950789 := bbase (se 4 (by rfl) ⟨276636, by rfl⟩ : syracuseStep 2950789 = 553273) (by norm_num)
theorem B3933845 : Blo 1164640 3933845 := bbase (se 6 (by rfl) ⟨92199, by rfl⟩ : syracuseStep 3933845 = 184399) (by norm_num)
theorem B1181341 : Blo 1164640 1181341 := bbase (se 3 (by rfl) ⟨221501, by rfl⟩ : syracuseStep 1181341 = 443003) (by norm_num)
theorem B1967773 : Blo 1164640 1967773 := bbase (se 3 (by rfl) ⟨368957, by rfl⟩ : syracuseStep 1967773 = 737915) (by norm_num)
theorem B1574581 : Blo 1164640 1574581 := bbase (se 5 (by rfl) ⟨73808, by rfl⟩ : syracuseStep 1574581 = 147617) (by norm_num)
theorem B6727349 : Blo 1164640 6727349 := bbase (se 5 (by rfl) ⟨315344, by rfl⟩ : syracuseStep 6727349 = 630689) (by norm_num)
theorem B2623157 : Blo 1164640 2623157 := bbase (se 5 (by rfl) ⟨122960, by rfl⟩ : syracuseStep 2623157 = 245921) (by norm_num)
theorem B2950901 : Blo 1164640 2950901 := bbase (se 5 (by rfl) ⟨138323, by rfl⟩ : syracuseStep 2950901 = 276647) (by norm_num)
theorem B1967861 : Blo 1164640 1967861 := bbase (se 5 (by rfl) ⟨92243, by rfl⟩ : syracuseStep 1967861 = 184487) (by norm_num)
theorem B2623229 : Blo 1164640 2623229 := bbase (se 3 (by rfl) ⟨491855, by rfl⟩ : syracuseStep 2623229 = 983711) (by norm_num)
theorem B2361125 : Blo 1164640 2361125 := bbase (se 4 (by rfl) ⟨221355, by rfl⟩ : syracuseStep 2361125 = 442711) (by norm_num)
theorem B2213669 : Blo 1164640 2213669 := bbase (se 4 (by rfl) ⟨207531, by rfl⟩ : syracuseStep 2213669 = 415063) (by norm_num)
theorem B2623301 : Blo 1164640 2623301 := bbase (se 4 (by rfl) ⟨245934, by rfl⟩ : syracuseStep 2623301 = 491869) (by norm_num)
theorem B1967989 : Blo 1164640 1967989 := bbase (se 5 (by rfl) ⟨92249, by rfl⟩ : syracuseStep 1967989 = 184499) (by norm_num)
theorem B2623373 : Blo 1164640 2623373 := bbase (se 3 (by rfl) ⟨491882, by rfl⟩ : syracuseStep 2623373 = 983765) (by norm_num)
theorem B4425637 : Blo 1164640 4425637 := bbase (se 4 (by rfl) ⟨414903, by rfl⟩ : syracuseStep 4425637 = 829807) (by norm_num)
theorem B2951093 : Blo 1164640 2951093 := bbase (se 5 (by rfl) ⟨138332, by rfl⟩ : syracuseStep 2951093 = 276665) (by norm_num)
theorem B1992637 : Blo 1164640 1992637 := bbase (se 3 (by rfl) ⟨373619, by rfl⟩ : syracuseStep 1992637 = 747239) (by norm_num)
theorem B2213821 : Blo 1164640 2213821 := bbase (se 3 (by rfl) ⟨415091, by rfl⟩ : syracuseStep 2213821 = 830183) (by norm_num)
theorem B1181633 : Blo 1164640 1181633 := bbase (se 2 (by rfl) ⟨443112, by rfl⟩ : syracuseStep 1181633 = 886225) (by norm_num)
theorem B1968077 : Blo 1164640 1968077 := bbase (se 3 (by rfl) ⟨369014, by rfl⟩ : syracuseStep 1968077 = 738029) (by norm_num)
theorem B2623445 : Blo 1164640 2623445 := bbase (se 7 (by rfl) ⟨30743, by rfl⟩ : syracuseStep 2623445 = 61487) (by norm_num)
theorem B14378965 : Blo 1164640 14378965 := bbase (se 7 (by rfl) ⟨168503, by rfl⟩ : syracuseStep 14378965 = 337007) (by norm_num)
theorem B1181665 : Blo 1164640 1181665 := bbase (se 2 (by rfl) ⟨443124, by rfl⟩ : syracuseStep 1181665 = 886249) (by norm_num)
theorem B1746965 : Blo 1164640 1746965 := bbase (se 6 (by rfl) ⟨40944, by rfl⟩ : syracuseStep 1746965 = 81889) (by norm_num)
theorem B2623517 : Blo 1164640 2623517 := bbase (se 3 (by rfl) ⟨491909, by rfl⟩ : syracuseStep 2623517 = 983819) (by norm_num)
theorem B1746989 : Blo 1164640 1746989 := bbase (se 3 (by rfl) ⟨327560, by rfl⟩ : syracuseStep 1746989 = 655121) (by norm_num)
theorem B1747013 : Blo 1164640 1747013 := bbase (se 4 (by rfl) ⟨163782, by rfl⟩ : syracuseStep 1747013 = 327565) (by norm_num)
theorem B3934277 : Blo 1164640 3934277 := bbase (se 4 (by rfl) ⟨368838, by rfl⟩ : syracuseStep 3934277 = 737677) (by norm_num)
theorem B1968205 : Blo 1164640 1968205 := bbase (se 3 (by rfl) ⟨369038, by rfl⟩ : syracuseStep 1968205 = 738077) (by norm_num)
theorem B1747037 : Blo 1164640 1747037 := bbase (se 3 (by rfl) ⟨327569, by rfl⟩ : syracuseStep 1747037 = 655139) (by norm_num)
theorem B2623589 : Blo 1164640 2623589 := bbase (se 4 (by rfl) ⟨245961, by rfl⟩ : syracuseStep 2623589 = 491923) (by norm_num)
theorem B1747061 : Blo 1164640 1747061 := bbase (se 5 (by rfl) ⟨81893, by rfl⟩ : syracuseStep 1747061 = 163787) (by norm_num)
theorem B1747085 : Blo 1164640 1747085 := bbase (se 3 (by rfl) ⟨327578, by rfl⟩ : syracuseStep 1747085 = 655157) (by norm_num)
theorem B1796237 : Blo 1164640 1796237 := bbase (se 3 (by rfl) ⟨336794, by rfl⟩ : syracuseStep 1796237 = 673589) (by norm_num)
theorem B3319957 : Blo 1164640 3319957 := bbase (se 6 (by rfl) ⟨77811, by rfl⟩ : syracuseStep 3319957 = 155623) (by norm_num)
theorem B1747109 : Blo 1164640 1747109 := bbase (se 4 (by rfl) ⟨163791, by rfl⟩ : syracuseStep 1747109 = 327583) (by norm_num)
theorem B1968293 : Blo 1164640 1968293 := bbase (se 4 (by rfl) ⟨184527, by rfl⟩ : syracuseStep 1968293 = 369055) (by norm_num)
theorem B2623661 : Blo 1164640 2623661 := bbase (se 3 (by rfl) ⟨491936, by rfl⟩ : syracuseStep 2623661 = 983873) (by norm_num)
theorem B1747133 : Blo 1164640 1747133 := bbase (se 3 (by rfl) ⟨327587, by rfl⟩ : syracuseStep 1747133 = 655175) (by norm_num)
theorem B1747157 : Blo 1164640 1747157 := bbase (se 7 (by rfl) ⟨20474, by rfl⟩ : syracuseStep 1747157 = 40949) (by norm_num)
theorem B4425941 : Blo 1164640 4425941 := bbase (se 7 (by rfl) ⟨51866, by rfl⟩ : syracuseStep 4425941 = 103733) (by norm_num)
theorem B1747181 : Blo 1164640 1747181 := bbase (se 3 (by rfl) ⟨327596, by rfl⟩ : syracuseStep 1747181 = 655193) (by norm_num)
theorem B2214125 : Blo 1164640 2214125 := bbase (se 3 (by rfl) ⟨415148, by rfl⟩ : syracuseStep 2214125 = 830297) (by norm_num)
theorem B2623733 : Blo 1164640 2623733 := bbase (se 5 (by rfl) ⟨122987, by rfl⟩ : syracuseStep 2623733 = 245975) (by norm_num)
theorem B1747205 : Blo 1164640 1747205 := bbase (se 4 (by rfl) ⟨163800, by rfl⟩ : syracuseStep 1747205 = 327601) (by norm_num)
theorem B2951437 : Blo 1164640 2951437 := bbase (se 3 (by rfl) ⟨553394, by rfl⟩ : syracuseStep 2951437 = 1106789) (by norm_num)
theorem B1747229 : Blo 1164640 1747229 := bbase (se 3 (by rfl) ⟨327605, by rfl⟩ : syracuseStep 1747229 = 655211) (by norm_num)
theorem B1747253 : Blo 1164640 1747253 := bbase (se 5 (by rfl) ⟨81902, by rfl⟩ : syracuseStep 1747253 = 163805) (by norm_num)
theorem B2623805 : Blo 1164640 2623805 := bbase (se 3 (by rfl) ⟨491963, by rfl⟩ : syracuseStep 2623805 = 983927) (by norm_num)
theorem B1747277 : Blo 1164640 1747277 := bbase (se 3 (by rfl) ⟨327614, by rfl⟩ : syracuseStep 1747277 = 655229) (by norm_num)
theorem B6637909 : Blo 1164640 6637909 := bbase (se 10 (by rfl) ⟨9723, by rfl⟩ : syracuseStep 6637909 = 19447) (by norm_num)
theorem B1747301 : Blo 1164640 1747301 := bbase (se 4 (by rfl) ⟨163809, by rfl⟩ : syracuseStep 1747301 = 327619) (by norm_num)
theorem B1747325 : Blo 1164640 1747325 := bbase (se 3 (by rfl) ⟨327623, by rfl⟩ : syracuseStep 1747325 = 655247) (by norm_num)
theorem B2951549 : Blo 1164640 2951549 := bbase (se 3 (by rfl) ⟨553415, by rfl⟩ : syracuseStep 2951549 = 1106831) (by norm_num)
theorem B2623877 : Blo 1164640 2623877 := bbase (se 4 (by rfl) ⟨245988, by rfl⟩ : syracuseStep 2623877 = 491977) (by norm_num)
theorem B1747349 : Blo 1164640 1747349 := bbase (se 6 (by rfl) ⟨40953, by rfl⟩ : syracuseStep 1747349 = 81907) (by norm_num)
theorem B12954005 : Blo 1164640 12954005 := bbase (se 6 (by rfl) ⟨303609, by rfl⟩ : syracuseStep 12954005 = 607219) (by norm_num)
theorem B1747373 : Blo 1164640 1747373 := bbase (se 3 (by rfl) ⟨327632, by rfl⟩ : syracuseStep 1747373 = 655265) (by norm_num)
theorem B2591165 : Blo 1164640 2591165 := bbase (se 3 (by rfl) ⟨485843, by rfl⟩ : syracuseStep 2591165 = 971687) (by norm_num)
theorem B1747397 : Blo 1164640 1747397 := bbase (se 4 (by rfl) ⟨163818, by rfl⟩ : syracuseStep 1747397 = 327637) (by norm_num)
theorem B2623949 : Blo 1164640 2623949 := bbase (se 3 (by rfl) ⟨491990, by rfl⟩ : syracuseStep 2623949 = 983981) (by norm_num)
theorem B1182161 : Blo 1164640 1182161 := bbase (se 2 (by rfl) ⟨443310, by rfl⟩ : syracuseStep 1182161 = 886621) (by norm_num)
theorem B1329625 : Blo 1164640 1329625 := bbase (se 2 (by rfl) ⟨498609, by rfl⟩ : syracuseStep 1329625 = 997219) (by norm_num)
theorem B1747421 : Blo 1164640 1747421 := bbase (se 3 (by rfl) ⟨327641, by rfl⟩ : syracuseStep 1747421 = 655283) (by norm_num)
theorem B1747445 : Blo 1164640 1747445 := bbase (se 5 (by rfl) ⟨81911, by rfl⟩ : syracuseStep 1747445 = 163823) (by norm_num)
theorem B3934709 : Blo 1164640 3934709 := bbase (se 5 (by rfl) ⟨184439, by rfl⟩ : syracuseStep 3934709 = 368879) (by norm_num)
theorem B1747469 : Blo 1164640 1747469 := bbase (se 3 (by rfl) ⟨327650, by rfl⟩ : syracuseStep 1747469 = 655301) (by norm_num)
theorem B2624021 : Blo 1164640 2624021 := bbase (se 6 (by rfl) ⟨61500, by rfl⟩ : syracuseStep 2624021 = 123001) (by norm_num)
theorem B1182233 : Blo 1164640 1182233 := bbase (se 2 (by rfl) ⟨443337, by rfl⟩ : syracuseStep 1182233 = 886675) (by norm_num)
theorem B1747493 : Blo 1164640 1747493 := bbase (se 4 (by rfl) ⟨163827, by rfl⟩ : syracuseStep 1747493 = 327655) (by norm_num)
theorem B1747517 : Blo 1164640 1747517 := bbase (se 3 (by rfl) ⟨327659, by rfl⟩ : syracuseStep 1747517 = 655319) (by norm_num)
theorem B2099773 : Blo 1164640 2099773 := bbase (se 3 (by rfl) ⟨393707, by rfl⟩ : syracuseStep 2099773 = 787415) (by norm_num)
theorem B2951741 : Blo 1164640 2951741 := bbase (se 3 (by rfl) ⟨553451, by rfl⟩ : syracuseStep 2951741 = 1106903) (by norm_num)
theorem B1747541 : Blo 1164640 1747541 := bbase (se 8 (by rfl) ⟨10239, by rfl⟩ : syracuseStep 1747541 = 20479) (by norm_num)
theorem B7088725 : Blo 1164640 7088725 := bbase (se 8 (by rfl) ⟨41535, by rfl⟩ : syracuseStep 7088725 = 83071) (by norm_num)
theorem B2624093 : Blo 1164640 2624093 := bbase (se 3 (by rfl) ⟨492017, by rfl⟩ : syracuseStep 2624093 = 984035) (by norm_num)
theorem B1747565 : Blo 1164640 1747565 := bbase (se 3 (by rfl) ⟨327668, by rfl⟩ : syracuseStep 1747565 = 655337) (by norm_num)
theorem B1747589 : Blo 1164640 1747589 := bbase (se 4 (by rfl) ⟨163836, by rfl⟩ : syracuseStep 1747589 = 327673) (by norm_num)
theorem B1747613 : Blo 1164640 1747613 := bbase (se 3 (by rfl) ⟨327677, by rfl⟩ : syracuseStep 1747613 = 655355) (by norm_num)
theorem B2624165 : Blo 1164640 2624165 := bbase (se 4 (by rfl) ⟨246015, by rfl⟩ : syracuseStep 2624165 = 492031) (by norm_num)
theorem B1747637 : Blo 1164640 1747637 := bbase (se 5 (by rfl) ⟨81920, by rfl⟩ : syracuseStep 1747637 = 163841) (by norm_num)
theorem B1747661 : Blo 1164640 1747661 := bbase (se 3 (by rfl) ⟨327686, by rfl⟩ : syracuseStep 1747661 = 655373) (by norm_num)
theorem B1747685 : Blo 1164640 1747685 := bbase (se 4 (by rfl) ⟨163845, by rfl⟩ : syracuseStep 1747685 = 327691) (by norm_num)
theorem B2624237 : Blo 1164640 2624237 := bbase (se 3 (by rfl) ⟨492044, by rfl⟩ : syracuseStep 2624237 = 984089) (by norm_num)
theorem B1747709 : Blo 1164640 1747709 := bbase (se 3 (by rfl) ⟨327695, by rfl⟩ : syracuseStep 1747709 = 655391) (by norm_num)
theorem B1747733 : Blo 1164640 1747733 := bbase (se 6 (by rfl) ⟨40962, by rfl⟩ : syracuseStep 1747733 = 81925) (by norm_num)
theorem B1747757 : Blo 1164640 1747757 := bbase (se 3 (by rfl) ⟨327704, by rfl⟩ : syracuseStep 1747757 = 655409) (by norm_num)
theorem B2624309 : Blo 1164640 2624309 := bbase (se 5 (by rfl) ⟨123014, by rfl⟩ : syracuseStep 2624309 = 246029) (by norm_num)
theorem B1747781 : Blo 1164640 1747781 := bbase (se 4 (by rfl) ⟨163854, by rfl⟩ : syracuseStep 1747781 = 327709) (by norm_num)
theorem B1747805 : Blo 1164640 1747805 := bbase (se 3 (by rfl) ⟨327713, by rfl⟩ : syracuseStep 1747805 = 655427) (by norm_num)
theorem B2657141 : Blo 1164640 2657141 := bbase (se 5 (by rfl) ⟨124553, by rfl⟩ : syracuseStep 2657141 = 249107) (by norm_num)
theorem B1747829 : Blo 1164640 1747829 := bbase (se 5 (by rfl) ⟨81929, by rfl⟩ : syracuseStep 1747829 = 163859) (by norm_num)
theorem B5901173 : Blo 1164640 5901173 := bbase (se 5 (by rfl) ⟨276617, by rfl⟩ : syracuseStep 5901173 = 553235) (by norm_num)
theorem B2624381 : Blo 1164640 2624381 := bbase (se 3 (by rfl) ⟨492071, by rfl⟩ : syracuseStep 2624381 = 984143) (by norm_num)
theorem B1747853 : Blo 1164640 1747853 := bbase (se 3 (by rfl) ⟨327722, by rfl⟩ : syracuseStep 1747853 = 655445) (by norm_num)
theorem B15944597 : Blo 1164640 15944597 := bbase (se 6 (by rfl) ⟨373701, by rfl⟩ : syracuseStep 15944597 = 747403) (by norm_num)
theorem B2952085 : Blo 1164640 2952085 := bbase (se 6 (by rfl) ⟨69189, by rfl⟩ : syracuseStep 2952085 = 138379) (by norm_num)
theorem B1747877 : Blo 1164640 1747877 := bbase (se 4 (by rfl) ⟨163863, by rfl⟩ : syracuseStep 1747877 = 327727) (by norm_num)
theorem B3935141 : Blo 1164640 3935141 := bbase (se 4 (by rfl) ⟨368919, by rfl⟩ : syracuseStep 3935141 = 737839) (by norm_num)
theorem B4549541 : Blo 1164640 4549541 := bbase (se 4 (by rfl) ⟨426519, by rfl⟩ : syracuseStep 4549541 = 853039) (by norm_num)
theorem B1747901 : Blo 1164640 1747901 := bbase (se 3 (by rfl) ⟨327731, by rfl⟩ : syracuseStep 1747901 = 655463) (by norm_num)
theorem B1747925 : Blo 1164640 1747925 := bbase (se 7 (by rfl) ⟨20483, by rfl⟩ : syracuseStep 1747925 = 40967) (by norm_num)
theorem B1747949 : Blo 1164640 1747949 := bbase (se 3 (by rfl) ⟨327740, by rfl⟩ : syracuseStep 1747949 = 655481) (by norm_num)
theorem B1747973 : Blo 1164640 1747973 := bbase (se 4 (by rfl) ⟨163872, by rfl⟩ : syracuseStep 1747973 = 327745) (by norm_num)
theorem B2952197 : Blo 1164640 2952197 := bbase (se 4 (by rfl) ⟨276768, by rfl⟩ : syracuseStep 2952197 = 553537) (by norm_num)
theorem B1747997 : Blo 1164640 1747997 := bbase (se 3 (by rfl) ⟨327749, by rfl⟩ : syracuseStep 1747997 = 655499) (by norm_num)
theorem B1748021 : Blo 1164640 1748021 := bbase (se 5 (by rfl) ⟨81938, by rfl⟩ : syracuseStep 1748021 = 163877) (by norm_num)
theorem B1748045 : Blo 1164640 1748045 := bbase (se 3 (by rfl) ⟨327758, by rfl⟩ : syracuseStep 1748045 = 655517) (by norm_num)
theorem B1748069 : Blo 1164640 1748069 := bbase (se 4 (by rfl) ⟨163881, by rfl⟩ : syracuseStep 1748069 = 327763) (by norm_num)
theorem B1748093 : Blo 1164640 1748093 := bbase (se 3 (by rfl) ⟨327767, by rfl⟩ : syracuseStep 1748093 = 655535) (by norm_num)
theorem B1748117 : Blo 1164640 1748117 := bbase (se 6 (by rfl) ⟨40971, by rfl⟩ : syracuseStep 1748117 = 81943) (by norm_num)
theorem B1748141 : Blo 1164640 1748141 := bbase (se 3 (by rfl) ⟨327776, by rfl⟩ : syracuseStep 1748141 = 655553) (by norm_num)
theorem B1748165 : Blo 1164640 1748165 := bbase (se 4 (by rfl) ⟨163890, by rfl⟩ : syracuseStep 1748165 = 327781) (by norm_num)
theorem B2952389 : Blo 1164640 2952389 := bbase (se 4 (by rfl) ⟨276786, by rfl⟩ : syracuseStep 2952389 = 553573) (by norm_num)
theorem B1748189 : Blo 1164640 1748189 := bbase (se 3 (by rfl) ⟨327785, by rfl⟩ : syracuseStep 1748189 = 655571) (by norm_num)
theorem B5115109 : Blo 1164640 5115109 := bbase (se 4 (by rfl) ⟨479541, by rfl⟩ : syracuseStep 5115109 = 959083) (by norm_num)
theorem B1748213 : Blo 1164640 1748213 := bbase (se 5 (by rfl) ⟨81947, by rfl⟩ : syracuseStep 1748213 = 163895) (by norm_num)
theorem B1748237 : Blo 1164640 1748237 := bbase (se 3 (by rfl) ⟨327794, by rfl⟩ : syracuseStep 1748237 = 655589) (by norm_num)
theorem B1748261 : Blo 1164640 1748261 := bbase (se 4 (by rfl) ⟨163899, by rfl⟩ : syracuseStep 1748261 = 327799) (by norm_num)
theorem B1748285 : Blo 1164640 1748285 := bbase (se 3 (by rfl) ⟨327803, by rfl⟩ : syracuseStep 1748285 = 655607) (by norm_num)
theorem B1748309 : Blo 1164640 1748309 := bbase (se 11 (by rfl) ⟨1280, by rfl⟩ : syracuseStep 1748309 = 2561) (by norm_num)
theorem B3935573 : Blo 1164640 3935573 := bbase (se 11 (by rfl) ⟨2882, by rfl⟩ : syracuseStep 3935573 = 5765) (by norm_num)
theorem B1748333 : Blo 1164640 1748333 := bbase (se 3 (by rfl) ⟨327812, by rfl⟩ : syracuseStep 1748333 = 655625) (by norm_num)
theorem B1748357 : Blo 1164640 1748357 := bbase (se 4 (by rfl) ⟨163908, by rfl⟩ : syracuseStep 1748357 = 327817) (by norm_num)
theorem B1748381 : Blo 1164640 1748381 := bbase (se 3 (by rfl) ⟨327821, by rfl⟩ : syracuseStep 1748381 = 655643) (by norm_num)
theorem B1748405 : Blo 1164640 1748405 := bbase (se 5 (by rfl) ⟨81956, by rfl⟩ : syracuseStep 1748405 = 163913) (by norm_num)
theorem B1748429 : Blo 1164640 1748429 := bbase (se 3 (by rfl) ⟨327830, by rfl⟩ : syracuseStep 1748429 = 655661) (by norm_num)
theorem B4197845 : Blo 1164640 4197845 := bbase (se 7 (by rfl) ⟨49193, by rfl⟩ : syracuseStep 4197845 = 98387) (by norm_num)
theorem B1658333 : Blo 1164640 1658333 := bbase (se 3 (by rfl) ⟨310937, by rfl⟩ : syracuseStep 1658333 = 621875) (by norm_num)
theorem B1748453 : Blo 1164640 1748453 := bbase (se 4 (by rfl) ⟨163917, by rfl⟩ : syracuseStep 1748453 = 327835) (by norm_num)
theorem B1748477 : Blo 1164640 1748477 := bbase (se 3 (by rfl) ⟨327839, by rfl⟩ : syracuseStep 1748477 = 655679) (by norm_num)
theorem B1748501 : Blo 1164640 1748501 := bbase (se 6 (by rfl) ⟨40980, by rfl⟩ : syracuseStep 1748501 = 81961) (by norm_num)
theorem B1748525 : Blo 1164640 1748525 := bbase (se 3 (by rfl) ⟨327848, by rfl⟩ : syracuseStep 1748525 = 655697) (by norm_num)
theorem B1748549 : Blo 1164640 1748549 := bbase (se 4 (by rfl) ⟨163926, by rfl⟩ : syracuseStep 1748549 = 327853) (by norm_num)
theorem B1748573 : Blo 1164640 1748573 := bbase (se 3 (by rfl) ⟨327857, by rfl⟩ : syracuseStep 1748573 = 655715) (by norm_num)
theorem B4976245 : Blo 1164640 4976245 := bbase (se 5 (by rfl) ⟨233261, by rfl⟩ : syracuseStep 4976245 = 466523) (by norm_num)
theorem B1748597 : Blo 1164640 1748597 := bbase (se 5 (by rfl) ⟨81965, by rfl⟩ : syracuseStep 1748597 = 163931) (by norm_num)
theorem B3321461 : Blo 1164640 3321461 := bbase (se 5 (by rfl) ⟨155693, by rfl⟩ : syracuseStep 3321461 = 311387) (by norm_num)
theorem B1748621 : Blo 1164640 1748621 := bbase (se 3 (by rfl) ⟨327866, by rfl⟩ : syracuseStep 1748621 = 655733) (by norm_num)
theorem B1748645 : Blo 1164640 1748645 := bbase (se 4 (by rfl) ⟨163935, by rfl⟩ : syracuseStep 1748645 = 327871) (by norm_num)
theorem B2657981 : Blo 1164640 2657981 := bbase (se 3 (by rfl) ⟨498371, by rfl⟩ : syracuseStep 2657981 = 996743) (by norm_num)
theorem B1748669 : Blo 1164640 1748669 := bbase (se 3 (by rfl) ⟨327875, by rfl⟩ : syracuseStep 1748669 = 655751) (by norm_num)
theorem B1748693 : Blo 1164640 1748693 := bbase (se 7 (by rfl) ⟨20492, by rfl⟩ : syracuseStep 1748693 = 40985) (by norm_num)
theorem B1748717 : Blo 1164640 1748717 := bbase (se 3 (by rfl) ⟨327884, by rfl⟩ : syracuseStep 1748717 = 655769) (by norm_num)
theorem B1748741 : Blo 1164640 1748741 := bbase (se 4 (by rfl) ⟨163944, by rfl⟩ : syracuseStep 1748741 = 327889) (by norm_num)
theorem B3936005 : Blo 1164640 3936005 := bbase (se 4 (by rfl) ⟨369000, by rfl⟩ : syracuseStep 3936005 = 738001) (by norm_num)
theorem B1748765 : Blo 1164640 1748765 := bbase (se 3 (by rfl) ⟨327893, by rfl⟩ : syracuseStep 1748765 = 655787) (by norm_num)
theorem B1748789 : Blo 1164640 1748789 := bbase (se 5 (by rfl) ⟨81974, by rfl⟩ : syracuseStep 1748789 = 163949) (by norm_num)
theorem B1748813 : Blo 1164640 1748813 := bbase (se 3 (by rfl) ⟨327902, by rfl⟩ : syracuseStep 1748813 = 655805) (by norm_num)
theorem B2838365 : Blo 1164640 2838365 := bbase (se 3 (by rfl) ⟨532193, by rfl⟩ : syracuseStep 2838365 = 1064387) (by norm_num)
theorem B1748837 : Blo 1164640 1748837 := bbase (se 4 (by rfl) ⟨163953, by rfl⟩ : syracuseStep 1748837 = 327907) (by norm_num)
theorem B1748861 : Blo 1164640 1748861 := bbase (se 3 (by rfl) ⟨327911, by rfl⟩ : syracuseStep 1748861 = 655823) (by norm_num)
theorem B1748885 : Blo 1164640 1748885 := bbase (se 6 (by rfl) ⟨40989, by rfl⟩ : syracuseStep 1748885 = 81979) (by norm_num)
theorem B2101157 : Blo 1164640 2101157 := bbase (se 4 (by rfl) ⟨196983, by rfl⟩ : syracuseStep 2101157 = 393967) (by norm_num)
theorem B1748909 : Blo 1164640 1748909 := bbase (se 3 (by rfl) ⟨327920, by rfl⟩ : syracuseStep 1748909 = 655841) (by norm_num)
theorem B1748933 : Blo 1164640 1748933 := bbase (se 4 (by rfl) ⟨163962, by rfl⟩ : syracuseStep 1748933 = 327925) (by norm_num)
theorem B1748957 : Blo 1164640 1748957 := bbase (se 3 (by rfl) ⟨327929, by rfl⟩ : syracuseStep 1748957 = 655859) (by norm_num)
theorem B2101229 : Blo 1164640 2101229 := bbase (se 3 (by rfl) ⟨393980, by rfl⟩ : syracuseStep 2101229 = 787961) (by norm_num)
theorem B1748981 : Blo 1164640 1748981 := bbase (se 5 (by rfl) ⟨81983, by rfl⟩ : syracuseStep 1748981 = 163967) (by norm_num)
theorem B1658885 : Blo 1164640 1658885 := bbase (se 4 (by rfl) ⟨155520, by rfl⟩ : syracuseStep 1658885 = 311041) (by norm_num)
theorem B1749005 : Blo 1164640 1749005 := bbase (se 3 (by rfl) ⟨327938, by rfl⟩ : syracuseStep 1749005 = 655877) (by norm_num)
theorem B2363413 : Blo 1164640 2363413 := bbase (se 6 (by rfl) ⟨55392, by rfl⟩ : syracuseStep 2363413 = 110785) (by norm_num)
theorem B3543077 : Blo 1164640 3543077 := bbase (se 4 (by rfl) ⟨332163, by rfl⟩ : syracuseStep 3543077 = 664327) (by norm_num)
theorem B1749029 : Blo 1164640 1749029 := bbase (se 4 (by rfl) ⟨163971, by rfl⟩ : syracuseStep 1749029 = 327943) (by norm_num)
theorem B1749053 : Blo 1164640 1749053 := bbase (se 3 (by rfl) ⟨327947, by rfl⟩ : syracuseStep 1749053 = 655895) (by norm_num)
theorem B1749077 : Blo 1164640 1749077 := bbase (se 8 (by rfl) ⟨10248, by rfl⟩ : syracuseStep 1749077 = 20497) (by norm_num)
theorem B1749101 : Blo 1164640 1749101 := bbase (se 3 (by rfl) ⟨327956, by rfl⟩ : syracuseStep 1749101 = 655913) (by norm_num)
theorem B2101373 : Blo 1164640 2101373 := bbase (se 3 (by rfl) ⟨394007, by rfl⟩ : syracuseStep 2101373 = 788015) (by norm_num)
theorem B5902469 : Blo 1164640 5902469 := bbase (se 4 (by rfl) ⟨553356, by rfl⟩ : syracuseStep 5902469 = 1106713) (by norm_num)
theorem B1749125 : Blo 1164640 1749125 := bbase (se 4 (by rfl) ⟨163980, by rfl⟩ : syracuseStep 1749125 = 327961) (by norm_num)
theorem B1749149 : Blo 1164640 1749149 := bbase (se 3 (by rfl) ⟨327965, by rfl⟩ : syracuseStep 1749149 = 655931) (by norm_num)
theorem B1749173 : Blo 1164640 1749173 := bbase (se 5 (by rfl) ⟨81992, by rfl⟩ : syracuseStep 1749173 = 163985) (by norm_num)
theorem B3936437 : Blo 1164640 3936437 := bbase (se 5 (by rfl) ⟨184520, by rfl⟩ : syracuseStep 3936437 = 369041) (by norm_num)
theorem B1749197 : Blo 1164640 1749197 := bbase (se 3 (by rfl) ⟨327974, by rfl⟩ : syracuseStep 1749197 = 655949) (by norm_num)
theorem B1749221 : Blo 1164640 1749221 := bbase (se 4 (by rfl) ⟨163989, by rfl⟩ : syracuseStep 1749221 = 327979) (by norm_num)
theorem B1749245 : Blo 1164640 1749245 := bbase (se 3 (by rfl) ⟨327983, by rfl⟩ : syracuseStep 1749245 = 655967) (by norm_num)
theorem B9957653 : Blo 1164640 9957653 := bbase (se 6 (by rfl) ⟨233382, by rfl⟩ : syracuseStep 9957653 = 466765) (by norm_num)
theorem B6639893 : Blo 1164640 6639893 := bbase (se 6 (by rfl) ⟨155622, by rfl⟩ : syracuseStep 6639893 = 311245) (by norm_num)
theorem B1749269 : Blo 1164640 1749269 := bbase (se 6 (by rfl) ⟨40998, by rfl⟩ : syracuseStep 1749269 = 81997) (by norm_num)
theorem B4428053 : Blo 1164640 4428053 := bbase (se 6 (by rfl) ⟨103782, by rfl⟩ : syracuseStep 4428053 = 207565) (by norm_num)
theorem B1749293 : Blo 1164640 1749293 := bbase (se 3 (by rfl) ⟨327992, by rfl⟩ : syracuseStep 1749293 = 655985) (by norm_num)
theorem B1749317 : Blo 1164640 1749317 := bbase (se 4 (by rfl) ⟨163998, by rfl⟩ : syracuseStep 1749317 = 327997) (by norm_num)
theorem B1749341 : Blo 1164640 1749341 := bbase (se 3 (by rfl) ⟨328001, by rfl⟩ : syracuseStep 1749341 = 656003) (by norm_num)
theorem B1995101 : Blo 1164640 1995101 := bbase (se 3 (by rfl) ⟨374081, by rfl⟩ : syracuseStep 1995101 = 748163) (by norm_num)
theorem B1749365 : Blo 1164640 1749365 := bbase (se 5 (by rfl) ⟨82001, by rfl⟩ : syracuseStep 1749365 = 164003) (by norm_num)
theorem B1749389 : Blo 1164640 1749389 := bbase (se 3 (by rfl) ⟨328010, by rfl⟩ : syracuseStep 1749389 = 656021) (by norm_num)
theorem B1749413 : Blo 1164640 1749413 := bbase (se 4 (by rfl) ⟨164007, by rfl⟩ : syracuseStep 1749413 = 328015) (by norm_num)
theorem B1438133 : Blo 1164640 1438133 := bbase (se 5 (by rfl) ⟨67412, by rfl⟩ : syracuseStep 1438133 = 134825) (by norm_num)
theorem B1749437 : Blo 1164640 1749437 := bbase (se 3 (by rfl) ⟨328019, by rfl⟩ : syracuseStep 1749437 = 656039) (by norm_num)
theorem B4198853 : Blo 1164640 4198853 := bbase (se 4 (by rfl) ⟨393642, by rfl⟩ : syracuseStep 4198853 = 787285) (by norm_num)
theorem B1749461 : Blo 1164640 1749461 := bbase (se 7 (by rfl) ⟨20501, by rfl⟩ : syracuseStep 1749461 = 41003) (by norm_num)
theorem B1749485 : Blo 1164640 1749485 := bbase (se 3 (by rfl) ⟨328028, by rfl⟩ : syracuseStep 1749485 = 656057) (by norm_num)
theorem B1749509 : Blo 1164640 1749509 := bbase (se 4 (by rfl) ⟨164016, by rfl⟩ : syracuseStep 1749509 = 328033) (by norm_num)
theorem B1749533 : Blo 1164640 1749533 := bbase (se 3 (by rfl) ⟨328037, by rfl⟩ : syracuseStep 1749533 = 656075) (by norm_num)
theorem B4428341 : Blo 1164640 4428341 := bbase (se 5 (by rfl) ⟨207578, by rfl⟩ : syracuseStep 4428341 = 415157) (by norm_num)
theorem B1749557 : Blo 1164640 1749557 := bbase (se 5 (by rfl) ⟨82010, by rfl⟩ : syracuseStep 1749557 = 164021) (by norm_num)
theorem B1749581 : Blo 1164640 1749581 := bbase (se 3 (by rfl) ⟨328046, by rfl⟩ : syracuseStep 1749581 = 656093) (by norm_num)
theorem B1659637 : Blo 1164640 1659637 := bbase (se 5 (by rfl) ⟨77795, by rfl⟩ : syracuseStep 1659637 = 155591) (by norm_num)
theorem B1365017 : Blo 1164640 1365017 := bbase (se 2 (by rfl) ⟨511881, by rfl⟩ : syracuseStep 1365017 = 1023763) (by norm_num)
theorem B2798621 : Blo 1164640 2798621 := bbase (se 3 (by rfl) ⟨524741, by rfl⟩ : syracuseStep 2798621 = 1049483) (by norm_num)
theorem B4977733 : Blo 1164640 4977733 := bbase (se 4 (by rfl) ⟨466662, by rfl⟩ : syracuseStep 4977733 = 933325) (by norm_num)
theorem B4977749 : Blo 1164640 4977749 := bbase (se 8 (by rfl) ⟨29166, by rfl⟩ : syracuseStep 4977749 = 58333) (by norm_num)
theorem B6304981 : Blo 1164640 6304981 := bbase (se 7 (by rfl) ⟨73886, by rfl⟩ : syracuseStep 6304981 = 147773) (by norm_num)
theorem B3151237 : Blo 1164640 3151237 := bbase (se 4 (by rfl) ⟨295428, by rfl⟩ : syracuseStep 3151237 = 590857) (by norm_num)
theorem B5903765 : Blo 1164640 5903765 := bbase (se 6 (by rfl) ⟨138369, by rfl⟩ : syracuseStep 5903765 = 276739) (by norm_num)
theorem B7468469 : Blo 1164640 7468469 := bbase (se 5 (by rfl) ⟨350084, by rfl⟩ : syracuseStep 7468469 = 700169) (by norm_num)
theorem B2799053 : Blo 1164640 2799053 := bbase (se 3 (by rfl) ⟨524822, by rfl⟩ : syracuseStep 2799053 = 1049645) (by norm_num)
theorem B2487773 : Blo 1164640 2487773 := bbase (se 3 (by rfl) ⟨466457, by rfl⟩ : syracuseStep 2487773 = 932915) (by norm_num)
theorem B2487781 : Blo 1164640 2487781 := bbase (se 4 (by rfl) ⟨233229, by rfl⟩ : syracuseStep 2487781 = 466459) (by norm_num)
theorem B1660429 : Blo 1164640 1660429 := bbase (se 3 (by rfl) ⟨311330, by rfl⟩ : syracuseStep 1660429 = 622661) (by norm_num)
theorem B2660125 : Blo 1164640 2660125 := bbase (se 3 (by rfl) ⟨498773, by rfl⟩ : syracuseStep 2660125 = 997547) (by norm_num)
theorem B11196245 : Blo 1164640 11196245 := bbase (se 9 (by rfl) ⟨32801, by rfl⟩ : syracuseStep 11196245 = 65603) (by norm_num)
theorem B8853461 : Blo 1164640 8853461 := bbase (se 7 (by rfl) ⟨103751, by rfl⟩ : syracuseStep 8853461 = 207503) (by norm_num)
theorem B3545093 : Blo 1164640 3545093 := bbase (se 4 (by rfl) ⟨332352, by rfl⟩ : syracuseStep 3545093 = 664705) (by norm_num)
theorem B2799677 : Blo 1164640 2799677 := bbase (se 3 (by rfl) ⟨524939, by rfl⟩ : syracuseStep 2799677 = 1049879) (by norm_num)
theorem B3545189 : Blo 1164640 3545189 := bbase (se 4 (by rfl) ⟨332361, by rfl⟩ : syracuseStep 3545189 = 664723) (by norm_num)
theorem B1366121 : Blo 1164640 1366121 := bbase (se 2 (by rfl) ⟨512295, by rfl⟩ : syracuseStep 1366121 = 1024591) (by norm_num)
theorem B2021573 : Blo 1164640 2021573 := bbase (se 4 (by rfl) ⟨189522, by rfl⟩ : syracuseStep 2021573 = 379045) (by norm_num)
theorem B1865933 : Blo 1164640 1865933 := bbase (se 3 (by rfl) ⟨349862, by rfl⟩ : syracuseStep 1865933 = 699725) (by norm_num)
theorem B8845685 : Blo 1164640 8845685 := bbase (se 5 (by rfl) ⟨414641, by rfl⟩ : syracuseStep 8845685 = 829283) (by norm_num)
theorem B3733877 : Blo 1164640 3733877 := bbase (se 5 (by rfl) ⟨175025, by rfl⟩ : syracuseStep 3733877 = 350051) (by norm_num)
theorem B2128285 : Blo 1164640 2128285 := bbase (se 3 (by rfl) ⟨399053, by rfl⟩ : syracuseStep 2128285 = 798107) (by norm_num)
theorem B4422053 : Blo 1164640 4422053 := bbase (se 4 (by rfl) ⟨414567, by rfl⟩ : syracuseStep 4422053 = 829135) (by norm_num)
theorem B6642101 : Blo 1164640 6642101 := bbase (se 5 (by rfl) ⟨311348, by rfl⟩ : syracuseStep 6642101 = 622697) (by norm_num)
theorem B5601797 : Blo 1164640 5601797 := bbase (se 4 (by rfl) ⟨525168, by rfl⟩ : syracuseStep 5601797 = 1050337) (by norm_num)
theorem B2521621 : Blo 1164640 2521621 := bbase (se 6 (by rfl) ⟨59100, by rfl⟩ : syracuseStep 2521621 = 118201) (by norm_num)
theorem B2488909 : Blo 1164640 2488909 := bbase (se 3 (by rfl) ⟨466670, by rfl⟩ : syracuseStep 2488909 = 933341) (by norm_num)
theorem B3930821 : Blo 1164640 3930821 := bbase (se 4 (by rfl) ⟨368514, by rfl⟩ : syracuseStep 3930821 = 737029) (by norm_num)
theorem B2489285 : Blo 1164640 2489285 := bbase (se 4 (by rfl) ⟨233370, by rfl⟩ : syracuseStep 2489285 = 466741) (by norm_num)
theorem B4488149 : Blo 1164640 4488149 := bbase (se 7 (by rfl) ⟨52595, by rfl⟩ : syracuseStep 4488149 = 105191) (by norm_num)
theorem B1399781 : Blo 1164640 1399781 := bbase (se 4 (by rfl) ⟨131229, by rfl⟩ : syracuseStep 1399781 = 262459) (by norm_num)
theorem B5897285 : Blo 1164640 5897285 := bbase (se 4 (by rfl) ⟨552870, by rfl⟩ : syracuseStep 5897285 = 1105741) (by norm_num)
theorem B2620493 : Blo 1164640 2620493 := bbase (se 3 (by rfl) ⟨491342, by rfl⟩ : syracuseStep 2620493 = 982685) (by norm_num)
theorem B2948197 : Blo 1164640 2948197 := bbase (se 4 (by rfl) ⟨276393, by rfl⟩ : syracuseStep 2948197 = 552787) (by norm_num)
theorem B3931253 : Blo 1164640 3931253 := bbase (se 5 (by rfl) ⟨184277, by rfl⟩ : syracuseStep 3931253 = 368555) (by norm_num)
theorem B2620565 : Blo 1164640 2620565 := bbase (se 6 (by rfl) ⟨61419, by rfl⟩ : syracuseStep 2620565 = 122839) (by norm_num)
theorem B1312177 : Blo 1164640 1312177 := bbase (se 2 (by rfl) ⟨492066, by rfl⟩ : syracuseStep 1312177 = 984133) (by norm_num)
theorem B1244369 : Blo 1164640 1244369 := bbase (se 2 (by rfl) ⟨466638, by rfl⟩ : syracuseStep 1244369 = 933277) (by norm_num)
theorem B2948309 : Blo 1164640 2948309 := bbase (se 7 (by rfl) ⟨34550, by rfl⟩ : syracuseStep 2948309 = 69101) (by norm_num)
theorem B2620637 : Blo 1164640 2620637 := bbase (se 3 (by rfl) ⟨491369, by rfl⟩ : syracuseStep 2620637 = 982739) (by norm_num)
theorem B1400041 : Blo 1164640 1400041 := bbase (se 2 (by rfl) ⟨525015, by rfl⟩ : syracuseStep 1400041 = 1050031) (by norm_num)
theorem B7093493 : Blo 1164640 7093493 := bbase (se 5 (by rfl) ⟨332507, by rfl⟩ : syracuseStep 7093493 = 665015) (by norm_num)
theorem B7462165 : Blo 1164640 7462165 := bbase (se 6 (by rfl) ⟨174894, by rfl⟩ : syracuseStep 7462165 = 349789) (by norm_num)
theorem B2620709 : Blo 1164640 2620709 := bbase (se 4 (by rfl) ⟨245691, by rfl⟩ : syracuseStep 2620709 = 491383) (by norm_num)
theorem B4980005 : Blo 1164640 4980005 := bbase (se 4 (by rfl) ⟨466875, by rfl⟩ : syracuseStep 4980005 = 933751) (by norm_num)
theorem B2211133 : Blo 1164640 2211133 := bbase (se 3 (by rfl) ⟨414587, by rfl⟩ : syracuseStep 2211133 = 829175) (by norm_num)
theorem B1965397 : Blo 1164640 1965397 := bbase (se 11 (by rfl) ⟨1439, by rfl⟩ : syracuseStep 1965397 = 2879) (by norm_num)
theorem B2620781 : Blo 1164640 2620781 := bbase (se 3 (by rfl) ⟨491396, by rfl⟩ : syracuseStep 2620781 = 982793) (by norm_num)
theorem B9444757 : Blo 1164640 9444757 := bbase (se 6 (by rfl) ⟨221361, by rfl⟩ : syracuseStep 9444757 = 442723) (by norm_num)
theorem B2948501 : Blo 1164640 2948501 := bbase (se 6 (by rfl) ⟨69105, by rfl⟩ : syracuseStep 2948501 = 138211) (by norm_num)
theorem B1400233 : Blo 1164640 1400233 := bbase (se 2 (by rfl) ⟨525087, by rfl⟩ : syracuseStep 1400233 = 1050175) (by norm_num)
theorem B1965485 : Blo 1164640 1965485 := bbase (se 3 (by rfl) ⟨368528, by rfl⟩ : syracuseStep 1965485 = 737057) (by norm_num)
theorem B2620853 : Blo 1164640 2620853 := bbase (se 5 (by rfl) ⟨122852, by rfl⟩ : syracuseStep 2620853 = 245705) (by norm_num)
theorem B1400257 : Blo 1164640 1400257 := bbase (se 2 (by rfl) ⟨525096, by rfl⟩ : syracuseStep 1400257 = 1050193) (by norm_num)
theorem B1400261 : Blo 1164640 1400261 := bbase (se 4 (by rfl) ⟨131274, by rfl⟩ : syracuseStep 1400261 = 262549) (by norm_num)
theorem B2211293 : Blo 1164640 2211293 := bbase (se 3 (by rfl) ⟨414617, by rfl⟩ : syracuseStep 2211293 = 829235) (by norm_num)
theorem B1474033 : Blo 1164640 1474033 := bbase (se 2 (by rfl) ⟨552762, by rfl⟩ : syracuseStep 1474033 = 1105525) (by norm_num)
theorem B2620925 : Blo 1164640 2620925 := bbase (se 3 (by rfl) ⟨491423, by rfl⟩ : syracuseStep 2620925 = 982847) (by norm_num)
theorem B3988997 : Blo 1164640 3988997 := bbase (se 4 (by rfl) ⟨373968, by rfl⟩ : syracuseStep 3988997 = 747937) (by norm_num)
theorem B3317269 : Blo 1164640 3317269 := bbase (se 6 (by rfl) ⟨77748, by rfl⟩ : syracuseStep 3317269 = 155497) (by norm_num)
theorem B1310233 : Blo 1164640 1310233 := bbase (se 2 (by rfl) ⟨491337, by rfl⟩ : syracuseStep 1310233 = 982675) (by norm_num)
theorem B3931685 : Blo 1164640 3931685 := bbase (se 4 (by rfl) ⟨368595, by rfl⟩ : syracuseStep 3931685 = 737191) (by norm_num)
theorem B1965613 : Blo 1164640 1965613 := bbase (se 3 (by rfl) ⟨368552, by rfl⟩ : syracuseStep 1965613 = 737105) (by norm_num)
theorem B1310269 : Blo 1164640 1310269 := bbase (se 3 (by rfl) ⟨245675, by rfl⟩ : syracuseStep 1310269 = 491351) (by norm_num)
theorem B2620997 : Blo 1164640 2620997 := bbase (se 4 (by rfl) ⟨245718, by rfl⟩ : syracuseStep 2620997 = 491437) (by norm_num)
theorem B1474129 : Blo 1164640 1474129 := bbase (se 2 (by rfl) ⟨552798, by rfl⟩ : syracuseStep 1474129 = 1105597) (by norm_num)
theorem B1867349 : Blo 1164640 1867349 := bbase (se 8 (by rfl) ⟨10941, by rfl⟩ : syracuseStep 1867349 = 21883) (by norm_num)
theorem B1310305 : Blo 1164640 1310305 := bbase (se 2 (by rfl) ⟨491364, by rfl⟩ : syracuseStep 1310305 = 982729) (by norm_num)
theorem B2211437 : Blo 1164640 2211437 := bbase (se 3 (by rfl) ⟨414644, by rfl⟩ : syracuseStep 2211437 = 829289) (by norm_num)
theorem B1310341 : Blo 1164640 1310341 := bbase (se 4 (by rfl) ⟨122844, by rfl⟩ : syracuseStep 1310341 = 245689) (by norm_num)
theorem B1965701 : Blo 1164640 1965701 := bbase (se 4 (by rfl) ⟨184284, by rfl⟩ : syracuseStep 1965701 = 368569) (by norm_num)
theorem B2621069 : Blo 1164640 2621069 := bbase (se 3 (by rfl) ⟨491450, by rfl⟩ : syracuseStep 2621069 = 982901) (by norm_num)
theorem B1244813 : Blo 1164640 1244813 := bbase (se 3 (by rfl) ⟨233402, by rfl⟩ : syracuseStep 1244813 = 466805) (by norm_num)
theorem B1310377 : Blo 1164640 1310377 := bbase (se 2 (by rfl) ⟨491391, by rfl⟩ : syracuseStep 1310377 = 982783) (by norm_num)
theorem B3317429 : Blo 1164640 3317429 := bbase (se 5 (by rfl) ⟨155504, by rfl⟩ : syracuseStep 3317429 = 311009) (by norm_num)
theorem B1310413 : Blo 1164640 1310413 := bbase (se 3 (by rfl) ⟨245702, by rfl⟩ : syracuseStep 1310413 = 491405) (by norm_num)
theorem B2621141 : Blo 1164640 2621141 := bbase (se 7 (by rfl) ⟨30716, by rfl⟩ : syracuseStep 2621141 = 61433) (by norm_num)
theorem B2948845 : Blo 1164640 2948845 := bbase (se 3 (by rfl) ⟨552908, by rfl⟩ : syracuseStep 2948845 = 1105817) (by norm_num)
theorem B1310449 : Blo 1164640 1310449 := bbase (se 2 (by rfl) ⟨491418, by rfl⟩ : syracuseStep 1310449 = 982837) (by norm_num)
theorem B1474301 : Blo 1164640 1474301 := bbase (se 3 (by rfl) ⟨276431, by rfl⟩ : syracuseStep 1474301 = 552863) (by norm_num)
theorem B1965829 : Blo 1164640 1965829 := bbase (se 4 (by rfl) ⟨184296, by rfl⟩ : syracuseStep 1965829 = 368593) (by norm_num)
theorem B1310485 : Blo 1164640 1310485 := bbase (se 6 (by rfl) ⟨30714, by rfl⟩ : syracuseStep 1310485 = 61429) (by norm_num)
theorem B2621213 : Blo 1164640 2621213 := bbase (se 3 (by rfl) ⟨491477, by rfl⟩ : syracuseStep 2621213 = 982955) (by norm_num)
theorem B1474357 : Blo 1164640 1474357 := bbase (se 5 (by rfl) ⟨69110, by rfl⟩ : syracuseStep 1474357 = 138221) (by norm_num)
theorem B1867573 : Blo 1164640 1867573 := bbase (se 5 (by rfl) ⟨87542, by rfl⟩ : syracuseStep 1867573 = 175085) (by norm_num)
theorem B1310521 : Blo 1164640 1310521 := bbase (se 2 (by rfl) ⟨491445, by rfl⟩ : syracuseStep 1310521 = 982891) (by norm_num)
theorem B1310557 : Blo 1164640 1310557 := bbase (se 3 (by rfl) ⟨245729, by rfl⟩ : syracuseStep 1310557 = 491459) (by norm_num)
theorem B1965917 : Blo 1164640 1965917 := bbase (se 3 (by rfl) ⟨368609, by rfl⟩ : syracuseStep 1965917 = 737219) (by norm_num)
theorem B2948957 : Blo 1164640 2948957 := bbase (se 3 (by rfl) ⟨552929, by rfl⟩ : syracuseStep 2948957 = 1105859) (by norm_num)
theorem B2621285 : Blo 1164640 2621285 := bbase (se 4 (by rfl) ⟨245745, by rfl⟩ : syracuseStep 2621285 = 491491) (by norm_num)
theorem B3030901 : Blo 1164640 3030901 := bbase (se 5 (by rfl) ⟨142073, by rfl⟩ : syracuseStep 3030901 = 284147) (by norm_num)
theorem B1310593 : Blo 1164640 1310593 := bbase (se 2 (by rfl) ⟨491472, by rfl⟩ : syracuseStep 1310593 = 982945) (by norm_num)
theorem B1245061 : Blo 1164640 1245061 := bbase (se 4 (by rfl) ⟨116724, by rfl⟩ : syracuseStep 1245061 = 233449) (by norm_num)
theorem B2211725 : Blo 1164640 2211725 := bbase (se 3 (by rfl) ⟨414698, by rfl⟩ : syracuseStep 2211725 = 829397) (by norm_num)
theorem B1474453 : Blo 1164640 1474453 := bbase (se 6 (by rfl) ⟨34557, by rfl⟩ : syracuseStep 1474453 = 69115) (by norm_num)
theorem B1310629 : Blo 1164640 1310629 := bbase (se 4 (by rfl) ⟨122871, by rfl⟩ : syracuseStep 1310629 = 245743) (by norm_num)
theorem B3317669 : Blo 1164640 3317669 := bbase (se 4 (by rfl) ⟨311031, by rfl⟩ : syracuseStep 3317669 = 622063) (by norm_num)
theorem B2621357 : Blo 1164640 2621357 := bbase (se 3 (by rfl) ⟨491504, by rfl⟩ : syracuseStep 2621357 = 983009) (by norm_num)
theorem B1400761 : Blo 1164640 1400761 := bbase (se 2 (by rfl) ⟨525285, by rfl⟩ : syracuseStep 1400761 = 1050571) (by norm_num)
theorem B1310665 : Blo 1164640 1310665 := bbase (se 2 (by rfl) ⟨491499, by rfl⟩ : syracuseStep 1310665 = 982999) (by norm_num)
theorem B3932117 : Blo 1164640 3932117 := bbase (se 7 (by rfl) ⟨46079, by rfl⟩ : syracuseStep 3932117 = 92159) (by norm_num)
theorem B1966045 : Blo 1164640 1966045 := bbase (se 3 (by rfl) ⟨368633, by rfl⟩ : syracuseStep 1966045 = 737267) (by norm_num)
theorem B1310701 : Blo 1164640 1310701 := bbase (se 3 (by rfl) ⟨245756, by rfl⟩ : syracuseStep 1310701 = 491513) (by norm_num)
theorem B2621429 : Blo 1164640 2621429 := bbase (se 5 (by rfl) ⟨122879, by rfl⟩ : syracuseStep 2621429 = 245759) (by norm_num)
theorem B4423693 : Blo 1164640 4423693 := bstep (se 3 (by rfl) ⟨829442, by rfl⟩ : syracuseStep 4423693 = 1658885) B1658885
theorem B9453581 : Blo 1164640 9453581 := bstep (se 3 (by rfl) ⟨1772546, by rfl⟩ : syracuseStep 9453581 = 3545093) B3545093
theorem B1966099 : Blo 1164640 1966099 := bstep (se 1 (by rfl) ⟨1474574, by rfl⟩ : syracuseStep 1966099 = 2949149) B2949149
theorem B1310755 : Blo 1164640 1310755 := bstep (se 1 (by rfl) ⟨983066, by rfl⟩ : syracuseStep 1310755 = 1966133) B1966133
theorem B2949169 : Blo 1164640 2949169 := bstep (se 2 (by rfl) ⟨1105938, by rfl⟩ : syracuseStep 2949169 = 2211877) B2211877
theorem B1400915 : Blo 1164640 1400915 := bstep (se 1 (by rfl) ⟨1050686, by rfl⟩ : syracuseStep 1400915 = 2101373) B2101373
theorem B7471237 : Blo 1164640 7471237 := bstep (se 4 (by rfl) ⟨700428, by rfl⟩ : syracuseStep 7471237 = 1400857) B1400857
theorem B1966241 : Blo 1164640 1966241 := bstep (se 2 (by rfl) ⟨737340, by rfl⟩ : syracuseStep 1966241 = 1474681) B1474681
theorem B3932333 : Blo 1164640 3932333 := bstep (se 3 (by rfl) ⟨737312, by rfl⟩ : syracuseStep 3932333 = 1474625) B1474625
theorem B1310899 : Blo 1164640 1310899 := bstep (se 1 (by rfl) ⟨983174, by rfl⟩ : syracuseStep 1310899 = 1966349) B1966349
theorem B3932387 : Blo 1164640 3932387 := bstep (se 1 (by rfl) ⟨2949290, by rfl⟩ : syracuseStep 3932387 = 5898581) B5898581
theorem B1474787 : Blo 1164640 1474787 := bstep (se 1 (by rfl) ⟨1106090, by rfl⟩ : syracuseStep 1474787 = 2212181) B2212181
theorem B2621681 : Blo 1164640 2621681 := bstep (se 2 (by rfl) ⟨983130, by rfl⟩ : syracuseStep 2621681 = 1966261) B1966261
theorem B2621699 : Blo 1164640 2621699 := bstep (se 1 (by rfl) ⟨1966274, by rfl⟩ : syracuseStep 2621699 = 3932549) B3932549
theorem B8847629 : Blo 1164640 8847629 := bstep (se 3 (by rfl) ⟨1658930, by rfl⟩ : syracuseStep 8847629 = 3317861) B3317861
theorem B1966369 : Blo 1164640 1966369 := bstep (se 2 (by rfl) ⟨737388, by rfl⟩ : syracuseStep 1966369 = 1474777) B1474777
theorem B2949443 : Blo 1164640 2949443 := bstep (se 1 (by rfl) ⟨2212082, by rfl⟩ : syracuseStep 2949443 = 4424165) B4424165
theorem B1966403 : Blo 1164640 1966403 := bstep (se 1 (by rfl) ⟨1474802, by rfl⟩ : syracuseStep 1966403 = 2949605) B2949605
theorem B1311043 : Blo 1164640 1311043 := bstep (se 1 (by rfl) ⟨983282, by rfl⟩ : syracuseStep 1311043 = 1966565) B1966565
theorem B3735875 : Blo 1164640 3735875 := bstep (se 1 (by rfl) ⟨2801906, by rfl⟩ : syracuseStep 3735875 = 5603813) B5603813
theorem B1966531 : Blo 1164640 1966531 := bstep (se 1 (by rfl) ⟨1474898, by rfl⟩ : syracuseStep 1966531 = 2949797) B2949797
theorem B37806533 : Blo 1164640 37806533 := bstep (se 4 (by rfl) ⟨3544362, by rfl⟩ : syracuseStep 37806533 = 7088725) B7088725
theorem B7668173 : Blo 1164640 7668173 := bstep (se 3 (by rfl) ⟨1437782, by rfl⟩ : syracuseStep 7668173 = 2875565) B2875565
theorem B1311187 : Blo 1164640 1311187 := bstep (se 1 (by rfl) ⟨983390, by rfl⟩ : syracuseStep 1311187 = 1966781) B1966781
theorem B3932657 : Blo 1164640 3932657 := bstep (se 2 (by rfl) ⟨1474746, by rfl⟩ : syracuseStep 3932657 = 2949493) B2949493
theorem B2949635 : Blo 1164640 2949635 := bstep (se 1 (by rfl) ⟨2212226, by rfl⟩ : syracuseStep 2949635 = 4424453) B4424453
theorem B2621969 : Blo 1164640 2621969 := bstep (se 2 (by rfl) ⟨983238, by rfl⟩ : syracuseStep 2621969 = 1966477) B1966477
theorem B2621987 : Blo 1164640 2621987 := bstep (se 1 (by rfl) ⟨1966490, by rfl⟩ : syracuseStep 2621987 = 3932981) B3932981
theorem B3318317 : Blo 1164640 3318317 := bstep (se 3 (by rfl) ⟨622184, by rfl⟩ : syracuseStep 3318317 = 1244369) B1244369
theorem B1966673 : Blo 1164640 1966673 := bstep (se 2 (by rfl) ⟨737502, by rfl⟩ : syracuseStep 1966673 = 1475005) B1475005
theorem B1311331 : Blo 1164640 1311331 := bstep (se 1 (by rfl) ⟨983498, by rfl⟩ : syracuseStep 1311331 = 1966997) B1966997
theorem B19923569 : Blo 1164640 19923569 := bstep (se 2 (by rfl) ⟨7471338, by rfl⟩ : syracuseStep 19923569 = 14942677) B14942677
theorem B11207281 : Blo 1164640 11207281 := bstep (se 2 (by rfl) ⟨4202730, by rfl⟩ : syracuseStep 11207281 = 8405461) B8405461
theorem B1966801 : Blo 1164640 1966801 := bstep (se 2 (by rfl) ⟨737550, by rfl⟩ : syracuseStep 1966801 = 1475101) B1475101
theorem B3318499 : Blo 1164640 3318499 := bstep (se 1 (by rfl) ⟨2488874, by rfl⟩ : syracuseStep 3318499 = 4977749) B4977749
theorem B1966835 : Blo 1164640 1966835 := bstep (se 1 (by rfl) ⟨1475126, by rfl⟩ : syracuseStep 1966835 = 2950253) B2950253
theorem B1311475 : Blo 1164640 1311475 := bstep (se 1 (by rfl) ⟨983606, by rfl⟩ : syracuseStep 1311475 = 1967213) B1967213
theorem B3318545 : Blo 1164640 3318545 := bstep (se 2 (by rfl) ⟨1244454, by rfl⟩ : syracuseStep 3318545 = 2488909) B2488909
theorem B4424483 : Blo 1164640 4424483 := bstep (se 1 (by rfl) ⟨3318362, by rfl⟩ : syracuseStep 4424483 = 6636725) B6636725
theorem B2622257 : Blo 1164640 2622257 := bstep (se 2 (by rfl) ⟨983346, by rfl⟩ : syracuseStep 2622257 = 1966693) B1966693
theorem B2622275 : Blo 1164640 2622275 := bstep (se 1 (by rfl) ⟨1966706, by rfl⟩ : syracuseStep 2622275 = 3933413) B3933413
theorem B1966963 : Blo 1164640 1966963 := bstep (se 1 (by rfl) ⟨1475222, by rfl⟩ : syracuseStep 1966963 = 2950445) B2950445
theorem B1311619 : Blo 1164640 1311619 := bstep (se 1 (by rfl) ⟨983714, by rfl⟩ : syracuseStep 1311619 = 1967429) B1967429
theorem B6636451 : Blo 1164640 6636451 := bstep (se 1 (by rfl) ⟨4977338, by rfl⟩ : syracuseStep 6636451 = 9954677) B9954677
theorem B1475491 : Blo 1164640 1475491 := bstep (se 1 (by rfl) ⟨1106618, by rfl⟩ : syracuseStep 1475491 = 2213237) B2213237
theorem B2212849 : Blo 1164640 2212849 := bstep (se 2 (by rfl) ⟨829818, by rfl⟩ : syracuseStep 2212849 = 1659637) B1659637
theorem B1967105 : Blo 1164640 1967105 := bstep (se 2 (by rfl) ⟨737664, by rfl⟩ : syracuseStep 1967105 = 1475329) B1475329
theorem B1475587 : Blo 1164640 1475587 := bstep (se 1 (by rfl) ⟨1106690, by rfl⟩ : syracuseStep 1475587 = 2213381) B2213381
theorem B3933197 : Blo 1164640 3933197 := bstep (se 3 (by rfl) ⟨737474, by rfl⟩ : syracuseStep 3933197 = 1474949) B1474949
theorem B1311763 : Blo 1164640 1311763 := bstep (se 1 (by rfl) ⟨983822, by rfl⟩ : syracuseStep 1311763 = 1967645) B1967645
theorem B37815349 : Blo 1164640 37815349 := bstep (se 5 (by rfl) ⟨1772594, by rfl⟩ : syracuseStep 37815349 = 3545189) B3545189
theorem B3933251 : Blo 1164640 3933251 := bstep (se 1 (by rfl) ⟨2949938, by rfl⟩ : syracuseStep 3933251 = 5899877) B5899877
theorem B2622545 : Blo 1164640 2622545 := bstep (se 2 (by rfl) ⟨983454, by rfl⟩ : syracuseStep 2622545 = 1966909) B1966909
theorem B2622563 : Blo 1164640 2622563 := bstep (se 1 (by rfl) ⟨1966922, by rfl⟩ : syracuseStep 2622563 = 3933845) B3933845
theorem B50398321 : Blo 1164640 50398321 := bstep (se 2 (by rfl) ⟨18899370, by rfl⟩ : syracuseStep 50398321 = 37798741) B37798741
theorem B1967233 : Blo 1164640 1967233 := bstep (se 2 (by rfl) ⟨737712, by rfl⟩ : syracuseStep 1967233 = 1475425) B1475425
theorem B1967267 : Blo 1164640 1967267 := bstep (se 1 (by rfl) ⟨1475450, by rfl⟩ : syracuseStep 1967267 = 2950901) B2950901
theorem B1311907 : Blo 1164640 1311907 := bstep (se 1 (by rfl) ⟨983930, by rfl⟩ : syracuseStep 1311907 = 1967861) B1967861
theorem B1574083 : Blo 1164640 1574083 := bstep (se 1 (by rfl) ⟨1180562, by rfl⟩ : syracuseStep 1574083 = 2361125) B2361125
theorem B7464163 : Blo 1164640 7464163 := bstep (se 1 (by rfl) ⟨5598122, by rfl⟩ : syracuseStep 7464163 = 11196245) B11196245
theorem B1967395 : Blo 1164640 1967395 := bstep (se 1 (by rfl) ⟨1475546, by rfl⟩ : syracuseStep 1967395 = 2951093) B2951093
theorem B1312051 : Blo 1164640 1312051 := bstep (se 1 (by rfl) ⟨984038, by rfl⟩ : syracuseStep 1312051 = 1968077) B1968077
theorem B3933521 : Blo 1164640 3933521 := bstep (se 2 (by rfl) ⟨1475070, by rfl⟩ : syracuseStep 3933521 = 2950141) B2950141
theorem B1164643 : Blo 1164640 1164643 := bstep (se 1 (by rfl) ⟨873482, by rfl⟩ : syracuseStep 1164643 = 1746965) B1746965
theorem B2622833 : Blo 1164640 2622833 := bstep (se 2 (by rfl) ⟨983562, by rfl⟩ : syracuseStep 2622833 = 1967125) B1967125
theorem B1164659 : Blo 1164640 1164659 := bstep (se 1 (by rfl) ⟨873494, by rfl⟩ : syracuseStep 1164659 = 1746989) B1746989
theorem B1164675 : Blo 1164640 1164675 := bstep (se 1 (by rfl) ⟨873506, by rfl⟩ : syracuseStep 1164675 = 1747013) B1747013
theorem B2622851 : Blo 1164640 2622851 := bstep (se 1 (by rfl) ⟨1967138, by rfl⟩ : syracuseStep 2622851 = 3934277) B3934277
theorem B1164691 : Blo 1164640 1164691 := bstep (se 1 (by rfl) ⟨873518, by rfl⟩ : syracuseStep 1164691 = 1747037) B1747037
theorem B1164707 : Blo 1164640 1164707 := bstep (se 1 (by rfl) ⟨873530, by rfl⟩ : syracuseStep 1164707 = 1747061) B1747061
theorem B1574321 : Blo 1164640 1574321 := bstep (se 2 (by rfl) ⟨590370, by rfl⟩ : syracuseStep 1574321 = 1180741) B1180741
theorem B6636977 : Blo 1164640 6636977 := bstep (se 2 (by rfl) ⟨2488866, by rfl⟩ : syracuseStep 6636977 = 4977733) B4977733
theorem B1164723 : Blo 1164640 1164723 := bstep (se 1 (by rfl) ⟨873542, by rfl⟩ : syracuseStep 1164723 = 1747085) B1747085
theorem B4425137 : Blo 1164640 4425137 := bstep (se 2 (by rfl) ⟨1659426, by rfl⟩ : syracuseStep 4425137 = 3318853) B3318853
theorem B1197491 : Blo 1164640 1197491 := bstep (se 1 (by rfl) ⟨898118, by rfl⟩ : syracuseStep 1197491 = 1796237) B1796237
theorem B2950577 : Blo 1164640 2950577 := bstep (se 2 (by rfl) ⟨1106466, by rfl⟩ : syracuseStep 2950577 = 2212933) B2212933
theorem B1967537 : Blo 1164640 1967537 := bstep (se 2 (by rfl) ⟨737826, by rfl⟩ : syracuseStep 1967537 = 1475653) B1475653
theorem B1164739 : Blo 1164640 1164739 := bstep (se 1 (by rfl) ⟨873554, by rfl⟩ : syracuseStep 1164739 = 1747109) B1747109
theorem B1312195 : Blo 1164640 1312195 := bstep (se 1 (by rfl) ⟨984146, by rfl⟩ : syracuseStep 1312195 = 1968293) B1968293
theorem B1164755 : Blo 1164640 1164755 := bstep (se 1 (by rfl) ⟨873566, by rfl⟩ : syracuseStep 1164755 = 1747133) B1747133
theorem B1164771 : Blo 1164640 1164771 := bstep (se 1 (by rfl) ⟨873578, by rfl⟩ : syracuseStep 1164771 = 1747157) B1747157
theorem B2950627 : Blo 1164640 2950627 := bstep (se 1 (by rfl) ⟨2212970, by rfl⟩ : syracuseStep 2950627 = 4425941) B4425941
theorem B1164787 : Blo 1164640 1164787 := bstep (se 1 (by rfl) ⟨873590, by rfl⟩ : syracuseStep 1164787 = 1747181) B1747181
theorem B1476083 : Blo 1164640 1476083 := bstep (se 1 (by rfl) ⟨1107062, by rfl⟩ : syracuseStep 1476083 = 2214125) B2214125
theorem B1164803 : Blo 1164640 1164803 := bstep (se 1 (by rfl) ⟨873602, by rfl⟩ : syracuseStep 1164803 = 1747205) B1747205
theorem B1164819 : Blo 1164640 1164819 := bstep (se 1 (by rfl) ⟨873614, by rfl⟩ : syracuseStep 1164819 = 1747229) B1747229
theorem B1164835 : Blo 1164640 1164835 := bstep (se 1 (by rfl) ⟨873626, by rfl⟩ : syracuseStep 1164835 = 1747253) B1747253
theorem B1967665 : Blo 1164640 1967665 := bstep (se 2 (by rfl) ⟨737874, by rfl⟩ : syracuseStep 1967665 = 1475749) B1475749
theorem B1164851 : Blo 1164640 1164851 := bstep (se 1 (by rfl) ⟨873638, by rfl⟩ : syracuseStep 1164851 = 1747277) B1747277
theorem B1164867 : Blo 1164640 1164867 := bstep (se 1 (by rfl) ⟨873650, by rfl⟩ : syracuseStep 1164867 = 1747301) B1747301
theorem B1164883 : Blo 1164640 1164883 := bstep (se 1 (by rfl) ⟨873662, by rfl⟩ : syracuseStep 1164883 = 1747325) B1747325
theorem B1967699 : Blo 1164640 1967699 := bstep (se 1 (by rfl) ⟨1475774, by rfl⟩ : syracuseStep 1967699 = 2951549) B2951549
theorem B1164899 : Blo 1164640 1164899 := bstep (se 1 (by rfl) ⟨873674, by rfl⟩ : syracuseStep 1164899 = 1747349) B1747349
theorem B8636003 : Blo 1164640 8636003 := bstep (se 1 (by rfl) ⟨6477002, by rfl⟩ : syracuseStep 8636003 = 12954005) B12954005
theorem B2950769 : Blo 1164640 2950769 := bstep (se 2 (by rfl) ⟨1106538, by rfl⟩ : syracuseStep 2950769 = 2213077) B2213077
theorem B8406641 : Blo 1164640 8406641 := bstep (se 2 (by rfl) ⟨3152490, by rfl⟩ : syracuseStep 8406641 = 6304981) B6304981
theorem B1164915 : Blo 1164640 1164915 := bstep (se 1 (by rfl) ⟨873686, by rfl⟩ : syracuseStep 1164915 = 1747373) B1747373
theorem B1164931 : Blo 1164640 1164931 := bstep (se 1 (by rfl) ⟨873698, by rfl⟩ : syracuseStep 1164931 = 1747397) B1747397
theorem B2623121 : Blo 1164640 2623121 := bstep (se 2 (by rfl) ⟨983670, by rfl⟩ : syracuseStep 2623121 = 1967341) B1967341
theorem B1164947 : Blo 1164640 1164947 := bstep (se 1 (by rfl) ⟨873710, by rfl⟩ : syracuseStep 1164947 = 1747421) B1747421
theorem B1164963 : Blo 1164640 1164963 := bstep (se 1 (by rfl) ⟨873722, by rfl⟩ : syracuseStep 1164963 = 1747445) B1747445
theorem B2623139 : Blo 1164640 2623139 := bstep (se 1 (by rfl) ⟨1967354, by rfl⟩ : syracuseStep 2623139 = 3934709) B3934709
theorem B1164979 : Blo 1164640 1164979 := bstep (se 1 (by rfl) ⟨873734, by rfl⟩ : syracuseStep 1164979 = 1747469) B1747469
theorem B1164995 : Blo 1164640 1164995 := bstep (se 1 (by rfl) ⟨873746, by rfl⟩ : syracuseStep 1164995 = 1747493) B1747493
theorem B1165011 : Blo 1164640 1165011 := bstep (se 1 (by rfl) ⟨873758, by rfl⟩ : syracuseStep 1165011 = 1747517) B1747517
theorem B1967827 : Blo 1164640 1967827 := bstep (se 1 (by rfl) ⟨1475870, by rfl⟩ : syracuseStep 1967827 = 2951741) B2951741
theorem B1165027 : Blo 1164640 1165027 := bstep (se 1 (by rfl) ⟨873770, by rfl⟩ : syracuseStep 1165027 = 1747541) B1747541
theorem B1165043 : Blo 1164640 1165043 := bstep (se 1 (by rfl) ⟨873782, by rfl⟩ : syracuseStep 1165043 = 1747565) B1747565
theorem B1165059 : Blo 1164640 1165059 := bstep (se 1 (by rfl) ⟨873794, by rfl⟩ : syracuseStep 1165059 = 1747589) B1747589
theorem B14944013 : Blo 1164640 14944013 := bstep (se 3 (by rfl) ⟨2802002, by rfl⟩ : syracuseStep 14944013 = 5604005) B5604005
theorem B1165075 : Blo 1164640 1165075 := bstep (se 1 (by rfl) ⟨873806, by rfl⟩ : syracuseStep 1165075 = 1747613) B1747613
theorem B1165091 : Blo 1164640 1165091 := bstep (se 1 (by rfl) ⟨873818, by rfl⟩ : syracuseStep 1165091 = 1747637) B1747637
theorem B1165107 : Blo 1164640 1165107 := bstep (se 1 (by rfl) ⟨873830, by rfl⟩ : syracuseStep 1165107 = 1747661) B1747661
theorem B1165123 : Blo 1164640 1165123 := bstep (se 1 (by rfl) ⟨873842, by rfl⟩ : syracuseStep 1165123 = 1747685) B1747685
theorem B7087949 : Blo 1164640 7087949 := bstep (se 3 (by rfl) ⟨1328990, by rfl⟩ : syracuseStep 7087949 = 2657981) B2657981
theorem B1165139 : Blo 1164640 1165139 := bstep (se 1 (by rfl) ⟨873854, by rfl⟩ : syracuseStep 1165139 = 1747709) B1747709
theorem B1967969 : Blo 1164640 1967969 := bstep (se 2 (by rfl) ⟨737988, by rfl⟩ : syracuseStep 1967969 = 1475977) B1475977
theorem B1165155 : Blo 1164640 1165155 := bstep (se 1 (by rfl) ⟨873866, by rfl⟩ : syracuseStep 1165155 = 1747733) B1747733
theorem B3934061 : Blo 1164640 3934061 := bstep (se 3 (by rfl) ⟨737636, by rfl⟩ : syracuseStep 3934061 = 1475273) B1475273
theorem B12593009 : Blo 1164640 12593009 := bstep (se 2 (by rfl) ⟨4722378, by rfl⟩ : syracuseStep 12593009 = 9444757) B9444757
theorem B1165171 : Blo 1164640 1165171 := bstep (se 1 (by rfl) ⟨873878, by rfl⟩ : syracuseStep 1165171 = 1747757) B1747757
theorem B1165187 : Blo 1164640 1165187 := bstep (se 1 (by rfl) ⟨873890, by rfl⟩ : syracuseStep 1165187 = 1747781) B1747781
theorem B1165203 : Blo 1164640 1165203 := bstep (se 1 (by rfl) ⟨873902, by rfl⟩ : syracuseStep 1165203 = 1747805) B1747805
theorem B1771427 : Blo 1164640 1771427 := bstep (se 1 (by rfl) ⟨1328570, by rfl⟩ : syracuseStep 1771427 = 2657141) B2657141
theorem B1165219 : Blo 1164640 1165219 := bstep (se 1 (by rfl) ⟨873914, by rfl⟩ : syracuseStep 1165219 = 1747829) B1747829
theorem B3934115 : Blo 1164640 3934115 := bstep (se 1 (by rfl) ⟨2950586, by rfl⟩ : syracuseStep 3934115 = 5901173) B5901173
theorem B2623409 : Blo 1164640 2623409 := bstep (se 2 (by rfl) ⟨983778, by rfl⟩ : syracuseStep 2623409 = 1967557) B1967557
theorem B1165235 : Blo 1164640 1165235 := bstep (se 1 (by rfl) ⟨873926, by rfl⟩ : syracuseStep 1165235 = 1747853) B1747853
theorem B1165251 : Blo 1164640 1165251 := bstep (se 1 (by rfl) ⟨873938, by rfl⟩ : syracuseStep 1165251 = 1747877) B1747877
theorem B2623427 : Blo 1164640 2623427 := bstep (se 1 (by rfl) ⟨1967570, by rfl⟩ : syracuseStep 2623427 = 3935141) B3935141
theorem B1165267 : Blo 1164640 1165267 := bstep (se 1 (by rfl) ⟨873950, by rfl⟩ : syracuseStep 1165267 = 1747901) B1747901
theorem B1968097 : Blo 1164640 1968097 := bstep (se 2 (by rfl) ⟨738036, by rfl⟩ : syracuseStep 1968097 = 1476073) B1476073
theorem B1165283 : Blo 1164640 1165283 := bstep (se 1 (by rfl) ⟨873962, by rfl⟩ : syracuseStep 1165283 = 1747925) B1747925
theorem B2992099 : Blo 1164640 2992099 := bstep (se 1 (by rfl) ⟨2244074, by rfl⟩ : syracuseStep 2992099 = 4488149) B4488149
theorem B1165299 : Blo 1164640 1165299 := bstep (se 1 (by rfl) ⟨873974, by rfl⟩ : syracuseStep 1165299 = 1747949) B1747949
theorem B1165315 : Blo 1164640 1165315 := bstep (se 1 (by rfl) ⟨873986, by rfl⟩ : syracuseStep 1165315 = 1747973) B1747973
theorem B1968131 : Blo 1164640 1968131 := bstep (se 1 (by rfl) ⟨1476098, by rfl⟩ : syracuseStep 1968131 = 2952197) B2952197
theorem B2213905 : Blo 1164640 2213905 := bstep (se 2 (by rfl) ⟨830214, by rfl⟩ : syracuseStep 2213905 = 1660429) B1660429
theorem B1165331 : Blo 1164640 1165331 := bstep (se 1 (by rfl) ⟨873998, by rfl⟩ : syracuseStep 1165331 = 1747997) B1747997
theorem B1746977 : Blo 1164640 1746977 := bstep (se 2 (by rfl) ⟨655116, by rfl⟩ : syracuseStep 1746977 = 1310233) B1310233
theorem B1165347 : Blo 1164640 1165347 := bstep (se 1 (by rfl) ⟨874010, by rfl⟩ : syracuseStep 1165347 = 1748021) B1748021
theorem B1746995 : Blo 1164640 1746995 := bstep (se 1 (by rfl) ⟨1310246, by rfl⟩ : syracuseStep 1746995 = 2620493) B2620493
theorem B1165363 : Blo 1164640 1165363 := bstep (se 1 (by rfl) ⟨874022, by rfl⟩ : syracuseStep 1165363 = 1748045) B1748045
theorem B1165379 : Blo 1164640 1165379 := bstep (se 1 (by rfl) ⟨874034, by rfl⟩ : syracuseStep 1165379 = 1748069) B1748069
theorem B1747025 : Blo 1164640 1747025 := bstep (se 2 (by rfl) ⟨655134, by rfl⟩ : syracuseStep 1747025 = 1310269) B1310269
theorem B1165395 : Blo 1164640 1165395 := bstep (se 1 (by rfl) ⟨874046, by rfl⟩ : syracuseStep 1165395 = 1748093) B1748093
theorem B1747043 : Blo 1164640 1747043 := bstep (se 1 (by rfl) ⟨1310282, by rfl⟩ : syracuseStep 1747043 = 2620565) B2620565
theorem B1165411 : Blo 1164640 1165411 := bstep (se 1 (by rfl) ⟨874058, by rfl⟩ : syracuseStep 1165411 = 1748117) B1748117
theorem B1165427 : Blo 1164640 1165427 := bstep (se 1 (by rfl) ⟨874070, by rfl⟩ : syracuseStep 1165427 = 1748141) B1748141
theorem B1747073 : Blo 1164640 1747073 := bstep (se 2 (by rfl) ⟨655152, by rfl⟩ : syracuseStep 1747073 = 1310305) B1310305
theorem B1165443 : Blo 1164640 1165443 := bstep (se 1 (by rfl) ⟨874082, by rfl⟩ : syracuseStep 1165443 = 1748165) B1748165
theorem B1968259 : Blo 1164640 1968259 := bstep (se 1 (by rfl) ⟨1476194, by rfl⟩ : syracuseStep 1968259 = 2952389) B2952389
theorem B1747091 : Blo 1164640 1747091 := bstep (se 1 (by rfl) ⟨1310318, by rfl⟩ : syracuseStep 1747091 = 2620637) B2620637
theorem B1165459 : Blo 1164640 1165459 := bstep (se 1 (by rfl) ⟨874094, by rfl⟩ : syracuseStep 1165459 = 1748189) B1748189
theorem B1575073 : Blo 1164640 1575073 := bstep (se 2 (by rfl) ⟨590652, by rfl⟩ : syracuseStep 1575073 = 1181305) B1181305
theorem B1165475 : Blo 1164640 1165475 := bstep (se 1 (by rfl) ⟨874106, by rfl⟩ : syracuseStep 1165475 = 1748213) B1748213
theorem B4728995 : Blo 1164640 4728995 := bstep (se 1 (by rfl) ⟨3546746, by rfl⟩ : syracuseStep 4728995 = 7093493) B7093493
theorem B1747121 : Blo 1164640 1747121 := bstep (se 2 (by rfl) ⟨655170, by rfl⟩ : syracuseStep 1747121 = 1310341) B1310341
theorem B3934385 : Blo 1164640 3934385 := bstep (se 2 (by rfl) ⟨1475394, by rfl⟩ : syracuseStep 3934385 = 2950789) B2950789
theorem B1165491 : Blo 1164640 1165491 := bstep (se 1 (by rfl) ⟨874118, by rfl⟩ : syracuseStep 1165491 = 1748237) B1748237
theorem B1747139 : Blo 1164640 1747139 := bstep (se 1 (by rfl) ⟨1310354, by rfl⟩ : syracuseStep 1747139 = 2620709) B2620709
theorem B1165507 : Blo 1164640 1165507 := bstep (se 1 (by rfl) ⟨874130, by rfl⟩ : syracuseStep 1165507 = 1748261) B1748261
theorem B3320003 : Blo 1164640 3320003 := bstep (se 1 (by rfl) ⟨2490002, by rfl⟩ : syracuseStep 3320003 = 4980005) B4980005
theorem B1575121 : Blo 1164640 1575121 := bstep (se 2 (by rfl) ⟨590670, by rfl⟩ : syracuseStep 1575121 = 1181341) B1181341
theorem B2623697 : Blo 1164640 2623697 := bstep (se 2 (by rfl) ⟨983886, by rfl⟩ : syracuseStep 2623697 = 1967773) B1967773
theorem B1165523 : Blo 1164640 1165523 := bstep (se 1 (by rfl) ⟨874142, by rfl⟩ : syracuseStep 1165523 = 1748285) B1748285
theorem B1747169 : Blo 1164640 1747169 := bstep (se 2 (by rfl) ⟨655188, by rfl⟩ : syracuseStep 1747169 = 1310377) B1310377
theorem B1165539 : Blo 1164640 1165539 := bstep (se 1 (by rfl) ⟨874154, by rfl⟩ : syracuseStep 1165539 = 1748309) B1748309
theorem B2623715 : Blo 1164640 2623715 := bstep (se 1 (by rfl) ⟨1967786, by rfl⟩ : syracuseStep 2623715 = 3935573) B3935573
theorem B2099441 : Blo 1164640 2099441 := bstep (se 2 (by rfl) ⟨787290, by rfl⟩ : syracuseStep 2099441 = 1574581) B1574581
theorem B1747187 : Blo 1164640 1747187 := bstep (se 1 (by rfl) ⟨1310390, by rfl⟩ : syracuseStep 1747187 = 2620781) B2620781
theorem B1165555 : Blo 1164640 1165555 := bstep (se 1 (by rfl) ⟨874166, by rfl⟩ : syracuseStep 1165555 = 1748333) B1748333
theorem B1165571 : Blo 1164640 1165571 := bstep (se 1 (by rfl) ⟨874178, by rfl⟩ : syracuseStep 1165571 = 1748357) B1748357
theorem B1747217 : Blo 1164640 1747217 := bstep (se 2 (by rfl) ⟨655206, by rfl⟩ : syracuseStep 1747217 = 1310413) B1310413
theorem B1165587 : Blo 1164640 1165587 := bstep (se 1 (by rfl) ⟨874190, by rfl⟩ : syracuseStep 1165587 = 1748381) B1748381
theorem B1747235 : Blo 1164640 1747235 := bstep (se 1 (by rfl) ⟨1310426, by rfl⟩ : syracuseStep 1747235 = 2620853) B2620853
theorem B1165603 : Blo 1164640 1165603 := bstep (se 1 (by rfl) ⟨874202, by rfl⟩ : syracuseStep 1165603 = 1748405) B1748405
theorem B1165619 : Blo 1164640 1165619 := bstep (se 1 (by rfl) ⟨874214, by rfl⟩ : syracuseStep 1165619 = 1748429) B1748429
theorem B1747265 : Blo 1164640 1747265 := bstep (se 2 (by rfl) ⟨655224, by rfl⟩ : syracuseStep 1747265 = 1310449) B1310449
theorem B1165635 : Blo 1164640 1165635 := bstep (se 1 (by rfl) ⟨874226, by rfl⟩ : syracuseStep 1165635 = 1748453) B1748453
theorem B1747283 : Blo 1164640 1747283 := bstep (se 1 (by rfl) ⟨1310462, by rfl⟩ : syracuseStep 1747283 = 2620925) B2620925
theorem B1165651 : Blo 1164640 1165651 := bstep (se 1 (by rfl) ⟨874238, by rfl⟩ : syracuseStep 1165651 = 1748477) B1748477
theorem B1165667 : Blo 1164640 1165667 := bstep (se 1 (by rfl) ⟨874250, by rfl⟩ : syracuseStep 1165667 = 1748501) B1748501
theorem B1747313 : Blo 1164640 1747313 := bstep (se 2 (by rfl) ⟨655242, by rfl⟩ : syracuseStep 1747313 = 1310485) B1310485
theorem B1165683 : Blo 1164640 1165683 := bstep (se 1 (by rfl) ⟨874262, by rfl⟩ : syracuseStep 1165683 = 1748525) B1748525
theorem B1747331 : Blo 1164640 1747331 := bstep (se 1 (by rfl) ⟨1310498, by rfl⟩ : syracuseStep 1747331 = 2620997) B2620997
theorem B1165699 : Blo 1164640 1165699 := bstep (se 1 (by rfl) ⟨874274, by rfl⟩ : syracuseStep 1165699 = 1748549) B1748549
theorem B1165715 : Blo 1164640 1165715 := bstep (se 1 (by rfl) ⟨874286, by rfl⟩ : syracuseStep 1165715 = 1748573) B1748573
theorem B1747361 : Blo 1164640 1747361 := bstep (se 2 (by rfl) ⟨655260, by rfl⟩ : syracuseStep 1747361 = 1310521) B1310521
theorem B1165731 : Blo 1164640 1165731 := bstep (se 1 (by rfl) ⟨874298, by rfl⟩ : syracuseStep 1165731 = 1748597) B1748597
theorem B2214307 : Blo 1164640 2214307 := bstep (se 1 (by rfl) ⟨1660730, by rfl⟩ : syracuseStep 2214307 = 3321461) B3321461
theorem B1747379 : Blo 1164640 1747379 := bstep (se 1 (by rfl) ⟨1310534, by rfl⟩ : syracuseStep 1747379 = 2621069) B2621069
theorem B1165747 : Blo 1164640 1165747 := bstep (se 1 (by rfl) ⟨874310, by rfl⟩ : syracuseStep 1165747 = 1748621) B1748621
theorem B1165763 : Blo 1164640 1165763 := bstep (se 1 (by rfl) ⟨874322, by rfl⟩ : syracuseStep 1165763 = 1748645) B1748645
theorem B76687813 : Blo 1164640 76687813 := bstep (se 4 (by rfl) ⟨7189482, by rfl⟩ : syracuseStep 76687813 = 14378965) B14378965
theorem B1747409 : Blo 1164640 1747409 := bstep (se 2 (by rfl) ⟨655278, by rfl⟩ : syracuseStep 1747409 = 1310557) B1310557
theorem B1165779 : Blo 1164640 1165779 := bstep (se 1 (by rfl) ⟨874334, by rfl⟩ : syracuseStep 1165779 = 1748669) B1748669
theorem B1747427 : Blo 1164640 1747427 := bstep (se 1 (by rfl) ⟨1310570, by rfl⟩ : syracuseStep 1747427 = 2621141) B2621141
theorem B1165795 : Blo 1164640 1165795 := bstep (se 1 (by rfl) ⟨874346, by rfl⟩ : syracuseStep 1165795 = 1748693) B1748693
theorem B2623985 : Blo 1164640 2623985 := bstep (se 2 (by rfl) ⟨983994, by rfl⟩ : syracuseStep 2623985 = 1967989) B1967989
theorem B1165811 : Blo 1164640 1165811 := bstep (se 1 (by rfl) ⟨874358, by rfl⟩ : syracuseStep 1165811 = 1748717) B1748717
theorem B1747457 : Blo 1164640 1747457 := bstep (se 2 (by rfl) ⟨655296, by rfl⟩ : syracuseStep 1747457 = 1310593) B1310593
theorem B1165827 : Blo 1164640 1165827 := bstep (se 1 (by rfl) ⟨874370, by rfl⟩ : syracuseStep 1165827 = 1748741) B1748741
theorem B2624003 : Blo 1164640 2624003 := bstep (se 1 (by rfl) ⟨1968002, by rfl⟩ : syracuseStep 2624003 = 3936005) B3936005
theorem B6302213 : Blo 1164640 6302213 := bstep (se 4 (by rfl) ⟨590832, by rfl⟩ : syracuseStep 6302213 = 1181665) B1181665
theorem B1747475 : Blo 1164640 1747475 := bstep (se 1 (by rfl) ⟨1310606, by rfl⟩ : syracuseStep 1747475 = 2621213) B2621213
theorem B1165843 : Blo 1164640 1165843 := bstep (se 1 (by rfl) ⟨874382, by rfl⟩ : syracuseStep 1165843 = 1748765) B1748765
theorem B1165859 : Blo 1164640 1165859 := bstep (se 1 (by rfl) ⟨874394, by rfl⟩ : syracuseStep 1165859 = 1748789) B1748789
theorem B1747505 : Blo 1164640 1747505 := bstep (se 2 (by rfl) ⟨655314, by rfl⟩ : syracuseStep 1747505 = 1310629) B1310629
theorem B5900849 : Blo 1164640 5900849 := bstep (se 2 (by rfl) ⟨2212818, by rfl⟩ : syracuseStep 5900849 = 4425637) B4425637
theorem B1165875 : Blo 1164640 1165875 := bstep (se 1 (by rfl) ⟨874406, by rfl⟩ : syracuseStep 1165875 = 1748813) B1748813
theorem B1747523 : Blo 1164640 1747523 := bstep (se 1 (by rfl) ⟨1310642, by rfl⟩ : syracuseStep 1747523 = 2621285) B2621285
theorem B1165891 : Blo 1164640 1165891 := bstep (se 1 (by rfl) ⟨874418, by rfl⟩ : syracuseStep 1165891 = 1748837) B1748837
theorem B2656849 : Blo 1164640 2656849 := bstep (se 2 (by rfl) ⟨996318, by rfl⟩ : syracuseStep 2656849 = 1992637) B1992637
theorem B2951761 : Blo 1164640 2951761 := bstep (se 2 (by rfl) ⟨1106910, by rfl⟩ : syracuseStep 2951761 = 2213821) B2213821
theorem B1165907 : Blo 1164640 1165907 := bstep (se 1 (by rfl) ⟨874430, by rfl⟩ : syracuseStep 1165907 = 1748861) B1748861
theorem B1747553 : Blo 1164640 1747553 := bstep (se 2 (by rfl) ⟨655332, by rfl⟩ : syracuseStep 1747553 = 1310665) B1310665
theorem B1165923 : Blo 1164640 1165923 := bstep (se 1 (by rfl) ⟨874442, by rfl⟩ : syracuseStep 1165923 = 1748885) B1748885
theorem B1747571 : Blo 1164640 1747571 := bstep (se 1 (by rfl) ⟨1310678, by rfl⟩ : syracuseStep 1747571 = 2621357) B2621357
theorem B1165939 : Blo 1164640 1165939 := bstep (se 1 (by rfl) ⟨874454, by rfl⟩ : syracuseStep 1165939 = 1748909) B1748909
theorem B1165955 : Blo 1164640 1165955 := bstep (se 1 (by rfl) ⟨874466, by rfl⟩ : syracuseStep 1165955 = 1748933) B1748933
theorem B1747601 : Blo 1164640 1747601 := bstep (se 2 (by rfl) ⟨655350, by rfl⟩ : syracuseStep 1747601 = 1310701) B1310701
theorem B1165971 : Blo 1164640 1165971 := bstep (se 1 (by rfl) ⟨874478, by rfl⟩ : syracuseStep 1165971 = 1748957) B1748957
theorem B1747619 : Blo 1164640 1747619 := bstep (se 1 (by rfl) ⟨1310714, by rfl⟩ : syracuseStep 1747619 = 2621429) B2621429
theorem B1165987 : Blo 1164640 1165987 := bstep (se 1 (by rfl) ⟨874490, by rfl⟩ : syracuseStep 1165987 = 1748981) B1748981
theorem B1166003 : Blo 1164640 1166003 := bstep (se 1 (by rfl) ⟨874502, by rfl⟩ : syracuseStep 1166003 = 1749005) B1749005
theorem B1747649 : Blo 1164640 1747649 := bstep (se 2 (by rfl) ⟨655368, by rfl⟩ : syracuseStep 1747649 = 1310737) B1310737
theorem B2362051 : Blo 1164640 2362051 := bstep (se 1 (by rfl) ⟨1771538, by rfl⟩ : syracuseStep 2362051 = 3543077) B3543077
theorem B1166019 : Blo 1164640 1166019 := bstep (se 1 (by rfl) ⟨874514, by rfl⟩ : syracuseStep 1166019 = 1749029) B1749029
theorem B3934925 : Blo 1164640 3934925 := bstep (se 3 (by rfl) ⟨737798, by rfl⟩ : syracuseStep 3934925 = 1475597) B1475597
theorem B1747667 : Blo 1164640 1747667 := bstep (se 1 (by rfl) ⟨1310750, by rfl⟩ : syracuseStep 1747667 = 2621501) B2621501
theorem B1166035 : Blo 1164640 1166035 := bstep (se 1 (by rfl) ⟨874526, by rfl⟩ : syracuseStep 1166035 = 1749053) B1749053
theorem B1166051 : Blo 1164640 1166051 := bstep (se 1 (by rfl) ⟨874538, by rfl⟩ : syracuseStep 1166051 = 1749077) B1749077
theorem B1747697 : Blo 1164640 1747697 := bstep (se 2 (by rfl) ⟨655386, by rfl⟩ : syracuseStep 1747697 = 1310773) B1310773
theorem B1166067 : Blo 1164640 1166067 := bstep (se 1 (by rfl) ⟨874550, by rfl⟩ : syracuseStep 1166067 = 1749101) B1749101
theorem B1747715 : Blo 1164640 1747715 := bstep (se 1 (by rfl) ⟨1310786, by rfl⟩ : syracuseStep 1747715 = 2621573) B2621573
theorem B3934979 : Blo 1164640 3934979 := bstep (se 1 (by rfl) ⟨2951234, by rfl⟩ : syracuseStep 3934979 = 5902469) B5902469
theorem B1166083 : Blo 1164640 1166083 := bstep (se 1 (by rfl) ⟨874562, by rfl⟩ : syracuseStep 1166083 = 1749125) B1749125
theorem B2624273 : Blo 1164640 2624273 := bstep (se 2 (by rfl) ⟨984102, by rfl⟩ : syracuseStep 2624273 = 1968205) B1968205
theorem B1166099 : Blo 1164640 1166099 := bstep (se 1 (by rfl) ⟨874574, by rfl⟩ : syracuseStep 1166099 = 1749149) B1749149
theorem B1747745 : Blo 1164640 1747745 := bstep (se 2 (by rfl) ⟨655404, by rfl⟩ : syracuseStep 1747745 = 1310809) B1310809
theorem B1166115 : Blo 1164640 1166115 := bstep (se 1 (by rfl) ⟨874586, by rfl⟩ : syracuseStep 1166115 = 1749173) B1749173
theorem B2624291 : Blo 1164640 2624291 := bstep (se 1 (by rfl) ⟨1968218, by rfl⟩ : syracuseStep 2624291 = 3936437) B3936437
theorem B1747763 : Blo 1164640 1747763 := bstep (se 1 (by rfl) ⟨1310822, by rfl⟩ : syracuseStep 1747763 = 2621645) B2621645
theorem B1166131 : Blo 1164640 1166131 := bstep (se 1 (by rfl) ⟨874598, by rfl⟩ : syracuseStep 1166131 = 1749197) B1749197
theorem B1166147 : Blo 1164640 1166147 := bstep (se 1 (by rfl) ⟨874610, by rfl⟩ : syracuseStep 1166147 = 1749221) B1749221
theorem B1747793 : Blo 1164640 1747793 := bstep (se 2 (by rfl) ⟨655422, by rfl⟩ : syracuseStep 1747793 = 1310845) B1310845
theorem B1166163 : Blo 1164640 1166163 := bstep (se 1 (by rfl) ⟨874622, by rfl⟩ : syracuseStep 1166163 = 1749245) B1749245
theorem B1747811 : Blo 1164640 1747811 := bstep (se 1 (by rfl) ⟨1310858, by rfl⟩ : syracuseStep 1747811 = 2621717) B2621717
theorem B6638435 : Blo 1164640 6638435 := bstep (se 1 (by rfl) ⟨4978826, by rfl⟩ : syracuseStep 6638435 = 9957653) B9957653
theorem B4426595 : Blo 1164640 4426595 := bstep (se 1 (by rfl) ⟨3319946, by rfl⟩ : syracuseStep 4426595 = 6639893) B6639893
theorem B1166179 : Blo 1164640 1166179 := bstep (se 1 (by rfl) ⟨874634, by rfl⟩ : syracuseStep 1166179 = 1749269) B1749269
theorem B2952035 : Blo 1164640 2952035 := bstep (se 1 (by rfl) ⟨2214026, by rfl⟩ : syracuseStep 2952035 = 4428053) B4428053
theorem B4426609 : Blo 1164640 4426609 := bstep (se 2 (by rfl) ⟨1659978, by rfl⟩ : syracuseStep 4426609 = 3319957) B3319957
theorem B1166195 : Blo 1164640 1166195 := bstep (se 1 (by rfl) ⟨874646, by rfl⟩ : syracuseStep 1166195 = 1749293) B1749293
theorem B1747841 : Blo 1164640 1747841 := bstep (se 2 (by rfl) ⟨655440, by rfl⟩ : syracuseStep 1747841 = 1310881) B1310881
theorem B1166211 : Blo 1164640 1166211 := bstep (se 1 (by rfl) ⟨874658, by rfl⟩ : syracuseStep 1166211 = 1749317) B1749317
theorem B1747859 : Blo 1164640 1747859 := bstep (se 1 (by rfl) ⟨1310894, by rfl⟩ : syracuseStep 1747859 = 2621789) B2621789
theorem B1166227 : Blo 1164640 1166227 := bstep (se 1 (by rfl) ⟨874670, by rfl⟩ : syracuseStep 1166227 = 1749341) B1749341
theorem B1330067 : Blo 1164640 1330067 := bstep (se 1 (by rfl) ⟨997550, by rfl⟩ : syracuseStep 1330067 = 1995101) B1995101
theorem B1166243 : Blo 1164640 1166243 := bstep (se 1 (by rfl) ⟨874682, by rfl⟩ : syracuseStep 1166243 = 1749365) B1749365
theorem B1747889 : Blo 1164640 1747889 := bstep (se 2 (by rfl) ⟨655458, by rfl⟩ : syracuseStep 1747889 = 1310917) B1310917
theorem B1166259 : Blo 1164640 1166259 := bstep (se 1 (by rfl) ⟨874694, by rfl⟩ : syracuseStep 1166259 = 1749389) B1749389
theorem B14560181 : Blo 1164640 14560181 := bstep (se 5 (by rfl) ⟨682508, by rfl⟩ : syracuseStep 14560181 = 1365017) B1365017
theorem B1747907 : Blo 1164640 1747907 := bstep (se 1 (by rfl) ⟨1310930, by rfl⟩ : syracuseStep 1747907 = 2621861) B2621861
theorem B1166275 : Blo 1164640 1166275 := bstep (se 1 (by rfl) ⟨874706, by rfl⟩ : syracuseStep 1166275 = 1749413) B1749413
theorem B1166291 : Blo 1164640 1166291 := bstep (se 1 (by rfl) ⟨874718, by rfl⟩ : syracuseStep 1166291 = 1749437) B1749437
theorem B1747937 : Blo 1164640 1747937 := bstep (se 2 (by rfl) ⟨655476, by rfl⟩ : syracuseStep 1747937 = 1310953) B1310953
theorem B1166307 : Blo 1164640 1166307 := bstep (se 1 (by rfl) ⟨874730, by rfl⟩ : syracuseStep 1166307 = 1749461) B1749461
theorem B1747955 : Blo 1164640 1747955 := bstep (se 1 (by rfl) ⟨1310966, by rfl⟩ : syracuseStep 1747955 = 2621933) B2621933
theorem B1166323 : Blo 1164640 1166323 := bstep (se 1 (by rfl) ⟨874742, by rfl⟩ : syracuseStep 1166323 = 1749485) B1749485
theorem B1166339 : Blo 1164640 1166339 := bstep (se 1 (by rfl) ⟨874754, by rfl⟩ : syracuseStep 1166339 = 1749509) B1749509
theorem B1747985 : Blo 1164640 1747985 := bstep (se 2 (by rfl) ⟨655494, by rfl⟩ : syracuseStep 1747985 = 1310989) B1310989
theorem B3935249 : Blo 1164640 3935249 := bstep (se 2 (by rfl) ⟨1475718, by rfl⟩ : syracuseStep 3935249 = 2951437) B2951437
theorem B1166355 : Blo 1164640 1166355 := bstep (se 1 (by rfl) ⟨874766, by rfl⟩ : syracuseStep 1166355 = 1749533) B1749533
theorem B1748003 : Blo 1164640 1748003 := bstep (se 1 (by rfl) ⟨1311002, by rfl⟩ : syracuseStep 1748003 = 2622005) B2622005
theorem B2952227 : Blo 1164640 2952227 := bstep (se 1 (by rfl) ⟨2214170, by rfl⟩ : syracuseStep 2952227 = 4428341) B4428341
theorem B1166371 : Blo 1164640 1166371 := bstep (se 1 (by rfl) ⟨874778, by rfl⟩ : syracuseStep 1166371 = 1749557) B1749557
theorem B1166387 : Blo 1164640 1166387 := bstep (se 1 (by rfl) ⟨874790, by rfl⟩ : syracuseStep 1166387 = 1749581) B1749581
theorem B1748033 : Blo 1164640 1748033 := bstep (se 2 (by rfl) ⟨655512, by rfl⟩ : syracuseStep 1748033 = 1311025) B1311025
theorem B1748051 : Blo 1164640 1748051 := bstep (se 1 (by rfl) ⟨1311038, by rfl⟩ : syracuseStep 1748051 = 2622077) B2622077
theorem B1748081 : Blo 1164640 1748081 := bstep (se 2 (by rfl) ⟨655530, by rfl⟩ : syracuseStep 1748081 = 1311061) B1311061
theorem B8850545 : Blo 1164640 8850545 := bstep (se 2 (by rfl) ⟨3318954, by rfl⟩ : syracuseStep 8850545 = 6637909) B6637909
theorem B1748099 : Blo 1164640 1748099 := bstep (se 1 (by rfl) ⟨1311074, by rfl⟩ : syracuseStep 1748099 = 2622149) B2622149
theorem B1748129 : Blo 1164640 1748129 := bstep (se 2 (by rfl) ⟨655548, by rfl⟩ : syracuseStep 1748129 = 1311097) B1311097
theorem B1748147 : Blo 1164640 1748147 := bstep (se 1 (by rfl) ⟨1311110, by rfl⟩ : syracuseStep 1748147 = 2622221) B2622221
theorem B2837713 : Blo 1164640 2837713 := bstep (se 2 (by rfl) ⟨1064142, by rfl⟩ : syracuseStep 2837713 = 2128285) B2128285
theorem B1748177 : Blo 1164640 1748177 := bstep (se 2 (by rfl) ⟨655566, by rfl⟩ : syracuseStep 1748177 = 1311133) B1311133
theorem B1748195 : Blo 1164640 1748195 := bstep (se 1 (by rfl) ⟨1311146, by rfl⟩ : syracuseStep 1748195 = 2622293) B2622293
theorem B1748225 : Blo 1164640 1748225 := bstep (se 2 (by rfl) ⟨655584, by rfl⟩ : syracuseStep 1748225 = 1311169) B1311169
theorem B1748243 : Blo 1164640 1748243 := bstep (se 1 (by rfl) ⟨1311182, by rfl⟩ : syracuseStep 1748243 = 2622365) B2622365
theorem B1748273 : Blo 1164640 1748273 := bstep (se 2 (by rfl) ⟨655602, by rfl⟩ : syracuseStep 1748273 = 1311205) B1311205
theorem B7089457 : Blo 1164640 7089457 := bstep (se 2 (by rfl) ⟨2658546, by rfl⟩ : syracuseStep 7089457 = 5317093) B5317093
theorem B1748291 : Blo 1164640 1748291 := bstep (se 1 (by rfl) ⟨1311218, by rfl⟩ : syracuseStep 1748291 = 2622437) B2622437
theorem B1748321 : Blo 1164640 1748321 := bstep (se 2 (by rfl) ⟨655620, by rfl⟩ : syracuseStep 1748321 = 1311241) B1311241
theorem B3362161 : Blo 1164640 3362161 := bstep (se 2 (by rfl) ⟨1260810, by rfl⟩ : syracuseStep 3362161 = 2521621) B2521621
theorem B1748339 : Blo 1164640 1748339 := bstep (se 1 (by rfl) ⟨1311254, by rfl⟩ : syracuseStep 1748339 = 2622509) B2622509
theorem B1748369 : Blo 1164640 1748369 := bstep (se 2 (by rfl) ⟨655638, by rfl⟩ : syracuseStep 1748369 = 1311277) B1311277
theorem B3321233 : Blo 1164640 3321233 := bstep (se 2 (by rfl) ⟨1245462, by rfl⟩ : syracuseStep 3321233 = 2490925) B2490925
theorem B1748387 : Blo 1164640 1748387 := bstep (se 1 (by rfl) ⟨1311290, by rfl⟩ : syracuseStep 1748387 = 2622581) B2622581
theorem B1748417 : Blo 1164640 1748417 := bstep (se 2 (by rfl) ⟨655656, by rfl⟩ : syracuseStep 1748417 = 1311313) B1311313
theorem B1748435 : Blo 1164640 1748435 := bstep (se 1 (by rfl) ⟨1311326, by rfl⟩ : syracuseStep 1748435 = 2622653) B2622653
theorem B14167523 : Blo 1164640 14167523 := bstep (se 1 (by rfl) ⟨10625642, by rfl⟩ : syracuseStep 14167523 = 21251285) B21251285
theorem B1748465 : Blo 1164640 1748465 := bstep (se 2 (by rfl) ⟨655674, by rfl⟩ : syracuseStep 1748465 = 1311349) B1311349
theorem B1748483 : Blo 1164640 1748483 := bstep (se 1 (by rfl) ⟨1311362, by rfl⟩ : syracuseStep 1748483 = 2622725) B2622725
theorem B4197901 : Blo 1164640 4197901 := bstep (se 3 (by rfl) ⟨787106, by rfl⟩ : syracuseStep 4197901 = 1574213) B1574213
theorem B1748513 : Blo 1164640 1748513 := bstep (se 2 (by rfl) ⟨655692, by rfl⟩ : syracuseStep 1748513 = 1311385) B1311385
theorem B3935789 : Blo 1164640 3935789 := bstep (se 3 (by rfl) ⟨737960, by rfl⟩ : syracuseStep 3935789 = 1475921) B1475921
theorem B1748531 : Blo 1164640 1748531 := bstep (se 1 (by rfl) ⟨1311398, by rfl⟩ : syracuseStep 1748531 = 2622797) B2622797
theorem B1748561 : Blo 1164640 1748561 := bstep (se 2 (by rfl) ⟨655710, by rfl⟩ : syracuseStep 1748561 = 1311421) B1311421
theorem B1748579 : Blo 1164640 1748579 := bstep (se 1 (by rfl) ⟨1311434, by rfl⟩ : syracuseStep 1748579 = 2622869) B2622869
theorem B3935843 : Blo 1164640 3935843 := bstep (se 1 (by rfl) ⟨2951882, by rfl⟩ : syracuseStep 3935843 = 5903765) B5903765
theorem B1748609 : Blo 1164640 1748609 := bstep (se 2 (by rfl) ⟨655728, by rfl⟩ : syracuseStep 1748609 = 1311457) B1311457
theorem B1748627 : Blo 1164640 1748627 := bstep (se 1 (by rfl) ⟨1311470, by rfl⟩ : syracuseStep 1748627 = 2622941) B2622941
theorem B3149485 : Blo 1164640 3149485 := bstep (se 3 (by rfl) ⟨590528, by rfl⟩ : syracuseStep 3149485 = 1181057) B1181057
theorem B1748657 : Blo 1164640 1748657 := bstep (se 2 (by rfl) ⟨655746, by rfl⟩ : syracuseStep 1748657 = 1311493) B1311493
theorem B1748675 : Blo 1164640 1748675 := bstep (se 1 (by rfl) ⟨1311506, by rfl⟩ : syracuseStep 1748675 = 2623013) B2623013
theorem B1748705 : Blo 1164640 1748705 := bstep (se 2 (by rfl) ⟨655764, by rfl⟩ : syracuseStep 1748705 = 1311529) B1311529
theorem B1748723 : Blo 1164640 1748723 := bstep (se 1 (by rfl) ⟨1311542, by rfl⟩ : syracuseStep 1748723 = 2623085) B2623085
theorem B1748753 : Blo 1164640 1748753 := bstep (se 2 (by rfl) ⟨655782, by rfl⟩ : syracuseStep 1748753 = 1311565) B1311565
theorem B4484899 : Blo 1164640 4484899 := bstep (se 1 (by rfl) ⟨3363674, by rfl⟩ : syracuseStep 4484899 = 6727349) B6727349
theorem B1748771 : Blo 1164640 1748771 := bstep (se 1 (by rfl) ⟨1311578, by rfl⟩ : syracuseStep 1748771 = 2623157) B2623157
theorem B1748801 : Blo 1164640 1748801 := bstep (se 2 (by rfl) ⟨655800, by rfl⟩ : syracuseStep 1748801 = 1311601) B1311601
theorem B1748819 : Blo 1164640 1748819 := bstep (se 1 (by rfl) ⟨1311614, by rfl⟩ : syracuseStep 1748819 = 2623229) B2623229
theorem B1748849 : Blo 1164640 1748849 := bstep (se 2 (by rfl) ⟨655818, by rfl⟩ : syracuseStep 1748849 = 1311637) B1311637
theorem B3936113 : Blo 1164640 3936113 := bstep (se 2 (by rfl) ⟨1476042, by rfl⟩ : syracuseStep 3936113 = 2952085) B2952085
theorem B1748867 : Blo 1164640 1748867 := bstep (se 1 (by rfl) ⟨1311650, by rfl⟩ : syracuseStep 1748867 = 2623301) B2623301
theorem B1748897 : Blo 1164640 1748897 := bstep (se 2 (by rfl) ⟨655836, by rfl⟩ : syracuseStep 1748897 = 1311673) B1311673
theorem B1748915 : Blo 1164640 1748915 := bstep (se 1 (by rfl) ⟨1311686, by rfl⟩ : syracuseStep 1748915 = 2623373) B2623373
theorem B1748945 : Blo 1164640 1748945 := bstep (se 2 (by rfl) ⟨655854, by rfl⟩ : syracuseStep 1748945 = 1311709) B1311709
theorem B5902307 : Blo 1164640 5902307 := bstep (se 1 (by rfl) ⟨4426730, by rfl⟩ : syracuseStep 5902307 = 8853461) B8853461
theorem B1748963 : Blo 1164640 1748963 := bstep (se 1 (by rfl) ⟨1311722, by rfl⟩ : syracuseStep 1748963 = 2623445) B2623445
theorem B1748993 : Blo 1164640 1748993 := bstep (se 2 (by rfl) ⟨655872, by rfl⟩ : syracuseStep 1748993 = 1311745) B1311745
theorem B1749011 : Blo 1164640 1749011 := bstep (se 1 (by rfl) ⟨1311758, by rfl⟩ : syracuseStep 1749011 = 2623517) B2623517
theorem B1749041 : Blo 1164640 1749041 := bstep (se 2 (by rfl) ⟨655890, by rfl⟩ : syracuseStep 1749041 = 1311781) B1311781
theorem B1749059 : Blo 1164640 1749059 := bstep (se 1 (by rfl) ⟨1311794, by rfl⟩ : syracuseStep 1749059 = 2623589) B2623589
theorem B1749089 : Blo 1164640 1749089 := bstep (se 2 (by rfl) ⟨655908, by rfl⟩ : syracuseStep 1749089 = 1311817) B1311817
theorem B1749107 : Blo 1164640 1749107 := bstep (se 1 (by rfl) ⟨1311830, by rfl⟩ : syracuseStep 1749107 = 2623661) B2623661
theorem B1347715 : Blo 1164640 1347715 := bstep (se 1 (by rfl) ⟨1010786, by rfl⟩ : syracuseStep 1347715 = 2021573) B2021573
theorem B1749137 : Blo 1164640 1749137 := bstep (se 2 (by rfl) ⟨655926, by rfl⟩ : syracuseStep 1749137 = 1311853) B1311853
theorem B1749155 : Blo 1164640 1749155 := bstep (se 1 (by rfl) ⟨1311866, by rfl⟩ : syracuseStep 1749155 = 2623733) B2623733
theorem B1749185 : Blo 1164640 1749185 := bstep (se 2 (by rfl) ⟨655944, by rfl⟩ : syracuseStep 1749185 = 1311889) B1311889
theorem B1749203 : Blo 1164640 1749203 := bstep (se 1 (by rfl) ⟨1311902, by rfl⟩ : syracuseStep 1749203 = 2623805) B2623805
theorem B1749233 : Blo 1164640 1749233 := bstep (se 2 (by rfl) ⟨655962, by rfl⟩ : syracuseStep 1749233 = 1311925) B1311925
theorem B1749251 : Blo 1164640 1749251 := bstep (se 1 (by rfl) ⟨1311938, by rfl⟩ : syracuseStep 1749251 = 2623877) B2623877
theorem B1749281 : Blo 1164640 1749281 := bstep (se 2 (by rfl) ⟨655980, by rfl⟩ : syracuseStep 1749281 = 1311961) B1311961
theorem B4428067 : Blo 1164640 4428067 := bstep (se 1 (by rfl) ⟨3321050, by rfl⟩ : syracuseStep 4428067 = 6642101) B6642101
theorem B6820145 : Blo 1164640 6820145 := bstep (se 2 (by rfl) ⟨2557554, by rfl⟩ : syracuseStep 6820145 = 5115109) B5115109
theorem B1749299 : Blo 1164640 1749299 := bstep (se 1 (by rfl) ⟨1311974, by rfl⟩ : syracuseStep 1749299 = 2623949) B2623949
theorem B1749329 : Blo 1164640 1749329 := bstep (se 2 (by rfl) ⟨655998, by rfl⟩ : syracuseStep 1749329 = 1311997) B1311997
theorem B1749347 : Blo 1164640 1749347 := bstep (se 1 (by rfl) ⟨1312010, by rfl⟩ : syracuseStep 1749347 = 2624021) B2624021
theorem B9949553 : Blo 1164640 9949553 := bstep (se 2 (by rfl) ⟨3731082, by rfl⟩ : syracuseStep 9949553 = 7462165) B7462165
theorem B1749377 : Blo 1164640 1749377 := bstep (se 2 (by rfl) ⟨656016, by rfl⟩ : syracuseStep 1749377 = 1312033) B1312033
theorem B1749395 : Blo 1164640 1749395 := bstep (se 1 (by rfl) ⟨1312046, by rfl⟩ : syracuseStep 1749395 = 2624093) B2624093
theorem B1749425 : Blo 1164640 1749425 := bstep (se 2 (by rfl) ⟨656034, by rfl⟩ : syracuseStep 1749425 = 1312069) B1312069
theorem B1749443 : Blo 1164640 1749443 := bstep (se 1 (by rfl) ⟨1312082, by rfl⟩ : syracuseStep 1749443 = 2624165) B2624165
theorem B1749473 : Blo 1164640 1749473 := bstep (se 2 (by rfl) ⟨656052, by rfl⟩ : syracuseStep 1749473 = 1312105) B1312105
theorem B1749491 : Blo 1164640 1749491 := bstep (se 1 (by rfl) ⟨1312118, by rfl⟩ : syracuseStep 1749491 = 2624237) B2624237
theorem B1749521 : Blo 1164640 1749521 := bstep (se 2 (by rfl) ⟨656070, by rfl⟩ : syracuseStep 1749521 = 1312141) B1312141
theorem B1749539 : Blo 1164640 1749539 := bstep (se 1 (by rfl) ⟨1312154, by rfl⟩ : syracuseStep 1749539 = 2624309) B2624309
theorem B15340085 : Blo 1164640 15340085 := bstep (se 5 (by rfl) ⟨719066, by rfl⟩ : syracuseStep 15340085 = 1438133) B1438133
theorem B1749569 : Blo 1164640 1749569 := bstep (se 2 (by rfl) ⟨656088, by rfl⟩ : syracuseStep 1749569 = 1312177) B1312177
theorem B1749587 : Blo 1164640 1749587 := bstep (se 1 (by rfl) ⟨1312190, by rfl⟩ : syracuseStep 1749587 = 2624381) B2624381
theorem B10629731 : Blo 1164640 10629731 := bstep (se 1 (by rfl) ⟨7972298, by rfl⟩ : syracuseStep 10629731 = 15944597) B15944597
theorem B1659523 : Blo 1164640 1659523 := bstep (se 1 (by rfl) ⟨1244642, by rfl⟩ : syracuseStep 1659523 = 2489285) B2489285
theorem B6640325 : Blo 1164640 6640325 := bstep (se 4 (by rfl) ⟨622530, by rfl⟩ : syracuseStep 6640325 = 1245061) B1245061
theorem B5903117 : Blo 1164640 5903117 := bstep (se 3 (by rfl) ⟨1106834, by rfl⟩ : syracuseStep 5903117 = 2213669) B2213669
theorem B2798563 : Blo 1164640 2798563 := bstep (se 1 (by rfl) ⟨2098922, by rfl⟩ : syracuseStep 2798563 = 4197845) B4197845
theorem B2659331 : Blo 1164640 2659331 := bstep (se 1 (by rfl) ⟨1994498, by rfl⟩ : syracuseStep 2659331 = 3988997) B3988997
theorem B7468037 : Blo 1164640 7468037 := bstep (se 4 (by rfl) ⟨700128, by rfl⟩ : syracuseStep 7468037 = 1400257) B1400257
theorem B7091333 : Blo 1164640 7091333 := bstep (se 4 (by rfl) ⟨664812, by rfl⟩ : syracuseStep 7091333 = 1329625) B1329625
theorem B3151021 : Blo 1164640 3151021 := bstep (se 3 (by rfl) ⟨590816, by rfl⟩ : syracuseStep 3151021 = 1181633) B1181633
theorem B3732749 : Blo 1164640 3732749 := bstep (se 3 (by rfl) ⟨699890, by rfl⟩ : syracuseStep 3732749 = 1399781) B1399781
theorem B3151217 : Blo 1164640 3151217 := bstep (se 2 (by rfl) ⟨1181706, by rfl⟩ : syracuseStep 3151217 = 2363413) B2363413
theorem B3642989 : Blo 1164640 3642989 := bstep (se 3 (by rfl) ⟨683060, by rfl⟩ : syracuseStep 3642989 = 1366121) B1366121
theorem B2799235 : Blo 1164640 2799235 := bstep (se 1 (by rfl) ⟨2099426, by rfl⟩ : syracuseStep 2799235 = 4198853) B4198853
theorem B2021059 : Blo 1164640 2021059 := bstep (se 1 (by rfl) ⟨1515794, by rfl⟩ : syracuseStep 2021059 = 3031589) B3031589
theorem B1660657 : Blo 1164640 1660657 := bstep (se 2 (by rfl) ⟨622746, by rfl⟩ : syracuseStep 1660657 = 1245493) B1245493
theorem B1660753 : Blo 1164640 1660753 := bstep (se 2 (by rfl) ⟨622782, by rfl⟩ : syracuseStep 1660753 = 1245565) B1245565
theorem B1865747 : Blo 1164640 1865747 := bstep (se 1 (by rfl) ⟨1399310, by rfl⟩ : syracuseStep 1865747 = 2798621) B2798621
theorem B2799697 : Blo 1164640 2799697 := bstep (se 2 (by rfl) ⟨1049886, by rfl⟩ : syracuseStep 2799697 = 2099773) B2099773
theorem B4978979 : Blo 1164640 4978979 := bstep (se 1 (by rfl) ⟨3734234, by rfl⟩ : syracuseStep 4978979 = 7468469) B7468469
theorem B1866035 : Blo 1164640 1866035 := bstep (se 1 (by rfl) ⟨1399526, by rfl⟩ : syracuseStep 1866035 = 2799053) B2799053
theorem B3734029 : Blo 1164640 3734029 := bstep (se 3 (by rfl) ⟨700130, by rfl⟩ : syracuseStep 3734029 = 1400261) B1400261
theorem B3152429 : Blo 1164640 3152429 := bstep (se 3 (by rfl) ⟨591080, by rfl⟩ : syracuseStep 3152429 = 1182161) B1182161
theorem B45439541 : Blo 1164640 45439541 := bstep (se 5 (by rfl) ⟨2129978, by rfl⟩ : syracuseStep 45439541 = 4259957) B4259957
theorem B4422221 : Blo 1164640 4422221 := bstep (se 3 (by rfl) ⟨829166, by rfl⟩ : syracuseStep 4422221 = 1658333) B1658333
theorem B6634061 : Blo 1164640 6634061 := bstep (se 3 (by rfl) ⟨1243886, by rfl⟩ : syracuseStep 6634061 = 2487773) B2487773
theorem B1866451 : Blo 1164640 1866451 := bstep (se 1 (by rfl) ⟨1399838, by rfl⟩ : syracuseStep 1866451 = 2799677) B2799677
theorem B3152621 : Blo 1164640 3152621 := bstep (se 3 (by rfl) ⟨591116, by rfl⟩ : syracuseStep 3152621 = 1182233) B1182233
theorem B3930929 : Blo 1164640 3930929 := bstep (se 2 (by rfl) ⟨1474098, by rfl⟩ : syracuseStep 3930929 = 2948197) B2948197
theorem B1243955 : Blo 1164640 1243955 := bstep (se 1 (by rfl) ⟨932966, by rfl⟩ : syracuseStep 1243955 = 1865933) B1865933
theorem B13278005 : Blo 1164640 13278005 := bstep (se 5 (by rfl) ⟨622406, by rfl⟩ : syracuseStep 13278005 = 1244813) B1244813
theorem B5897123 : Blo 1164640 5897123 := bstep (se 1 (by rfl) ⟨4422842, by rfl⟩ : syracuseStep 5897123 = 8845685) B8845685
theorem B2489251 : Blo 1164640 2489251 := bstep (se 1 (by rfl) ⟨1866938, by rfl⟩ : syracuseStep 2489251 = 3733877) B3733877
theorem B2948035 : Blo 1164640 2948035 := bstep (se 1 (by rfl) ⟨2211026, by rfl⟩ : syracuseStep 2948035 = 4422053) B4422053
theorem B1727443 : Blo 1164640 1727443 := bstep (se 1 (by rfl) ⟨1295582, by rfl⟩ : syracuseStep 1727443 = 2591165) B2591165
theorem B1866721 : Blo 1164640 1866721 := bstep (se 2 (by rfl) ⟨700020, by rfl⟩ : syracuseStep 1866721 = 1400041) B1400041
theorem B3734531 : Blo 1164640 3734531 := bstep (se 1 (by rfl) ⟨2800898, by rfl⟩ : syracuseStep 3734531 = 5601797) B5601797
theorem B2948177 : Blo 1164640 2948177 := bstep (se 2 (by rfl) ⟨1105566, by rfl⟩ : syracuseStep 2948177 = 2211133) B2211133
theorem B2620529 : Blo 1164640 2620529 := bstep (se 2 (by rfl) ⟨982698, by rfl⟩ : syracuseStep 2620529 = 1965397) B1965397
theorem B2620547 : Blo 1164640 2620547 := bstep (se 1 (by rfl) ⟨1965410, by rfl⟩ : syracuseStep 2620547 = 3930821) B3930821
theorem B4201649 : Blo 1164640 4201649 := bstep (se 2 (by rfl) ⟨1575618, by rfl⟩ : syracuseStep 4201649 = 3151237) B3151237
theorem B1866977 : Blo 1164640 1866977 := bstep (se 2 (by rfl) ⟨700116, by rfl⟩ : syracuseStep 1866977 = 1400233) B1400233
theorem B3317041 : Blo 1164640 3317041 := bstep (se 2 (by rfl) ⟨1243890, by rfl⟩ : syracuseStep 3317041 = 2487781) B2487781
theorem B1965377 : Blo 1164640 1965377 := bstep (se 2 (by rfl) ⟨737016, by rfl⟩ : syracuseStep 1965377 = 1474033) B1474033
theorem B3931469 : Blo 1164640 3931469 := bstep (se 3 (by rfl) ⟨737150, by rfl⟩ : syracuseStep 3931469 = 1474301) B1474301
theorem B4423025 : Blo 1164640 4423025 := bstep (se 2 (by rfl) ⟨1658634, by rfl⟩ : syracuseStep 4423025 = 3317269) B3317269
theorem B3931523 : Blo 1164640 3931523 := bstep (se 1 (by rfl) ⟨2948642, by rfl⟩ : syracuseStep 3931523 = 5897285) B5897285
theorem B2620817 : Blo 1164640 2620817 := bstep (se 2 (by rfl) ⟨982806, by rfl⟩ : syracuseStep 2620817 = 1965613) B1965613
theorem B2620835 : Blo 1164640 2620835 := bstep (se 1 (by rfl) ⟨1965626, by rfl⟩ : syracuseStep 2620835 = 3931253) B3931253
theorem B1965505 : Blo 1164640 1965505 := bstep (se 2 (by rfl) ⟨737064, by rfl⟩ : syracuseStep 1965505 = 1474129) B1474129
theorem B1965539 : Blo 1164640 1965539 := bstep (se 1 (by rfl) ⟨1474154, by rfl⟩ : syracuseStep 1965539 = 2948309) B2948309
theorem B6634993 : Blo 1164640 6634993 := bstep (se 2 (by rfl) ⟨2488122, by rfl⟩ : syracuseStep 6634993 = 4976245) B4976245
theorem B1965667 : Blo 1164640 1965667 := bstep (se 1 (by rfl) ⟨1474250, by rfl⟩ : syracuseStep 1965667 = 2948501) B2948501
theorem B1310323 : Blo 1164640 1310323 := bstep (se 1 (by rfl) ⟨982742, by rfl⟩ : syracuseStep 1310323 = 1965485) B1965485
theorem B3931793 : Blo 1164640 3931793 := bstep (se 2 (by rfl) ⟨1474422, by rfl⟩ : syracuseStep 3931793 = 2948845) B2948845
theorem B1474195 : Blo 1164640 1474195 := bstep (se 1 (by rfl) ⟨1105646, by rfl⟩ : syracuseStep 1474195 = 2211293) B2211293
theorem B2621105 : Blo 1164640 2621105 := bstep (se 2 (by rfl) ⟨982914, by rfl⟩ : syracuseStep 2621105 = 1965829) B1965829
theorem B2621123 : Blo 1164640 2621123 := bstep (se 1 (by rfl) ⟨1965842, by rfl⟩ : syracuseStep 2621123 = 3931685) B3931685
theorem B5897933 : Blo 1164640 5897933 := bstep (se 3 (by rfl) ⟨1105862, by rfl⟩ : syracuseStep 5897933 = 2211725) B2211725
theorem B3546833 : Blo 1164640 3546833 := bstep (se 2 (by rfl) ⟨1330062, by rfl⟩ : syracuseStep 3546833 = 2660125) B2660125
theorem B1244899 : Blo 1164640 1244899 := bstep (se 1 (by rfl) ⟨933674, by rfl⟩ : syracuseStep 1244899 = 1867349) B1867349
theorem B1965809 : Blo 1164640 1965809 := bstep (se 2 (by rfl) ⟨737178, by rfl⟩ : syracuseStep 1965809 = 1474357) B1474357
theorem B1474291 : Blo 1164640 1474291 := bstep (se 1 (by rfl) ⟨1105718, by rfl⟩ : syracuseStep 1474291 = 2211437) B2211437
theorem B2490097 : Blo 1164640 2490097 := bstep (se 2 (by rfl) ⟨933786, by rfl⟩ : syracuseStep 2490097 = 1867573) B1867573
theorem B1310467 : Blo 1164640 1310467 := bstep (se 1 (by rfl) ⟨982850, by rfl⟩ : syracuseStep 1310467 = 1965701) B1965701
theorem B12132109 : Blo 1164640 12132109 := bstep (se 3 (by rfl) ⟨2274770, by rfl⟩ : syracuseStep 12132109 = 4549541) B4549541
theorem B64659221 : Blo 1164640 64659221 := bstep (se 6 (by rfl) ⟨1515450, by rfl⟩ : syracuseStep 64659221 = 3030901) B3030901
theorem B2211619 : Blo 1164640 2211619 := bstep (se 1 (by rfl) ⟨1658714, by rfl⟩ : syracuseStep 2211619 = 3317429) B3317429
theorem B1965937 : Blo 1164640 1965937 := bstep (se 2 (by rfl) ⟨737226, by rfl⟩ : syracuseStep 1965937 = 1474453) B1474453
theorem B1310611 : Blo 1164640 1310611 := bstep (se 1 (by rfl) ⟨982958, by rfl⟩ : syracuseStep 1310611 = 1965917) B1965917
theorem B1965971 : Blo 1164640 1965971 := bstep (se 1 (by rfl) ⟨1474478, by rfl⟩ : syracuseStep 1965971 = 2948957) B2948957
theorem B1892243 : Blo 1164640 1892243 := bstep (se 1 (by rfl) ⟨1419182, by rfl⟩ : syracuseStep 1892243 = 2838365) B2838365
theorem B1867681 : Blo 1164640 1867681 := bstep (se 2 (by rfl) ⟨700380, by rfl⟩ : syracuseStep 1867681 = 1400761) B1400761
theorem B2211779 : Blo 1164640 2211779 := bstep (se 1 (by rfl) ⟨1658834, by rfl⟩ : syracuseStep 2211779 = 3317669) B3317669
theorem B1400771 : Blo 1164640 1400771 := bstep (se 1 (by rfl) ⟨1050578, by rfl⟩ : syracuseStep 1400771 = 2101157) B2101157
theorem B2621393 : Blo 1164640 2621393 := bstep (se 2 (by rfl) ⟨983022, by rfl⟩ : syracuseStep 2621393 = 1966045) B1966045
theorem B2621411 : Blo 1164640 2621411 := bstep (se 1 (by rfl) ⟨1966058, by rfl⟩ : syracuseStep 2621411 = 3932117) B3932117
theorem B1400819 : Blo 1164640 1400819 := bstep (se 1 (by rfl) ⟨1050614, by rfl⟩ : syracuseStep 1400819 = 2101229) B2101229
theorem B5898257 : Blo 1164640 5898257 := bstep (se 2 (by rfl) ⟨2211846, by rfl⟩ : syracuseStep 5898257 = 4423693) B4423693
theorem B2621465 : Blo 1164640 2621465 := bstep (se 2 (by rfl) ⟨983049, by rfl⟩ : syracuseStep 2621465 = 1966099) B1966099
theorem B3932225 : Blo 1164640 3932225 := bstep (se 2 (by rfl) ⟨1474584, by rfl⟩ : syracuseStep 3932225 = 2949169) B2949169
theorem B19914821 : Blo 1164640 19914821 := bstep (se 4 (by rfl) ⟨1867014, by rfl⟩ : syracuseStep 19914821 = 3734029) B3734029
theorem B1310827 : Blo 1164640 1310827 := bstep (se 1 (by rfl) ⟨983120, by rfl⟩ : syracuseStep 1310827 = 1966241) B1966241
theorem B2621555 : Blo 1164640 2621555 := bstep (se 1 (by rfl) ⟨1966166, by rfl⟩ : syracuseStep 2621555 = 3932333) B3932333
theorem B2621591 : Blo 1164640 2621591 := bstep (se 1 (by rfl) ⟨1966193, by rfl⟩ : syracuseStep 2621591 = 3932387) B3932387
theorem B9961649 : Blo 1164640 9961649 := bstep (se 2 (by rfl) ⟨3735618, by rfl⟩ : syracuseStep 9961649 = 7471237) B7471237
theorem B5898419 : Blo 1164640 5898419 := bstep (se 1 (by rfl) ⟨4423814, by rfl⟩ : syracuseStep 5898419 = 8847629) B8847629
theorem B4546763 : Blo 1164640 4546763 := bstep (se 1 (by rfl) ⟨3410072, by rfl⟩ : syracuseStep 4546763 = 6820145) B6820145
theorem B1966295 : Blo 1164640 1966295 := bstep (se 1 (by rfl) ⟨1474721, by rfl⟩ : syracuseStep 1966295 = 2949443) B2949443
theorem B1310935 : Blo 1164640 1310935 := bstep (se 1 (by rfl) ⟨983201, by rfl⟩ : syracuseStep 1310935 = 1966403) B1966403
theorem B2490583 : Blo 1164640 2490583 := bstep (se 1 (by rfl) ⟨1867937, by rfl⟩ : syracuseStep 2490583 = 3735875) B3735875
theorem B3735773 : Blo 1164640 3735773 := bstep (se 3 (by rfl) ⟨700457, by rfl⟩ : syracuseStep 3735773 = 1400915) B1400915
theorem B5112115 : Blo 1164640 5112115 := bstep (se 1 (by rfl) ⟨3834086, by rfl⟩ : syracuseStep 5112115 = 7668173) B7668173
theorem B2621771 : Blo 1164640 2621771 := bstep (se 1 (by rfl) ⟨1966328, by rfl⟩ : syracuseStep 2621771 = 3932657) B3932657
theorem B1966423 : Blo 1164640 1966423 := bstep (se 1 (by rfl) ⟨1474817, by rfl⟩ : syracuseStep 1966423 = 2949635) B2949635
theorem B2212211 : Blo 1164640 2212211 := bstep (se 1 (by rfl) ⟨1659158, by rfl⟩ : syracuseStep 2212211 = 3318317) B3318317
theorem B2621825 : Blo 1164640 2621825 := bstep (se 2 (by rfl) ⟨983184, by rfl⟩ : syracuseStep 2621825 = 1966369) B1966369
theorem B1311115 : Blo 1164640 1311115 := bstep (se 1 (by rfl) ⟨983336, by rfl⟩ : syracuseStep 1311115 = 1966673) B1966673
theorem B1311223 : Blo 1164640 1311223 := bstep (se 1 (by rfl) ⟨983417, by rfl⟩ : syracuseStep 1311223 = 1966835) B1966835
theorem B2212363 : Blo 1164640 2212363 := bstep (se 1 (by rfl) ⟨1659272, by rfl⟩ : syracuseStep 2212363 = 3318545) B3318545
theorem B2949655 : Blo 1164640 2949655 := bstep (se 1 (by rfl) ⟨2212241, by rfl⟩ : syracuseStep 2949655 = 4424483) B4424483
theorem B163627573 : Blo 1164640 163627573 := bstep (se 5 (by rfl) ⟨7670042, by rfl⟩ : syracuseStep 163627573 = 15340085) B15340085
theorem B2622041 : Blo 1164640 2622041 := bstep (se 2 (by rfl) ⟨983265, by rfl⟩ : syracuseStep 2622041 = 1966531) B1966531
theorem B3932765 : Blo 1164640 3932765 := bstep (se 3 (by rfl) ⟨737393, by rfl⟩ : syracuseStep 3932765 = 1474787) B1474787
theorem B1311403 : Blo 1164640 1311403 := bstep (se 1 (by rfl) ⟨983552, by rfl⟩ : syracuseStep 1311403 = 1967105) B1967105
theorem B2622131 : Blo 1164640 2622131 := bstep (se 1 (by rfl) ⟨1966598, by rfl⟩ : syracuseStep 2622131 = 3933197) B3933197
theorem B2622167 : Blo 1164640 2622167 := bstep (se 1 (by rfl) ⟨1966625, by rfl⟩ : syracuseStep 2622167 = 3933251) B3933251
theorem B4727555 : Blo 1164640 4727555 := bstep (se 1 (by rfl) ⟨3545666, by rfl⟩ : syracuseStep 4727555 = 7091333) B7091333
theorem B1311511 : Blo 1164640 1311511 := bstep (se 1 (by rfl) ⟨983633, by rfl⟩ : syracuseStep 1311511 = 1967267) B1967267
theorem B14943041 : Blo 1164640 14943041 := bstep (se 2 (by rfl) ⟨5603640, by rfl⟩ : syracuseStep 14943041 = 11207281) B11207281
theorem B2212697 : Blo 1164640 2212697 := bstep (se 2 (by rfl) ⟨829761, by rfl⟩ : syracuseStep 2212697 = 1659523) B1659523
theorem B2622347 : Blo 1164640 2622347 := bstep (se 1 (by rfl) ⟨1966760, by rfl⟩ : syracuseStep 2622347 = 3933521) B3933521
theorem B2622401 : Blo 1164640 2622401 := bstep (se 2 (by rfl) ⟨983400, by rfl⟩ : syracuseStep 2622401 = 1966801) B1966801
theorem B4424651 : Blo 1164640 4424651 := bstep (se 1 (by rfl) ⟨3318488, by rfl⟩ : syracuseStep 4424651 = 6636977) B6636977
theorem B2950091 : Blo 1164640 2950091 := bstep (se 1 (by rfl) ⟨2212568, by rfl⟩ : syracuseStep 2950091 = 4425137) B4425137
theorem B1967051 : Blo 1164640 1967051 := bstep (se 1 (by rfl) ⟨1475288, by rfl⟩ : syracuseStep 1967051 = 2950577) B2950577
theorem B1311691 : Blo 1164640 1311691 := bstep (se 1 (by rfl) ⟨983768, by rfl⟩ : syracuseStep 1311691 = 1967537) B1967537
theorem B4424665 : Blo 1164640 4424665 := bstep (se 2 (by rfl) ⟨1659249, by rfl⟩ : syracuseStep 4424665 = 3318499) B3318499
theorem B1311799 : Blo 1164640 1311799 := bstep (se 1 (by rfl) ⟨983849, by rfl⟩ : syracuseStep 1311799 = 1967699) B1967699
theorem B1967179 : Blo 1164640 1967179 := bstep (se 1 (by rfl) ⟨1475384, by rfl⟩ : syracuseStep 1967179 = 2950769) B2950769
theorem B5604427 : Blo 1164640 5604427 := bstep (se 1 (by rfl) ⟨4203320, by rfl⟩ : syracuseStep 5604427 = 8406641) B8406641
theorem B2622617 : Blo 1164640 2622617 := bstep (se 2 (by rfl) ⟨983481, by rfl⟩ : syracuseStep 2622617 = 1966963) B1966963
theorem B9962675 : Blo 1164640 9962675 := bstep (se 1 (by rfl) ⟨7472006, by rfl⟩ : syracuseStep 9962675 = 14944013) B14944013
theorem B8848601 : Blo 1164640 8848601 := bstep (se 2 (by rfl) ⟨3318225, by rfl⟩ : syracuseStep 8848601 = 6636451) B6636451
theorem B3319001 : Blo 1164640 3319001 := bstep (se 2 (by rfl) ⟨1244625, by rfl⟩ : syracuseStep 3319001 = 2489251) B2489251
theorem B1967321 : Blo 1164640 1967321 := bstep (se 2 (by rfl) ⟨737745, by rfl⟩ : syracuseStep 1967321 = 1475491) B1475491
theorem B1311979 : Blo 1164640 1311979 := bstep (se 1 (by rfl) ⟨983984, by rfl⟩ : syracuseStep 1311979 = 1967969) B1967969
theorem B2622707 : Blo 1164640 2622707 := bstep (se 1 (by rfl) ⟨1967030, by rfl⟩ : syracuseStep 2622707 = 3934061) B3934061
theorem B2622743 : Blo 1164640 2622743 := bstep (se 1 (by rfl) ⟨1967057, by rfl⟩ : syracuseStep 2622743 = 3934115) B3934115
theorem B2303257 : Blo 1164640 2303257 := bstep (se 2 (by rfl) ⟨863721, by rfl⟩ : syracuseStep 2303257 = 1727443) B1727443
theorem B2950465 : Blo 1164640 2950465 := bstep (se 2 (by rfl) ⟨1106424, by rfl⟩ : syracuseStep 2950465 = 2212849) B2212849
theorem B1312087 : Blo 1164640 1312087 := bstep (se 1 (by rfl) ⟨984065, by rfl⟩ : syracuseStep 1312087 = 1968131) B1968131
theorem B1967449 : Blo 1164640 1967449 := bstep (se 2 (by rfl) ⟨737793, by rfl⟩ : syracuseStep 1967449 = 1475587) B1475587
theorem B1164651 : Blo 1164640 1164651 := bstep (se 1 (by rfl) ⟨873488, by rfl⟩ : syracuseStep 1164651 = 1746977) B1746977
theorem B1164663 : Blo 1164640 1164663 := bstep (se 1 (by rfl) ⟨873497, by rfl⟩ : syracuseStep 1164663 = 1746995) B1746995
theorem B1164683 : Blo 1164640 1164683 := bstep (se 1 (by rfl) ⟨873512, by rfl⟩ : syracuseStep 1164683 = 1747025) B1747025
theorem B1164695 : Blo 1164640 1164695 := bstep (se 1 (by rfl) ⟨873521, by rfl⟩ : syracuseStep 1164695 = 1747043) B1747043
theorem B1164715 : Blo 1164640 1164715 := bstep (se 1 (by rfl) ⟨873536, by rfl⟩ : syracuseStep 1164715 = 1747073) B1747073
theorem B1164727 : Blo 1164640 1164727 := bstep (se 1 (by rfl) ⟨873545, by rfl⟩ : syracuseStep 1164727 = 1747091) B1747091
theorem B1164747 : Blo 1164640 1164747 := bstep (se 1 (by rfl) ⟨873560, by rfl⟩ : syracuseStep 1164747 = 1747121) B1747121
theorem B2622923 : Blo 1164640 2622923 := bstep (se 1 (by rfl) ⟨1967192, by rfl⟩ : syracuseStep 2622923 = 3934385) B3934385
theorem B1164759 : Blo 1164640 1164759 := bstep (se 1 (by rfl) ⟨873569, by rfl⟩ : syracuseStep 1164759 = 1747139) B1747139
theorem B2213335 : Blo 1164640 2213335 := bstep (se 1 (by rfl) ⟨1660001, by rfl⟩ : syracuseStep 2213335 = 3320003) B3320003
theorem B1164779 : Blo 1164640 1164779 := bstep (se 1 (by rfl) ⟨873584, by rfl⟩ : syracuseStep 1164779 = 1747169) B1747169
theorem B1164791 : Blo 1164640 1164791 := bstep (se 1 (by rfl) ⟨873593, by rfl⟩ : syracuseStep 1164791 = 1747187) B1747187
theorem B2622977 : Blo 1164640 2622977 := bstep (se 2 (by rfl) ⟨983616, by rfl⟩ : syracuseStep 2622977 = 1967233) B1967233
theorem B1164811 : Blo 1164640 1164811 := bstep (se 1 (by rfl) ⟨873608, by rfl⟩ : syracuseStep 1164811 = 1747217) B1747217
theorem B1164823 : Blo 1164640 1164823 := bstep (se 1 (by rfl) ⟨873617, by rfl⟩ : syracuseStep 1164823 = 1747235) B1747235
theorem B3319319 : Blo 1164640 3319319 := bstep (se 1 (by rfl) ⟨2489489, by rfl⟩ : syracuseStep 3319319 = 4978979) B4978979
theorem B1164843 : Blo 1164640 1164843 := bstep (se 1 (by rfl) ⟨873632, by rfl⟩ : syracuseStep 1164843 = 1747265) B1747265
theorem B1164855 : Blo 1164640 1164855 := bstep (se 1 (by rfl) ⟨873641, by rfl⟩ : syracuseStep 1164855 = 1747283) B1747283
theorem B1164875 : Blo 1164640 1164875 := bstep (se 1 (by rfl) ⟨873656, by rfl⟩ : syracuseStep 1164875 = 1747313) B1747313
theorem B1164887 : Blo 1164640 1164887 := bstep (se 1 (by rfl) ⟨873665, by rfl⟩ : syracuseStep 1164887 = 1747331) B1747331
theorem B28345949 : Blo 1164640 28345949 := bstep (se 3 (by rfl) ⟨5314865, by rfl⟩ : syracuseStep 28345949 = 10629731) B10629731
theorem B1164907 : Blo 1164640 1164907 := bstep (se 1 (by rfl) ⟨873680, by rfl⟩ : syracuseStep 1164907 = 1747361) B1747361
theorem B1164919 : Blo 1164640 1164919 := bstep (se 1 (by rfl) ⟨873689, by rfl⟩ : syracuseStep 1164919 = 1747379) B1747379
theorem B1164939 : Blo 1164640 1164939 := bstep (se 1 (by rfl) ⟨873704, by rfl⟩ : syracuseStep 1164939 = 1747409) B1747409
theorem B1164951 : Blo 1164640 1164951 := bstep (se 1 (by rfl) ⟨873713, by rfl⟩ : syracuseStep 1164951 = 1747427) B1747427
theorem B1164971 : Blo 1164640 1164971 := bstep (se 1 (by rfl) ⟨873728, by rfl⟩ : syracuseStep 1164971 = 1747457) B1747457
theorem B1164983 : Blo 1164640 1164983 := bstep (se 1 (by rfl) ⟨873737, by rfl⟩ : syracuseStep 1164983 = 1747475) B1747475
theorem B1165003 : Blo 1164640 1165003 := bstep (se 1 (by rfl) ⟨873752, by rfl⟩ : syracuseStep 1165003 = 1747505) B1747505
theorem B3933899 : Blo 1164640 3933899 := bstep (se 1 (by rfl) ⟨2950424, by rfl⟩ : syracuseStep 3933899 = 5900849) B5900849
theorem B1165015 : Blo 1164640 1165015 := bstep (se 1 (by rfl) ⟨873761, by rfl⟩ : syracuseStep 1165015 = 1747523) B1747523
theorem B2623193 : Blo 1164640 2623193 := bstep (se 2 (by rfl) ⟨983697, by rfl⟩ : syracuseStep 2623193 = 1967395) B1967395
theorem B1165035 : Blo 1164640 1165035 := bstep (se 1 (by rfl) ⟨873776, by rfl⟩ : syracuseStep 1165035 = 1747553) B1747553
theorem B1165047 : Blo 1164640 1165047 := bstep (se 1 (by rfl) ⟨873785, by rfl⟩ : syracuseStep 1165047 = 1747571) B1747571
theorem B8857349 : Blo 1164640 8857349 := bstep (se 4 (by rfl) ⟨830376, by rfl⟩ : syracuseStep 8857349 = 1660753) B1660753
theorem B1165067 : Blo 1164640 1165067 := bstep (se 1 (by rfl) ⟨873800, by rfl⟩ : syracuseStep 1165067 = 1747601) B1747601
theorem B1165079 : Blo 1164640 1165079 := bstep (se 1 (by rfl) ⟨873809, by rfl⟩ : syracuseStep 1165079 = 1747619) B1747619
theorem B1165099 : Blo 1164640 1165099 := bstep (se 1 (by rfl) ⟨873824, by rfl⟩ : syracuseStep 1165099 = 1747649) B1747649
theorem B2623283 : Blo 1164640 2623283 := bstep (se 1 (by rfl) ⟨1967462, by rfl⟩ : syracuseStep 2623283 = 3934925) B3934925
theorem B1165111 : Blo 1164640 1165111 := bstep (se 1 (by rfl) ⟨873833, by rfl⟩ : syracuseStep 1165111 = 1747667) B1747667
theorem B4482881 : Blo 1164640 4482881 := bstep (se 2 (by rfl) ⟨1681080, by rfl⟩ : syracuseStep 4482881 = 3362161) B3362161
theorem B1165131 : Blo 1164640 1165131 := bstep (se 1 (by rfl) ⟨873848, by rfl⟩ : syracuseStep 1165131 = 1747697) B1747697
theorem B1165143 : Blo 1164640 1165143 := bstep (se 1 (by rfl) ⟨873857, by rfl⟩ : syracuseStep 1165143 = 1747715) B1747715
theorem B2623319 : Blo 1164640 2623319 := bstep (se 1 (by rfl) ⟨1967489, by rfl⟩ : syracuseStep 2623319 = 3934979) B3934979
theorem B1165163 : Blo 1164640 1165163 := bstep (se 1 (by rfl) ⟨873872, by rfl⟩ : syracuseStep 1165163 = 1747745) B1747745
theorem B1165175 : Blo 1164640 1165175 := bstep (se 1 (by rfl) ⟨873881, by rfl⟩ : syracuseStep 1165175 = 1747763) B1747763
theorem B1165195 : Blo 1164640 1165195 := bstep (se 1 (by rfl) ⟨873896, by rfl⟩ : syracuseStep 1165195 = 1747793) B1747793
theorem B1165207 : Blo 1164640 1165207 := bstep (se 1 (by rfl) ⟨873905, by rfl⟩ : syracuseStep 1165207 = 1747811) B1747811
theorem B4425623 : Blo 1164640 4425623 := bstep (se 1 (by rfl) ⟨3319217, by rfl⟩ : syracuseStep 4425623 = 6638435) B6638435
theorem B2951063 : Blo 1164640 2951063 := bstep (se 1 (by rfl) ⟨2213297, by rfl⟩ : syracuseStep 2951063 = 4426595) B4426595
theorem B1968023 : Blo 1164640 1968023 := bstep (se 1 (by rfl) ⟨1476017, by rfl⟩ : syracuseStep 1968023 = 2952035) B2952035
theorem B1165227 : Blo 1164640 1165227 := bstep (se 1 (by rfl) ⟨873920, by rfl⟩ : syracuseStep 1165227 = 1747841) B1747841
theorem B1165239 : Blo 1164640 1165239 := bstep (se 1 (by rfl) ⟨873929, by rfl⟩ : syracuseStep 1165239 = 1747859) B1747859
theorem B1165259 : Blo 1164640 1165259 := bstep (se 1 (by rfl) ⟨873944, by rfl⟩ : syracuseStep 1165259 = 1747889) B1747889
theorem B8406989 : Blo 1164640 8406989 := bstep (se 3 (by rfl) ⟨1576310, by rfl⟩ : syracuseStep 8406989 = 3152621) B3152621
theorem B1165271 : Blo 1164640 1165271 := bstep (se 1 (by rfl) ⟨873953, by rfl⟩ : syracuseStep 1165271 = 1747907) B1747907
theorem B3934169 : Blo 1164640 3934169 := bstep (se 2 (by rfl) ⟨1475313, by rfl⟩ : syracuseStep 3934169 = 2950627) B2950627
theorem B1165291 : Blo 1164640 1165291 := bstep (se 1 (by rfl) ⟨873968, by rfl⟩ : syracuseStep 1165291 = 1747937) B1747937
theorem B1165303 : Blo 1164640 1165303 := bstep (se 1 (by rfl) ⟨873977, by rfl⟩ : syracuseStep 1165303 = 1747955) B1747955
theorem B1165323 : Blo 1164640 1165323 := bstep (se 1 (by rfl) ⟨873992, by rfl⟩ : syracuseStep 1165323 = 1747985) B1747985
theorem B2623499 : Blo 1164640 2623499 := bstep (se 1 (by rfl) ⟨1967624, by rfl⟩ : syracuseStep 2623499 = 3935249) B3935249
theorem B5597201 : Blo 1164640 5597201 := bstep (se 2 (by rfl) ⟨2098950, by rfl⟩ : syracuseStep 5597201 = 4197901) B4197901
theorem B1165335 : Blo 1164640 1165335 := bstep (se 1 (by rfl) ⟨874001, by rfl⟩ : syracuseStep 1165335 = 1748003) B1748003
theorem B1968151 : Blo 1164640 1968151 := bstep (se 1 (by rfl) ⟨1476113, by rfl⟩ : syracuseStep 1968151 = 2952227) B2952227
theorem B1165355 : Blo 1164640 1165355 := bstep (se 1 (by rfl) ⟨874016, by rfl⟩ : syracuseStep 1165355 = 1748033) B1748033
theorem B1165367 : Blo 1164640 1165367 := bstep (se 1 (by rfl) ⟨874025, by rfl⟩ : syracuseStep 1165367 = 1748051) B1748051
theorem B2623553 : Blo 1164640 2623553 := bstep (se 2 (by rfl) ⟨983832, by rfl⟩ : syracuseStep 2623553 = 1967665) B1967665
theorem B1747019 : Blo 1164640 1747019 := bstep (se 1 (by rfl) ⟨1310264, by rfl⟩ : syracuseStep 1747019 = 2620529) B2620529
theorem B1165387 : Blo 1164640 1165387 := bstep (se 1 (by rfl) ⟨874040, by rfl⟩ : syracuseStep 1165387 = 1748081) B1748081
theorem B5900363 : Blo 1164640 5900363 := bstep (se 1 (by rfl) ⟨4425272, by rfl⟩ : syracuseStep 5900363 = 8850545) B8850545
theorem B1747031 : Blo 1164640 1747031 := bstep (se 1 (by rfl) ⟨1310273, by rfl⟩ : syracuseStep 1747031 = 2620547) B2620547
theorem B1165399 : Blo 1164640 1165399 := bstep (se 1 (by rfl) ⟨874049, by rfl⟩ : syracuseStep 1165399 = 1748099) B1748099
theorem B1165419 : Blo 1164640 1165419 := bstep (se 1 (by rfl) ⟨874064, by rfl⟩ : syracuseStep 1165419 = 1748129) B1748129
theorem B1165431 : Blo 1164640 1165431 := bstep (se 1 (by rfl) ⟨874073, by rfl⟩ : syracuseStep 1165431 = 1748147) B1748147
theorem B1165451 : Blo 1164640 1165451 := bstep (se 1 (by rfl) ⟨874088, by rfl⟩ : syracuseStep 1165451 = 1748177) B1748177
theorem B1165463 : Blo 1164640 1165463 := bstep (se 1 (by rfl) ⟨874097, by rfl⟩ : syracuseStep 1165463 = 1748195) B1748195
theorem B1747097 : Blo 1164640 1747097 := bstep (se 2 (by rfl) ⟨655161, by rfl⟩ : syracuseStep 1747097 = 1310323) B1310323
theorem B1165483 : Blo 1164640 1165483 := bstep (se 1 (by rfl) ⟨874112, by rfl⟩ : syracuseStep 1165483 = 1748225) B1748225
theorem B1165495 : Blo 1164640 1165495 := bstep (se 1 (by rfl) ⟨874121, by rfl⟩ : syracuseStep 1165495 = 1748243) B1748243
theorem B1165515 : Blo 1164640 1165515 := bstep (se 1 (by rfl) ⟨874136, by rfl⟩ : syracuseStep 1165515 = 1748273) B1748273
theorem B1165527 : Blo 1164640 1165527 := bstep (se 1 (by rfl) ⟨874145, by rfl⟩ : syracuseStep 1165527 = 1748291) B1748291
theorem B1165547 : Blo 1164640 1165547 := bstep (se 1 (by rfl) ⟨874160, by rfl⟩ : syracuseStep 1165547 = 1748321) B1748321
theorem B1165559 : Blo 1164640 1165559 := bstep (se 1 (by rfl) ⟨874169, by rfl⟩ : syracuseStep 1165559 = 1748339) B1748339
theorem B1747211 : Blo 1164640 1747211 := bstep (se 1 (by rfl) ⟨1310408, by rfl⟩ : syracuseStep 1747211 = 2620817) B2620817
theorem B1165579 : Blo 1164640 1165579 := bstep (se 1 (by rfl) ⟨874184, by rfl⟩ : syracuseStep 1165579 = 1748369) B1748369
theorem B2214155 : Blo 1164640 2214155 := bstep (se 1 (by rfl) ⟨1660616, by rfl⟩ : syracuseStep 2214155 = 3321233) B3321233
theorem B1747223 : Blo 1164640 1747223 := bstep (se 1 (by rfl) ⟨1310417, by rfl⟩ : syracuseStep 1747223 = 2620835) B2620835
theorem B1165591 : Blo 1164640 1165591 := bstep (se 1 (by rfl) ⟨874193, by rfl⟩ : syracuseStep 1165591 = 1748387) B1748387
theorem B2623769 : Blo 1164640 2623769 := bstep (se 2 (by rfl) ⟨983913, by rfl⟩ : syracuseStep 2623769 = 1967827) B1967827
theorem B1165611 : Blo 1164640 1165611 := bstep (se 1 (by rfl) ⟨874208, by rfl⟩ : syracuseStep 1165611 = 1748417) B1748417
theorem B1165623 : Blo 1164640 1165623 := bstep (se 1 (by rfl) ⟨874217, by rfl⟩ : syracuseStep 1165623 = 1748435) B1748435
theorem B3320129 : Blo 1164640 3320129 := bstep (se 2 (by rfl) ⟨1245048, by rfl⟩ : syracuseStep 3320129 = 2490097) B2490097
theorem B2214209 : Blo 1164640 2214209 := bstep (se 2 (by rfl) ⟨830328, by rfl⟩ : syracuseStep 2214209 = 1660657) B1660657
theorem B1165643 : Blo 1164640 1165643 := bstep (se 1 (by rfl) ⟨874232, by rfl⟩ : syracuseStep 1165643 = 1748465) B1748465
theorem B1165655 : Blo 1164640 1165655 := bstep (se 1 (by rfl) ⟨874241, by rfl⟩ : syracuseStep 1165655 = 1748483) B1748483
theorem B1747289 : Blo 1164640 1747289 := bstep (se 2 (by rfl) ⟨655233, by rfl⟩ : syracuseStep 1747289 = 1310467) B1310467
theorem B1165675 : Blo 1164640 1165675 := bstep (se 1 (by rfl) ⟨874256, by rfl⟩ : syracuseStep 1165675 = 1748513) B1748513
theorem B2623859 : Blo 1164640 2623859 := bstep (se 1 (by rfl) ⟨1967894, by rfl⟩ : syracuseStep 2623859 = 3935789) B3935789
theorem B1165687 : Blo 1164640 1165687 := bstep (se 1 (by rfl) ⟨874265, by rfl⟩ : syracuseStep 1165687 = 1748531) B1748531
theorem B1165707 : Blo 1164640 1165707 := bstep (se 1 (by rfl) ⟨874280, by rfl⟩ : syracuseStep 1165707 = 1748561) B1748561
theorem B1165719 : Blo 1164640 1165719 := bstep (se 1 (by rfl) ⟨874289, by rfl⟩ : syracuseStep 1165719 = 1748579) B1748579
theorem B2623895 : Blo 1164640 2623895 := bstep (se 1 (by rfl) ⟨1967921, by rfl⟩ : syracuseStep 2623895 = 3935843) B3935843
theorem B1165739 : Blo 1164640 1165739 := bstep (se 1 (by rfl) ⟨874304, by rfl⟩ : syracuseStep 1165739 = 1748609) B1748609
theorem B1165751 : Blo 1164640 1165751 := bstep (se 1 (by rfl) ⟨874313, by rfl⟩ : syracuseStep 1165751 = 1748627) B1748627
theorem B1747403 : Blo 1164640 1747403 := bstep (se 1 (by rfl) ⟨1310552, by rfl⟩ : syracuseStep 1747403 = 2621105) B2621105
theorem B1165771 : Blo 1164640 1165771 := bstep (se 1 (by rfl) ⟨874328, by rfl⟩ : syracuseStep 1165771 = 1748657) B1748657
theorem B1747415 : Blo 1164640 1747415 := bstep (se 1 (by rfl) ⟨1310561, by rfl⟩ : syracuseStep 1747415 = 2621123) B2621123
theorem B1165783 : Blo 1164640 1165783 := bstep (se 1 (by rfl) ⟨874337, by rfl⟩ : syracuseStep 1165783 = 1748675) B1748675
theorem B1165803 : Blo 1164640 1165803 := bstep (se 1 (by rfl) ⟨874352, by rfl⟩ : syracuseStep 1165803 = 1748705) B1748705
theorem B1165815 : Blo 1164640 1165815 := bstep (se 1 (by rfl) ⟨874361, by rfl⟩ : syracuseStep 1165815 = 1748723) B1748723
theorem B1165835 : Blo 1164640 1165835 := bstep (se 1 (by rfl) ⟨874376, by rfl⟩ : syracuseStep 1165835 = 1748753) B1748753
theorem B1165847 : Blo 1164640 1165847 := bstep (se 1 (by rfl) ⟨874385, by rfl⟩ : syracuseStep 1165847 = 1748771) B1748771
theorem B1747481 : Blo 1164640 1747481 := bstep (se 2 (by rfl) ⟨655305, by rfl⟩ : syracuseStep 1747481 = 1310611) B1310611
theorem B1165867 : Blo 1164640 1165867 := bstep (se 1 (by rfl) ⟨874400, by rfl⟩ : syracuseStep 1165867 = 1748801) B1748801
theorem B1165879 : Blo 1164640 1165879 := bstep (se 1 (by rfl) ⟨874409, by rfl⟩ : syracuseStep 1165879 = 1748819) B1748819
theorem B1165899 : Blo 1164640 1165899 := bstep (se 1 (by rfl) ⟨874424, by rfl⟩ : syracuseStep 1165899 = 1748849) B1748849
theorem B2624075 : Blo 1164640 2624075 := bstep (se 1 (by rfl) ⟨1968056, by rfl⟩ : syracuseStep 2624075 = 3936113) B3936113
theorem B1165911 : Blo 1164640 1165911 := bstep (se 1 (by rfl) ⟨874433, by rfl⟩ : syracuseStep 1165911 = 1748867) B1748867
theorem B1165931 : Blo 1164640 1165931 := bstep (se 1 (by rfl) ⟨874448, by rfl⟩ : syracuseStep 1165931 = 1748897) B1748897
theorem B1165943 : Blo 1164640 1165943 := bstep (se 1 (by rfl) ⟨874457, by rfl⟩ : syracuseStep 1165943 = 1748915) B1748915
theorem B2624129 : Blo 1164640 2624129 := bstep (se 2 (by rfl) ⟨984048, by rfl⟩ : syracuseStep 2624129 = 1968097) B1968097
theorem B1747595 : Blo 1164640 1747595 := bstep (se 1 (by rfl) ⟨1310696, by rfl⟩ : syracuseStep 1747595 = 2621393) B2621393
theorem B1165963 : Blo 1164640 1165963 := bstep (se 1 (by rfl) ⟨874472, by rfl⟩ : syracuseStep 1165963 = 1748945) B1748945
theorem B1747607 : Blo 1164640 1747607 := bstep (se 1 (by rfl) ⟨1310705, by rfl⟩ : syracuseStep 1747607 = 2621411) B2621411
theorem B3934871 : Blo 1164640 3934871 := bstep (se 1 (by rfl) ⟨2951153, by rfl⟩ : syracuseStep 3934871 = 5902307) B5902307
theorem B1165975 : Blo 1164640 1165975 := bstep (se 1 (by rfl) ⟨874481, by rfl⟩ : syracuseStep 1165975 = 1748963) B1748963
theorem B1165995 : Blo 1164640 1165995 := bstep (se 1 (by rfl) ⟨874496, by rfl⟩ : syracuseStep 1165995 = 1748993) B1748993
theorem B6302387 : Blo 1164640 6302387 := bstep (se 1 (by rfl) ⟨4726790, by rfl⟩ : syracuseStep 6302387 = 9453581) B9453581
theorem B1166007 : Blo 1164640 1166007 := bstep (se 1 (by rfl) ⟨874505, by rfl⟩ : syracuseStep 1166007 = 1749011) B1749011
theorem B2951873 : Blo 1164640 2951873 := bstep (se 2 (by rfl) ⟨1106952, by rfl⟩ : syracuseStep 2951873 = 2213905) B2213905
theorem B1166027 : Blo 1164640 1166027 := bstep (se 1 (by rfl) ⟨874520, by rfl⟩ : syracuseStep 1166027 = 1749041) B1749041
theorem B1166039 : Blo 1164640 1166039 := bstep (se 1 (by rfl) ⟨874529, by rfl⟩ : syracuseStep 1166039 = 1749059) B1749059
theorem B1747673 : Blo 1164640 1747673 := bstep (se 2 (by rfl) ⟨655377, by rfl⟩ : syracuseStep 1747673 = 1310755) B1310755
theorem B1166059 : Blo 1164640 1166059 := bstep (se 1 (by rfl) ⟨874544, by rfl⟩ : syracuseStep 1166059 = 1749089) B1749089
theorem B1166071 : Blo 1164640 1166071 := bstep (se 1 (by rfl) ⟨874553, by rfl⟩ : syracuseStep 1166071 = 1749107) B1749107
theorem B1166091 : Blo 1164640 1166091 := bstep (se 1 (by rfl) ⟨874568, by rfl⟩ : syracuseStep 1166091 = 1749137) B1749137
theorem B1166103 : Blo 1164640 1166103 := bstep (se 1 (by rfl) ⟨874577, by rfl⟩ : syracuseStep 1166103 = 1749155) B1749155
theorem B1166123 : Blo 1164640 1166123 := bstep (se 1 (by rfl) ⟨874592, by rfl⟩ : syracuseStep 1166123 = 1749185) B1749185
theorem B1166135 : Blo 1164640 1166135 := bstep (se 1 (by rfl) ⟨874601, by rfl⟩ : syracuseStep 1166135 = 1749203) B1749203
theorem B1747787 : Blo 1164640 1747787 := bstep (se 1 (by rfl) ⟨1310840, by rfl⟩ : syracuseStep 1747787 = 2621681) B2621681
theorem B1166155 : Blo 1164640 1166155 := bstep (se 1 (by rfl) ⟨874616, by rfl⟩ : syracuseStep 1166155 = 1749233) B1749233
theorem B1747799 : Blo 1164640 1747799 := bstep (se 1 (by rfl) ⟨1310849, by rfl⟩ : syracuseStep 1747799 = 2621699) B2621699
theorem B1166167 : Blo 1164640 1166167 := bstep (se 1 (by rfl) ⟨874625, by rfl⟩ : syracuseStep 1166167 = 1749251) B1749251
theorem B1796953 : Blo 1164640 1796953 := bstep (se 2 (by rfl) ⟨673857, by rfl⟩ : syracuseStep 1796953 = 1347715) B1347715
theorem B2624345 : Blo 1164640 2624345 := bstep (se 2 (by rfl) ⟨984129, by rfl⟩ : syracuseStep 2624345 = 1968259) B1968259
theorem B1166187 : Blo 1164640 1166187 := bstep (se 1 (by rfl) ⟨874640, by rfl⟩ : syracuseStep 1166187 = 1749281) B1749281
theorem B1166199 : Blo 1164640 1166199 := bstep (se 1 (by rfl) ⟨874649, by rfl⟩ : syracuseStep 1166199 = 1749299) B1749299
theorem B2100097 : Blo 1164640 2100097 := bstep (se 2 (by rfl) ⟨787536, by rfl⟩ : syracuseStep 2100097 = 1575073) B1575073
theorem B1166219 : Blo 1164640 1166219 := bstep (se 1 (by rfl) ⟨874664, by rfl⟩ : syracuseStep 1166219 = 1749329) B1749329
theorem B1166231 : Blo 1164640 1166231 := bstep (se 1 (by rfl) ⟨874673, by rfl⟩ : syracuseStep 1166231 = 1749347) B1749347
theorem B1747865 : Blo 1164640 1747865 := bstep (se 2 (by rfl) ⟨655449, by rfl⟩ : syracuseStep 1747865 = 1310899) B1310899
theorem B1166251 : Blo 1164640 1166251 := bstep (se 1 (by rfl) ⟨874688, by rfl⟩ : syracuseStep 1166251 = 1749377) B1749377
theorem B1166263 : Blo 1164640 1166263 := bstep (se 1 (by rfl) ⟨874697, by rfl⟩ : syracuseStep 1166263 = 1749395) B1749395
theorem B2100161 : Blo 1164640 2100161 := bstep (se 2 (by rfl) ⟨787560, by rfl⟩ : syracuseStep 2100161 = 1575121) B1575121
theorem B1166283 : Blo 1164640 1166283 := bstep (se 1 (by rfl) ⟨874712, by rfl⟩ : syracuseStep 1166283 = 1749425) B1749425
theorem B1166295 : Blo 1164640 1166295 := bstep (se 1 (by rfl) ⟨874721, by rfl⟩ : syracuseStep 1166295 = 1749443) B1749443
theorem B1166315 : Blo 1164640 1166315 := bstep (se 1 (by rfl) ⟨874736, by rfl⟩ : syracuseStep 1166315 = 1749473) B1749473
theorem B1166327 : Blo 1164640 1166327 := bstep (se 1 (by rfl) ⟨874745, by rfl⟩ : syracuseStep 1166327 = 1749491) B1749491
theorem B1747979 : Blo 1164640 1747979 := bstep (se 1 (by rfl) ⟨1310984, by rfl⟩ : syracuseStep 1747979 = 2621969) B2621969
theorem B1166347 : Blo 1164640 1166347 := bstep (se 1 (by rfl) ⟨874760, by rfl⟩ : syracuseStep 1166347 = 1749521) B1749521
theorem B1747991 : Blo 1164640 1747991 := bstep (se 1 (by rfl) ⟨1310993, by rfl⟩ : syracuseStep 1747991 = 2621987) B2621987
theorem B1166359 : Blo 1164640 1166359 := bstep (se 1 (by rfl) ⟨874769, by rfl⟩ : syracuseStep 1166359 = 1749539) B1749539
theorem B1166379 : Blo 1164640 1166379 := bstep (se 1 (by rfl) ⟨874784, by rfl⟩ : syracuseStep 1166379 = 1749569) B1749569
theorem B1166391 : Blo 1164640 1166391 := bstep (se 1 (by rfl) ⟨874793, by rfl⟩ : syracuseStep 1166391 = 1749587) B1749587
theorem B13282379 : Blo 1164640 13282379 := bstep (se 1 (by rfl) ⟨9961784, by rfl⟩ : syracuseStep 13282379 = 19923569) B19923569
theorem B1748057 : Blo 1164640 1748057 := bstep (se 2 (by rfl) ⟨655521, by rfl⟩ : syracuseStep 1748057 = 1311043) B1311043
theorem B4426883 : Blo 1164640 4426883 := bstep (se 1 (by rfl) ⟨3320162, by rfl⟩ : syracuseStep 4426883 = 6640325) B6640325
theorem B3935411 : Blo 1164640 3935411 := bstep (se 1 (by rfl) ⟨2951558, by rfl⟩ : syracuseStep 3935411 = 5903117) B5903117
theorem B1748171 : Blo 1164640 1748171 := bstep (se 1 (by rfl) ⟨1311128, by rfl⟩ : syracuseStep 1748171 = 2622257) B2622257
theorem B1748183 : Blo 1164640 1748183 := bstep (se 1 (by rfl) ⟨1311137, by rfl⟩ : syracuseStep 1748183 = 2622275) B2622275
theorem B2952409 : Blo 1164640 2952409 := bstep (se 2 (by rfl) ⟨1107153, by rfl⟩ : syracuseStep 2952409 = 2214307) B2214307
theorem B1748249 : Blo 1164640 1748249 := bstep (se 2 (by rfl) ⟨655593, by rfl⟩ : syracuseStep 1748249 = 1311187) B1311187
theorem B1748363 : Blo 1164640 1748363 := bstep (se 1 (by rfl) ⟨1311272, by rfl⟩ : syracuseStep 1748363 = 2622545) B2622545
theorem B1748375 : Blo 1164640 1748375 := bstep (se 1 (by rfl) ⟨1311281, by rfl⟩ : syracuseStep 1748375 = 2622563) B2622563
theorem B3542465 : Blo 1164640 3542465 := bstep (se 2 (by rfl) ⟨1328424, by rfl⟩ : syracuseStep 3542465 = 2656849) B2656849
theorem B3935681 : Blo 1164640 3935681 := bstep (se 2 (by rfl) ⟨1475880, by rfl⟩ : syracuseStep 3935681 = 2951761) B2951761
theorem B1748441 : Blo 1164640 1748441 := bstep (se 2 (by rfl) ⟨655665, by rfl⟩ : syracuseStep 1748441 = 1311331) B1311331
theorem B4976093 : Blo 1164640 4976093 := bstep (se 3 (by rfl) ⟨933017, by rfl⟩ : syracuseStep 4976093 = 1866035) B1866035
theorem B16797253 : Blo 1164640 16797253 := bstep (se 4 (by rfl) ⟨1574742, by rfl⟩ : syracuseStep 16797253 = 3149485) B3149485
theorem B1748555 : Blo 1164640 1748555 := bstep (se 1 (by rfl) ⟨1311416, by rfl⟩ : syracuseStep 1748555 = 2622833) B2622833
theorem B2100811 : Blo 1164640 2100811 := bstep (se 1 (by rfl) ⟨1575608, by rfl⟩ : syracuseStep 2100811 = 3151217) B3151217
theorem B1748567 : Blo 1164640 1748567 := bstep (se 1 (by rfl) ⟨1311425, by rfl⟩ : syracuseStep 1748567 = 2622851) B2622851
theorem B3149401 : Blo 1164640 3149401 := bstep (se 2 (by rfl) ⟨1181025, by rfl⟩ : syracuseStep 3149401 = 2362051) B2362051
theorem B1748633 : Blo 1164640 1748633 := bstep (se 2 (by rfl) ⟨655737, by rfl⟩ : syracuseStep 1748633 = 1311475) B1311475
theorem B1748747 : Blo 1164640 1748747 := bstep (se 1 (by rfl) ⟨1311560, by rfl⟩ : syracuseStep 1748747 = 2623121) B2623121
theorem B1748759 : Blo 1164640 1748759 := bstep (se 1 (by rfl) ⟨1311569, by rfl⟩ : syracuseStep 1748759 = 2623139) B2623139
theorem B5902145 : Blo 1164640 5902145 := bstep (se 2 (by rfl) ⟨2213304, by rfl⟩ : syracuseStep 5902145 = 4426609) B4426609
theorem B1748825 : Blo 1164640 1748825 := bstep (se 2 (by rfl) ⟨655809, by rfl⟩ : syracuseStep 1748825 = 1311619) B1311619
theorem B1748939 : Blo 1164640 1748939 := bstep (se 1 (by rfl) ⟨1311704, by rfl⟩ : syracuseStep 1748939 = 2623409) B2623409
theorem B1748951 : Blo 1164640 1748951 := bstep (se 1 (by rfl) ⟨1311713, by rfl⟩ : syracuseStep 1748951 = 2623427) B2623427
theorem B3731417 : Blo 1164640 3731417 := bstep (se 2 (by rfl) ⟨1399281, by rfl⟩ : syracuseStep 3731417 = 2798563) B2798563
theorem B3936221 : Blo 1164640 3936221 := bstep (se 3 (by rfl) ⟨738041, by rfl⟩ : syracuseStep 3936221 = 1476083) B1476083
theorem B1749017 : Blo 1164640 1749017 := bstep (se 2 (by rfl) ⟨655881, by rfl⟩ : syracuseStep 1749017 = 1311763) B1311763
theorem B1749131 : Blo 1164640 1749131 := bstep (se 1 (by rfl) ⟨1311848, by rfl⟩ : syracuseStep 1749131 = 2623697) B2623697
theorem B1749143 : Blo 1164640 1749143 := bstep (se 1 (by rfl) ⟨1311857, by rfl⟩ : syracuseStep 1749143 = 2623715) B2623715
theorem B1749209 : Blo 1164640 1749209 := bstep (se 2 (by rfl) ⟨655953, by rfl⟩ : syracuseStep 1749209 = 1311907) B1311907
theorem B1749323 : Blo 1164640 1749323 := bstep (se 1 (by rfl) ⟨1311992, by rfl⟩ : syracuseStep 1749323 = 2623985) B2623985
theorem B1749335 : Blo 1164640 1749335 := bstep (se 1 (by rfl) ⟨1312001, by rfl⟩ : syracuseStep 1749335 = 2624003) B2624003
theorem B2101619 : Blo 1164640 2101619 := bstep (se 1 (by rfl) ⟨1576214, by rfl⟩ : syracuseStep 2101619 = 3152429) B3152429
theorem B1749401 : Blo 1164640 1749401 := bstep (se 2 (by rfl) ⟨656025, by rfl⟩ : syracuseStep 1749401 = 1312051) B1312051
theorem B1749515 : Blo 1164640 1749515 := bstep (se 1 (by rfl) ⟨1312136, by rfl⟩ : syracuseStep 1749515 = 2624273) B2624273
theorem B1749527 : Blo 1164640 1749527 := bstep (se 1 (by rfl) ⟨1312145, by rfl⟩ : syracuseStep 1749527 = 2624291) B2624291
theorem B8852003 : Blo 1164640 8852003 := bstep (se 1 (by rfl) ⟨6639002, by rfl⟩ : syracuseStep 8852003 = 13278005) B13278005
theorem B9458221 : Blo 1164640 9458221 := bstep (se 3 (by rfl) ⟨1773416, by rfl⟩ : syracuseStep 9458221 = 3546833) B3546833
theorem B1749593 : Blo 1164640 1749593 := bstep (se 2 (by rfl) ⟨656097, by rfl⟩ : syracuseStep 1749593 = 1312195) B1312195
theorem B3732313 : Blo 1164640 3732313 := bstep (se 2 (by rfl) ⟨1399617, by rfl⟩ : syracuseStep 3732313 = 2799235) B2799235
theorem B1659865 : Blo 1164640 1659865 := bstep (se 2 (by rfl) ⟨622449, by rfl⟩ : syracuseStep 1659865 = 1244899) B1244899
theorem B16176145 : Blo 1164640 16176145 := bstep (se 2 (by rfl) ⟨6066054, by rfl⟩ : syracuseStep 16176145 = 12132109) B12132109
theorem B4723805 : Blo 1164640 4723805 := bstep (se 3 (by rfl) ⟨885713, by rfl⟩ : syracuseStep 4723805 = 1771427) B1771427
theorem B7091549 : Blo 1164640 7091549 := bstep (se 3 (by rfl) ⟨1329665, by rfl⟩ : syracuseStep 7091549 = 2659331) B2659331
theorem B3732929 : Blo 1164640 3732929 := bstep (se 2 (by rfl) ⟨1399848, by rfl⟩ : syracuseStep 3732929 = 2799697) B2799697
theorem B6633035 : Blo 1164640 6633035 := bstep (se 1 (by rfl) ⟨4974776, by rfl⟩ : syracuseStep 6633035 = 9949553) B9949553
theorem B25204355 : Blo 1164640 25204355 := bstep (se 1 (by rfl) ⟨18903266, by rfl⟩ : syracuseStep 25204355 = 37806533) B37806533
theorem B5904089 : Blo 1164640 5904089 := bstep (se 2 (by rfl) ⟨2214033, by rfl⟩ : syracuseStep 5904089 = 4428067) B4428067
theorem B4978691 : Blo 1164640 4978691 := bstep (se 1 (by rfl) ⟨3734018, by rfl⟩ : syracuseStep 4978691 = 7468037) B7468037
theorem B2488499 : Blo 1164640 2488499 := bstep (se 1 (by rfl) ⟨1866374, by rfl⟩ : syracuseStep 2488499 = 3732749) B3732749
theorem B2488601 : Blo 1164640 2488601 := bstep (se 2 (by rfl) ⟨933225, by rfl⟩ : syracuseStep 2488601 = 1866451) B1866451
theorem B8395109 : Blo 1164640 8395109 := bstep (se 4 (by rfl) ⟨787041, by rfl⟩ : syracuseStep 8395109 = 1574083) B1574083
theorem B5757335 : Blo 1164640 5757335 := bstep (se 1 (by rfl) ⟨4318001, by rfl⟩ : syracuseStep 5757335 = 8636003) B8636003
theorem B3193309 : Blo 1164640 3193309 := bstep (se 3 (by rfl) ⟨598745, by rfl⟩ : syracuseStep 3193309 = 1197491) B1197491
theorem B4725299 : Blo 1164640 4725299 := bstep (se 1 (by rfl) ⟨3543974, by rfl⟩ : syracuseStep 4725299 = 7087949) B7087949
theorem B8395339 : Blo 1164640 8395339 := bstep (se 1 (by rfl) ⟨6296504, by rfl⟩ : syracuseStep 8395339 = 12593009) B12593009
theorem B3930713 : Blo 1164640 3930713 := bstep (se 2 (by rfl) ⟨1474017, by rfl⟩ : syracuseStep 3930713 = 2948035) B2948035
theorem B2488961 : Blo 1164640 2488961 := bstep (se 2 (by rfl) ⟨933360, by rfl⟩ : syracuseStep 2488961 = 1866721) B1866721
theorem B1243831 : Blo 1164640 1243831 := bstep (se 1 (by rfl) ⟨932873, by rfl⟩ : syracuseStep 1243831 = 1865747) B1865747
theorem B50420465 : Blo 1164640 50420465 := bstep (se 2 (by rfl) ⟨18907674, by rfl⟩ : syracuseStep 50420465 = 37815349) B37815349
theorem B3152663 : Blo 1164640 3152663 := bstep (se 1 (by rfl) ⟨2364497, by rfl⟩ : syracuseStep 3152663 = 4728995) B4728995
theorem B67197761 : Blo 1164640 67197761 := bstep (se 2 (by rfl) ⟨25199160, by rfl⟩ : syracuseStep 67197761 = 50398321) B50398321
theorem B1399627 : Blo 1164640 1399627 := bstep (se 1 (by rfl) ⟨1049720, by rfl⟩ : syracuseStep 1399627 = 2099441) B2099441
theorem B23919461 : Blo 1164640 23919461 := bstep (se 4 (by rfl) ⟨2242449, by rfl⟩ : syracuseStep 23919461 = 4484899) B4484899
theorem B4201361 : Blo 1164640 4201361 := bstep (se 2 (by rfl) ⟨1575510, by rfl⟩ : syracuseStep 4201361 = 3151021) B3151021
theorem B3783617 : Blo 1164640 3783617 := bstep (se 2 (by rfl) ⟨1418856, by rfl⟩ : syracuseStep 3783617 = 2837713) B2837713
theorem B9714637 : Blo 1164640 9714637 := bstep (se 3 (by rfl) ⟨1821494, by rfl⟩ : syracuseStep 9714637 = 3642989) B3642989
theorem B9952217 : Blo 1164640 9952217 := bstep (se 2 (by rfl) ⟨3732081, by rfl⟩ : syracuseStep 9952217 = 7464163) B7464163
theorem B4201475 : Blo 1164640 4201475 := bstep (se 1 (by rfl) ⟨3151106, by rfl⟩ : syracuseStep 4201475 = 6302213) B6302213
theorem B30293027 : Blo 1164640 30293027 := bstep (se 1 (by rfl) ⟨22719770, by rfl⟩ : syracuseStep 30293027 = 45439541) B45439541
theorem B2948147 : Blo 1164640 2948147 := bstep (se 1 (by rfl) ⟨2211110, by rfl⟩ : syracuseStep 2948147 = 4422221) B4422221
theorem B4422707 : Blo 1164640 4422707 := bstep (se 1 (by rfl) ⟨3317030, by rfl⟩ : syracuseStep 4422707 = 6634061) B6634061
theorem B4422721 : Blo 1164640 4422721 := bstep (se 2 (by rfl) ⟨1658520, by rfl⟩ : syracuseStep 4422721 = 3317041) B3317041
theorem B9452609 : Blo 1164640 9452609 := bstep (se 2 (by rfl) ⟨3544728, by rfl⟩ : syracuseStep 9452609 = 7089457) B7089457
theorem B16792757 : Blo 1164640 16792757 := bstep (se 5 (by rfl) ⟨787160, by rfl⟩ : syracuseStep 16792757 = 1574321) B1574321
theorem B2620619 : Blo 1164640 2620619 := bstep (se 1 (by rfl) ⟨1965464, by rfl⟩ : syracuseStep 2620619 = 3930929) B3930929
theorem B2620673 : Blo 1164640 2620673 := bstep (se 2 (by rfl) ⟨982752, by rfl⟩ : syracuseStep 2620673 = 1965505) B1965505
theorem B3931415 : Blo 1164640 3931415 := bstep (se 1 (by rfl) ⟨2948561, by rfl⟩ : syracuseStep 3931415 = 5897123) B5897123
theorem B9706787 : Blo 1164640 9706787 := bstep (se 1 (by rfl) ⟨7280090, by rfl⟩ : syracuseStep 9706787 = 14560181) B14560181
theorem B8846657 : Blo 1164640 8846657 := bstep (se 2 (by rfl) ⟨3317496, by rfl⟩ : syracuseStep 8846657 = 6634993) B6634993
theorem B2489687 : Blo 1164640 2489687 := bstep (se 1 (by rfl) ⟨1867265, by rfl⟩ : syracuseStep 2489687 = 3734531) B3734531
theorem B1965451 : Blo 1164640 1965451 := bstep (se 1 (by rfl) ⟨1474088, by rfl⟩ : syracuseStep 1965451 = 2948177) B2948177
theorem B2801099 : Blo 1164640 2801099 := bstep (se 1 (by rfl) ⟨2100824, by rfl⟩ : syracuseStep 2801099 = 4201649) B4201649
theorem B2620889 : Blo 1164640 2620889 := bstep (se 2 (by rfl) ⟨982833, by rfl⟩ : syracuseStep 2620889 = 1965667) B1965667
theorem B3317213 : Blo 1164640 3317213 := bstep (se 3 (by rfl) ⟨621977, by rfl⟩ : syracuseStep 3317213 = 1243955) B1243955
theorem B1244651 : Blo 1164640 1244651 := bstep (se 1 (by rfl) ⟨933488, by rfl⟩ : syracuseStep 1244651 = 1866977) B1866977
theorem B9960965 : Blo 1164640 9960965 := bstep (se 4 (by rfl) ⟨933840, by rfl⟩ : syracuseStep 9960965 = 1867681) B1867681
theorem B1965593 : Blo 1164640 1965593 := bstep (se 2 (by rfl) ⟨737097, by rfl⟩ : syracuseStep 1965593 = 1474195) B1474195
theorem B1310251 : Blo 1164640 1310251 := bstep (se 1 (by rfl) ⟨982688, by rfl⟩ : syracuseStep 1310251 = 1965377) B1965377
theorem B2620979 : Blo 1164640 2620979 := bstep (se 1 (by rfl) ⟨1965734, by rfl⟩ : syracuseStep 2620979 = 3931469) B3931469
theorem B2948683 : Blo 1164640 2948683 := bstep (se 1 (by rfl) ⟨2211512, by rfl⟩ : syracuseStep 2948683 = 4423025) B4423025
theorem B2621015 : Blo 1164640 2621015 := bstep (se 1 (by rfl) ⟨1965761, by rfl⟩ : syracuseStep 2621015 = 3931523) B3931523
theorem B2694745 : Blo 1164640 2694745 := bstep (se 2 (by rfl) ⟨1010529, by rfl⟩ : syracuseStep 2694745 = 2021059) B2021059
theorem B9445015 : Blo 1164640 9445015 := bstep (se 1 (by rfl) ⟨7083761, by rfl⟩ : syracuseStep 9445015 = 14167523) B14167523
theorem B1310359 : Blo 1164640 1310359 := bstep (se 1 (by rfl) ⟨982769, by rfl⟩ : syracuseStep 1310359 = 1965539) B1965539
theorem B1965721 : Blo 1164640 1965721 := bstep (se 2 (by rfl) ⟨737145, by rfl⟩ : syracuseStep 1965721 = 1474291) B1474291
theorem B409001669 : Blo 1164640 409001669 := bstep (se 4 (by rfl) ⟨38343906, by rfl⟩ : syracuseStep 409001669 = 76687813) B76687813
theorem B2948825 : Blo 1164640 2948825 := bstep (se 2 (by rfl) ⟨1105809, by rfl⟩ : syracuseStep 2948825 = 2211619) B2211619
theorem B3546845 : Blo 1164640 3546845 := bstep (se 3 (by rfl) ⟨665033, by rfl⟩ : syracuseStep 3546845 = 1330067) B1330067
theorem B2621195 : Blo 1164640 2621195 := bstep (se 1 (by rfl) ⟨1965896, by rfl⟩ : syracuseStep 2621195 = 3931793) B3931793
theorem B3931955 : Blo 1164640 3931955 := bstep (se 1 (by rfl) ⟨2948966, by rfl⟩ : syracuseStep 3931955 = 5897933) B5897933
theorem B2621249 : Blo 1164640 2621249 := bstep (se 2 (by rfl) ⟨982968, by rfl⟩ : syracuseStep 2621249 = 1965937) B1965937
theorem B1310539 : Blo 1164640 1310539 := bstep (se 1 (by rfl) ⟨982904, by rfl⟩ : syracuseStep 1310539 = 1965809) B1965809
theorem B3735389 : Blo 1164640 3735389 := bstep (se 3 (by rfl) ⟨700385, by rfl⟩ : syracuseStep 3735389 = 1400771) B1400771
theorem B43106147 : Blo 1164640 43106147 := bstep (se 1 (by rfl) ⟨32329610, by rfl⟩ : syracuseStep 43106147 = 64659221) B64659221
theorem B1310647 : Blo 1164640 1310647 := bstep (se 1 (by rfl) ⟨982985, by rfl⟩ : syracuseStep 1310647 = 1965971) B1965971
theorem B1261495 : Blo 1164640 1261495 := bstep (se 1 (by rfl) ⟨946121, by rfl⟩ : syracuseStep 1261495 = 1892243) B1892243
theorem B1474519 : Blo 1164640 1474519 := bstep (se 1 (by rfl) ⟨1105889, by rfl⟩ : syracuseStep 1474519 = 2211779) B2211779
theorem B3989465 : Blo 1164640 3989465 := bstep (se 2 (by rfl) ⟨1496049, by rfl⟩ : syracuseStep 3989465 = 2992099) B2992099
theorem B3735517 : Blo 1164640 3735517 := bstep (se 3 (by rfl) ⟨700409, by rfl⟩ : syracuseStep 3735517 = 1400819) B1400819
theorem B3932171 : Blo 1164640 3932171 := bstep (se 1 (by rfl) ⟨2949128, by rfl⟩ : syracuseStep 3932171 = 5898257) B5898257
theorem B2621483 : Blo 1164640 2621483 := bstep (se 1 (by rfl) ⟨1966112, by rfl⟩ : syracuseStep 2621483 = 3932225) B3932225
theorem B3932279 : Blo 1164640 3932279 := bstep (se 1 (by rfl) ⟨2949209, by rfl⟩ : syracuseStep 3932279 = 5898419) B5898419
theorem B3031175 : Blo 1164640 3031175 := bstep (se 1 (by rfl) ⟨2273381, by rfl⟩ : syracuseStep 3031175 = 4546763) B4546763
theorem B1310863 : Blo 1164640 1310863 := bstep (se 1 (by rfl) ⟨983147, by rfl⟩ : syracuseStep 1310863 = 1966295) B1966295
theorem B2490515 : Blo 1164640 2490515 := bstep (se 1 (by rfl) ⟨1867886, by rfl⟩ : syracuseStep 2490515 = 3735773) B3735773
theorem B33628405 : Blo 1164640 33628405 := bstep (se 5 (by rfl) ⟨1576331, by rfl⟩ : syracuseStep 33628405 = 3152663) B3152663
theorem B1401079 : Blo 1164640 1401079 := bstep (se 1 (by rfl) ⟨1050809, by rfl⟩ : syracuseStep 1401079 = 2101619) B2101619
theorem B2621843 : Blo 1164640 2621843 := bstep (se 1 (by rfl) ⟨1966382, by rfl⟩ : syracuseStep 2621843 = 3932765) B3932765
theorem B2621897 : Blo 1164640 2621897 := bstep (se 2 (by rfl) ⟨983211, by rfl⟩ : syracuseStep 2621897 = 1966423) B1966423
theorem B49136149 : Blo 1164640 49136149 := bstep (se 6 (by rfl) ⟨1151628, by rfl⟩ : syracuseStep 49136149 = 2303257) B2303257
theorem B9962027 : Blo 1164640 9962027 := bstep (se 1 (by rfl) ⟨7471520, by rfl⟩ : syracuseStep 9962027 = 14943041) B14943041
theorem B2949767 : Blo 1164640 2949767 := bstep (se 1 (by rfl) ⟨2212325, by rfl⟩ : syracuseStep 2949767 = 4424651) B4424651
theorem B1966727 : Blo 1164640 1966727 := bstep (se 1 (by rfl) ⟨1475045, by rfl⟩ : syracuseStep 1966727 = 2950091) B2950091
theorem B1311367 : Blo 1164640 1311367 := bstep (se 1 (by rfl) ⟨983525, by rfl⟩ : syracuseStep 1311367 = 1967051) B1967051
theorem B2949817 : Blo 1164640 2949817 := bstep (se 2 (by rfl) ⟨1106181, by rfl⟩ : syracuseStep 2949817 = 2212363) B2212363
theorem B3932873 : Blo 1164640 3932873 := bstep (se 2 (by rfl) ⟨1474827, by rfl⟩ : syracuseStep 3932873 = 2949655) B2949655
theorem B6636269 : Blo 1164640 6636269 := bstep (se 3 (by rfl) ⟨1244300, by rfl⟩ : syracuseStep 6636269 = 2488601) B2488601
theorem B218170097 : Blo 1164640 218170097 := bstep (se 2 (by rfl) ⟨81813786, by rfl⟩ : syracuseStep 218170097 = 163627573) B163627573
theorem B50373413 : Blo 1164640 50373413 := bstep (se 4 (by rfl) ⟨4722507, by rfl⟩ : syracuseStep 50373413 = 9445015) B9445015
theorem B5899067 : Blo 1164640 5899067 := bstep (se 1 (by rfl) ⟨4424300, by rfl⟩ : syracuseStep 5899067 = 8848601) B8848601
theorem B2212667 : Blo 1164640 2212667 := bstep (se 1 (by rfl) ⟨1659500, by rfl⟩ : syracuseStep 2212667 = 3319001) B3319001
theorem B1311547 : Blo 1164640 1311547 := bstep (se 1 (by rfl) ⟨983660, by rfl⟩ : syracuseStep 1311547 = 1967321) B1967321
theorem B4727699 : Blo 1164640 4727699 := bstep (se 1 (by rfl) ⟨3545774, by rfl⟩ : syracuseStep 4727699 = 7091549) B7091549
theorem B5899229 : Blo 1164640 5899229 := bstep (se 3 (by rfl) ⟨1106105, by rfl⟩ : syracuseStep 5899229 = 2212211) B2212211
theorem B16802903 : Blo 1164640 16802903 := bstep (se 1 (by rfl) ⟨12602177, by rfl⟩ : syracuseStep 16802903 = 25204355) B25204355
theorem B2622599 : Blo 1164640 2622599 := bstep (se 1 (by rfl) ⟨1966949, by rfl⟩ : syracuseStep 2622599 = 3933899) B3933899
theorem B2950415 : Blo 1164640 2950415 := bstep (se 1 (by rfl) ⟨2212811, by rfl⟩ : syracuseStep 2950415 = 4425623) B4425623
theorem B1967375 : Blo 1164640 1967375 := bstep (se 1 (by rfl) ⟨1475531, by rfl⟩ : syracuseStep 1967375 = 2951063) B2951063
theorem B1312015 : Blo 1164640 1312015 := bstep (se 1 (by rfl) ⟨984011, by rfl⟩ : syracuseStep 1312015 = 1968023) B1968023
theorem B3319069 : Blo 1164640 3319069 := bstep (se 3 (by rfl) ⟨622325, by rfl⟩ : syracuseStep 3319069 = 1244651) B1244651
theorem B5899553 : Blo 1164640 5899553 := bstep (se 2 (by rfl) ⟨2212332, by rfl⟩ : syracuseStep 5899553 = 4424665) B4424665
theorem B2213153 : Blo 1164640 2213153 := bstep (se 2 (by rfl) ⟨829932, by rfl⟩ : syracuseStep 2213153 = 1659865) B1659865
theorem B5604659 : Blo 1164640 5604659 := bstep (se 1 (by rfl) ⟨4203494, by rfl⟩ : syracuseStep 5604659 = 8406989) B8406989
theorem B2622779 : Blo 1164640 2622779 := bstep (se 1 (by rfl) ⟨1967084, by rfl⟩ : syracuseStep 2622779 = 3934169) B3934169
theorem B3319127 : Blo 1164640 3319127 := bstep (se 1 (by rfl) ⟨2489345, by rfl⟩ : syracuseStep 3319127 = 4978691) B4978691
theorem B1164679 : Blo 1164640 1164679 := bstep (se 1 (by rfl) ⟨873509, by rfl⟩ : syracuseStep 1164679 = 1747019) B1747019
theorem B3933575 : Blo 1164640 3933575 := bstep (se 1 (by rfl) ⟨2950181, by rfl⟩ : syracuseStep 3933575 = 5900363) B5900363
theorem B1164687 : Blo 1164640 1164687 := bstep (se 1 (by rfl) ⟨873515, by rfl⟩ : syracuseStep 1164687 = 1747031) B1747031
theorem B2622905 : Blo 1164640 2622905 := bstep (se 2 (by rfl) ⟨983589, by rfl⟩ : syracuseStep 2622905 = 1967179) B1967179
theorem B7472569 : Blo 1164640 7472569 := bstep (se 2 (by rfl) ⟨2802213, by rfl⟩ : syracuseStep 7472569 = 5604427) B5604427
theorem B1164731 : Blo 1164640 1164731 := bstep (se 1 (by rfl) ⟨873548, by rfl⟩ : syracuseStep 1164731 = 1747097) B1747097
theorem B1164807 : Blo 1164640 1164807 := bstep (se 1 (by rfl) ⟨873605, by rfl⟩ : syracuseStep 1164807 = 1747211) B1747211
theorem B1164815 : Blo 1164640 1164815 := bstep (se 1 (by rfl) ⟨873611, by rfl⟩ : syracuseStep 1164815 = 1747223) B1747223
theorem B2213419 : Blo 1164640 2213419 := bstep (se 1 (by rfl) ⟨1660064, by rfl⟩ : syracuseStep 2213419 = 3320129) B3320129
theorem B1476139 : Blo 1164640 1476139 := bstep (se 1 (by rfl) ⟨1107104, by rfl⟩ : syracuseStep 1476139 = 2214209) B2214209
theorem B1164859 : Blo 1164640 1164859 := bstep (se 1 (by rfl) ⟨873644, by rfl⟩ : syracuseStep 1164859 = 1747289) B1747289
theorem B5596739 : Blo 1164640 5596739 := bstep (se 1 (by rfl) ⟨4197554, by rfl⟩ : syracuseStep 5596739 = 8395109) B8395109
theorem B27264613 : Blo 1164640 27264613 := bstep (se 4 (by rfl) ⟨2556057, by rfl⟩ : syracuseStep 27264613 = 5112115) B5112115
theorem B1164935 : Blo 1164640 1164935 := bstep (se 1 (by rfl) ⟨873701, by rfl⟩ : syracuseStep 1164935 = 1747403) B1747403
theorem B1164943 : Blo 1164640 1164943 := bstep (se 1 (by rfl) ⟨873707, by rfl⟩ : syracuseStep 1164943 = 1747415) B1747415
theorem B1164987 : Blo 1164640 1164987 := bstep (se 1 (by rfl) ⟨873740, by rfl⟩ : syracuseStep 1164987 = 1747481) B1747481
theorem B3933953 : Blo 1164640 3933953 := bstep (se 2 (by rfl) ⟨1475232, by rfl⟩ : syracuseStep 3933953 = 2950465) B2950465
theorem B1165063 : Blo 1164640 1165063 := bstep (se 1 (by rfl) ⟨873797, by rfl⟩ : syracuseStep 1165063 = 1747595) B1747595
theorem B1165071 : Blo 1164640 1165071 := bstep (se 1 (by rfl) ⟨873803, by rfl⟩ : syracuseStep 1165071 = 1747607) B1747607
theorem B2623247 : Blo 1164640 2623247 := bstep (se 1 (by rfl) ⟨1967435, by rfl⟩ : syracuseStep 2623247 = 3934871) B3934871
theorem B2623265 : Blo 1164640 2623265 := bstep (se 2 (by rfl) ⟨983724, by rfl⟩ : syracuseStep 2623265 = 1967449) B1967449
theorem B1967915 : Blo 1164640 1967915 := bstep (se 1 (by rfl) ⟨1475936, by rfl⟩ : syracuseStep 1967915 = 2951873) B2951873
theorem B1165115 : Blo 1164640 1165115 := bstep (se 1 (by rfl) ⟨873836, by rfl⟩ : syracuseStep 1165115 = 1747673) B1747673
theorem B33613643 : Blo 1164640 33613643 := bstep (se 1 (by rfl) ⟨25210232, by rfl⟩ : syracuseStep 33613643 = 50420465) B50420465
theorem B1165191 : Blo 1164640 1165191 := bstep (se 1 (by rfl) ⟨873893, by rfl⟩ : syracuseStep 1165191 = 1747787) B1747787
theorem B1165199 : Blo 1164640 1165199 := bstep (se 1 (by rfl) ⟨873899, by rfl⟩ : syracuseStep 1165199 = 1747799) B1747799
theorem B1165243 : Blo 1164640 1165243 := bstep (se 1 (by rfl) ⟨873932, by rfl⟩ : syracuseStep 1165243 = 1747865) B1747865
theorem B2951113 : Blo 1164640 2951113 := bstep (se 2 (by rfl) ⟨1106667, by rfl⟩ : syracuseStep 2951113 = 2213335) B2213335
theorem B11200517 : Blo 1164640 11200517 := bstep (se 4 (by rfl) ⟨1050048, by rfl⟩ : syracuseStep 11200517 = 2100097) B2100097
theorem B1165319 : Blo 1164640 1165319 := bstep (se 1 (by rfl) ⟨873989, by rfl⟩ : syracuseStep 1165319 = 1747979) B1747979
theorem B1165327 : Blo 1164640 1165327 := bstep (se 1 (by rfl) ⟨873995, by rfl⟩ : syracuseStep 1165327 = 1747991) B1747991
theorem B20195351 : Blo 1164640 20195351 := bstep (se 1 (by rfl) ⟨15146513, by rfl⟩ : syracuseStep 20195351 = 30293027) B30293027
theorem B6301739 : Blo 1164640 6301739 := bstep (se 1 (by rfl) ⟨4726304, by rfl⟩ : syracuseStep 6301739 = 9452609) B9452609
theorem B1747001 : Blo 1164640 1747001 := bstep (se 2 (by rfl) ⟨655125, by rfl⟩ : syracuseStep 1747001 = 1310251) B1310251
theorem B1165371 : Blo 1164640 1165371 := bstep (se 1 (by rfl) ⟨874028, by rfl⟩ : syracuseStep 1165371 = 1748057) B1748057
theorem B2951255 : Blo 1164640 2951255 := bstep (se 1 (by rfl) ⟨2213441, by rfl⟩ : syracuseStep 2951255 = 4426883) B4426883
theorem B2623607 : Blo 1164640 2623607 := bstep (se 1 (by rfl) ⟨1967705, by rfl⟩ : syracuseStep 2623607 = 3935411) B3935411
theorem B1747079 : Blo 1164640 1747079 := bstep (se 1 (by rfl) ⟨1310309, by rfl⟩ : syracuseStep 1747079 = 2620619) B2620619
theorem B1165447 : Blo 1164640 1165447 := bstep (se 1 (by rfl) ⟨874085, by rfl⟩ : syracuseStep 1165447 = 1748171) B1748171
theorem B1165455 : Blo 1164640 1165455 := bstep (se 1 (by rfl) ⟨874091, by rfl⟩ : syracuseStep 1165455 = 1748183) B1748183
theorem B1747115 : Blo 1164640 1747115 := bstep (se 1 (by rfl) ⟨1310336, by rfl⟩ : syracuseStep 1747115 = 2620673) B2620673
theorem B1165499 : Blo 1164640 1165499 := bstep (se 1 (by rfl) ⟨874124, by rfl⟩ : syracuseStep 1165499 = 1748249) B1748249
theorem B1747145 : Blo 1164640 1747145 := bstep (se 2 (by rfl) ⟨655179, by rfl⟩ : syracuseStep 1747145 = 1310359) B1310359
theorem B5900525 : Blo 1164640 5900525 := bstep (se 3 (by rfl) ⟨1106348, by rfl⟩ : syracuseStep 5900525 = 2212697) B2212697
theorem B1165575 : Blo 1164640 1165575 := bstep (se 1 (by rfl) ⟨874181, by rfl⟩ : syracuseStep 1165575 = 1748363) B1748363
theorem B1165583 : Blo 1164640 1165583 := bstep (se 1 (by rfl) ⟨874187, by rfl⟩ : syracuseStep 1165583 = 1748375) B1748375
theorem B2361643 : Blo 1164640 2361643 := bstep (se 1 (by rfl) ⟨1771232, by rfl⟩ : syracuseStep 2361643 = 3542465) B3542465
theorem B2623787 : Blo 1164640 2623787 := bstep (se 1 (by rfl) ⟨1967840, by rfl⟩ : syracuseStep 2623787 = 3935681) B3935681
theorem B1747259 : Blo 1164640 1747259 := bstep (se 1 (by rfl) ⟨1310444, by rfl⟩ : syracuseStep 1747259 = 2620889) B2620889
theorem B1165627 : Blo 1164640 1165627 := bstep (se 1 (by rfl) ⟨874220, by rfl⟩ : syracuseStep 1165627 = 1748441) B1748441
theorem B1747319 : Blo 1164640 1747319 := bstep (se 1 (by rfl) ⟨1310489, by rfl⟩ : syracuseStep 1747319 = 2620979) B2620979
theorem B1165703 : Blo 1164640 1165703 := bstep (se 1 (by rfl) ⟨874277, by rfl⟩ : syracuseStep 1165703 = 1748555) B1748555
theorem B1747343 : Blo 1164640 1747343 := bstep (se 1 (by rfl) ⟨1310507, by rfl⟩ : syracuseStep 1747343 = 2621015) B2621015
theorem B1165711 : Blo 1164640 1165711 := bstep (se 1 (by rfl) ⟨874283, by rfl⟩ : syracuseStep 1165711 = 1748567) B1748567
theorem B1747385 : Blo 1164640 1747385 := bstep (se 2 (by rfl) ⟨655269, by rfl⟩ : syracuseStep 1747385 = 1310539) B1310539
theorem B1165755 : Blo 1164640 1165755 := bstep (se 1 (by rfl) ⟨874316, by rfl⟩ : syracuseStep 1165755 = 1748633) B1748633
theorem B1747463 : Blo 1164640 1747463 := bstep (se 1 (by rfl) ⟨1310597, by rfl⟩ : syracuseStep 1747463 = 2621195) B2621195
theorem B1165831 : Blo 1164640 1165831 := bstep (se 1 (by rfl) ⟨874373, by rfl⟩ : syracuseStep 1165831 = 1748747) B1748747
theorem B1165839 : Blo 1164640 1165839 := bstep (se 1 (by rfl) ⟨874379, by rfl⟩ : syracuseStep 1165839 = 1748759) B1748759
theorem B1747499 : Blo 1164640 1747499 := bstep (se 1 (by rfl) ⟨1310624, by rfl⟩ : syracuseStep 1747499 = 2621249) B2621249
theorem B3934763 : Blo 1164640 3934763 := bstep (se 1 (by rfl) ⟨2951072, by rfl⟩ : syracuseStep 3934763 = 5902145) B5902145
theorem B1165883 : Blo 1164640 1165883 := bstep (se 1 (by rfl) ⟨874412, by rfl⟩ : syracuseStep 1165883 = 1748825) B1748825
theorem B1747529 : Blo 1164640 1747529 := bstep (se 2 (by rfl) ⟨655323, by rfl⟩ : syracuseStep 1747529 = 1310647) B1310647
theorem B1681993 : Blo 1164640 1681993 := bstep (se 2 (by rfl) ⟨630747, by rfl⟩ : syracuseStep 1681993 = 1261495) B1261495
theorem B1165959 : Blo 1164640 1165959 := bstep (se 1 (by rfl) ⟨874469, by rfl⟩ : syracuseStep 1165959 = 1748939) B1748939
theorem B1165967 : Blo 1164640 1165967 := bstep (se 1 (by rfl) ⟨874475, by rfl⟩ : syracuseStep 1165967 = 1748951) B1748951
theorem B2624147 : Blo 1164640 2624147 := bstep (se 1 (by rfl) ⟨1968110, by rfl⟩ : syracuseStep 2624147 = 3936221) B3936221
theorem B1747643 : Blo 1164640 1747643 := bstep (se 1 (by rfl) ⟨1310732, by rfl⟩ : syracuseStep 1747643 = 2621465) B2621465
theorem B1166011 : Blo 1164640 1166011 := bstep (se 1 (by rfl) ⟨874508, by rfl⟩ : syracuseStep 1166011 = 1749017) B1749017
theorem B2624201 : Blo 1164640 2624201 := bstep (se 2 (by rfl) ⟨984075, by rfl⟩ : syracuseStep 2624201 = 1968151) B1968151
theorem B1747703 : Blo 1164640 1747703 := bstep (se 1 (by rfl) ⟨1310777, by rfl⟩ : syracuseStep 1747703 = 2621555) B2621555
theorem B1166087 : Blo 1164640 1166087 := bstep (se 1 (by rfl) ⟨874565, by rfl⟩ : syracuseStep 1166087 = 1749131) B1749131
theorem B1747727 : Blo 1164640 1747727 := bstep (se 1 (by rfl) ⟨1310795, by rfl⟩ : syracuseStep 1747727 = 2621591) B2621591
theorem B1166095 : Blo 1164640 1166095 := bstep (se 1 (by rfl) ⟨874571, by rfl⟩ : syracuseStep 1166095 = 1749143) B1749143
theorem B1747769 : Blo 1164640 1747769 := bstep (se 2 (by rfl) ⟨655413, by rfl⟩ : syracuseStep 1747769 = 1310827) B1310827
theorem B1166139 : Blo 1164640 1166139 := bstep (se 1 (by rfl) ⟨874604, by rfl⟩ : syracuseStep 1166139 = 1749209) B1749209
theorem B1747847 : Blo 1164640 1747847 := bstep (se 1 (by rfl) ⟨1310885, by rfl⟩ : syracuseStep 1747847 = 2621771) B2621771
theorem B1166215 : Blo 1164640 1166215 := bstep (se 1 (by rfl) ⟨874661, by rfl⟩ : syracuseStep 1166215 = 1749323) B1749323
theorem B1166223 : Blo 1164640 1166223 := bstep (se 1 (by rfl) ⟨874667, by rfl⟩ : syracuseStep 1166223 = 1749335) B1749335
theorem B1747883 : Blo 1164640 1747883 := bstep (se 1 (by rfl) ⟨1310912, by rfl⟩ : syracuseStep 1747883 = 2621825) B2621825
theorem B1166267 : Blo 1164640 1166267 := bstep (se 1 (by rfl) ⟨874700, by rfl⟩ : syracuseStep 1166267 = 1749401) B1749401
theorem B1747913 : Blo 1164640 1747913 := bstep (se 2 (by rfl) ⟨655467, by rfl⟩ : syracuseStep 1747913 = 1310935) B1310935
theorem B3320777 : Blo 1164640 3320777 := bstep (se 2 (by rfl) ⟨1245291, by rfl⟩ : syracuseStep 3320777 = 2490583) B2490583
theorem B1166343 : Blo 1164640 1166343 := bstep (se 1 (by rfl) ⟨874757, by rfl⟩ : syracuseStep 1166343 = 1749515) B1749515
theorem B1166351 : Blo 1164640 1166351 := bstep (se 1 (by rfl) ⟨874763, by rfl⟩ : syracuseStep 1166351 = 1749527) B1749527
theorem B5901335 : Blo 1164640 5901335 := bstep (se 1 (by rfl) ⟨4426001, by rfl⟩ : syracuseStep 5901335 = 8852003) B8852003
theorem B1748027 : Blo 1164640 1748027 := bstep (se 1 (by rfl) ⟨1311020, by rfl⟩ : syracuseStep 1748027 = 2622041) B2622041
theorem B1166395 : Blo 1164640 1166395 := bstep (se 1 (by rfl) ⟨874796, by rfl⟩ : syracuseStep 1166395 = 1749593) B1749593
theorem B1748087 : Blo 1164640 1748087 := bstep (se 1 (by rfl) ⟨1311065, by rfl⟩ : syracuseStep 1748087 = 2622131) B2622131
theorem B1748111 : Blo 1164640 1748111 := bstep (se 1 (by rfl) ⟨1311083, by rfl⟩ : syracuseStep 1748111 = 2622167) B2622167
theorem B1748153 : Blo 1164640 1748153 := bstep (se 2 (by rfl) ⟨655557, by rfl⟩ : syracuseStep 1748153 = 1311115) B1311115
theorem B1748231 : Blo 1164640 1748231 := bstep (se 1 (by rfl) ⟨1311173, by rfl⟩ : syracuseStep 1748231 = 2622347) B2622347
theorem B1748267 : Blo 1164640 1748267 := bstep (se 1 (by rfl) ⟨1311200, by rfl⟩ : syracuseStep 1748267 = 2622401) B2622401
theorem B1748297 : Blo 1164640 1748297 := bstep (se 2 (by rfl) ⟨655611, by rfl⟩ : syracuseStep 1748297 = 1311223) B1311223
theorem B12610961 : Blo 1164640 12610961 := bstep (se 2 (by rfl) ⟨4729110, by rfl⟩ : syracuseStep 12610961 = 9458221) B9458221
theorem B11193785 : Blo 1164640 11193785 := bstep (se 2 (by rfl) ⟨4197669, by rfl⟩ : syracuseStep 11193785 = 8395339) B8395339
theorem B1748411 : Blo 1164640 1748411 := bstep (se 1 (by rfl) ⟨1311308, by rfl⟩ : syracuseStep 1748411 = 2622617) B2622617
theorem B1748471 : Blo 1164640 1748471 := bstep (se 1 (by rfl) ⟨1311353, by rfl⟩ : syracuseStep 1748471 = 2622707) B2622707
theorem B1748495 : Blo 1164640 1748495 := bstep (se 1 (by rfl) ⟨1311371, by rfl⟩ : syracuseStep 1748495 = 2622743) B2622743
theorem B1748537 : Blo 1164640 1748537 := bstep (se 2 (by rfl) ⟨655701, by rfl⟩ : syracuseStep 1748537 = 1311403) B1311403
theorem B1658441 : Blo 1164640 1658441 := bstep (se 2 (by rfl) ⟨621915, by rfl⟩ : syracuseStep 1658441 = 1243831) B1243831
theorem B1748615 : Blo 1164640 1748615 := bstep (se 1 (by rfl) ⟨1311461, by rfl⟩ : syracuseStep 1748615 = 2622923) B2622923
theorem B1748651 : Blo 1164640 1748651 := bstep (se 1 (by rfl) ⟨1311488, by rfl⟩ : syracuseStep 1748651 = 2622977) B2622977
theorem B1748681 : Blo 1164640 1748681 := bstep (se 2 (by rfl) ⟨655755, by rfl⟩ : syracuseStep 1748681 = 1311511) B1311511
theorem B4976417 : Blo 1164640 4976417 := bstep (se 2 (by rfl) ⟨1866156, by rfl⟩ : syracuseStep 4976417 = 3732313) B3732313
theorem B2395937 : Blo 1164640 2395937 := bstep (se 2 (by rfl) ⟨898476, by rfl⟩ : syracuseStep 2395937 = 1796953) B1796953
theorem B1748795 : Blo 1164640 1748795 := bstep (se 1 (by rfl) ⟨1311596, by rfl⟩ : syracuseStep 1748795 = 2623193) B2623193
theorem B3936059 : Blo 1164640 3936059 := bstep (se 1 (by rfl) ⟨2952044, by rfl⟩ : syracuseStep 3936059 = 5904089) B5904089
theorem B1748855 : Blo 1164640 1748855 := bstep (se 1 (by rfl) ⟨1311641, by rfl⟩ : syracuseStep 1748855 = 2623283) B2623283
theorem B1748879 : Blo 1164640 1748879 := bstep (se 1 (by rfl) ⟨1311659, by rfl⟩ : syracuseStep 1748879 = 2623319) B2623319
theorem B1748921 : Blo 1164640 1748921 := bstep (se 2 (by rfl) ⟨655845, by rfl⟩ : syracuseStep 1748921 = 1311691) B1311691
theorem B1748999 : Blo 1164640 1748999 := bstep (se 1 (by rfl) ⟨1311749, by rfl⟩ : syracuseStep 1748999 = 2623499) B2623499
theorem B3731467 : Blo 1164640 3731467 := bstep (se 1 (by rfl) ⟨2798600, by rfl⟩ : syracuseStep 3731467 = 5597201) B5597201
theorem B1749035 : Blo 1164640 1749035 := bstep (se 1 (by rfl) ⟨1311776, by rfl⟩ : syracuseStep 1749035 = 2623553) B2623553
theorem B8851517 : Blo 1164640 8851517 := bstep (se 3 (by rfl) ⟨1659659, by rfl⟩ : syracuseStep 8851517 = 3319319) B3319319
theorem B1749065 : Blo 1164640 1749065 := bstep (se 2 (by rfl) ⟨655899, by rfl⟩ : syracuseStep 1749065 = 1311799) B1311799
theorem B1658999 : Blo 1164640 1658999 := bstep (se 1 (by rfl) ⟨1244249, by rfl⟩ : syracuseStep 1658999 = 2488499) B2488499
theorem B1749179 : Blo 1164640 1749179 := bstep (se 1 (by rfl) ⟨1311884, by rfl⟩ : syracuseStep 1749179 = 2623769) B2623769
theorem B1749239 : Blo 1164640 1749239 := bstep (se 1 (by rfl) ⟨1311929, by rfl⟩ : syracuseStep 1749239 = 2623859) B2623859
theorem B3838223 : Blo 1164640 3838223 := bstep (se 1 (by rfl) ⟨2878667, by rfl⟩ : syracuseStep 3838223 = 5757335) B5757335
theorem B1749263 : Blo 1164640 1749263 := bstep (se 1 (by rfl) ⟨1311947, by rfl⟩ : syracuseStep 1749263 = 2623895) B2623895
theorem B3936545 : Blo 1164640 3936545 := bstep (se 2 (by rfl) ⟨1476204, by rfl⟩ : syracuseStep 3936545 = 2952409) B2952409
theorem B1749305 : Blo 1164640 1749305 := bstep (se 2 (by rfl) ⟨655989, by rfl⟩ : syracuseStep 1749305 = 1311979) B1311979
theorem B3150199 : Blo 1164640 3150199 := bstep (se 1 (by rfl) ⟨2362649, by rfl⟩ : syracuseStep 3150199 = 4725299) B4725299
theorem B1749383 : Blo 1164640 1749383 := bstep (se 1 (by rfl) ⟨1312037, by rfl⟩ : syracuseStep 1749383 = 2624075) B2624075
theorem B1659307 : Blo 1164640 1659307 := bstep (se 1 (by rfl) ⟨1244480, by rfl⟩ : syracuseStep 1659307 = 2488961) B2488961
theorem B1749419 : Blo 1164640 1749419 := bstep (se 1 (by rfl) ⟨1312064, by rfl⟩ : syracuseStep 1749419 = 2624129) B2624129
theorem B1749449 : Blo 1164640 1749449 := bstep (se 2 (by rfl) ⟨656043, by rfl⟩ : syracuseStep 1749449 = 1312087) B1312087
theorem B16806365 : Blo 1164640 16806365 := bstep (se 3 (by rfl) ⟨3151193, by rfl⟩ : syracuseStep 16806365 = 6302387) B6302387
theorem B44798507 : Blo 1164640 44798507 := bstep (se 1 (by rfl) ⟨33598880, by rfl⟩ : syracuseStep 44798507 = 67197761) B67197761
theorem B1749563 : Blo 1164640 1749563 := bstep (se 1 (by rfl) ⟨1312172, by rfl⟩ : syracuseStep 1749563 = 2624345) B2624345
theorem B15946307 : Blo 1164640 15946307 := bstep (se 1 (by rfl) ⟨11959730, by rfl⟩ : syracuseStep 15946307 = 23919461) B23919461
theorem B4199201 : Blo 1164640 4199201 := bstep (se 2 (by rfl) ⟨1574700, by rfl⟩ : syracuseStep 4199201 = 3149401) B3149401
theorem B3592993 : Blo 1164640 3592993 := bstep (se 2 (by rfl) ⟨1347372, by rfl⟩ : syracuseStep 3592993 = 2694745) B2694745
theorem B11195171 : Blo 1164640 11195171 := bstep (se 1 (by rfl) ⟨8396378, by rfl⟩ : syracuseStep 11195171 = 16792757) B16792757
theorem B1659791 : Blo 1164640 1659791 := bstep (se 1 (by rfl) ⟨1244843, by rfl⟩ : syracuseStep 1659791 = 2489687) B2489687
theorem B6640643 : Blo 1164640 6640643 := bstep (se 1 (by rfl) ⟨4980482, by rfl⟩ : syracuseStep 6640643 = 9960965) B9960965
theorem B51811397 : Blo 1164640 51811397 := bstep (se 4 (by rfl) ⟨4857318, by rfl⟩ : syracuseStep 51811397 = 9714637) B9714637
theorem B272667779 : Blo 1164640 272667779 := bstep (se 1 (by rfl) ⟨204500834, by rfl⟩ : syracuseStep 272667779 = 409001669) B409001669
theorem B2364563 : Blo 1164640 2364563 := bstep (se 1 (by rfl) ⟨1773422, by rfl⟩ : syracuseStep 2364563 = 3546845) B3546845
theorem B5600429 : Blo 1164640 5600429 := bstep (se 3 (by rfl) ⟨1050080, by rfl⟩ : syracuseStep 5600429 = 2100161) B2100161
theorem B2487611 : Blo 1164640 2487611 := bstep (se 1 (by rfl) ⟨1865708, by rfl⟩ : syracuseStep 2487611 = 3731417) B3731417
theorem B2659643 : Blo 1164640 2659643 := bstep (se 1 (by rfl) ⟨1994732, by rfl⟩ : syracuseStep 2659643 = 3989465) B3989465
theorem B11203933 : Blo 1164640 11203933 := bstep (se 3 (by rfl) ⟨2100737, by rfl⟩ : syracuseStep 11203933 = 4201475) B4201475
theorem B13276547 : Blo 1164640 13276547 := bstep (se 1 (by rfl) ⟨9957410, by rfl⟩ : syracuseStep 13276547 = 19914821) B19914821
theorem B6641099 : Blo 1164640 6641099 := bstep (se 1 (by rfl) ⟨4980824, by rfl⟩ : syracuseStep 6641099 = 9961649) B9961649
theorem B12596813 : Blo 1164640 12596813 := bstep (se 3 (by rfl) ⟨2361902, by rfl⟩ : syracuseStep 12596813 = 4723805) B4723805
theorem B3151703 : Blo 1164640 3151703 := bstep (se 1 (by rfl) ⟨2363777, by rfl⟩ : syracuseStep 3151703 = 4727555) B4727555
theorem B5904413 : Blo 1164640 5904413 := bstep (se 3 (by rfl) ⟨1107077, by rfl⟩ : syracuseStep 5904413 = 2214155) B2214155
theorem B6641783 : Blo 1164640 6641783 := bstep (se 1 (by rfl) ⟨4981337, by rfl⟩ : syracuseStep 6641783 = 9962675) B9962675
theorem B2488619 : Blo 1164640 2488619 := bstep (se 1 (by rfl) ⟨1866464, by rfl⟩ : syracuseStep 2488619 = 3732929) B3732929
theorem B4422023 : Blo 1164640 4422023 := bstep (se 1 (by rfl) ⟨3316517, by rfl⟩ : syracuseStep 4422023 = 6633035) B6633035
theorem B18897299 : Blo 1164640 18897299 := bstep (se 1 (by rfl) ⟨14172974, by rfl⟩ : syracuseStep 18897299 = 28345949) B28345949
theorem B1866169 : Blo 1164640 1866169 := bstep (se 2 (by rfl) ⟨699813, by rfl⟩ : syracuseStep 1866169 = 1399627) B1399627
theorem B5904899 : Blo 1164640 5904899 := bstep (se 1 (by rfl) ⟨4428674, by rfl⟩ : syracuseStep 5904899 = 8857349) B8857349
theorem B7469597 : Blo 1164640 7469597 := bstep (se 3 (by rfl) ⟨1400549, by rfl⟩ : syracuseStep 7469597 = 2801099) B2801099
theorem B2988587 : Blo 1164640 2988587 := bstep (se 1 (by rfl) ⟨2241440, by rfl⟩ : syracuseStep 2988587 = 4482881) B4482881
theorem B21568193 : Blo 1164640 21568193 := bstep (se 2 (by rfl) ⟨8088072, by rfl⟩ : syracuseStep 21568193 = 16176145) B16176145
theorem B5896961 : Blo 1164640 5896961 := bstep (se 2 (by rfl) ⟨2211360, by rfl⟩ : syracuseStep 5896961 = 4422721) B4422721
theorem B2620475 : Blo 1164640 2620475 := bstep (se 1 (by rfl) ⟨1965356, by rfl⟩ : syracuseStep 2620475 = 3930713) B3930713
theorem B2620601 : Blo 1164640 2620601 := bstep (se 2 (by rfl) ⟨982725, by rfl⟩ : syracuseStep 2620601 = 1965451) B1965451
theorem B2800907 : Blo 1164640 2800907 := bstep (se 1 (by rfl) ⟨2100680, by rfl⟩ : syracuseStep 2800907 = 4201361) B4201361
theorem B2522411 : Blo 1164640 2522411 := bstep (se 1 (by rfl) ⟨1891808, by rfl⟩ : syracuseStep 2522411 = 3783617) B3783617
theorem B6634811 : Blo 1164640 6634811 := bstep (se 1 (by rfl) ⟨4976108, by rfl⟩ : syracuseStep 6634811 = 9952217) B9952217
theorem B1965431 : Blo 1164640 1965431 := bstep (se 1 (by rfl) ⟨1474073, by rfl⟩ : syracuseStep 1965431 = 2948147) B2948147
theorem B2948471 : Blo 1164640 2948471 := bstep (se 1 (by rfl) ⟨2211353, by rfl⟩ : syracuseStep 2948471 = 4422707) B4422707
theorem B8854919 : Blo 1164640 8854919 := bstep (se 1 (by rfl) ⟨6641189, by rfl⟩ : syracuseStep 8854919 = 13282379) B13282379
theorem B22396337 : Blo 1164640 22396337 := bstep (se 2 (by rfl) ⟨8398626, by rfl⟩ : syracuseStep 22396337 = 16797253) B16797253
theorem B3931577 : Blo 1164640 3931577 := bstep (se 2 (by rfl) ⟨1474341, by rfl⟩ : syracuseStep 3931577 = 2948683) B2948683
theorem B2801081 : Blo 1164640 2801081 := bstep (se 2 (by rfl) ⟨1050405, by rfl⟩ : syracuseStep 2801081 = 2100811) B2100811
theorem B2620943 : Blo 1164640 2620943 := bstep (se 1 (by rfl) ⟨1965707, by rfl⟩ : syracuseStep 2620943 = 3931415) B3931415
theorem B6471191 : Blo 1164640 6471191 := bstep (se 1 (by rfl) ⟨4853393, by rfl⟩ : syracuseStep 6471191 = 9706787) B9706787
theorem B2620961 : Blo 1164640 2620961 := bstep (se 2 (by rfl) ⟨982860, by rfl⟩ : syracuseStep 2620961 = 1965721) B1965721
theorem B5897771 : Blo 1164640 5897771 := bstep (se 1 (by rfl) ⟨4423328, by rfl⟩ : syracuseStep 5897771 = 8846657) B8846657
theorem B2211475 : Blo 1164640 2211475 := bstep (se 1 (by rfl) ⟨1658606, by rfl⟩ : syracuseStep 2211475 = 3317213) B3317213
theorem B3317395 : Blo 1164640 3317395 := bstep (se 1 (by rfl) ⟨2488046, by rfl⟩ : syracuseStep 3317395 = 4976093) B4976093
theorem B1310395 : Blo 1164640 1310395 := bstep (se 1 (by rfl) ⟨982796, by rfl⟩ : syracuseStep 1310395 = 1965593) B1965593
theorem B1965883 : Blo 1164640 1965883 := bstep (se 1 (by rfl) ⟨1474412, by rfl⟩ : syracuseStep 1965883 = 2948825) B2948825
theorem B17030981 : Blo 1164640 17030981 := bstep (se 4 (by rfl) ⟨1596654, by rfl⟩ : syracuseStep 17030981 = 3193309) B3193309
theorem B2621303 : Blo 1164640 2621303 := bstep (se 1 (by rfl) ⟨1965977, by rfl⟩ : syracuseStep 2621303 = 3931955) B3931955
theorem B28737431 : Blo 1164640 28737431 := bstep (se 1 (by rfl) ⟨21553073, by rfl⟩ : syracuseStep 28737431 = 43106147) B43106147
theorem B2490259 : Blo 1164640 2490259 := bstep (se 1 (by rfl) ⟨1867694, by rfl⟩ : syracuseStep 2490259 = 3735389) B3735389
theorem B1966025 : Blo 1164640 1966025 := bstep (se 2 (by rfl) ⟨737259, by rfl⟩ : syracuseStep 1966025 = 1474519) B1474519
theorem B4980689 : Blo 1164640 4980689 := bstep (se 2 (by rfl) ⟨1867758, by rfl⟩ : syracuseStep 4980689 = 3735517) B3735517
theorem B2621447 : Blo 1164640 2621447 := bstep (se 1 (by rfl) ⟨1966085, by rfl⟩ : syracuseStep 2621447 = 3932171) B3932171
theorem B2621519 : Blo 1164640 2621519 := bstep (se 1 (by rfl) ⟨1966139, by rfl⟩ : syracuseStep 2621519 = 3932279) B3932279
theorem B4423997 : Blo 1164640 4423997 := bstep (se 3 (by rfl) ⟨829499, by rfl⟩ : syracuseStep 4423997 = 1658999) B1658999
theorem B1868105 : Blo 1164640 1868105 := bstep (se 2 (by rfl) ⟨700539, by rfl⟩ : syracuseStep 1868105 = 1401079) B1401079
theorem B1966511 : Blo 1164640 1966511 := bstep (se 1 (by rfl) ⟨1474883, by rfl⟩ : syracuseStep 1966511 = 2949767) B2949767
theorem B1311151 : Blo 1164640 1311151 := bstep (se 1 (by rfl) ⟨983363, by rfl⟩ : syracuseStep 1311151 = 1966727) B1966727
theorem B2621915 : Blo 1164640 2621915 := bstep (se 1 (by rfl) ⟨1966436, by rfl⟩ : syracuseStep 2621915 = 3932873) B3932873
theorem B4424179 : Blo 1164640 4424179 := bstep (se 1 (by rfl) ⟨3318134, by rfl⟩ : syracuseStep 4424179 = 6636269) B6636269
theorem B7463447 : Blo 1164640 7463447 := bstep (se 1 (by rfl) ⟨5597585, by rfl⟩ : syracuseStep 7463447 = 11195171) B11195171
theorem B3932711 : Blo 1164640 3932711 := bstep (se 1 (by rfl) ⟨2949533, by rfl⟩ : syracuseStep 3932711 = 5899067) B5899067
theorem B1475111 : Blo 1164640 1475111 := bstep (se 1 (by rfl) ⟨1106333, by rfl⟩ : syracuseStep 1475111 = 2212667) B2212667
theorem B2212409 : Blo 1164640 2212409 := bstep (se 2 (by rfl) ⟨829653, by rfl⟩ : syracuseStep 2212409 = 1659307) B1659307
theorem B3932819 : Blo 1164640 3932819 := bstep (se 1 (by rfl) ⟨2949614, by rfl⟩ : syracuseStep 3932819 = 5899229) B5899229
theorem B1966943 : Blo 1164640 1966943 := bstep (se 1 (by rfl) ⟨1475207, by rfl⟩ : syracuseStep 1966943 = 2950415) B2950415
theorem B1311583 : Blo 1164640 1311583 := bstep (se 1 (by rfl) ⟨983687, by rfl⟩ : syracuseStep 1311583 = 1967375) B1967375
theorem B3933035 : Blo 1164640 3933035 := bstep (se 1 (by rfl) ⟨2949776, by rfl⟩ : syracuseStep 3933035 = 5899553) B5899553
theorem B1475435 : Blo 1164640 1475435 := bstep (se 1 (by rfl) ⟨1106576, by rfl⟩ : syracuseStep 1475435 = 2213153) B2213153
theorem B3736439 : Blo 1164640 3736439 := bstep (se 1 (by rfl) ⟨2802329, by rfl⟩ : syracuseStep 3736439 = 5604659) B5604659
theorem B2212751 : Blo 1164640 2212751 := bstep (se 1 (by rfl) ⟨1659563, by rfl⟩ : syracuseStep 2212751 = 3319127) B3319127
theorem B3933089 : Blo 1164640 3933089 := bstep (se 2 (by rfl) ⟨1474908, by rfl⟩ : syracuseStep 3933089 = 2949817) B2949817
theorem B2622383 : Blo 1164640 2622383 := bstep (se 1 (by rfl) ⟨1966787, by rfl⟩ : syracuseStep 2622383 = 3933575) B3933575
theorem B8397875 : Blo 1164640 8397875 := bstep (se 1 (by rfl) ⟨6298406, by rfl⟩ : syracuseStep 8397875 = 12596813) B12596813
theorem B2622635 : Blo 1164640 2622635 := bstep (se 1 (by rfl) ⟨1966976, by rfl⟩ : syracuseStep 2622635 = 3933953) B3933953
theorem B1311943 : Blo 1164640 1311943 := bstep (se 1 (by rfl) ⟨983957, by rfl⟩ : syracuseStep 1311943 = 1967915) B1967915
theorem B1164667 : Blo 1164640 1164667 := bstep (se 1 (by rfl) ⟨873500, by rfl⟩ : syracuseStep 1164667 = 1747001) B1747001
theorem B1967503 : Blo 1164640 1967503 := bstep (se 1 (by rfl) ⟨1475627, by rfl⟩ : syracuseStep 1967503 = 2951255) B2951255
theorem B1164719 : Blo 1164640 1164719 := bstep (se 1 (by rfl) ⟨873539, by rfl⟩ : syracuseStep 1164719 = 1747079) B1747079
theorem B1164743 : Blo 1164640 1164743 := bstep (se 1 (by rfl) ⟨873557, by rfl⟩ : syracuseStep 1164743 = 1747115) B1747115
theorem B1164763 : Blo 1164640 1164763 := bstep (se 1 (by rfl) ⟨873572, by rfl⟩ : syracuseStep 1164763 = 1747145) B1747145
theorem B3933683 : Blo 1164640 3933683 := bstep (se 1 (by rfl) ⟨2950262, by rfl⟩ : syracuseStep 3933683 = 5900525) B5900525
theorem B1164839 : Blo 1164640 1164839 := bstep (se 1 (by rfl) ⟨873629, by rfl⟩ : syracuseStep 1164839 = 1747259) B1747259
theorem B1164879 : Blo 1164640 1164879 := bstep (se 1 (by rfl) ⟨873659, by rfl⟩ : syracuseStep 1164879 = 1747319) B1747319
theorem B1164895 : Blo 1164640 1164895 := bstep (se 1 (by rfl) ⟨873671, by rfl⟩ : syracuseStep 1164895 = 1747343) B1747343
theorem B1164923 : Blo 1164640 1164923 := bstep (se 1 (by rfl) ⟨873692, by rfl⟩ : syracuseStep 1164923 = 1747385) B1747385
theorem B1164975 : Blo 1164640 1164975 := bstep (se 1 (by rfl) ⟨873731, by rfl⟩ : syracuseStep 1164975 = 1747463) B1747463
theorem B1164999 : Blo 1164640 1164999 := bstep (se 1 (by rfl) ⟨873749, by rfl⟩ : syracuseStep 1164999 = 1747499) B1747499
theorem B2623175 : Blo 1164640 2623175 := bstep (se 1 (by rfl) ⟨1967381, by rfl⟩ : syracuseStep 2623175 = 3934763) B3934763
theorem B4425425 : Blo 1164640 4425425 := bstep (se 2 (by rfl) ⟨1659534, by rfl⟩ : syracuseStep 4425425 = 3319069) B3319069
theorem B1165019 : Blo 1164640 1165019 := bstep (se 1 (by rfl) ⟨873764, by rfl⟩ : syracuseStep 1165019 = 1747529) B1747529
theorem B1165095 : Blo 1164640 1165095 := bstep (se 1 (by rfl) ⟨873821, by rfl⟩ : syracuseStep 1165095 = 1747643) B1747643
theorem B14378795 : Blo 1164640 14378795 := bstep (se 1 (by rfl) ⟨10784096, by rfl⟩ : syracuseStep 14378795 = 21568193) B21568193
theorem B1165135 : Blo 1164640 1165135 := bstep (se 1 (by rfl) ⟨873851, by rfl⟩ : syracuseStep 1165135 = 1747703) B1747703
theorem B1165151 : Blo 1164640 1165151 := bstep (se 1 (by rfl) ⟨873863, by rfl⟩ : syracuseStep 1165151 = 1747727) B1747727
theorem B1165179 : Blo 1164640 1165179 := bstep (se 1 (by rfl) ⟨873884, by rfl⟩ : syracuseStep 1165179 = 1747769) B1747769
theorem B9963425 : Blo 1164640 9963425 := bstep (se 2 (by rfl) ⟨3736284, by rfl⟩ : syracuseStep 9963425 = 7472569) B7472569
theorem B1165231 : Blo 1164640 1165231 := bstep (se 1 (by rfl) ⟨873923, by rfl⟩ : syracuseStep 1165231 = 1747847) B1747847
theorem B1165255 : Blo 1164640 1165255 := bstep (se 1 (by rfl) ⟨873941, by rfl⟩ : syracuseStep 1165255 = 1747883) B1747883
theorem B1165275 : Blo 1164640 1165275 := bstep (se 1 (by rfl) ⟨873956, by rfl⟩ : syracuseStep 1165275 = 1747913) B1747913
theorem B3934223 : Blo 1164640 3934223 := bstep (se 1 (by rfl) ⟨2950667, by rfl⟩ : syracuseStep 3934223 = 5901335) B5901335
theorem B1746983 : Blo 1164640 1746983 := bstep (se 1 (by rfl) ⟨1310237, by rfl⟩ : syracuseStep 1746983 = 2620475) B2620475
theorem B1165351 : Blo 1164640 1165351 := bstep (se 1 (by rfl) ⟨874013, by rfl⟩ : syracuseStep 1165351 = 1748027) B1748027
theorem B2951225 : Blo 1164640 2951225 := bstep (se 2 (by rfl) ⟨1106709, by rfl⟩ : syracuseStep 2951225 = 2213419) B2213419
theorem B1968185 : Blo 1164640 1968185 := bstep (se 2 (by rfl) ⟨738069, by rfl⟩ : syracuseStep 1968185 = 1476139) B1476139
theorem B1165391 : Blo 1164640 1165391 := bstep (se 1 (by rfl) ⟨874043, by rfl⟩ : syracuseStep 1165391 = 1748087) B1748087
theorem B1165407 : Blo 1164640 1165407 := bstep (se 1 (by rfl) ⟨874055, by rfl⟩ : syracuseStep 1165407 = 1748111) B1748111
theorem B1747067 : Blo 1164640 1747067 := bstep (se 1 (by rfl) ⟨1310300, by rfl⟩ : syracuseStep 1747067 = 2620601) B2620601
theorem B1165435 : Blo 1164640 1165435 := bstep (se 1 (by rfl) ⟨874076, by rfl⟩ : syracuseStep 1165435 = 1748153) B1748153
theorem B1165487 : Blo 1164640 1165487 := bstep (se 1 (by rfl) ⟨874115, by rfl⟩ : syracuseStep 1165487 = 1748231) B1748231
theorem B1681607 : Blo 1164640 1681607 := bstep (se 1 (by rfl) ⟨1261205, by rfl⟩ : syracuseStep 1681607 = 2522411) B2522411
theorem B1165511 : Blo 1164640 1165511 := bstep (se 1 (by rfl) ⟨874133, by rfl⟩ : syracuseStep 1165511 = 1748267) B1748267
theorem B1165531 : Blo 1164640 1165531 := bstep (se 1 (by rfl) ⟨874148, by rfl⟩ : syracuseStep 1165531 = 1748297) B1748297
theorem B1747193 : Blo 1164640 1747193 := bstep (se 2 (by rfl) ⟨655197, by rfl⟩ : syracuseStep 1747193 = 1310395) B1310395
theorem B8407307 : Blo 1164640 8407307 := bstep (se 1 (by rfl) ⟨6305480, by rfl⟩ : syracuseStep 8407307 = 12610961) B12610961
theorem B1165607 : Blo 1164640 1165607 := bstep (se 1 (by rfl) ⟨874205, by rfl⟩ : syracuseStep 1165607 = 1748411) B1748411
theorem B1165647 : Blo 1164640 1165647 := bstep (se 1 (by rfl) ⟨874235, by rfl⟩ : syracuseStep 1165647 = 1748471) B1748471
theorem B1747295 : Blo 1164640 1747295 := bstep (se 1 (by rfl) ⟨1310471, by rfl⟩ : syracuseStep 1747295 = 2620943) B2620943
theorem B1165663 : Blo 1164640 1165663 := bstep (se 1 (by rfl) ⟨874247, by rfl⟩ : syracuseStep 1165663 = 1748495) B1748495
theorem B1747307 : Blo 1164640 1747307 := bstep (se 1 (by rfl) ⟨1310480, by rfl⟩ : syracuseStep 1747307 = 2620961) B2620961
theorem B1165691 : Blo 1164640 1165691 := bstep (se 1 (by rfl) ⟨874268, by rfl⟩ : syracuseStep 1165691 = 1748537) B1748537
theorem B4426109 : Blo 1164640 4426109 := bstep (se 3 (by rfl) ⟨829895, by rfl⟩ : syracuseStep 4426109 = 1659791) B1659791
theorem B1165743 : Blo 1164640 1165743 := bstep (se 1 (by rfl) ⟨874307, by rfl⟩ : syracuseStep 1165743 = 1748615) B1748615
theorem B1165767 : Blo 1164640 1165767 := bstep (se 1 (by rfl) ⟨874325, by rfl⟩ : syracuseStep 1165767 = 1748651) B1748651
theorem B1165787 : Blo 1164640 1165787 := bstep (se 1 (by rfl) ⟨874340, by rfl⟩ : syracuseStep 1165787 = 1748681) B1748681
theorem B3320345 : Blo 1164640 3320345 := bstep (se 2 (by rfl) ⟨1245129, by rfl⟩ : syracuseStep 3320345 = 2490259) B2490259
theorem B1165863 : Blo 1164640 1165863 := bstep (se 1 (by rfl) ⟨874397, by rfl⟩ : syracuseStep 1165863 = 1748795) B1748795
theorem B2624039 : Blo 1164640 2624039 := bstep (se 1 (by rfl) ⟨1968029, by rfl⟩ : syracuseStep 2624039 = 3936059) B3936059
theorem B1747535 : Blo 1164640 1747535 := bstep (se 1 (by rfl) ⟨1310651, by rfl⟩ : syracuseStep 1747535 = 2621303) B2621303
theorem B1165903 : Blo 1164640 1165903 := bstep (se 1 (by rfl) ⟨874427, by rfl⟩ : syracuseStep 1165903 = 1748855) B1748855
theorem B1165919 : Blo 1164640 1165919 := bstep (se 1 (by rfl) ⟨874439, by rfl⟩ : syracuseStep 1165919 = 1748879) B1748879
theorem B3934817 : Blo 1164640 3934817 := bstep (se 2 (by rfl) ⟨1475556, by rfl⟩ : syracuseStep 3934817 = 2951113) B2951113
theorem B1165947 : Blo 1164640 1165947 := bstep (se 1 (by rfl) ⟨874460, by rfl⟩ : syracuseStep 1165947 = 1748921) B1748921
theorem B3320459 : Blo 1164640 3320459 := bstep (se 1 (by rfl) ⟨2490344, by rfl⟩ : syracuseStep 3320459 = 4980689) B4980689
theorem B1165999 : Blo 1164640 1165999 := bstep (se 1 (by rfl) ⟨874499, by rfl⟩ : syracuseStep 1165999 = 1748999) B1748999
theorem B4975289 : Blo 1164640 4975289 := bstep (se 2 (by rfl) ⟨1865733, by rfl⟩ : syracuseStep 4975289 = 3731467) B3731467
theorem B1747655 : Blo 1164640 1747655 := bstep (se 1 (by rfl) ⟨1310741, by rfl⟩ : syracuseStep 1747655 = 2621483) B2621483
theorem B1166023 : Blo 1164640 1166023 := bstep (se 1 (by rfl) ⟨874517, by rfl⟩ : syracuseStep 1166023 = 1749035) B1749035
theorem B5901011 : Blo 1164640 5901011 := bstep (se 1 (by rfl) ⟨4425758, by rfl⟩ : syracuseStep 5901011 = 8851517) B8851517
theorem B1166043 : Blo 1164640 1166043 := bstep (se 1 (by rfl) ⟨874532, by rfl⟩ : syracuseStep 1166043 = 1749065) B1749065
theorem B1166119 : Blo 1164640 1166119 := bstep (se 1 (by rfl) ⟨874589, by rfl⟩ : syracuseStep 1166119 = 1749179) B1749179
theorem B1166159 : Blo 1164640 1166159 := bstep (se 1 (by rfl) ⟨874619, by rfl⟩ : syracuseStep 1166159 = 1749239) B1749239
theorem B1166175 : Blo 1164640 1166175 := bstep (se 1 (by rfl) ⟨874631, by rfl⟩ : syracuseStep 1166175 = 1749263) B1749263
theorem B1747817 : Blo 1164640 1747817 := bstep (se 2 (by rfl) ⟨655431, by rfl⟩ : syracuseStep 1747817 = 1310863) B1310863
theorem B2624363 : Blo 1164640 2624363 := bstep (se 1 (by rfl) ⟨1968272, by rfl⟩ : syracuseStep 2624363 = 3936545) B3936545
theorem B1166203 : Blo 1164640 1166203 := bstep (se 1 (by rfl) ⟨874652, by rfl⟩ : syracuseStep 1166203 = 1749305) B1749305
theorem B1166255 : Blo 1164640 1166255 := bstep (se 1 (by rfl) ⟨874691, by rfl⟩ : syracuseStep 1166255 = 1749383) B1749383
theorem B1747895 : Blo 1164640 1747895 := bstep (se 1 (by rfl) ⟨1310921, by rfl⟩ : syracuseStep 1747895 = 2621843) B2621843
theorem B1166279 : Blo 1164640 1166279 := bstep (se 1 (by rfl) ⟨874709, by rfl⟩ : syracuseStep 1166279 = 1749419) B1749419
theorem B1747931 : Blo 1164640 1747931 := bstep (se 1 (by rfl) ⟨1310948, by rfl⟩ : syracuseStep 1747931 = 2621897) B2621897
theorem B1166299 : Blo 1164640 1166299 := bstep (se 1 (by rfl) ⟨874724, by rfl⟩ : syracuseStep 1166299 = 1749449) B1749449
theorem B44837873 : Blo 1164640 44837873 := bstep (se 2 (by rfl) ⟨16814202, by rfl⟩ : syracuseStep 44837873 = 33628405) B33628405
theorem B1166375 : Blo 1164640 1166375 := bstep (se 1 (by rfl) ⟨874781, by rfl⟩ : syracuseStep 1166375 = 1749563) B1749563
theorem B33582275 : Blo 1164640 33582275 := bstep (se 1 (by rfl) ⟨25186706, by rfl⟩ : syracuseStep 33582275 = 50373413) B50373413
theorem B4427095 : Blo 1164640 4427095 := bstep (se 1 (by rfl) ⟨3320321, by rfl⟩ : syracuseStep 4427095 = 6640643) B6640643
theorem B65514865 : Blo 1164640 65514865 := bstep (se 2 (by rfl) ⟨24568074, by rfl⟩ : syracuseStep 65514865 = 49136149) B49136149
theorem B10235261 : Blo 1164640 10235261 := bstep (se 3 (by rfl) ⟨1919111, by rfl⟩ : syracuseStep 10235261 = 3838223) B3838223
theorem B34540931 : Blo 1164640 34540931 := bstep (se 1 (by rfl) ⟨25905698, by rfl⟩ : syracuseStep 34540931 = 51811397) B51811397
theorem B11201935 : Blo 1164640 11201935 := bstep (se 1 (by rfl) ⟨8401451, by rfl⟩ : syracuseStep 11201935 = 16802903) B16802903
theorem B1748399 : Blo 1164640 1748399 := bstep (se 1 (by rfl) ⟨1311299, by rfl⟩ : syracuseStep 1748399 = 2622599) B2622599
theorem B1748489 : Blo 1164640 1748489 := bstep (se 2 (by rfl) ⟨655683, by rfl⟩ : syracuseStep 1748489 = 1311367) B1311367
theorem B1658407 : Blo 1164640 1658407 := bstep (se 1 (by rfl) ⟨1243805, by rfl⟩ : syracuseStep 1658407 = 2487611) B2487611
theorem B1748519 : Blo 1164640 1748519 := bstep (se 1 (by rfl) ⟨1311389, by rfl⟩ : syracuseStep 1748519 = 2622779) B2622779
theorem B1773095 : Blo 1164640 1773095 := bstep (se 1 (by rfl) ⟨1329821, by rfl⟩ : syracuseStep 1773095 = 2659643) B2659643
theorem B8851031 : Blo 1164640 8851031 := bstep (se 1 (by rfl) ⟨6638273, by rfl⟩ : syracuseStep 8851031 = 13276547) B13276547
theorem B1748603 : Blo 1164640 1748603 := bstep (se 1 (by rfl) ⟨1311452, by rfl⟩ : syracuseStep 1748603 = 2622905) B2622905
theorem B4427399 : Blo 1164640 4427399 := bstep (se 1 (by rfl) ⟨3320549, by rfl⟩ : syracuseStep 4427399 = 6641099) B6641099
theorem B3731159 : Blo 1164640 3731159 := bstep (se 1 (by rfl) ⟨2798369, by rfl⟩ : syracuseStep 3731159 = 5596739) B5596739
theorem B1748729 : Blo 1164640 1748729 := bstep (se 2 (by rfl) ⟨655773, by rfl⟩ : syracuseStep 1748729 = 1311547) B1311547
theorem B1748831 : Blo 1164640 1748831 := bstep (se 1 (by rfl) ⟨1311623, by rfl⟩ : syracuseStep 1748831 = 2623247) B2623247
theorem B1748843 : Blo 1164640 1748843 := bstep (se 1 (by rfl) ⟨1311632, by rfl⟩ : syracuseStep 1748843 = 2623265) B2623265
theorem B22409095 : Blo 1164640 22409095 := bstep (se 1 (by rfl) ⟨16806821, by rfl⟩ : syracuseStep 22409095 = 33613643) B33613643
theorem B2101135 : Blo 1164640 2101135 := bstep (se 1 (by rfl) ⟨1575851, by rfl⟩ : syracuseStep 2101135 = 3151703) B3151703
theorem B7467011 : Blo 1164640 7467011 := bstep (se 1 (by rfl) ⟨5600258, by rfl⟩ : syracuseStep 7467011 = 11200517) B11200517
theorem B13463567 : Blo 1164640 13463567 := bstep (se 1 (by rfl) ⟨10097675, by rfl⟩ : syracuseStep 13463567 = 20195351) B20195351
theorem B3936275 : Blo 1164640 3936275 := bstep (se 1 (by rfl) ⟨2952206, by rfl⟩ : syracuseStep 3936275 = 5904413) B5904413
theorem B17256509 : Blo 1164640 17256509 := bstep (se 3 (by rfl) ⟨3235595, by rfl⟩ : syracuseStep 17256509 = 6471191) B6471191
theorem B1749071 : Blo 1164640 1749071 := bstep (se 1 (by rfl) ⟨1311803, by rfl⟩ : syracuseStep 1749071 = 2623607) B2623607
theorem B4427855 : Blo 1164640 4427855 := bstep (se 1 (by rfl) ⟨3320891, by rfl⟩ : syracuseStep 4427855 = 6641783) B6641783
theorem B1659079 : Blo 1164640 1659079 := bstep (se 1 (by rfl) ⟨1244309, by rfl⟩ : syracuseStep 1659079 = 2488619) B2488619
theorem B1749191 : Blo 1164640 1749191 := bstep (se 1 (by rfl) ⟨1311893, by rfl⟩ : syracuseStep 1749191 = 2623787) B2623787
theorem B12595429 : Blo 1164640 12595429 := bstep (se 4 (by rfl) ⟨1180821, by rfl⟩ : syracuseStep 12595429 = 2361643) B2361643
theorem B3936599 : Blo 1164640 3936599 := bstep (se 1 (by rfl) ⟨2952449, by rfl⟩ : syracuseStep 3936599 = 5904899) B5904899
theorem B1749353 : Blo 1164640 1749353 := bstep (se 2 (by rfl) ⟨656007, by rfl⟩ : syracuseStep 1749353 = 1312015) B1312015
theorem B1749431 : Blo 1164640 1749431 := bstep (se 1 (by rfl) ⟨1312073, by rfl⟩ : syracuseStep 1749431 = 2624147) B2624147
theorem B14938577 : Blo 1164640 14938577 := bstep (se 2 (by rfl) ⟨5601966, by rfl⟩ : syracuseStep 14938577 = 11203933) B11203933
theorem B1749467 : Blo 1164640 1749467 := bstep (se 1 (by rfl) ⟨1312100, by rfl⟩ : syracuseStep 1749467 = 2624201) B2624201
theorem B36352817 : Blo 1164640 36352817 := bstep (se 2 (by rfl) ⟨13632306, by rfl⟩ : syracuseStep 36352817 = 27264613) B27264613
theorem B5903279 : Blo 1164640 5903279 := bstep (se 1 (by rfl) ⟨4427459, by rfl⟩ : syracuseStep 5903279 = 8854919) B8854919
theorem B14930891 : Blo 1164640 14930891 := bstep (se 1 (by rfl) ⟨11198168, by rfl⟩ : syracuseStep 14930891 = 22396337) B22396337
theorem B19158287 : Blo 1164640 19158287 := bstep (se 1 (by rfl) ⟨14368715, by rfl⟩ : syracuseStep 19158287 = 28737431) B28737431
theorem B2020783 : Blo 1164640 2020783 := bstep (se 1 (by rfl) ⟨1515587, by rfl⟩ : syracuseStep 2020783 = 3031175) B3031175
theorem B1660343 : Blo 1164640 1660343 := bstep (se 1 (by rfl) ⟨1245257, by rfl⟩ : syracuseStep 1660343 = 2490515) B2490515
theorem B11204243 : Blo 1164640 11204243 := bstep (se 1 (by rfl) ⟨8403182, by rfl⟩ : syracuseStep 11204243 = 16806365) B16806365
theorem B29865671 : Blo 1164640 29865671 := bstep (se 1 (by rfl) ⟨22399253, by rfl⟩ : syracuseStep 29865671 = 44798507) B44798507
theorem B6641351 : Blo 1164640 6641351 := bstep (se 1 (by rfl) ⟨4981013, by rfl⟩ : syracuseStep 6641351 = 9962027) B9962027
theorem B10630871 : Blo 1164640 10630871 := bstep (se 1 (by rfl) ⟨7973153, by rfl⟩ : syracuseStep 10630871 = 15946307) B15946307
theorem B6305501 : Blo 1164640 6305501 := bstep (se 3 (by rfl) ⟨1182281, by rfl⟩ : syracuseStep 6305501 = 2364563) B2364563
theorem B4200265 : Blo 1164640 4200265 := bstep (se 2 (by rfl) ⟨1575099, by rfl⟩ : syracuseStep 4200265 = 3150199) B3150199
theorem B145446731 : Blo 1164640 145446731 := bstep (se 1 (by rfl) ⟨109085048, by rfl⟩ : syracuseStep 145446731 = 218170097) B218170097
theorem B2799467 : Blo 1164640 2799467 := bstep (se 1 (by rfl) ⟨2099600, by rfl⟩ : syracuseStep 2799467 = 4199201) B4199201
theorem B3151799 : Blo 1164640 3151799 := bstep (se 1 (by rfl) ⟨2363849, by rfl⟩ : syracuseStep 3151799 = 4727699) B4727699
theorem B181778519 : Blo 1164640 181778519 := bstep (se 1 (by rfl) ⟨136333889, by rfl⟩ : syracuseStep 181778519 = 272667779) B272667779
theorem B2242657 : Blo 1164640 2242657 := bstep (se 2 (by rfl) ⟨840996, by rfl⟩ : syracuseStep 2242657 = 1681993) B1681993
theorem B3733619 : Blo 1164640 3733619 := bstep (se 1 (by rfl) ⟨2800214, by rfl⟩ : syracuseStep 3733619 = 5600429) B5600429
theorem B4790657 : Blo 1164640 4790657 := bstep (se 2 (by rfl) ⟨1796496, by rfl⟩ : syracuseStep 4790657 = 3592993) B3592993
theorem B4201159 : Blo 1164640 4201159 := bstep (se 1 (by rfl) ⟨3150869, by rfl⟩ : syracuseStep 4201159 = 6301739) B6301739
theorem B7969565 : Blo 1164640 7969565 := bstep (se 3 (by rfl) ⟨1494293, by rfl⟩ : syracuseStep 7969565 = 2988587) B2988587
theorem B4422509 : Blo 1164640 4422509 := bstep (se 3 (by rfl) ⟨829220, by rfl⟩ : syracuseStep 4422509 = 1658441) B1658441
theorem B2948015 : Blo 1164640 2948015 := bstep (se 1 (by rfl) ⟨2211011, by rfl⟩ : syracuseStep 2948015 = 4422023) B4422023
theorem B12598199 : Blo 1164640 12598199 := bstep (se 1 (by rfl) ⟨9448649, by rfl⟩ : syracuseStep 12598199 = 18897299) B18897299
theorem B4979731 : Blo 1164640 4979731 := bstep (se 1 (by rfl) ⟨3734798, by rfl⟩ : syracuseStep 4979731 = 7469597) B7469597
theorem B3931307 : Blo 1164640 3931307 := bstep (se 1 (by rfl) ⟨2948480, by rfl⟩ : syracuseStep 3931307 = 5896961) B5896961
theorem B1867271 : Blo 1164640 1867271 := bstep (se 1 (by rfl) ⟨1400453, by rfl⟩ : syracuseStep 1867271 = 2800907) B2800907
theorem B2948633 : Blo 1164640 2948633 := bstep (se 2 (by rfl) ⟨1105737, by rfl⟩ : syracuseStep 2948633 = 2211475) B2211475
theorem B4423193 : Blo 1164640 4423193 := bstep (se 2 (by rfl) ⟨1658697, by rfl⟩ : syracuseStep 4423193 = 3317395) B3317395
theorem B4423207 : Blo 1164640 4423207 := bstep (se 1 (by rfl) ⟨3317405, by rfl⟩ : syracuseStep 4423207 = 6634811) B6634811
theorem B1310287 : Blo 1164640 1310287 := bstep (se 1 (by rfl) ⟨982715, by rfl⟩ : syracuseStep 1310287 = 1965431) B1965431
theorem B1965647 : Blo 1164640 1965647 := bstep (se 1 (by rfl) ⟨1474235, by rfl⟩ : syracuseStep 1965647 = 2948471) B2948471
theorem B7462523 : Blo 1164640 7462523 := bstep (se 1 (by rfl) ⟨5596892, by rfl⟩ : syracuseStep 7462523 = 11193785) B11193785
theorem B2621051 : Blo 1164640 2621051 := bstep (se 1 (by rfl) ⟨1965788, by rfl⟩ : syracuseStep 2621051 = 3931577) B3931577
theorem B1867387 : Blo 1164640 1867387 := bstep (se 1 (by rfl) ⟨1400540, by rfl⟩ : syracuseStep 1867387 = 2801081) B2801081
theorem B9952901 : Blo 1164640 9952901 := bstep (se 4 (by rfl) ⟨933084, by rfl⟩ : syracuseStep 9952901 = 1866169) B1866169
theorem B3931847 : Blo 1164640 3931847 := bstep (se 1 (by rfl) ⟨2948885, by rfl⟩ : syracuseStep 3931847 = 5897771) B5897771
theorem B2621177 : Blo 1164640 2621177 := bstep (se 2 (by rfl) ⟨982941, by rfl⟩ : syracuseStep 2621177 = 1965883) B1965883
theorem B3317611 : Blo 1164640 3317611 := bstep (se 1 (by rfl) ⟨2488208, by rfl⟩ : syracuseStep 3317611 = 4976417) B4976417
theorem B1597291 : Blo 1164640 1597291 := bstep (se 1 (by rfl) ⟨1197968, by rfl⟩ : syracuseStep 1597291 = 2395937) B2395937
theorem B8855405 : Blo 1164640 8855405 := bstep (se 3 (by rfl) ⟨1660388, by rfl⟩ : syracuseStep 8855405 = 3320777) B3320777
theorem B11353987 : Blo 1164640 11353987 := bstep (se 1 (by rfl) ⟨8515490, by rfl⟩ : syracuseStep 11353987 = 17030981) B17030981
theorem B1310683 : Blo 1164640 1310683 := bstep (se 1 (by rfl) ⟨983012, by rfl⟩ : syracuseStep 1310683 = 1966025) B1966025
theorem B2990209 : Blo 1164640 2990209 := bstep (se 2 (by rfl) ⟨1121328, by rfl⟩ : syracuseStep 2990209 = 2242657) B2242657
theorem B2949331 : Blo 1164640 2949331 := bstep (se 1 (by rfl) ⟨2211998, by rfl⟩ : syracuseStep 2949331 = 4423997) B4423997
theorem B1245403 : Blo 1164640 1245403 := bstep (se 1 (by rfl) ⟨934052, by rfl⟩ : syracuseStep 1245403 = 1868105) B1868105
theorem B2212105 : Blo 1164640 2212105 := bstep (se 2 (by rfl) ⟨829539, by rfl⟩ : syracuseStep 2212105 = 1659079) B1659079
theorem B1311007 : Blo 1164640 1311007 := bstep (se 1 (by rfl) ⟨983255, by rfl⟩ : syracuseStep 1311007 = 1966511) B1966511
theorem B16793905 : Blo 1164640 16793905 := bstep (se 2 (by rfl) ⟨6297714, by rfl⟩ : syracuseStep 16793905 = 12595429) B12595429
theorem B2621807 : Blo 1164640 2621807 := bstep (se 1 (by rfl) ⟨1966355, by rfl⟩ : syracuseStep 2621807 = 3932711) B3932711
theorem B1474939 : Blo 1164640 1474939 := bstep (se 1 (by rfl) ⟨1106204, by rfl⟩ : syracuseStep 1474939 = 2212409) B2212409
theorem B2621879 : Blo 1164640 2621879 := bstep (se 1 (by rfl) ⟨1966409, by rfl⟩ : syracuseStep 2621879 = 3932819) B3932819
theorem B1311295 : Blo 1164640 1311295 := bstep (se 1 (by rfl) ⟨983471, by rfl⟩ : syracuseStep 1311295 = 1966943) B1966943
theorem B2622023 : Blo 1164640 2622023 := bstep (se 1 (by rfl) ⟨1966517, by rfl⟩ : syracuseStep 2622023 = 3933035) B3933035
theorem B2490959 : Blo 1164640 2490959 := bstep (se 1 (by rfl) ⟨1868219, by rfl⟩ : syracuseStep 2490959 = 3736439) B3736439
theorem B1475167 : Blo 1164640 1475167 := bstep (se 1 (by rfl) ⟨1106375, by rfl⟩ : syracuseStep 1475167 = 2212751) B2212751
theorem B2622059 : Blo 1164640 2622059 := bstep (se 1 (by rfl) ⟨1966544, by rfl⟩ : syracuseStep 2622059 = 3933089) B3933089
theorem B9953927 : Blo 1164640 9953927 := bstep (se 1 (by rfl) ⟨7465445, by rfl⟩ : syracuseStep 9953927 = 14930891) B14930891
theorem B5898905 : Blo 1164640 5898905 := bstep (se 2 (by rfl) ⟨2212089, by rfl⟩ : syracuseStep 5898905 = 4424179) B4424179
theorem B2622455 : Blo 1164640 2622455 := bstep (se 1 (by rfl) ⟨1966841, by rfl⟩ : syracuseStep 2622455 = 3933683) B3933683
theorem B2950283 : Blo 1164640 2950283 := bstep (se 1 (by rfl) ⟨2212712, by rfl⟩ : syracuseStep 2950283 = 4425425) B4425425
theorem B7087247 : Blo 1164640 7087247 := bstep (se 1 (by rfl) ⟨5315435, by rfl⟩ : syracuseStep 7087247 = 10630871) B10630871
theorem B4203667 : Blo 1164640 4203667 := bstep (se 1 (by rfl) ⟨3152750, by rfl⟩ : syracuseStep 4203667 = 6305501) B6305501
theorem B9585863 : Blo 1164640 9585863 := bstep (se 1 (by rfl) ⟨7189397, by rfl⟩ : syracuseStep 9585863 = 14378795) B14378795
theorem B2622815 : Blo 1164640 2622815 := bstep (se 1 (by rfl) ⟨1967111, by rfl⟩ : syracuseStep 2622815 = 3934223) B3934223
theorem B1164655 : Blo 1164640 1164655 := bstep (se 1 (by rfl) ⟨873491, by rfl⟩ : syracuseStep 1164655 = 1746983) B1746983
theorem B1967483 : Blo 1164640 1967483 := bstep (se 1 (by rfl) ⟨1475612, by rfl⟩ : syracuseStep 1967483 = 2951225) B2951225
theorem B1312123 : Blo 1164640 1312123 := bstep (se 1 (by rfl) ⟨984092, by rfl⟩ : syracuseStep 1312123 = 1968185) B1968185
theorem B121185679 : Blo 1164640 121185679 := bstep (se 1 (by rfl) ⟨90889259, by rfl⟩ : syracuseStep 121185679 = 181778519) B181778519
theorem B1164711 : Blo 1164640 1164711 := bstep (se 1 (by rfl) ⟨873533, by rfl⟩ : syracuseStep 1164711 = 1747067) B1747067
theorem B3933629 : Blo 1164640 3933629 := bstep (se 3 (by rfl) ⟨737555, by rfl⟩ : syracuseStep 3933629 = 1475111) B1475111
theorem B4728253 : Blo 1164640 4728253 := bstep (se 3 (by rfl) ⟨886547, by rfl⟩ : syracuseStep 4728253 = 1773095) B1773095
theorem B1164795 : Blo 1164640 1164795 := bstep (se 1 (by rfl) ⟨873596, by rfl⟩ : syracuseStep 1164795 = 1747193) B1747193
theorem B5604871 : Blo 1164640 5604871 := bstep (se 1 (by rfl) ⟨4203653, by rfl⟩ : syracuseStep 5604871 = 8407307) B8407307
theorem B1164863 : Blo 1164640 1164863 := bstep (se 1 (by rfl) ⟨873647, by rfl⟩ : syracuseStep 1164863 = 1747295) B1747295
theorem B1164871 : Blo 1164640 1164871 := bstep (se 1 (by rfl) ⟨873653, by rfl⟩ : syracuseStep 1164871 = 1747307) B1747307
theorem B2950739 : Blo 1164640 2950739 := bstep (se 1 (by rfl) ⟨2213054, by rfl⟩ : syracuseStep 2950739 = 4426109) B4426109
theorem B2213563 : Blo 1164640 2213563 := bstep (se 1 (by rfl) ⟨1660172, by rfl⟩ : syracuseStep 2213563 = 3320345) B3320345
theorem B1165023 : Blo 1164640 1165023 := bstep (se 1 (by rfl) ⟨873767, by rfl⟩ : syracuseStep 1165023 = 1747535) B1747535
theorem B2623211 : Blo 1164640 2623211 := bstep (se 1 (by rfl) ⟨1967408, by rfl⟩ : syracuseStep 2623211 = 3934817) B3934817
theorem B2213639 : Blo 1164640 2213639 := bstep (se 1 (by rfl) ⟨1660229, by rfl⟩ : syracuseStep 2213639 = 3320459) B3320459
theorem B1165103 : Blo 1164640 1165103 := bstep (se 1 (by rfl) ⟨873827, by rfl⟩ : syracuseStep 1165103 = 1747655) B1747655
theorem B3934007 : Blo 1164640 3934007 := bstep (se 1 (by rfl) ⟨2950505, by rfl⟩ : syracuseStep 3934007 = 5901011) B5901011
theorem B87353153 : Blo 1164640 87353153 := bstep (se 2 (by rfl) ⟨32757432, by rfl⟩ : syracuseStep 87353153 = 65514865) B65514865
theorem B14935913 : Blo 1164640 14935913 := bstep (se 2 (by rfl) ⟨5600967, by rfl⟩ : syracuseStep 14935913 = 11201935) B11201935
theorem B2623337 : Blo 1164640 2623337 := bstep (se 2 (by rfl) ⟨983751, by rfl⟩ : syracuseStep 2623337 = 1967503) B1967503
theorem B1165211 : Blo 1164640 1165211 := bstep (se 1 (by rfl) ⟨873908, by rfl⟩ : syracuseStep 1165211 = 1747817) B1747817
theorem B8398799 : Blo 1164640 8398799 := bstep (se 1 (by rfl) ⟨6299099, by rfl⟩ : syracuseStep 8398799 = 12598199) B12598199
theorem B1165263 : Blo 1164640 1165263 := bstep (se 1 (by rfl) ⟨873947, by rfl⟩ : syracuseStep 1165263 = 1747895) B1747895
theorem B1165287 : Blo 1164640 1165287 := bstep (se 1 (by rfl) ⟨873965, by rfl⟩ : syracuseStep 1165287 = 1747931) B1747931
theorem B1747049 : Blo 1164640 1747049 := bstep (se 2 (by rfl) ⟨655143, by rfl⟩ : syracuseStep 1747049 = 1310287) B1310287
theorem B3934493 : Blo 1164640 3934493 := bstep (se 3 (by rfl) ⟨737717, by rfl⟩ : syracuseStep 3934493 = 1475435) B1475435
theorem B1165599 : Blo 1164640 1165599 := bstep (se 1 (by rfl) ⟨874199, by rfl⟩ : syracuseStep 1165599 = 1748399) B1748399
theorem B1165659 : Blo 1164640 1165659 := bstep (se 1 (by rfl) ⟨874244, by rfl⟩ : syracuseStep 1165659 = 1748489) B1748489
theorem B1165679 : Blo 1164640 1165679 := bstep (se 1 (by rfl) ⟨874259, by rfl⟩ : syracuseStep 1165679 = 1748519) B1748519
theorem B5900687 : Blo 1164640 5900687 := bstep (se 1 (by rfl) ⟨4425515, by rfl⟩ : syracuseStep 5900687 = 8851031) B8851031
theorem B4975015 : Blo 1164640 4975015 := bstep (se 1 (by rfl) ⟨3731261, by rfl⟩ : syracuseStep 4975015 = 7462523) B7462523
theorem B1747367 : Blo 1164640 1747367 := bstep (se 1 (by rfl) ⟨1310525, by rfl⟩ : syracuseStep 1747367 = 2621051) B2621051
theorem B1165735 : Blo 1164640 1165735 := bstep (se 1 (by rfl) ⟨874301, by rfl⟩ : syracuseStep 1165735 = 1748603) B1748603
theorem B2951599 : Blo 1164640 2951599 := bstep (se 1 (by rfl) ⟨2213699, by rfl⟩ : syracuseStep 2951599 = 4427399) B4427399
theorem B1747451 : Blo 1164640 1747451 := bstep (se 1 (by rfl) ⟨1310588, by rfl⟩ : syracuseStep 1747451 = 2621177) B2621177
theorem B1165819 : Blo 1164640 1165819 := bstep (se 1 (by rfl) ⟨874364, by rfl⟩ : syracuseStep 1165819 = 1748729) B1748729
theorem B29878793 : Blo 1164640 29878793 := bstep (se 2 (by rfl) ⟨11204547, by rfl⟩ : syracuseStep 29878793 = 22409095) B22409095
theorem B1165887 : Blo 1164640 1165887 := bstep (se 1 (by rfl) ⟨874415, by rfl⟩ : syracuseStep 1165887 = 1748831) B1748831
theorem B1165895 : Blo 1164640 1165895 := bstep (se 1 (by rfl) ⟨874421, by rfl⟩ : syracuseStep 1165895 = 1748843) B1748843
theorem B1747577 : Blo 1164640 1747577 := bstep (se 2 (by rfl) ⟨655341, by rfl⟩ : syracuseStep 1747577 = 1310683) B1310683
theorem B1747631 : Blo 1164640 1747631 := bstep (se 1 (by rfl) ⟨1310723, by rfl⟩ : syracuseStep 1747631 = 2621447) B2621447
theorem B2624183 : Blo 1164640 2624183 := bstep (se 1 (by rfl) ⟨1968137, by rfl⟩ : syracuseStep 2624183 = 3936275) B3936275
theorem B11504339 : Blo 1164640 11504339 := bstep (se 1 (by rfl) ⟨8628254, by rfl⟩ : syracuseStep 11504339 = 17256509) B17256509
theorem B1747679 : Blo 1164640 1747679 := bstep (se 1 (by rfl) ⟨1310759, by rfl⟩ : syracuseStep 1747679 = 2621519) B2621519
theorem B1166047 : Blo 1164640 1166047 := bstep (se 1 (by rfl) ⟨874535, by rfl⟩ : syracuseStep 1166047 = 1749071) B1749071
theorem B2951903 : Blo 1164640 2951903 := bstep (se 1 (by rfl) ⟨2213927, by rfl⟩ : syracuseStep 2951903 = 4427855) B4427855
theorem B1166127 : Blo 1164640 1166127 := bstep (se 1 (by rfl) ⟨874595, by rfl⟩ : syracuseStep 1166127 = 1749191) B1749191
theorem B2624399 : Blo 1164640 2624399 := bstep (se 1 (by rfl) ⟨1968299, by rfl⟩ : syracuseStep 2624399 = 3936599) B3936599
theorem B1166235 : Blo 1164640 1166235 := bstep (se 1 (by rfl) ⟨874676, by rfl⟩ : syracuseStep 1166235 = 1749353) B1749353
theorem B1166287 : Blo 1164640 1166287 := bstep (se 1 (by rfl) ⟨874715, by rfl⟩ : syracuseStep 1166287 = 1749431) B1749431
theorem B9956317 : Blo 1164640 9956317 := bstep (se 3 (by rfl) ⟨1866809, by rfl⟩ : syracuseStep 9956317 = 3733619) B3733619
theorem B1747943 : Blo 1164640 1747943 := bstep (se 1 (by rfl) ⟨1310957, by rfl⟩ : syracuseStep 1747943 = 2621915) B2621915
theorem B1166311 : Blo 1164640 1166311 := bstep (se 1 (by rfl) ⟨874733, by rfl⟩ : syracuseStep 1166311 = 1749467) B1749467
theorem B4975631 : Blo 1164640 4975631 := bstep (se 1 (by rfl) ⟨3731723, by rfl⟩ : syracuseStep 4975631 = 7463447) B7463447
theorem B4484285 : Blo 1164640 4484285 := bstep (se 3 (by rfl) ⟨840803, by rfl⟩ : syracuseStep 4484285 = 1681607) B1681607
theorem B24235211 : Blo 1164640 24235211 := bstep (se 1 (by rfl) ⟨18176408, by rfl⟩ : syracuseStep 24235211 = 36352817) B36352817
theorem B1748201 : Blo 1164640 1748201 := bstep (se 2 (by rfl) ⟨655575, by rfl⟩ : syracuseStep 1748201 = 1311151) B1311151
theorem B1748255 : Blo 1164640 1748255 := bstep (se 1 (by rfl) ⟨1311191, by rfl⟩ : syracuseStep 1748255 = 2622383) B2622383
theorem B3935519 : Blo 1164640 3935519 := bstep (se 1 (by rfl) ⟨2951639, by rfl⟩ : syracuseStep 3935519 = 5903279) B5903279
theorem B51088765 : Blo 1164640 51088765 := bstep (se 3 (by rfl) ⟨9579143, by rfl⟩ : syracuseStep 51088765 = 19158287) B19158287
theorem B1748423 : Blo 1164640 1748423 := bstep (se 1 (by rfl) ⟨1311317, by rfl⟩ : syracuseStep 1748423 = 2622635) B2622635
theorem B12775085 : Blo 1164640 12775085 := bstep (se 3 (by rfl) ⟨2395328, by rfl⟩ : syracuseStep 12775085 = 4790657) B4790657
theorem B1748777 : Blo 1164640 1748777 := bstep (se 2 (by rfl) ⟨655791, by rfl⟩ : syracuseStep 1748777 = 1311583) B1311583
theorem B19910447 : Blo 1164640 19910447 := bstep (se 1 (by rfl) ⟨14932835, by rfl⟩ : syracuseStep 19910447 = 29865671) B29865671
theorem B1748783 : Blo 1164640 1748783 := bstep (se 1 (by rfl) ⟨1311587, by rfl⟩ : syracuseStep 1748783 = 2623175) B2623175
theorem B4427567 : Blo 1164640 4427567 := bstep (se 1 (by rfl) ⟨3320675, by rfl⟩ : syracuseStep 4427567 = 6641351) B6641351
theorem B4427581 : Blo 1164640 4427581 := bstep (se 3 (by rfl) ⟨830171, by rfl⟩ : syracuseStep 4427581 = 1660343) B1660343
theorem B96964487 : Blo 1164640 96964487 := bstep (se 1 (by rfl) ⟨72723365, by rfl⟩ : syracuseStep 96964487 = 145446731) B145446731
theorem B2101199 : Blo 1164640 2101199 := bstep (se 1 (by rfl) ⟨1575899, by rfl⟩ : syracuseStep 2101199 = 3151799) B3151799
theorem B6639641 : Blo 1164640 6639641 := bstep (se 2 (by rfl) ⟨2489865, by rfl⟩ : syracuseStep 6639641 = 4979731) B4979731
theorem B1749257 : Blo 1164640 1749257 := bstep (se 2 (by rfl) ⟨655971, by rfl⟩ : syracuseStep 1749257 = 1311943) B1311943
theorem B1749359 : Blo 1164640 1749359 := bstep (se 1 (by rfl) ⟨1312019, by rfl⟩ : syracuseStep 1749359 = 2624039) B2624039
theorem B5902793 : Blo 1164640 5902793 := bstep (se 2 (by rfl) ⟨2213547, by rfl⟩ : syracuseStep 5902793 = 4427095) B4427095
theorem B5313043 : Blo 1164640 5313043 := bstep (se 1 (by rfl) ⟨3984782, by rfl⟩ : syracuseStep 5313043 = 7969565) B7969565
theorem B1749575 : Blo 1164640 1749575 := bstep (se 1 (by rfl) ⟨1312181, by rfl⟩ : syracuseStep 1749575 = 2624363) B2624363
theorem B34075541 : Blo 1164640 34075541 := bstep (se 6 (by rfl) ⟨798645, by rfl⟩ : syracuseStep 34075541 = 1597291) B1597291
theorem B5600353 : Blo 1164640 5600353 := bstep (se 2 (by rfl) ⟨2100132, by rfl⟩ : syracuseStep 5600353 = 4200265) B4200265
theorem B2487439 : Blo 1164640 2487439 := bstep (se 1 (by rfl) ⟨1865579, by rfl⟩ : syracuseStep 2487439 = 3731159) B3731159
theorem B5903603 : Blo 1164640 5903603 := bstep (se 1 (by rfl) ⟨4427702, by rfl⟩ : syracuseStep 5903603 = 8855405) B8855405
theorem B4978007 : Blo 1164640 4978007 := bstep (se 1 (by rfl) ⟨3733505, by rfl⟩ : syracuseStep 4978007 = 7467011) B7467011
theorem B8975711 : Blo 1164640 8975711 := bstep (se 1 (by rfl) ⟨6731783, by rfl⟩ : syracuseStep 8975711 = 13463567) B13463567
theorem B22394333 : Blo 1164640 22394333 := bstep (se 3 (by rfl) ⟨4198937, by rfl⟩ : syracuseStep 22394333 = 8397875) B8397875
theorem B9959051 : Blo 1164640 9959051 := bstep (se 1 (by rfl) ⟨7469288, by rfl⟩ : syracuseStep 9959051 = 14938577) B14938577
theorem B5601545 : Blo 1164640 5601545 := bstep (se 2 (by rfl) ⟨2100579, by rfl⟩ : syracuseStep 5601545 = 4201159) B4201159
theorem B7469495 : Blo 1164640 7469495 := bstep (se 1 (by rfl) ⟨5602121, by rfl⟩ : syracuseStep 7469495 = 11204243) B11204243
theorem B1866311 : Blo 1164640 1866311 := bstep (se 1 (by rfl) ⟨1399733, by rfl⟩ : syracuseStep 1866311 = 2799467) B2799467
theorem B6642283 : Blo 1164640 6642283 := bstep (se 1 (by rfl) ⟨4981712, by rfl⟩ : syracuseStep 6642283 = 9963425) B9963425
theorem B4979389 : Blo 1164640 4979389 := bstep (se 3 (by rfl) ⟨933635, by rfl⟩ : syracuseStep 4979389 = 1867271) B1867271
theorem B3316859 : Blo 1164640 3316859 := bstep (se 1 (by rfl) ⟨2487644, by rfl⟩ : syracuseStep 3316859 = 4975289) B4975289
theorem B2694377 : Blo 1164640 2694377 := bstep (se 2 (by rfl) ⟨1010391, by rfl⟩ : syracuseStep 2694377 = 2020783) B2020783
theorem B2948339 : Blo 1164640 2948339 := bstep (se 1 (by rfl) ⟨2211254, by rfl⟩ : syracuseStep 2948339 = 4422509) B4422509
theorem B1965343 : Blo 1164640 1965343 := bstep (se 1 (by rfl) ⟨1474007, by rfl⟩ : syracuseStep 1965343 = 2948015) B2948015
theorem B29891915 : Blo 1164640 29891915 := bstep (se 1 (by rfl) ⟨22418936, by rfl⟩ : syracuseStep 29891915 = 44837873) B44837873
theorem B2211209 : Blo 1164640 2211209 := bstep (se 2 (by rfl) ⟨829203, by rfl⟩ : syracuseStep 2211209 = 1658407) B1658407
theorem B5897609 : Blo 1164640 5897609 := bstep (se 2 (by rfl) ⟨2211603, by rfl⟩ : syracuseStep 5897609 = 4423207) B4423207
theorem B2620871 : Blo 1164640 2620871 := bstep (se 1 (by rfl) ⟨1965653, by rfl⟩ : syracuseStep 2620871 = 3931307) B3931307
theorem B22388183 : Blo 1164640 22388183 := bstep (se 1 (by rfl) ⟨16791137, by rfl⟩ : syracuseStep 22388183 = 33582275) B33582275
theorem B2489849 : Blo 1164640 2489849 := bstep (se 2 (by rfl) ⟨933693, by rfl⟩ : syracuseStep 2489849 = 1867387) B1867387
theorem B6823507 : Blo 1164640 6823507 := bstep (se 1 (by rfl) ⟨5117630, by rfl⟩ : syracuseStep 6823507 = 10235261) B10235261
theorem B23027287 : Blo 1164640 23027287 := bstep (se 1 (by rfl) ⟨17270465, by rfl⟩ : syracuseStep 23027287 = 34540931) B34540931
theorem B1965755 : Blo 1164640 1965755 := bstep (se 1 (by rfl) ⟨1474316, by rfl⟩ : syracuseStep 1965755 = 2948633) B2948633
theorem B2948795 : Blo 1164640 2948795 := bstep (se 1 (by rfl) ⟨2211596, by rfl⟩ : syracuseStep 2948795 = 4423193) B4423193
theorem B1310431 : Blo 1164640 1310431 := bstep (se 1 (by rfl) ⟨982823, by rfl⟩ : syracuseStep 1310431 = 1965647) B1965647
theorem B6635267 : Blo 1164640 6635267 := bstep (se 1 (by rfl) ⟨4976450, by rfl⟩ : syracuseStep 6635267 = 9952901) B9952901
theorem B2621231 : Blo 1164640 2621231 := bstep (se 1 (by rfl) ⟨1965923, by rfl⟩ : syracuseStep 2621231 = 3931847) B3931847
theorem B4423481 : Blo 1164640 4423481 := bstep (se 2 (by rfl) ⟨1658805, by rfl⟩ : syracuseStep 4423481 = 3317611) B3317611
theorem B15138649 : Blo 1164640 15138649 := bstep (se 2 (by rfl) ⟨5676993, by rfl⟩ : syracuseStep 15138649 = 11353987) B11353987
theorem B2801513 : Blo 1164640 2801513 := bstep (se 2 (by rfl) ⟨1050567, by rfl⟩ : syracuseStep 2801513 = 2101135) B2101135
theorem B3932441 : Blo 1164640 3932441 := bstep (se 2 (by rfl) ⟨1474665, by rfl⟩ : syracuseStep 3932441 = 2949331) B2949331
theorem B2949473 : Blo 1164640 2949473 := bstep (se 2 (by rfl) ⟨1106052, by rfl⟩ : syracuseStep 2949473 = 2212105) B2212105
theorem B6635951 : Blo 1164640 6635951 := bstep (se 1 (by rfl) ⟨4976963, by rfl⟩ : syracuseStep 6635951 = 9953927) B9953927
theorem B3932603 : Blo 1164640 3932603 := bstep (se 1 (by rfl) ⟨2949452, by rfl⟩ : syracuseStep 3932603 = 5898905) B5898905
theorem B1966585 : Blo 1164640 1966585 := bstep (se 2 (by rfl) ⟨737469, by rfl⟩ : syracuseStep 1966585 = 1474939) B1474939
theorem B64627229 : Blo 1164640 64627229 := bstep (se 3 (by rfl) ⟨12117605, by rfl⟩ : syracuseStep 64627229 = 24235211) B24235211
theorem B22717027 : Blo 1164640 22717027 := bstep (se 1 (by rfl) ⟨17037770, by rfl⟩ : syracuseStep 22717027 = 34075541) B34075541
theorem B1966855 : Blo 1164640 1966855 := bstep (se 1 (by rfl) ⟨1475141, by rfl⟩ : syracuseStep 1966855 = 2950283) B2950283
theorem B1966889 : Blo 1164640 1966889 := bstep (se 2 (by rfl) ⟨737583, by rfl⟩ : syracuseStep 1966889 = 1475167) B1475167
theorem B6390575 : Blo 1164640 6390575 := bstep (se 1 (by rfl) ⟨4792931, by rfl⟩ : syracuseStep 6390575 = 9585863) B9585863
theorem B8856377 : Blo 1164640 8856377 := bstep (se 2 (by rfl) ⟨3321141, by rfl⟩ : syracuseStep 8856377 = 6642283) B6642283
theorem B3318671 : Blo 1164640 3318671 := bstep (se 1 (by rfl) ⟨2489003, by rfl⟩ : syracuseStep 3318671 = 4978007) B4978007
theorem B1311655 : Blo 1164640 1311655 := bstep (se 1 (by rfl) ⟨983741, by rfl⟩ : syracuseStep 1311655 = 1967483) B1967483
theorem B2622419 : Blo 1164640 2622419 := bstep (se 1 (by rfl) ⟨1966814, by rfl⟩ : syracuseStep 2622419 = 3933629) B3933629
theorem B1967159 : Blo 1164640 1967159 := bstep (se 1 (by rfl) ⟨1475369, by rfl⟩ : syracuseStep 1967159 = 2950739) B2950739
theorem B1475759 : Blo 1164640 1475759 := bstep (se 1 (by rfl) ⟨1106819, by rfl⟩ : syracuseStep 1475759 = 2213639) B2213639
theorem B2622671 : Blo 1164640 2622671 := bstep (se 1 (by rfl) ⟨1967003, by rfl⟩ : syracuseStep 2622671 = 3934007) B3934007
theorem B1164699 : Blo 1164640 1164699 := bstep (se 1 (by rfl) ⟨873524, by rfl⟩ : syracuseStep 1164699 = 1747049) B1747049
theorem B2622995 : Blo 1164640 2622995 := bstep (se 1 (by rfl) ⟨1967246, by rfl⟩ : syracuseStep 2622995 = 3934493) B3934493
theorem B5604889 : Blo 1164640 5604889 := bstep (se 2 (by rfl) ⟨2101833, by rfl⟩ : syracuseStep 5604889 = 4203667) B4203667
theorem B3933791 : Blo 1164640 3933791 := bstep (se 1 (by rfl) ⟨2950343, by rfl⟩ : syracuseStep 3933791 = 5900687) B5900687
theorem B1164911 : Blo 1164640 1164911 := bstep (se 1 (by rfl) ⟨873683, by rfl⟩ : syracuseStep 1164911 = 1747367) B1747367
theorem B1164967 : Blo 1164640 1164967 := bstep (se 1 (by rfl) ⟨873725, by rfl⟩ : syracuseStep 1164967 = 1747451) B1747451
theorem B1165051 : Blo 1164640 1165051 := bstep (se 1 (by rfl) ⟨873788, by rfl⟩ : syracuseStep 1165051 = 1747577) B1747577
theorem B1165087 : Blo 1164640 1165087 := bstep (se 1 (by rfl) ⟨873815, by rfl⟩ : syracuseStep 1165087 = 1747631) B1747631
theorem B7669559 : Blo 1164640 7669559 := bstep (se 1 (by rfl) ⟨5752169, by rfl⟩ : syracuseStep 7669559 = 11504339) B11504339
theorem B1165119 : Blo 1164640 1165119 := bstep (se 1 (by rfl) ⟨873839, by rfl⟩ : syracuseStep 1165119 = 1747679) B1747679
theorem B1967935 : Blo 1164640 1967935 := bstep (se 1 (by rfl) ⟨1475951, by rfl⟩ : syracuseStep 1967935 = 2951903) B2951903
theorem B68118353 : Blo 1164640 68118353 := bstep (se 2 (by rfl) ⟨25544382, by rfl⟩ : syracuseStep 68118353 = 51088765) B51088765
theorem B161580905 : Blo 1164640 161580905 := bstep (se 2 (by rfl) ⟨60592839, by rfl⟩ : syracuseStep 161580905 = 121185679) B121185679
theorem B1165295 : Blo 1164640 1165295 := bstep (se 1 (by rfl) ⟨873971, by rfl⟩ : syracuseStep 1165295 = 1747943) B1747943
theorem B7473161 : Blo 1164640 7473161 := bstep (se 2 (by rfl) ⟨2802435, by rfl⟩ : syracuseStep 7473161 = 5604871) B5604871
theorem B1165467 : Blo 1164640 1165467 := bstep (se 1 (by rfl) ⟨874100, by rfl⟩ : syracuseStep 1165467 = 1748201) B1748201
theorem B1796251 : Blo 1164640 1796251 := bstep (se 1 (by rfl) ⟨1347188, by rfl⟩ : syracuseStep 1796251 = 2694377) B2694377
theorem B1165503 : Blo 1164640 1165503 := bstep (se 1 (by rfl) ⟨874127, by rfl⟩ : syracuseStep 1165503 = 1748255) B1748255
theorem B2623679 : Blo 1164640 2623679 := bstep (se 1 (by rfl) ⟨1967759, by rfl⟩ : syracuseStep 2623679 = 3935519) B3935519
theorem B2951417 : Blo 1164640 2951417 := bstep (se 2 (by rfl) ⟨1106781, by rfl⟩ : syracuseStep 2951417 = 2213563) B2213563
theorem B1747241 : Blo 1164640 1747241 := bstep (se 2 (by rfl) ⟨655215, by rfl⟩ : syracuseStep 1747241 = 1310431) B1310431
theorem B1747247 : Blo 1164640 1747247 := bstep (se 1 (by rfl) ⟨1310435, by rfl⟩ : syracuseStep 1747247 = 2620871) B2620871
theorem B1165615 : Blo 1164640 1165615 := bstep (se 1 (by rfl) ⟨874211, by rfl⟩ : syracuseStep 1165615 = 1748423) B1748423
theorem B1165851 : Blo 1164640 1165851 := bstep (se 1 (by rfl) ⟨874388, by rfl⟩ : syracuseStep 1165851 = 1748777) B1748777
theorem B1747487 : Blo 1164640 1747487 := bstep (se 1 (by rfl) ⟨1310615, by rfl⟩ : syracuseStep 1747487 = 2621231) B2621231
theorem B13273631 : Blo 1164640 13273631 := bstep (se 1 (by rfl) ⟨9955223, by rfl⟩ : syracuseStep 13273631 = 19910447) B19910447
theorem B1165855 : Blo 1164640 1165855 := bstep (se 1 (by rfl) ⟨874391, by rfl⟩ : syracuseStep 1165855 = 1748783) B1748783
theorem B2951711 : Blo 1164640 2951711 := bstep (se 1 (by rfl) ⟨2213783, by rfl⟩ : syracuseStep 2951711 = 4427567) B4427567
theorem B4426427 : Blo 1164640 4426427 := bstep (se 1 (by rfl) ⟨3319820, by rfl⟩ : syracuseStep 4426427 = 6639641) B6639641
theorem B1166171 : Blo 1164640 1166171 := bstep (se 1 (by rfl) ⟨874628, by rfl⟩ : syracuseStep 1166171 = 1749257) B1749257
theorem B1747871 : Blo 1164640 1747871 := bstep (se 1 (by rfl) ⟨1310903, by rfl⟩ : syracuseStep 1747871 = 2621807) B2621807
theorem B1166239 : Blo 1164640 1166239 := bstep (se 1 (by rfl) ⟨874679, by rfl⟩ : syracuseStep 1166239 = 1749359) B1749359
theorem B1747919 : Blo 1164640 1747919 := bstep (se 1 (by rfl) ⟨1310939, by rfl⟩ : syracuseStep 1747919 = 2621879) B2621879
theorem B3935195 : Blo 1164640 3935195 := bstep (se 1 (by rfl) ⟨2951396, by rfl⟩ : syracuseStep 3935195 = 5902793) B5902793
theorem B1748009 : Blo 1164640 1748009 := bstep (se 2 (by rfl) ⟨655503, by rfl⟩ : syracuseStep 1748009 = 1311007) B1311007
theorem B1748015 : Blo 1164640 1748015 := bstep (se 1 (by rfl) ⟨1311011, by rfl⟩ : syracuseStep 1748015 = 2622023) B2622023
theorem B1166383 : Blo 1164640 1166383 := bstep (se 1 (by rfl) ⟨874787, by rfl⟩ : syracuseStep 1166383 = 1749575) B1749575
theorem B22391873 : Blo 1164640 22391873 := bstep (se 2 (by rfl) ⟨8396952, by rfl⟩ : syracuseStep 22391873 = 16793905) B16793905
theorem B1748039 : Blo 1164640 1748039 := bstep (se 1 (by rfl) ⟨1311029, by rfl⟩ : syracuseStep 1748039 = 2622059) B2622059
theorem B3935465 : Blo 1164640 3935465 := bstep (se 2 (by rfl) ⟨1475799, by rfl⟩ : syracuseStep 3935465 = 2951599) B2951599
theorem B1748303 : Blo 1164640 1748303 := bstep (se 1 (by rfl) ⟨1311227, by rfl⟩ : syracuseStep 1748303 = 2622455) B2622455
theorem B13266341 : Blo 1164640 13266341 := bstep (se 4 (by rfl) ⟨1243719, by rfl⟩ : syracuseStep 13266341 = 2487439) B2487439
theorem B1748393 : Blo 1164640 1748393 := bstep (se 2 (by rfl) ⟨655647, by rfl⟩ : syracuseStep 1748393 = 1311295) B1311295
theorem B3935735 : Blo 1164640 3935735 := bstep (se 1 (by rfl) ⟨2951801, by rfl⟩ : syracuseStep 3935735 = 5903603) B5903603
theorem B1748543 : Blo 1164640 1748543 := bstep (se 1 (by rfl) ⟨1311407, by rfl⟩ : syracuseStep 1748543 = 2622815) B2622815
theorem B5983807 : Blo 1164640 5983807 := bstep (se 1 (by rfl) ⟨4487855, by rfl⟩ : syracuseStep 5983807 = 8975711) B8975711
theorem B6639185 : Blo 1164640 6639185 := bstep (se 2 (by rfl) ⟨2489694, by rfl⟩ : syracuseStep 6639185 = 4979389) B4979389
theorem B14929555 : Blo 1164640 14929555 := bstep (se 1 (by rfl) ⟨11197166, by rfl⟩ : syracuseStep 14929555 = 22394333) B22394333
theorem B6639367 : Blo 1164640 6639367 := bstep (se 1 (by rfl) ⟨4979525, by rfl⟩ : syracuseStep 6639367 = 9959051) B9959051
theorem B1748807 : Blo 1164640 1748807 := bstep (se 1 (by rfl) ⟨1311605, by rfl⟩ : syracuseStep 1748807 = 2623211) B2623211
theorem B9957275 : Blo 1164640 9957275 := bstep (se 1 (by rfl) ⟨7467956, by rfl⟩ : syracuseStep 9957275 = 14935913) B14935913
theorem B1748891 : Blo 1164640 1748891 := bstep (se 1 (by rfl) ⟨1311668, by rfl⟩ : syracuseStep 1748891 = 2623337) B2623337
theorem B13275089 : Blo 1164640 13275089 := bstep (se 2 (by rfl) ⟨4978158, by rfl⟩ : syracuseStep 13275089 = 9956317) B9956317
theorem B5599199 : Blo 1164640 5599199 := bstep (se 1 (by rfl) ⟨4199399, by rfl⟩ : syracuseStep 5599199 = 8398799) B8398799
theorem B7467137 : Blo 1164640 7467137 := bstep (se 2 (by rfl) ⟨2800176, by rfl⟩ : syracuseStep 7467137 = 5600353) B5600353
theorem B19919195 : Blo 1164640 19919195 := bstep (se 1 (by rfl) ⟨14939396, by rfl⟩ : syracuseStep 19919195 = 29878793) B29878793
theorem B1749455 : Blo 1164640 1749455 := bstep (se 1 (by rfl) ⟨1312091, by rfl⟩ : syracuseStep 1749455 = 2624183) B2624183
theorem B1749497 : Blo 1164640 1749497 := bstep (se 2 (by rfl) ⟨656061, by rfl⟩ : syracuseStep 1749497 = 1312123) B1312123
theorem B6304337 : Blo 1164640 6304337 := bstep (se 2 (by rfl) ⟨2364126, by rfl⟩ : syracuseStep 6304337 = 4728253) B4728253
theorem B1749599 : Blo 1164640 1749599 := bstep (se 1 (by rfl) ⟨1312199, by rfl⟩ : syracuseStep 1749599 = 2624399) B2624399
theorem B9098009 : Blo 1164640 9098009 := bstep (se 2 (by rfl) ⟨3411753, by rfl⟩ : syracuseStep 9098009 = 6823507) B6823507
theorem B19927943 : Blo 1164640 19927943 := bstep (se 1 (by rfl) ⟨14945957, by rfl⟩ : syracuseStep 19927943 = 29891915) B29891915
theorem B1659899 : Blo 1164640 1659899 := bstep (se 1 (by rfl) ⟨1244924, by rfl⟩ : syracuseStep 1659899 = 2489849) B2489849
theorem B5903441 : Blo 1164640 5903441 := bstep (se 2 (by rfl) ⟨2213790, by rfl⟩ : syracuseStep 5903441 = 4427581) B4427581
theorem B8516723 : Blo 1164640 8516723 := bstep (se 1 (by rfl) ⟨6387542, by rfl⟩ : syracuseStep 8516723 = 12775085) B12775085
theorem B3986945 : Blo 1164640 3986945 := bstep (se 2 (by rfl) ⟨1495104, by rfl⟩ : syracuseStep 3986945 = 2990209) B2990209
theorem B1660537 : Blo 1164640 1660537 := bstep (se 2 (by rfl) ⟨622701, by rfl⟩ : syracuseStep 1660537 = 1245403) B1245403
theorem B6633353 : Blo 1164640 6633353 := bstep (se 2 (by rfl) ⟨2487507, by rfl⟩ : syracuseStep 6633353 = 4975015) B4975015
theorem B7084057 : Blo 1164640 7084057 := bstep (se 2 (by rfl) ⟨2656521, by rfl⟩ : syracuseStep 7084057 = 5313043) B5313043
theorem B4724831 : Blo 1164640 4724831 := bstep (se 1 (by rfl) ⟨3543623, by rfl⟩ : syracuseStep 4724831 = 7087247) B7087247
theorem B58235435 : Blo 1164640 58235435 := bstep (se 1 (by rfl) ⟨43676576, by rfl⟩ : syracuseStep 58235435 = 87353153) B87353153
theorem B3734363 : Blo 1164640 3734363 := bstep (se 1 (by rfl) ⟨2800772, by rfl⟩ : syracuseStep 3734363 = 5601545) B5601545
theorem B6642557 : Blo 1164640 6642557 := bstep (se 3 (by rfl) ⟨1245479, by rfl⟩ : syracuseStep 6642557 = 2490959) B2490959
theorem B4979663 : Blo 1164640 4979663 := bstep (se 1 (by rfl) ⟨3734747, by rfl⟩ : syracuseStep 4979663 = 7469495) B7469495
theorem B2620457 : Blo 1164640 2620457 := bstep (se 2 (by rfl) ⟨982671, by rfl⟩ : syracuseStep 2620457 = 1965343) B1965343
theorem B1244207 : Blo 1164640 1244207 := bstep (se 1 (by rfl) ⟨933155, by rfl⟩ : syracuseStep 1244207 = 1866311) B1866311
theorem B80739461 : Blo 1164640 80739461 := bstep (se 4 (by rfl) ⟨7569324, by rfl⟩ : syracuseStep 80739461 = 15138649) B15138649
theorem B3317087 : Blo 1164640 3317087 := bstep (se 1 (by rfl) ⟨2487815, by rfl⟩ : syracuseStep 3317087 = 4975631) B4975631
theorem B2211239 : Blo 1164640 2211239 := bstep (se 1 (by rfl) ⟨1658429, by rfl⟩ : syracuseStep 2211239 = 3316859) B3316859
theorem B30703049 : Blo 1164640 30703049 := bstep (se 2 (by rfl) ⟨11513643, by rfl⟩ : syracuseStep 30703049 = 23027287) B23027287
theorem B2989523 : Blo 1164640 2989523 := bstep (se 1 (by rfl) ⟨2242142, by rfl⟩ : syracuseStep 2989523 = 4484285) B4484285
theorem B1965559 : Blo 1164640 1965559 := bstep (se 1 (by rfl) ⟨1474169, by rfl⟩ : syracuseStep 1965559 = 2948339) B2948339
theorem B1474139 : Blo 1164640 1474139 := bstep (se 1 (by rfl) ⟨1105604, by rfl⟩ : syracuseStep 1474139 = 2211209) B2211209
theorem B3931739 : Blo 1164640 3931739 := bstep (se 1 (by rfl) ⟨2948804, by rfl⟩ : syracuseStep 3931739 = 5897609) B5897609
theorem B7470701 : Blo 1164640 7470701 := bstep (se 3 (by rfl) ⟨1400756, by rfl⟩ : syracuseStep 7470701 = 2801513) B2801513
theorem B14925455 : Blo 1164640 14925455 := bstep (se 1 (by rfl) ⟨11194091, by rfl⟩ : syracuseStep 14925455 = 22388183) B22388183
theorem B1310503 : Blo 1164640 1310503 := bstep (se 1 (by rfl) ⟨982877, by rfl⟩ : syracuseStep 1310503 = 1965755) B1965755
theorem B1965863 : Blo 1164640 1965863 := bstep (se 1 (by rfl) ⟨1474397, by rfl⟩ : syracuseStep 1965863 = 2948795) B2948795
theorem B4423511 : Blo 1164640 4423511 := bstep (se 1 (by rfl) ⟨3317633, by rfl⟩ : syracuseStep 4423511 = 6635267) B6635267
theorem B2948987 : Blo 1164640 2948987 := bstep (se 1 (by rfl) ⟨2211740, by rfl⟩ : syracuseStep 2948987 = 4423481) B4423481
theorem B5603197 : Blo 1164640 5603197 := bstep (se 3 (by rfl) ⟨1050599, by rfl⟩ : syracuseStep 5603197 = 2101199) B2101199
theorem B64642991 : Blo 1164640 64642991 := bstep (se 1 (by rfl) ⟨48482243, by rfl⟩ : syracuseStep 64642991 = 96964487) B96964487
theorem B9445409 : Blo 1164640 9445409 := bstep (se 2 (by rfl) ⟨3542028, by rfl⟩ : syracuseStep 9445409 = 7084057) B7084057
theorem B3317885 : Blo 1164640 3317885 := bstep (se 3 (by rfl) ⟨622103, by rfl⟩ : syracuseStep 3317885 = 1244207) B1244207
theorem B2621627 : Blo 1164640 2621627 := bstep (se 1 (by rfl) ⟨1966220, by rfl⟩ : syracuseStep 2621627 = 3932441) B3932441
theorem B13279463 : Blo 1164640 13279463 := bstep (se 1 (by rfl) ⟨9959597, by rfl⟩ : syracuseStep 13279463 = 19919195) B19919195
theorem B1966315 : Blo 1164640 1966315 := bstep (se 1 (by rfl) ⟨1474736, by rfl⟩ : syracuseStep 1966315 = 2949473) B2949473
theorem B12599549 : Blo 1164640 12599549 := bstep (se 3 (by rfl) ⟨2362415, by rfl⟩ : syracuseStep 12599549 = 4724831) B4724831
theorem B4423967 : Blo 1164640 4423967 := bstep (se 1 (by rfl) ⟨3317975, by rfl⟩ : syracuseStep 4423967 = 6635951) B6635951
theorem B2621735 : Blo 1164640 2621735 := bstep (se 1 (by rfl) ⟨1966301, by rfl⟩ : syracuseStep 2621735 = 3932603) B3932603
theorem B4202891 : Blo 1164640 4202891 := bstep (se 1 (by rfl) ⟨3152168, by rfl⟩ : syracuseStep 4202891 = 6304337) B6304337
theorem B1311259 : Blo 1164640 1311259 := bstep (se 1 (by rfl) ⟨983444, by rfl⟩ : syracuseStep 1311259 = 1966889) B1966889
theorem B4260383 : Blo 1164640 4260383 := bstep (se 1 (by rfl) ⟨3195287, by rfl⟩ : syracuseStep 4260383 = 6390575) B6390575
theorem B2212447 : Blo 1164640 2212447 := bstep (se 1 (by rfl) ⟨1659335, by rfl⟩ : syracuseStep 2212447 = 3318671) B3318671
theorem B2622113 : Blo 1164640 2622113 := bstep (se 2 (by rfl) ⟨983292, by rfl⟩ : syracuseStep 2622113 = 1966585) B1966585
theorem B1311439 : Blo 1164640 1311439 := bstep (se 1 (by rfl) ⟨983579, by rfl⟩ : syracuseStep 1311439 = 1967159) B1967159
theorem B2622473 : Blo 1164640 2622473 := bstep (se 2 (by rfl) ⟨983427, by rfl⟩ : syracuseStep 2622473 = 1966855) B1966855
theorem B2622527 : Blo 1164640 2622527 := bstep (se 1 (by rfl) ⟨1966895, by rfl⟩ : syracuseStep 2622527 = 3933791) B3933791
theorem B5113039 : Blo 1164640 5113039 := bstep (se 1 (by rfl) ⟨3834779, by rfl⟩ : syracuseStep 5113039 = 7669559) B7669559
theorem B4982107 : Blo 1164640 4982107 := bstep (se 1 (by rfl) ⟨3736580, by rfl⟩ : syracuseStep 4982107 = 7473161) B7473161
theorem B1967611 : Blo 1164640 1967611 := bstep (se 1 (by rfl) ⟨1475708, by rfl⟩ : syracuseStep 1967611 = 2951417) B2951417
theorem B1164827 : Blo 1164640 1164827 := bstep (se 1 (by rfl) ⟨873620, by rfl⟩ : syracuseStep 1164827 = 1747241) B1747241
theorem B1164831 : Blo 1164640 1164831 := bstep (se 1 (by rfl) ⟨873623, by rfl⟩ : syracuseStep 1164831 = 1747247) B1747247
theorem B1164991 : Blo 1164640 1164991 := bstep (se 1 (by rfl) ⟨873743, by rfl⟩ : syracuseStep 1164991 = 1747487) B1747487
theorem B8849087 : Blo 1164640 8849087 := bstep (se 1 (by rfl) ⟨6636815, by rfl⟩ : syracuseStep 8849087 = 13273631) B13273631
theorem B1967807 : Blo 1164640 1967807 := bstep (se 1 (by rfl) ⟨1475855, by rfl⟩ : syracuseStep 1967807 = 2951711) B2951711
theorem B38823623 : Blo 1164640 38823623 := bstep (se 1 (by rfl) ⟨29117717, by rfl⟩ : syracuseStep 38823623 = 58235435) B58235435
theorem B2950951 : Blo 1164640 2950951 := bstep (se 1 (by rfl) ⟨2213213, by rfl⟩ : syracuseStep 2950951 = 4426427) B4426427
theorem B1165247 : Blo 1164640 1165247 := bstep (se 1 (by rfl) ⟨873935, by rfl⟩ : syracuseStep 1165247 = 1747871) B1747871
theorem B1165279 : Blo 1164640 1165279 := bstep (se 1 (by rfl) ⟨873959, by rfl⟩ : syracuseStep 1165279 = 1747919) B1747919
theorem B3319775 : Blo 1164640 3319775 := bstep (se 1 (by rfl) ⟨2489831, by rfl⟩ : syracuseStep 3319775 = 4979663) B4979663
theorem B2623463 : Blo 1164640 2623463 := bstep (se 1 (by rfl) ⟨1967597, by rfl⟩ : syracuseStep 2623463 = 3935195) B3935195
theorem B1746971 : Blo 1164640 1746971 := bstep (se 1 (by rfl) ⟨1310228, by rfl⟩ : syracuseStep 1746971 = 2620457) B2620457
theorem B1165339 : Blo 1164640 1165339 := bstep (se 1 (by rfl) ⟨874004, by rfl⟩ : syracuseStep 1165339 = 1748009) B1748009
theorem B1165343 : Blo 1164640 1165343 := bstep (se 1 (by rfl) ⟨874007, by rfl⟩ : syracuseStep 1165343 = 1748015) B1748015
theorem B7473185 : Blo 1164640 7473185 := bstep (se 2 (by rfl) ⟨2802444, by rfl⟩ : syracuseStep 7473185 = 5604889) B5604889
theorem B14927915 : Blo 1164640 14927915 := bstep (se 1 (by rfl) ⟨11195936, by rfl⟩ : syracuseStep 14927915 = 22391873) B22391873
theorem B1165359 : Blo 1164640 1165359 := bstep (se 1 (by rfl) ⟨874019, by rfl⟩ : syracuseStep 1165359 = 1748039) B1748039
theorem B2623643 : Blo 1164640 2623643 := bstep (se 1 (by rfl) ⟨1967732, by rfl⟩ : syracuseStep 2623643 = 3935465) B3935465
theorem B2214049 : Blo 1164640 2214049 := bstep (se 2 (by rfl) ⟨830268, by rfl⟩ : syracuseStep 2214049 = 1660537) B1660537
theorem B1165535 : Blo 1164640 1165535 := bstep (se 1 (by rfl) ⟨874151, by rfl⟩ : syracuseStep 1165535 = 1748303) B1748303
theorem B1165595 : Blo 1164640 1165595 := bstep (se 1 (by rfl) ⟨874196, by rfl⟩ : syracuseStep 1165595 = 1748393) B1748393
theorem B1993015 : Blo 1164640 1993015 := bstep (se 1 (by rfl) ⟨1494761, by rfl⟩ : syracuseStep 1993015 = 2989523) B2989523
theorem B2623823 : Blo 1164640 2623823 := bstep (se 1 (by rfl) ⟨1967867, by rfl⟩ : syracuseStep 2623823 = 3935735) B3935735
theorem B1165695 : Blo 1164640 1165695 := bstep (se 1 (by rfl) ⟨874271, by rfl⟩ : syracuseStep 1165695 = 1748543) B1748543
theorem B1747337 : Blo 1164640 1747337 := bstep (se 2 (by rfl) ⟨655251, by rfl⟩ : syracuseStep 1747337 = 1310503) B1310503
theorem B4426123 : Blo 1164640 4426123 := bstep (se 1 (by rfl) ⟨3319592, by rfl⟩ : syracuseStep 4426123 = 6639185) B6639185
theorem B2623913 : Blo 1164640 2623913 := bstep (se 2 (by rfl) ⟨983967, by rfl⟩ : syracuseStep 2623913 = 1967935) B1967935
theorem B1165871 : Blo 1164640 1165871 := bstep (se 1 (by rfl) ⟨874403, by rfl⟩ : syracuseStep 1165871 = 1748807) B1748807
theorem B6638183 : Blo 1164640 6638183 := bstep (se 1 (by rfl) ⟨4978637, by rfl⟩ : syracuseStep 6638183 = 9957275) B9957275
theorem B1165927 : Blo 1164640 1165927 := bstep (se 1 (by rfl) ⟨874445, by rfl⟩ : syracuseStep 1165927 = 1748891) B1748891
theorem B8850059 : Blo 1164640 8850059 := bstep (se 1 (by rfl) ⟨6637544, by rfl⟩ : syracuseStep 8850059 = 13275089) B13275089
theorem B4426397 : Blo 1164640 4426397 := bstep (se 3 (by rfl) ⟨829949, by rfl⟩ : syracuseStep 4426397 = 1659899) B1659899
theorem B2395001 : Blo 1164640 2395001 := bstep (se 2 (by rfl) ⟨898125, by rfl⟩ : syracuseStep 2395001 = 1796251) B1796251
theorem B22711261 : Blo 1164640 22711261 := bstep (se 3 (by rfl) ⟨4258361, by rfl⟩ : syracuseStep 22711261 = 8516723) B8516723
theorem B1166303 : Blo 1164640 1166303 := bstep (se 1 (by rfl) ⟨874727, by rfl⟩ : syracuseStep 1166303 = 1749455) B1749455
theorem B1166331 : Blo 1164640 1166331 := bstep (se 1 (by rfl) ⟨874748, by rfl⟩ : syracuseStep 1166331 = 1749497) B1749497
theorem B215305229 : Blo 1164640 215305229 := bstep (se 3 (by rfl) ⟨40369730, by rfl⟩ : syracuseStep 215305229 = 80739461) B80739461
theorem B43084819 : Blo 1164640 43084819 := bstep (se 1 (by rfl) ⟨32313614, by rfl⟩ : syracuseStep 43084819 = 64627229) B64627229
theorem B1166399 : Blo 1164640 1166399 := bstep (se 1 (by rfl) ⟨874799, by rfl⟩ : syracuseStep 1166399 = 1749599) B1749599
theorem B3935357 : Blo 1164640 3935357 := bstep (se 3 (by rfl) ⟨737879, by rfl⟩ : syracuseStep 3935357 = 1475759) B1475759
theorem B6065339 : Blo 1164640 6065339 := bstep (se 1 (by rfl) ⟨4549004, by rfl⟩ : syracuseStep 6065339 = 9098009) B9098009
theorem B1748279 : Blo 1164640 1748279 := bstep (se 1 (by rfl) ⟨1311209, by rfl⟩ : syracuseStep 1748279 = 2622419) B2622419
theorem B3935627 : Blo 1164640 3935627 := bstep (se 1 (by rfl) ⟨2951720, by rfl⟩ : syracuseStep 3935627 = 5903441) B5903441
theorem B1748447 : Blo 1164640 1748447 := bstep (se 1 (by rfl) ⟨1311335, by rfl⟩ : syracuseStep 1748447 = 2622671) B2622671
theorem B2657963 : Blo 1164640 2657963 := bstep (se 1 (by rfl) ⟨1993472, by rfl⟩ : syracuseStep 2657963 = 3986945) B3986945
theorem B1748663 : Blo 1164640 1748663 := bstep (se 1 (by rfl) ⟨1311497, by rfl⟩ : syracuseStep 1748663 = 2622995) B2622995
theorem B1748873 : Blo 1164640 1748873 := bstep (se 2 (by rfl) ⟨655827, by rfl⟩ : syracuseStep 1748873 = 1311655) B1311655
theorem B45412235 : Blo 1164640 45412235 := bstep (se 1 (by rfl) ⟨34059176, by rfl⟩ : syracuseStep 45412235 = 68118353) B68118353
theorem B107720603 : Blo 1164640 107720603 := bstep (se 1 (by rfl) ⟨80790452, by rfl⟩ : syracuseStep 107720603 = 161580905) B161580905
theorem B1749119 : Blo 1164640 1749119 := bstep (se 1 (by rfl) ⟨1311839, by rfl⟩ : syracuseStep 1749119 = 2623679) B2623679
theorem B689525237 : Blo 1164640 689525237 := bstep (se 5 (by rfl) ⟨32321495, by rfl⟩ : syracuseStep 689525237 = 64642991) B64642991
theorem B4428371 : Blo 1164640 4428371 := bstep (se 1 (by rfl) ⟨3321278, by rfl⟩ : syracuseStep 4428371 = 6642557) B6642557
theorem B9958301 : Blo 1164640 9958301 := bstep (se 3 (by rfl) ⟨1867181, by rfl⟩ : syracuseStep 9958301 = 3734363) B3734363
theorem B8844227 : Blo 1164640 8844227 := bstep (se 1 (by rfl) ⟨6633170, by rfl⟩ : syracuseStep 8844227 = 13266341) B13266341
theorem B20468699 : Blo 1164640 20468699 := bstep (se 1 (by rfl) ⟨15351524, by rfl⟩ : syracuseStep 20468699 = 30703049) B30703049
theorem B8852489 : Blo 1164640 8852489 := bstep (se 2 (by rfl) ⟨3319683, by rfl⟩ : syracuseStep 8852489 = 6639367) B6639367
theorem B9950303 : Blo 1164640 9950303 := bstep (se 1 (by rfl) ⟨7462727, by rfl⟩ : syracuseStep 9950303 = 14925455) B14925455
theorem B3732799 : Blo 1164640 3732799 := bstep (se 1 (by rfl) ⟨2799599, by rfl⟩ : syracuseStep 3732799 = 5599199) B5599199
theorem B4978091 : Blo 1164640 4978091 := bstep (se 1 (by rfl) ⟨3733568, by rfl⟩ : syracuseStep 4978091 = 7467137) B7467137
theorem B121157477 : Blo 1164640 121157477 := bstep (se 4 (by rfl) ⟨11358513, by rfl⟩ : syracuseStep 121157477 = 22717027) B22717027
theorem B5904251 : Blo 1164640 5904251 := bstep (se 1 (by rfl) ⟨4428188, by rfl⟩ : syracuseStep 5904251 = 8856377) B8856377
theorem B13285295 : Blo 1164640 13285295 := bstep (se 1 (by rfl) ⟨9963971, by rfl⟩ : syracuseStep 13285295 = 19927943) B19927943
theorem B5896637 : Blo 1164640 5896637 := bstep (se 3 (by rfl) ⟨1105619, by rfl⟩ : syracuseStep 5896637 = 2211239) B2211239
theorem B4422235 : Blo 1164640 4422235 := bstep (se 1 (by rfl) ⟨3316676, by rfl⟩ : syracuseStep 4422235 = 6633353) B6633353
theorem B3931037 : Blo 1164640 3931037 := bstep (se 3 (by rfl) ⟨737069, by rfl⟩ : syracuseStep 3931037 = 1474139) B1474139
theorem B2620745 : Blo 1164640 2620745 := bstep (se 2 (by rfl) ⟨982779, by rfl⟩ : syracuseStep 2620745 = 1965559) B1965559
theorem B7978409 : Blo 1164640 7978409 := bstep (se 2 (by rfl) ⟨2991903, by rfl⟩ : syracuseStep 7978409 = 5983807) B5983807
theorem B19906073 : Blo 1164640 19906073 := bstep (se 2 (by rfl) ⟨7464777, by rfl⟩ : syracuseStep 19906073 = 14929555) B14929555
theorem B2211391 : Blo 1164640 2211391 := bstep (se 1 (by rfl) ⟨1658543, by rfl⟩ : syracuseStep 2211391 = 3317087) B3317087
theorem B2621159 : Blo 1164640 2621159 := bstep (se 1 (by rfl) ⟨1965869, by rfl⟩ : syracuseStep 2621159 = 3931739) B3931739
theorem B4980467 : Blo 1164640 4980467 := bstep (se 1 (by rfl) ⟨3735350, by rfl⟩ : syracuseStep 4980467 = 7470701) B7470701
theorem B7470929 : Blo 1164640 7470929 := bstep (se 2 (by rfl) ⟨2801598, by rfl⟩ : syracuseStep 7470929 = 5603197) B5603197
theorem B1310575 : Blo 1164640 1310575 := bstep (se 1 (by rfl) ⟨982931, by rfl⟩ : syracuseStep 1310575 = 1965863) B1965863
theorem B2949007 : Blo 1164640 2949007 := bstep (se 1 (by rfl) ⟨2211755, by rfl⟩ : syracuseStep 2949007 = 4423511) B4423511
theorem B1965991 : Blo 1164640 1965991 := bstep (se 1 (by rfl) ⟨1474493, by rfl⟩ : syracuseStep 1965991 = 2948987) B2948987
theorem B2211923 : Blo 1164640 2211923 := bstep (se 1 (by rfl) ⟨1658942, by rfl⟩ : syracuseStep 2211923 = 3317885) B3317885
theorem B2949311 : Blo 1164640 2949311 := bstep (se 1 (by rfl) ⟨2211983, by rfl⟩ : syracuseStep 2949311 = 4423967) B4423967
theorem B2801927 : Blo 1164640 2801927 := bstep (se 1 (by rfl) ⟨2101445, by rfl⟩ : syracuseStep 2801927 = 4202891) B4202891
theorem B2621753 : Blo 1164640 2621753 := bstep (se 2 (by rfl) ⟨983157, by rfl⟩ : syracuseStep 2621753 = 1966315) B1966315
theorem B2949929 : Blo 1164640 2949929 := bstep (se 2 (by rfl) ⟨1106223, by rfl⟩ : syracuseStep 2949929 = 2212447) B2212447
theorem B3318727 : Blo 1164640 3318727 := bstep (se 1 (by rfl) ⟨2489045, by rfl⟩ : syracuseStep 3318727 = 4978091) B4978091
theorem B5899391 : Blo 1164640 5899391 := bstep (se 1 (by rfl) ⟨4424543, by rfl⟩ : syracuseStep 5899391 = 8849087) B8849087
theorem B1311871 : Blo 1164640 1311871 := bstep (se 1 (by rfl) ⟨983903, by rfl⟩ : syracuseStep 1311871 = 1967807) B1967807
theorem B8856863 : Blo 1164640 8856863 := bstep (se 1 (by rfl) ⟨6642647, by rfl⟩ : syracuseStep 8856863 = 13285295) B13285295
theorem B2213183 : Blo 1164640 2213183 := bstep (se 1 (by rfl) ⟨1659887, by rfl⟩ : syracuseStep 2213183 = 3319775) B3319775
theorem B1164647 : Blo 1164640 1164647 := bstep (se 1 (by rfl) ⟨873485, by rfl⟩ : syracuseStep 1164647 = 1746971) B1746971
theorem B4982123 : Blo 1164640 4982123 := bstep (se 1 (by rfl) ⟨3736592, by rfl⟩ : syracuseStep 4982123 = 7473185) B7473185
theorem B1164891 : Blo 1164640 1164891 := bstep (se 1 (by rfl) ⟨873668, by rfl⟩ : syracuseStep 1164891 = 1747337) B1747337
theorem B6817385 : Blo 1164640 6817385 := bstep (se 2 (by rfl) ⟨2556519, by rfl⟩ : syracuseStep 6817385 = 5113039) B5113039
theorem B4425455 : Blo 1164640 4425455 := bstep (se 1 (by rfl) ⟨3319091, by rfl⟩ : syracuseStep 4425455 = 6638183) B6638183
theorem B5900039 : Blo 1164640 5900039 := bstep (se 1 (by rfl) ⟨4425029, by rfl⟩ : syracuseStep 5900039 = 8850059) B8850059
theorem B2950931 : Blo 1164640 2950931 := bstep (se 1 (by rfl) ⟨2213198, by rfl⟩ : syracuseStep 2950931 = 4426397) B4426397
theorem B2623481 : Blo 1164640 2623481 := bstep (se 2 (by rfl) ⟨983805, by rfl⟩ : syracuseStep 2623481 = 1967611) B1967611
theorem B2623571 : Blo 1164640 2623571 := bstep (se 1 (by rfl) ⟨1967678, by rfl⟩ : syracuseStep 2623571 = 3935357) B3935357
theorem B1165519 : Blo 1164640 1165519 := bstep (se 1 (by rfl) ⟨874139, by rfl⟩ : syracuseStep 1165519 = 1748279) B1748279
theorem B1747163 : Blo 1164640 1747163 := bstep (se 1 (by rfl) ⟨1310372, by rfl⟩ : syracuseStep 1747163 = 2620745) B2620745
theorem B2623751 : Blo 1164640 2623751 := bstep (se 1 (by rfl) ⟨1967813, by rfl⟩ : syracuseStep 2623751 = 3935627) B3935627
theorem B5318939 : Blo 1164640 5318939 := bstep (se 1 (by rfl) ⟨3989204, by rfl⟩ : syracuseStep 5318939 = 7978409) B7978409
theorem B1165631 : Blo 1164640 1165631 := bstep (se 1 (by rfl) ⟨874223, by rfl⟩ : syracuseStep 1165631 = 1748447) B1748447
theorem B3934601 : Blo 1164640 3934601 := bstep (se 2 (by rfl) ⟨1475475, by rfl⟩ : syracuseStep 3934601 = 2950951) B2950951
theorem B1771975 : Blo 1164640 1771975 := bstep (se 1 (by rfl) ⟨1328981, by rfl⟩ : syracuseStep 1771975 = 2657963) B2657963
theorem B1165775 : Blo 1164640 1165775 := bstep (se 1 (by rfl) ⟨874331, by rfl⟩ : syracuseStep 1165775 = 1748663) B1748663
theorem B1747433 : Blo 1164640 1747433 := bstep (se 2 (by rfl) ⟨655287, by rfl⟩ : syracuseStep 1747433 = 1310575) B1310575
theorem B1747439 : Blo 1164640 1747439 := bstep (se 1 (by rfl) ⟨1310579, by rfl⟩ : syracuseStep 1747439 = 2621159) B2621159
theorem B3320311 : Blo 1164640 3320311 := bstep (se 1 (by rfl) ⟨2490233, by rfl⟩ : syracuseStep 3320311 = 4980467) B4980467
theorem B1165915 : Blo 1164640 1165915 := bstep (se 1 (by rfl) ⟨874436, by rfl⟩ : syracuseStep 1165915 = 1748873) B1748873
theorem B71813735 : Blo 1164640 71813735 := bstep (se 1 (by rfl) ⟨53860301, by rfl⟩ : syracuseStep 71813735 = 107720603) B107720603
theorem B1166079 : Blo 1164640 1166079 := bstep (se 1 (by rfl) ⟨874559, by rfl⟩ : syracuseStep 1166079 = 1749119) B1749119
theorem B1747751 : Blo 1164640 1747751 := bstep (se 1 (by rfl) ⟨1310813, by rfl⟩ : syracuseStep 1747751 = 2621627) B2621627
theorem B8399699 : Blo 1164640 8399699 := bstep (se 1 (by rfl) ⟨6299774, by rfl⟩ : syracuseStep 8399699 = 12599549) B12599549
theorem B1747823 : Blo 1164640 1747823 := bstep (se 1 (by rfl) ⟨1310867, by rfl⟩ : syracuseStep 1747823 = 2621735) B2621735
theorem B2952065 : Blo 1164640 2952065 := bstep (se 2 (by rfl) ⟨1107024, by rfl⟩ : syracuseStep 2952065 = 2214049) B2214049
theorem B2952247 : Blo 1164640 2952247 := bstep (se 1 (by rfl) ⟨2214185, by rfl⟩ : syracuseStep 2952247 = 4428371) B4428371
theorem B1748075 : Blo 1164640 1748075 := bstep (se 1 (by rfl) ⟨1311056, by rfl⟩ : syracuseStep 1748075 = 2622113) B2622113
theorem B16174237 : Blo 1164640 16174237 := bstep (se 3 (by rfl) ⟨3032669, by rfl⟩ : syracuseStep 16174237 = 6065339) B6065339
theorem B5901497 : Blo 1164640 5901497 := bstep (se 2 (by rfl) ⟨2213061, by rfl⟩ : syracuseStep 5901497 = 4426123) B4426123
theorem B6638867 : Blo 1164640 6638867 := bstep (se 1 (by rfl) ⟨4979150, by rfl⟩ : syracuseStep 6638867 = 9958301) B9958301
theorem B1748315 : Blo 1164640 1748315 := bstep (se 1 (by rfl) ⟨1311236, by rfl⟩ : syracuseStep 1748315 = 2622473) B2622473
theorem B5901659 : Blo 1164640 5901659 := bstep (se 1 (by rfl) ⟨4426244, by rfl⟩ : syracuseStep 5901659 = 8852489) B8852489
theorem B1748345 : Blo 1164640 1748345 := bstep (se 2 (by rfl) ⟨655629, by rfl⟩ : syracuseStep 1748345 = 1311259) B1311259
theorem B1748351 : Blo 1164640 1748351 := bstep (se 1 (by rfl) ⟨1311263, by rfl⟩ : syracuseStep 1748351 = 2622527) B2622527
theorem B1748585 : Blo 1164640 1748585 := bstep (se 2 (by rfl) ⟨655719, by rfl⟩ : syracuseStep 1748585 = 1311439) B1311439
theorem B25882415 : Blo 1164640 25882415 := bstep (se 1 (by rfl) ⟨19411811, by rfl⟩ : syracuseStep 25882415 = 38823623) B38823623
theorem B3936167 : Blo 1164640 3936167 := bstep (se 1 (by rfl) ⟨2952125, by rfl⟩ : syracuseStep 3936167 = 5904251) B5904251
theorem B30281681 : Blo 1164640 30281681 := bstep (se 2 (by rfl) ⟨11355630, by rfl⟩ : syracuseStep 30281681 = 22711261) B22711261
theorem B1748975 : Blo 1164640 1748975 := bstep (se 1 (by rfl) ⟨1311731, by rfl⟩ : syracuseStep 1748975 = 2623463) B2623463
theorem B57446425 : Blo 1164640 57446425 := bstep (se 2 (by rfl) ⟨21542409, by rfl⟩ : syracuseStep 57446425 = 43084819) B43084819
theorem B1749095 : Blo 1164640 1749095 := bstep (se 1 (by rfl) ⟨1311821, by rfl⟩ : syracuseStep 1749095 = 2623643) B2623643
theorem B1749215 : Blo 1164640 1749215 := bstep (se 1 (by rfl) ⟨1311911, by rfl⟩ : syracuseStep 1749215 = 2623823) B2623823
theorem B1749275 : Blo 1164640 1749275 := bstep (se 1 (by rfl) ⟨1311956, by rfl⟩ : syracuseStep 1749275 = 2623913) B2623913
theorem B10629413 : Blo 1164640 10629413 := bstep (se 4 (by rfl) ⟨996507, by rfl⟩ : syracuseStep 10629413 = 1993015) B1993015
theorem B4977065 : Blo 1164640 4977065 := bstep (se 2 (by rfl) ⟨1866399, by rfl⟩ : syracuseStep 4977065 = 3732799) B3732799
theorem B143536819 : Blo 1164640 143536819 := bstep (se 1 (by rfl) ⟨107652614, by rfl⟩ : syracuseStep 143536819 = 215305229) B215305229
theorem B30274823 : Blo 1164640 30274823 := bstep (se 1 (by rfl) ⟨22706117, by rfl⟩ : syracuseStep 30274823 = 45412235) B45412235
theorem B6296939 : Blo 1164640 6296939 := bstep (se 1 (by rfl) ⟨4722704, by rfl⟩ : syracuseStep 6296939 = 9445409) B9445409
theorem B8852975 : Blo 1164640 8852975 := bstep (se 1 (by rfl) ⟨6639731, by rfl⟩ : syracuseStep 8852975 = 13279463) B13279463
theorem B2840255 : Blo 1164640 2840255 := bstep (se 1 (by rfl) ⟨2130191, by rfl⟩ : syracuseStep 2840255 = 4260383) B4260383
theorem B5896151 : Blo 1164640 5896151 := bstep (se 1 (by rfl) ⟨4422113, by rfl⟩ : syracuseStep 5896151 = 8844227) B8844227
theorem B13645799 : Blo 1164640 13645799 := bstep (se 1 (by rfl) ⟨10234349, by rfl⟩ : syracuseStep 13645799 = 20468699) B20468699
theorem B6633535 : Blo 1164640 6633535 := bstep (se 1 (by rfl) ⟨4975151, by rfl⟩ : syracuseStep 6633535 = 9950303) B9950303
theorem B5896313 : Blo 1164640 5896313 := bstep (se 2 (by rfl) ⟨2211117, by rfl⟩ : syracuseStep 5896313 = 4422235) B4422235
theorem B80771651 : Blo 1164640 80771651 := bstep (se 1 (by rfl) ⟨60578738, by rfl⟩ : syracuseStep 80771651 = 121157477) B121157477
theorem B1838733965 : Blo 1164640 1838733965 := bstep (se 3 (by rfl) ⟨344762618, by rfl⟩ : syracuseStep 1838733965 = 689525237) B689525237
theorem B9951943 : Blo 1164640 9951943 := bstep (se 1 (by rfl) ⟨7463957, by rfl⟩ : syracuseStep 9951943 = 14927915) B14927915
theorem B3931091 : Blo 1164640 3931091 := bstep (se 1 (by rfl) ⟨2948318, by rfl⟩ : syracuseStep 3931091 = 5896637) B5896637
theorem B6642809 : Blo 1164640 6642809 := bstep (se 2 (by rfl) ⟨2491053, by rfl⟩ : syracuseStep 6642809 = 4982107) B4982107
theorem B1596667 : Blo 1164640 1596667 := bstep (se 1 (by rfl) ⟨1197500, by rfl⟩ : syracuseStep 1596667 = 2395001) B2395001
theorem B2620691 : Blo 1164640 2620691 := bstep (se 1 (by rfl) ⟨1965518, by rfl⟩ : syracuseStep 2620691 = 3931037) B3931037
theorem B2948521 : Blo 1164640 2948521 := bstep (se 2 (by rfl) ⟨1105695, by rfl⟩ : syracuseStep 2948521 = 2211391) B2211391
theorem B13270715 : Blo 1164640 13270715 := bstep (se 1 (by rfl) ⟨9953036, by rfl⟩ : syracuseStep 13270715 = 19906073) B19906073
theorem B3932009 : Blo 1164640 3932009 := bstep (se 2 (by rfl) ⟨1474503, by rfl⟩ : syracuseStep 3932009 = 2949007) B2949007
theorem B2621321 : Blo 1164640 2621321 := bstep (se 2 (by rfl) ⟨982995, by rfl⟩ : syracuseStep 2621321 = 1965991) B1965991
theorem B4980619 : Blo 1164640 4980619 := bstep (se 1 (by rfl) ⟨3735464, by rfl⟩ : syracuseStep 4980619 = 7470929) B7470929
theorem B76595233 : Blo 1164640 76595233 := bstep (se 2 (by rfl) ⟨28723212, by rfl⟩ : syracuseStep 76595233 = 57446425) B57446425
theorem B1474615 : Blo 1164640 1474615 := bstep (se 1 (by rfl) ⟨1105961, by rfl⟩ : syracuseStep 1474615 = 2211923) B2211923
theorem B1966207 : Blo 1164640 1966207 := bstep (se 1 (by rfl) ⟨1474655, by rfl⟩ : syracuseStep 1966207 = 2949311) B2949311
theorem B1867951 : Blo 1164640 1867951 := bstep (se 1 (by rfl) ⟨1400963, by rfl⟩ : syracuseStep 1867951 = 2801927) B2801927
theorem B7086275 : Blo 1164640 7086275 := bstep (se 1 (by rfl) ⟨5314706, by rfl⟩ : syracuseStep 7086275 = 10629413) B10629413
theorem B1966619 : Blo 1164640 1966619 := bstep (se 1 (by rfl) ⟨1474964, by rfl⟩ : syracuseStep 1966619 = 2949929) B2949929
theorem B3932927 : Blo 1164640 3932927 := bstep (se 1 (by rfl) ⟨2949695, by rfl⟩ : syracuseStep 3932927 = 5899391) B5899391
theorem B191382425 : Blo 1164640 191382425 := bstep (se 2 (by rfl) ⟨71768409, by rfl⟩ : syracuseStep 191382425 = 143536819) B143536819
theorem B13272173 : Blo 1164640 13272173 := bstep (se 3 (by rfl) ⟨2488532, by rfl⟩ : syracuseStep 13272173 = 4977065) B4977065
theorem B1893503 : Blo 1164640 1893503 := bstep (se 1 (by rfl) ⟨1420127, by rfl⟩ : syracuseStep 1893503 = 2840255) B2840255
theorem B2950303 : Blo 1164640 2950303 := bstep (se 1 (by rfl) ⟨2212727, by rfl⟩ : syracuseStep 2950303 = 4425455) B4425455
theorem B3933359 : Blo 1164640 3933359 := bstep (se 1 (by rfl) ⟨2950019, by rfl⟩ : syracuseStep 3933359 = 5900039) B5900039
theorem B1967287 : Blo 1164640 1967287 := bstep (se 1 (by rfl) ⟨1475465, by rfl⟩ : syracuseStep 1967287 = 2950931) B2950931
theorem B4424969 : Blo 1164640 4424969 := bstep (se 2 (by rfl) ⟨1659363, by rfl⟩ : syracuseStep 4424969 = 3318727) B3318727
theorem B1164775 : Blo 1164640 1164775 := bstep (se 1 (by rfl) ⟨873581, by rfl⟩ : syracuseStep 1164775 = 1747163) B1747163
theorem B2623067 : Blo 1164640 2623067 := bstep (se 1 (by rfl) ⟨1967300, by rfl⟩ : syracuseStep 2623067 = 3934601) B3934601
theorem B1164955 : Blo 1164640 1164955 := bstep (se 1 (by rfl) ⟨873716, by rfl⟩ : syracuseStep 1164955 = 1747433) B1747433
theorem B1164959 : Blo 1164640 1164959 := bstep (se 1 (by rfl) ⟨873719, by rfl⟩ : syracuseStep 1164959 = 1747439) B1747439
theorem B53847767 : Blo 1164640 53847767 := bstep (se 1 (by rfl) ⟨40385825, by rfl⟩ : syracuseStep 53847767 = 80771651) B80771651
theorem B47875823 : Blo 1164640 47875823 := bstep (se 1 (by rfl) ⟨35906867, by rfl⟩ : syracuseStep 47875823 = 71813735) B71813735
theorem B1165167 : Blo 1164640 1165167 := bstep (se 1 (by rfl) ⟨873875, by rfl⟩ : syracuseStep 1165167 = 1747751) B1747751
theorem B1165215 : Blo 1164640 1165215 := bstep (se 1 (by rfl) ⟨873911, by rfl⟩ : syracuseStep 1165215 = 1747823) B1747823
theorem B1968043 : Blo 1164640 1968043 := bstep (se 1 (by rfl) ⟨1476032, by rfl⟩ : syracuseStep 1968043 = 2952065) B2952065
theorem B1165383 : Blo 1164640 1165383 := bstep (se 1 (by rfl) ⟨874037, by rfl⟩ : syracuseStep 1165383 = 1748075) B1748075
theorem B3934331 : Blo 1164640 3934331 := bstep (se 1 (by rfl) ⟨2950748, by rfl⟩ : syracuseStep 3934331 = 5901497) B5901497
theorem B1747127 : Blo 1164640 1747127 := bstep (se 1 (by rfl) ⟨1310345, by rfl⟩ : syracuseStep 1747127 = 2620691) B2620691
theorem B4425911 : Blo 1164640 4425911 := bstep (se 1 (by rfl) ⟨3319433, by rfl⟩ : syracuseStep 4425911 = 6638867) B6638867
theorem B1165543 : Blo 1164640 1165543 := bstep (se 1 (by rfl) ⟨874157, by rfl⟩ : syracuseStep 1165543 = 1748315) B1748315
theorem B3934439 : Blo 1164640 3934439 := bstep (se 1 (by rfl) ⟨2950829, by rfl⟩ : syracuseStep 3934439 = 5901659) B5901659
theorem B1165563 : Blo 1164640 1165563 := bstep (se 1 (by rfl) ⟨874172, by rfl⟩ : syracuseStep 1165563 = 1748345) B1748345
theorem B1165567 : Blo 1164640 1165567 := bstep (se 1 (by rfl) ⟨874175, by rfl⟩ : syracuseStep 1165567 = 1748351) B1748351
theorem B1165723 : Blo 1164640 1165723 := bstep (se 1 (by rfl) ⟨874292, by rfl⟩ : syracuseStep 1165723 = 1748585) B1748585
theorem B17254943 : Blo 1164640 17254943 := bstep (se 1 (by rfl) ⟨12941207, by rfl⟩ : syracuseStep 17254943 = 25882415) B25882415
theorem B1747547 : Blo 1164640 1747547 := bstep (se 1 (by rfl) ⟨1310660, by rfl⟩ : syracuseStep 1747547 = 2621321) B2621321
theorem B2624111 : Blo 1164640 2624111 := bstep (se 1 (by rfl) ⟨1968083, by rfl⟩ : syracuseStep 2624111 = 3936167) B3936167
theorem B20187787 : Blo 1164640 20187787 := bstep (se 1 (by rfl) ⟨15140840, by rfl⟩ : syracuseStep 20187787 = 30281681) B30281681
theorem B1165983 : Blo 1164640 1165983 := bstep (se 1 (by rfl) ⟨874487, by rfl⟩ : syracuseStep 1165983 = 1748975) B1748975
theorem B1166063 : Blo 1164640 1166063 := bstep (se 1 (by rfl) ⟨874547, by rfl⟩ : syracuseStep 1166063 = 1749095) B1749095
theorem B1166143 : Blo 1164640 1166143 := bstep (se 1 (by rfl) ⟨874607, by rfl⟩ : syracuseStep 1166143 = 1749215) B1749215
theorem B1166183 : Blo 1164640 1166183 := bstep (se 1 (by rfl) ⟨874637, by rfl⟩ : syracuseStep 1166183 = 1749275) B1749275
theorem B1747835 : Blo 1164640 1747835 := bstep (se 1 (by rfl) ⟨1310876, by rfl⟩ : syracuseStep 1747835 = 2621753) B2621753
theorem B4427081 : Blo 1164640 4427081 := bstep (se 2 (by rfl) ⟨1660155, by rfl⟩ : syracuseStep 4427081 = 3320311) B3320311
theorem B5901821 : Blo 1164640 5901821 := bstep (se 3 (by rfl) ⟨1106591, by rfl⟩ : syracuseStep 5901821 = 2213183) B2213183
theorem B4197959 : Blo 1164640 4197959 := bstep (se 1 (by rfl) ⟨3148469, by rfl⟩ : syracuseStep 4197959 = 6296939) B6296939
theorem B3321415 : Blo 1164640 3321415 := bstep (se 1 (by rfl) ⟨2491061, by rfl⟩ : syracuseStep 3321415 = 4982123) B4982123
theorem B5901983 : Blo 1164640 5901983 := bstep (se 1 (by rfl) ⟨4426487, by rfl⟩ : syracuseStep 5901983 = 8852975) B8852975
theorem B9097199 : Blo 1164640 9097199 := bstep (se 1 (by rfl) ⟨6822899, by rfl⟩ : syracuseStep 9097199 = 13645799) B13645799
theorem B1748987 : Blo 1164640 1748987 := bstep (se 1 (by rfl) ⟨1311740, by rfl⟩ : syracuseStep 1748987 = 2623481) B2623481
theorem B1749047 : Blo 1164640 1749047 := bstep (se 1 (by rfl) ⟨1311785, by rfl⟩ : syracuseStep 1749047 = 2623571) B2623571
theorem B3936329 : Blo 1164640 3936329 := bstep (se 2 (by rfl) ⟨1476123, by rfl⟩ : syracuseStep 3936329 = 2952247) B2952247
theorem B1749161 : Blo 1164640 1749161 := bstep (se 2 (by rfl) ⟨655935, by rfl⟩ : syracuseStep 1749161 = 1311871) B1311871
theorem B1749167 : Blo 1164640 1749167 := bstep (se 1 (by rfl) ⟨1311875, by rfl⟩ : syracuseStep 1749167 = 2623751) B2623751
theorem B21565649 : Blo 1164640 21565649 := bstep (se 2 (by rfl) ⟨8087118, by rfl⟩ : syracuseStep 21565649 = 16174237) B16174237
theorem B1225822643 : Blo 1164640 1225822643 := bstep (se 1 (by rfl) ⟨919366982, by rfl⟩ : syracuseStep 1225822643 = 1838733965) B1838733965
theorem B5599799 : Blo 1164640 5599799 := bstep (se 1 (by rfl) ⟨4199849, by rfl⟩ : syracuseStep 5599799 = 8399699) B8399699
theorem B4428539 : Blo 1164640 4428539 := bstep (se 1 (by rfl) ⟨3321404, by rfl⟩ : syracuseStep 4428539 = 6642809) B6642809
theorem B9450533 : Blo 1164640 9450533 := bstep (se 4 (by rfl) ⟨885987, by rfl⟩ : syracuseStep 9450533 = 1771975) B1771975
theorem B6640825 : Blo 1164640 6640825 := bstep (se 2 (by rfl) ⟨2490309, by rfl⟩ : syracuseStep 6640825 = 4980619) B4980619
theorem B8844713 : Blo 1164640 8844713 := bstep (se 2 (by rfl) ⟨3316767, by rfl⟩ : syracuseStep 8844713 = 6633535) B6633535
theorem B20183215 : Blo 1164640 20183215 := bstep (se 1 (by rfl) ⟨15137411, by rfl⟩ : syracuseStep 20183215 = 30274823) B30274823
theorem B5904575 : Blo 1164640 5904575 := bstep (se 1 (by rfl) ⟨4428431, by rfl⟩ : syracuseStep 5904575 = 8856863) B8856863
theorem B13269257 : Blo 1164640 13269257 := bstep (se 2 (by rfl) ⟨4975971, by rfl⟩ : syracuseStep 13269257 = 9951943) B9951943
theorem B4544923 : Blo 1164640 4544923 := bstep (se 1 (by rfl) ⟨3408692, by rfl⟩ : syracuseStep 4544923 = 6817385) B6817385
theorem B3930767 : Blo 1164640 3930767 := bstep (se 1 (by rfl) ⟨2948075, by rfl⟩ : syracuseStep 3930767 = 5896151) B5896151
theorem B3930875 : Blo 1164640 3930875 := bstep (se 1 (by rfl) ⟨2948156, by rfl⟩ : syracuseStep 3930875 = 5896313) B5896313
theorem B3545959 : Blo 1164640 3545959 := bstep (se 1 (by rfl) ⟨2659469, by rfl⟩ : syracuseStep 3545959 = 5318939) B5318939
theorem B2128889 : Blo 1164640 2128889 := bstep (se 2 (by rfl) ⟨798333, by rfl⟩ : syracuseStep 2128889 = 1596667) B1596667
theorem B3931361 : Blo 1164640 3931361 := bstep (se 2 (by rfl) ⟨1474260, by rfl⟩ : syracuseStep 3931361 = 2948521) B2948521
theorem B2620727 : Blo 1164640 2620727 := bstep (se 1 (by rfl) ⟨1965545, by rfl⟩ : syracuseStep 2620727 = 3931091) B3931091
theorem B8847143 : Blo 1164640 8847143 := bstep (se 1 (by rfl) ⟨6635357, by rfl⟩ : syracuseStep 8847143 = 13270715) B13270715
theorem B2621339 : Blo 1164640 2621339 := bstep (se 1 (by rfl) ⟨1966004, by rfl⟩ : syracuseStep 2621339 = 3932009) B3932009
theorem B1966153 : Blo 1164640 1966153 := bstep (se 2 (by rfl) ⟨737307, by rfl⟩ : syracuseStep 1966153 = 1474615) B1474615
theorem B14377099 : Blo 1164640 14377099 := bstep (se 1 (by rfl) ⟨10782824, by rfl⟩ : syracuseStep 14377099 = 21565649) B21565649
theorem B2621609 : Blo 1164640 2621609 := bstep (se 2 (by rfl) ⟨983103, by rfl⟩ : syracuseStep 2621609 = 1966207) B1966207
theorem B26910953 : Blo 1164640 26910953 := bstep (se 2 (by rfl) ⟨10091607, by rfl⟩ : syracuseStep 26910953 = 20183215) B20183215
theorem B2490601 : Blo 1164640 2490601 := bstep (se 2 (by rfl) ⟨933975, by rfl⟩ : syracuseStep 2490601 = 1867951) B1867951
theorem B1311079 : Blo 1164640 1311079 := bstep (se 1 (by rfl) ⟨983309, by rfl⟩ : syracuseStep 1311079 = 1966619) B1966619
theorem B2621951 : Blo 1164640 2621951 := bstep (se 1 (by rfl) ⟨1966463, by rfl⟩ : syracuseStep 2621951 = 3932927) B3932927
theorem B6300355 : Blo 1164640 6300355 := bstep (se 1 (by rfl) ⟨4725266, by rfl⟩ : syracuseStep 6300355 = 9450533) B9450533
theorem B8848115 : Blo 1164640 8848115 := bstep (se 1 (by rfl) ⟨6636086, by rfl⟩ : syracuseStep 8848115 = 13272173) B13272173
theorem B1262335 : Blo 1164640 1262335 := bstep (se 1 (by rfl) ⟨946751, by rfl⟩ : syracuseStep 1262335 = 1893503) B1893503
theorem B2622239 : Blo 1164640 2622239 := bstep (se 1 (by rfl) ⟨1966679, by rfl⟩ : syracuseStep 2622239 = 3933359) B3933359
theorem B2949979 : Blo 1164640 2949979 := bstep (se 1 (by rfl) ⟨2212484, by rfl⟩ : syracuseStep 2949979 = 4424969) B4424969
theorem B4727945 : Blo 1164640 4727945 := bstep (se 2 (by rfl) ⟨1772979, by rfl⟩ : syracuseStep 4727945 = 3545959) B3545959
theorem B35898511 : Blo 1164640 35898511 := bstep (se 1 (by rfl) ⟨26923883, by rfl⟩ : syracuseStep 35898511 = 53847767) B53847767
theorem B31917215 : Blo 1164640 31917215 := bstep (se 1 (by rfl) ⟨23937911, by rfl⟩ : syracuseStep 31917215 = 47875823) B47875823
theorem B2622887 : Blo 1164640 2622887 := bstep (se 1 (by rfl) ⟨1967165, by rfl⟩ : syracuseStep 2622887 = 3934331) B3934331
theorem B1164751 : Blo 1164640 1164751 := bstep (se 1 (by rfl) ⟨873563, by rfl⟩ : syracuseStep 1164751 = 1747127) B1747127
theorem B2950607 : Blo 1164640 2950607 := bstep (se 1 (by rfl) ⟨2212955, by rfl⟩ : syracuseStep 2950607 = 4425911) B4425911
theorem B2622959 : Blo 1164640 2622959 := bstep (se 1 (by rfl) ⟨1967219, by rfl⟩ : syracuseStep 2622959 = 3934439) B3934439
theorem B3933737 : Blo 1164640 3933737 := bstep (se 2 (by rfl) ⟨1475151, by rfl⟩ : syracuseStep 3933737 = 2950303) B2950303
theorem B2623049 : Blo 1164640 2623049 := bstep (se 2 (by rfl) ⟨983643, by rfl⟩ : syracuseStep 2623049 = 1967287) B1967287
theorem B11503295 : Blo 1164640 11503295 := bstep (se 1 (by rfl) ⟨8627471, by rfl⟩ : syracuseStep 11503295 = 17254943) B17254943
theorem B1165031 : Blo 1164640 1165031 := bstep (se 1 (by rfl) ⟨873773, by rfl⟩ : syracuseStep 1165031 = 1747547) B1747547
theorem B1165223 : Blo 1164640 1165223 := bstep (se 1 (by rfl) ⟨873917, by rfl⟩ : syracuseStep 1165223 = 1747835) B1747835
theorem B1747151 : Blo 1164640 1747151 := bstep (se 1 (by rfl) ⟨1310363, by rfl⟩ : syracuseStep 1747151 = 2620727) B2620727
theorem B2951387 : Blo 1164640 2951387 := bstep (se 1 (by rfl) ⟨2213540, by rfl⟩ : syracuseStep 2951387 = 4427081) B4427081
theorem B3934547 : Blo 1164640 3934547 := bstep (se 1 (by rfl) ⟨2950910, by rfl⟩ : syracuseStep 3934547 = 5901821) B5901821
theorem B3934655 : Blo 1164640 3934655 := bstep (se 1 (by rfl) ⟨2950991, by rfl⟩ : syracuseStep 3934655 = 5901983) B5901983
theorem B2624057 : Blo 1164640 2624057 := bstep (se 2 (by rfl) ⟨984021, by rfl⟩ : syracuseStep 2624057 = 1968043) B1968043
theorem B1747559 : Blo 1164640 1747559 := bstep (se 1 (by rfl) ⟨1310669, by rfl⟩ : syracuseStep 1747559 = 2621339) B2621339
theorem B6064799 : Blo 1164640 6064799 := bstep (se 1 (by rfl) ⟨4548599, by rfl⟩ : syracuseStep 6064799 = 9097199) B9097199
theorem B1165991 : Blo 1164640 1165991 := bstep (se 1 (by rfl) ⟨874493, by rfl⟩ : syracuseStep 1165991 = 1748987) B1748987
theorem B1166031 : Blo 1164640 1166031 := bstep (se 1 (by rfl) ⟨874523, by rfl⟩ : syracuseStep 1166031 = 1749047) B1749047
theorem B2624219 : Blo 1164640 2624219 := bstep (se 1 (by rfl) ⟨1968164, by rfl⟩ : syracuseStep 2624219 = 3936329) B3936329
theorem B1166107 : Blo 1164640 1166107 := bstep (se 1 (by rfl) ⟨874580, by rfl⟩ : syracuseStep 1166107 = 1749161) B1749161
theorem B1166111 : Blo 1164640 1166111 := bstep (se 1 (by rfl) ⟨874583, by rfl⟩ : syracuseStep 1166111 = 1749167) B1749167
theorem B2952359 : Blo 1164640 2952359 := bstep (se 1 (by rfl) ⟨2214269, by rfl⟩ : syracuseStep 2952359 = 4428539) B4428539
theorem B1748711 : Blo 1164640 1748711 := bstep (se 1 (by rfl) ⟨1311533, by rfl⟩ : syracuseStep 1748711 = 2623067) B2623067
theorem B3936383 : Blo 1164640 3936383 := bstep (se 1 (by rfl) ⟨2952287, by rfl⟩ : syracuseStep 3936383 = 5904575) B5904575
theorem B1749407 : Blo 1164640 1749407 := bstep (se 1 (by rfl) ⟨1312055, by rfl⟩ : syracuseStep 1749407 = 2624111) B2624111
theorem B4428553 : Blo 1164640 4428553 := bstep (se 2 (by rfl) ⟨1660707, by rfl⟩ : syracuseStep 4428553 = 3321415) B3321415
theorem B2798639 : Blo 1164640 2798639 := bstep (se 1 (by rfl) ⟨2098979, by rfl⟩ : syracuseStep 2798639 = 4197959) B4197959
theorem B102126977 : Blo 1164640 102126977 := bstep (se 2 (by rfl) ⟨38297616, by rfl⟩ : syracuseStep 102126977 = 76595233) B76595233
theorem B4724183 : Blo 1164640 4724183 := bstep (se 1 (by rfl) ⟨3543137, by rfl⟩ : syracuseStep 4724183 = 7086275) B7086275
theorem B817215095 : Blo 1164640 817215095 := bstep (se 1 (by rfl) ⟨612911321, by rfl⟩ : syracuseStep 817215095 = 1225822643) B1225822643
theorem B3733199 : Blo 1164640 3733199 := bstep (se 1 (by rfl) ⟨2799899, by rfl⟩ : syracuseStep 3733199 = 5599799) B5599799
theorem B6059897 : Blo 1164640 6059897 := bstep (se 2 (by rfl) ⟨2272461, by rfl⟩ : syracuseStep 6059897 = 4544923) B4544923
theorem B127588283 : Blo 1164640 127588283 := bstep (se 1 (by rfl) ⟨95691212, by rfl⟩ : syracuseStep 127588283 = 191382425) B191382425
theorem B26917049 : Blo 1164640 26917049 := bstep (se 2 (by rfl) ⟨10093893, by rfl⟩ : syracuseStep 26917049 = 20187787) B20187787
theorem B5896475 : Blo 1164640 5896475 := bstep (se 1 (by rfl) ⟨4422356, by rfl⟩ : syracuseStep 5896475 = 8844713) B8844713
theorem B8846171 : Blo 1164640 8846171 := bstep (se 1 (by rfl) ⟨6634628, by rfl⟩ : syracuseStep 8846171 = 13269257) B13269257
theorem B8854433 : Blo 1164640 8854433 := bstep (se 2 (by rfl) ⟨3320412, by rfl⟩ : syracuseStep 8854433 = 6640825) B6640825
theorem B2620511 : Blo 1164640 2620511 := bstep (se 1 (by rfl) ⟨1965383, by rfl⟩ : syracuseStep 2620511 = 3930767) B3930767
theorem B2620583 : Blo 1164640 2620583 := bstep (se 1 (by rfl) ⟨1965437, by rfl⟩ : syracuseStep 2620583 = 3930875) B3930875
theorem B2620907 : Blo 1164640 2620907 := bstep (se 1 (by rfl) ⟨1965680, by rfl⟩ : syracuseStep 2620907 = 3931361) B3931361
theorem B5898095 : Blo 1164640 5898095 := bstep (se 1 (by rfl) ⟨4423571, by rfl⟩ : syracuseStep 5898095 = 8847143) B8847143
theorem B5677037 : Blo 1164640 5677037 := bstep (se 3 (by rfl) ⟨1064444, by rfl⟩ : syracuseStep 5677037 = 2128889) B2128889
theorem B2621537 : Blo 1164640 2621537 := bstep (se 2 (by rfl) ⟨983076, by rfl⟩ : syracuseStep 2621537 = 1966153) B1966153
theorem B17940635 : Blo 1164640 17940635 := bstep (se 1 (by rfl) ⟨13455476, by rfl⟩ : syracuseStep 17940635 = 26910953) B26910953
theorem B19169465 : Blo 1164640 19169465 := bstep (se 2 (by rfl) ⟨7188549, by rfl⟩ : syracuseStep 19169465 = 14377099) B14377099
theorem B71778797 : Blo 1164640 71778797 := bstep (se 3 (by rfl) ⟨13458524, by rfl⟩ : syracuseStep 71778797 = 26917049) B26917049
theorem B5898743 : Blo 1164640 5898743 := bstep (se 1 (by rfl) ⟨4424057, by rfl⟩ : syracuseStep 5898743 = 8848115) B8848115
theorem B68084651 : Blo 1164640 68084651 := bstep (se 1 (by rfl) ⟨51063488, by rfl⟩ : syracuseStep 68084651 = 102126977) B102126977
theorem B1967071 : Blo 1164640 1967071 := bstep (se 1 (by rfl) ⟨1475303, by rfl⟩ : syracuseStep 1967071 = 2950607) B2950607
theorem B2622491 : Blo 1164640 2622491 := bstep (se 1 (by rfl) ⟨1966868, by rfl⟩ : syracuseStep 2622491 = 3933737) B3933737
theorem B544810063 : Blo 1164640 544810063 := bstep (se 1 (by rfl) ⟨408607547, by rfl⟩ : syracuseStep 544810063 = 817215095) B817215095
theorem B3933305 : Blo 1164640 3933305 := bstep (se 2 (by rfl) ⟨1474989, by rfl⟩ : syracuseStep 3933305 = 2949979) B2949979
theorem B7668863 : Blo 1164640 7668863 := bstep (se 1 (by rfl) ⟨5751647, by rfl⟩ : syracuseStep 7668863 = 11503295) B11503295
theorem B4039931 : Blo 1164640 4039931 := bstep (se 1 (by rfl) ⟨3029948, by rfl⟩ : syracuseStep 4039931 = 6059897) B6059897
theorem B85058855 : Blo 1164640 85058855 := bstep (se 1 (by rfl) ⟨63794141, by rfl⟩ : syracuseStep 85058855 = 127588283) B127588283
theorem B1164767 : Blo 1164640 1164767 := bstep (se 1 (by rfl) ⟨873575, by rfl⟩ : syracuseStep 1164767 = 1747151) B1747151
theorem B1967591 : Blo 1164640 1967591 := bstep (se 1 (by rfl) ⟨1475693, by rfl⟩ : syracuseStep 1967591 = 2951387) B2951387
theorem B2623031 : Blo 1164640 2623031 := bstep (se 1 (by rfl) ⟨1967273, by rfl⟩ : syracuseStep 2623031 = 3934547) B3934547
theorem B2623103 : Blo 1164640 2623103 := bstep (se 1 (by rfl) ⟨1967327, by rfl⟩ : syracuseStep 2623103 = 3934655) B3934655
theorem B1165039 : Blo 1164640 1165039 := bstep (se 1 (by rfl) ⟨873779, by rfl⟩ : syracuseStep 1165039 = 1747559) B1747559
theorem B16172797 : Blo 1164640 16172797 := bstep (se 3 (by rfl) ⟨3032399, by rfl⟩ : syracuseStep 16172797 = 6064799) B6064799
theorem B1747007 : Blo 1164640 1747007 := bstep (se 1 (by rfl) ⟨1310255, by rfl⟩ : syracuseStep 1747007 = 2620511) B2620511
theorem B1747055 : Blo 1164640 1747055 := bstep (se 1 (by rfl) ⟨1310291, by rfl⟩ : syracuseStep 1747055 = 2620583) B2620583
theorem B1968239 : Blo 1164640 1968239 := bstep (se 1 (by rfl) ⟨1476179, by rfl⟩ : syracuseStep 1968239 = 2952359) B2952359
theorem B1747271 : Blo 1164640 1747271 := bstep (se 1 (by rfl) ⟨1310453, by rfl⟩ : syracuseStep 1747271 = 2620907) B2620907
theorem B1165807 : Blo 1164640 1165807 := bstep (se 1 (by rfl) ⟨874355, by rfl⟩ : syracuseStep 1165807 = 1748711) B1748711
theorem B2624255 : Blo 1164640 2624255 := bstep (se 1 (by rfl) ⟨1968191, by rfl⟩ : syracuseStep 2624255 = 3936383) B3936383
theorem B1747739 : Blo 1164640 1747739 := bstep (se 1 (by rfl) ⟨1310804, by rfl⟩ : syracuseStep 1747739 = 2621609) B2621609
theorem B1166271 : Blo 1164640 1166271 := bstep (se 1 (by rfl) ⟨874703, by rfl⟩ : syracuseStep 1166271 = 1749407) B1749407
theorem B3320801 : Blo 1164640 3320801 := bstep (se 2 (by rfl) ⟨1245300, by rfl⟩ : syracuseStep 3320801 = 2490601) B2490601
theorem B1747967 : Blo 1164640 1747967 := bstep (se 1 (by rfl) ⟨1310975, by rfl⟩ : syracuseStep 1747967 = 2621951) B2621951
theorem B1748105 : Blo 1164640 1748105 := bstep (se 2 (by rfl) ⟨655539, by rfl⟩ : syracuseStep 1748105 = 1311079) B1311079
theorem B1748159 : Blo 1164640 1748159 := bstep (se 1 (by rfl) ⟨1311119, by rfl⟩ : syracuseStep 1748159 = 2622239) B2622239
theorem B21278143 : Blo 1164640 21278143 := bstep (se 1 (by rfl) ⟨15958607, by rfl⟩ : syracuseStep 21278143 = 31917215) B31917215
theorem B8400473 : Blo 1164640 8400473 := bstep (se 2 (by rfl) ⟨3150177, by rfl⟩ : syracuseStep 8400473 = 6300355) B6300355
theorem B1748591 : Blo 1164640 1748591 := bstep (se 1 (by rfl) ⟨1311443, by rfl⟩ : syracuseStep 1748591 = 2622887) B2622887
theorem B3149455 : Blo 1164640 3149455 := bstep (se 1 (by rfl) ⟨2362091, by rfl⟩ : syracuseStep 3149455 = 4724183) B4724183
theorem B1748639 : Blo 1164640 1748639 := bstep (se 1 (by rfl) ⟨1311479, by rfl⟩ : syracuseStep 1748639 = 2622959) B2622959
theorem B1683113 : Blo 1164640 1683113 := bstep (se 2 (by rfl) ⟨631167, by rfl⟩ : syracuseStep 1683113 = 1262335) B1262335
theorem B1748699 : Blo 1164640 1748699 := bstep (se 1 (by rfl) ⟨1311524, by rfl⟩ : syracuseStep 1748699 = 2623049) B2623049
theorem B1749371 : Blo 1164640 1749371 := bstep (se 1 (by rfl) ⟨1312028, by rfl⟩ : syracuseStep 1749371 = 2624057) B2624057
theorem B1749479 : Blo 1164640 1749479 := bstep (se 1 (by rfl) ⟨1312109, by rfl⟩ : syracuseStep 1749479 = 2624219) B2624219
theorem B5902955 : Blo 1164640 5902955 := bstep (se 1 (by rfl) ⟨4427216, by rfl⟩ : syracuseStep 5902955 = 8854433) B8854433
theorem B1865759 : Blo 1164640 1865759 := bstep (se 1 (by rfl) ⟨1399319, by rfl⟩ : syracuseStep 1865759 = 2798639) B2798639
theorem B3151963 : Blo 1164640 3151963 := bstep (se 1 (by rfl) ⟨2363972, by rfl⟩ : syracuseStep 3151963 = 4727945) B4727945
theorem B5904737 : Blo 1164640 5904737 := bstep (se 2 (by rfl) ⟨2214276, by rfl⟩ : syracuseStep 5904737 = 4428553) B4428553
theorem B2488799 : Blo 1164640 2488799 := bstep (se 1 (by rfl) ⟨1866599, by rfl⟩ : syracuseStep 2488799 = 3733199) B3733199
theorem B3930983 : Blo 1164640 3930983 := bstep (se 1 (by rfl) ⟨2948237, by rfl⟩ : syracuseStep 3930983 = 5896475) B5896475
theorem B47864681 : Blo 1164640 47864681 := bstep (se 2 (by rfl) ⟨17949255, by rfl⟩ : syracuseStep 47864681 = 35898511) B35898511
theorem B5897447 : Blo 1164640 5897447 := bstep (se 1 (by rfl) ⟨4423085, by rfl⟩ : syracuseStep 5897447 = 8846171) B8846171
theorem B3932063 : Blo 1164640 3932063 := bstep (se 1 (by rfl) ⟨2949047, by rfl⟩ : syracuseStep 3932063 = 5898095) B5898095
theorem B3784691 : Blo 1164640 3784691 := bstep (se 1 (by rfl) ⟨2838518, by rfl⟩ : syracuseStep 3784691 = 5677037) B5677037
theorem B11960423 : Blo 1164640 11960423 := bstep (se 1 (by rfl) ⟨8970317, by rfl⟩ : syracuseStep 11960423 = 17940635) B17940635
theorem B4202617 : Blo 1164640 4202617 := bstep (se 2 (by rfl) ⟨1575981, by rfl⟩ : syracuseStep 4202617 = 3151963) B3151963
theorem B3932495 : Blo 1164640 3932495 := bstep (se 1 (by rfl) ⟨2949371, by rfl⟩ : syracuseStep 3932495 = 5898743) B5898743
theorem B51118573 : Blo 1164640 51118573 := bstep (se 3 (by rfl) ⟨9584732, by rfl⟩ : syracuseStep 51118573 = 19169465) B19169465
theorem B2622203 : Blo 1164640 2622203 := bstep (se 1 (by rfl) ⟨1966652, by rfl⟩ : syracuseStep 2622203 = 3933305) B3933305
theorem B5112575 : Blo 1164640 5112575 := bstep (se 1 (by rfl) ⟨3834431, by rfl⟩ : syracuseStep 5112575 = 7668863) B7668863
theorem B56705903 : Blo 1164640 56705903 := bstep (se 1 (by rfl) ⟨42529427, by rfl⟩ : syracuseStep 56705903 = 85058855) B85058855
theorem B1311727 : Blo 1164640 1311727 := bstep (se 1 (by rfl) ⟨983795, by rfl⟩ : syracuseStep 1311727 = 1967591) B1967591
theorem B2622761 : Blo 1164640 2622761 := bstep (se 2 (by rfl) ⟨983535, by rfl⟩ : syracuseStep 2622761 = 1967071) B1967071
theorem B1164671 : Blo 1164640 1164671 := bstep (se 1 (by rfl) ⟨873503, by rfl⟩ : syracuseStep 1164671 = 1747007) B1747007
theorem B1164703 : Blo 1164640 1164703 := bstep (se 1 (by rfl) ⟨873527, by rfl⟩ : syracuseStep 1164703 = 1747055) B1747055
theorem B1312159 : Blo 1164640 1312159 := bstep (se 1 (by rfl) ⟨984119, by rfl⟩ : syracuseStep 1312159 = 1968239) B1968239
theorem B1164847 : Blo 1164640 1164847 := bstep (se 1 (by rfl) ⟨873635, by rfl⟩ : syracuseStep 1164847 = 1747271) B1747271
theorem B1165159 : Blo 1164640 1165159 := bstep (se 1 (by rfl) ⟨873869, by rfl⟩ : syracuseStep 1165159 = 1747739) B1747739
theorem B31909787 : Blo 1164640 31909787 := bstep (se 1 (by rfl) ⟨23932340, by rfl⟩ : syracuseStep 31909787 = 47864681) B47864681
theorem B28370857 : Blo 1164640 28370857 := bstep (se 2 (by rfl) ⟨10639071, by rfl⟩ : syracuseStep 28370857 = 21278143) B21278143
theorem B2213867 : Blo 1164640 2213867 := bstep (se 1 (by rfl) ⟨1660400, by rfl⟩ : syracuseStep 2213867 = 3320801) B3320801
theorem B1165311 : Blo 1164640 1165311 := bstep (se 1 (by rfl) ⟨873983, by rfl⟩ : syracuseStep 1165311 = 1747967) B1747967
theorem B1165403 : Blo 1164640 1165403 := bstep (se 1 (by rfl) ⟨874052, by rfl⟩ : syracuseStep 1165403 = 1748105) B1748105
theorem B1165439 : Blo 1164640 1165439 := bstep (se 1 (by rfl) ⟨874079, by rfl⟩ : syracuseStep 1165439 = 1748159) B1748159
theorem B21563729 : Blo 1164640 21563729 := bstep (se 2 (by rfl) ⟨8086398, by rfl⟩ : syracuseStep 21563729 = 16172797) B16172797
theorem B1165727 : Blo 1164640 1165727 := bstep (se 1 (by rfl) ⟨874295, by rfl⟩ : syracuseStep 1165727 = 1748591) B1748591
theorem B1165759 : Blo 1164640 1165759 := bstep (se 1 (by rfl) ⟨874319, by rfl⟩ : syracuseStep 1165759 = 1748639) B1748639
theorem B1165799 : Blo 1164640 1165799 := bstep (se 1 (by rfl) ⟨874349, by rfl⟩ : syracuseStep 1165799 = 1748699) B1748699
theorem B1747691 : Blo 1164640 1747691 := bstep (se 1 (by rfl) ⟨1310768, by rfl⟩ : syracuseStep 1747691 = 2621537) B2621537
theorem B4975357 : Blo 1164640 4975357 := bstep (se 3 (by rfl) ⟨932879, by rfl⟩ : syracuseStep 4975357 = 1865759) B1865759
theorem B1166247 : Blo 1164640 1166247 := bstep (se 1 (by rfl) ⟨874685, by rfl⟩ : syracuseStep 1166247 = 1749371) B1749371
theorem B1166319 : Blo 1164640 1166319 := bstep (se 1 (by rfl) ⟨874739, by rfl⟩ : syracuseStep 1166319 = 1749479) B1749479
theorem B47852531 : Blo 1164640 47852531 := bstep (se 1 (by rfl) ⟨35889398, by rfl⟩ : syracuseStep 47852531 = 71778797) B71778797
theorem B3935303 : Blo 1164640 3935303 := bstep (se 1 (by rfl) ⟨2951477, by rfl⟩ : syracuseStep 3935303 = 5902955) B5902955
theorem B1748327 : Blo 1164640 1748327 := bstep (se 1 (by rfl) ⟨1311245, by rfl⟩ : syracuseStep 1748327 = 2622491) B2622491
theorem B1748687 : Blo 1164640 1748687 := bstep (se 1 (by rfl) ⟨1311515, by rfl⟩ : syracuseStep 1748687 = 2623031) B2623031
theorem B1748735 : Blo 1164640 1748735 := bstep (se 1 (by rfl) ⟨1311551, by rfl⟩ : syracuseStep 1748735 = 2623103) B2623103
theorem B726413417 : Blo 1164640 726413417 := bstep (se 2 (by rfl) ⟨272405031, by rfl⟩ : syracuseStep 726413417 = 544810063) B544810063
theorem B3936491 : Blo 1164640 3936491 := bstep (se 1 (by rfl) ⟨2952368, by rfl⟩ : syracuseStep 3936491 = 5904737) B5904737
theorem B1659199 : Blo 1164640 1659199 := bstep (se 1 (by rfl) ⟨1244399, by rfl⟩ : syracuseStep 1659199 = 2488799) B2488799
theorem B1749503 : Blo 1164640 1749503 := bstep (se 1 (by rfl) ⟨1312127, by rfl⟩ : syracuseStep 1749503 = 2624255) B2624255
theorem B4199273 : Blo 1164640 4199273 := bstep (se 2 (by rfl) ⟨1574727, by rfl⟩ : syracuseStep 4199273 = 3149455) B3149455
theorem B5600315 : Blo 1164640 5600315 := bstep (se 1 (by rfl) ⟨4200236, by rfl⟩ : syracuseStep 5600315 = 8400473) B8400473
theorem B2693287 : Blo 1164640 2693287 := bstep (se 1 (by rfl) ⟨2019965, by rfl⟩ : syracuseStep 2693287 = 4039931) B4039931
theorem B4488301 : Blo 1164640 4488301 := bstep (se 3 (by rfl) ⟨841556, by rfl⟩ : syracuseStep 4488301 = 1683113) B1683113
theorem B2620655 : Blo 1164640 2620655 := bstep (se 1 (by rfl) ⟨1965491, by rfl⟩ : syracuseStep 2620655 = 3930983) B3930983
theorem B3931631 : Blo 1164640 3931631 := bstep (se 1 (by rfl) ⟨2948723, by rfl⟩ : syracuseStep 3931631 = 5897447) B5897447
theorem B181559069 : Blo 1164640 181559069 := bstep (se 3 (by rfl) ⟨34042325, by rfl⟩ : syracuseStep 181559069 = 68084651) B68084651
theorem B2621375 : Blo 1164640 2621375 := bstep (se 1 (by rfl) ⟨1966031, by rfl⟩ : syracuseStep 2621375 = 3932063) B3932063
theorem B10092509 : Blo 1164640 10092509 := bstep (se 3 (by rfl) ⟨1892345, by rfl⟩ : syracuseStep 10092509 = 3784691) B3784691
theorem B5603489 : Blo 1164640 5603489 := bstep (se 2 (by rfl) ⟨2101308, by rfl⟩ : syracuseStep 5603489 = 4202617) B4202617
theorem B2621663 : Blo 1164640 2621663 := bstep (se 1 (by rfl) ⟨1966247, by rfl⟩ : syracuseStep 2621663 = 3932495) B3932495
theorem B2212265 : Blo 1164640 2212265 := bstep (se 2 (by rfl) ⟨829599, by rfl⟩ : syracuseStep 2212265 = 1659199) B1659199
theorem B3408383 : Blo 1164640 3408383 := bstep (se 1 (by rfl) ⟨2556287, by rfl⟩ : syracuseStep 3408383 = 5112575) B5112575
theorem B23937605 : Blo 1164640 23937605 := bstep (se 4 (by rfl) ⟨2244150, by rfl⟩ : syracuseStep 23937605 = 4488301) B4488301
theorem B68158097 : Blo 1164640 68158097 := bstep (se 2 (by rfl) ⟨25559286, by rfl⟩ : syracuseStep 68158097 = 51118573) B51118573
theorem B1475911 : Blo 1164640 1475911 := bstep (se 1 (by rfl) ⟨1106933, by rfl⟩ : syracuseStep 1475911 = 2213867) B2213867
theorem B1165127 : Blo 1164640 1165127 := bstep (se 1 (by rfl) ⟨873845, by rfl⟩ : syracuseStep 1165127 = 1747691) B1747691
theorem B31901687 : Blo 1164640 31901687 := bstep (se 1 (by rfl) ⟨23926265, by rfl⟩ : syracuseStep 31901687 = 47852531) B47852531
theorem B2623535 : Blo 1164640 2623535 := bstep (se 1 (by rfl) ⟨1967651, by rfl⟩ : syracuseStep 2623535 = 3935303) B3935303
theorem B1747103 : Blo 1164640 1747103 := bstep (se 1 (by rfl) ⟨1310327, by rfl⟩ : syracuseStep 1747103 = 2620655) B2620655
theorem B1165551 : Blo 1164640 1165551 := bstep (se 1 (by rfl) ⟨874163, by rfl⟩ : syracuseStep 1165551 = 1748327) B1748327
theorem B1165791 : Blo 1164640 1165791 := bstep (se 1 (by rfl) ⟨874343, by rfl⟩ : syracuseStep 1165791 = 1748687) B1748687
theorem B1165823 : Blo 1164640 1165823 := bstep (se 1 (by rfl) ⟨874367, by rfl⟩ : syracuseStep 1165823 = 1748735) B1748735
theorem B121039379 : Blo 1164640 121039379 := bstep (se 1 (by rfl) ⟨90779534, by rfl⟩ : syracuseStep 121039379 = 181559069) B181559069
theorem B1747583 : Blo 1164640 1747583 := bstep (se 1 (by rfl) ⟨1310687, by rfl⟩ : syracuseStep 1747583 = 2621375) B2621375
theorem B6728339 : Blo 1164640 6728339 := bstep (se 1 (by rfl) ⟨5046254, by rfl⟩ : syracuseStep 6728339 = 10092509) B10092509
theorem B7973615 : Blo 1164640 7973615 := bstep (se 1 (by rfl) ⟨5980211, by rfl⟩ : syracuseStep 7973615 = 11960423) B11960423
theorem B2624327 : Blo 1164640 2624327 := bstep (se 1 (by rfl) ⟨1968245, by rfl⟩ : syracuseStep 2624327 = 3936491) B3936491
theorem B3591049 : Blo 1164640 3591049 := bstep (se 2 (by rfl) ⟨1346643, by rfl⟩ : syracuseStep 3591049 = 2693287) B2693287
theorem B1166335 : Blo 1164640 1166335 := bstep (se 1 (by rfl) ⟨874751, by rfl⟩ : syracuseStep 1166335 = 1749503) B1749503
theorem B1748135 : Blo 1164640 1748135 := bstep (se 1 (by rfl) ⟨1311101, by rfl⟩ : syracuseStep 1748135 = 2622203) B2622203
theorem B1748507 : Blo 1164640 1748507 := bstep (se 1 (by rfl) ⟨1311380, by rfl⟩ : syracuseStep 1748507 = 2622761) B2622761
theorem B1748969 : Blo 1164640 1748969 := bstep (se 2 (by rfl) ⟨655863, by rfl⟩ : syracuseStep 1748969 = 1311727) B1311727
theorem B1749545 : Blo 1164640 1749545 := bstep (se 2 (by rfl) ⟨656079, by rfl⟩ : syracuseStep 1749545 = 1312159) B1312159
theorem B37827809 : Blo 1164640 37827809 := bstep (se 2 (by rfl) ⟨14185428, by rfl⟩ : syracuseStep 37827809 = 28370857) B28370857
theorem B484275611 : Blo 1164640 484275611 := bstep (se 1 (by rfl) ⟨363206708, by rfl⟩ : syracuseStep 484275611 = 726413417) B726413417
theorem B2799515 : Blo 1164640 2799515 := bstep (se 1 (by rfl) ⟨2099636, by rfl⟩ : syracuseStep 2799515 = 4199273) B4199273
theorem B37803935 : Blo 1164640 37803935 := bstep (se 1 (by rfl) ⟨28352951, by rfl⟩ : syracuseStep 37803935 = 56705903) B56705903
theorem B3733543 : Blo 1164640 3733543 := bstep (se 1 (by rfl) ⟨2800157, by rfl⟩ : syracuseStep 3733543 = 5600315) B5600315
theorem B6633809 : Blo 1164640 6633809 := bstep (se 2 (by rfl) ⟨2487678, by rfl⟩ : syracuseStep 6633809 = 4975357) B4975357
theorem B21273191 : Blo 1164640 21273191 := bstep (se 1 (by rfl) ⟨15954893, by rfl⟩ : syracuseStep 21273191 = 31909787) B31909787
theorem B14375819 : Blo 1164640 14375819 := bstep (se 1 (by rfl) ⟨10781864, by rfl⟩ : syracuseStep 14375819 = 21563729) B21563729
theorem B2621087 : Blo 1164640 2621087 := bstep (se 1 (by rfl) ⟨1965815, by rfl⟩ : syracuseStep 2621087 = 3931631) B3931631
theorem B3735659 : Blo 1164640 3735659 := bstep (se 1 (by rfl) ⟨2801744, by rfl⟩ : syracuseStep 3735659 = 5603489) B5603489
theorem B1474843 : Blo 1164640 1474843 := bstep (se 1 (by rfl) ⟨1106132, by rfl⟩ : syracuseStep 1474843 = 2212265) B2212265
theorem B15958403 : Blo 1164640 15958403 := bstep (se 1 (by rfl) ⟨11968802, by rfl⟩ : syracuseStep 15958403 = 23937605) B23937605
theorem B21267791 : Blo 1164640 21267791 := bstep (se 1 (by rfl) ⟨15950843, by rfl⟩ : syracuseStep 21267791 = 31901687) B31901687
theorem B1164735 : Blo 1164640 1164735 := bstep (se 1 (by rfl) ⟨873551, by rfl⟩ : syracuseStep 1164735 = 1747103) B1747103
theorem B80692919 : Blo 1164640 80692919 := bstep (se 1 (by rfl) ⟨60519689, by rfl⟩ : syracuseStep 80692919 = 121039379) B121039379
theorem B14182127 : Blo 1164640 14182127 := bstep (se 1 (by rfl) ⟨10636595, by rfl⟩ : syracuseStep 14182127 = 21273191) B21273191
theorem B1165055 : Blo 1164640 1165055 := bstep (se 1 (by rfl) ⟨873791, by rfl⟩ : syracuseStep 1165055 = 1747583) B1747583
theorem B1967881 : Blo 1164640 1967881 := bstep (se 2 (by rfl) ⟨737955, by rfl⟩ : syracuseStep 1967881 = 1475911) B1475911
theorem B1165423 : Blo 1164640 1165423 := bstep (se 1 (by rfl) ⟨874067, by rfl⟩ : syracuseStep 1165423 = 1748135) B1748135
theorem B1165671 : Blo 1164640 1165671 := bstep (se 1 (by rfl) ⟨874253, by rfl⟩ : syracuseStep 1165671 = 1748507) B1748507
theorem B1747391 : Blo 1164640 1747391 := bstep (se 1 (by rfl) ⟨1310543, by rfl⟩ : syracuseStep 1747391 = 2621087) B2621087
theorem B1165979 : Blo 1164640 1165979 := bstep (se 1 (by rfl) ⟨874484, by rfl⟩ : syracuseStep 1165979 = 1748969) B1748969
theorem B1747775 : Blo 1164640 1747775 := bstep (se 1 (by rfl) ⟨1310831, by rfl⟩ : syracuseStep 1747775 = 2621663) B2621663
theorem B2272255 : Blo 1164640 2272255 := bstep (se 1 (by rfl) ⟨1704191, by rfl⟩ : syracuseStep 2272255 = 3408383) B3408383
theorem B1166363 : Blo 1164640 1166363 := bstep (se 1 (by rfl) ⟨874772, by rfl⟩ : syracuseStep 1166363 = 1749545) B1749545
theorem B25218539 : Blo 1164640 25218539 := bstep (se 1 (by rfl) ⟨18913904, by rfl⟩ : syracuseStep 25218539 = 37827809) B37827809
theorem B4788065 : Blo 1164640 4788065 := bstep (se 2 (by rfl) ⟨1795524, by rfl⟩ : syracuseStep 4788065 = 3591049) B3591049
theorem B25202623 : Blo 1164640 25202623 := bstep (se 1 (by rfl) ⟨18901967, by rfl⟩ : syracuseStep 25202623 = 37803935) B37803935
theorem B1749023 : Blo 1164640 1749023 := bstep (se 1 (by rfl) ⟨1311767, by rfl⟩ : syracuseStep 1749023 = 2623535) B2623535
theorem B4485559 : Blo 1164640 4485559 := bstep (se 1 (by rfl) ⟨3364169, by rfl⟩ : syracuseStep 4485559 = 6728339) B6728339
theorem B1749551 : Blo 1164640 1749551 := bstep (se 1 (by rfl) ⟨1312163, by rfl⟩ : syracuseStep 1749551 = 2624327) B2624327
theorem B4978057 : Blo 1164640 4978057 := bstep (se 2 (by rfl) ⟨1866771, by rfl⟩ : syracuseStep 4978057 = 3733543) B3733543
theorem B45438731 : Blo 1164640 45438731 := bstep (se 1 (by rfl) ⟨34079048, by rfl⟩ : syracuseStep 45438731 = 68158097) B68158097
theorem B1291401629 : Blo 1164640 1291401629 := bstep (se 3 (by rfl) ⟨242137805, by rfl⟩ : syracuseStep 1291401629 = 484275611) B484275611
theorem B1866343 : Blo 1164640 1866343 := bstep (se 1 (by rfl) ⟨1399757, by rfl⟩ : syracuseStep 1866343 = 2799515) B2799515
theorem B4422539 : Blo 1164640 4422539 := bstep (se 1 (by rfl) ⟨3316904, by rfl⟩ : syracuseStep 4422539 = 6633809) B6633809
theorem B5315743 : Blo 1164640 5315743 := bstep (se 1 (by rfl) ⟨3986807, by rfl⟩ : syracuseStep 5315743 = 7973615) B7973615
theorem B9583879 : Blo 1164640 9583879 := bstep (se 1 (by rfl) ⟨7187909, by rfl⟩ : syracuseStep 9583879 = 14375819) B14375819
theorem B2490439 : Blo 1164640 2490439 := bstep (se 1 (by rfl) ⟨1867829, by rfl⟩ : syracuseStep 2490439 = 3735659) B3735659
theorem B1966457 : Blo 1164640 1966457 := bstep (se 2 (by rfl) ⟨737421, by rfl⟩ : syracuseStep 1966457 = 1474843) B1474843
theorem B5980745 : Blo 1164640 5980745 := bstep (se 2 (by rfl) ⟨2242779, by rfl⟩ : syracuseStep 5980745 = 4485559) B4485559
theorem B9454751 : Blo 1164640 9454751 := bstep (se 1 (by rfl) ⟨7091063, by rfl⟩ : syracuseStep 9454751 = 14182127) B14182127
theorem B7087657 : Blo 1164640 7087657 := bstep (se 2 (by rfl) ⟨2657871, by rfl⟩ : syracuseStep 7087657 = 5315743) B5315743
theorem B1164927 : Blo 1164640 1164927 := bstep (se 1 (by rfl) ⟨873695, by rfl⟩ : syracuseStep 1164927 = 1747391) B1747391
theorem B6637409 : Blo 1164640 6637409 := bstep (se 2 (by rfl) ⟨2489028, by rfl⟩ : syracuseStep 6637409 = 4978057) B4978057
theorem B1165183 : Blo 1164640 1165183 := bstep (se 1 (by rfl) ⟨873887, by rfl⟩ : syracuseStep 1165183 = 1747775) B1747775
theorem B16812359 : Blo 1164640 16812359 := bstep (se 1 (by rfl) ⟨12609269, by rfl⟩ : syracuseStep 16812359 = 25218539) B25218539
theorem B2623841 : Blo 1164640 2623841 := bstep (se 2 (by rfl) ⟨983940, by rfl⟩ : syracuseStep 2623841 = 1967881) B1967881
theorem B48474773 : Blo 1164640 48474773 := bstep (se 6 (by rfl) ⟨1136127, by rfl⟩ : syracuseStep 48474773 = 2272255) B2272255
theorem B1166015 : Blo 1164640 1166015 := bstep (se 1 (by rfl) ⟨874511, by rfl⟩ : syracuseStep 1166015 = 1749023) B1749023
theorem B1166367 : Blo 1164640 1166367 := bstep (se 1 (by rfl) ⟨874775, by rfl⟩ : syracuseStep 1166367 = 1749551) B1749551
theorem B860934419 : Blo 1164640 860934419 := bstep (se 1 (by rfl) ⟨645700814, by rfl⟩ : syracuseStep 860934419 = 1291401629) B1291401629
theorem B3192043 : Blo 1164640 3192043 := bstep (se 1 (by rfl) ⟨2394032, by rfl⟩ : syracuseStep 3192043 = 4788065) B4788065
theorem B10638935 : Blo 1164640 10638935 := bstep (se 1 (by rfl) ⟨7979201, by rfl⟩ : syracuseStep 10638935 = 15958403) B15958403
theorem B2488457 : Blo 1164640 2488457 := bstep (se 2 (by rfl) ⟨933171, by rfl⟩ : syracuseStep 2488457 = 1866343) B1866343
theorem B14178527 : Blo 1164640 14178527 := bstep (se 1 (by rfl) ⟨10633895, by rfl⟩ : syracuseStep 14178527 = 21267791) B21267791
theorem B53795279 : Blo 1164640 53795279 := bstep (se 1 (by rfl) ⟨40346459, by rfl⟩ : syracuseStep 53795279 = 80692919) B80692919
theorem B30292487 : Blo 1164640 30292487 := bstep (se 1 (by rfl) ⟨22719365, by rfl⟩ : syracuseStep 30292487 = 45438731) B45438731
theorem B12778505 : Blo 1164640 12778505 := bstep (se 2 (by rfl) ⟨4791939, by rfl⟩ : syracuseStep 12778505 = 9583879) B9583879
theorem B2948359 : Blo 1164640 2948359 := bstep (se 1 (by rfl) ⟨2211269, by rfl⟩ : syracuseStep 2948359 = 4422539) B4422539
theorem B33603497 : Blo 1164640 33603497 := bstep (se 2 (by rfl) ⟨12601311, by rfl⟩ : syracuseStep 33603497 = 25202623) B25202623
theorem B573956279 : Blo 1164640 573956279 := bstep (se 1 (by rfl) ⟨430467209, by rfl⟩ : syracuseStep 573956279 = 860934419) B860934419
theorem B1310971 : Blo 1164640 1310971 := bstep (se 1 (by rfl) ⟨983228, by rfl⟩ : syracuseStep 1310971 = 1966457) B1966457
theorem B4424939 : Blo 1164640 4424939 := bstep (se 1 (by rfl) ⟨3318704, by rfl⟩ : syracuseStep 4424939 = 6637409) B6637409
theorem B11208239 : Blo 1164640 11208239 := bstep (se 1 (by rfl) ⟨8406179, by rfl⟩ : syracuseStep 11208239 = 16812359) B16812359
theorem B20194991 : Blo 1164640 20194991 := bstep (se 1 (by rfl) ⟨15146243, by rfl⟩ : syracuseStep 20194991 = 30292487) B30292487
theorem B3320585 : Blo 1164640 3320585 := bstep (se 2 (by rfl) ⟨1245219, by rfl⟩ : syracuseStep 3320585 = 2490439) B2490439
theorem B6303167 : Blo 1164640 6303167 := bstep (se 1 (by rfl) ⟨4727375, by rfl⟩ : syracuseStep 6303167 = 9454751) B9454751
theorem B1658971 : Blo 1164640 1658971 := bstep (se 1 (by rfl) ⟨1244228, by rfl⟩ : syracuseStep 1658971 = 2488457) B2488457
theorem B1749227 : Blo 1164640 1749227 := bstep (se 1 (by rfl) ⟨1311920, by rfl⟩ : syracuseStep 1749227 = 2623841) B2623841
theorem B4256057 : Blo 1164640 4256057 := bstep (se 2 (by rfl) ⟨1596021, by rfl⟩ : syracuseStep 4256057 = 3192043) B3192043
theorem B9450209 : Blo 1164640 9450209 := bstep (se 2 (by rfl) ⟨3543828, by rfl⟩ : syracuseStep 9450209 = 7087657) B7087657
theorem B22402331 : Blo 1164640 22402331 := bstep (se 1 (by rfl) ⟨16801748, by rfl⟩ : syracuseStep 22402331 = 33603497) B33603497
theorem B3987163 : Blo 1164640 3987163 := bstep (se 1 (by rfl) ⟨2990372, by rfl⟩ : syracuseStep 3987163 = 5980745) B5980745
theorem B7092623 : Blo 1164640 7092623 := bstep (se 1 (by rfl) ⟨5319467, by rfl⟩ : syracuseStep 7092623 = 10638935) B10638935
theorem B9452351 : Blo 1164640 9452351 := bstep (se 1 (by rfl) ⟨7089263, by rfl⟩ : syracuseStep 9452351 = 14178527) B14178527
theorem B35863519 : Blo 1164640 35863519 := bstep (se 1 (by rfl) ⟨26897639, by rfl⟩ : syracuseStep 35863519 = 53795279) B53795279
theorem B3931145 : Blo 1164640 3931145 := bstep (se 2 (by rfl) ⟨1474179, by rfl⟩ : syracuseStep 3931145 = 2948359) B2948359
theorem B32316515 : Blo 1164640 32316515 := bstep (se 1 (by rfl) ⟨24237386, by rfl⟩ : syracuseStep 32316515 = 48474773) B48474773
theorem B8519003 : Blo 1164640 8519003 := bstep (se 1 (by rfl) ⟨6389252, by rfl⟩ : syracuseStep 8519003 = 12778505) B12778505
theorem B2211961 : Blo 1164640 2211961 := bstep (se 2 (by rfl) ⟨829485, by rfl⟩ : syracuseStep 2211961 = 1658971) B1658971
theorem B6300139 : Blo 1164640 6300139 := bstep (se 1 (by rfl) ⟨4725104, by rfl⟩ : syracuseStep 6300139 = 9450209) B9450209
theorem B2949959 : Blo 1164640 2949959 := bstep (se 1 (by rfl) ⟨2212469, by rfl⟩ : syracuseStep 2949959 = 4424939) B4424939
theorem B14934887 : Blo 1164640 14934887 := bstep (se 1 (by rfl) ⟨11201165, by rfl⟩ : syracuseStep 14934887 = 22402331) B22402331
theorem B7472159 : Blo 1164640 7472159 := bstep (se 1 (by rfl) ⟨5604119, by rfl⟩ : syracuseStep 7472159 = 11208239) B11208239
theorem B47818025 : Blo 1164640 47818025 := bstep (se 2 (by rfl) ⟨17931759, by rfl⟩ : syracuseStep 47818025 = 35863519) B35863519
theorem B4728415 : Blo 1164640 4728415 := bstep (se 1 (by rfl) ⟨3546311, by rfl⟩ : syracuseStep 4728415 = 7092623) B7092623
theorem B2213723 : Blo 1164640 2213723 := bstep (se 1 (by rfl) ⟨1660292, by rfl⟩ : syracuseStep 2213723 = 3320585) B3320585
theorem B6301567 : Blo 1164640 6301567 := bstep (se 1 (by rfl) ⟨4726175, by rfl⟩ : syracuseStep 6301567 = 9452351) B9452351
theorem B5679335 : Blo 1164640 5679335 := bstep (se 1 (by rfl) ⟨4259501, by rfl⟩ : syracuseStep 5679335 = 8519003) B8519003
theorem B1166151 : Blo 1164640 1166151 := bstep (se 1 (by rfl) ⟨874613, by rfl⟩ : syracuseStep 1166151 = 1749227) B1749227
theorem B2837371 : Blo 1164640 2837371 := bstep (se 1 (by rfl) ⟨2128028, by rfl⟩ : syracuseStep 2837371 = 4256057) B4256057
theorem B1747961 : Blo 1164640 1747961 := bstep (se 2 (by rfl) ⟨655485, by rfl⟩ : syracuseStep 1747961 = 1310971) B1310971
theorem B13463327 : Blo 1164640 13463327 := bstep (se 1 (by rfl) ⟨10097495, by rfl⟩ : syracuseStep 13463327 = 20194991) B20194991
theorem B382637519 : Blo 1164640 382637519 := bstep (se 1 (by rfl) ⟨286978139, by rfl⟩ : syracuseStep 382637519 = 573956279) B573956279
theorem B21264869 : Blo 1164640 21264869 := bstep (se 4 (by rfl) ⟨1993581, by rfl⟩ : syracuseStep 21264869 = 3987163) B3987163
theorem B2620763 : Blo 1164640 2620763 := bstep (se 1 (by rfl) ⟨1965572, by rfl⟩ : syracuseStep 2620763 = 3931145) B3931145
theorem B21544343 : Blo 1164640 21544343 := bstep (se 1 (by rfl) ⟨16158257, by rfl⟩ : syracuseStep 21544343 = 32316515) B32316515
theorem B4202111 : Blo 1164640 4202111 := bstep (se 1 (by rfl) ⟨3151583, by rfl⟩ : syracuseStep 4202111 = 6303167) B6303167
theorem B2949281 : Blo 1164640 2949281 := bstep (se 2 (by rfl) ⟨1105980, by rfl⟩ : syracuseStep 2949281 = 2211961) B2211961
theorem B1966639 : Blo 1164640 1966639 := bstep (se 1 (by rfl) ⟨1474979, by rfl⟩ : syracuseStep 1966639 = 2949959) B2949959
theorem B4981439 : Blo 1164640 4981439 := bstep (se 1 (by rfl) ⟨3736079, by rfl⟩ : syracuseStep 4981439 = 7472159) B7472159
theorem B255091679 : Blo 1164640 255091679 := bstep (se 1 (by rfl) ⟨191318759, by rfl⟩ : syracuseStep 255091679 = 382637519) B382637519
theorem B1475815 : Blo 1164640 1475815 := bstep (se 1 (by rfl) ⟨1106861, by rfl⟩ : syracuseStep 1475815 = 2213723) B2213723
theorem B1165307 : Blo 1164640 1165307 := bstep (se 1 (by rfl) ⟨873980, by rfl⟩ : syracuseStep 1165307 = 1747961) B1747961
theorem B1747175 : Blo 1164640 1747175 := bstep (se 1 (by rfl) ⟨1310381, by rfl⟩ : syracuseStep 1747175 = 2620763) B2620763
theorem B14362895 : Blo 1164640 14362895 := bstep (se 1 (by rfl) ⟨10772171, by rfl⟩ : syracuseStep 14362895 = 21544343) B21544343
theorem B9956591 : Blo 1164640 9956591 := bstep (se 1 (by rfl) ⟨7467443, by rfl⟩ : syracuseStep 9956591 = 14934887) B14934887
theorem B8400185 : Blo 1164640 8400185 := bstep (se 2 (by rfl) ⟨3150069, by rfl⟩ : syracuseStep 8400185 = 6300139) B6300139
theorem B31878683 : Blo 1164640 31878683 := bstep (se 1 (by rfl) ⟨23909012, by rfl⟩ : syracuseStep 31878683 = 47818025) B47818025
theorem B14176579 : Blo 1164640 14176579 := bstep (se 1 (by rfl) ⟨10632434, by rfl⟩ : syracuseStep 14176579 = 21264869) B21264869
theorem B6304553 : Blo 1164640 6304553 := bstep (se 2 (by rfl) ⟨2364207, by rfl⟩ : syracuseStep 6304553 = 4728415) B4728415
theorem B8402089 : Blo 1164640 8402089 := bstep (se 2 (by rfl) ⟨3150783, by rfl⟩ : syracuseStep 8402089 = 6301567) B6301567
theorem B8975551 : Blo 1164640 8975551 := bstep (se 1 (by rfl) ⟨6731663, by rfl⟩ : syracuseStep 8975551 = 13463327) B13463327
theorem B15144893 : Blo 1164640 15144893 := bstep (se 3 (by rfl) ⟨2839667, by rfl⟩ : syracuseStep 15144893 = 5679335) B5679335
theorem B3783161 : Blo 1164640 3783161 := bstep (se 2 (by rfl) ⟨1418685, by rfl⟩ : syracuseStep 3783161 = 2837371) B2837371
theorem B2801407 : Blo 1164640 2801407 := bstep (se 1 (by rfl) ⟨2101055, by rfl⟩ : syracuseStep 2801407 = 4202111) B4202111
theorem B1966187 : Blo 1164640 1966187 := bstep (se 1 (by rfl) ⟨1474640, by rfl⟩ : syracuseStep 1966187 = 2949281) B2949281
theorem B4203035 : Blo 1164640 4203035 := bstep (se 1 (by rfl) ⟨3152276, by rfl⟩ : syracuseStep 4203035 = 6304553) B6304553
theorem B2622185 : Blo 1164640 2622185 := bstep (se 2 (by rfl) ⟨983319, by rfl⟩ : syracuseStep 2622185 = 1966639) B1966639
theorem B1164783 : Blo 1164640 1164783 := bstep (se 1 (by rfl) ⟨873587, by rfl⟩ : syracuseStep 1164783 = 1747175) B1747175
theorem B1967753 : Blo 1164640 1967753 := bstep (se 2 (by rfl) ⟨737907, by rfl⟩ : syracuseStep 1967753 = 1475815) B1475815
theorem B6637727 : Blo 1164640 6637727 := bstep (se 1 (by rfl) ⟨4978295, by rfl⟩ : syracuseStep 6637727 = 9956591) B9956591
theorem B21252455 : Blo 1164640 21252455 := bstep (se 1 (by rfl) ⟨15939341, by rfl⟩ : syracuseStep 21252455 = 31878683) B31878683
theorem B18902105 : Blo 1164640 18902105 := bstep (se 2 (by rfl) ⟨7088289, by rfl⟩ : syracuseStep 18902105 = 14176579) B14176579
theorem B170061119 : Blo 1164640 170061119 := bstep (se 1 (by rfl) ⟨127545839, by rfl⟩ : syracuseStep 170061119 = 255091679) B255091679
theorem B10096595 : Blo 1164640 10096595 := bstep (se 1 (by rfl) ⟨7572446, by rfl⟩ : syracuseStep 10096595 = 15144893) B15144893
theorem B11202785 : Blo 1164640 11202785 := bstep (se 2 (by rfl) ⟨4201044, by rfl⟩ : syracuseStep 11202785 = 8402089) B8402089
theorem B13283837 : Blo 1164640 13283837 := bstep (se 3 (by rfl) ⟨2490719, by rfl⟩ : syracuseStep 13283837 = 4981439) B4981439
theorem B5600123 : Blo 1164640 5600123 := bstep (se 1 (by rfl) ⟨4200092, by rfl⟩ : syracuseStep 5600123 = 8400185) B8400185
theorem B9575263 : Blo 1164640 9575263 := bstep (se 1 (by rfl) ⟨7181447, by rfl⟩ : syracuseStep 9575263 = 14362895) B14362895
theorem B11967401 : Blo 1164640 11967401 := bstep (se 2 (by rfl) ⟨4487775, by rfl⟩ : syracuseStep 11967401 = 8975551) B8975551
theorem B2522107 : Blo 1164640 2522107 := bstep (se 1 (by rfl) ⟨1891580, by rfl⟩ : syracuseStep 2522107 = 3783161) B3783161
theorem B3735209 : Blo 1164640 3735209 := bstep (se 2 (by rfl) ⟨1400703, by rfl⟩ : syracuseStep 3735209 = 2801407) B2801407
theorem B1310791 : Blo 1164640 1310791 := bstep (se 1 (by rfl) ⟨983093, by rfl⟩ : syracuseStep 1310791 = 1966187) B1966187
theorem B8855891 : Blo 1164640 8855891 := bstep (se 1 (by rfl) ⟨6641918, by rfl⟩ : syracuseStep 8855891 = 13283837) B13283837
theorem B2802023 : Blo 1164640 2802023 := bstep (se 1 (by rfl) ⟨2101517, by rfl⟩ : syracuseStep 2802023 = 4203035) B4203035
theorem B1311835 : Blo 1164640 1311835 := bstep (se 1 (by rfl) ⟨983876, by rfl⟩ : syracuseStep 1311835 = 1967753) B1967753
theorem B4425151 : Blo 1164640 4425151 := bstep (se 1 (by rfl) ⟨3318863, by rfl⟩ : syracuseStep 4425151 = 6637727) B6637727
theorem B12601403 : Blo 1164640 12601403 := bstep (se 1 (by rfl) ⟨9451052, by rfl⟩ : syracuseStep 12601403 = 18902105) B18902105
theorem B1748123 : Blo 1164640 1748123 := bstep (se 1 (by rfl) ⟨1311092, by rfl⟩ : syracuseStep 1748123 = 2622185) B2622185
theorem B3362809 : Blo 1164640 3362809 := bstep (se 2 (by rfl) ⟨1261053, by rfl⟩ : syracuseStep 3362809 = 2522107) B2522107
theorem B14168303 : Blo 1164640 14168303 := bstep (se 1 (by rfl) ⟨10626227, by rfl⟩ : syracuseStep 14168303 = 21252455) B21252455
theorem B113374079 : Blo 1164640 113374079 := bstep (se 1 (by rfl) ⟨85030559, by rfl⟩ : syracuseStep 113374079 = 170061119) B170061119
theorem B6731063 : Blo 1164640 6731063 := bstep (se 1 (by rfl) ⟨5048297, by rfl⟩ : syracuseStep 6731063 = 10096595) B10096595
theorem B7468523 : Blo 1164640 7468523 := bstep (se 1 (by rfl) ⟨5601392, by rfl⟩ : syracuseStep 7468523 = 11202785) B11202785
theorem B3733415 : Blo 1164640 3733415 := bstep (se 1 (by rfl) ⟨2800061, by rfl⟩ : syracuseStep 3733415 = 5600123) B5600123
theorem B51068069 : Blo 1164640 51068069 := bstep (se 4 (by rfl) ⟨4787631, by rfl⟩ : syracuseStep 51068069 = 9575263) B9575263
theorem B7978267 : Blo 1164640 7978267 := bstep (se 1 (by rfl) ⟨5983700, by rfl⟩ : syracuseStep 7978267 = 11967401) B11967401
theorem B2490139 : Blo 1164640 2490139 := bstep (se 1 (by rfl) ⟨1867604, by rfl⟩ : syracuseStep 2490139 = 3735209) B3735209
theorem B9445535 : Blo 1164640 9445535 := bstep (se 1 (by rfl) ⟨7084151, by rfl⟩ : syracuseStep 9445535 = 14168303) B14168303
theorem B1868015 : Blo 1164640 1868015 := bstep (se 1 (by rfl) ⟨1401011, by rfl⟩ : syracuseStep 1868015 = 2802023) B2802023
theorem B5900201 : Blo 1164640 5900201 := bstep (se 2 (by rfl) ⟨2212575, by rfl⟩ : syracuseStep 5900201 = 4425151) B4425151
theorem B1165415 : Blo 1164640 1165415 := bstep (se 1 (by rfl) ⟨874061, by rfl⟩ : syracuseStep 1165415 = 1748123) B1748123
theorem B3320185 : Blo 1164640 3320185 := bstep (se 2 (by rfl) ⟨1245069, by rfl⟩ : syracuseStep 3320185 = 2490139) B2490139
theorem B4483745 : Blo 1164640 4483745 := bstep (se 2 (by rfl) ⟨1681404, by rfl⟩ : syracuseStep 4483745 = 3362809) B3362809
theorem B1747721 : Blo 1164640 1747721 := bstep (se 2 (by rfl) ⟨655395, by rfl⟩ : syracuseStep 1747721 = 1310791) B1310791
theorem B75582719 : Blo 1164640 75582719 := bstep (se 1 (by rfl) ⟨56687039, by rfl⟩ : syracuseStep 75582719 = 113374079) B113374079
theorem B8400935 : Blo 1164640 8400935 := bstep (se 1 (by rfl) ⟨6300701, by rfl⟩ : syracuseStep 8400935 = 12601403) B12601403
theorem B1749113 : Blo 1164640 1749113 := bstep (se 2 (by rfl) ⟨655917, by rfl⟩ : syracuseStep 1749113 = 1311835) B1311835
theorem B10637689 : Blo 1164640 10637689 := bstep (se 2 (by rfl) ⟨3989133, by rfl⟩ : syracuseStep 10637689 = 7978267) B7978267
theorem B5903927 : Blo 1164640 5903927 := bstep (se 1 (by rfl) ⟨4427945, by rfl⟩ : syracuseStep 5903927 = 8855891) B8855891
theorem B4487375 : Blo 1164640 4487375 := bstep (se 1 (by rfl) ⟨3365531, by rfl⟩ : syracuseStep 4487375 = 6731063) B6731063
theorem B4979015 : Blo 1164640 4979015 := bstep (se 1 (by rfl) ⟨3734261, by rfl⟩ : syracuseStep 4979015 = 7468523) B7468523
theorem B2488943 : Blo 1164640 2488943 := bstep (se 1 (by rfl) ⟨1866707, by rfl⟩ : syracuseStep 2488943 = 3733415) B3733415
theorem B34045379 : Blo 1164640 34045379 := bstep (se 1 (by rfl) ⟨25534034, by rfl⟩ : syracuseStep 34045379 = 51068069) B51068069
theorem B1245343 : Blo 1164640 1245343 := bstep (se 1 (by rfl) ⟨934007, by rfl⟩ : syracuseStep 1245343 = 1868015) B1868015
theorem B3933467 : Blo 1164640 3933467 := bstep (se 1 (by rfl) ⟨2950100, by rfl⟩ : syracuseStep 3933467 = 5900201) B5900201
theorem B2991583 : Blo 1164640 2991583 := bstep (se 1 (by rfl) ⟨2243687, by rfl⟩ : syracuseStep 2991583 = 4487375) B4487375
theorem B3319343 : Blo 1164640 3319343 := bstep (se 1 (by rfl) ⟨2489507, by rfl⟩ : syracuseStep 3319343 = 4979015) B4979015
theorem B1165147 : Blo 1164640 1165147 := bstep (se 1 (by rfl) ⟨873860, by rfl⟩ : syracuseStep 1165147 = 1747721) B1747721
theorem B1166075 : Blo 1164640 1166075 := bstep (se 1 (by rfl) ⟨874556, by rfl⟩ : syracuseStep 1166075 = 1749113) B1749113
theorem B4426913 : Blo 1164640 4426913 := bstep (se 2 (by rfl) ⟨1660092, by rfl⟩ : syracuseStep 4426913 = 3320185) B3320185
theorem B14183585 : Blo 1164640 14183585 := bstep (se 2 (by rfl) ⟨5318844, by rfl⟩ : syracuseStep 14183585 = 10637689) B10637689
theorem B3935951 : Blo 1164640 3935951 := bstep (se 1 (by rfl) ⟨2951963, by rfl⟩ : syracuseStep 3935951 = 5903927) B5903927
theorem B1659295 : Blo 1164640 1659295 := bstep (se 1 (by rfl) ⟨1244471, by rfl⟩ : syracuseStep 1659295 = 2488943) B2488943
theorem B22696919 : Blo 1164640 22696919 := bstep (se 1 (by rfl) ⟨17022689, by rfl⟩ : syracuseStep 22696919 = 34045379) B34045379
theorem B5600623 : Blo 1164640 5600623 := bstep (se 1 (by rfl) ⟨4200467, by rfl⟩ : syracuseStep 5600623 = 8400935) B8400935
theorem B6297023 : Blo 1164640 6297023 := bstep (se 1 (by rfl) ⟨4722767, by rfl⟩ : syracuseStep 6297023 = 9445535) B9445535
theorem B2989163 : Blo 1164640 2989163 := bstep (se 1 (by rfl) ⟨2241872, by rfl⟩ : syracuseStep 2989163 = 4483745) B4483745
theorem B50388479 : Blo 1164640 50388479 := bstep (se 1 (by rfl) ⟨37791359, by rfl⟩ : syracuseStep 50388479 = 75582719) B75582719
theorem B15131279 : Blo 1164640 15131279 := bstep (se 1 (by rfl) ⟨11348459, by rfl⟩ : syracuseStep 15131279 = 22696919) B22696919
theorem B2622311 : Blo 1164640 2622311 := bstep (se 1 (by rfl) ⟨1966733, by rfl⟩ : syracuseStep 2622311 = 3933467) B3933467
theorem B2212895 : Blo 1164640 2212895 := bstep (se 1 (by rfl) ⟨1659671, by rfl⟩ : syracuseStep 2212895 = 3319343) B3319343
theorem B1992775 : Blo 1164640 1992775 := bstep (se 1 (by rfl) ⟨1494581, by rfl⟩ : syracuseStep 1992775 = 2989163) B2989163
theorem B2951275 : Blo 1164640 2951275 := bstep (se 1 (by rfl) ⟨2213456, by rfl⟩ : syracuseStep 2951275 = 4426913) B4426913
theorem B9455723 : Blo 1164640 9455723 := bstep (se 1 (by rfl) ⟨7091792, by rfl⟩ : syracuseStep 9455723 = 14183585) B14183585
theorem B8849573 : Blo 1164640 8849573 := bstep (se 4 (by rfl) ⟨829647, by rfl⟩ : syracuseStep 8849573 = 1659295) B1659295
theorem B2623967 : Blo 1164640 2623967 := bstep (se 1 (by rfl) ⟨1967975, by rfl⟩ : syracuseStep 2623967 = 3935951) B3935951
theorem B4198015 : Blo 1164640 4198015 := bstep (se 1 (by rfl) ⟨3148511, by rfl⟩ : syracuseStep 4198015 = 6297023) B6297023
theorem B7467497 : Blo 1164640 7467497 := bstep (se 2 (by rfl) ⟨2800311, by rfl⟩ : syracuseStep 7467497 = 5600623) B5600623
theorem B33592319 : Blo 1164640 33592319 := bstep (se 1 (by rfl) ⟨25194239, by rfl⟩ : syracuseStep 33592319 = 50388479) B50388479
theorem B1660457 : Blo 1164640 1660457 := bstep (se 2 (by rfl) ⟨622671, by rfl⟩ : syracuseStep 1660457 = 1245343) B1245343
theorem B3988777 : Blo 1164640 3988777 := bstep (se 2 (by rfl) ⟨1495791, by rfl⟩ : syracuseStep 3988777 = 2991583) B2991583
theorem B1475263 : Blo 1164640 1475263 := bstep (se 1 (by rfl) ⟨1106447, by rfl⟩ : syracuseStep 1475263 = 2212895) B2212895
theorem B5899715 : Blo 1164640 5899715 := bstep (se 1 (by rfl) ⟨4424786, by rfl⟩ : syracuseStep 5899715 = 8849573) B8849573
theorem B5318369 : Blo 1164640 5318369 := bstep (se 2 (by rfl) ⟨1994388, by rfl⟩ : syracuseStep 5318369 = 3988777) B3988777
theorem B5597353 : Blo 1164640 5597353 := bstep (se 2 (by rfl) ⟨2099007, by rfl⟩ : syracuseStep 5597353 = 4198015) B4198015
theorem B2657033 : Blo 1164640 2657033 := bstep (se 2 (by rfl) ⟨996387, by rfl⟩ : syracuseStep 2657033 = 1992775) B1992775
theorem B3935033 : Blo 1164640 3935033 := bstep (se 2 (by rfl) ⟨1475637, by rfl⟩ : syracuseStep 3935033 = 2951275) B2951275
theorem B10087519 : Blo 1164640 10087519 := bstep (se 1 (by rfl) ⟨7565639, by rfl⟩ : syracuseStep 10087519 = 15131279) B15131279
theorem B1748207 : Blo 1164640 1748207 := bstep (se 1 (by rfl) ⟨1311155, by rfl⟩ : syracuseStep 1748207 = 2622311) B2622311
theorem B6303815 : Blo 1164640 6303815 := bstep (se 1 (by rfl) ⟨4727861, by rfl⟩ : syracuseStep 6303815 = 9455723) B9455723
theorem B4427885 : Blo 1164640 4427885 := bstep (se 3 (by rfl) ⟨830228, by rfl⟩ : syracuseStep 4427885 = 1660457) B1660457
theorem B1749311 : Blo 1164640 1749311 := bstep (se 1 (by rfl) ⟨1311983, by rfl⟩ : syracuseStep 1749311 = 2623967) B2623967
theorem B4978331 : Blo 1164640 4978331 := bstep (se 1 (by rfl) ⟨3733748, by rfl⟩ : syracuseStep 4978331 = 7467497) B7467497
theorem B22394879 : Blo 1164640 22394879 := bstep (se 1 (by rfl) ⟨16796159, by rfl⟩ : syracuseStep 22394879 = 33592319) B33592319
theorem B4202543 : Blo 1164640 4202543 := bstep (se 1 (by rfl) ⟨3151907, by rfl⟩ : syracuseStep 4202543 = 6303815) B6303815
theorem B29852549 : Blo 1164640 29852549 := bstep (se 4 (by rfl) ⟨2798676, by rfl⟩ : syracuseStep 29852549 = 5597353) B5597353
theorem B1967017 : Blo 1164640 1967017 := bstep (se 2 (by rfl) ⟨737631, by rfl⟩ : syracuseStep 1967017 = 1475263) B1475263
theorem B3933143 : Blo 1164640 3933143 := bstep (se 1 (by rfl) ⟨2949857, by rfl⟩ : syracuseStep 3933143 = 5899715) B5899715
theorem B3318887 : Blo 1164640 3318887 := bstep (se 1 (by rfl) ⟨2489165, by rfl⟩ : syracuseStep 3318887 = 4978331) B4978331
theorem B1771355 : Blo 1164640 1771355 := bstep (se 1 (by rfl) ⟨1328516, by rfl⟩ : syracuseStep 1771355 = 2657033) B2657033
theorem B2623355 : Blo 1164640 2623355 := bstep (se 1 (by rfl) ⟨1967516, by rfl⟩ : syracuseStep 2623355 = 3935033) B3935033
theorem B1165471 : Blo 1164640 1165471 := bstep (se 1 (by rfl) ⟨874103, by rfl⟩ : syracuseStep 1165471 = 1748207) B1748207
theorem B2951923 : Blo 1164640 2951923 := bstep (se 1 (by rfl) ⟨2213942, by rfl⟩ : syracuseStep 2951923 = 4427885) B4427885
theorem B1166207 : Blo 1164640 1166207 := bstep (se 1 (by rfl) ⟨874655, by rfl⟩ : syracuseStep 1166207 = 1749311) B1749311
theorem B14929919 : Blo 1164640 14929919 := bstep (se 1 (by rfl) ⟨11197439, by rfl⟩ : syracuseStep 14929919 = 22394879) B22394879
theorem B3545579 : Blo 1164640 3545579 := bstep (se 1 (by rfl) ⟨2659184, by rfl⟩ : syracuseStep 3545579 = 5318369) B5318369
theorem B13450025 : Blo 1164640 13450025 := bstep (se 2 (by rfl) ⟨5043759, by rfl⟩ : syracuseStep 13450025 = 10087519) B10087519
theorem B11206781 : Blo 1164640 11206781 := bstep (se 3 (by rfl) ⟨2101271, by rfl⟩ : syracuseStep 11206781 = 4202543) B4202543
theorem B2622095 : Blo 1164640 2622095 := bstep (se 1 (by rfl) ⟨1966571, by rfl⟩ : syracuseStep 2622095 = 3933143) B3933143
theorem B2212591 : Blo 1164640 2212591 := bstep (se 1 (by rfl) ⟨1659443, by rfl⟩ : syracuseStep 2212591 = 3318887) B3318887
theorem B2622689 : Blo 1164640 2622689 := bstep (se 2 (by rfl) ⟨983508, by rfl⟩ : syracuseStep 2622689 = 1967017) B1967017
theorem B9454877 : Blo 1164640 9454877 := bstep (se 3 (by rfl) ⟨1772789, by rfl⟩ : syracuseStep 9454877 = 3545579) B3545579
theorem B19901699 : Blo 1164640 19901699 := bstep (se 1 (by rfl) ⟨14926274, by rfl⟩ : syracuseStep 19901699 = 29852549) B29852549
theorem B3935897 : Blo 1164640 3935897 := bstep (se 2 (by rfl) ⟨1475961, by rfl⟩ : syracuseStep 3935897 = 2951923) B2951923
theorem B1748903 : Blo 1164640 1748903 := bstep (se 1 (by rfl) ⟨1311677, by rfl⟩ : syracuseStep 1748903 = 2623355) B2623355
theorem B8966683 : Blo 1164640 8966683 := bstep (se 1 (by rfl) ⟨6725012, by rfl⟩ : syracuseStep 8966683 = 13450025) B13450025
theorem B4723613 : Blo 1164640 4723613 := bstep (se 3 (by rfl) ⟨885677, by rfl⟩ : syracuseStep 4723613 = 1771355) B1771355
theorem B9953279 : Blo 1164640 9953279 := bstep (se 1 (by rfl) ⟨7464959, by rfl⟩ : syracuseStep 9953279 = 14929919) B14929919
theorem B7471187 : Blo 1164640 7471187 := bstep (se 1 (by rfl) ⟨5603390, by rfl⟩ : syracuseStep 7471187 = 11206781) B11206781
theorem B2950121 : Blo 1164640 2950121 := bstep (se 2 (by rfl) ⟨1106295, by rfl⟩ : syracuseStep 2950121 = 2212591) B2212591
theorem B2623931 : Blo 1164640 2623931 := bstep (se 1 (by rfl) ⟨1967948, by rfl⟩ : syracuseStep 2623931 = 3935897) B3935897
theorem B1165935 : Blo 1164640 1165935 := bstep (se 1 (by rfl) ⟨874451, by rfl⟩ : syracuseStep 1165935 = 1748903) B1748903
theorem B1748063 : Blo 1164640 1748063 := bstep (se 1 (by rfl) ⟨1311047, by rfl⟩ : syracuseStep 1748063 = 2622095) B2622095
theorem B3149075 : Blo 1164640 3149075 := bstep (se 1 (by rfl) ⟨2361806, by rfl⟩ : syracuseStep 3149075 = 4723613) B4723613
theorem B1748459 : Blo 1164640 1748459 := bstep (se 1 (by rfl) ⟨1311344, by rfl⟩ : syracuseStep 1748459 = 2622689) B2622689
theorem B6303251 : Blo 1164640 6303251 := bstep (se 1 (by rfl) ⟨4727438, by rfl⟩ : syracuseStep 6303251 = 9454877) B9454877
theorem B13267799 : Blo 1164640 13267799 := bstep (se 1 (by rfl) ⟨9950849, by rfl⟩ : syracuseStep 13267799 = 19901699) B19901699
theorem B47822309 : Blo 1164640 47822309 := bstep (se 4 (by rfl) ⟨4483341, by rfl⟩ : syracuseStep 47822309 = 8966683) B8966683
theorem B6635519 : Blo 1164640 6635519 := bstep (se 1 (by rfl) ⟨4976639, by rfl⟩ : syracuseStep 6635519 = 9953279) B9953279
theorem B4980791 : Blo 1164640 4980791 := bstep (se 1 (by rfl) ⟨3735593, by rfl⟩ : syracuseStep 4980791 = 7471187) B7471187
theorem B1966747 : Blo 1164640 1966747 := bstep (se 1 (by rfl) ⟨1475060, by rfl⟩ : syracuseStep 1966747 = 2950121) B2950121
theorem B8397533 : Blo 1164640 8397533 := bstep (se 3 (by rfl) ⟨1574537, by rfl⟩ : syracuseStep 8397533 = 3149075) B3149075
theorem B1165375 : Blo 1164640 1165375 := bstep (se 1 (by rfl) ⟨874031, by rfl⟩ : syracuseStep 1165375 = 1748063) B1748063
theorem B1165639 : Blo 1164640 1165639 := bstep (se 1 (by rfl) ⟨874229, by rfl⟩ : syracuseStep 1165639 = 1748459) B1748459
theorem B1749287 : Blo 1164640 1749287 := bstep (se 1 (by rfl) ⟨1311965, by rfl⟩ : syracuseStep 1749287 = 2623931) B2623931
theorem B8845199 : Blo 1164640 8845199 := bstep (se 1 (by rfl) ⟨6633899, by rfl⟩ : syracuseStep 8845199 = 13267799) B13267799
theorem B31881539 : Blo 1164640 31881539 := bstep (se 1 (by rfl) ⟨23911154, by rfl⟩ : syracuseStep 31881539 = 47822309) B47822309
theorem B4423679 : Blo 1164640 4423679 := bstep (se 1 (by rfl) ⟨3317759, by rfl⟩ : syracuseStep 4423679 = 6635519) B6635519
theorem B4202167 : Blo 1164640 4202167 := bstep (se 1 (by rfl) ⟨3151625, by rfl⟩ : syracuseStep 4202167 = 6303251) B6303251
theorem B2622329 : Blo 1164640 2622329 := bstep (se 2 (by rfl) ⟨983373, by rfl⟩ : syracuseStep 2622329 = 1966747) B1966747
theorem B2949119 : Blo 1164640 2949119 := bstep (se 1 (by rfl) ⟨2211839, by rfl⟩ : syracuseStep 2949119 = 4423679) B4423679
theorem B3320527 : Blo 1164640 3320527 := bstep (se 1 (by rfl) ⟨2490395, by rfl⟩ : syracuseStep 3320527 = 4980791) B4980791
theorem B1166191 : Blo 1164640 1166191 := bstep (se 1 (by rfl) ⟨874643, by rfl⟩ : syracuseStep 1166191 = 1749287) B1749287
theorem B5598355 : Blo 1164640 5598355 := bstep (se 1 (by rfl) ⟨4198766, by rfl⟩ : syracuseStep 5598355 = 8397533) B8397533
theorem B21254359 : Blo 1164640 21254359 := bstep (se 1 (by rfl) ⟨15940769, by rfl⟩ : syracuseStep 21254359 = 31881539) B31881539
theorem B5896799 : Blo 1164640 5896799 := bstep (se 1 (by rfl) ⟨4422599, by rfl⟩ : syracuseStep 5896799 = 8845199) B8845199
theorem B5602889 : Blo 1164640 5602889 := bstep (se 2 (by rfl) ⟨2101083, by rfl⟩ : syracuseStep 5602889 = 4202167) B4202167
theorem B7464473 : Blo 1164640 7464473 := bstep (se 2 (by rfl) ⟨2799177, by rfl⟩ : syracuseStep 7464473 = 5598355) B5598355
theorem B28339145 : Blo 1164640 28339145 := bstep (se 2 (by rfl) ⟨10627179, by rfl⟩ : syracuseStep 28339145 = 21254359) B21254359
theorem B1748219 : Blo 1164640 1748219 := bstep (se 1 (by rfl) ⟨1311164, by rfl⟩ : syracuseStep 1748219 = 2622329) B2622329
theorem B4427369 : Blo 1164640 4427369 := bstep (se 2 (by rfl) ⟨1660263, by rfl⟩ : syracuseStep 4427369 = 3320527) B3320527
theorem B1966079 : Blo 1164640 1966079 := bstep (se 1 (by rfl) ⟨1474559, by rfl⟩ : syracuseStep 1966079 = 2949119) B2949119
theorem B14941037 : Blo 1164640 14941037 := bstep (se 3 (by rfl) ⟨2801444, by rfl⟩ : syracuseStep 14941037 = 5602889) B5602889
theorem B3931199 : Blo 1164640 3931199 := bstep (se 1 (by rfl) ⟨2948399, by rfl⟩ : syracuseStep 3931199 = 5896799) B5896799
theorem B18892763 : Blo 1164640 18892763 := bstep (se 1 (by rfl) ⟨14169572, by rfl⟩ : syracuseStep 18892763 = 28339145) B28339145
theorem B1165479 : Blo 1164640 1165479 := bstep (se 1 (by rfl) ⟨874109, by rfl⟩ : syracuseStep 1165479 = 1748219) B1748219
theorem B2951579 : Blo 1164640 2951579 := bstep (se 1 (by rfl) ⟨2213684, by rfl⟩ : syracuseStep 2951579 = 4427369) B4427369
theorem B4976315 : Blo 1164640 4976315 := bstep (se 1 (by rfl) ⟨3732236, by rfl⟩ : syracuseStep 4976315 = 7464473) B7464473
theorem B9960691 : Blo 1164640 9960691 := bstep (se 1 (by rfl) ⟨7470518, by rfl⟩ : syracuseStep 9960691 = 14941037) B14941037
theorem B2620799 : Blo 1164640 2620799 := bstep (se 1 (by rfl) ⟨1965599, by rfl⟩ : syracuseStep 2620799 = 3931199) B3931199
theorem B1310719 : Blo 1164640 1310719 := bstep (se 1 (by rfl) ⟨983039, by rfl⟩ : syracuseStep 1310719 = 1966079) B1966079
theorem B1967719 : Blo 1164640 1967719 := bstep (se 1 (by rfl) ⟨1475789, by rfl⟩ : syracuseStep 1967719 = 2951579) B2951579
theorem B13280921 : Blo 1164640 13280921 := bstep (se 2 (by rfl) ⟨4980345, by rfl⟩ : syracuseStep 13280921 = 9960691) B9960691
theorem B1747199 : Blo 1164640 1747199 := bstep (se 1 (by rfl) ⟨1310399, by rfl⟩ : syracuseStep 1747199 = 2620799) B2620799
theorem B1747625 : Blo 1164640 1747625 := bstep (se 2 (by rfl) ⟨655359, by rfl⟩ : syracuseStep 1747625 = 1310719) B1310719
theorem B12595175 : Blo 1164640 12595175 := bstep (se 1 (by rfl) ⟨9446381, by rfl⟩ : syracuseStep 12595175 = 18892763) B18892763
theorem B3317543 : Blo 1164640 3317543 := bstep (se 1 (by rfl) ⟨2488157, by rfl⟩ : syracuseStep 3317543 = 4976315) B4976315
theorem B1164799 : Blo 1164640 1164799 := bstep (se 1 (by rfl) ⟨873599, by rfl⟩ : syracuseStep 1164799 = 1747199) B1747199
theorem B1165083 : Blo 1164640 1165083 := bstep (se 1 (by rfl) ⟨873812, by rfl⟩ : syracuseStep 1165083 = 1747625) B1747625
theorem B2623625 : Blo 1164640 2623625 := bstep (se 2 (by rfl) ⟨983859, by rfl⟩ : syracuseStep 2623625 = 1967719) B1967719
theorem B8853947 : Blo 1164640 8853947 := bstep (se 1 (by rfl) ⟨6640460, by rfl⟩ : syracuseStep 8853947 = 13280921) B13280921
theorem B2211695 : Blo 1164640 2211695 := bstep (se 1 (by rfl) ⟨1658771, by rfl⟩ : syracuseStep 2211695 = 3317543) B3317543
theorem B8396783 : Blo 1164640 8396783 := bstep (se 1 (by rfl) ⟨6297587, by rfl⟩ : syracuseStep 8396783 = 12595175) B12595175
theorem B5597855 : Blo 1164640 5597855 := bstep (se 1 (by rfl) ⟨4198391, by rfl⟩ : syracuseStep 5597855 = 8396783) B8396783
theorem B1749083 : Blo 1164640 1749083 := bstep (se 1 (by rfl) ⟨1311812, by rfl⟩ : syracuseStep 1749083 = 2623625) B2623625
theorem B5902631 : Blo 1164640 5902631 := bstep (se 1 (by rfl) ⟨4426973, by rfl⟩ : syracuseStep 5902631 = 8853947) B8853947
theorem B1474463 : Blo 1164640 1474463 := bstep (se 1 (by rfl) ⟨1105847, by rfl⟩ : syracuseStep 1474463 = 2211695) B2211695
theorem B1166055 : Blo 1164640 1166055 := bstep (se 1 (by rfl) ⟨874541, by rfl⟩ : syracuseStep 1166055 = 1749083) B1749083
theorem B3935087 : Blo 1164640 3935087 := bstep (se 1 (by rfl) ⟨2951315, by rfl⟩ : syracuseStep 3935087 = 5902631) B5902631
theorem B3731903 : Blo 1164640 3731903 := bstep (se 1 (by rfl) ⟨2798927, by rfl⟩ : syracuseStep 3731903 = 5597855) B5597855
theorem B3931901 : Blo 1164640 3931901 := bstep (se 3 (by rfl) ⟨737231, by rfl⟩ : syracuseStep 3931901 = 1474463) B1474463
theorem B2623391 : Blo 1164640 2623391 := bstep (se 1 (by rfl) ⟨1967543, by rfl⟩ : syracuseStep 2623391 = 3935087) B3935087
theorem B2487935 : Blo 1164640 2487935 := bstep (se 1 (by rfl) ⟨1865951, by rfl⟩ : syracuseStep 2487935 = 3731903) B3731903
theorem B2621267 : Blo 1164640 2621267 := bstep (se 1 (by rfl) ⟨1965950, by rfl⟩ : syracuseStep 2621267 = 3931901) B3931901
theorem B1747511 : Blo 1164640 1747511 := bstep (se 1 (by rfl) ⟨1310633, by rfl⟩ : syracuseStep 1747511 = 2621267) B2621267
theorem B1748927 : Blo 1164640 1748927 := bstep (se 1 (by rfl) ⟨1311695, by rfl⟩ : syracuseStep 1748927 = 2623391) B2623391
theorem B6634493 : Blo 1164640 6634493 := bstep (se 3 (by rfl) ⟨1243967, by rfl⟩ : syracuseStep 6634493 = 2487935) B2487935
theorem B1165007 : Blo 1164640 1165007 := bstep (se 1 (by rfl) ⟨873755, by rfl⟩ : syracuseStep 1165007 = 1747511) B1747511
theorem B1165951 : Blo 1164640 1165951 := bstep (se 1 (by rfl) ⟨874463, by rfl⟩ : syracuseStep 1165951 = 1748927) B1748927
theorem B4422995 : Blo 1164640 4422995 := bstep (se 1 (by rfl) ⟨3317246, by rfl⟩ : syracuseStep 4422995 = 6634493) B6634493
theorem B2948663 : Blo 1164640 2948663 := bstep (se 1 (by rfl) ⟨2211497, by rfl⟩ : syracuseStep 2948663 = 4422995) B4422995
theorem B1965775 : Blo 1164640 1965775 := bstep (se 1 (by rfl) ⟨1474331, by rfl⟩ : syracuseStep 1965775 = 2948663) B2948663
theorem B2621033 : Blo 1164640 2621033 := bstep (se 2 (by rfl) ⟨982887, by rfl⟩ : syracuseStep 2621033 = 1965775) B1965775
theorem B1747355 : Blo 1164640 1747355 := bstep (se 1 (by rfl) ⟨1310516, by rfl⟩ : syracuseStep 1747355 = 2621033) B2621033
theorem B1164903 : Blo 1164640 1164903 := bstep (se 1 (by rfl) ⟨873677, by rfl⟩ : syracuseStep 1164903 = 1747355) B1747355

theorem C0 (j : ℕ) (h1 : 291160 ≤ j) (h2 : j ≤ 291599) : Blo 1164640 (4 * j + 3) := by
  interval_cases j
  · exact B1164643
  · exact B1164647
  · exact B1164651
  · exact B1164655
  · exact B1164659
  · exact B1164663
  · exact B1164667
  · exact B1164671
  · exact B1164675
  · exact B1164679
  · exact B1164683
  · exact B1164687
  · exact B1164691
  · exact B1164695
  · exact B1164699
  · exact B1164703
  · exact B1164707
  · exact B1164711
  · exact B1164715
  · exact B1164719
  · exact B1164723
  · exact B1164727
  · exact B1164731
  · exact B1164735
  · exact B1164739
  · exact B1164743
  · exact B1164747
  · exact B1164751
  · exact B1164755
  · exact B1164759
  · exact B1164763
  · exact B1164767
  · exact B1164771
  · exact B1164775
  · exact B1164779
  · exact B1164783
  · exact B1164787
  · exact B1164791
  · exact B1164795
  · exact B1164799
  · exact B1164803
  · exact B1164807
  · exact B1164811
  · exact B1164815
  · exact B1164819
  · exact B1164823
  · exact B1164827
  · exact B1164831
  · exact B1164835
  · exact B1164839
  · exact B1164843
  · exact B1164847
  · exact B1164851
  · exact B1164855
  · exact B1164859
  · exact B1164863
  · exact B1164867
  · exact B1164871
  · exact B1164875
  · exact B1164879
  · exact B1164883
  · exact B1164887
  · exact B1164891
  · exact B1164895
  · exact B1164899
  · exact B1164903
  · exact B1164907
  · exact B1164911
  · exact B1164915
  · exact B1164919
  · exact B1164923
  · exact B1164927
  · exact B1164931
  · exact B1164935
  · exact B1164939
  · exact B1164943
  · exact B1164947
  · exact B1164951
  · exact B1164955
  · exact B1164959
  · exact B1164963
  · exact B1164967
  · exact B1164971
  · exact B1164975
  · exact B1164979
  · exact B1164983
  · exact B1164987
  · exact B1164991
  · exact B1164995
  · exact B1164999
  · exact B1165003
  · exact B1165007
  · exact B1165011
  · exact B1165015
  · exact B1165019
  · exact B1165023
  · exact B1165027
  · exact B1165031
  · exact B1165035
  · exact B1165039
  · exact B1165043
  · exact B1165047
  · exact B1165051
  · exact B1165055
  · exact B1165059
  · exact B1165063
  · exact B1165067
  · exact B1165071
  · exact B1165075
  · exact B1165079
  · exact B1165083
  · exact B1165087
  · exact B1165091
  · exact B1165095
  · exact B1165099
  · exact B1165103
  · exact B1165107
  · exact B1165111
  · exact B1165115
  · exact B1165119
  · exact B1165123
  · exact B1165127
  · exact B1165131
  · exact B1165135
  · exact B1165139
  · exact B1165143
  · exact B1165147
  · exact B1165151
  · exact B1165155
  · exact B1165159
  · exact B1165163
  · exact B1165167
  · exact B1165171
  · exact B1165175
  · exact B1165179
  · exact B1165183
  · exact B1165187
  · exact B1165191
  · exact B1165195
  · exact B1165199
  · exact B1165203
  · exact B1165207
  · exact B1165211
  · exact B1165215
  · exact B1165219
  · exact B1165223
  · exact B1165227
  · exact B1165231
  · exact B1165235
  · exact B1165239
  · exact B1165243
  · exact B1165247
  · exact B1165251
  · exact B1165255
  · exact B1165259
  · exact B1165263
  · exact B1165267
  · exact B1165271
  · exact B1165275
  · exact B1165279
  · exact B1165283
  · exact B1165287
  · exact B1165291
  · exact B1165295
  · exact B1165299
  · exact B1165303
  · exact B1165307
  · exact B1165311
  · exact B1165315
  · exact B1165319
  · exact B1165323
  · exact B1165327
  · exact B1165331
  · exact B1165335
  · exact B1165339
  · exact B1165343
  · exact B1165347
  · exact B1165351
  · exact B1165355
  · exact B1165359
  · exact B1165363
  · exact B1165367
  · exact B1165371
  · exact B1165375
  · exact B1165379
  · exact B1165383
  · exact B1165387
  · exact B1165391
  · exact B1165395
  · exact B1165399
  · exact B1165403
  · exact B1165407
  · exact B1165411
  · exact B1165415
  · exact B1165419
  · exact B1165423
  · exact B1165427
  · exact B1165431
  · exact B1165435
  · exact B1165439
  · exact B1165443
  · exact B1165447
  · exact B1165451
  · exact B1165455
  · exact B1165459
  · exact B1165463
  · exact B1165467
  · exact B1165471
  · exact B1165475
  · exact B1165479
  · exact B1165483
  · exact B1165487
  · exact B1165491
  · exact B1165495
  · exact B1165499
  · exact B1165503
  · exact B1165507
  · exact B1165511
  · exact B1165515
  · exact B1165519
  · exact B1165523
  · exact B1165527
  · exact B1165531
  · exact B1165535
  · exact B1165539
  · exact B1165543
  · exact B1165547
  · exact B1165551
  · exact B1165555
  · exact B1165559
  · exact B1165563
  · exact B1165567
  · exact B1165571
  · exact B1165575
  · exact B1165579
  · exact B1165583
  · exact B1165587
  · exact B1165591
  · exact B1165595
  · exact B1165599
  · exact B1165603
  · exact B1165607
  · exact B1165611
  · exact B1165615
  · exact B1165619
  · exact B1165623
  · exact B1165627
  · exact B1165631
  · exact B1165635
  · exact B1165639
  · exact B1165643
  · exact B1165647
  · exact B1165651
  · exact B1165655
  · exact B1165659
  · exact B1165663
  · exact B1165667
  · exact B1165671
  · exact B1165675
  · exact B1165679
  · exact B1165683
  · exact B1165687
  · exact B1165691
  · exact B1165695
  · exact B1165699
  · exact B1165703
  · exact B1165707
  · exact B1165711
  · exact B1165715
  · exact B1165719
  · exact B1165723
  · exact B1165727
  · exact B1165731
  · exact B1165735
  · exact B1165739
  · exact B1165743
  · exact B1165747
  · exact B1165751
  · exact B1165755
  · exact B1165759
  · exact B1165763
  · exact B1165767
  · exact B1165771
  · exact B1165775
  · exact B1165779
  · exact B1165783
  · exact B1165787
  · exact B1165791
  · exact B1165795
  · exact B1165799
  · exact B1165803
  · exact B1165807
  · exact B1165811
  · exact B1165815
  · exact B1165819
  · exact B1165823
  · exact B1165827
  · exact B1165831
  · exact B1165835
  · exact B1165839
  · exact B1165843
  · exact B1165847
  · exact B1165851
  · exact B1165855
  · exact B1165859
  · exact B1165863
  · exact B1165867
  · exact B1165871
  · exact B1165875
  · exact B1165879
  · exact B1165883
  · exact B1165887
  · exact B1165891
  · exact B1165895
  · exact B1165899
  · exact B1165903
  · exact B1165907
  · exact B1165911
  · exact B1165915
  · exact B1165919
  · exact B1165923
  · exact B1165927
  · exact B1165931
  · exact B1165935
  · exact B1165939
  · exact B1165943
  · exact B1165947
  · exact B1165951
  · exact B1165955
  · exact B1165959
  · exact B1165963
  · exact B1165967
  · exact B1165971
  · exact B1165975
  · exact B1165979
  · exact B1165983
  · exact B1165987
  · exact B1165991
  · exact B1165995
  · exact B1165999
  · exact B1166003
  · exact B1166007
  · exact B1166011
  · exact B1166015
  · exact B1166019
  · exact B1166023
  · exact B1166027
  · exact B1166031
  · exact B1166035
  · exact B1166039
  · exact B1166043
  · exact B1166047
  · exact B1166051
  · exact B1166055
  · exact B1166059
  · exact B1166063
  · exact B1166067
  · exact B1166071
  · exact B1166075
  · exact B1166079
  · exact B1166083
  · exact B1166087
  · exact B1166091
  · exact B1166095
  · exact B1166099
  · exact B1166103
  · exact B1166107
  · exact B1166111
  · exact B1166115
  · exact B1166119
  · exact B1166123
  · exact B1166127
  · exact B1166131
  · exact B1166135
  · exact B1166139
  · exact B1166143
  · exact B1166147
  · exact B1166151
  · exact B1166155
  · exact B1166159
  · exact B1166163
  · exact B1166167
  · exact B1166171
  · exact B1166175
  · exact B1166179
  · exact B1166183
  · exact B1166187
  · exact B1166191
  · exact B1166195
  · exact B1166199
  · exact B1166203
  · exact B1166207
  · exact B1166211
  · exact B1166215
  · exact B1166219
  · exact B1166223
  · exact B1166227
  · exact B1166231
  · exact B1166235
  · exact B1166239
  · exact B1166243
  · exact B1166247
  · exact B1166251
  · exact B1166255
  · exact B1166259
  · exact B1166263
  · exact B1166267
  · exact B1166271
  · exact B1166275
  · exact B1166279
  · exact B1166283
  · exact B1166287
  · exact B1166291
  · exact B1166295
  · exact B1166299
  · exact B1166303
  · exact B1166307
  · exact B1166311
  · exact B1166315
  · exact B1166319
  · exact B1166323
  · exact B1166327
  · exact B1166331
  · exact B1166335
  · exact B1166339
  · exact B1166343
  · exact B1166347
  · exact B1166351
  · exact B1166355
  · exact B1166359
  · exact B1166363
  · exact B1166367
  · exact B1166371
  · exact B1166375
  · exact B1166379
  · exact B1166383
  · exact B1166387
  · exact B1166391
  · exact B1166395
  · exact B1166399

theorem solution (m : ℕ) (hlo : 1164640 ≤ m) (hhi : m ≤ 1166399) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 291160 ≤ j := by omega
    have hj2 : j ≤ 291599 := by omega
    have hb : Blo 1164640 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
