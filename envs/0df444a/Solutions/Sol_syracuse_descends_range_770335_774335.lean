-- Prove2me | solution 1 for syracuse_descends_range_770335_774335
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:24.59103+00:00
-- url     : https://prove2.me/submissions/1a9b86d5-e0f7-4dcf-a922-cd8816d30896

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


theorem B1736765 : Blo 770335 1736765 := bbase (se 3 (by rfl) ⟨325643, by rfl⟩ : syracuseStep 1736765 = 651287) (by norm_num)
theorem B1736837 : Blo 770335 1736837 := bbase (se 4 (by rfl) ⟨162828, by rfl⟩ : syracuseStep 1736837 = 325657) (by norm_num)
theorem B1736909 : Blo 770335 1736909 := bbase (se 3 (by rfl) ⟨325670, by rfl⟩ : syracuseStep 1736909 = 651341) (by norm_num)
theorem B1736981 : Blo 770335 1736981 := bbase (se 6 (by rfl) ⟨40710, by rfl⟩ : syracuseStep 1736981 = 81421) (by norm_num)
theorem B1737053 : Blo 770335 1737053 := bbase (se 3 (by rfl) ⟨325697, by rfl⟩ : syracuseStep 1737053 = 651395) (by norm_num)
theorem B1737125 : Blo 770335 1737125 := bbase (se 4 (by rfl) ⟨162855, by rfl⟩ : syracuseStep 1737125 = 325711) (by norm_num)
theorem B1671637 : Blo 770335 1671637 := bbase (se 7 (by rfl) ⟨19589, by rfl⟩ : syracuseStep 1671637 = 39179) (by norm_num)
theorem B1737197 : Blo 770335 1737197 := bbase (se 3 (by rfl) ⟨325724, by rfl⟩ : syracuseStep 1737197 = 651449) (by norm_num)
theorem B1737269 : Blo 770335 1737269 := bbase (se 5 (by rfl) ⟨81434, by rfl⟩ : syracuseStep 1737269 = 162869) (by norm_num)
theorem B1737341 : Blo 770335 1737341 := bbase (se 3 (by rfl) ⟨325751, by rfl⟩ : syracuseStep 1737341 = 651503) (by norm_num)
theorem B1737413 : Blo 770335 1737413 := bbase (se 4 (by rfl) ⟨162882, by rfl⟩ : syracuseStep 1737413 = 325765) (by norm_num)
theorem B3900149 : Blo 770335 3900149 := bbase (se 5 (by rfl) ⟨182819, by rfl⟩ : syracuseStep 3900149 = 365639) (by norm_num)
theorem B1737485 : Blo 770335 1737485 := bbase (se 3 (by rfl) ⟨325778, by rfl⟩ : syracuseStep 1737485 = 651557) (by norm_num)
theorem B7144213 : Blo 770335 7144213 := bbase (se 6 (by rfl) ⟨167442, by rfl⟩ : syracuseStep 7144213 = 334885) (by norm_num)
theorem B1737557 : Blo 770335 1737557 := bbase (se 9 (by rfl) ⟨5090, by rfl⟩ : syracuseStep 1737557 = 10181) (by norm_num)
theorem B2196341 : Blo 770335 2196341 := bbase (se 5 (by rfl) ⟨102953, by rfl⟩ : syracuseStep 2196341 = 205907) (by norm_num)
theorem B1409909 : Blo 770335 1409909 := bbase (se 5 (by rfl) ⟨66089, by rfl⟩ : syracuseStep 1409909 = 132179) (by norm_num)
theorem B1737629 : Blo 770335 1737629 := bbase (se 3 (by rfl) ⟨325805, by rfl⟩ : syracuseStep 1737629 = 651611) (by norm_num)
theorem B1737701 : Blo 770335 1737701 := bbase (se 4 (by rfl) ⟨162909, by rfl⟩ : syracuseStep 1737701 = 325819) (by norm_num)
theorem B1737773 : Blo 770335 1737773 := bbase (se 3 (by rfl) ⟨325832, by rfl⟩ : syracuseStep 1737773 = 651665) (by norm_num)
theorem B4949045 : Blo 770335 4949045 := bbase (se 5 (by rfl) ⟨231986, by rfl⟩ : syracuseStep 4949045 = 463973) (by norm_num)
theorem B1737845 : Blo 770335 1737845 := bbase (se 5 (by rfl) ⟨81461, by rfl⟩ : syracuseStep 1737845 = 162923) (by norm_num)
theorem B5276821 : Blo 770335 5276821 := bbase (se 6 (by rfl) ⟨123675, by rfl⟩ : syracuseStep 5276821 = 247351) (by norm_num)
theorem B1737917 : Blo 770335 1737917 := bbase (se 3 (by rfl) ⟨325859, by rfl⟩ : syracuseStep 1737917 = 651719) (by norm_num)
theorem B1737989 : Blo 770335 1737989 := bbase (se 4 (by rfl) ⟨162936, by rfl⟩ : syracuseStep 1737989 = 325873) (by norm_num)
theorem B3343685 : Blo 770335 3343685 := bbase (se 4 (by rfl) ⟨313470, by rfl⟩ : syracuseStep 3343685 = 626941) (by norm_num)
theorem B1738061 : Blo 770335 1738061 := bbase (se 3 (by rfl) ⟨325886, by rfl⟩ : syracuseStep 1738061 = 651773) (by norm_num)
theorem B1738133 : Blo 770335 1738133 := bbase (se 6 (by rfl) ⟨40737, by rfl⟩ : syracuseStep 1738133 = 81475) (by norm_num)
theorem B1738205 : Blo 770335 1738205 := bbase (se 3 (by rfl) ⟨325913, by rfl⟩ : syracuseStep 1738205 = 651827) (by norm_num)
theorem B1738277 : Blo 770335 1738277 := bbase (se 4 (by rfl) ⟨162963, by rfl⟩ : syracuseStep 1738277 = 325927) (by norm_num)
theorem B1738349 : Blo 770335 1738349 := bbase (se 3 (by rfl) ⟨325940, by rfl⟩ : syracuseStep 1738349 = 651881) (by norm_num)
theorem B1738421 : Blo 770335 1738421 := bbase (se 5 (by rfl) ⟨81488, by rfl⟩ : syracuseStep 1738421 = 162977) (by norm_num)
theorem B8914645 : Blo 770335 8914645 := bbase (se 7 (by rfl) ⟨104468, by rfl⟩ : syracuseStep 8914645 = 208937) (by norm_num)
theorem B1738493 : Blo 770335 1738493 := bbase (se 3 (by rfl) ⟨325967, by rfl⟩ : syracuseStep 1738493 = 651935) (by norm_num)
theorem B1738565 : Blo 770335 1738565 := bbase (se 4 (by rfl) ⟨162990, by rfl⟩ : syracuseStep 1738565 = 325981) (by norm_num)
theorem B1738637 : Blo 770335 1738637 := bbase (se 3 (by rfl) ⟨325994, by rfl⟩ : syracuseStep 1738637 = 651989) (by norm_num)
theorem B5867477 : Blo 770335 5867477 := bbase (se 7 (by rfl) ⟨68759, by rfl⟩ : syracuseStep 5867477 = 137519) (by norm_num)
theorem B1738709 : Blo 770335 1738709 := bbase (se 7 (by rfl) ⟨20375, by rfl⟩ : syracuseStep 1738709 = 40751) (by norm_num)
theorem B3901445 : Blo 770335 3901445 := bbase (se 4 (by rfl) ⟨365760, by rfl⟩ : syracuseStep 3901445 = 731521) (by norm_num)
theorem B2197525 : Blo 770335 2197525 := bbase (se 6 (by rfl) ⟨51504, by rfl⟩ : syracuseStep 2197525 = 103009) (by norm_num)
theorem B1738781 : Blo 770335 1738781 := bbase (se 3 (by rfl) ⟨326021, by rfl⟩ : syracuseStep 1738781 = 652043) (by norm_num)
theorem B1738853 : Blo 770335 1738853 := bbase (se 4 (by rfl) ⟨163017, by rfl⟩ : syracuseStep 1738853 = 326035) (by norm_num)
theorem B1738925 : Blo 770335 1738925 := bbase (se 3 (by rfl) ⟨326048, by rfl⟩ : syracuseStep 1738925 = 652097) (by norm_num)
theorem B2197685 : Blo 770335 2197685 := bbase (se 5 (by rfl) ⟨103016, by rfl⟩ : syracuseStep 2197685 = 206033) (by norm_num)
theorem B1738997 : Blo 770335 1738997 := bbase (se 5 (by rfl) ⟨81515, by rfl⟩ : syracuseStep 1738997 = 163031) (by norm_num)
theorem B1739069 : Blo 770335 1739069 := bbase (se 3 (by rfl) ⟨326075, by rfl⟩ : syracuseStep 1739069 = 652151) (by norm_num)
theorem B3705173 : Blo 770335 3705173 := bbase (se 10 (by rfl) ⟨5427, by rfl⟩ : syracuseStep 3705173 = 10855) (by norm_num)
theorem B1739141 : Blo 770335 1739141 := bbase (se 4 (by rfl) ⟨163044, by rfl⟩ : syracuseStep 1739141 = 326089) (by norm_num)
theorem B2197925 : Blo 770335 2197925 := bbase (se 4 (by rfl) ⟨206055, by rfl⟩ : syracuseStep 2197925 = 412111) (by norm_num)
theorem B1739213 : Blo 770335 1739213 := bbase (se 3 (by rfl) ⟨326102, by rfl⟩ : syracuseStep 1739213 = 652205) (by norm_num)
theorem B1739285 : Blo 770335 1739285 := bbase (se 6 (by rfl) ⟨40764, by rfl⟩ : syracuseStep 1739285 = 81529) (by norm_num)
theorem B1739357 : Blo 770335 1739357 := bbase (se 3 (by rfl) ⟨326129, by rfl⟩ : syracuseStep 1739357 = 652259) (by norm_num)
theorem B2198117 : Blo 770335 2198117 := bbase (se 4 (by rfl) ⟨206073, by rfl⟩ : syracuseStep 2198117 = 412147) (by norm_num)
theorem B1739429 : Blo 770335 1739429 := bbase (se 4 (by rfl) ⟨163071, by rfl⟩ : syracuseStep 1739429 = 326143) (by norm_num)
theorem B1739501 : Blo 770335 1739501 := bbase (se 3 (by rfl) ⟨326156, by rfl⟩ : syracuseStep 1739501 = 652313) (by norm_num)
theorem B1739573 : Blo 770335 1739573 := bbase (se 5 (by rfl) ⟨81542, by rfl⟩ : syracuseStep 1739573 = 163085) (by norm_num)
theorem B1739645 : Blo 770335 1739645 := bbase (se 3 (by rfl) ⟨326183, by rfl⟩ : syracuseStep 1739645 = 652367) (by norm_num)
theorem B1739717 : Blo 770335 1739717 := bbase (se 4 (by rfl) ⟨163098, by rfl⟩ : syracuseStep 1739717 = 326197) (by norm_num)
theorem B1739789 : Blo 770335 1739789 := bbase (se 3 (by rfl) ⟨326210, by rfl⟩ : syracuseStep 1739789 = 652421) (by norm_num)
theorem B1739861 : Blo 770335 1739861 := bbase (se 8 (by rfl) ⟨10194, by rfl⟩ : syracuseStep 1739861 = 20389) (by norm_num)
theorem B1739933 : Blo 770335 1739933 := bbase (se 3 (by rfl) ⟨326237, by rfl⟩ : syracuseStep 1739933 = 652475) (by norm_num)
theorem B1740005 : Blo 770335 1740005 := bbase (se 4 (by rfl) ⟨163125, by rfl⟩ : syracuseStep 1740005 = 326251) (by norm_num)
theorem B3902741 : Blo 770335 3902741 := bbase (se 6 (by rfl) ⟨91470, by rfl⟩ : syracuseStep 3902741 = 182941) (by norm_num)
theorem B1740077 : Blo 770335 1740077 := bbase (se 3 (by rfl) ⟨326264, by rfl⟩ : syracuseStep 1740077 = 652529) (by norm_num)
theorem B822637 : Blo 770335 822637 := bbase (se 3 (by rfl) ⟨154244, by rfl⟩ : syracuseStep 822637 = 308489) (by norm_num)
theorem B1740149 : Blo 770335 1740149 := bbase (se 5 (by rfl) ⟨81569, by rfl⟩ : syracuseStep 1740149 = 163139) (by norm_num)
theorem B1740221 : Blo 770335 1740221 := bbase (se 3 (by rfl) ⟨326291, by rfl⟩ : syracuseStep 1740221 = 652583) (by norm_num)
theorem B1740293 : Blo 770335 1740293 := bbase (se 4 (by rfl) ⟨163152, by rfl⟩ : syracuseStep 1740293 = 326305) (by norm_num)
theorem B2199109 : Blo 770335 2199109 := bbase (se 4 (by rfl) ⟨206166, by rfl⟩ : syracuseStep 2199109 = 412333) (by norm_num)
theorem B1740365 : Blo 770335 1740365 := bbase (se 3 (by rfl) ⟨326318, by rfl⟩ : syracuseStep 1740365 = 652637) (by norm_num)
theorem B822889 : Blo 770335 822889 := bbase (se 2 (by rfl) ⟨308583, by rfl⟩ : syracuseStep 822889 = 617167) (by norm_num)
theorem B822893 : Blo 770335 822893 := bbase (se 3 (by rfl) ⟨154292, by rfl⟩ : syracuseStep 822893 = 308585) (by norm_num)
theorem B1740437 : Blo 770335 1740437 := bbase (se 6 (by rfl) ⟨40791, by rfl⟩ : syracuseStep 1740437 = 81583) (by norm_num)
theorem B1740509 : Blo 770335 1740509 := bbase (se 3 (by rfl) ⟨326345, by rfl⟩ : syracuseStep 1740509 = 652691) (by norm_num)
theorem B1740581 : Blo 770335 1740581 := bbase (se 4 (by rfl) ⟨163179, by rfl⟩ : syracuseStep 1740581 = 326359) (by norm_num)
theorem B1806149 : Blo 770335 1806149 := bbase (se 4 (by rfl) ⟨169326, by rfl⟩ : syracuseStep 1806149 = 338653) (by norm_num)
theorem B1740653 : Blo 770335 1740653 := bbase (se 3 (by rfl) ⟨326372, by rfl⟩ : syracuseStep 1740653 = 652745) (by norm_num)
theorem B1740725 : Blo 770335 1740725 := bbase (se 5 (by rfl) ⟨81596, by rfl⟩ : syracuseStep 1740725 = 163193) (by norm_num)
theorem B1740797 : Blo 770335 1740797 := bbase (se 3 (by rfl) ⟨326399, by rfl⟩ : syracuseStep 1740797 = 652799) (by norm_num)
theorem B1740869 : Blo 770335 1740869 := bbase (se 4 (by rfl) ⟨163206, by rfl⟩ : syracuseStep 1740869 = 326413) (by norm_num)
theorem B1740941 : Blo 770335 1740941 := bbase (se 3 (by rfl) ⟨326426, by rfl⟩ : syracuseStep 1740941 = 652853) (by norm_num)
theorem B823457 : Blo 770335 823457 := bbase (se 2 (by rfl) ⟨308796, by rfl⟩ : syracuseStep 823457 = 617593) (by norm_num)
theorem B1741013 : Blo 770335 1741013 := bbase (se 7 (by rfl) ⟨20402, by rfl⟩ : syracuseStep 1741013 = 40805) (by norm_num)
theorem B1741085 : Blo 770335 1741085 := bbase (se 3 (by rfl) ⟨326453, by rfl⟩ : syracuseStep 1741085 = 652907) (by norm_num)
theorem B823645 : Blo 770335 823645 := bbase (se 3 (by rfl) ⟨154433, by rfl⟩ : syracuseStep 823645 = 308867) (by norm_num)
theorem B1741157 : Blo 770335 1741157 := bbase (se 4 (by rfl) ⟨163233, by rfl⟩ : syracuseStep 1741157 = 326467) (by norm_num)
theorem B1741229 : Blo 770335 1741229 := bbase (se 3 (by rfl) ⟨326480, by rfl⟩ : syracuseStep 1741229 = 652961) (by norm_num)
theorem B1741301 : Blo 770335 1741301 := bbase (se 5 (by rfl) ⟨81623, by rfl⟩ : syracuseStep 1741301 = 163247) (by norm_num)
theorem B3904037 : Blo 770335 3904037 := bbase (se 4 (by rfl) ⟨366003, by rfl⟩ : syracuseStep 3904037 = 732007) (by norm_num)
theorem B1741373 : Blo 770335 1741373 := bbase (se 3 (by rfl) ⟨326507, by rfl⟩ : syracuseStep 1741373 = 653015) (by norm_num)
theorem B1741445 : Blo 770335 1741445 := bbase (se 4 (by rfl) ⟨163260, by rfl⟩ : syracuseStep 1741445 = 326521) (by norm_num)
theorem B2200213 : Blo 770335 2200213 := bbase (se 6 (by rfl) ⟨51567, by rfl⟩ : syracuseStep 2200213 = 103135) (by norm_num)
theorem B1741517 : Blo 770335 1741517 := bbase (se 3 (by rfl) ⟨326534, by rfl⟩ : syracuseStep 1741517 = 653069) (by norm_num)
theorem B1741589 : Blo 770335 1741589 := bbase (se 6 (by rfl) ⟨40818, by rfl⟩ : syracuseStep 1741589 = 81637) (by norm_num)
theorem B1741661 : Blo 770335 1741661 := bbase (se 3 (by rfl) ⟨326561, by rfl⟩ : syracuseStep 1741661 = 653123) (by norm_num)
theorem B1741733 : Blo 770335 1741733 := bbase (se 4 (by rfl) ⟨163287, by rfl⟩ : syracuseStep 1741733 = 326575) (by norm_num)
theorem B1741805 : Blo 770335 1741805 := bbase (se 3 (by rfl) ⟨326588, by rfl⟩ : syracuseStep 1741805 = 653177) (by norm_num)
theorem B1741877 : Blo 770335 1741877 := bbase (se 5 (by rfl) ⟨81650, by rfl⟩ : syracuseStep 1741877 = 163301) (by norm_num)
theorem B1741949 : Blo 770335 1741949 := bbase (se 3 (by rfl) ⟨326615, by rfl⟩ : syracuseStep 1741949 = 653231) (by norm_num)
theorem B824465 : Blo 770335 824465 := bbase (se 2 (by rfl) ⟨309174, by rfl⟩ : syracuseStep 824465 = 618349) (by norm_num)
theorem B1742021 : Blo 770335 1742021 := bbase (se 4 (by rfl) ⟨163314, by rfl⟩ : syracuseStep 1742021 = 326629) (by norm_num)
theorem B1742093 : Blo 770335 1742093 := bbase (se 3 (by rfl) ⟨326642, by rfl⟩ : syracuseStep 1742093 = 653285) (by norm_num)
theorem B988465 : Blo 770335 988465 := bbase (se 2 (by rfl) ⟨370674, by rfl⟩ : syracuseStep 988465 = 741349) (by norm_num)
theorem B1742165 : Blo 770335 1742165 := bbase (se 14 (by rfl) ⟨159, by rfl⟩ : syracuseStep 1742165 = 319) (by norm_num)
theorem B1742237 : Blo 770335 1742237 := bbase (se 3 (by rfl) ⟨326669, by rfl⟩ : syracuseStep 1742237 = 653339) (by norm_num)
theorem B824909 : Blo 770335 824909 := bbase (se 3 (by rfl) ⟨154670, by rfl⟩ : syracuseStep 824909 = 309341) (by norm_num)
theorem B3905333 : Blo 770335 3905333 := bbase (se 5 (by rfl) ⟨183062, by rfl⟩ : syracuseStep 3905333 = 366125) (by norm_num)
theorem B825157 : Blo 770335 825157 := bbase (se 4 (by rfl) ⟨77358, by rfl⟩ : syracuseStep 825157 = 154717) (by norm_num)
theorem B12064853 : Blo 770335 12064853 := bbase (se 8 (by rfl) ⟨70692, by rfl⟩ : syracuseStep 12064853 = 141385) (by norm_num)
theorem B5576789 : Blo 770335 5576789 := bbase (se 8 (by rfl) ⟨32676, by rfl⟩ : syracuseStep 5576789 = 65353) (by norm_num)
theorem B2201717 : Blo 770335 2201717 := bbase (se 5 (by rfl) ⟨103205, by rfl⟩ : syracuseStep 2201717 = 206411) (by norm_num)
theorem B4397237 : Blo 770335 4397237 := bbase (se 5 (by rfl) ⟨206120, by rfl⟩ : syracuseStep 4397237 = 412241) (by norm_num)
theorem B825589 : Blo 770335 825589 := bbase (se 5 (by rfl) ⟨38699, by rfl⟩ : syracuseStep 825589 = 77399) (by norm_num)
theorem B4692277 : Blo 770335 4692277 := bbase (se 5 (by rfl) ⟨219950, by rfl⟩ : syracuseStep 4692277 = 439901) (by norm_num)
theorem B825661 : Blo 770335 825661 := bbase (se 3 (by rfl) ⟨154811, by rfl⟩ : syracuseStep 825661 = 309623) (by norm_num)
theorem B3578309 : Blo 770335 3578309 := bbase (se 4 (by rfl) ⟨335466, by rfl⟩ : syracuseStep 3578309 = 670933) (by norm_num)
theorem B826033 : Blo 770335 826033 := bbase (se 2 (by rfl) ⟨309762, by rfl⟩ : syracuseStep 826033 = 619525) (by norm_num)
theorem B826409 : Blo 770335 826409 := bbase (se 2 (by rfl) ⟨309903, by rfl⟩ : syracuseStep 826409 = 619807) (by norm_num)
theorem B3906629 : Blo 770335 3906629 := bbase (se 4 (by rfl) ⟨366246, by rfl⟩ : syracuseStep 3906629 = 732493) (by norm_num)
theorem B826481 : Blo 770335 826481 := bbase (se 2 (by rfl) ⟨309930, by rfl⟩ : syracuseStep 826481 = 619861) (by norm_num)
theorem B826669 : Blo 770335 826669 := bbase (se 3 (by rfl) ⟨155000, by rfl⟩ : syracuseStep 826669 = 310001) (by norm_num)
theorem B38083925 : Blo 770335 38083925 := bbase (se 11 (by rfl) ⟨27893, by rfl⟩ : syracuseStep 38083925 = 55787) (by norm_num)
theorem B4398421 : Blo 770335 4398421 := bbase (se 11 (by rfl) ⟨3221, by rfl⟩ : syracuseStep 4398421 = 6443) (by norm_num)
theorem B1645957 : Blo 770335 1645957 := bbase (se 4 (by rfl) ⟨154308, by rfl⟩ : syracuseStep 1645957 = 308617) (by norm_num)
theorem B826853 : Blo 770335 826853 := bbase (se 4 (by rfl) ⟨77517, by rfl⟩ : syracuseStep 826853 = 155035) (by norm_num)
theorem B1646077 : Blo 770335 1646077 := bbase (se 3 (by rfl) ⟨308639, by rfl⟩ : syracuseStep 1646077 = 617279) (by norm_num)
theorem B990733 : Blo 770335 990733 := bbase (se 3 (by rfl) ⟨185762, by rfl⟩ : syracuseStep 990733 = 371525) (by norm_num)
theorem B2203301 : Blo 770335 2203301 := bbase (se 4 (by rfl) ⟨206559, by rfl⟩ : syracuseStep 2203301 = 413119) (by norm_num)
theorem B9903829 : Blo 770335 9903829 := bbase (se 7 (by rfl) ⟨116060, by rfl⟩ : syracuseStep 9903829 = 232121) (by norm_num)
theorem B1646333 : Blo 770335 1646333 := bbase (se 3 (by rfl) ⟨308687, by rfl⟩ : syracuseStep 1646333 = 617375) (by norm_num)
theorem B925597 : Blo 770335 925597 := bbase (se 3 (by rfl) ⟨173549, by rfl⟩ : syracuseStep 925597 = 347099) (by norm_num)
theorem B925601 : Blo 770335 925601 := bbase (se 2 (by rfl) ⟨347100, by rfl⟩ : syracuseStep 925601 = 694201) (by norm_num)
theorem B7610453 : Blo 770335 7610453 := bbase (se 8 (by rfl) ⟨44592, by rfl⟩ : syracuseStep 7610453 = 89185) (by norm_num)
theorem B2924869 : Blo 770335 2924869 := bbase (se 4 (by rfl) ⟨274206, by rfl⟩ : syracuseStep 2924869 = 548413) (by norm_num)
theorem B2203973 : Blo 770335 2203973 := bbase (se 4 (by rfl) ⟨206622, by rfl⟩ : syracuseStep 2203973 = 413245) (by norm_num)
theorem B3907925 : Blo 770335 3907925 := bbase (se 10 (by rfl) ⟨5724, by rfl⟩ : syracuseStep 3907925 = 11449) (by norm_num)
theorem B3514757 : Blo 770335 3514757 := bbase (se 4 (by rfl) ⟨329508, by rfl⟩ : syracuseStep 3514757 = 659017) (by norm_num)
theorem B926101 : Blo 770335 926101 := bbase (se 6 (by rfl) ⟨21705, by rfl⟩ : syracuseStep 926101 = 43411) (by norm_num)
theorem B1155509 : Blo 770335 1155509 := bbase (se 5 (by rfl) ⟨54164, by rfl⟩ : syracuseStep 1155509 = 108329) (by norm_num)
theorem B1155533 : Blo 770335 1155533 := bbase (se 3 (by rfl) ⟨216662, by rfl⟩ : syracuseStep 1155533 = 433325) (by norm_num)
theorem B1155557 : Blo 770335 1155557 := bbase (se 4 (by rfl) ⟨108333, by rfl⟩ : syracuseStep 1155557 = 216667) (by norm_num)
theorem B1155581 : Blo 770335 1155581 := bbase (se 3 (by rfl) ⟨216671, by rfl⟩ : syracuseStep 1155581 = 433343) (by norm_num)
theorem B1155605 : Blo 770335 1155605 := bbase (se 6 (by rfl) ⟨27084, by rfl⟩ : syracuseStep 1155605 = 54169) (by norm_num)
theorem B1155629 : Blo 770335 1155629 := bbase (se 3 (by rfl) ⟨216680, by rfl⟩ : syracuseStep 1155629 = 433361) (by norm_num)
theorem B1155653 : Blo 770335 1155653 := bbase (se 4 (by rfl) ⟨108342, by rfl⟩ : syracuseStep 1155653 = 216685) (by norm_num)
theorem B1155677 : Blo 770335 1155677 := bbase (se 3 (by rfl) ⟨216689, by rfl⟩ : syracuseStep 1155677 = 433379) (by norm_num)
theorem B2925173 : Blo 770335 2925173 := bbase (se 5 (by rfl) ⟨137117, by rfl⟩ : syracuseStep 2925173 = 274235) (by norm_num)
theorem B1155701 : Blo 770335 1155701 := bbase (se 5 (by rfl) ⟨54173, by rfl⟩ : syracuseStep 1155701 = 108347) (by norm_num)
theorem B1647221 : Blo 770335 1647221 := bbase (se 5 (by rfl) ⟨77213, by rfl⟩ : syracuseStep 1647221 = 154427) (by norm_num)
theorem B2171525 : Blo 770335 2171525 := bbase (se 4 (by rfl) ⟨203580, by rfl⟩ : syracuseStep 2171525 = 407161) (by norm_num)
theorem B1155725 : Blo 770335 1155725 := bbase (se 3 (by rfl) ⟨216698, by rfl⟩ : syracuseStep 1155725 = 433397) (by norm_num)
theorem B11870869 : Blo 770335 11870869 := bbase (se 6 (by rfl) ⟨278223, by rfl⟩ : syracuseStep 11870869 = 556447) (by norm_num)
theorem B1155749 : Blo 770335 1155749 := bbase (se 4 (by rfl) ⟨108351, by rfl⟩ : syracuseStep 1155749 = 216703) (by norm_num)
theorem B1155773 : Blo 770335 1155773 := bbase (se 3 (by rfl) ⟨216707, by rfl⟩ : syracuseStep 1155773 = 433415) (by norm_num)
theorem B1155797 : Blo 770335 1155797 := bbase (se 7 (by rfl) ⟨13544, by rfl⟩ : syracuseStep 1155797 = 27089) (by norm_num)
theorem B1155821 : Blo 770335 1155821 := bbase (se 3 (by rfl) ⟨216716, by rfl⟩ : syracuseStep 1155821 = 433433) (by norm_num)
theorem B2204405 : Blo 770335 2204405 := bbase (se 5 (by rfl) ⟨103331, by rfl⟩ : syracuseStep 2204405 = 206663) (by norm_num)
theorem B1155845 : Blo 770335 1155845 := bbase (se 4 (by rfl) ⟨108360, by rfl⟩ : syracuseStep 1155845 = 216721) (by norm_num)
theorem B926485 : Blo 770335 926485 := bbase (se 6 (by rfl) ⟨21714, by rfl⟩ : syracuseStep 926485 = 43429) (by norm_num)
theorem B1155869 : Blo 770335 1155869 := bbase (se 3 (by rfl) ⟨216725, by rfl⟩ : syracuseStep 1155869 = 433451) (by norm_num)
theorem B1155893 : Blo 770335 1155893 := bbase (se 5 (by rfl) ⟨54182, by rfl⟩ : syracuseStep 1155893 = 108365) (by norm_num)
theorem B1155917 : Blo 770335 1155917 := bbase (se 3 (by rfl) ⟨216734, by rfl⟩ : syracuseStep 1155917 = 433469) (by norm_num)
theorem B1155941 : Blo 770335 1155941 := bbase (se 4 (by rfl) ⟨108369, by rfl⟩ : syracuseStep 1155941 = 216739) (by norm_num)
theorem B1647461 : Blo 770335 1647461 := bbase (se 4 (by rfl) ⟨154449, by rfl⟩ : syracuseStep 1647461 = 308899) (by norm_num)
theorem B6595445 : Blo 770335 6595445 := bbase (se 5 (by rfl) ⟨309161, by rfl⟩ : syracuseStep 6595445 = 618323) (by norm_num)
theorem B1155965 : Blo 770335 1155965 := bbase (se 3 (by rfl) ⟨216743, by rfl⟩ : syracuseStep 1155965 = 433487) (by norm_num)
theorem B1155989 : Blo 770335 1155989 := bbase (se 6 (by rfl) ⟨27093, by rfl⟩ : syracuseStep 1155989 = 54187) (by norm_num)
theorem B1156013 : Blo 770335 1156013 := bbase (se 3 (by rfl) ⟨216752, by rfl⟩ : syracuseStep 1156013 = 433505) (by norm_num)
theorem B1156037 : Blo 770335 1156037 := bbase (se 4 (by rfl) ⟨108378, by rfl⟩ : syracuseStep 1156037 = 216757) (by norm_num)
theorem B1156061 : Blo 770335 1156061 := bbase (se 3 (by rfl) ⟨216761, by rfl⟩ : syracuseStep 1156061 = 433523) (by norm_num)
theorem B1156085 : Blo 770335 1156085 := bbase (se 5 (by rfl) ⟨54191, by rfl⟩ : syracuseStep 1156085 = 108383) (by norm_num)
theorem B1156109 : Blo 770335 1156109 := bbase (se 3 (by rfl) ⟨216770, by rfl⟩ : syracuseStep 1156109 = 433541) (by norm_num)
theorem B1156133 : Blo 770335 1156133 := bbase (se 4 (by rfl) ⟨108387, by rfl⟩ : syracuseStep 1156133 = 216775) (by norm_num)
theorem B1156157 : Blo 770335 1156157 := bbase (se 3 (by rfl) ⟨216779, by rfl⟩ : syracuseStep 1156157 = 433559) (by norm_num)
theorem B1156181 : Blo 770335 1156181 := bbase (se 8 (by rfl) ⟨6774, by rfl⟩ : syracuseStep 1156181 = 13549) (by norm_num)
theorem B5022805 : Blo 770335 5022805 := bbase (se 8 (by rfl) ⟨29430, by rfl⟩ : syracuseStep 5022805 = 58861) (by norm_num)
theorem B1156205 : Blo 770335 1156205 := bbase (se 3 (by rfl) ⟨216788, by rfl⟩ : syracuseStep 1156205 = 433577) (by norm_num)
theorem B1156229 : Blo 770335 1156229 := bbase (se 4 (by rfl) ⟨108396, by rfl⟩ : syracuseStep 1156229 = 216793) (by norm_num)
theorem B992405 : Blo 770335 992405 := bbase (se 6 (by rfl) ⟨23259, by rfl⟩ : syracuseStep 992405 = 46519) (by norm_num)
theorem B1156253 : Blo 770335 1156253 := bbase (se 3 (by rfl) ⟨216797, by rfl⟩ : syracuseStep 1156253 = 433595) (by norm_num)
theorem B1156277 : Blo 770335 1156277 := bbase (se 5 (by rfl) ⟨54200, by rfl⟩ : syracuseStep 1156277 = 108401) (by norm_num)
theorem B1156301 : Blo 770335 1156301 := bbase (se 3 (by rfl) ⟨216806, by rfl⟩ : syracuseStep 1156301 = 433613) (by norm_num)
theorem B1156325 : Blo 770335 1156325 := bbase (se 4 (by rfl) ⟨108405, by rfl⟩ : syracuseStep 1156325 = 216811) (by norm_num)
theorem B3712229 : Blo 770335 3712229 := bbase (se 4 (by rfl) ⟨348021, by rfl⟩ : syracuseStep 3712229 = 696043) (by norm_num)
theorem B1254637 : Blo 770335 1254637 := bbase (se 3 (by rfl) ⟨235244, by rfl⟩ : syracuseStep 1254637 = 470489) (by norm_num)
theorem B1156349 : Blo 770335 1156349 := bbase (se 3 (by rfl) ⟨216815, by rfl⟩ : syracuseStep 1156349 = 433631) (by norm_num)
theorem B1156373 : Blo 770335 1156373 := bbase (se 6 (by rfl) ⟨27102, by rfl⟩ : syracuseStep 1156373 = 54205) (by norm_num)
theorem B4400405 : Blo 770335 4400405 := bbase (se 6 (by rfl) ⟨103134, by rfl⟩ : syracuseStep 4400405 = 206269) (by norm_num)
theorem B2827541 : Blo 770335 2827541 := bbase (se 6 (by rfl) ⟨66270, by rfl⟩ : syracuseStep 2827541 = 132541) (by norm_num)
theorem B1156397 : Blo 770335 1156397 := bbase (se 3 (by rfl) ⟨216824, by rfl⟩ : syracuseStep 1156397 = 433649) (by norm_num)
theorem B1156421 : Blo 770335 1156421 := bbase (se 4 (by rfl) ⟨108414, by rfl⟩ : syracuseStep 1156421 = 216829) (by norm_num)
theorem B1156445 : Blo 770335 1156445 := bbase (se 3 (by rfl) ⟨216833, by rfl⟩ : syracuseStep 1156445 = 433667) (by norm_num)
theorem B1647965 : Blo 770335 1647965 := bbase (se 3 (by rfl) ⟨308993, by rfl⟩ : syracuseStep 1647965 = 617987) (by norm_num)
theorem B1647973 : Blo 770335 1647973 := bbase (se 4 (by rfl) ⟨154497, by rfl⟩ : syracuseStep 1647973 = 308995) (by norm_num)
theorem B1156469 : Blo 770335 1156469 := bbase (se 5 (by rfl) ⟨54209, by rfl⟩ : syracuseStep 1156469 = 108419) (by norm_num)
theorem B1156493 : Blo 770335 1156493 := bbase (se 3 (by rfl) ⟨216842, by rfl⟩ : syracuseStep 1156493 = 433685) (by norm_num)
theorem B1156517 : Blo 770335 1156517 := bbase (se 4 (by rfl) ⟨108423, by rfl⟩ : syracuseStep 1156517 = 216847) (by norm_num)
theorem B2860469 : Blo 770335 2860469 := bbase (se 5 (by rfl) ⟨134084, by rfl⟩ : syracuseStep 2860469 = 268169) (by norm_num)
theorem B992693 : Blo 770335 992693 := bbase (se 5 (by rfl) ⟨46532, by rfl⟩ : syracuseStep 992693 = 93065) (by norm_num)
theorem B1156541 : Blo 770335 1156541 := bbase (se 3 (by rfl) ⟨216851, by rfl⟩ : syracuseStep 1156541 = 433703) (by norm_num)
theorem B1156565 : Blo 770335 1156565 := bbase (se 7 (by rfl) ⟨13553, by rfl⟩ : syracuseStep 1156565 = 27107) (by norm_num)
theorem B1156589 : Blo 770335 1156589 := bbase (se 3 (by rfl) ⟨216860, by rfl⟩ : syracuseStep 1156589 = 433721) (by norm_num)
theorem B1156613 : Blo 770335 1156613 := bbase (se 4 (by rfl) ⟨108432, by rfl⟩ : syracuseStep 1156613 = 216865) (by norm_num)
theorem B1254917 : Blo 770335 1254917 := bbase (se 4 (by rfl) ⟨117648, by rfl⟩ : syracuseStep 1254917 = 235297) (by norm_num)
theorem B1156637 : Blo 770335 1156637 := bbase (se 3 (by rfl) ⟨216869, by rfl⟩ : syracuseStep 1156637 = 433739) (by norm_num)
theorem B1156661 : Blo 770335 1156661 := bbase (se 5 (by rfl) ⟨54218, by rfl⟩ : syracuseStep 1156661 = 108437) (by norm_num)
theorem B5875253 : Blo 770335 5875253 := bbase (se 5 (by rfl) ⟨275402, by rfl⟩ : syracuseStep 5875253 = 550805) (by norm_num)
theorem B1156685 : Blo 770335 1156685 := bbase (se 3 (by rfl) ⟨216878, by rfl⟩ : syracuseStep 1156685 = 433757) (by norm_num)
theorem B1156709 : Blo 770335 1156709 := bbase (se 4 (by rfl) ⟨108441, by rfl⟩ : syracuseStep 1156709 = 216883) (by norm_num)
theorem B3909221 : Blo 770335 3909221 := bbase (se 4 (by rfl) ⟨366489, by rfl⟩ : syracuseStep 3909221 = 732979) (by norm_num)
theorem B1156733 : Blo 770335 1156733 := bbase (se 3 (by rfl) ⟨216887, by rfl⟩ : syracuseStep 1156733 = 433775) (by norm_num)
theorem B1156757 : Blo 770335 1156757 := bbase (se 6 (by rfl) ⟨27111, by rfl⟩ : syracuseStep 1156757 = 54223) (by norm_num)
theorem B927389 : Blo 770335 927389 := bbase (se 3 (by rfl) ⟨173885, by rfl⟩ : syracuseStep 927389 = 347771) (by norm_num)
theorem B1156781 : Blo 770335 1156781 := bbase (se 3 (by rfl) ⟨216896, by rfl⟩ : syracuseStep 1156781 = 433793) (by norm_num)
theorem B1156805 : Blo 770335 1156805 := bbase (se 4 (by rfl) ⟨108450, by rfl⟩ : syracuseStep 1156805 = 216901) (by norm_num)
theorem B1156829 : Blo 770335 1156829 := bbase (se 3 (by rfl) ⟨216905, by rfl⟩ : syracuseStep 1156829 = 433811) (by norm_num)
theorem B1156853 : Blo 770335 1156853 := bbase (se 5 (by rfl) ⟨54227, by rfl⟩ : syracuseStep 1156853 = 108455) (by norm_num)
theorem B1156877 : Blo 770335 1156877 := bbase (se 3 (by rfl) ⟨216914, by rfl⟩ : syracuseStep 1156877 = 433829) (by norm_num)
theorem B1156901 : Blo 770335 1156901 := bbase (se 4 (by rfl) ⟨108459, by rfl⟩ : syracuseStep 1156901 = 216919) (by norm_num)
theorem B1156925 : Blo 770335 1156925 := bbase (se 3 (by rfl) ⟨216923, by rfl⟩ : syracuseStep 1156925 = 433847) (by norm_num)
theorem B1156949 : Blo 770335 1156949 := bbase (se 9 (by rfl) ⟨3389, by rfl⟩ : syracuseStep 1156949 = 6779) (by norm_num)
theorem B1156973 : Blo 770335 1156973 := bbase (se 3 (by rfl) ⟨216932, by rfl⟩ : syracuseStep 1156973 = 433865) (by norm_num)
theorem B1156997 : Blo 770335 1156997 := bbase (se 4 (by rfl) ⟨108468, by rfl⟩ : syracuseStep 1156997 = 216937) (by norm_num)
theorem B1157021 : Blo 770335 1157021 := bbase (se 3 (by rfl) ⟨216941, by rfl⟩ : syracuseStep 1157021 = 433883) (by norm_num)
theorem B927649 : Blo 770335 927649 := bbase (se 2 (by rfl) ⟨347868, by rfl⟩ : syracuseStep 927649 = 695737) (by norm_num)
theorem B1157045 : Blo 770335 1157045 := bbase (se 5 (by rfl) ⟨54236, by rfl⟩ : syracuseStep 1157045 = 108473) (by norm_num)
theorem B1157069 : Blo 770335 1157069 := bbase (se 3 (by rfl) ⟨216950, by rfl⟩ : syracuseStep 1157069 = 433901) (by norm_num)
theorem B1157093 : Blo 770335 1157093 := bbase (se 4 (by rfl) ⟨108477, by rfl⟩ : syracuseStep 1157093 = 216955) (by norm_num)
theorem B1157117 : Blo 770335 1157117 := bbase (se 3 (by rfl) ⟨216959, by rfl⟩ : syracuseStep 1157117 = 433919) (by norm_num)
theorem B1157141 : Blo 770335 1157141 := bbase (se 6 (by rfl) ⟨27120, by rfl⟩ : syracuseStep 1157141 = 54241) (by norm_num)
theorem B1157165 : Blo 770335 1157165 := bbase (se 3 (by rfl) ⟨216968, by rfl⟩ : syracuseStep 1157165 = 433937) (by norm_num)
theorem B1157189 : Blo 770335 1157189 := bbase (se 4 (by rfl) ⟨108486, by rfl⟩ : syracuseStep 1157189 = 216973) (by norm_num)
theorem B993349 : Blo 770335 993349 := bbase (se 4 (by rfl) ⟨93126, by rfl⟩ : syracuseStep 993349 = 186253) (by norm_num)
theorem B1157213 : Blo 770335 1157213 := bbase (se 3 (by rfl) ⟨216977, by rfl⟩ : syracuseStep 1157213 = 433955) (by norm_num)
theorem B927841 : Blo 770335 927841 := bbase (se 2 (by rfl) ⟨347940, by rfl⟩ : syracuseStep 927841 = 695881) (by norm_num)
theorem B1157237 : Blo 770335 1157237 := bbase (se 5 (by rfl) ⟨54245, by rfl⟩ : syracuseStep 1157237 = 108491) (by norm_num)
theorem B927865 : Blo 770335 927865 := bbase (se 2 (by rfl) ⟨347949, by rfl⟩ : syracuseStep 927865 = 695899) (by norm_num)
theorem B927869 : Blo 770335 927869 := bbase (se 3 (by rfl) ⟨173975, by rfl⟩ : syracuseStep 927869 = 347951) (by norm_num)
theorem B1157261 : Blo 770335 1157261 := bbase (se 3 (by rfl) ⟨216986, by rfl⟩ : syracuseStep 1157261 = 433973) (by norm_num)
theorem B1157285 : Blo 770335 1157285 := bbase (se 4 (by rfl) ⟨108495, by rfl⟩ : syracuseStep 1157285 = 216991) (by norm_num)
theorem B1157309 : Blo 770335 1157309 := bbase (se 3 (by rfl) ⟨216995, by rfl⟩ : syracuseStep 1157309 = 433991) (by norm_num)
theorem B1157333 : Blo 770335 1157333 := bbase (se 7 (by rfl) ⟨13562, by rfl⟩ : syracuseStep 1157333 = 27125) (by norm_num)
theorem B1157357 : Blo 770335 1157357 := bbase (se 3 (by rfl) ⟨217004, by rfl⟩ : syracuseStep 1157357 = 434009) (by norm_num)
theorem B4466933 : Blo 770335 4466933 := bbase (se 5 (by rfl) ⟨209387, by rfl⟩ : syracuseStep 4466933 = 418775) (by norm_num)
theorem B1157381 : Blo 770335 1157381 := bbase (se 4 (by rfl) ⟨108504, by rfl⟩ : syracuseStep 1157381 = 217009) (by norm_num)
theorem B1157405 : Blo 770335 1157405 := bbase (se 3 (by rfl) ⟨217013, by rfl⟩ : syracuseStep 1157405 = 434027) (by norm_num)
theorem B1976621 : Blo 770335 1976621 := bbase (se 3 (by rfl) ⟨370616, by rfl⟩ : syracuseStep 1976621 = 741233) (by norm_num)
theorem B1157429 : Blo 770335 1157429 := bbase (se 5 (by rfl) ⟨54254, by rfl⟩ : syracuseStep 1157429 = 108509) (by norm_num)
theorem B1157453 : Blo 770335 1157453 := bbase (se 3 (by rfl) ⟨217022, by rfl⟩ : syracuseStep 1157453 = 434045) (by norm_num)
theorem B1157477 : Blo 770335 1157477 := bbase (se 4 (by rfl) ⟨108513, by rfl⟩ : syracuseStep 1157477 = 217027) (by norm_num)
theorem B1157501 : Blo 770335 1157501 := bbase (se 3 (by rfl) ⟨217031, by rfl⟩ : syracuseStep 1157501 = 434063) (by norm_num)
theorem B1157525 : Blo 770335 1157525 := bbase (se 6 (by rfl) ⟨27129, by rfl⟩ : syracuseStep 1157525 = 54259) (by norm_num)
theorem B1157549 : Blo 770335 1157549 := bbase (se 3 (by rfl) ⟨217040, by rfl⟩ : syracuseStep 1157549 = 434081) (by norm_num)
theorem B1157573 : Blo 770335 1157573 := bbase (se 4 (by rfl) ⟨108522, by rfl⟩ : syracuseStep 1157573 = 217045) (by norm_num)
theorem B1649101 : Blo 770335 1649101 := bbase (se 3 (by rfl) ⟨309206, by rfl⟩ : syracuseStep 1649101 = 618413) (by norm_num)
theorem B1157597 : Blo 770335 1157597 := bbase (se 3 (by rfl) ⟨217049, by rfl⟩ : syracuseStep 1157597 = 434099) (by norm_num)
theorem B1157621 : Blo 770335 1157621 := bbase (se 5 (by rfl) ⟨54263, by rfl⟩ : syracuseStep 1157621 = 108527) (by norm_num)
theorem B1157645 : Blo 770335 1157645 := bbase (se 3 (by rfl) ⟨217058, by rfl⟩ : syracuseStep 1157645 = 434117) (by norm_num)
theorem B1878565 : Blo 770335 1878565 := bbase (se 4 (by rfl) ⟨176115, by rfl⟩ : syracuseStep 1878565 = 352231) (by norm_num)
theorem B1157669 : Blo 770335 1157669 := bbase (se 4 (by rfl) ⟨108531, by rfl⟩ : syracuseStep 1157669 = 217063) (by norm_num)
theorem B1321525 : Blo 770335 1321525 := bbase (se 5 (by rfl) ⟨61946, by rfl⟩ : syracuseStep 1321525 = 123893) (by norm_num)
theorem B1157693 : Blo 770335 1157693 := bbase (se 3 (by rfl) ⟨217067, by rfl⟩ : syracuseStep 1157693 = 434135) (by norm_num)
theorem B1157717 : Blo 770335 1157717 := bbase (se 8 (by rfl) ⟨6783, by rfl⟩ : syracuseStep 1157717 = 13567) (by norm_num)
theorem B1157741 : Blo 770335 1157741 := bbase (se 3 (by rfl) ⟨217076, by rfl⟩ : syracuseStep 1157741 = 434153) (by norm_num)
theorem B928369 : Blo 770335 928369 := bbase (se 2 (by rfl) ⟨348138, by rfl⟩ : syracuseStep 928369 = 696277) (by norm_num)
theorem B1157765 : Blo 770335 1157765 := bbase (se 4 (by rfl) ⟨108540, by rfl⟩ : syracuseStep 1157765 = 217081) (by norm_num)
theorem B2468501 : Blo 770335 2468501 := bbase (se 6 (by rfl) ⟨57855, by rfl⟩ : syracuseStep 2468501 = 115711) (by norm_num)
theorem B1157789 : Blo 770335 1157789 := bbase (se 3 (by rfl) ⟨217085, by rfl⟩ : syracuseStep 1157789 = 434171) (by norm_num)
theorem B2927285 : Blo 770335 2927285 := bbase (se 5 (by rfl) ⟨137216, by rfl⟩ : syracuseStep 2927285 = 274433) (by norm_num)
theorem B1157813 : Blo 770335 1157813 := bbase (se 5 (by rfl) ⟨54272, by rfl⟩ : syracuseStep 1157813 = 108545) (by norm_num)
theorem B1157837 : Blo 770335 1157837 := bbase (se 3 (by rfl) ⟨217094, by rfl⟩ : syracuseStep 1157837 = 434189) (by norm_num)
theorem B928465 : Blo 770335 928465 := bbase (se 2 (by rfl) ⟨348174, by rfl⟩ : syracuseStep 928465 = 696349) (by norm_num)
theorem B1157861 : Blo 770335 1157861 := bbase (se 4 (by rfl) ⟨108549, by rfl⟩ : syracuseStep 1157861 = 217099) (by norm_num)
theorem B1157885 : Blo 770335 1157885 := bbase (se 3 (by rfl) ⟨217103, by rfl⟩ : syracuseStep 1157885 = 434207) (by norm_num)
theorem B1157909 : Blo 770335 1157909 := bbase (se 6 (by rfl) ⟨27138, by rfl⟩ : syracuseStep 1157909 = 54277) (by norm_num)
theorem B1157933 : Blo 770335 1157933 := bbase (se 3 (by rfl) ⟨217112, by rfl⟩ : syracuseStep 1157933 = 434225) (by norm_num)
theorem B1157957 : Blo 770335 1157957 := bbase (se 4 (by rfl) ⟨108558, by rfl⟩ : syracuseStep 1157957 = 217117) (by norm_num)
theorem B1649477 : Blo 770335 1649477 := bbase (se 4 (by rfl) ⟨154638, by rfl⟩ : syracuseStep 1649477 = 309277) (by norm_num)
theorem B1157981 : Blo 770335 1157981 := bbase (se 3 (by rfl) ⟨217121, by rfl⟩ : syracuseStep 1157981 = 434243) (by norm_num)
theorem B1158005 : Blo 770335 1158005 := bbase (se 5 (by rfl) ⟨54281, by rfl⟩ : syracuseStep 1158005 = 108563) (by norm_num)
theorem B3910517 : Blo 770335 3910517 := bbase (se 5 (by rfl) ⟨183305, by rfl⟩ : syracuseStep 3910517 = 366611) (by norm_num)
theorem B1158029 : Blo 770335 1158029 := bbase (se 3 (by rfl) ⟨217130, by rfl⟩ : syracuseStep 1158029 = 434261) (by norm_num)
theorem B1158053 : Blo 770335 1158053 := bbase (se 4 (by rfl) ⟨108567, by rfl⟩ : syracuseStep 1158053 = 217135) (by norm_num)
theorem B1158077 : Blo 770335 1158077 := bbase (se 3 (by rfl) ⟨217139, by rfl⟩ : syracuseStep 1158077 = 434279) (by norm_num)
theorem B2927573 : Blo 770335 2927573 := bbase (se 7 (by rfl) ⟨34307, by rfl⟩ : syracuseStep 2927573 = 68615) (by norm_num)
theorem B18754517 : Blo 770335 18754517 := bbase (se 7 (by rfl) ⟨219779, by rfl⟩ : syracuseStep 18754517 = 439559) (by norm_num)
theorem B1158101 : Blo 770335 1158101 := bbase (se 7 (by rfl) ⟨13571, by rfl⟩ : syracuseStep 1158101 = 27143) (by norm_num)
theorem B1158125 : Blo 770335 1158125 := bbase (se 3 (by rfl) ⟨217148, by rfl⟩ : syracuseStep 1158125 = 434297) (by norm_num)
theorem B1158149 : Blo 770335 1158149 := bbase (se 4 (by rfl) ⟨108576, by rfl⟩ : syracuseStep 1158149 = 217153) (by norm_num)
theorem B1158173 : Blo 770335 1158173 := bbase (se 3 (by rfl) ⟨217157, by rfl⟩ : syracuseStep 1158173 = 434315) (by norm_num)
theorem B1158197 : Blo 770335 1158197 := bbase (se 5 (by rfl) ⟨54290, by rfl⟩ : syracuseStep 1158197 = 108581) (by norm_num)
theorem B1158221 : Blo 770335 1158221 := bbase (se 3 (by rfl) ⟨217166, by rfl⟩ : syracuseStep 1158221 = 434333) (by norm_num)
theorem B1158245 : Blo 770335 1158245 := bbase (se 4 (by rfl) ⟨108585, by rfl⟩ : syracuseStep 1158245 = 217171) (by norm_num)
theorem B1158269 : Blo 770335 1158269 := bbase (se 3 (by rfl) ⟨217175, by rfl⟩ : syracuseStep 1158269 = 434351) (by norm_num)
theorem B1158293 : Blo 770335 1158293 := bbase (se 6 (by rfl) ⟨27147, by rfl⟩ : syracuseStep 1158293 = 54295) (by norm_num)
theorem B1158317 : Blo 770335 1158317 := bbase (se 3 (by rfl) ⟨217184, by rfl⟩ : syracuseStep 1158317 = 434369) (by norm_num)
theorem B1158341 : Blo 770335 1158341 := bbase (se 4 (by rfl) ⟨108594, by rfl⟩ : syracuseStep 1158341 = 217189) (by norm_num)
theorem B3714245 : Blo 770335 3714245 := bbase (se 4 (by rfl) ⟨348210, by rfl⟩ : syracuseStep 3714245 = 696421) (by norm_num)
theorem B1158365 : Blo 770335 1158365 := bbase (se 3 (by rfl) ⟨217193, by rfl⟩ : syracuseStep 1158365 = 434387) (by norm_num)
theorem B1158389 : Blo 770335 1158389 := bbase (se 5 (by rfl) ⟨54299, by rfl⟩ : syracuseStep 1158389 = 108599) (by norm_num)
theorem B1158413 : Blo 770335 1158413 := bbase (se 3 (by rfl) ⟨217202, by rfl⟩ : syracuseStep 1158413 = 434405) (by norm_num)
theorem B7417109 : Blo 770335 7417109 := bbase (se 6 (by rfl) ⟨173838, by rfl⟩ : syracuseStep 7417109 = 347677) (by norm_num)
theorem B1158437 : Blo 770335 1158437 := bbase (se 4 (by rfl) ⟨108603, by rfl⟩ : syracuseStep 1158437 = 217207) (by norm_num)
theorem B1158461 : Blo 770335 1158461 := bbase (se 3 (by rfl) ⟨217211, by rfl⟩ : syracuseStep 1158461 = 434423) (by norm_num)
theorem B2600261 : Blo 770335 2600261 := bbase (se 4 (by rfl) ⟨243774, by rfl⟩ : syracuseStep 2600261 = 487549) (by norm_num)
theorem B1158485 : Blo 770335 1158485 := bbase (se 11 (by rfl) ⟨848, by rfl⟩ : syracuseStep 1158485 = 1697) (by norm_num)
theorem B1977709 : Blo 770335 1977709 := bbase (se 3 (by rfl) ⟨370820, by rfl⟩ : syracuseStep 1977709 = 741641) (by norm_num)
theorem B1158509 : Blo 770335 1158509 := bbase (se 3 (by rfl) ⟨217220, by rfl⟩ : syracuseStep 1158509 = 434441) (by norm_num)
theorem B1158533 : Blo 770335 1158533 := bbase (se 4 (by rfl) ⟨108612, by rfl⟩ : syracuseStep 1158533 = 217225) (by norm_num)
theorem B3714437 : Blo 770335 3714437 := bbase (se 4 (by rfl) ⟨348228, by rfl⟩ : syracuseStep 3714437 = 696457) (by norm_num)
theorem B1486237 : Blo 770335 1486237 := bbase (se 3 (by rfl) ⟨278669, by rfl⟩ : syracuseStep 1486237 = 557339) (by norm_num)
theorem B1158557 : Blo 770335 1158557 := bbase (se 3 (by rfl) ⟨217229, by rfl⟩ : syracuseStep 1158557 = 434459) (by norm_num)
theorem B1158581 : Blo 770335 1158581 := bbase (se 5 (by rfl) ⟨54308, by rfl⟩ : syracuseStep 1158581 = 108617) (by norm_num)
theorem B4402613 : Blo 770335 4402613 := bbase (se 5 (by rfl) ⟨206372, by rfl⟩ : syracuseStep 4402613 = 412745) (by norm_num)
theorem B1158605 : Blo 770335 1158605 := bbase (se 3 (by rfl) ⟨217238, by rfl⟩ : syracuseStep 1158605 = 434477) (by norm_num)
theorem B1158629 : Blo 770335 1158629 := bbase (se 4 (by rfl) ⟨108621, by rfl⟩ : syracuseStep 1158629 = 217243) (by norm_num)
theorem B1158653 : Blo 770335 1158653 := bbase (se 3 (by rfl) ⟨217247, by rfl⟩ : syracuseStep 1158653 = 434495) (by norm_num)
theorem B1158677 : Blo 770335 1158677 := bbase (se 6 (by rfl) ⟨27156, by rfl⟩ : syracuseStep 1158677 = 54313) (by norm_num)
theorem B1158701 : Blo 770335 1158701 := bbase (se 3 (by rfl) ⟨217256, by rfl⟩ : syracuseStep 1158701 = 434513) (by norm_num)
theorem B1158725 : Blo 770335 1158725 := bbase (se 4 (by rfl) ⟨108630, by rfl⟩ : syracuseStep 1158725 = 217261) (by norm_num)
theorem B1158749 : Blo 770335 1158749 := bbase (se 3 (by rfl) ⟨217265, by rfl⟩ : syracuseStep 1158749 = 434531) (by norm_num)
theorem B1158773 : Blo 770335 1158773 := bbase (se 5 (by rfl) ⟨54317, by rfl⟩ : syracuseStep 1158773 = 108635) (by norm_num)
theorem B1158797 : Blo 770335 1158797 := bbase (se 3 (by rfl) ⟨217274, by rfl⟩ : syracuseStep 1158797 = 434549) (by norm_num)
theorem B929441 : Blo 770335 929441 := bbase (se 2 (by rfl) ⟨348540, by rfl⟩ : syracuseStep 929441 = 697081) (by norm_num)
theorem B1158821 : Blo 770335 1158821 := bbase (se 4 (by rfl) ⟨108639, by rfl⟩ : syracuseStep 1158821 = 217279) (by norm_num)
theorem B1158845 : Blo 770335 1158845 := bbase (se 3 (by rfl) ⟨217283, by rfl⟩ : syracuseStep 1158845 = 434567) (by norm_num)
theorem B1158869 : Blo 770335 1158869 := bbase (se 7 (by rfl) ⟨13580, by rfl⟩ : syracuseStep 1158869 = 27161) (by norm_num)
theorem B1158893 : Blo 770335 1158893 := bbase (se 3 (by rfl) ⟨217292, by rfl⟩ : syracuseStep 1158893 = 434585) (by norm_num)
theorem B2600693 : Blo 770335 2600693 := bbase (se 5 (by rfl) ⟨121907, by rfl⟩ : syracuseStep 2600693 = 243815) (by norm_num)
theorem B1158917 : Blo 770335 1158917 := bbase (se 4 (by rfl) ⟨108648, by rfl⟩ : syracuseStep 1158917 = 217297) (by norm_num)
theorem B6598421 : Blo 770335 6598421 := bbase (se 6 (by rfl) ⟨154650, by rfl⟩ : syracuseStep 6598421 = 309301) (by norm_num)
theorem B1158941 : Blo 770335 1158941 := bbase (se 3 (by rfl) ⟨217301, by rfl⟩ : syracuseStep 1158941 = 434603) (by norm_num)
theorem B1158965 : Blo 770335 1158965 := bbase (se 5 (by rfl) ⟨54326, by rfl⟩ : syracuseStep 1158965 = 108653) (by norm_num)
theorem B1158989 : Blo 770335 1158989 := bbase (se 3 (by rfl) ⟨217310, by rfl⟩ : syracuseStep 1158989 = 434621) (by norm_num)
theorem B1159013 : Blo 770335 1159013 := bbase (se 4 (by rfl) ⟨108657, by rfl⟩ : syracuseStep 1159013 = 217315) (by norm_num)
theorem B1159037 : Blo 770335 1159037 := bbase (se 3 (by rfl) ⟨217319, by rfl⟩ : syracuseStep 1159037 = 434639) (by norm_num)
theorem B1159061 : Blo 770335 1159061 := bbase (se 6 (by rfl) ⟨27165, by rfl⟩ : syracuseStep 1159061 = 54331) (by norm_num)
theorem B1159085 : Blo 770335 1159085 := bbase (se 3 (by rfl) ⟨217328, by rfl⟩ : syracuseStep 1159085 = 434657) (by norm_num)
theorem B1159109 : Blo 770335 1159109 := bbase (se 4 (by rfl) ⟨108666, by rfl⟩ : syracuseStep 1159109 = 217333) (by norm_num)
theorem B1159133 : Blo 770335 1159133 := bbase (se 3 (by rfl) ⟨217337, by rfl⟩ : syracuseStep 1159133 = 434675) (by norm_num)
theorem B1159157 : Blo 770335 1159157 := bbase (se 5 (by rfl) ⟨54335, by rfl⟩ : syracuseStep 1159157 = 108671) (by norm_num)
theorem B1159181 : Blo 770335 1159181 := bbase (se 3 (by rfl) ⟨217346, by rfl⟩ : syracuseStep 1159181 = 434693) (by norm_num)
theorem B1159205 : Blo 770335 1159205 := bbase (se 4 (by rfl) ⟨108675, by rfl⟩ : syracuseStep 1159205 = 217351) (by norm_num)
theorem B1159229 : Blo 770335 1159229 := bbase (se 3 (by rfl) ⟨217355, by rfl⟩ : syracuseStep 1159229 = 434711) (by norm_num)
theorem B1159253 : Blo 770335 1159253 := bbase (se 8 (by rfl) ⟨6792, by rfl⟩ : syracuseStep 1159253 = 13585) (by norm_num)
theorem B1159277 : Blo 770335 1159277 := bbase (se 3 (by rfl) ⟨217364, by rfl⟩ : syracuseStep 1159277 = 434729) (by norm_num)
theorem B2928757 : Blo 770335 2928757 := bbase (se 5 (by rfl) ⟨137285, by rfl⟩ : syracuseStep 2928757 = 274571) (by norm_num)
theorem B929917 : Blo 770335 929917 := bbase (se 3 (by rfl) ⟨174359, by rfl⟩ : syracuseStep 929917 = 348719) (by norm_num)
theorem B3911813 : Blo 770335 3911813 := bbase (se 4 (by rfl) ⟨366732, by rfl⟩ : syracuseStep 3911813 = 733465) (by norm_num)
theorem B1159301 : Blo 770335 1159301 := bbase (se 4 (by rfl) ⟨108684, by rfl⟩ : syracuseStep 1159301 = 217369) (by norm_num)
theorem B929945 : Blo 770335 929945 := bbase (se 2 (by rfl) ⟨348729, by rfl⟩ : syracuseStep 929945 = 697459) (by norm_num)
theorem B1159325 : Blo 770335 1159325 := bbase (se 3 (by rfl) ⟨217373, by rfl⟩ : syracuseStep 1159325 = 434747) (by norm_num)
theorem B2601125 : Blo 770335 2601125 := bbase (se 4 (by rfl) ⟨243855, by rfl⟩ : syracuseStep 2601125 = 487711) (by norm_num)
theorem B1159349 : Blo 770335 1159349 := bbase (se 5 (by rfl) ⟨54344, by rfl⟩ : syracuseStep 1159349 = 108689) (by norm_num)
theorem B1159373 : Blo 770335 1159373 := bbase (se 3 (by rfl) ⟨217382, by rfl⟩ : syracuseStep 1159373 = 434765) (by norm_num)
theorem B1159397 : Blo 770335 1159397 := bbase (se 4 (by rfl) ⟨108693, by rfl⟩ : syracuseStep 1159397 = 217387) (by norm_num)
theorem B1159421 : Blo 770335 1159421 := bbase (se 3 (by rfl) ⟨217391, by rfl⟩ : syracuseStep 1159421 = 434783) (by norm_num)
theorem B1159445 : Blo 770335 1159445 := bbase (se 6 (by rfl) ⟨27174, by rfl⟩ : syracuseStep 1159445 = 54349) (by norm_num)
theorem B1159469 : Blo 770335 1159469 := bbase (se 3 (by rfl) ⟨217400, by rfl⟩ : syracuseStep 1159469 = 434801) (by norm_num)
theorem B1585469 : Blo 770335 1585469 := bbase (se 3 (by rfl) ⟨297275, by rfl⟩ : syracuseStep 1585469 = 594551) (by norm_num)
theorem B1159493 : Blo 770335 1159493 := bbase (se 4 (by rfl) ⟨108702, by rfl⟩ : syracuseStep 1159493 = 217405) (by norm_num)
theorem B930133 : Blo 770335 930133 := bbase (se 10 (by rfl) ⟨1362, by rfl⟩ : syracuseStep 930133 = 2725) (by norm_num)
theorem B1159517 : Blo 770335 1159517 := bbase (se 3 (by rfl) ⟨217409, by rfl⟩ : syracuseStep 1159517 = 434819) (by norm_num)
theorem B1159541 : Blo 770335 1159541 := bbase (se 5 (by rfl) ⟨54353, by rfl⟩ : syracuseStep 1159541 = 108707) (by norm_num)
theorem B1159565 : Blo 770335 1159565 := bbase (se 3 (by rfl) ⟨217418, by rfl⟩ : syracuseStep 1159565 = 434837) (by norm_num)
theorem B2929061 : Blo 770335 2929061 := bbase (se 4 (by rfl) ⟨274599, by rfl⟩ : syracuseStep 2929061 = 549199) (by norm_num)
theorem B1159589 : Blo 770335 1159589 := bbase (se 4 (by rfl) ⟨108711, by rfl⟩ : syracuseStep 1159589 = 217423) (by norm_num)
theorem B1651117 : Blo 770335 1651117 := bbase (se 3 (by rfl) ⟨309584, by rfl⟩ : syracuseStep 1651117 = 619169) (by norm_num)
theorem B7516597 : Blo 770335 7516597 := bbase (se 5 (by rfl) ⟨352340, by rfl⟩ : syracuseStep 7516597 = 704681) (by norm_num)
theorem B1159613 : Blo 770335 1159613 := bbase (se 3 (by rfl) ⟨217427, by rfl⟩ : syracuseStep 1159613 = 434855) (by norm_num)
theorem B930253 : Blo 770335 930253 := bbase (se 3 (by rfl) ⟨174422, by rfl⟩ : syracuseStep 930253 = 348845) (by norm_num)
theorem B1159637 : Blo 770335 1159637 := bbase (se 7 (by rfl) ⟨13589, by rfl⟩ : syracuseStep 1159637 = 27179) (by norm_num)
theorem B1159661 : Blo 770335 1159661 := bbase (se 3 (by rfl) ⟨217436, by rfl⟩ : syracuseStep 1159661 = 434873) (by norm_num)
theorem B1159685 : Blo 770335 1159685 := bbase (se 4 (by rfl) ⟨108720, by rfl⟩ : syracuseStep 1159685 = 217441) (by norm_num)
theorem B1159709 : Blo 770335 1159709 := bbase (se 3 (by rfl) ⟨217445, by rfl⟩ : syracuseStep 1159709 = 434891) (by norm_num)
theorem B1159733 : Blo 770335 1159733 := bbase (se 5 (by rfl) ⟨54362, by rfl⟩ : syracuseStep 1159733 = 108725) (by norm_num)
theorem B1159757 : Blo 770335 1159757 := bbase (se 3 (by rfl) ⟨217454, by rfl⟩ : syracuseStep 1159757 = 434909) (by norm_num)
theorem B2601557 : Blo 770335 2601557 := bbase (se 8 (by rfl) ⟨15243, by rfl⟩ : syracuseStep 2601557 = 30487) (by norm_num)
theorem B1159781 : Blo 770335 1159781 := bbase (se 4 (by rfl) ⟨108729, by rfl⟩ : syracuseStep 1159781 = 217459) (by norm_num)
theorem B1159805 : Blo 770335 1159805 := bbase (se 3 (by rfl) ⟨217463, by rfl⟩ : syracuseStep 1159805 = 434927) (by norm_num)
theorem B1159829 : Blo 770335 1159829 := bbase (se 6 (by rfl) ⟨27183, by rfl⟩ : syracuseStep 1159829 = 54367) (by norm_num)
theorem B1159853 : Blo 770335 1159853 := bbase (se 3 (by rfl) ⟨217472, by rfl⟩ : syracuseStep 1159853 = 434945) (by norm_num)
theorem B1159877 : Blo 770335 1159877 := bbase (se 4 (by rfl) ⟨108738, by rfl⟩ : syracuseStep 1159877 = 217477) (by norm_num)
theorem B1159901 : Blo 770335 1159901 := bbase (se 3 (by rfl) ⟨217481, by rfl⟩ : syracuseStep 1159901 = 434963) (by norm_num)
theorem B1159925 : Blo 770335 1159925 := bbase (se 5 (by rfl) ⟨54371, by rfl⟩ : syracuseStep 1159925 = 108743) (by norm_num)
theorem B1389325 : Blo 770335 1389325 := bbase (se 3 (by rfl) ⟨260498, by rfl⟩ : syracuseStep 1389325 = 520997) (by norm_num)
theorem B1159949 : Blo 770335 1159949 := bbase (se 3 (by rfl) ⟨217490, by rfl⟩ : syracuseStep 1159949 = 434981) (by norm_num)
theorem B1159973 : Blo 770335 1159973 := bbase (se 4 (by rfl) ⟨108747, by rfl⟩ : syracuseStep 1159973 = 217495) (by norm_num)
theorem B1159997 : Blo 770335 1159997 := bbase (se 3 (by rfl) ⟨217499, by rfl⟩ : syracuseStep 1159997 = 434999) (by norm_num)
theorem B1160021 : Blo 770335 1160021 := bbase (se 9 (by rfl) ⟨3398, by rfl⟩ : syracuseStep 1160021 = 6797) (by norm_num)
theorem B1160045 : Blo 770335 1160045 := bbase (se 3 (by rfl) ⟨217508, by rfl⟩ : syracuseStep 1160045 = 435017) (by norm_num)
theorem B1160069 : Blo 770335 1160069 := bbase (se 4 (by rfl) ⟨108756, by rfl⟩ : syracuseStep 1160069 = 217513) (by norm_num)
theorem B1389469 : Blo 770335 1389469 := bbase (se 3 (by rfl) ⟨260525, by rfl⟩ : syracuseStep 1389469 = 521051) (by norm_num)
theorem B1160093 : Blo 770335 1160093 := bbase (se 3 (by rfl) ⟨217517, by rfl⟩ : syracuseStep 1160093 = 435035) (by norm_num)
theorem B1160117 : Blo 770335 1160117 := bbase (se 5 (by rfl) ⟨54380, by rfl⟩ : syracuseStep 1160117 = 108761) (by norm_num)
theorem B1160141 : Blo 770335 1160141 := bbase (se 3 (by rfl) ⟨217526, by rfl⟩ : syracuseStep 1160141 = 435053) (by norm_num)
theorem B1160165 : Blo 770335 1160165 := bbase (se 4 (by rfl) ⟨108765, by rfl⟩ : syracuseStep 1160165 = 217531) (by norm_num)
theorem B1160189 : Blo 770335 1160189 := bbase (se 3 (by rfl) ⟨217535, by rfl⟩ : syracuseStep 1160189 = 435071) (by norm_num)
theorem B2601989 : Blo 770335 2601989 := bbase (se 4 (by rfl) ⟨243936, by rfl⟩ : syracuseStep 2601989 = 487873) (by norm_num)
theorem B1160213 : Blo 770335 1160213 := bbase (se 6 (by rfl) ⟨27192, by rfl⟩ : syracuseStep 1160213 = 54385) (by norm_num)
theorem B1160237 : Blo 770335 1160237 := bbase (se 3 (by rfl) ⟨217544, by rfl⟩ : syracuseStep 1160237 = 435089) (by norm_num)
theorem B1389629 : Blo 770335 1389629 := bbase (se 3 (by rfl) ⟨260555, by rfl⟩ : syracuseStep 1389629 = 521111) (by norm_num)
theorem B1160261 : Blo 770335 1160261 := bbase (se 4 (by rfl) ⟨108774, by rfl⟩ : syracuseStep 1160261 = 217549) (by norm_num)
theorem B1160285 : Blo 770335 1160285 := bbase (se 3 (by rfl) ⟨217553, by rfl⟩ : syracuseStep 1160285 = 435107) (by norm_num)
theorem B1389685 : Blo 770335 1389685 := bbase (se 5 (by rfl) ⟨65141, by rfl⟩ : syracuseStep 1389685 = 130283) (by norm_num)
theorem B1160309 : Blo 770335 1160309 := bbase (se 5 (by rfl) ⟨54389, by rfl⟩ : syracuseStep 1160309 = 108779) (by norm_num)
theorem B1160333 : Blo 770335 1160333 := bbase (se 3 (by rfl) ⟨217562, by rfl⟩ : syracuseStep 1160333 = 435125) (by norm_num)
theorem B1160357 : Blo 770335 1160357 := bbase (se 4 (by rfl) ⟨108783, by rfl⟩ : syracuseStep 1160357 = 217567) (by norm_num)
theorem B1160381 : Blo 770335 1160381 := bbase (se 3 (by rfl) ⟨217571, by rfl⟩ : syracuseStep 1160381 = 435143) (by norm_num)
theorem B1160405 : Blo 770335 1160405 := bbase (se 7 (by rfl) ⟨13598, by rfl⟩ : syracuseStep 1160405 = 27197) (by norm_num)
theorem B1160429 : Blo 770335 1160429 := bbase (se 3 (by rfl) ⟨217580, by rfl⟩ : syracuseStep 1160429 = 435161) (by norm_num)
theorem B1160453 : Blo 770335 1160453 := bbase (se 4 (by rfl) ⟨108792, by rfl⟩ : syracuseStep 1160453 = 217585) (by norm_num)
theorem B1160477 : Blo 770335 1160477 := bbase (se 3 (by rfl) ⟨217589, by rfl⟩ : syracuseStep 1160477 = 435179) (by norm_num)
theorem B1652005 : Blo 770335 1652005 := bbase (se 4 (by rfl) ⟨154875, by rfl⟩ : syracuseStep 1652005 = 309751) (by norm_num)
theorem B1160501 : Blo 770335 1160501 := bbase (se 5 (by rfl) ⟨54398, by rfl⟩ : syracuseStep 1160501 = 108797) (by norm_num)
theorem B1160525 : Blo 770335 1160525 := bbase (se 3 (by rfl) ⟨217598, by rfl⟩ : syracuseStep 1160525 = 435197) (by norm_num)
theorem B2471269 : Blo 770335 2471269 := bbase (se 4 (by rfl) ⟨231681, by rfl⟩ : syracuseStep 2471269 = 463363) (by norm_num)
theorem B1160549 : Blo 770335 1160549 := bbase (se 4 (by rfl) ⟨108801, by rfl⟩ : syracuseStep 1160549 = 217603) (by norm_num)
theorem B1160573 : Blo 770335 1160573 := bbase (se 3 (by rfl) ⟨217607, by rfl⟩ : syracuseStep 1160573 = 435215) (by norm_num)
theorem B3913109 : Blo 770335 3913109 := bbase (se 6 (by rfl) ⟨91713, by rfl⟩ : syracuseStep 3913109 = 183427) (by norm_num)
theorem B1160597 : Blo 770335 1160597 := bbase (se 6 (by rfl) ⟨27201, by rfl⟩ : syracuseStep 1160597 = 54403) (by norm_num)
theorem B1160621 : Blo 770335 1160621 := bbase (se 3 (by rfl) ⟨217616, by rfl⟩ : syracuseStep 1160621 = 435233) (by norm_num)
theorem B2602421 : Blo 770335 2602421 := bbase (se 5 (by rfl) ⟨121988, by rfl⟩ : syracuseStep 2602421 = 243977) (by norm_num)
theorem B3716533 : Blo 770335 3716533 := bbase (se 5 (by rfl) ⟨174212, by rfl⟩ : syracuseStep 3716533 = 348425) (by norm_num)
theorem B1160645 : Blo 770335 1160645 := bbase (se 4 (by rfl) ⟨108810, by rfl⟩ : syracuseStep 1160645 = 217621) (by norm_num)
theorem B1160669 : Blo 770335 1160669 := bbase (se 3 (by rfl) ⟨217625, by rfl⟩ : syracuseStep 1160669 = 435251) (by norm_num)
theorem B1160693 : Blo 770335 1160693 := bbase (se 5 (by rfl) ⟨54407, by rfl⟩ : syracuseStep 1160693 = 108815) (by norm_num)
theorem B1160717 : Blo 770335 1160717 := bbase (se 3 (by rfl) ⟨217634, by rfl⟩ : syracuseStep 1160717 = 435269) (by norm_num)
theorem B1160741 : Blo 770335 1160741 := bbase (se 4 (by rfl) ⟨108819, by rfl⟩ : syracuseStep 1160741 = 217639) (by norm_num)
theorem B1160765 : Blo 770335 1160765 := bbase (se 3 (by rfl) ⟨217643, by rfl⟩ : syracuseStep 1160765 = 435287) (by norm_num)
theorem B8336981 : Blo 770335 8336981 := bbase (se 8 (by rfl) ⟨48849, by rfl⟩ : syracuseStep 8336981 = 97699) (by norm_num)
theorem B1160789 : Blo 770335 1160789 := bbase (se 8 (by rfl) ⟨6801, by rfl⟩ : syracuseStep 1160789 = 13603) (by norm_num)
theorem B1160813 : Blo 770335 1160813 := bbase (se 3 (by rfl) ⟨217652, by rfl⟩ : syracuseStep 1160813 = 435305) (by norm_num)
theorem B1160837 : Blo 770335 1160837 := bbase (se 4 (by rfl) ⟨108828, by rfl⟩ : syracuseStep 1160837 = 217657) (by norm_num)
theorem B1160861 : Blo 770335 1160861 := bbase (se 3 (by rfl) ⟨217661, by rfl⟩ : syracuseStep 1160861 = 435323) (by norm_num)
theorem B1160885 : Blo 770335 1160885 := bbase (se 5 (by rfl) ⟨54416, by rfl⟩ : syracuseStep 1160885 = 108833) (by norm_num)
theorem B1160909 : Blo 770335 1160909 := bbase (se 3 (by rfl) ⟨217670, by rfl⟩ : syracuseStep 1160909 = 435341) (by norm_num)
theorem B1160933 : Blo 770335 1160933 := bbase (se 4 (by rfl) ⟨108837, by rfl⟩ : syracuseStep 1160933 = 217675) (by norm_num)
theorem B1160957 : Blo 770335 1160957 := bbase (se 3 (by rfl) ⟨217679, by rfl⟩ : syracuseStep 1160957 = 435359) (by norm_num)
theorem B2897669 : Blo 770335 2897669 := bbase (se 4 (by rfl) ⟨271656, by rfl⟩ : syracuseStep 2897669 = 543313) (by norm_num)
theorem B1652501 : Blo 770335 1652501 := bbase (se 6 (by rfl) ⟨38730, by rfl⟩ : syracuseStep 1652501 = 77461) (by norm_num)
theorem B1160981 : Blo 770335 1160981 := bbase (se 6 (by rfl) ⟨27210, by rfl⟩ : syracuseStep 1160981 = 54421) (by norm_num)
theorem B1161005 : Blo 770335 1161005 := bbase (se 3 (by rfl) ⟨217688, by rfl⟩ : syracuseStep 1161005 = 435377) (by norm_num)
theorem B1488701 : Blo 770335 1488701 := bbase (se 3 (by rfl) ⟨279131, by rfl⟩ : syracuseStep 1488701 = 558263) (by norm_num)
theorem B1161029 : Blo 770335 1161029 := bbase (se 4 (by rfl) ⟨108846, by rfl⟩ : syracuseStep 1161029 = 217693) (by norm_num)
theorem B1161053 : Blo 770335 1161053 := bbase (se 3 (by rfl) ⟨217697, by rfl⟩ : syracuseStep 1161053 = 435395) (by norm_num)
theorem B2602853 : Blo 770335 2602853 := bbase (se 4 (by rfl) ⟨244017, by rfl⟩ : syracuseStep 2602853 = 488035) (by norm_num)
theorem B1161077 : Blo 770335 1161077 := bbase (se 5 (by rfl) ⟨54425, by rfl⟩ : syracuseStep 1161077 = 108851) (by norm_num)
theorem B1161101 : Blo 770335 1161101 := bbase (se 3 (by rfl) ⟨217706, by rfl⟩ : syracuseStep 1161101 = 435413) (by norm_num)
theorem B1161125 : Blo 770335 1161125 := bbase (se 4 (by rfl) ⟨108855, by rfl⟩ : syracuseStep 1161125 = 217711) (by norm_num)
theorem B1161149 : Blo 770335 1161149 := bbase (se 3 (by rfl) ⟨217715, by rfl⟩ : syracuseStep 1161149 = 435431) (by norm_num)
theorem B1161173 : Blo 770335 1161173 := bbase (se 7 (by rfl) ⟨13607, by rfl⟩ : syracuseStep 1161173 = 27215) (by norm_num)
theorem B1161197 : Blo 770335 1161197 := bbase (se 3 (by rfl) ⟨217724, by rfl⟩ : syracuseStep 1161197 = 435449) (by norm_num)
theorem B1161221 : Blo 770335 1161221 := bbase (se 4 (by rfl) ⟨108864, by rfl⟩ : syracuseStep 1161221 = 217729) (by norm_num)
theorem B1161245 : Blo 770335 1161245 := bbase (se 3 (by rfl) ⟨217733, by rfl⟩ : syracuseStep 1161245 = 435467) (by norm_num)
theorem B1161269 : Blo 770335 1161269 := bbase (se 5 (by rfl) ⟨54434, by rfl⟩ : syracuseStep 1161269 = 108869) (by norm_num)
theorem B1161293 : Blo 770335 1161293 := bbase (se 3 (by rfl) ⟨217742, by rfl⟩ : syracuseStep 1161293 = 435485) (by norm_num)
theorem B1161317 : Blo 770335 1161317 := bbase (se 4 (by rfl) ⟨108873, by rfl⟩ : syracuseStep 1161317 = 217747) (by norm_num)
theorem B1161341 : Blo 770335 1161341 := bbase (se 3 (by rfl) ⟨217751, by rfl⟩ : syracuseStep 1161341 = 435503) (by norm_num)
theorem B1161365 : Blo 770335 1161365 := bbase (se 6 (by rfl) ⟨27219, by rfl⟩ : syracuseStep 1161365 = 54439) (by norm_num)
theorem B1161389 : Blo 770335 1161389 := bbase (se 3 (by rfl) ⟨217760, by rfl⟩ : syracuseStep 1161389 = 435521) (by norm_num)
theorem B1161413 : Blo 770335 1161413 := bbase (se 4 (by rfl) ⟨108882, by rfl⟩ : syracuseStep 1161413 = 217765) (by norm_num)
theorem B1161437 : Blo 770335 1161437 := bbase (se 3 (by rfl) ⟨217769, by rfl⟩ : syracuseStep 1161437 = 435539) (by norm_num)
theorem B1161461 : Blo 770335 1161461 := bbase (se 5 (by rfl) ⟨54443, by rfl⟩ : syracuseStep 1161461 = 108887) (by norm_num)
theorem B1390853 : Blo 770335 1390853 := bbase (se 4 (by rfl) ⟨130392, by rfl⟩ : syracuseStep 1390853 = 260785) (by norm_num)
theorem B1161485 : Blo 770335 1161485 := bbase (se 3 (by rfl) ⟨217778, by rfl⟩ : syracuseStep 1161485 = 435557) (by norm_num)
theorem B2603285 : Blo 770335 2603285 := bbase (se 6 (by rfl) ⟨61014, by rfl⟩ : syracuseStep 2603285 = 122029) (by norm_num)
theorem B866641 : Blo 770335 866641 := bbase (se 2 (by rfl) ⟨324990, by rfl⟩ : syracuseStep 866641 = 649981) (by norm_num)
theorem B866677 : Blo 770335 866677 := bbase (se 5 (by rfl) ⟨40625, by rfl⟩ : syracuseStep 866677 = 81251) (by norm_num)
theorem B866713 : Blo 770335 866713 := bbase (se 2 (by rfl) ⟨325017, by rfl⟩ : syracuseStep 866713 = 650035) (by norm_num)
theorem B866749 : Blo 770335 866749 := bbase (se 3 (by rfl) ⟨162515, by rfl⟩ : syracuseStep 866749 = 325031) (by norm_num)
theorem B866785 : Blo 770335 866785 := bbase (se 2 (by rfl) ⟨325044, by rfl⟩ : syracuseStep 866785 = 650089) (by norm_num)
theorem B2931173 : Blo 770335 2931173 := bbase (se 4 (by rfl) ⟨274797, by rfl⟩ : syracuseStep 2931173 = 549595) (by norm_num)
theorem B866821 : Blo 770335 866821 := bbase (se 4 (by rfl) ⟨81264, by rfl⟩ : syracuseStep 866821 = 162529) (by norm_num)
theorem B866857 : Blo 770335 866857 := bbase (se 2 (by rfl) ⟨325071, by rfl⟩ : syracuseStep 866857 = 650143) (by norm_num)
theorem B866893 : Blo 770335 866893 := bbase (se 3 (by rfl) ⟨162542, by rfl⟩ : syracuseStep 866893 = 325085) (by norm_num)
theorem B866929 : Blo 770335 866929 := bbase (se 2 (by rfl) ⟨325098, by rfl⟩ : syracuseStep 866929 = 650197) (by norm_num)
theorem B1653365 : Blo 770335 1653365 := bbase (se 5 (by rfl) ⟨77501, by rfl⟩ : syracuseStep 1653365 = 155003) (by norm_num)
theorem B866965 : Blo 770335 866965 := bbase (se 6 (by rfl) ⟨20319, by rfl⟩ : syracuseStep 866965 = 40639) (by norm_num)
theorem B3914405 : Blo 770335 3914405 := bbase (se 4 (by rfl) ⟨366975, by rfl⟩ : syracuseStep 3914405 = 733951) (by norm_num)
theorem B867001 : Blo 770335 867001 := bbase (se 2 (by rfl) ⟨325125, by rfl⟩ : syracuseStep 867001 = 650251) (by norm_num)
theorem B2603717 : Blo 770335 2603717 := bbase (se 4 (by rfl) ⟨244098, by rfl⟩ : syracuseStep 2603717 = 488197) (by norm_num)
theorem B867037 : Blo 770335 867037 := bbase (se 3 (by rfl) ⟨162569, by rfl⟩ : syracuseStep 867037 = 325139) (by norm_num)
theorem B867073 : Blo 770335 867073 := bbase (se 2 (by rfl) ⟨325152, by rfl⟩ : syracuseStep 867073 = 650305) (by norm_num)
theorem B2931461 : Blo 770335 2931461 := bbase (se 4 (by rfl) ⟨274824, by rfl⟩ : syracuseStep 2931461 = 549649) (by norm_num)
theorem B1653509 : Blo 770335 1653509 := bbase (se 4 (by rfl) ⟨155016, by rfl⟩ : syracuseStep 1653509 = 310033) (by norm_num)
theorem B867109 : Blo 770335 867109 := bbase (se 4 (by rfl) ⟨81291, by rfl⟩ : syracuseStep 867109 = 162583) (by norm_num)
theorem B867145 : Blo 770335 867145 := bbase (se 2 (by rfl) ⟨325179, by rfl⟩ : syracuseStep 867145 = 650359) (by norm_num)
theorem B867181 : Blo 770335 867181 := bbase (se 3 (by rfl) ⟨162596, by rfl⟩ : syracuseStep 867181 = 325193) (by norm_num)
theorem B867217 : Blo 770335 867217 := bbase (se 2 (by rfl) ⟨325206, by rfl⟩ : syracuseStep 867217 = 650413) (by norm_num)
theorem B1391509 : Blo 770335 1391509 := bbase (se 6 (by rfl) ⟨32613, by rfl⟩ : syracuseStep 1391509 = 65227) (by norm_num)
theorem B867253 : Blo 770335 867253 := bbase (se 5 (by rfl) ⟨40652, by rfl⟩ : syracuseStep 867253 = 81305) (by norm_num)
theorem B1391573 : Blo 770335 1391573 := bbase (se 7 (by rfl) ⟨16307, by rfl⟩ : syracuseStep 1391573 = 32615) (by norm_num)
theorem B867289 : Blo 770335 867289 := bbase (se 2 (by rfl) ⟨325233, by rfl⟩ : syracuseStep 867289 = 650467) (by norm_num)
theorem B867325 : Blo 770335 867325 := bbase (se 3 (by rfl) ⟨162623, by rfl⟩ : syracuseStep 867325 = 325247) (by norm_num)
theorem B867361 : Blo 770335 867361 := bbase (se 2 (by rfl) ⟨325260, by rfl⟩ : syracuseStep 867361 = 650521) (by norm_num)
theorem B867397 : Blo 770335 867397 := bbase (se 4 (by rfl) ⟨81318, by rfl⟩ : syracuseStep 867397 = 162637) (by norm_num)
theorem B867433 : Blo 770335 867433 := bbase (se 2 (by rfl) ⟨325287, by rfl⟩ : syracuseStep 867433 = 650575) (by norm_num)
theorem B2604149 : Blo 770335 2604149 := bbase (se 5 (by rfl) ⟨122069, by rfl⟩ : syracuseStep 2604149 = 244139) (by norm_num)
theorem B867469 : Blo 770335 867469 := bbase (se 3 (by rfl) ⟨162650, by rfl⟩ : syracuseStep 867469 = 325301) (by norm_num)
theorem B3292325 : Blo 770335 3292325 := bbase (se 4 (by rfl) ⟨308655, by rfl⟩ : syracuseStep 3292325 = 617311) (by norm_num)
theorem B867505 : Blo 770335 867505 := bbase (se 2 (by rfl) ⟨325314, by rfl⟩ : syracuseStep 867505 = 650629) (by norm_num)
theorem B867541 : Blo 770335 867541 := bbase (se 7 (by rfl) ⟨10166, by rfl⟩ : syracuseStep 867541 = 20333) (by norm_num)
theorem B867577 : Blo 770335 867577 := bbase (se 2 (by rfl) ⟨325341, by rfl⟩ : syracuseStep 867577 = 650683) (by norm_num)
theorem B867613 : Blo 770335 867613 := bbase (se 3 (by rfl) ⟨162677, by rfl⟩ : syracuseStep 867613 = 325355) (by norm_num)
theorem B867649 : Blo 770335 867649 := bbase (se 2 (by rfl) ⟨325368, by rfl⟩ : syracuseStep 867649 = 650737) (by norm_num)
theorem B11124053 : Blo 770335 11124053 := bbase (se 11 (by rfl) ⟨8147, by rfl⟩ : syracuseStep 11124053 = 16295) (by norm_num)
theorem B867685 : Blo 770335 867685 := bbase (se 4 (by rfl) ⟨81345, by rfl⟩ : syracuseStep 867685 = 162691) (by norm_num)
theorem B1097077 : Blo 770335 1097077 := bbase (se 5 (by rfl) ⟨51425, by rfl⟩ : syracuseStep 1097077 = 102851) (by norm_num)
theorem B867721 : Blo 770335 867721 := bbase (se 2 (by rfl) ⟨325395, by rfl⟩ : syracuseStep 867721 = 650791) (by norm_num)
theorem B867757 : Blo 770335 867757 := bbase (se 3 (by rfl) ⟨162704, by rfl⟩ : syracuseStep 867757 = 325409) (by norm_num)
theorem B867793 : Blo 770335 867793 := bbase (se 2 (by rfl) ⟨325422, by rfl⟩ : syracuseStep 867793 = 650845) (by norm_num)
theorem B867829 : Blo 770335 867829 := bbase (se 5 (by rfl) ⟨40679, by rfl⟩ : syracuseStep 867829 = 81359) (by norm_num)
theorem B2637317 : Blo 770335 2637317 := bbase (se 4 (by rfl) ⟨247248, by rfl⟩ : syracuseStep 2637317 = 494497) (by norm_num)
theorem B867865 : Blo 770335 867865 := bbase (se 2 (by rfl) ⟨325449, by rfl⟩ : syracuseStep 867865 = 650899) (by norm_num)
theorem B2604581 : Blo 770335 2604581 := bbase (se 4 (by rfl) ⟨244179, by rfl⟩ : syracuseStep 2604581 = 488359) (by norm_num)
theorem B867901 : Blo 770335 867901 := bbase (se 3 (by rfl) ⟨162731, by rfl⟩ : syracuseStep 867901 = 325463) (by norm_num)
theorem B867937 : Blo 770335 867937 := bbase (se 2 (by rfl) ⟨325476, by rfl⟩ : syracuseStep 867937 = 650953) (by norm_num)
theorem B867973 : Blo 770335 867973 := bbase (se 4 (by rfl) ⟨81372, by rfl⟩ : syracuseStep 867973 = 162745) (by norm_num)
theorem B868009 : Blo 770335 868009 := bbase (se 2 (by rfl) ⟨325503, by rfl⟩ : syracuseStep 868009 = 651007) (by norm_num)
theorem B868045 : Blo 770335 868045 := bbase (se 3 (by rfl) ⟨162758, by rfl⟩ : syracuseStep 868045 = 325517) (by norm_num)
theorem B868081 : Blo 770335 868081 := bbase (se 2 (by rfl) ⟨325530, by rfl⟩ : syracuseStep 868081 = 651061) (by norm_num)
theorem B868117 : Blo 770335 868117 := bbase (se 6 (by rfl) ⟨20346, by rfl⟩ : syracuseStep 868117 = 40693) (by norm_num)
theorem B868153 : Blo 770335 868153 := bbase (se 2 (by rfl) ⟨325557, by rfl⟩ : syracuseStep 868153 = 651115) (by norm_num)
theorem B868189 : Blo 770335 868189 := bbase (se 3 (by rfl) ⟨162785, by rfl⟩ : syracuseStep 868189 = 325571) (by norm_num)
theorem B868225 : Blo 770335 868225 := bbase (se 2 (by rfl) ⟨325584, by rfl⟩ : syracuseStep 868225 = 651169) (by norm_num)
theorem B868261 : Blo 770335 868261 := bbase (se 4 (by rfl) ⟨81399, by rfl⟩ : syracuseStep 868261 = 162799) (by norm_num)
theorem B2932645 : Blo 770335 2932645 := bbase (se 4 (by rfl) ⟨274935, by rfl⟩ : syracuseStep 2932645 = 549871) (by norm_num)
theorem B3915701 : Blo 770335 3915701 := bbase (se 5 (by rfl) ⟨183548, by rfl⟩ : syracuseStep 3915701 = 367097) (by norm_num)
theorem B1097669 : Blo 770335 1097669 := bbase (se 4 (by rfl) ⟨102906, by rfl⟩ : syracuseStep 1097669 = 205813) (by norm_num)
theorem B868297 : Blo 770335 868297 := bbase (se 2 (by rfl) ⟨325611, by rfl⟩ : syracuseStep 868297 = 651223) (by norm_num)
theorem B2605013 : Blo 770335 2605013 := bbase (se 7 (by rfl) ⟨30527, by rfl⟩ : syracuseStep 2605013 = 61055) (by norm_num)
theorem B868333 : Blo 770335 868333 := bbase (se 3 (by rfl) ⟨162812, by rfl⟩ : syracuseStep 868333 = 325625) (by norm_num)
theorem B868369 : Blo 770335 868369 := bbase (se 2 (by rfl) ⟨325638, by rfl⟩ : syracuseStep 868369 = 651277) (by norm_num)
theorem B1097749 : Blo 770335 1097749 := bbase (se 6 (by rfl) ⟨25728, by rfl⟩ : syracuseStep 1097749 = 51457) (by norm_num)
theorem B868405 : Blo 770335 868405 := bbase (se 5 (by rfl) ⟨40706, by rfl⟩ : syracuseStep 868405 = 81413) (by norm_num)
theorem B868441 : Blo 770335 868441 := bbase (se 2 (by rfl) ⟨325665, by rfl⟩ : syracuseStep 868441 = 651331) (by norm_num)
theorem B868477 : Blo 770335 868477 := bbase (se 3 (by rfl) ⟨162839, by rfl⟩ : syracuseStep 868477 = 325679) (by norm_num)
theorem B1097869 : Blo 770335 1097869 := bbase (se 3 (by rfl) ⟨205850, by rfl⟩ : syracuseStep 1097869 = 411701) (by norm_num)
theorem B868513 : Blo 770335 868513 := bbase (se 2 (by rfl) ⟨325692, by rfl⟩ : syracuseStep 868513 = 651385) (by norm_num)
theorem B2474165 : Blo 770335 2474165 := bbase (se 5 (by rfl) ⟨115976, by rfl⟩ : syracuseStep 2474165 = 231953) (by norm_num)
theorem B868549 : Blo 770335 868549 := bbase (se 4 (by rfl) ⟨81426, by rfl⟩ : syracuseStep 868549 = 162853) (by norm_num)
theorem B2932949 : Blo 770335 2932949 := bbase (se 7 (by rfl) ⟨34370, by rfl⟩ : syracuseStep 2932949 = 68741) (by norm_num)
theorem B868585 : Blo 770335 868585 := bbase (se 2 (by rfl) ⟨325719, by rfl⟩ : syracuseStep 868585 = 651439) (by norm_num)
theorem B1949933 : Blo 770335 1949933 := bbase (se 3 (by rfl) ⟨365612, by rfl⟩ : syracuseStep 1949933 = 731225) (by norm_num)
theorem B1097965 : Blo 770335 1097965 := bbase (se 3 (by rfl) ⟨205868, by rfl⟩ : syracuseStep 1097965 = 411737) (by norm_num)
theorem B868621 : Blo 770335 868621 := bbase (se 3 (by rfl) ⟨162866, by rfl⟩ : syracuseStep 868621 = 325733) (by norm_num)
theorem B868657 : Blo 770335 868657 := bbase (se 2 (by rfl) ⟨325746, by rfl⟩ : syracuseStep 868657 = 651493) (by norm_num)
theorem B868693 : Blo 770335 868693 := bbase (se 10 (by rfl) ⟨1272, by rfl⟩ : syracuseStep 868693 = 2545) (by norm_num)
theorem B868729 : Blo 770335 868729 := bbase (se 2 (by rfl) ⟨325773, by rfl⟩ : syracuseStep 868729 = 651547) (by norm_num)
theorem B2605445 : Blo 770335 2605445 := bbase (se 4 (by rfl) ⟨244260, by rfl⟩ : syracuseStep 2605445 = 488521) (by norm_num)
theorem B868765 : Blo 770335 868765 := bbase (se 3 (by rfl) ⟨162893, by rfl⟩ : syracuseStep 868765 = 325787) (by norm_num)
theorem B868801 : Blo 770335 868801 := bbase (se 2 (by rfl) ⟨325800, by rfl⟩ : syracuseStep 868801 = 651601) (by norm_num)
theorem B868837 : Blo 770335 868837 := bbase (se 4 (by rfl) ⟨81453, by rfl⟩ : syracuseStep 868837 = 162907) (by norm_num)
theorem B868873 : Blo 770335 868873 := bbase (se 2 (by rfl) ⟨325827, by rfl⟩ : syracuseStep 868873 = 651655) (by norm_num)
theorem B7225877 : Blo 770335 7225877 := bbase (se 6 (by rfl) ⟨169356, by rfl⟩ : syracuseStep 7225877 = 338713) (by norm_num)
theorem B868909 : Blo 770335 868909 := bbase (se 3 (by rfl) ⟨162920, by rfl⟩ : syracuseStep 868909 = 325841) (by norm_num)
theorem B1950277 : Blo 770335 1950277 := bbase (se 4 (by rfl) ⟨182838, by rfl⟩ : syracuseStep 1950277 = 365677) (by norm_num)
theorem B868945 : Blo 770335 868945 := bbase (se 2 (by rfl) ⟨325854, by rfl⟩ : syracuseStep 868945 = 651709) (by norm_num)
theorem B868981 : Blo 770335 868981 := bbase (se 5 (by rfl) ⟨40733, by rfl⟩ : syracuseStep 868981 = 81467) (by norm_num)
theorem B869017 : Blo 770335 869017 := bbase (se 2 (by rfl) ⟨325881, by rfl⟩ : syracuseStep 869017 = 651763) (by norm_num)
theorem B1950389 : Blo 770335 1950389 := bbase (se 5 (by rfl) ⟨91424, by rfl⟩ : syracuseStep 1950389 = 182849) (by norm_num)
theorem B869053 : Blo 770335 869053 := bbase (se 3 (by rfl) ⟨162947, by rfl⟩ : syracuseStep 869053 = 325895) (by norm_num)
theorem B1098461 : Blo 770335 1098461 := bbase (se 3 (by rfl) ⟨205961, by rfl⟩ : syracuseStep 1098461 = 411923) (by norm_num)
theorem B869089 : Blo 770335 869089 := bbase (se 2 (by rfl) ⟨325908, by rfl⟩ : syracuseStep 869089 = 651817) (by norm_num)
theorem B869125 : Blo 770335 869125 := bbase (se 4 (by rfl) ⟨81480, by rfl⟩ : syracuseStep 869125 = 162961) (by norm_num)
theorem B869161 : Blo 770335 869161 := bbase (se 2 (by rfl) ⟨325935, by rfl⟩ : syracuseStep 869161 = 651871) (by norm_num)
theorem B2605877 : Blo 770335 2605877 := bbase (se 5 (by rfl) ⟨122150, by rfl⟩ : syracuseStep 2605877 = 244301) (by norm_num)
theorem B869197 : Blo 770335 869197 := bbase (se 3 (by rfl) ⟨162974, by rfl⟩ : syracuseStep 869197 = 325949) (by norm_num)
theorem B20071253 : Blo 770335 20071253 := bbase (se 9 (by rfl) ⟨58802, by rfl⟩ : syracuseStep 20071253 = 117605) (by norm_num)
theorem B869233 : Blo 770335 869233 := bbase (se 2 (by rfl) ⟨325962, by rfl⟩ : syracuseStep 869233 = 651925) (by norm_num)
theorem B1950581 : Blo 770335 1950581 := bbase (se 5 (by rfl) ⟨91433, by rfl⟩ : syracuseStep 1950581 = 182867) (by norm_num)
theorem B3294101 : Blo 770335 3294101 := bbase (se 6 (by rfl) ⟨77205, by rfl⟩ : syracuseStep 3294101 = 154411) (by norm_num)
theorem B869269 : Blo 770335 869269 := bbase (se 6 (by rfl) ⟨20373, by rfl⟩ : syracuseStep 869269 = 40747) (by norm_num)
theorem B869305 : Blo 770335 869305 := bbase (se 2 (by rfl) ⟨325989, by rfl⟩ : syracuseStep 869305 = 651979) (by norm_num)
theorem B869341 : Blo 770335 869341 := bbase (se 3 (by rfl) ⟨163001, by rfl⟩ : syracuseStep 869341 = 326003) (by norm_num)
theorem B869377 : Blo 770335 869377 := bbase (se 2 (by rfl) ⟨326016, by rfl⟩ : syracuseStep 869377 = 652033) (by norm_num)
theorem B869413 : Blo 770335 869413 := bbase (se 4 (by rfl) ⟨81507, by rfl⟩ : syracuseStep 869413 = 163015) (by norm_num)
theorem B869449 : Blo 770335 869449 := bbase (se 2 (by rfl) ⟨326043, by rfl⟩ : syracuseStep 869449 = 652087) (by norm_num)
theorem B869485 : Blo 770335 869485 := bbase (se 3 (by rfl) ⟨163028, by rfl⟩ : syracuseStep 869485 = 326057) (by norm_num)
theorem B3294341 : Blo 770335 3294341 := bbase (se 4 (by rfl) ⟨308844, by rfl⟩ : syracuseStep 3294341 = 617689) (by norm_num)
theorem B869521 : Blo 770335 869521 := bbase (se 2 (by rfl) ⟨326070, by rfl⟩ : syracuseStep 869521 = 652141) (by norm_num)
theorem B869557 : Blo 770335 869557 := bbase (se 5 (by rfl) ⟨40760, by rfl⟩ : syracuseStep 869557 = 81521) (by norm_num)
theorem B3916997 : Blo 770335 3916997 := bbase (se 4 (by rfl) ⟨367218, by rfl⟩ : syracuseStep 3916997 = 734437) (by norm_num)
theorem B1950925 : Blo 770335 1950925 := bbase (se 3 (by rfl) ⟨365798, by rfl⟩ : syracuseStep 1950925 = 731597) (by norm_num)
theorem B869593 : Blo 770335 869593 := bbase (se 2 (by rfl) ⟨326097, by rfl⟩ : syracuseStep 869593 = 652195) (by norm_num)
theorem B2606309 : Blo 770335 2606309 := bbase (se 4 (by rfl) ⟨244341, by rfl⟩ : syracuseStep 2606309 = 488683) (by norm_num)
theorem B1885421 : Blo 770335 1885421 := bbase (se 3 (by rfl) ⟨353516, by rfl⟩ : syracuseStep 1885421 = 707033) (by norm_num)
theorem B1983733 : Blo 770335 1983733 := bbase (se 5 (by rfl) ⟨92987, by rfl⟩ : syracuseStep 1983733 = 185975) (by norm_num)
theorem B3720437 : Blo 770335 3720437 := bbase (se 5 (by rfl) ⟨174395, by rfl⟩ : syracuseStep 3720437 = 348791) (by norm_num)
theorem B869629 : Blo 770335 869629 := bbase (se 3 (by rfl) ⟨163055, by rfl⟩ : syracuseStep 869629 = 326111) (by norm_num)
theorem B1099013 : Blo 770335 1099013 := bbase (se 4 (by rfl) ⟨103032, by rfl⟩ : syracuseStep 1099013 = 206065) (by norm_num)
theorem B869665 : Blo 770335 869665 := bbase (se 2 (by rfl) ⟨326124, by rfl⟩ : syracuseStep 869665 = 652249) (by norm_num)
theorem B1951037 : Blo 770335 1951037 := bbase (se 3 (by rfl) ⟨365819, by rfl⟩ : syracuseStep 1951037 = 731639) (by norm_num)
theorem B869701 : Blo 770335 869701 := bbase (se 4 (by rfl) ⟨81534, by rfl⟩ : syracuseStep 869701 = 163069) (by norm_num)
theorem B869737 : Blo 770335 869737 := bbase (se 2 (by rfl) ⟨326151, by rfl⟩ : syracuseStep 869737 = 652303) (by norm_num)
theorem B869773 : Blo 770335 869773 := bbase (se 3 (by rfl) ⟨163082, by rfl⟩ : syracuseStep 869773 = 326165) (by norm_num)
theorem B869809 : Blo 770335 869809 := bbase (se 2 (by rfl) ⟨326178, by rfl⟩ : syracuseStep 869809 = 652357) (by norm_num)
theorem B1852885 : Blo 770335 1852885 := bbase (se 7 (by rfl) ⟨21713, by rfl⟩ : syracuseStep 1852885 = 43427) (by norm_num)
theorem B869845 : Blo 770335 869845 := bbase (se 7 (by rfl) ⟨10193, by rfl⟩ : syracuseStep 869845 = 20387) (by norm_num)
theorem B1983989 : Blo 770335 1983989 := bbase (se 5 (by rfl) ⟨92999, by rfl⟩ : syracuseStep 1983989 = 185999) (by norm_num)
theorem B869881 : Blo 770335 869881 := bbase (se 2 (by rfl) ⟨326205, by rfl⟩ : syracuseStep 869881 = 652411) (by norm_num)
theorem B1951229 : Blo 770335 1951229 := bbase (se 3 (by rfl) ⟨365855, by rfl⟩ : syracuseStep 1951229 = 731711) (by norm_num)
theorem B869917 : Blo 770335 869917 := bbase (se 3 (by rfl) ⟨163109, by rfl⟩ : syracuseStep 869917 = 326219) (by norm_num)
theorem B869953 : Blo 770335 869953 := bbase (se 2 (by rfl) ⟨326232, by rfl⟩ : syracuseStep 869953 = 652465) (by norm_num)
theorem B869989 : Blo 770335 869989 := bbase (se 4 (by rfl) ⟨81561, by rfl⟩ : syracuseStep 869989 = 163123) (by norm_num)
theorem B870025 : Blo 770335 870025 := bbase (se 2 (by rfl) ⟨326259, by rfl⟩ : syracuseStep 870025 = 652519) (by norm_num)
theorem B2606741 : Blo 770335 2606741 := bbase (se 6 (by rfl) ⟨61095, by rfl⟩ : syracuseStep 2606741 = 122191) (by norm_num)
theorem B870061 : Blo 770335 870061 := bbase (se 3 (by rfl) ⟨163136, by rfl⟩ : syracuseStep 870061 = 326273) (by norm_num)
theorem B870097 : Blo 770335 870097 := bbase (se 2 (by rfl) ⟨326286, by rfl⟩ : syracuseStep 870097 = 652573) (by norm_num)
theorem B4703957 : Blo 770335 4703957 := bbase (se 7 (by rfl) ⟨55124, by rfl⟩ : syracuseStep 4703957 = 110249) (by norm_num)
theorem B870133 : Blo 770335 870133 := bbase (se 5 (by rfl) ⟨40787, by rfl⟩ : syracuseStep 870133 = 81575) (by norm_num)
theorem B1132309 : Blo 770335 1132309 := bbase (se 6 (by rfl) ⟨26538, by rfl⟩ : syracuseStep 1132309 = 53077) (by norm_num)
theorem B870169 : Blo 770335 870169 := bbase (se 2 (by rfl) ⟨326313, by rfl⟩ : syracuseStep 870169 = 652627) (by norm_num)
theorem B1853221 : Blo 770335 1853221 := bbase (se 4 (by rfl) ⟨173739, by rfl⟩ : syracuseStep 1853221 = 347479) (by norm_num)
theorem B870205 : Blo 770335 870205 := bbase (se 3 (by rfl) ⟨163163, by rfl⟩ : syracuseStep 870205 = 326327) (by norm_num)
theorem B1951573 : Blo 770335 1951573 := bbase (se 9 (by rfl) ⟨5717, by rfl⟩ : syracuseStep 1951573 = 11435) (by norm_num)
theorem B870241 : Blo 770335 870241 := bbase (se 2 (by rfl) ⟨326340, by rfl⟩ : syracuseStep 870241 = 652681) (by norm_num)
theorem B870277 : Blo 770335 870277 := bbase (se 4 (by rfl) ⟨81588, by rfl⟩ : syracuseStep 870277 = 163177) (by norm_num)
theorem B870313 : Blo 770335 870313 := bbase (se 2 (by rfl) ⟨326367, by rfl⟩ : syracuseStep 870313 = 652735) (by norm_num)
theorem B1951685 : Blo 770335 1951685 := bbase (se 4 (by rfl) ⟨182970, by rfl⟩ : syracuseStep 1951685 = 365941) (by norm_num)
theorem B870349 : Blo 770335 870349 := bbase (se 3 (by rfl) ⟨163190, by rfl⟩ : syracuseStep 870349 = 326381) (by norm_num)
theorem B870385 : Blo 770335 870385 := bbase (se 2 (by rfl) ⟨326394, by rfl⟩ : syracuseStep 870385 = 652789) (by norm_num)
theorem B1099765 : Blo 770335 1099765 := bbase (se 5 (by rfl) ⟨51551, by rfl⟩ : syracuseStep 1099765 = 103103) (by norm_num)
theorem B2672645 : Blo 770335 2672645 := bbase (se 4 (by rfl) ⟨250560, by rfl⟩ : syracuseStep 2672645 = 501121) (by norm_num)
theorem B870421 : Blo 770335 870421 := bbase (se 6 (by rfl) ⟨20400, by rfl⟩ : syracuseStep 870421 = 40801) (by norm_num)
theorem B870457 : Blo 770335 870457 := bbase (se 2 (by rfl) ⟨326421, by rfl⟩ : syracuseStep 870457 = 652843) (by norm_num)
theorem B2607173 : Blo 770335 2607173 := bbase (se 4 (by rfl) ⟨244422, by rfl⟩ : syracuseStep 2607173 = 488845) (by norm_num)
theorem B870493 : Blo 770335 870493 := bbase (se 3 (by rfl) ⟨163217, by rfl⟩ : syracuseStep 870493 = 326435) (by norm_num)
theorem B870529 : Blo 770335 870529 := bbase (se 2 (by rfl) ⟨326448, by rfl⟩ : syracuseStep 870529 = 652897) (by norm_num)
theorem B1951877 : Blo 770335 1951877 := bbase (se 4 (by rfl) ⟨182988, by rfl⟩ : syracuseStep 1951877 = 365977) (by norm_num)
theorem B870565 : Blo 770335 870565 := bbase (se 4 (by rfl) ⟨81615, by rfl⟩ : syracuseStep 870565 = 163231) (by norm_num)
theorem B870601 : Blo 770335 870601 := bbase (se 2 (by rfl) ⟨326475, by rfl⟩ : syracuseStep 870601 = 652951) (by norm_num)
theorem B870637 : Blo 770335 870637 := bbase (se 3 (by rfl) ⟨163244, by rfl⟩ : syracuseStep 870637 = 326489) (by norm_num)
theorem B870673 : Blo 770335 870673 := bbase (se 2 (by rfl) ⟨326502, by rfl⟩ : syracuseStep 870673 = 653005) (by norm_num)
theorem B2935061 : Blo 770335 2935061 := bbase (se 6 (by rfl) ⟨68790, by rfl⟩ : syracuseStep 2935061 = 137581) (by norm_num)
theorem B870709 : Blo 770335 870709 := bbase (se 5 (by rfl) ⟨40814, by rfl⟩ : syracuseStep 870709 = 81629) (by norm_num)
theorem B870745 : Blo 770335 870745 := bbase (se 2 (by rfl) ⟨326529, by rfl⟩ : syracuseStep 870745 = 653059) (by norm_num)
theorem B870781 : Blo 770335 870781 := bbase (se 3 (by rfl) ⟨163271, by rfl⟩ : syracuseStep 870781 = 326543) (by norm_num)
theorem B1853837 : Blo 770335 1853837 := bbase (se 3 (by rfl) ⟨347594, by rfl⟩ : syracuseStep 1853837 = 695189) (by norm_num)
theorem B870817 : Blo 770335 870817 := bbase (se 2 (by rfl) ⟨326556, by rfl⟩ : syracuseStep 870817 = 653113) (by norm_num)
theorem B870853 : Blo 770335 870853 := bbase (se 4 (by rfl) ⟨81642, by rfl⟩ : syracuseStep 870853 = 163285) (by norm_num)
theorem B3918293 : Blo 770335 3918293 := bbase (se 7 (by rfl) ⟨45917, by rfl⟩ : syracuseStep 3918293 = 91835) (by norm_num)
theorem B1952221 : Blo 770335 1952221 := bbase (se 3 (by rfl) ⟨366041, by rfl⟩ : syracuseStep 1952221 = 732083) (by norm_num)
theorem B870889 : Blo 770335 870889 := bbase (se 2 (by rfl) ⟨326583, by rfl⟩ : syracuseStep 870889 = 653167) (by norm_num)
theorem B2607605 : Blo 770335 2607605 := bbase (se 5 (by rfl) ⟨122231, by rfl⟩ : syracuseStep 2607605 = 244463) (by norm_num)
theorem B870925 : Blo 770335 870925 := bbase (se 3 (by rfl) ⟨163298, by rfl⟩ : syracuseStep 870925 = 326597) (by norm_num)
theorem B870961 : Blo 770335 870961 := bbase (se 2 (by rfl) ⟨326610, by rfl⟩ : syracuseStep 870961 = 653221) (by norm_num)
theorem B2935349 : Blo 770335 2935349 := bbase (se 5 (by rfl) ⟨137594, by rfl⟩ : syracuseStep 2935349 = 275189) (by norm_num)
theorem B1952333 : Blo 770335 1952333 := bbase (se 3 (by rfl) ⟨366062, by rfl⟩ : syracuseStep 1952333 = 732125) (by norm_num)
theorem B870997 : Blo 770335 870997 := bbase (se 8 (by rfl) ⟨5103, by rfl⟩ : syracuseStep 870997 = 10207) (by norm_num)
theorem B871033 : Blo 770335 871033 := bbase (se 2 (by rfl) ⟨326637, by rfl⟩ : syracuseStep 871033 = 653275) (by norm_num)
theorem B871069 : Blo 770335 871069 := bbase (se 3 (by rfl) ⟨163325, by rfl⟩ : syracuseStep 871069 = 326651) (by norm_num)
theorem B871105 : Blo 770335 871105 := bbase (se 2 (by rfl) ⟨326664, by rfl⟩ : syracuseStep 871105 = 653329) (by norm_num)
theorem B1952525 : Blo 770335 1952525 := bbase (se 3 (by rfl) ⟨366098, by rfl⟩ : syracuseStep 1952525 = 732197) (by norm_num)
theorem B1100557 : Blo 770335 1100557 := bbase (se 3 (by rfl) ⟨206354, by rfl⟩ : syracuseStep 1100557 = 412709) (by norm_num)
theorem B5851925 : Blo 770335 5851925 := bbase (se 6 (by rfl) ⟨137154, by rfl⟩ : syracuseStep 5851925 = 274309) (by norm_num)
theorem B1854269 : Blo 770335 1854269 := bbase (se 3 (by rfl) ⟨347675, by rfl⟩ : syracuseStep 1854269 = 695351) (by norm_num)
theorem B2608037 : Blo 770335 2608037 := bbase (se 4 (by rfl) ⟨244503, by rfl⟩ : syracuseStep 2608037 = 489007) (by norm_num)
theorem B1985509 : Blo 770335 1985509 := bbase (se 4 (by rfl) ⟨186141, by rfl⟩ : syracuseStep 1985509 = 372283) (by norm_num)
theorem B1100893 : Blo 770335 1100893 := bbase (se 3 (by rfl) ⟨206417, by rfl⟩ : syracuseStep 1100893 = 412835) (by norm_num)
theorem B1952869 : Blo 770335 1952869 := bbase (se 4 (by rfl) ⟨183081, by rfl⟩ : syracuseStep 1952869 = 366163) (by norm_num)
theorem B3132533 : Blo 770335 3132533 := bbase (se 5 (by rfl) ⟨146837, by rfl⟩ : syracuseStep 3132533 = 293675) (by norm_num)
theorem B1952981 : Blo 770335 1952981 := bbase (se 7 (by rfl) ⟨22886, by rfl⟩ : syracuseStep 1952981 = 45773) (by norm_num)
theorem B2477317 : Blo 770335 2477317 := bbase (se 4 (by rfl) ⟨232248, by rfl⟩ : syracuseStep 2477317 = 464497) (by norm_num)
theorem B1101109 : Blo 770335 1101109 := bbase (se 5 (by rfl) ⟨51614, by rfl⟩ : syracuseStep 1101109 = 103229) (by norm_num)
theorem B2608469 : Blo 770335 2608469 := bbase (se 11 (by rfl) ⟨1910, by rfl⟩ : syracuseStep 2608469 = 3821) (by norm_num)
theorem B3296629 : Blo 770335 3296629 := bbase (se 5 (by rfl) ⟨154529, by rfl⟩ : syracuseStep 3296629 = 309059) (by norm_num)
theorem B1953173 : Blo 770335 1953173 := bbase (se 6 (by rfl) ⟨45777, by rfl⟩ : syracuseStep 1953173 = 91555) (by norm_num)
theorem B1854893 : Blo 770335 1854893 := bbase (se 3 (by rfl) ⟨347792, by rfl⟩ : syracuseStep 1854893 = 695585) (by norm_num)
theorem B1101485 : Blo 770335 1101485 := bbase (se 3 (by rfl) ⟨206528, by rfl⟩ : syracuseStep 1101485 = 413057) (by norm_num)
theorem B2936533 : Blo 770335 2936533 := bbase (se 7 (by rfl) ⟨34412, by rfl⟩ : syracuseStep 2936533 = 68825) (by norm_num)
theorem B3919589 : Blo 770335 3919589 := bbase (se 4 (by rfl) ⟨367461, by rfl⟩ : syracuseStep 3919589 = 734923) (by norm_num)
theorem B1953517 : Blo 770335 1953517 := bbase (se 3 (by rfl) ⟨366284, by rfl⟩ : syracuseStep 1953517 = 732569) (by norm_num)
theorem B2608901 : Blo 770335 2608901 := bbase (se 4 (by rfl) ⟨244584, by rfl⟩ : syracuseStep 2608901 = 489169) (by norm_num)
theorem B4181813 : Blo 770335 4181813 := bbase (se 5 (by rfl) ⟨196022, by rfl⟩ : syracuseStep 4181813 = 392045) (by norm_num)
theorem B1953629 : Blo 770335 1953629 := bbase (se 3 (by rfl) ⟨366305, by rfl⟩ : syracuseStep 1953629 = 732611) (by norm_num)
theorem B2936837 : Blo 770335 2936837 := bbase (se 4 (by rfl) ⟨275328, by rfl⟩ : syracuseStep 2936837 = 550657) (by norm_num)
theorem B1953821 : Blo 770335 1953821 := bbase (se 3 (by rfl) ⟨366341, by rfl⟩ : syracuseStep 1953821 = 732683) (by norm_num)
theorem B2609333 : Blo 770335 2609333 := bbase (se 5 (by rfl) ⟨122312, by rfl⟩ : syracuseStep 2609333 = 244625) (by norm_num)
theorem B1462549 : Blo 770335 1462549 := bbase (se 6 (by rfl) ⟨34278, by rfl⟩ : syracuseStep 1462549 = 68557) (by norm_num)
theorem B1954165 : Blo 770335 1954165 := bbase (se 5 (by rfl) ⟨91601, by rfl⟩ : syracuseStep 1954165 = 183203) (by norm_num)
theorem B1462693 : Blo 770335 1462693 := bbase (se 4 (by rfl) ⟨137127, by rfl⟩ : syracuseStep 1462693 = 274255) (by norm_num)
theorem B2347429 : Blo 770335 2347429 := bbase (se 4 (by rfl) ⟨220071, by rfl⟩ : syracuseStep 2347429 = 440143) (by norm_num)
theorem B938461 : Blo 770335 938461 := bbase (se 3 (by rfl) ⟨175961, by rfl⟩ : syracuseStep 938461 = 351923) (by norm_num)
theorem B1954277 : Blo 770335 1954277 := bbase (se 4 (by rfl) ⟨183213, by rfl⟩ : syracuseStep 1954277 = 366427) (by norm_num)
theorem B938537 : Blo 770335 938537 := bbase (se 2 (by rfl) ⟨351951, by rfl⟩ : syracuseStep 938537 = 703903) (by norm_num)
theorem B3527221 : Blo 770335 3527221 := bbase (se 5 (by rfl) ⟨165338, by rfl⟩ : syracuseStep 3527221 = 330677) (by norm_num)
theorem B1462853 : Blo 770335 1462853 := bbase (se 4 (by rfl) ⟨137142, by rfl⟩ : syracuseStep 1462853 = 274285) (by norm_num)
theorem B2642501 : Blo 770335 2642501 := bbase (se 4 (by rfl) ⟨247734, by rfl⟩ : syracuseStep 2642501 = 495469) (by norm_num)
theorem B2609765 : Blo 770335 2609765 := bbase (se 4 (by rfl) ⟨244665, by rfl⟩ : syracuseStep 2609765 = 489331) (by norm_num)
theorem B1954469 : Blo 770335 1954469 := bbase (se 4 (by rfl) ⟨183231, by rfl⟩ : syracuseStep 1954469 = 366463) (by norm_num)
theorem B938693 : Blo 770335 938693 := bbase (se 4 (by rfl) ⟨88002, by rfl⟩ : syracuseStep 938693 = 176005) (by norm_num)
theorem B1462997 : Blo 770335 1462997 := bbase (se 7 (by rfl) ⟨17144, by rfl⟩ : syracuseStep 1462997 = 34289) (by norm_num)
theorem B3298117 : Blo 770335 3298117 := bbase (se 4 (by rfl) ⟨309198, by rfl⟩ : syracuseStep 3298117 = 618397) (by norm_num)
theorem B3298133 : Blo 770335 3298133 := bbase (se 9 (by rfl) ⟨9662, by rfl⟩ : syracuseStep 3298133 = 19325) (by norm_num)
theorem B2118581 : Blo 770335 2118581 := bbase (se 5 (by rfl) ⟨99308, by rfl⟩ : syracuseStep 2118581 = 198617) (by norm_num)
theorem B1463285 : Blo 770335 1463285 := bbase (se 5 (by rfl) ⟨68591, by rfl⟩ : syracuseStep 1463285 = 137183) (by norm_num)
theorem B1954813 : Blo 770335 1954813 := bbase (se 3 (by rfl) ⟨366527, by rfl⟩ : syracuseStep 1954813 = 733055) (by norm_num)
theorem B2610197 : Blo 770335 2610197 := bbase (se 6 (by rfl) ⟨61176, by rfl⟩ : syracuseStep 2610197 = 122353) (by norm_num)
theorem B1954925 : Blo 770335 1954925 := bbase (se 3 (by rfl) ⟨366548, by rfl⟩ : syracuseStep 1954925 = 733097) (by norm_num)
theorem B1234045 : Blo 770335 1234045 := bbase (se 3 (by rfl) ⟨231383, by rfl⟩ : syracuseStep 1234045 = 462767) (by norm_num)
theorem B1463437 : Blo 770335 1463437 := bbase (se 3 (by rfl) ⟨274394, by rfl⟩ : syracuseStep 1463437 = 548789) (by norm_num)
theorem B1758437 : Blo 770335 1758437 := bbase (se 4 (by rfl) ⟨164853, by rfl⟩ : syracuseStep 1758437 = 329707) (by norm_num)
theorem B4936949 : Blo 770335 4936949 := bbase (se 5 (by rfl) ⟨231419, by rfl⟩ : syracuseStep 4936949 = 462839) (by norm_num)
theorem B1955117 : Blo 770335 1955117 := bbase (se 3 (by rfl) ⟨366584, by rfl⟩ : syracuseStep 1955117 = 733169) (by norm_num)
theorem B1463741 : Blo 770335 1463741 := bbase (se 3 (by rfl) ⟨274451, by rfl⟩ : syracuseStep 1463741 = 548903) (by norm_num)
theorem B2610629 : Blo 770335 2610629 := bbase (se 4 (by rfl) ⟨244746, by rfl⟩ : syracuseStep 2610629 = 489493) (by norm_num)
theorem B1299989 : Blo 770335 1299989 := bbase (se 6 (by rfl) ⟨30468, by rfl⟩ : syracuseStep 1299989 = 60937) (by norm_num)
theorem B1955461 : Blo 770335 1955461 := bbase (se 4 (by rfl) ⟨183324, by rfl⟩ : syracuseStep 1955461 = 366649) (by norm_num)
theorem B1300117 : Blo 770335 1300117 := bbase (se 6 (by rfl) ⟨30471, by rfl⟩ : syracuseStep 1300117 = 60943) (by norm_num)
theorem B939721 : Blo 770335 939721 := bbase (se 2 (by rfl) ⟨352395, by rfl⟩ : syracuseStep 939721 = 704791) (by norm_num)
theorem B1300205 : Blo 770335 1300205 := bbase (se 3 (by rfl) ⟨243788, by rfl⟩ : syracuseStep 1300205 = 487577) (by norm_num)
theorem B1955573 : Blo 770335 1955573 := bbase (se 5 (by rfl) ⟨91667, by rfl⟩ : syracuseStep 1955573 = 183335) (by norm_num)
theorem B1234693 : Blo 770335 1234693 := bbase (se 4 (by rfl) ⟨115752, by rfl⟩ : syracuseStep 1234693 = 231505) (by norm_num)
theorem B1300333 : Blo 770335 1300333 := bbase (se 3 (by rfl) ⟨243812, by rfl⟩ : syracuseStep 1300333 = 487625) (by norm_num)
theorem B2611061 : Blo 770335 2611061 := bbase (se 5 (by rfl) ⟨122393, by rfl⟩ : syracuseStep 2611061 = 244787) (by norm_num)
theorem B1955765 : Blo 770335 1955765 := bbase (se 5 (by rfl) ⟨91676, by rfl⟩ : syracuseStep 1955765 = 183353) (by norm_num)
theorem B1300421 : Blo 770335 1300421 := bbase (se 4 (by rfl) ⟨121914, by rfl⟩ : syracuseStep 1300421 = 243829) (by norm_num)
theorem B2480149 : Blo 770335 2480149 := bbase (se 6 (by rfl) ⟨58128, by rfl⟩ : syracuseStep 2480149 = 116257) (by norm_num)
theorem B1300549 : Blo 770335 1300549 := bbase (se 4 (by rfl) ⟨121926, by rfl⟩ : syracuseStep 1300549 = 243853) (by norm_num)
theorem B2938949 : Blo 770335 2938949 := bbase (se 4 (by rfl) ⟨275526, by rfl⟩ : syracuseStep 2938949 = 551053) (by norm_num)
theorem B2480213 : Blo 770335 2480213 := bbase (se 8 (by rfl) ⟨14532, by rfl⟩ : syracuseStep 2480213 = 29065) (by norm_num)
theorem B2349157 : Blo 770335 2349157 := bbase (se 4 (by rfl) ⟨220233, by rfl⟩ : syracuseStep 2349157 = 440467) (by norm_num)
theorem B1300637 : Blo 770335 1300637 := bbase (se 3 (by rfl) ⟨243869, by rfl⟩ : syracuseStep 1300637 = 487739) (by norm_num)
theorem B1464493 : Blo 770335 1464493 := bbase (se 3 (by rfl) ⟨274592, by rfl⟩ : syracuseStep 1464493 = 549185) (by norm_num)
theorem B2349253 : Blo 770335 2349253 := bbase (se 4 (by rfl) ⟨220242, by rfl⟩ : syracuseStep 2349253 = 440485) (by norm_num)
theorem B1956109 : Blo 770335 1956109 := bbase (se 3 (by rfl) ⟨366770, by rfl⟩ : syracuseStep 1956109 = 733541) (by norm_num)
theorem B1300765 : Blo 770335 1300765 := bbase (se 3 (by rfl) ⟨243893, by rfl⟩ : syracuseStep 1300765 = 487787) (by norm_num)
theorem B2611493 : Blo 770335 2611493 := bbase (se 4 (by rfl) ⟨244827, by rfl⟩ : syracuseStep 2611493 = 489655) (by norm_num)
theorem B1464637 : Blo 770335 1464637 := bbase (se 3 (by rfl) ⟨274619, by rfl⟩ : syracuseStep 1464637 = 549239) (by norm_num)
theorem B1857853 : Blo 770335 1857853 := bbase (se 3 (by rfl) ⟨348347, by rfl⟩ : syracuseStep 1857853 = 696695) (by norm_num)
theorem B2939237 : Blo 770335 2939237 := bbase (se 4 (by rfl) ⟨275553, by rfl⟩ : syracuseStep 2939237 = 551107) (by norm_num)
theorem B1300853 : Blo 770335 1300853 := bbase (se 5 (by rfl) ⟨60977, by rfl⟩ : syracuseStep 1300853 = 121955) (by norm_num)
theorem B1956221 : Blo 770335 1956221 := bbase (se 3 (by rfl) ⟨366791, by rfl⟩ : syracuseStep 1956221 = 733583) (by norm_num)
theorem B2087317 : Blo 770335 2087317 := bbase (se 6 (by rfl) ⟨48921, by rfl⟩ : syracuseStep 2087317 = 97843) (by norm_num)
theorem B5560757 : Blo 770335 5560757 := bbase (se 5 (by rfl) ⟨260660, by rfl⟩ : syracuseStep 5560757 = 521321) (by norm_num)
theorem B1464797 : Blo 770335 1464797 := bbase (se 3 (by rfl) ⟨274649, by rfl⟩ : syracuseStep 1464797 = 549299) (by norm_num)
theorem B1300981 : Blo 770335 1300981 := bbase (se 5 (by rfl) ⟨60983, by rfl⟩ : syracuseStep 1300981 = 121967) (by norm_num)
theorem B1858045 : Blo 770335 1858045 := bbase (se 3 (by rfl) ⟨348383, by rfl⟩ : syracuseStep 1858045 = 696767) (by norm_num)
theorem B1858085 : Blo 770335 1858085 := bbase (se 4 (by rfl) ⟨174195, by rfl⟩ : syracuseStep 1858085 = 348391) (by norm_num)
theorem B1956413 : Blo 770335 1956413 := bbase (se 3 (by rfl) ⟨366827, by rfl⟩ : syracuseStep 1956413 = 733655) (by norm_num)
theorem B1301069 : Blo 770335 1301069 := bbase (se 3 (by rfl) ⟨243950, by rfl⟩ : syracuseStep 1301069 = 487901) (by norm_num)
theorem B1464941 : Blo 770335 1464941 := bbase (se 3 (by rfl) ⟨274676, by rfl⟩ : syracuseStep 1464941 = 549353) (by norm_num)
theorem B3136133 : Blo 770335 3136133 := bbase (se 4 (by rfl) ⟨294012, by rfl⟩ : syracuseStep 3136133 = 588025) (by norm_num)
theorem B1235621 : Blo 770335 1235621 := bbase (se 4 (by rfl) ⟨115839, by rfl⟩ : syracuseStep 1235621 = 231679) (by norm_num)
theorem B2120357 : Blo 770335 2120357 := bbase (se 4 (by rfl) ⟨198783, by rfl⟩ : syracuseStep 2120357 = 397567) (by norm_num)
theorem B1301197 : Blo 770335 1301197 := bbase (se 3 (by rfl) ⟨243974, by rfl⟩ : syracuseStep 1301197 = 487949) (by norm_num)
theorem B2611925 : Blo 770335 2611925 := bbase (se 7 (by rfl) ⟨30608, by rfl⟩ : syracuseStep 2611925 = 61217) (by norm_num)
theorem B1301285 : Blo 770335 1301285 := bbase (se 4 (by rfl) ⟨121995, by rfl⟩ : syracuseStep 1301285 = 243991) (by norm_num)
theorem B1858373 : Blo 770335 1858373 := bbase (se 4 (by rfl) ⟨174222, by rfl⟩ : syracuseStep 1858373 = 348445) (by norm_num)
theorem B1563509 : Blo 770335 1563509 := bbase (se 5 (by rfl) ⟨73289, by rfl⟩ : syracuseStep 1563509 = 146579) (by norm_num)
theorem B1465229 : Blo 770335 1465229 := bbase (se 3 (by rfl) ⟨274730, by rfl⟩ : syracuseStep 1465229 = 549461) (by norm_num)
theorem B1956757 : Blo 770335 1956757 := bbase (se 6 (by rfl) ⟨45861, by rfl⟩ : syracuseStep 1956757 = 91723) (by norm_num)
theorem B1301413 : Blo 770335 1301413 := bbase (se 4 (by rfl) ⟨122007, by rfl⟩ : syracuseStep 1301413 = 244015) (by norm_num)
theorem B940997 : Blo 770335 940997 := bbase (se 4 (by rfl) ⟨88218, by rfl⟩ : syracuseStep 940997 = 176437) (by norm_num)
theorem B1301501 : Blo 770335 1301501 := bbase (se 3 (by rfl) ⟨244031, by rfl⟩ : syracuseStep 1301501 = 488063) (by norm_num)
theorem B1956869 : Blo 770335 1956869 := bbase (se 4 (by rfl) ⟨183456, by rfl⟩ : syracuseStep 1956869 = 366913) (by norm_num)
theorem B1465381 : Blo 770335 1465381 := bbase (se 4 (by rfl) ⟨137379, by rfl⟩ : syracuseStep 1465381 = 274759) (by norm_num)
theorem B3300389 : Blo 770335 3300389 := bbase (se 4 (by rfl) ⟨309411, by rfl⟩ : syracuseStep 3300389 = 618823) (by norm_num)
theorem B1236077 : Blo 770335 1236077 := bbase (se 3 (by rfl) ⟨231764, by rfl⟩ : syracuseStep 1236077 = 463529) (by norm_num)
theorem B1301629 : Blo 770335 1301629 := bbase (se 3 (by rfl) ⟨244055, by rfl⟩ : syracuseStep 1301629 = 488111) (by norm_num)
theorem B2612357 : Blo 770335 2612357 := bbase (se 4 (by rfl) ⟨244908, by rfl⟩ : syracuseStep 2612357 = 489817) (by norm_num)
theorem B1957061 : Blo 770335 1957061 := bbase (se 4 (by rfl) ⟨183474, by rfl⟩ : syracuseStep 1957061 = 366949) (by norm_num)
theorem B1301717 : Blo 770335 1301717 := bbase (se 7 (by rfl) ⟨15254, by rfl⟩ : syracuseStep 1301717 = 30509) (by norm_num)
theorem B1760501 : Blo 770335 1760501 := bbase (se 5 (by rfl) ⟨82523, by rfl⟩ : syracuseStep 1760501 = 165047) (by norm_num)
theorem B1301845 : Blo 770335 1301845 := bbase (se 11 (by rfl) ⟨953, by rfl⟩ : syracuseStep 1301845 = 1907) (by norm_num)
theorem B1465685 : Blo 770335 1465685 := bbase (se 11 (by rfl) ⟨1073, by rfl⟩ : syracuseStep 1465685 = 2147) (by norm_num)
theorem B1301933 : Blo 770335 1301933 := bbase (se 3 (by rfl) ⟨244112, by rfl⟩ : syracuseStep 1301933 = 488225) (by norm_num)
theorem B1957405 : Blo 770335 1957405 := bbase (se 3 (by rfl) ⟨367013, by rfl⟩ : syracuseStep 1957405 = 734027) (by norm_num)
theorem B1302061 : Blo 770335 1302061 := bbase (se 3 (by rfl) ⟨244136, by rfl⟩ : syracuseStep 1302061 = 488273) (by norm_num)
theorem B2612789 : Blo 770335 2612789 := bbase (se 5 (by rfl) ⟨122474, by rfl⟩ : syracuseStep 2612789 = 244949) (by norm_num)
theorem B1302149 : Blo 770335 1302149 := bbase (se 4 (by rfl) ⟨122076, by rfl⟩ : syracuseStep 1302149 = 244153) (by norm_num)
theorem B1957517 : Blo 770335 1957517 := bbase (se 3 (by rfl) ⟨367034, by rfl⟩ : syracuseStep 1957517 = 734069) (by norm_num)
theorem B2350741 : Blo 770335 2350741 := bbase (se 6 (by rfl) ⟨55095, by rfl⟩ : syracuseStep 2350741 = 110191) (by norm_num)
theorem B1302277 : Blo 770335 1302277 := bbase (se 4 (by rfl) ⟨122088, by rfl⟩ : syracuseStep 1302277 = 244177) (by norm_num)
theorem B1957709 : Blo 770335 1957709 := bbase (se 3 (by rfl) ⟨367070, by rfl⟩ : syracuseStep 1957709 = 734141) (by norm_num)
theorem B1302365 : Blo 770335 1302365 := bbase (se 3 (by rfl) ⟨244193, by rfl⟩ : syracuseStep 1302365 = 488387) (by norm_num)
theorem B2088821 : Blo 770335 2088821 := bbase (se 5 (by rfl) ⟨97913, by rfl⟩ : syracuseStep 2088821 = 195827) (by norm_num)
theorem B2088917 : Blo 770335 2088917 := bbase (se 7 (by rfl) ⟨24479, by rfl⟩ : syracuseStep 2088917 = 48959) (by norm_num)
theorem B1302493 : Blo 770335 1302493 := bbase (se 3 (by rfl) ⟨244217, by rfl⟩ : syracuseStep 1302493 = 488435) (by norm_num)
theorem B1564645 : Blo 770335 1564645 := bbase (se 4 (by rfl) ⟨146685, by rfl⟩ : syracuseStep 1564645 = 293371) (by norm_num)
theorem B2613221 : Blo 770335 2613221 := bbase (se 4 (by rfl) ⟨244989, by rfl⟩ : syracuseStep 2613221 = 489979) (by norm_num)
theorem B1302581 : Blo 770335 1302581 := bbase (se 5 (by rfl) ⟨61058, by rfl⟩ : syracuseStep 1302581 = 122117) (by norm_num)
theorem B1564741 : Blo 770335 1564741 := bbase (se 4 (by rfl) ⟨146694, by rfl⟩ : syracuseStep 1564741 = 293389) (by norm_num)
theorem B1466437 : Blo 770335 1466437 := bbase (se 4 (by rfl) ⟨137478, by rfl⟩ : syracuseStep 1466437 = 274957) (by norm_num)
theorem B1958053 : Blo 770335 1958053 := bbase (se 4 (by rfl) ⟨183567, by rfl⟩ : syracuseStep 1958053 = 367135) (by norm_num)
theorem B975017 : Blo 770335 975017 := bbase (se 2 (by rfl) ⟨365631, by rfl⟩ : syracuseStep 975017 = 731263) (by norm_num)
theorem B1302709 : Blo 770335 1302709 := bbase (se 5 (by rfl) ⟨61064, by rfl⟩ : syracuseStep 1302709 = 122129) (by norm_num)
theorem B1466581 : Blo 770335 1466581 := bbase (se 7 (by rfl) ⟨17186, by rfl⟩ : syracuseStep 1466581 = 34373) (by norm_num)
theorem B975073 : Blo 770335 975073 := bbase (se 2 (by rfl) ⟨365652, by rfl⟩ : syracuseStep 975073 = 731305) (by norm_num)
theorem B1302797 : Blo 770335 1302797 := bbase (se 3 (by rfl) ⟨244274, by rfl⟩ : syracuseStep 1302797 = 488549) (by norm_num)
theorem B1958165 : Blo 770335 1958165 := bbase (se 6 (by rfl) ⟨45894, by rfl⟩ : syracuseStep 1958165 = 91789) (by norm_num)
theorem B975169 : Blo 770335 975169 := bbase (se 2 (by rfl) ⟨365688, by rfl⟩ : syracuseStep 975169 = 731377) (by norm_num)
theorem B1466741 : Blo 770335 1466741 := bbase (se 5 (by rfl) ⟨68753, by rfl⟩ : syracuseStep 1466741 = 137507) (by norm_num)
theorem B1302925 : Blo 770335 1302925 := bbase (se 3 (by rfl) ⟨244298, by rfl⟩ : syracuseStep 1302925 = 488597) (by norm_num)
theorem B1958357 : Blo 770335 1958357 := bbase (se 7 (by rfl) ⟨22949, by rfl⟩ : syracuseStep 1958357 = 45899) (by norm_num)
theorem B1303013 : Blo 770335 1303013 := bbase (se 4 (by rfl) ⟨122157, by rfl⟩ : syracuseStep 1303013 = 244315) (by norm_num)
theorem B975341 : Blo 770335 975341 := bbase (se 3 (by rfl) ⟨182876, by rfl⟩ : syracuseStep 975341 = 365753) (by norm_num)
theorem B1237493 : Blo 770335 1237493 := bbase (se 5 (by rfl) ⟨58007, by rfl⟩ : syracuseStep 1237493 = 116015) (by norm_num)
theorem B1466885 : Blo 770335 1466885 := bbase (se 4 (by rfl) ⟨137520, by rfl⟩ : syracuseStep 1466885 = 275041) (by norm_num)
theorem B975397 : Blo 770335 975397 := bbase (se 4 (by rfl) ⟨91443, by rfl⟩ : syracuseStep 975397 = 182887) (by norm_num)
theorem B1303141 : Blo 770335 1303141 := bbase (se 4 (by rfl) ⟨122169, by rfl⟩ : syracuseStep 1303141 = 244339) (by norm_num)
theorem B975493 : Blo 770335 975493 := bbase (se 4 (by rfl) ⟨91452, by rfl⟩ : syracuseStep 975493 = 182905) (by norm_num)
theorem B1303229 : Blo 770335 1303229 := bbase (se 3 (by rfl) ⟨244355, by rfl⟩ : syracuseStep 1303229 = 488711) (by norm_num)
theorem B1237717 : Blo 770335 1237717 := bbase (se 7 (by rfl) ⟨14504, by rfl⟩ : syracuseStep 1237717 = 29009) (by norm_num)
theorem B1467173 : Blo 770335 1467173 := bbase (se 4 (by rfl) ⟨137547, by rfl⟩ : syracuseStep 1467173 = 275095) (by norm_num)
theorem B1958701 : Blo 770335 1958701 := bbase (se 3 (by rfl) ⟨367256, by rfl⟩ : syracuseStep 1958701 = 734513) (by norm_num)
theorem B975665 : Blo 770335 975665 := bbase (se 2 (by rfl) ⟨365874, by rfl⟩ : syracuseStep 975665 = 731749) (by norm_num)
theorem B2089781 : Blo 770335 2089781 := bbase (se 5 (by rfl) ⟨97958, by rfl⟩ : syracuseStep 2089781 = 195917) (by norm_num)
theorem B1303357 : Blo 770335 1303357 := bbase (se 3 (by rfl) ⟨244379, by rfl⟩ : syracuseStep 1303357 = 488759) (by norm_num)
theorem B975721 : Blo 770335 975721 := bbase (se 2 (by rfl) ⟨365895, by rfl⟩ : syracuseStep 975721 = 731791) (by norm_num)
theorem B1303445 : Blo 770335 1303445 := bbase (se 6 (by rfl) ⟨30549, by rfl⟩ : syracuseStep 1303445 = 61099) (by norm_num)
theorem B1958813 : Blo 770335 1958813 := bbase (se 3 (by rfl) ⟨367277, by rfl⟩ : syracuseStep 1958813 = 734555) (by norm_num)
theorem B1467325 : Blo 770335 1467325 := bbase (se 3 (by rfl) ⟨275123, by rfl⟩ : syracuseStep 1467325 = 550247) (by norm_num)
theorem B975817 : Blo 770335 975817 := bbase (se 2 (by rfl) ⟨365931, by rfl⟩ : syracuseStep 975817 = 731863) (by norm_num)
theorem B1172437 : Blo 770335 1172437 := bbase (se 7 (by rfl) ⟨13739, by rfl⟩ : syracuseStep 1172437 = 27479) (by norm_num)
theorem B1303573 : Blo 770335 1303573 := bbase (se 6 (by rfl) ⟨30552, by rfl⟩ : syracuseStep 1303573 = 61105) (by norm_num)
theorem B1959005 : Blo 770335 1959005 := bbase (se 3 (by rfl) ⟨367313, by rfl⟩ : syracuseStep 1959005 = 734627) (by norm_num)
theorem B1303661 : Blo 770335 1303661 := bbase (se 3 (by rfl) ⟨244436, by rfl⟩ : syracuseStep 1303661 = 488873) (by norm_num)
theorem B975989 : Blo 770335 975989 := bbase (se 5 (by rfl) ⟨45749, by rfl⟩ : syracuseStep 975989 = 91499) (by norm_num)
theorem B976045 : Blo 770335 976045 := bbase (se 3 (by rfl) ⟨183008, by rfl⟩ : syracuseStep 976045 = 366017) (by norm_num)
theorem B1303789 : Blo 770335 1303789 := bbase (se 3 (by rfl) ⟨244460, by rfl⟩ : syracuseStep 1303789 = 488921) (by norm_num)
theorem B1467629 : Blo 770335 1467629 := bbase (se 3 (by rfl) ⟨275180, by rfl⟩ : syracuseStep 1467629 = 550361) (by norm_num)
theorem B976141 : Blo 770335 976141 := bbase (se 3 (by rfl) ⟨183026, by rfl⟩ : syracuseStep 976141 = 366053) (by norm_num)
theorem B1303877 : Blo 770335 1303877 := bbase (se 4 (by rfl) ⟨122238, by rfl⟩ : syracuseStep 1303877 = 244477) (by norm_num)
theorem B2778533 : Blo 770335 2778533 := bbase (se 4 (by rfl) ⟨260487, by rfl⟩ : syracuseStep 2778533 = 520975) (by norm_num)
theorem B1959349 : Blo 770335 1959349 := bbase (se 5 (by rfl) ⟨91844, by rfl⟩ : syracuseStep 1959349 = 183689) (by norm_num)
theorem B976313 : Blo 770335 976313 := bbase (se 2 (by rfl) ⟨366117, by rfl⟩ : syracuseStep 976313 = 732235) (by norm_num)
theorem B1304005 : Blo 770335 1304005 := bbase (se 4 (by rfl) ⟨122250, by rfl⟩ : syracuseStep 1304005 = 244501) (by norm_num)
theorem B976369 : Blo 770335 976369 := bbase (se 2 (by rfl) ⟨366138, by rfl⟩ : syracuseStep 976369 = 732277) (by norm_num)
theorem B1304093 : Blo 770335 1304093 := bbase (se 3 (by rfl) ⟨244517, by rfl⟩ : syracuseStep 1304093 = 489035) (by norm_num)
theorem B1959461 : Blo 770335 1959461 := bbase (se 4 (by rfl) ⟨183699, by rfl⟩ : syracuseStep 1959461 = 367399) (by norm_num)
theorem B976465 : Blo 770335 976465 := bbase (se 2 (by rfl) ⟨366174, by rfl⟩ : syracuseStep 976465 = 732349) (by norm_num)
theorem B1304221 : Blo 770335 1304221 := bbase (se 3 (by rfl) ⟨244541, by rfl⟩ : syracuseStep 1304221 = 489083) (by norm_num)
theorem B1959653 : Blo 770335 1959653 := bbase (se 4 (by rfl) ⟨183717, by rfl⟩ : syracuseStep 1959653 = 367435) (by norm_num)
theorem B1304309 : Blo 770335 1304309 := bbase (se 5 (by rfl) ⟨61139, by rfl⟩ : syracuseStep 1304309 = 122279) (by norm_num)
theorem B976637 : Blo 770335 976637 := bbase (se 3 (by rfl) ⟨183119, by rfl⟩ : syracuseStep 976637 = 366239) (by norm_num)
theorem B976693 : Blo 770335 976693 := bbase (se 5 (by rfl) ⟨45782, by rfl⟩ : syracuseStep 976693 = 91565) (by norm_num)
theorem B1304437 : Blo 770335 1304437 := bbase (se 5 (by rfl) ⟨61145, by rfl⟩ : syracuseStep 1304437 = 122291) (by norm_num)
theorem B976789 : Blo 770335 976789 := bbase (se 6 (by rfl) ⟨22893, by rfl⟩ : syracuseStep 976789 = 45787) (by norm_num)
theorem B1304525 : Blo 770335 1304525 := bbase (se 3 (by rfl) ⟨244598, by rfl⟩ : syracuseStep 1304525 = 489197) (by norm_num)
theorem B1468381 : Blo 770335 1468381 := bbase (se 3 (by rfl) ⟨275321, by rfl⟩ : syracuseStep 1468381 = 550643) (by norm_num)
theorem B8775701 : Blo 770335 8775701 := bbase (se 6 (by rfl) ⟨205680, by rfl⟩ : syracuseStep 8775701 = 411361) (by norm_num)
theorem B1959997 : Blo 770335 1959997 := bbase (se 3 (by rfl) ⟨367499, by rfl⟩ : syracuseStep 1959997 = 734999) (by norm_num)
theorem B976961 : Blo 770335 976961 := bbase (se 2 (by rfl) ⟨366360, by rfl⟩ : syracuseStep 976961 = 732721) (by norm_num)
theorem B1304653 : Blo 770335 1304653 := bbase (se 3 (by rfl) ⟨244622, by rfl⟩ : syracuseStep 1304653 = 489245) (by norm_num)
theorem B1239133 : Blo 770335 1239133 := bbase (se 3 (by rfl) ⟨232337, by rfl⟩ : syracuseStep 1239133 = 464675) (by norm_num)
theorem B1468525 : Blo 770335 1468525 := bbase (se 3 (by rfl) ⟨275348, by rfl⟩ : syracuseStep 1468525 = 550697) (by norm_num)
theorem B977017 : Blo 770335 977017 := bbase (se 2 (by rfl) ⟨366381, by rfl⟩ : syracuseStep 977017 = 732763) (by norm_num)
theorem B1304741 : Blo 770335 1304741 := bbase (se 4 (by rfl) ⟨122319, by rfl⟩ : syracuseStep 1304741 = 244639) (by norm_num)
theorem B977113 : Blo 770335 977113 := bbase (se 2 (by rfl) ⟨366417, by rfl⟩ : syracuseStep 977113 = 732835) (by norm_num)
theorem B1566965 : Blo 770335 1566965 := bbase (se 5 (by rfl) ⟨73451, by rfl⟩ : syracuseStep 1566965 = 146903) (by norm_num)
theorem B2091253 : Blo 770335 2091253 := bbase (se 5 (by rfl) ⟨98027, by rfl⟩ : syracuseStep 2091253 = 196055) (by norm_num)
theorem B1468685 : Blo 770335 1468685 := bbase (se 3 (by rfl) ⟨275378, by rfl⟩ : syracuseStep 1468685 = 550757) (by norm_num)
theorem B1304869 : Blo 770335 1304869 := bbase (se 4 (by rfl) ⟨122331, by rfl⟩ : syracuseStep 1304869 = 244663) (by norm_num)
theorem B1239389 : Blo 770335 1239389 := bbase (se 3 (by rfl) ⟨232385, by rfl⟩ : syracuseStep 1239389 = 464771) (by norm_num)
theorem B5859701 : Blo 770335 5859701 := bbase (se 5 (by rfl) ⟨274673, by rfl⟩ : syracuseStep 5859701 = 549347) (by norm_num)
theorem B1304957 : Blo 770335 1304957 := bbase (se 3 (by rfl) ⟨244679, by rfl⟩ : syracuseStep 1304957 = 489359) (by norm_num)
theorem B977285 : Blo 770335 977285 := bbase (se 4 (by rfl) ⟨91620, by rfl⟩ : syracuseStep 977285 = 183241) (by norm_num)
theorem B1468829 : Blo 770335 1468829 := bbase (se 3 (by rfl) ⟨275405, by rfl⟩ : syracuseStep 1468829 = 550811) (by norm_num)
theorem B1173941 : Blo 770335 1173941 := bbase (se 5 (by rfl) ⟨55028, by rfl⟩ : syracuseStep 1173941 = 110057) (by norm_num)
theorem B977341 : Blo 770335 977341 := bbase (se 3 (by rfl) ⟨183251, by rfl⟩ : syracuseStep 977341 = 366503) (by norm_num)
theorem B1305085 : Blo 770335 1305085 := bbase (se 3 (by rfl) ⟨244703, by rfl⟩ : syracuseStep 1305085 = 489407) (by norm_num)
theorem B977437 : Blo 770335 977437 := bbase (se 3 (by rfl) ⟨183269, by rfl⟩ : syracuseStep 977437 = 366539) (by norm_num)
theorem B1239581 : Blo 770335 1239581 := bbase (se 3 (by rfl) ⟨232421, by rfl⟩ : syracuseStep 1239581 = 464843) (by norm_num)
theorem B1305173 : Blo 770335 1305173 := bbase (se 8 (by rfl) ⟨7647, by rfl⟩ : syracuseStep 1305173 = 15295) (by norm_num)
theorem B2976389 : Blo 770335 2976389 := bbase (se 4 (by rfl) ⟨279036, by rfl⟩ : syracuseStep 2976389 = 558073) (by norm_num)
theorem B2091685 : Blo 770335 2091685 := bbase (se 4 (by rfl) ⟨196095, by rfl⟩ : syracuseStep 2091685 = 392191) (by norm_num)
theorem B1469117 : Blo 770335 1469117 := bbase (se 3 (by rfl) ⟨275459, by rfl⟩ : syracuseStep 1469117 = 550919) (by norm_num)
theorem B977609 : Blo 770335 977609 := bbase (se 2 (by rfl) ⟨366603, by rfl⟩ : syracuseStep 977609 = 733207) (by norm_num)
theorem B1305301 : Blo 770335 1305301 := bbase (se 7 (by rfl) ⟨15296, by rfl⟩ : syracuseStep 1305301 = 30593) (by norm_num)
theorem B977665 : Blo 770335 977665 := bbase (se 2 (by rfl) ⟨366624, by rfl⟩ : syracuseStep 977665 = 733249) (by norm_num)
theorem B781073 : Blo 770335 781073 := bbase (se 2 (by rfl) ⟨292902, by rfl⟩ : syracuseStep 781073 = 585805) (by norm_num)
theorem B1567525 : Blo 770335 1567525 := bbase (se 4 (by rfl) ⟨146955, by rfl⟩ : syracuseStep 1567525 = 293911) (by norm_num)
theorem B1305389 : Blo 770335 1305389 := bbase (se 3 (by rfl) ⟨244760, by rfl⟩ : syracuseStep 1305389 = 489521) (by norm_num)
theorem B1469269 : Blo 770335 1469269 := bbase (se 9 (by rfl) ⟨4304, by rfl⟩ : syracuseStep 1469269 = 8609) (by norm_num)
theorem B977761 : Blo 770335 977761 := bbase (se 2 (by rfl) ⟨366660, by rfl⟩ : syracuseStep 977761 = 733321) (by norm_num)
theorem B4942741 : Blo 770335 4942741 := bbase (se 6 (by rfl) ⟨115845, by rfl⟩ : syracuseStep 4942741 = 231691) (by norm_num)
theorem B1305517 : Blo 770335 1305517 := bbase (se 3 (by rfl) ⟨244784, by rfl⟩ : syracuseStep 1305517 = 489569) (by norm_num)
theorem B1043389 : Blo 770335 1043389 := bbase (se 3 (by rfl) ⟨195635, by rfl⟩ : syracuseStep 1043389 = 391271) (by norm_num)
theorem B3304421 : Blo 770335 3304421 := bbase (se 4 (by rfl) ⟨309789, by rfl⟩ : syracuseStep 3304421 = 619579) (by norm_num)
theorem B781309 : Blo 770335 781309 := bbase (se 3 (by rfl) ⟨146495, by rfl⟩ : syracuseStep 781309 = 292991) (by norm_num)
theorem B1305605 : Blo 770335 1305605 := bbase (se 4 (by rfl) ⟨122400, by rfl⟩ : syracuseStep 1305605 = 244801) (by norm_num)
theorem B977933 : Blo 770335 977933 := bbase (se 3 (by rfl) ⟨183362, by rfl⟩ : syracuseStep 977933 = 366725) (by norm_num)
theorem B977989 : Blo 770335 977989 := bbase (se 4 (by rfl) ⟨91686, by rfl⟩ : syracuseStep 977989 = 183373) (by norm_num)
theorem B1305733 : Blo 770335 1305733 := bbase (se 4 (by rfl) ⟨122412, by rfl⟩ : syracuseStep 1305733 = 244825) (by norm_num)
theorem B1469573 : Blo 770335 1469573 := bbase (se 4 (by rfl) ⟨137772, by rfl⟩ : syracuseStep 1469573 = 275545) (by norm_num)
theorem B978085 : Blo 770335 978085 := bbase (se 4 (by rfl) ⟨91695, by rfl⟩ : syracuseStep 978085 = 183391) (by norm_num)
theorem B1305821 : Blo 770335 1305821 := bbase (se 3 (by rfl) ⟨244841, by rfl⟩ : syracuseStep 1305821 = 489683) (by norm_num)
theorem B978257 : Blo 770335 978257 := bbase (se 2 (by rfl) ⟨366846, by rfl⟩ : syracuseStep 978257 = 733693) (by norm_num)
theorem B1305949 : Blo 770335 1305949 := bbase (se 3 (by rfl) ⟨244865, by rfl⟩ : syracuseStep 1305949 = 489731) (by norm_num)
theorem B978313 : Blo 770335 978313 := bbase (se 2 (by rfl) ⟨366867, by rfl⟩ : syracuseStep 978313 = 733735) (by norm_num)
theorem B5270933 : Blo 770335 5270933 := bbase (se 6 (by rfl) ⟨123537, by rfl⟩ : syracuseStep 5270933 = 247075) (by norm_num)
theorem B880021 : Blo 770335 880021 := bbase (se 6 (by rfl) ⟨20625, by rfl⟩ : syracuseStep 880021 = 41251) (by norm_num)
theorem B1306037 : Blo 770335 1306037 := bbase (se 5 (by rfl) ⟨61220, by rfl⟩ : syracuseStep 1306037 = 122441) (by norm_num)
theorem B1174981 : Blo 770335 1174981 := bbase (se 4 (by rfl) ⟨110154, by rfl⟩ : syracuseStep 1174981 = 220309) (by norm_num)
theorem B978409 : Blo 770335 978409 := bbase (se 2 (by rfl) ⟨366903, by rfl⟩ : syracuseStep 978409 = 733807) (by norm_num)
theorem B1633781 : Blo 770335 1633781 := bbase (se 5 (by rfl) ⟨76583, by rfl⟩ : syracuseStep 1633781 = 153167) (by norm_num)
theorem B880141 : Blo 770335 880141 := bbase (se 3 (by rfl) ⟨165026, by rfl⟩ : syracuseStep 880141 = 330053) (by norm_num)
theorem B781849 : Blo 770335 781849 := bbase (se 2 (by rfl) ⟨293193, by rfl⟩ : syracuseStep 781849 = 586387) (by norm_num)
theorem B1175077 : Blo 770335 1175077 := bbase (se 4 (by rfl) ⟨110163, by rfl⟩ : syracuseStep 1175077 = 220327) (by norm_num)
theorem B2780725 : Blo 770335 2780725 := bbase (se 5 (by rfl) ⟨130346, by rfl⟩ : syracuseStep 2780725 = 260693) (by norm_num)
theorem B1306165 : Blo 770335 1306165 := bbase (se 5 (by rfl) ⟨61226, by rfl⟩ : syracuseStep 1306165 = 122453) (by norm_num)
theorem B6614581 : Blo 770335 6614581 := bbase (se 5 (by rfl) ⟨310058, by rfl⟩ : syracuseStep 6614581 = 620117) (by norm_num)
theorem B1306253 : Blo 770335 1306253 := bbase (se 3 (by rfl) ⟨244922, by rfl⟩ : syracuseStep 1306253 = 489845) (by norm_num)
theorem B978581 : Blo 770335 978581 := bbase (se 6 (by rfl) ⟨22935, by rfl⟩ : syracuseStep 978581 = 45871) (by norm_num)
theorem B978637 : Blo 770335 978637 := bbase (se 3 (by rfl) ⟨183494, by rfl⟩ : syracuseStep 978637 = 366989) (by norm_num)
theorem B1175285 : Blo 770335 1175285 := bbase (se 5 (by rfl) ⟨55091, by rfl⟩ : syracuseStep 1175285 = 110183) (by norm_num)
theorem B1306381 : Blo 770335 1306381 := bbase (se 3 (by rfl) ⟨244946, by rfl⟩ : syracuseStep 1306381 = 489893) (by norm_num)
theorem B978733 : Blo 770335 978733 := bbase (se 3 (by rfl) ⟨183512, by rfl⟩ : syracuseStep 978733 = 367025) (by norm_num)
theorem B2092853 : Blo 770335 2092853 := bbase (se 5 (by rfl) ⟨98102, by rfl⟩ : syracuseStep 2092853 = 196205) (by norm_num)
theorem B1306469 : Blo 770335 1306469 := bbase (se 4 (by rfl) ⟨122481, by rfl⟩ : syracuseStep 1306469 = 244963) (by norm_num)
theorem B1175405 : Blo 770335 1175405 := bbase (se 3 (by rfl) ⟨220388, by rfl⟩ : syracuseStep 1175405 = 440777) (by norm_num)
theorem B6352757 : Blo 770335 6352757 := bbase (se 5 (by rfl) ⟨297785, by rfl⟩ : syracuseStep 6352757 = 595571) (by norm_num)
theorem B1568717 : Blo 770335 1568717 := bbase (se 3 (by rfl) ⟨294134, by rfl⟩ : syracuseStep 1568717 = 588269) (by norm_num)
theorem B978905 : Blo 770335 978905 := bbase (se 2 (by rfl) ⟨367089, by rfl⟩ : syracuseStep 978905 = 734179) (by norm_num)
theorem B1306597 : Blo 770335 1306597 := bbase (se 4 (by rfl) ⟨122493, by rfl⟩ : syracuseStep 1306597 = 244987) (by norm_num)
theorem B978961 : Blo 770335 978961 := bbase (se 2 (by rfl) ⟨367110, by rfl⟩ : syracuseStep 978961 = 734221) (by norm_num)
theorem B1306685 : Blo 770335 1306685 := bbase (se 3 (by rfl) ⟨245003, by rfl⟩ : syracuseStep 1306685 = 490007) (by norm_num)
theorem B1044589 : Blo 770335 1044589 := bbase (se 3 (by rfl) ⟨195860, by rfl⟩ : syracuseStep 1044589 = 391721) (by norm_num)
theorem B979057 : Blo 770335 979057 := bbase (se 2 (by rfl) ⟨367146, by rfl⟩ : syracuseStep 979057 = 734293) (by norm_num)
theorem B1568893 : Blo 770335 1568893 := bbase (se 3 (by rfl) ⟨294167, by rfl⟩ : syracuseStep 1568893 = 588335) (by norm_num)
theorem B782465 : Blo 770335 782465 := bbase (se 2 (by rfl) ⟨293424, by rfl⟩ : syracuseStep 782465 = 586849) (by norm_num)
theorem B979229 : Blo 770335 979229 := bbase (se 3 (by rfl) ⟨183605, by rfl⟩ : syracuseStep 979229 = 367211) (by norm_num)
theorem B979285 : Blo 770335 979285 := bbase (se 10 (by rfl) ⟨1434, by rfl⟩ : syracuseStep 979285 = 2869) (by norm_num)
theorem B979381 : Blo 770335 979381 := bbase (se 5 (by rfl) ⟨45908, by rfl⟩ : syracuseStep 979381 = 91817) (by norm_num)
theorem B1765973 : Blo 770335 1765973 := bbase (se 8 (by rfl) ⟨10347, by rfl⟩ : syracuseStep 1765973 = 20695) (by norm_num)
theorem B979553 : Blo 770335 979553 := bbase (se 2 (by rfl) ⟨367332, by rfl⟩ : syracuseStep 979553 = 734665) (by norm_num)
theorem B979609 : Blo 770335 979609 := bbase (se 2 (by rfl) ⟨367353, by rfl⟩ : syracuseStep 979609 = 734707) (by norm_num)
theorem B2257573 : Blo 770335 2257573 := bbase (se 4 (by rfl) ⟨211647, by rfl⟩ : syracuseStep 2257573 = 423295) (by norm_num)
theorem B1733309 : Blo 770335 1733309 := bbase (se 3 (by rfl) ⟨324995, by rfl⟩ : syracuseStep 1733309 = 649991) (by norm_num)
theorem B7533269 : Blo 770335 7533269 := bbase (se 7 (by rfl) ⟨88280, by rfl⟩ : syracuseStep 7533269 = 176561) (by norm_num)
theorem B3306197 : Blo 770335 3306197 := bbase (se 7 (by rfl) ⟨38744, by rfl⟩ : syracuseStep 3306197 = 77489) (by norm_num)
theorem B979705 : Blo 770335 979705 := bbase (se 2 (by rfl) ⟨367389, by rfl⟩ : syracuseStep 979705 = 734779) (by norm_num)
theorem B1733381 : Blo 770335 1733381 := bbase (se 4 (by rfl) ⟨162504, by rfl⟩ : syracuseStep 1733381 = 325009) (by norm_num)
theorem B1733453 : Blo 770335 1733453 := bbase (se 3 (by rfl) ⟨325022, by rfl⟩ : syracuseStep 1733453 = 650045) (by norm_num)
theorem B1733525 : Blo 770335 1733525 := bbase (se 6 (by rfl) ⟨40629, by rfl⟩ : syracuseStep 1733525 = 81259) (by norm_num)
theorem B1930133 : Blo 770335 1930133 := bbase (se 6 (by rfl) ⟨45237, by rfl⟩ : syracuseStep 1930133 = 90475) (by norm_num)
theorem B979877 : Blo 770335 979877 := bbase (se 4 (by rfl) ⟨91863, by rfl⟩ : syracuseStep 979877 = 183727) (by norm_num)
theorem B881609 : Blo 770335 881609 := bbase (se 2 (by rfl) ⟨330603, by rfl⟩ : syracuseStep 881609 = 661207) (by norm_num)
theorem B1733597 : Blo 770335 1733597 := bbase (se 3 (by rfl) ⟨325049, by rfl⟩ : syracuseStep 1733597 = 650099) (by norm_num)
theorem B979933 : Blo 770335 979933 := bbase (se 3 (by rfl) ⟨183737, by rfl⟩ : syracuseStep 979933 = 367475) (by norm_num)
theorem B7435253 : Blo 770335 7435253 := bbase (se 5 (by rfl) ⟨348527, by rfl⟩ : syracuseStep 7435253 = 697055) (by norm_num)
theorem B783361 : Blo 770335 783361 := bbase (se 2 (by rfl) ⟨293760, by rfl⟩ : syracuseStep 783361 = 587521) (by norm_num)
theorem B1733669 : Blo 770335 1733669 := bbase (se 4 (by rfl) ⟨162531, by rfl⟩ : syracuseStep 1733669 = 325063) (by norm_num)
theorem B1733741 : Blo 770335 1733741 := bbase (se 3 (by rfl) ⟨325076, by rfl⟩ : syracuseStep 1733741 = 650153) (by norm_num)
theorem B1733813 : Blo 770335 1733813 := bbase (se 5 (by rfl) ⟨81272, by rfl⟩ : syracuseStep 1733813 = 162545) (by norm_num)
theorem B1668277 : Blo 770335 1668277 := bbase (se 5 (by rfl) ⟨78200, by rfl⟩ : syracuseStep 1668277 = 156401) (by norm_num)
theorem B1733885 : Blo 770335 1733885 := bbase (se 3 (by rfl) ⟨325103, by rfl⟩ : syracuseStep 1733885 = 650207) (by norm_num)
theorem B1733957 : Blo 770335 1733957 := bbase (se 4 (by rfl) ⟨162558, by rfl⟩ : syracuseStep 1733957 = 325117) (by norm_num)
theorem B1734029 : Blo 770335 1734029 := bbase (se 3 (by rfl) ⟨325130, by rfl⟩ : syracuseStep 1734029 = 650261) (by norm_num)
theorem B2717093 : Blo 770335 2717093 := bbase (se 4 (by rfl) ⟨254727, by rfl⟩ : syracuseStep 2717093 = 509455) (by norm_num)
theorem B1734101 : Blo 770335 1734101 := bbase (se 7 (by rfl) ⟨20321, by rfl⟩ : syracuseStep 1734101 = 40643) (by norm_num)
theorem B1045973 : Blo 770335 1045973 := bbase (se 7 (by rfl) ⟨12257, by rfl⟩ : syracuseStep 1045973 = 24515) (by norm_num)
theorem B1177109 : Blo 770335 1177109 := bbase (se 6 (by rfl) ⟨27588, by rfl⟩ : syracuseStep 1177109 = 55177) (by norm_num)
theorem B1734173 : Blo 770335 1734173 := bbase (se 3 (by rfl) ⟨325157, by rfl⟩ : syracuseStep 1734173 = 650315) (by norm_num)
theorem B1504861 : Blo 770335 1504861 := bbase (se 3 (by rfl) ⟨282161, by rfl⟩ : syracuseStep 1504861 = 564323) (by norm_num)
theorem B1734245 : Blo 770335 1734245 := bbase (se 4 (by rfl) ⟨162585, by rfl⟩ : syracuseStep 1734245 = 325171) (by norm_num)
theorem B783977 : Blo 770335 783977 := bbase (se 2 (by rfl) ⟨293991, by rfl⟩ : syracuseStep 783977 = 587983) (by norm_num)
theorem B1734317 : Blo 770335 1734317 := bbase (se 3 (by rfl) ⟨325184, by rfl⟩ : syracuseStep 1734317 = 650369) (by norm_num)
theorem B3307189 : Blo 770335 3307189 := bbase (se 5 (by rfl) ⟨155024, by rfl⟩ : syracuseStep 3307189 = 310049) (by norm_num)
theorem B1734389 : Blo 770335 1734389 := bbase (se 5 (by rfl) ⟨81299, by rfl⟩ : syracuseStep 1734389 = 162599) (by norm_num)
theorem B1734461 : Blo 770335 1734461 := bbase (se 3 (by rfl) ⟨325211, by rfl⟩ : syracuseStep 1734461 = 650423) (by norm_num)
theorem B1734533 : Blo 770335 1734533 := bbase (se 4 (by rfl) ⟨162612, by rfl⟩ : syracuseStep 1734533 = 325225) (by norm_num)
theorem B1734605 : Blo 770335 1734605 := bbase (se 3 (by rfl) ⟨325238, by rfl⟩ : syracuseStep 1734605 = 650477) (by norm_num)
theorem B1734677 : Blo 770335 1734677 := bbase (se 6 (by rfl) ⟨40656, by rfl⟩ : syracuseStep 1734677 = 81313) (by norm_num)
theorem B1734749 : Blo 770335 1734749 := bbase (se 3 (by rfl) ⟨325265, by rfl⟩ : syracuseStep 1734749 = 650531) (by norm_num)
theorem B1734821 : Blo 770335 1734821 := bbase (se 4 (by rfl) ⟨162639, by rfl⟩ : syracuseStep 1734821 = 325279) (by norm_num)
theorem B784561 : Blo 770335 784561 := bbase (se 2 (by rfl) ⟨294210, by rfl⟩ : syracuseStep 784561 = 588421) (by norm_num)
theorem B784609 : Blo 770335 784609 := bbase (se 2 (by rfl) ⟨294228, by rfl⟩ : syracuseStep 784609 = 588457) (by norm_num)
theorem B1734893 : Blo 770335 1734893 := bbase (se 3 (by rfl) ⟨325292, by rfl⟩ : syracuseStep 1734893 = 650585) (by norm_num)
theorem B4389173 : Blo 770335 4389173 := bbase (se 5 (by rfl) ⟨205742, by rfl⟩ : syracuseStep 4389173 = 411485) (by norm_num)
theorem B1734965 : Blo 770335 1734965 := bbase (se 5 (by rfl) ⟨81326, by rfl⟩ : syracuseStep 1734965 = 162653) (by norm_num)
theorem B1735037 : Blo 770335 1735037 := bbase (se 3 (by rfl) ⟨325319, by rfl⟩ : syracuseStep 1735037 = 650639) (by norm_num)
theorem B1735109 : Blo 770335 1735109 := bbase (se 4 (by rfl) ⟨162666, by rfl⟩ : syracuseStep 1735109 = 325333) (by norm_num)
theorem B1735181 : Blo 770335 1735181 := bbase (se 3 (by rfl) ⟨325346, by rfl⟩ : syracuseStep 1735181 = 650693) (by norm_num)
theorem B1735253 : Blo 770335 1735253 := bbase (se 8 (by rfl) ⟨10167, by rfl⟩ : syracuseStep 1735253 = 20335) (by norm_num)
theorem B1735325 : Blo 770335 1735325 := bbase (se 3 (by rfl) ⟨325373, by rfl⟩ : syracuseStep 1735325 = 650747) (by norm_num)
theorem B1735397 : Blo 770335 1735397 := bbase (se 4 (by rfl) ⟨162693, by rfl⟩ : syracuseStep 1735397 = 325387) (by norm_num)
theorem B10582805 : Blo 770335 10582805 := bbase (se 6 (by rfl) ⟨248034, by rfl⟩ : syracuseStep 10582805 = 496069) (by norm_num)
theorem B1735469 : Blo 770335 1735469 := bbase (se 3 (by rfl) ⟨325400, by rfl⟩ : syracuseStep 1735469 = 650801) (by norm_num)
theorem B3767093 : Blo 770335 3767093 := bbase (se 5 (by rfl) ⟨176582, by rfl⟩ : syracuseStep 3767093 = 353165) (by norm_num)
theorem B1735541 : Blo 770335 1735541 := bbase (se 5 (by rfl) ⟨81353, by rfl⟩ : syracuseStep 1735541 = 162707) (by norm_num)
theorem B1735613 : Blo 770335 1735613 := bbase (se 3 (by rfl) ⟨325427, by rfl⟩ : syracuseStep 1735613 = 650855) (by norm_num)
theorem B1407989 : Blo 770335 1407989 := bbase (se 5 (by rfl) ⟨65999, by rfl⟩ : syracuseStep 1407989 = 131999) (by norm_num)
theorem B1735685 : Blo 770335 1735685 := bbase (se 4 (by rfl) ⟨162720, by rfl⟩ : syracuseStep 1735685 = 325441) (by norm_num)
theorem B1735757 : Blo 770335 1735757 := bbase (se 3 (by rfl) ⟨325454, by rfl⟩ : syracuseStep 1735757 = 650909) (by norm_num)
theorem B1735829 : Blo 770335 1735829 := bbase (se 6 (by rfl) ⟨40683, by rfl⟩ : syracuseStep 1735829 = 81367) (by norm_num)
theorem B1735901 : Blo 770335 1735901 := bbase (se 3 (by rfl) ⟨325481, by rfl⟩ : syracuseStep 1735901 = 650963) (by norm_num)
theorem B1735973 : Blo 770335 1735973 := bbase (se 4 (by rfl) ⟨162747, by rfl⟩ : syracuseStep 1735973 = 325495) (by norm_num)
theorem B1736045 : Blo 770335 1736045 := bbase (se 3 (by rfl) ⟨325508, by rfl⟩ : syracuseStep 1736045 = 651017) (by norm_num)
theorem B1736117 : Blo 770335 1736117 := bbase (se 5 (by rfl) ⟨81380, by rfl⟩ : syracuseStep 1736117 = 162761) (by norm_num)
theorem B1736189 : Blo 770335 1736189 := bbase (se 3 (by rfl) ⟨325535, by rfl⟩ : syracuseStep 1736189 = 651071) (by norm_num)
theorem B1736261 : Blo 770335 1736261 := bbase (se 4 (by rfl) ⟨162774, by rfl⟩ : syracuseStep 1736261 = 325549) (by norm_num)
theorem B1736333 : Blo 770335 1736333 := bbase (se 3 (by rfl) ⟨325562, by rfl⟩ : syracuseStep 1736333 = 651125) (by norm_num)
theorem B1736405 : Blo 770335 1736405 := bbase (se 7 (by rfl) ⟨20348, by rfl⟩ : syracuseStep 1736405 = 40697) (by norm_num)
theorem B1736477 : Blo 770335 1736477 := bbase (se 3 (by rfl) ⟨325589, by rfl⟩ : syracuseStep 1736477 = 651179) (by norm_num)
theorem B1736549 : Blo 770335 1736549 := bbase (se 4 (by rfl) ⟨162801, by rfl⟩ : syracuseStep 1736549 = 325603) (by norm_num)
theorem B1736621 : Blo 770335 1736621 := bbase (se 3 (by rfl) ⟨325616, by rfl⟩ : syracuseStep 1736621 = 651233) (by norm_num)
theorem B1736693 : Blo 770335 1736693 := bbase (se 5 (by rfl) ⟨81407, by rfl⟩ : syracuseStep 1736693 = 162815) (by norm_num)
theorem B28508213 : Blo 770335 28508213 := bstep (se 5 (by rfl) ⟨1336322, by rfl⟩ : syracuseStep 28508213 = 2672645) B2672645
theorem B1736945 : Blo 770335 1736945 := bstep (se 2 (by rfl) ⟨651354, by rfl⟩ : syracuseStep 1736945 = 1302709) B1302709
theorem B1736963 : Blo 770335 1736963 := bstep (se 1 (by rfl) ⟨1302722, by rfl⟩ : syracuseStep 1736963 = 2605445) B2605445
theorem B4817251 : Blo 770335 4817251 := bstep (se 1 (by rfl) ⟨3612938, by rfl⟩ : syracuseStep 4817251 = 7225877) B7225877
theorem B2195885 : Blo 770335 2195885 := bstep (se 3 (by rfl) ⟨411728, by rfl⟩ : syracuseStep 2195885 = 823457) B823457
theorem B3899825 : Blo 770335 3899825 := bstep (se 2 (by rfl) ⟨1462434, by rfl⟩ : syracuseStep 3899825 = 2924869) B2924869
theorem B1737233 : Blo 770335 1737233 := bstep (se 2 (by rfl) ⟨651462, by rfl⟩ : syracuseStep 1737233 = 1302925) B1302925
theorem B1737251 : Blo 770335 1737251 := bstep (se 1 (by rfl) ⟨1302938, by rfl⟩ : syracuseStep 1737251 = 2605877) B2605877
theorem B2196067 : Blo 770335 2196067 := bstep (se 1 (by rfl) ⟨1647050, by rfl⟩ : syracuseStep 2196067 = 3294101) B3294101
theorem B2228849 : Blo 770335 2228849 := bstep (se 2 (by rfl) ⟨835818, by rfl⟩ : syracuseStep 2228849 = 1671637) B1671637
theorem B4948613 : Blo 770335 4948613 := bstep (se 4 (by rfl) ⟨463932, by rfl⟩ : syracuseStep 4948613 = 927865) B927865
theorem B2196227 : Blo 770335 2196227 := bstep (se 1 (by rfl) ⟨1647170, by rfl⟩ : syracuseStep 2196227 = 3294341) B3294341
theorem B1737521 : Blo 770335 1737521 := bstep (se 2 (by rfl) ⟨651570, by rfl⟩ : syracuseStep 1737521 = 1303141) B1303141
theorem B1737539 : Blo 770335 1737539 := bstep (se 1 (by rfl) ⟨1303154, by rfl⟩ : syracuseStep 1737539 = 2606309) B2606309
theorem B15827825 : Blo 770335 15827825 := bstep (se 2 (by rfl) ⟨5935434, by rfl⟩ : syracuseStep 15827825 = 11870869) B11870869
theorem B9372685 : Blo 770335 9372685 := bstep (se 3 (by rfl) ⟨1757378, by rfl⟩ : syracuseStep 9372685 = 3514757) B3514757
theorem B1737809 : Blo 770335 1737809 := bstep (se 2 (by rfl) ⟨651678, by rfl⟩ : syracuseStep 1737809 = 1303357) B1303357
theorem B1737827 : Blo 770335 1737827 := bstep (se 1 (by rfl) ⟨1303370, by rfl⟩ : syracuseStep 1737827 = 2606741) B2606741
theorem B1738097 : Blo 770335 1738097 := bstep (se 2 (by rfl) ⟨651786, by rfl⟩ : syracuseStep 1738097 = 1303573) B1303573
theorem B1738115 : Blo 770335 1738115 := bstep (se 1 (by rfl) ⟨1303586, by rfl⟩ : syracuseStep 1738115 = 2607173) B2607173
theorem B7046669 : Blo 770335 7046669 := bstep (se 3 (by rfl) ⟨1321250, by rfl⟩ : syracuseStep 7046669 = 2642501) B2642501
theorem B4392589 : Blo 770335 4392589 := bstep (se 3 (by rfl) ⟨823610, by rfl⟩ : syracuseStep 4392589 = 1647221) B1647221
theorem B1738385 : Blo 770335 1738385 := bstep (se 2 (by rfl) ⟨651894, by rfl⟩ : syracuseStep 1738385 = 1303789) B1303789
theorem B1672849 : Blo 770335 1672849 := bstep (se 2 (by rfl) ⟨627318, by rfl⟩ : syracuseStep 1672849 = 1254637) B1254637
theorem B1738403 : Blo 770335 1738403 := bstep (se 1 (by rfl) ⟨1303802, by rfl⟩ : syracuseStep 1738403 = 2607605) B2607605
theorem B2197297 : Blo 770335 2197297 := bstep (se 2 (by rfl) ⟨823986, by rfl⟩ : syracuseStep 2197297 = 1647973) B1647973
theorem B3901283 : Blo 770335 3901283 := bstep (se 1 (by rfl) ⟨2925962, by rfl⟩ : syracuseStep 3901283 = 5851925) B5851925
theorem B8816525 : Blo 770335 8816525 := bstep (se 3 (by rfl) ⟨1653098, by rfl⟩ : syracuseStep 8816525 = 3306197) B3306197
theorem B1738673 : Blo 770335 1738673 := bstep (se 2 (by rfl) ⟨652002, by rfl⟩ : syracuseStep 1738673 = 1304005) B1304005
theorem B1738691 : Blo 770335 1738691 := bstep (se 1 (by rfl) ⟨1304018, by rfl⟩ : syracuseStep 1738691 = 2608037) B2608037
theorem B1738961 : Blo 770335 1738961 := bstep (se 2 (by rfl) ⟨652110, by rfl⟩ : syracuseStep 1738961 = 1304221) B1304221
theorem B1738979 : Blo 770335 1738979 := bstep (se 1 (by rfl) ⟨1304234, by rfl⟩ : syracuseStep 1738979 = 2608469) B2608469
theorem B5147021 : Blo 770335 5147021 := bstep (se 3 (by rfl) ⟨965066, by rfl⟩ : syracuseStep 5147021 = 1930133) B1930133
theorem B1739249 : Blo 770335 1739249 := bstep (se 2 (by rfl) ⟨652218, by rfl⟩ : syracuseStep 1739249 = 1304437) B1304437
theorem B1739267 : Blo 770335 1739267 := bstep (se 1 (by rfl) ⟨1304450, by rfl⟩ : syracuseStep 1739267 = 2608901) B2608901
theorem B2787875 : Blo 770335 2787875 := bstep (se 1 (by rfl) ⟨2090906, by rfl⟩ : syracuseStep 2787875 = 4181813) B4181813
theorem B3902093 : Blo 770335 3902093 := bstep (se 3 (by rfl) ⟨731642, by rfl⟩ : syracuseStep 3902093 = 1463285) B1463285
theorem B19827341 : Blo 770335 19827341 := bstep (se 3 (by rfl) ⟨3717626, by rfl⟩ : syracuseStep 19827341 = 7435253) B7435253
theorem B1739537 : Blo 770335 1739537 := bstep (se 2 (by rfl) ⟨652326, by rfl⟩ : syracuseStep 1739537 = 1304653) B1304653
theorem B1739555 : Blo 770335 1739555 := bstep (se 1 (by rfl) ⟨1304666, by rfl⟩ : syracuseStep 1739555 = 2609333) B2609333
theorem B7048133 : Blo 770335 7048133 := bstep (se 4 (by rfl) ⟨660762, by rfl⟩ : syracuseStep 7048133 = 1321525) B1321525
theorem B2788337 : Blo 770335 2788337 := bstep (se 2 (by rfl) ⟨1045626, by rfl⟩ : syracuseStep 2788337 = 2091253) B2091253
theorem B2198573 : Blo 770335 2198573 := bstep (se 3 (by rfl) ⟨412232, by rfl⟩ : syracuseStep 2198573 = 824465) B824465
theorem B1739825 : Blo 770335 1739825 := bstep (se 2 (by rfl) ⟨652434, by rfl⟩ : syracuseStep 1739825 = 1304869) B1304869
theorem B1739843 : Blo 770335 1739843 := bstep (se 1 (by rfl) ⟨1304882, by rfl⟩ : syracuseStep 1739843 = 2609765) B2609765
theorem B2198755 : Blo 770335 2198755 := bstep (se 1 (by rfl) ⟨1649066, by rfl⟩ : syracuseStep 2198755 = 3298133) B3298133
theorem B2198801 : Blo 770335 2198801 := bstep (se 2 (by rfl) ⟨824550, by rfl⟩ : syracuseStep 2198801 = 1649101) B1649101
theorem B1412387 : Blo 770335 1412387 := bstep (se 1 (by rfl) ⟨1059290, by rfl⟩ : syracuseStep 1412387 = 2118581) B2118581
theorem B1740113 : Blo 770335 1740113 := bstep (se 2 (by rfl) ⟨652542, by rfl⟩ : syracuseStep 1740113 = 1305085) B1305085
theorem B1740131 : Blo 770335 1740131 := bstep (se 1 (by rfl) ⟨1305098, by rfl⟩ : syracuseStep 1740131 = 2610197) B2610197
theorem B2788913 : Blo 770335 2788913 := bstep (se 2 (by rfl) ⟨1045842, by rfl⟩ : syracuseStep 2788913 = 2091685) B2091685
theorem B4394573 : Blo 770335 4394573 := bstep (se 3 (by rfl) ⟨823982, by rfl⟩ : syracuseStep 4394573 = 1647965) B1647965
theorem B1740401 : Blo 770335 1740401 := bstep (se 2 (by rfl) ⟨652650, by rfl⟩ : syracuseStep 1740401 = 1305301) B1305301
theorem B1740419 : Blo 770335 1740419 := bstep (se 1 (by rfl) ⟨1305314, by rfl⟩ : syracuseStep 1740419 = 2610629) B2610629
theorem B4951813 : Blo 770335 4951813 := bstep (se 4 (by rfl) ⟨464232, by rfl⟩ : syracuseStep 4951813 = 928465) B928465
theorem B6590321 : Blo 770335 6590321 := bstep (se 2 (by rfl) ⟨2471370, by rfl⟩ : syracuseStep 6590321 = 4942741) B4942741
theorem B2789261 : Blo 770335 2789261 := bstep (se 3 (by rfl) ⟨522986, by rfl⟩ : syracuseStep 2789261 = 1045973) B1045973
theorem B1740689 : Blo 770335 1740689 := bstep (se 2 (by rfl) ⟨652758, by rfl⟩ : syracuseStep 1740689 = 1305517) B1305517
theorem B1740707 : Blo 770335 1740707 := bstep (se 1 (by rfl) ⟨1305530, by rfl⟩ : syracuseStep 1740707 = 2611061) B2611061
theorem B1740977 : Blo 770335 1740977 := bstep (se 2 (by rfl) ⟨652866, by rfl⟩ : syracuseStep 1740977 = 1305733) B1305733
theorem B1740995 : Blo 770335 1740995 := bstep (se 1 (by rfl) ⟨1305746, by rfl⟩ : syracuseStep 1740995 = 2611493) B2611493
theorem B3707171 : Blo 770335 3707171 := bstep (se 1 (by rfl) ⟨2780378, by rfl⟩ : syracuseStep 3707171 = 5560757) B5560757
theorem B1741265 : Blo 770335 1741265 := bstep (se 2 (by rfl) ⟨652974, by rfl⟩ : syracuseStep 1741265 = 1305949) B1305949
theorem B1741283 : Blo 770335 1741283 := bstep (se 1 (by rfl) ⟨1305962, by rfl⟩ : syracuseStep 1741283 = 2611925) B2611925
theorem B4395505 : Blo 770335 4395505 := bstep (se 2 (by rfl) ⟨1648314, by rfl⟩ : syracuseStep 4395505 = 3296629) B3296629
theorem B30511669 : Blo 770335 30511669 := bstep (se 5 (by rfl) ⟨1430234, by rfl⟩ : syracuseStep 30511669 = 2860469) B2860469
theorem B2200259 : Blo 770335 2200259 := bstep (se 1 (by rfl) ⟨1650194, by rfl⟩ : syracuseStep 2200259 = 3300389) B3300389
theorem B3707633 : Blo 770335 3707633 := bstep (se 2 (by rfl) ⟨1390362, by rfl⟩ : syracuseStep 3707633 = 2780725) B2780725
theorem B1741553 : Blo 770335 1741553 := bstep (se 2 (by rfl) ⟨653082, by rfl⟩ : syracuseStep 1741553 = 1306165) B1306165
theorem B824051 : Blo 770335 824051 := bstep (se 1 (by rfl) ⟨618038, by rfl⟩ : syracuseStep 824051 = 1236077) B1236077
theorem B8819441 : Blo 770335 8819441 := bstep (se 2 (by rfl) ⟨3307290, by rfl⟩ : syracuseStep 8819441 = 6614581) B6614581
theorem B1741571 : Blo 770335 1741571 := bstep (se 1 (by rfl) ⟨1306178, by rfl⟩ : syracuseStep 1741571 = 2612357) B2612357
theorem B1741841 : Blo 770335 1741841 := bstep (se 2 (by rfl) ⟨653190, by rfl⟩ : syracuseStep 1741841 = 1306381) B1306381
theorem B1741859 : Blo 770335 1741859 := bstep (se 1 (by rfl) ⟨1306394, by rfl⟩ : syracuseStep 1741859 = 2612789) B2612789
theorem B1742129 : Blo 770335 1742129 := bstep (se 2 (by rfl) ⟨653298, by rfl⟩ : syracuseStep 1742129 = 1306597) B1306597
theorem B1742147 : Blo 770335 1742147 := bstep (se 1 (by rfl) ⟨1306610, by rfl⟩ : syracuseStep 1742147 = 2613221) B2613221
theorem B3905009 : Blo 770335 3905009 := bstep (se 2 (by rfl) ⟨1464378, by rfl⟩ : syracuseStep 3905009 = 2928757) B2928757
theorem B824995 : Blo 770335 824995 := bstep (se 1 (by rfl) ⟨618746, by rfl⟩ : syracuseStep 824995 = 1237493) B1237493
theorem B2201489 : Blo 770335 2201489 := bstep (se 2 (by rfl) ⟨825558, by rfl⟩ : syracuseStep 2201489 = 1651117) B1651117
theorem B4396963 : Blo 770335 4396963 := bstep (se 1 (by rfl) ⟨3297722, by rfl⟩ : syracuseStep 4396963 = 6595445) B6595445
theorem B1251281 : Blo 770335 1251281 := bstep (se 2 (by rfl) ⟨469230, by rfl⟩ : syracuseStep 1251281 = 938461) B938461
theorem B4397489 : Blo 770335 4397489 := bstep (se 2 (by rfl) ⟨1649058, by rfl⟩ : syracuseStep 4397489 = 3298117) B3298117
theorem B826259 : Blo 770335 826259 := bstep (se 1 (by rfl) ⟨619694, by rfl⟩ : syracuseStep 826259 = 1239389) B1239389
theorem B3906467 : Blo 770335 3906467 := bstep (se 1 (by rfl) ⟨2929850, by rfl⟩ : syracuseStep 3906467 = 5859701) B5859701
theorem B1317953 : Blo 770335 1317953 := bstep (se 2 (by rfl) ⟨494232, by rfl⟩ : syracuseStep 1317953 = 988465) B988465
theorem B1645667 : Blo 770335 1645667 := bstep (se 1 (by rfl) ⟨1234250, by rfl⟩ : syracuseStep 1645667 = 2468501) B2468501
theorem B4955377 : Blo 770335 4955377 := bstep (se 2 (by rfl) ⟨1858266, by rfl⟩ : syracuseStep 4955377 = 3716533) B3716533
theorem B2202947 : Blo 770335 2202947 := bstep (se 1 (by rfl) ⟨1652210, by rfl⟩ : syracuseStep 2202947 = 3304421) B3304421
theorem B4693445 : Blo 770335 4693445 := bstep (se 4 (by rfl) ⟨440010, by rfl⟩ : syracuseStep 4693445 = 880021) B880021
theorem B1252961 : Blo 770335 1252961 := bstep (se 2 (by rfl) ⟨469860, by rfl⟩ : syracuseStep 1252961 = 939721) B939721
theorem B3513955 : Blo 770335 3513955 := bstep (se 1 (by rfl) ⟨2635466, by rfl⟩ : syracuseStep 3513955 = 5270933) B5270933
theorem B4169357 : Blo 770335 4169357 := bstep (se 3 (by rfl) ⟨781754, by rfl⟩ : syracuseStep 4169357 = 1563509) B1563509
theorem B1089187 : Blo 770335 1089187 := bstep (se 1 (by rfl) ⟨816890, by rfl⟩ : syracuseStep 1089187 = 1633781) B1633781
theorem B1646257 : Blo 770335 1646257 := bstep (se 2 (by rfl) ⟨617346, by rfl⟩ : syracuseStep 1646257 = 1234693) B1234693
theorem B3907277 : Blo 770335 3907277 := bstep (se 3 (by rfl) ⟨732614, by rfl⟩ : syracuseStep 3907277 = 1465229) B1465229
theorem B4398947 : Blo 770335 4398947 := bstep (se 1 (by rfl) ⟨3299210, by rfl⟩ : syracuseStep 4398947 = 6598421) B6598421
theorem B3710861 : Blo 770335 3710861 := bstep (se 3 (by rfl) ⟨695786, by rfl⟩ : syracuseStep 3710861 = 1391573) B1391573
theorem B4235171 : Blo 770335 4235171 := bstep (se 1 (by rfl) ⟨3176378, by rfl⟩ : syracuseStep 4235171 = 6352757) B6352757
theorem B2203757 : Blo 770335 2203757 := bstep (se 3 (by rfl) ⟨413204, by rfl⟩ : syracuseStep 2203757 = 826409) B826409
theorem B8331445 : Blo 770335 8331445 := bstep (se 5 (by rfl) ⟨390536, by rfl⟩ : syracuseStep 8331445 = 781073) B781073
theorem B6267077 : Blo 770335 6267077 := bstep (se 4 (by rfl) ⟨587538, by rfl⟩ : syracuseStep 6267077 = 1175077) B1175077
theorem B1056979 : Blo 770335 1056979 := bstep (se 1 (by rfl) ⟨792734, by rfl⟩ : syracuseStep 1056979 = 1585469) B1585469
theorem B2203949 : Blo 770335 2203949 := bstep (se 3 (by rfl) ⟨413240, by rfl⟩ : syracuseStep 2203949 = 826481) B826481
theorem B1155521 : Blo 770335 1155521 := bstep (se 2 (by rfl) ⟨433320, by rfl⟩ : syracuseStep 1155521 = 866641) B866641
theorem B1155539 : Blo 770335 1155539 := bstep (se 1 (by rfl) ⟨866654, by rfl⟩ : syracuseStep 1155539 = 1733309) B1733309
theorem B5022179 : Blo 770335 5022179 := bstep (se 1 (by rfl) ⟨3766634, by rfl⟩ : syracuseStep 5022179 = 7533269) B7533269
theorem B1155569 : Blo 770335 1155569 := bstep (se 2 (by rfl) ⟨433338, by rfl⟩ : syracuseStep 1155569 = 866677) B866677
theorem B1155587 : Blo 770335 1155587 := bstep (se 1 (by rfl) ⟨866690, by rfl⟩ : syracuseStep 1155587 = 1733381) B1733381
theorem B1155617 : Blo 770335 1155617 := bstep (se 2 (by rfl) ⟨433356, by rfl⟩ : syracuseStep 1155617 = 866713) B866713
theorem B1155635 : Blo 770335 1155635 := bstep (se 1 (by rfl) ⟨866726, by rfl⟩ : syracuseStep 1155635 = 1733453) B1733453
theorem B22290997 : Blo 770335 22290997 := bstep (se 5 (by rfl) ⟨1044890, by rfl⟩ : syracuseStep 22290997 = 2089781) B2089781
theorem B1155665 : Blo 770335 1155665 := bstep (se 2 (by rfl) ⟨433374, by rfl⟩ : syracuseStep 1155665 = 866749) B866749
theorem B1155683 : Blo 770335 1155683 := bstep (se 1 (by rfl) ⟨866762, by rfl⟩ : syracuseStep 1155683 = 1733525) B1733525
theorem B1155713 : Blo 770335 1155713 := bstep (se 2 (by rfl) ⟨433392, by rfl⟩ : syracuseStep 1155713 = 866785) B866785
theorem B4694669 : Blo 770335 4694669 := bstep (se 3 (by rfl) ⟨880250, by rfl⟩ : syracuseStep 4694669 = 1760501) B1760501
theorem B1155731 : Blo 770335 1155731 := bstep (se 1 (by rfl) ⟨866798, by rfl⟩ : syracuseStep 1155731 = 1733597) B1733597
theorem B1155761 : Blo 770335 1155761 := bstep (se 2 (by rfl) ⟨433410, by rfl⟩ : syracuseStep 1155761 = 866821) B866821
theorem B1155779 : Blo 770335 1155779 := bstep (se 1 (by rfl) ⟨866834, by rfl⟩ : syracuseStep 1155779 = 1733669) B1733669
theorem B926419 : Blo 770335 926419 := bstep (se 1 (by rfl) ⟨694814, by rfl⟩ : syracuseStep 926419 = 1389629) B1389629
theorem B1155809 : Blo 770335 1155809 := bstep (se 2 (by rfl) ⟨433428, by rfl⟩ : syracuseStep 1155809 = 866857) B866857
theorem B1155827 : Blo 770335 1155827 := bstep (se 1 (by rfl) ⟨866870, by rfl⟩ : syracuseStep 1155827 = 1733741) B1733741
theorem B1155857 : Blo 770335 1155857 := bstep (se 2 (by rfl) ⟨433446, by rfl⟩ : syracuseStep 1155857 = 866893) B866893
theorem B1155875 : Blo 770335 1155875 := bstep (se 1 (by rfl) ⟨866906, by rfl⟩ : syracuseStep 1155875 = 1733813) B1733813
theorem B1155905 : Blo 770335 1155905 := bstep (se 2 (by rfl) ⟨433464, by rfl⟩ : syracuseStep 1155905 = 866929) B866929
theorem B1155923 : Blo 770335 1155923 := bstep (se 1 (by rfl) ⟨866942, by rfl⟩ : syracuseStep 1155923 = 1733885) B1733885
theorem B1155953 : Blo 770335 1155953 := bstep (se 2 (by rfl) ⟨433482, by rfl⟩ : syracuseStep 1155953 = 866965) B866965
theorem B1155971 : Blo 770335 1155971 := bstep (se 1 (by rfl) ⟨866978, by rfl⟩ : syracuseStep 1155971 = 1733957) B1733957
theorem B1156001 : Blo 770335 1156001 := bstep (se 2 (by rfl) ⟨433500, by rfl⟩ : syracuseStep 1156001 = 867001) B867001
theorem B1156019 : Blo 770335 1156019 := bstep (se 1 (by rfl) ⟨867014, by rfl⟩ : syracuseStep 1156019 = 1734029) B1734029
theorem B1811395 : Blo 770335 1811395 := bstep (se 1 (by rfl) ⟨1358546, by rfl⟩ : syracuseStep 1811395 = 2717093) B2717093
theorem B1156049 : Blo 770335 1156049 := bstep (se 2 (by rfl) ⟨433518, by rfl⟩ : syracuseStep 1156049 = 867037) B867037
theorem B1156067 : Blo 770335 1156067 := bstep (se 1 (by rfl) ⟨867050, by rfl⟩ : syracuseStep 1156067 = 1734101) B1734101
theorem B1156097 : Blo 770335 1156097 := bstep (se 2 (by rfl) ⟨433536, by rfl⟩ : syracuseStep 1156097 = 867073) B867073
theorem B9905165 : Blo 770335 9905165 := bstep (se 3 (by rfl) ⟨1857218, by rfl⟩ : syracuseStep 9905165 = 3714437) B3714437
theorem B1156115 : Blo 770335 1156115 := bstep (se 1 (by rfl) ⟨867086, by rfl⟩ : syracuseStep 1156115 = 1734173) B1734173
theorem B1156145 : Blo 770335 1156145 := bstep (se 2 (by rfl) ⟨433554, by rfl⟩ : syracuseStep 1156145 = 867109) B867109
theorem B1156163 : Blo 770335 1156163 := bstep (se 1 (by rfl) ⟨867122, by rfl⟩ : syracuseStep 1156163 = 1734245) B1734245
theorem B1156193 : Blo 770335 1156193 := bstep (se 2 (by rfl) ⟨433572, by rfl⟩ : syracuseStep 1156193 = 867145) B867145
theorem B1156211 : Blo 770335 1156211 := bstep (se 1 (by rfl) ⟨867158, by rfl⟩ : syracuseStep 1156211 = 1734317) B1734317
theorem B1156241 : Blo 770335 1156241 := bstep (se 2 (by rfl) ⟨433590, by rfl⟩ : syracuseStep 1156241 = 867181) B867181
theorem B1156259 : Blo 770335 1156259 := bstep (se 1 (by rfl) ⟨867194, by rfl⟩ : syracuseStep 1156259 = 1734389) B1734389
theorem B1156289 : Blo 770335 1156289 := bstep (se 2 (by rfl) ⟨433608, by rfl⟩ : syracuseStep 1156289 = 867217) B867217
theorem B1156307 : Blo 770335 1156307 := bstep (se 1 (by rfl) ⟨867230, by rfl⟩ : syracuseStep 1156307 = 1734461) B1734461
theorem B992467 : Blo 770335 992467 := bstep (se 1 (by rfl) ⟨744350, by rfl⟩ : syracuseStep 992467 = 1488701) B1488701
theorem B1156337 : Blo 770335 1156337 := bstep (se 2 (by rfl) ⟨433626, by rfl⟩ : syracuseStep 1156337 = 867253) B867253
theorem B1156355 : Blo 770335 1156355 := bstep (se 1 (by rfl) ⟨867266, by rfl⟩ : syracuseStep 1156355 = 1734533) B1734533
theorem B2204941 : Blo 770335 2204941 := bstep (se 3 (by rfl) ⟨413426, by rfl⟩ : syracuseStep 2204941 = 826853) B826853
theorem B1156385 : Blo 770335 1156385 := bstep (se 2 (by rfl) ⟨433644, by rfl⟩ : syracuseStep 1156385 = 867289) B867289
theorem B1156403 : Blo 770335 1156403 := bstep (se 1 (by rfl) ⟨867302, by rfl⟩ : syracuseStep 1156403 = 1734605) B1734605
theorem B1156433 : Blo 770335 1156433 := bstep (se 2 (by rfl) ⟨433662, by rfl⟩ : syracuseStep 1156433 = 867325) B867325
theorem B1156451 : Blo 770335 1156451 := bstep (se 1 (by rfl) ⟨867338, by rfl⟩ : syracuseStep 1156451 = 1734677) B1734677
theorem B1156481 : Blo 770335 1156481 := bstep (se 2 (by rfl) ⟨433680, by rfl⟩ : syracuseStep 1156481 = 867361) B867361
theorem B1156499 : Blo 770335 1156499 := bstep (se 1 (by rfl) ⟨867374, by rfl⟩ : syracuseStep 1156499 = 1734749) B1734749
theorem B1156529 : Blo 770335 1156529 := bstep (se 2 (by rfl) ⟨433698, by rfl⟩ : syracuseStep 1156529 = 867397) B867397
theorem B1156547 : Blo 770335 1156547 := bstep (se 1 (by rfl) ⟨867410, by rfl⟩ : syracuseStep 1156547 = 1734821) B1734821
theorem B6038981 : Blo 770335 6038981 := bstep (se 4 (by rfl) ⟨566154, by rfl⟩ : syracuseStep 6038981 = 1132309) B1132309
theorem B1156577 : Blo 770335 1156577 := bstep (se 2 (by rfl) ⟨433716, by rfl⟩ : syracuseStep 1156577 = 867433) B867433
theorem B1156595 : Blo 770335 1156595 := bstep (se 1 (by rfl) ⟨867446, by rfl⟩ : syracuseStep 1156595 = 1734893) B1734893
theorem B927235 : Blo 770335 927235 := bstep (se 1 (by rfl) ⟨695426, by rfl⟩ : syracuseStep 927235 = 1390853) B1390853
theorem B1156625 : Blo 770335 1156625 := bstep (se 2 (by rfl) ⟨433734, by rfl⟩ : syracuseStep 1156625 = 867469) B867469
theorem B2926115 : Blo 770335 2926115 := bstep (se 1 (by rfl) ⟨2194586, by rfl⟩ : syracuseStep 2926115 = 4389173) B4389173
theorem B1156643 : Blo 770335 1156643 := bstep (se 1 (by rfl) ⟨867482, by rfl⟩ : syracuseStep 1156643 = 1734965) B1734965
theorem B1156673 : Blo 770335 1156673 := bstep (se 2 (by rfl) ⟨433752, by rfl⟩ : syracuseStep 1156673 = 867505) B867505
theorem B1156691 : Blo 770335 1156691 := bstep (se 1 (by rfl) ⟨867518, by rfl⟩ : syracuseStep 1156691 = 1735037) B1735037
theorem B1156721 : Blo 770335 1156721 := bstep (se 2 (by rfl) ⟨433770, by rfl⟩ : syracuseStep 1156721 = 867541) B867541
theorem B1156739 : Blo 770335 1156739 := bstep (se 1 (by rfl) ⟨867554, by rfl⟩ : syracuseStep 1156739 = 1735109) B1735109
theorem B1156769 : Blo 770335 1156769 := bstep (se 2 (by rfl) ⟨433788, by rfl⟩ : syracuseStep 1156769 = 867577) B867577
theorem B1156787 : Blo 770335 1156787 := bstep (se 1 (by rfl) ⟨867590, by rfl⟩ : syracuseStep 1156787 = 1735181) B1735181
theorem B4400837 : Blo 770335 4400837 := bstep (se 4 (by rfl) ⟨412578, by rfl⟩ : syracuseStep 4400837 = 825157) B825157
theorem B1156817 : Blo 770335 1156817 := bstep (se 2 (by rfl) ⟨433806, by rfl⟩ : syracuseStep 1156817 = 867613) B867613
theorem B1156835 : Blo 770335 1156835 := bstep (se 1 (by rfl) ⟨867626, by rfl⟩ : syracuseStep 1156835 = 1735253) B1735253
theorem B1156865 : Blo 770335 1156865 := bstep (se 2 (by rfl) ⟨433824, by rfl⟩ : syracuseStep 1156865 = 867649) B867649
theorem B1156883 : Blo 770335 1156883 := bstep (se 1 (by rfl) ⟨867662, by rfl⟩ : syracuseStep 1156883 = 1735325) B1735325
theorem B25011989 : Blo 770335 25011989 := bstep (se 6 (by rfl) ⟨586218, by rfl⟩ : syracuseStep 25011989 = 1172437) B1172437
theorem B1156913 : Blo 770335 1156913 := bstep (se 2 (by rfl) ⟨433842, by rfl⟩ : syracuseStep 1156913 = 867685) B867685
theorem B1156931 : Blo 770335 1156931 := bstep (se 1 (by rfl) ⟨867698, by rfl⟩ : syracuseStep 1156931 = 1735397) B1735397
theorem B1156961 : Blo 770335 1156961 := bstep (se 2 (by rfl) ⟨433860, by rfl⟩ : syracuseStep 1156961 = 867721) B867721
theorem B7055203 : Blo 770335 7055203 := bstep (se 1 (by rfl) ⟨5291402, by rfl⟩ : syracuseStep 7055203 = 10582805) B10582805
theorem B1156979 : Blo 770335 1156979 := bstep (se 1 (by rfl) ⟨867734, by rfl⟩ : syracuseStep 1156979 = 1735469) B1735469
theorem B1157009 : Blo 770335 1157009 := bstep (se 2 (by rfl) ⟨433878, by rfl⟩ : syracuseStep 1157009 = 867757) B867757
theorem B1157027 : Blo 770335 1157027 := bstep (se 1 (by rfl) ⟨867770, by rfl⟩ : syracuseStep 1157027 = 1735541) B1735541
theorem B1157057 : Blo 770335 1157057 := bstep (se 2 (by rfl) ⟨433896, by rfl⟩ : syracuseStep 1157057 = 867793) B867793
theorem B1157075 : Blo 770335 1157075 := bstep (se 1 (by rfl) ⟨867806, by rfl⟩ : syracuseStep 1157075 = 1735613) B1735613
theorem B1157105 : Blo 770335 1157105 := bstep (se 2 (by rfl) ⟨433914, by rfl⟩ : syracuseStep 1157105 = 867829) B867829
theorem B1157123 : Blo 770335 1157123 := bstep (se 1 (by rfl) ⟨867842, by rfl⟩ : syracuseStep 1157123 = 1735685) B1735685
theorem B1320977 : Blo 770335 1320977 := bstep (se 2 (by rfl) ⟨495366, by rfl⟩ : syracuseStep 1320977 = 990733) B990733
theorem B1157153 : Blo 770335 1157153 := bstep (se 2 (by rfl) ⟨433932, by rfl⟩ : syracuseStep 1157153 = 867865) B867865
theorem B1157171 : Blo 770335 1157171 := bstep (se 1 (by rfl) ⟨867878, by rfl⟩ : syracuseStep 1157171 = 1735757) B1735757
theorem B1157201 : Blo 770335 1157201 := bstep (se 2 (by rfl) ⟨433950, by rfl⟩ : syracuseStep 1157201 = 867901) B867901
theorem B1157219 : Blo 770335 1157219 := bstep (se 1 (by rfl) ⟨867914, by rfl⟩ : syracuseStep 1157219 = 1735829) B1735829
theorem B1157249 : Blo 770335 1157249 := bstep (se 2 (by rfl) ⟨433968, by rfl⟩ : syracuseStep 1157249 = 867937) B867937
theorem B1157267 : Blo 770335 1157267 := bstep (se 1 (by rfl) ⟨867950, by rfl⟩ : syracuseStep 1157267 = 1735901) B1735901
theorem B1157297 : Blo 770335 1157297 := bstep (se 2 (by rfl) ⟨433986, by rfl⟩ : syracuseStep 1157297 = 867973) B867973
theorem B1157315 : Blo 770335 1157315 := bstep (se 1 (by rfl) ⟨867986, by rfl⟩ : syracuseStep 1157315 = 1735973) B1735973
theorem B1157345 : Blo 770335 1157345 := bstep (se 2 (by rfl) ⟨434004, by rfl⟩ : syracuseStep 1157345 = 868009) B868009
theorem B7416035 : Blo 770335 7416035 := bstep (se 1 (by rfl) ⟨5562026, by rfl⟩ : syracuseStep 7416035 = 11124053) B11124053
theorem B1157363 : Blo 770335 1157363 := bstep (se 1 (by rfl) ⟨868022, by rfl⟩ : syracuseStep 1157363 = 1736045) B1736045
theorem B1157393 : Blo 770335 1157393 := bstep (se 2 (by rfl) ⟨434022, by rfl⟩ : syracuseStep 1157393 = 868045) B868045
theorem B1157411 : Blo 770335 1157411 := bstep (se 1 (by rfl) ⟨868058, by rfl⟩ : syracuseStep 1157411 = 1736117) B1736117
theorem B1157441 : Blo 770335 1157441 := bstep (se 2 (by rfl) ⟨434040, by rfl⟩ : syracuseStep 1157441 = 868081) B868081
theorem B1157459 : Blo 770335 1157459 := bstep (se 1 (by rfl) ⟨868094, by rfl⟩ : syracuseStep 1157459 = 1736189) B1736189
theorem B1157489 : Blo 770335 1157489 := bstep (se 2 (by rfl) ⟨434058, by rfl⟩ : syracuseStep 1157489 = 868117) B868117
theorem B1157507 : Blo 770335 1157507 := bstep (se 1 (by rfl) ⟨868130, by rfl⟩ : syracuseStep 1157507 = 1736261) B1736261
theorem B1157537 : Blo 770335 1157537 := bstep (se 2 (by rfl) ⟨434076, by rfl⟩ : syracuseStep 1157537 = 868153) B868153
theorem B2468269 : Blo 770335 2468269 := bstep (se 3 (by rfl) ⟨462800, by rfl⟩ : syracuseStep 2468269 = 925601) B925601
theorem B1157555 : Blo 770335 1157555 := bstep (se 1 (by rfl) ⟨868166, by rfl⟩ : syracuseStep 1157555 = 1736333) B1736333
theorem B1157585 : Blo 770335 1157585 := bstep (se 2 (by rfl) ⟨434094, by rfl⟩ : syracuseStep 1157585 = 868189) B868189
theorem B1157603 : Blo 770335 1157603 := bstep (se 1 (by rfl) ⟨868202, by rfl⟩ : syracuseStep 1157603 = 1736405) B1736405
theorem B1157633 : Blo 770335 1157633 := bstep (se 2 (by rfl) ⟨434112, by rfl⟩ : syracuseStep 1157633 = 868225) B868225
theorem B2927117 : Blo 770335 2927117 := bstep (se 3 (by rfl) ⟨548834, by rfl⟩ : syracuseStep 2927117 = 1097669) B1097669
theorem B1157651 : Blo 770335 1157651 := bstep (se 1 (by rfl) ⟨868238, by rfl⟩ : syracuseStep 1157651 = 1736477) B1736477
theorem B1157681 : Blo 770335 1157681 := bstep (se 2 (by rfl) ⟨434130, by rfl⟩ : syracuseStep 1157681 = 868261) B868261
theorem B3910193 : Blo 770335 3910193 := bstep (se 2 (by rfl) ⟨1466322, by rfl⟩ : syracuseStep 3910193 = 2932645) B2932645
theorem B1157699 : Blo 770335 1157699 := bstep (se 1 (by rfl) ⟨868274, by rfl⟩ : syracuseStep 1157699 = 1736549) B1736549
theorem B1157729 : Blo 770335 1157729 := bstep (se 2 (by rfl) ⟨434148, by rfl⟩ : syracuseStep 1157729 = 868297) B868297
theorem B1157747 : Blo 770335 1157747 := bstep (se 1 (by rfl) ⟨868310, by rfl⟩ : syracuseStep 1157747 = 1736621) B1736621
theorem B1157777 : Blo 770335 1157777 := bstep (se 2 (by rfl) ⟨434166, by rfl⟩ : syracuseStep 1157777 = 868333) B868333
theorem B1157795 : Blo 770335 1157795 := bstep (se 1 (by rfl) ⟨868346, by rfl⟩ : syracuseStep 1157795 = 1736693) B1736693
theorem B1157825 : Blo 770335 1157825 := bstep (se 2 (by rfl) ⟨434184, by rfl⟩ : syracuseStep 1157825 = 868369) B868369
theorem B1157843 : Blo 770335 1157843 := bstep (se 1 (by rfl) ⟨868382, by rfl⟩ : syracuseStep 1157843 = 1736765) B1736765
theorem B1157873 : Blo 770335 1157873 := bstep (se 2 (by rfl) ⟨434202, by rfl⟩ : syracuseStep 1157873 = 868405) B868405
theorem B1157891 : Blo 770335 1157891 := bstep (se 1 (by rfl) ⟨868418, by rfl⟩ : syracuseStep 1157891 = 1736837) B1736837
theorem B1157921 : Blo 770335 1157921 := bstep (se 2 (by rfl) ⟨434220, by rfl⟩ : syracuseStep 1157921 = 868441) B868441
theorem B1649443 : Blo 770335 1649443 := bstep (se 1 (by rfl) ⟨1237082, by rfl⟩ : syracuseStep 1649443 = 2474165) B2474165
theorem B1157939 : Blo 770335 1157939 := bstep (se 1 (by rfl) ⟨868454, by rfl⟩ : syracuseStep 1157939 = 1736909) B1736909
theorem B1157969 : Blo 770335 1157969 := bstep (se 2 (by rfl) ⟨434238, by rfl⟩ : syracuseStep 1157969 = 868477) B868477
theorem B1157987 : Blo 770335 1157987 := bstep (se 1 (by rfl) ⟨868490, by rfl⟩ : syracuseStep 1157987 = 1736981) B1736981
theorem B1158017 : Blo 770335 1158017 := bstep (se 2 (by rfl) ⟨434256, by rfl⟩ : syracuseStep 1158017 = 868513) B868513
theorem B1158035 : Blo 770335 1158035 := bstep (se 1 (by rfl) ⟨868526, by rfl⟩ : syracuseStep 1158035 = 1737053) B1737053
theorem B1158065 : Blo 770335 1158065 := bstep (se 2 (by rfl) ⟨434274, by rfl⟩ : syracuseStep 1158065 = 868549) B868549
theorem B1158083 : Blo 770335 1158083 := bstep (se 1 (by rfl) ⟨868562, by rfl⟩ : syracuseStep 1158083 = 1737125) B1737125
theorem B1158113 : Blo 770335 1158113 := bstep (se 2 (by rfl) ⟨434292, by rfl⟩ : syracuseStep 1158113 = 868585) B868585
theorem B1158131 : Blo 770335 1158131 := bstep (se 1 (by rfl) ⟨868598, by rfl⟩ : syracuseStep 1158131 = 1737197) B1737197
theorem B1158161 : Blo 770335 1158161 := bstep (se 2 (by rfl) ⟨434310, by rfl⟩ : syracuseStep 1158161 = 868621) B868621
theorem B1158179 : Blo 770335 1158179 := bstep (se 1 (by rfl) ⟨868634, by rfl⟩ : syracuseStep 1158179 = 1737269) B1737269
theorem B1158209 : Blo 770335 1158209 := bstep (se 2 (by rfl) ⟨434328, by rfl⟩ : syracuseStep 1158209 = 868657) B868657
theorem B1158227 : Blo 770335 1158227 := bstep (se 1 (by rfl) ⟨868670, by rfl⟩ : syracuseStep 1158227 = 1737341) B1737341
theorem B2600045 : Blo 770335 2600045 := bstep (se 3 (by rfl) ⟨487508, by rfl⟩ : syracuseStep 2600045 = 975017) B975017
theorem B1158257 : Blo 770335 1158257 := bstep (se 2 (by rfl) ⟨434346, by rfl⟩ : syracuseStep 1158257 = 868693) B868693
theorem B1158275 : Blo 770335 1158275 := bstep (se 1 (by rfl) ⟨868706, by rfl⟩ : syracuseStep 1158275 = 1737413) B1737413
theorem B1158305 : Blo 770335 1158305 := bstep (se 2 (by rfl) ⟨434364, by rfl⟩ : syracuseStep 1158305 = 868729) B868729
theorem B2600099 : Blo 770335 2600099 := bstep (se 1 (by rfl) ⟨1950074, by rfl⟩ : syracuseStep 2600099 = 3900149) B3900149
theorem B1158323 : Blo 770335 1158323 := bstep (se 1 (by rfl) ⟨868742, by rfl⟩ : syracuseStep 1158323 = 1737485) B1737485
theorem B1158353 : Blo 770335 1158353 := bstep (se 2 (by rfl) ⟨434382, by rfl⟩ : syracuseStep 1158353 = 868765) B868765
theorem B1158371 : Blo 770335 1158371 := bstep (se 1 (by rfl) ⟨868778, by rfl⟩ : syracuseStep 1158371 = 1737557) B1737557
theorem B1158401 : Blo 770335 1158401 := bstep (se 2 (by rfl) ⟨434400, by rfl⟩ : syracuseStep 1158401 = 868801) B868801
theorem B1158419 : Blo 770335 1158419 := bstep (se 1 (by rfl) ⟨868814, by rfl⟩ : syracuseStep 1158419 = 1737629) B1737629
theorem B1158449 : Blo 770335 1158449 := bstep (se 2 (by rfl) ⟨434418, by rfl⟩ : syracuseStep 1158449 = 868837) B868837
theorem B1158467 : Blo 770335 1158467 := bstep (se 1 (by rfl) ⟨868850, by rfl⟩ : syracuseStep 1158467 = 1737701) B1737701
theorem B1158497 : Blo 770335 1158497 := bstep (se 2 (by rfl) ⟨434436, by rfl⟩ : syracuseStep 1158497 = 868873) B868873
theorem B1158515 : Blo 770335 1158515 := bstep (se 1 (by rfl) ⟨868886, by rfl⟩ : syracuseStep 1158515 = 1737773) B1737773
theorem B1158545 : Blo 770335 1158545 := bstep (se 2 (by rfl) ⟨434454, by rfl⟩ : syracuseStep 1158545 = 868909) B868909
theorem B1158563 : Blo 770335 1158563 := bstep (se 1 (by rfl) ⟨868922, by rfl⟩ : syracuseStep 1158563 = 1737845) B1737845
theorem B2600369 : Blo 770335 2600369 := bstep (se 2 (by rfl) ⟨975138, by rfl⟩ : syracuseStep 2600369 = 1950277) B1950277
theorem B1158593 : Blo 770335 1158593 := bstep (se 2 (by rfl) ⟨434472, by rfl⟩ : syracuseStep 1158593 = 868945) B868945
theorem B1158611 : Blo 770335 1158611 := bstep (se 1 (by rfl) ⟨868958, by rfl⟩ : syracuseStep 1158611 = 1737917) B1737917
theorem B1158641 : Blo 770335 1158641 := bstep (se 2 (by rfl) ⟨434490, by rfl⟩ : syracuseStep 1158641 = 868981) B868981
theorem B1158659 : Blo 770335 1158659 := bstep (se 1 (by rfl) ⟨868994, by rfl⟩ : syracuseStep 1158659 = 1737989) B1737989
theorem B1158689 : Blo 770335 1158689 := bstep (se 2 (by rfl) ⟨434508, by rfl⟩ : syracuseStep 1158689 = 869017) B869017
theorem B1158707 : Blo 770335 1158707 := bstep (se 1 (by rfl) ⟨869030, by rfl⟩ : syracuseStep 1158707 = 1738061) B1738061
theorem B1158737 : Blo 770335 1158737 := bstep (se 2 (by rfl) ⟨434526, by rfl⟩ : syracuseStep 1158737 = 869053) B869053
theorem B1158755 : Blo 770335 1158755 := bstep (se 1 (by rfl) ⟨869066, by rfl⟩ : syracuseStep 1158755 = 1738133) B1738133
theorem B1650289 : Blo 770335 1650289 := bstep (se 2 (by rfl) ⟨618858, by rfl⟩ : syracuseStep 1650289 = 1237717) B1237717
theorem B1158785 : Blo 770335 1158785 := bstep (se 2 (by rfl) ⟨434544, by rfl⟩ : syracuseStep 1158785 = 869089) B869089
theorem B1158803 : Blo 770335 1158803 := bstep (se 1 (by rfl) ⟨869102, by rfl⟩ : syracuseStep 1158803 = 1738205) B1738205
theorem B1322659 : Blo 770335 1322659 := bstep (se 1 (by rfl) ⟨991994, by rfl⟩ : syracuseStep 1322659 = 1983989) B1983989
theorem B1158833 : Blo 770335 1158833 := bstep (se 2 (by rfl) ⟨434562, by rfl⟩ : syracuseStep 1158833 = 869125) B869125
theorem B1158851 : Blo 770335 1158851 := bstep (se 1 (by rfl) ⟨869138, by rfl⟩ : syracuseStep 1158851 = 1738277) B1738277
theorem B1158881 : Blo 770335 1158881 := bstep (se 2 (by rfl) ⟨434580, by rfl⟩ : syracuseStep 1158881 = 869161) B869161
theorem B1158899 : Blo 770335 1158899 := bstep (se 1 (by rfl) ⟨869174, by rfl⟩ : syracuseStep 1158899 = 1738349) B1738349
theorem B1158929 : Blo 770335 1158929 := bstep (se 2 (by rfl) ⟨434598, by rfl⟩ : syracuseStep 1158929 = 869197) B869197
theorem B1158947 : Blo 770335 1158947 := bstep (se 1 (by rfl) ⟨869210, by rfl⟩ : syracuseStep 1158947 = 1738421) B1738421
theorem B1158977 : Blo 770335 1158977 := bstep (se 2 (by rfl) ⟨434616, by rfl⟩ : syracuseStep 1158977 = 869233) B869233
theorem B1158995 : Blo 770335 1158995 := bstep (se 1 (by rfl) ⟨869246, by rfl⟩ : syracuseStep 1158995 = 1738493) B1738493
theorem B1159025 : Blo 770335 1159025 := bstep (se 2 (by rfl) ⟨434634, by rfl⟩ : syracuseStep 1159025 = 869269) B869269
theorem B1159043 : Blo 770335 1159043 := bstep (se 1 (by rfl) ⟨869282, by rfl⟩ : syracuseStep 1159043 = 1738565) B1738565
theorem B1159073 : Blo 770335 1159073 := bstep (se 2 (by rfl) ⟨434652, by rfl⟩ : syracuseStep 1159073 = 869305) B869305
theorem B1159091 : Blo 770335 1159091 := bstep (se 1 (by rfl) ⟨869318, by rfl⟩ : syracuseStep 1159091 = 1738637) B1738637
theorem B2600909 : Blo 770335 2600909 := bstep (se 3 (by rfl) ⟨487670, by rfl⟩ : syracuseStep 2600909 = 975341) B975341
theorem B1159121 : Blo 770335 1159121 := bstep (se 2 (by rfl) ⟨434670, by rfl⟩ : syracuseStep 1159121 = 869341) B869341
theorem B3911651 : Blo 770335 3911651 := bstep (se 1 (by rfl) ⟨2933738, by rfl⟩ : syracuseStep 3911651 = 5867477) B5867477
theorem B1159139 : Blo 770335 1159139 := bstep (se 1 (by rfl) ⟨869354, by rfl⟩ : syracuseStep 1159139 = 1738709) B1738709
theorem B1159169 : Blo 770335 1159169 := bstep (se 2 (by rfl) ⟨434688, by rfl⟩ : syracuseStep 1159169 = 869377) B869377
theorem B2600963 : Blo 770335 2600963 := bstep (se 1 (by rfl) ⟨1950722, by rfl⟩ : syracuseStep 2600963 = 3901445) B3901445
theorem B1159187 : Blo 770335 1159187 := bstep (se 1 (by rfl) ⟨869390, by rfl⟩ : syracuseStep 1159187 = 1738781) B1738781
theorem B1159217 : Blo 770335 1159217 := bstep (se 2 (by rfl) ⟨434706, by rfl⟩ : syracuseStep 1159217 = 869413) B869413
theorem B1159235 : Blo 770335 1159235 := bstep (se 1 (by rfl) ⟨869426, by rfl⟩ : syracuseStep 1159235 = 1738853) B1738853
theorem B1159265 : Blo 770335 1159265 := bstep (se 2 (by rfl) ⟨434724, by rfl⟩ : syracuseStep 1159265 = 869449) B869449
theorem B6697073 : Blo 770335 6697073 := bstep (se 2 (by rfl) ⟨2511402, by rfl⟩ : syracuseStep 6697073 = 5022805) B5022805
theorem B1159283 : Blo 770335 1159283 := bstep (se 1 (by rfl) ⟨869462, by rfl⟩ : syracuseStep 1159283 = 1738925) B1738925
theorem B1159313 : Blo 770335 1159313 := bstep (se 2 (by rfl) ⟨434742, by rfl⟩ : syracuseStep 1159313 = 869485) B869485
theorem B1159331 : Blo 770335 1159331 := bstep (se 1 (by rfl) ⟨869498, by rfl⟩ : syracuseStep 1159331 = 1738997) B1738997
theorem B1159361 : Blo 770335 1159361 := bstep (se 2 (by rfl) ⟨434760, by rfl⟩ : syracuseStep 1159361 = 869521) B869521
theorem B1159379 : Blo 770335 1159379 := bstep (se 1 (by rfl) ⟨869534, by rfl⟩ : syracuseStep 1159379 = 1739069) B1739069
theorem B2470115 : Blo 770335 2470115 := bstep (se 1 (by rfl) ⟨1852586, by rfl⟩ : syracuseStep 2470115 = 3705173) B3705173
theorem B1159409 : Blo 770335 1159409 := bstep (se 2 (by rfl) ⟨434778, by rfl⟩ : syracuseStep 1159409 = 869557) B869557
theorem B1159427 : Blo 770335 1159427 := bstep (se 1 (by rfl) ⟨869570, by rfl⟩ : syracuseStep 1159427 = 1739141) B1739141
theorem B2601233 : Blo 770335 2601233 := bstep (se 2 (by rfl) ⟨975462, by rfl⟩ : syracuseStep 2601233 = 1950925) B1950925
theorem B1159457 : Blo 770335 1159457 := bstep (se 2 (by rfl) ⟨434796, by rfl⟩ : syracuseStep 1159457 = 869593) B869593
theorem B1159475 : Blo 770335 1159475 := bstep (se 1 (by rfl) ⟨869606, by rfl⟩ : syracuseStep 1159475 = 1739213) B1739213
theorem B1159505 : Blo 770335 1159505 := bstep (se 2 (by rfl) ⟨434814, by rfl⟩ : syracuseStep 1159505 = 869629) B869629
theorem B1159523 : Blo 770335 1159523 := bstep (se 1 (by rfl) ⟨869642, by rfl⟩ : syracuseStep 1159523 = 1739285) B1739285
theorem B1159553 : Blo 770335 1159553 := bstep (se 2 (by rfl) ⟨434832, by rfl⟩ : syracuseStep 1159553 = 869665) B869665
theorem B1159571 : Blo 770335 1159571 := bstep (se 1 (by rfl) ⟨869678, by rfl⟩ : syracuseStep 1159571 = 1739357) B1739357
theorem B1159601 : Blo 770335 1159601 := bstep (se 2 (by rfl) ⟨434850, by rfl⟩ : syracuseStep 1159601 = 869701) B869701
theorem B1159619 : Blo 770335 1159619 := bstep (se 1 (by rfl) ⟨869714, by rfl⟩ : syracuseStep 1159619 = 1739429) B1739429
theorem B4960709 : Blo 770335 4960709 := bstep (se 4 (by rfl) ⟨465066, by rfl⟩ : syracuseStep 4960709 = 930133) B930133
theorem B1159649 : Blo 770335 1159649 := bstep (se 2 (by rfl) ⟨434868, by rfl⟩ : syracuseStep 1159649 = 869737) B869737
theorem B1159667 : Blo 770335 1159667 := bstep (se 1 (by rfl) ⟨869750, by rfl⟩ : syracuseStep 1159667 = 1739501) B1739501
theorem B2503181 : Blo 770335 2503181 := bstep (se 3 (by rfl) ⟨469346, by rfl⟩ : syracuseStep 2503181 = 938693) B938693
theorem B1159697 : Blo 770335 1159697 := bstep (se 2 (by rfl) ⟨434886, by rfl⟩ : syracuseStep 1159697 = 869773) B869773
theorem B1159715 : Blo 770335 1159715 := bstep (se 1 (by rfl) ⟨869786, by rfl⟩ : syracuseStep 1159715 = 1739573) B1739573
theorem B1159745 : Blo 770335 1159745 := bstep (se 2 (by rfl) ⟨434904, by rfl⟩ : syracuseStep 1159745 = 869809) B869809
theorem B2929229 : Blo 770335 2929229 := bstep (se 3 (by rfl) ⟨549230, by rfl⟩ : syracuseStep 2929229 = 1098461) B1098461
theorem B1159763 : Blo 770335 1159763 := bstep (se 1 (by rfl) ⟨869822, by rfl⟩ : syracuseStep 1159763 = 1739645) B1739645
theorem B2470513 : Blo 770335 2470513 := bstep (se 2 (by rfl) ⟨926442, by rfl⟩ : syracuseStep 2470513 = 1852885) B1852885
theorem B1159793 : Blo 770335 1159793 := bstep (se 2 (by rfl) ⟨434922, by rfl⟩ : syracuseStep 1159793 = 869845) B869845
theorem B1159811 : Blo 770335 1159811 := bstep (se 1 (by rfl) ⟨869858, by rfl⟩ : syracuseStep 1159811 = 1739717) B1739717
theorem B1159841 : Blo 770335 1159841 := bstep (se 2 (by rfl) ⟨434940, by rfl⟩ : syracuseStep 1159841 = 869881) B869881
theorem B1159859 : Blo 770335 1159859 := bstep (se 1 (by rfl) ⟨869894, by rfl⟩ : syracuseStep 1159859 = 1739789) B1739789
theorem B1159889 : Blo 770335 1159889 := bstep (se 2 (by rfl) ⟨434958, by rfl⟩ : syracuseStep 1159889 = 869917) B869917
theorem B1159907 : Blo 770335 1159907 := bstep (se 1 (by rfl) ⟨869930, by rfl⟩ : syracuseStep 1159907 = 1739861) B1739861
theorem B1159937 : Blo 770335 1159937 := bstep (se 2 (by rfl) ⟨434976, by rfl⟩ : syracuseStep 1159937 = 869953) B869953
theorem B3912461 : Blo 770335 3912461 := bstep (se 3 (by rfl) ⟨733586, by rfl⟩ : syracuseStep 3912461 = 1467173) B1467173
theorem B1159955 : Blo 770335 1159955 := bstep (se 1 (by rfl) ⟨869966, by rfl⟩ : syracuseStep 1159955 = 1739933) B1739933
theorem B2601773 : Blo 770335 2601773 := bstep (se 3 (by rfl) ⟨487832, by rfl⟩ : syracuseStep 2601773 = 975665) B975665
theorem B1159985 : Blo 770335 1159985 := bstep (se 2 (by rfl) ⟨434994, by rfl⟩ : syracuseStep 1159985 = 869989) B869989
theorem B1160003 : Blo 770335 1160003 := bstep (se 1 (by rfl) ⟨870002, by rfl⟩ : syracuseStep 1160003 = 1740005) B1740005
theorem B1160033 : Blo 770335 1160033 := bstep (se 2 (by rfl) ⟨435012, by rfl⟩ : syracuseStep 1160033 = 870025) B870025
theorem B2601827 : Blo 770335 2601827 := bstep (se 1 (by rfl) ⟨1951370, by rfl⟩ : syracuseStep 2601827 = 3902741) B3902741
theorem B1160051 : Blo 770335 1160051 := bstep (se 1 (by rfl) ⟨870038, by rfl⟩ : syracuseStep 1160051 = 1740077) B1740077
theorem B53523341 : Blo 770335 53523341 := bstep (se 3 (by rfl) ⟨10035626, by rfl⟩ : syracuseStep 53523341 = 20071253) B20071253
theorem B1160081 : Blo 770335 1160081 := bstep (se 2 (by rfl) ⟨435030, by rfl⟩ : syracuseStep 1160081 = 870061) B870061
theorem B1160099 : Blo 770335 1160099 := bstep (se 1 (by rfl) ⟨870074, by rfl⟩ : syracuseStep 1160099 = 1740149) B1740149
theorem B1160129 : Blo 770335 1160129 := bstep (se 2 (by rfl) ⟨435048, by rfl⟩ : syracuseStep 1160129 = 870097) B870097
theorem B1160147 : Blo 770335 1160147 := bstep (se 1 (by rfl) ⟨870110, by rfl⟩ : syracuseStep 1160147 = 1740221) B1740221
theorem B1160177 : Blo 770335 1160177 := bstep (se 2 (by rfl) ⟨435066, by rfl⟩ : syracuseStep 1160177 = 870133) B870133
theorem B1160195 : Blo 770335 1160195 := bstep (se 1 (by rfl) ⟨870146, by rfl⟩ : syracuseStep 1160195 = 1740293) B1740293
theorem B1160225 : Blo 770335 1160225 := bstep (se 2 (by rfl) ⟨435084, by rfl⟩ : syracuseStep 1160225 = 870169) B870169
theorem B2470961 : Blo 770335 2470961 := bstep (se 2 (by rfl) ⟨926610, by rfl⟩ : syracuseStep 2470961 = 1853221) B1853221
theorem B1160243 : Blo 770335 1160243 := bstep (se 1 (by rfl) ⟨870182, by rfl⟩ : syracuseStep 1160243 = 1740365) B1740365
theorem B1160273 : Blo 770335 1160273 := bstep (se 2 (by rfl) ⟨435102, by rfl⟩ : syracuseStep 1160273 = 870205) B870205
theorem B1160291 : Blo 770335 1160291 := bstep (se 1 (by rfl) ⟨870218, by rfl⟩ : syracuseStep 1160291 = 1740437) B1740437
theorem B2602097 : Blo 770335 2602097 := bstep (se 2 (by rfl) ⟨975786, by rfl⟩ : syracuseStep 2602097 = 1951573) B1951573
theorem B1160321 : Blo 770335 1160321 := bstep (se 2 (by rfl) ⟨435120, by rfl⟩ : syracuseStep 1160321 = 870241) B870241
theorem B1160339 : Blo 770335 1160339 := bstep (se 1 (by rfl) ⟨870254, by rfl⟩ : syracuseStep 1160339 = 1740509) B1740509
theorem B1160369 : Blo 770335 1160369 := bstep (se 2 (by rfl) ⟨435138, by rfl⟩ : syracuseStep 1160369 = 870277) B870277
theorem B1160387 : Blo 770335 1160387 := bstep (se 1 (by rfl) ⟨870290, by rfl⟩ : syracuseStep 1160387 = 1740581) B1740581
theorem B1160417 : Blo 770335 1160417 := bstep (se 2 (by rfl) ⟨435156, by rfl⟩ : syracuseStep 1160417 = 870313) B870313
theorem B1160435 : Blo 770335 1160435 := bstep (se 1 (by rfl) ⟨870326, by rfl⟩ : syracuseStep 1160435 = 1740653) B1740653
theorem B1160465 : Blo 770335 1160465 := bstep (se 2 (by rfl) ⟨435174, by rfl⟩ : syracuseStep 1160465 = 870349) B870349
theorem B1160483 : Blo 770335 1160483 := bstep (se 1 (by rfl) ⟨870362, by rfl⟩ : syracuseStep 1160483 = 1740725) B1740725
theorem B1160513 : Blo 770335 1160513 := bstep (se 2 (by rfl) ⟨435192, by rfl⟩ : syracuseStep 1160513 = 870385) B870385
theorem B1160531 : Blo 770335 1160531 := bstep (se 1 (by rfl) ⟨870398, by rfl⟩ : syracuseStep 1160531 = 1740797) B1740797
theorem B2930033 : Blo 770335 2930033 := bstep (se 2 (by rfl) ⟨1098762, by rfl⟩ : syracuseStep 2930033 = 2197525) B2197525
theorem B1160561 : Blo 770335 1160561 := bstep (se 2 (by rfl) ⟨435210, by rfl⟩ : syracuseStep 1160561 = 870421) B870421
theorem B1160579 : Blo 770335 1160579 := bstep (se 1 (by rfl) ⟨870434, by rfl⟩ : syracuseStep 1160579 = 1740869) B1740869
theorem B1160609 : Blo 770335 1160609 := bstep (se 2 (by rfl) ⟨435228, by rfl⟩ : syracuseStep 1160609 = 870457) B870457
theorem B1160627 : Blo 770335 1160627 := bstep (se 1 (by rfl) ⟨870470, by rfl⟩ : syracuseStep 1160627 = 1740941) B1740941
theorem B1652177 : Blo 770335 1652177 := bstep (se 2 (by rfl) ⟨619566, by rfl⟩ : syracuseStep 1652177 = 1239133) B1239133
theorem B1160657 : Blo 770335 1160657 := bstep (se 2 (by rfl) ⟨435246, by rfl⟩ : syracuseStep 1160657 = 870493) B870493
theorem B1160675 : Blo 770335 1160675 := bstep (se 1 (by rfl) ⟨870506, by rfl⟩ : syracuseStep 1160675 = 1741013) B1741013
theorem B1160705 : Blo 770335 1160705 := bstep (se 2 (by rfl) ⟨435264, by rfl⟩ : syracuseStep 1160705 = 870529) B870529
theorem B1160723 : Blo 770335 1160723 := bstep (se 1 (by rfl) ⟨870542, by rfl⟩ : syracuseStep 1160723 = 1741085) B1741085
theorem B1160753 : Blo 770335 1160753 := bstep (se 2 (by rfl) ⟨435282, by rfl⟩ : syracuseStep 1160753 = 870565) B870565
theorem B1160771 : Blo 770335 1160771 := bstep (se 1 (by rfl) ⟨870578, by rfl⟩ : syracuseStep 1160771 = 1741157) B1741157
theorem B1160801 : Blo 770335 1160801 := bstep (se 2 (by rfl) ⟨435300, by rfl⟩ : syracuseStep 1160801 = 870601) B870601
theorem B1160819 : Blo 770335 1160819 := bstep (se 1 (by rfl) ⟨870614, by rfl⟩ : syracuseStep 1160819 = 1741229) B1741229
theorem B2602637 : Blo 770335 2602637 := bstep (se 3 (by rfl) ⟨487994, by rfl⟩ : syracuseStep 2602637 = 975989) B975989
theorem B1160849 : Blo 770335 1160849 := bstep (se 2 (by rfl) ⟨435318, by rfl⟩ : syracuseStep 1160849 = 870637) B870637
theorem B1160867 : Blo 770335 1160867 := bstep (se 1 (by rfl) ⟨870650, by rfl⟩ : syracuseStep 1160867 = 1741301) B1741301
theorem B1160897 : Blo 770335 1160897 := bstep (se 2 (by rfl) ⟨435336, by rfl⟩ : syracuseStep 1160897 = 870673) B870673
theorem B2602691 : Blo 770335 2602691 := bstep (se 1 (by rfl) ⟨1952018, by rfl⟩ : syracuseStep 2602691 = 3904037) B3904037
theorem B1160915 : Blo 770335 1160915 := bstep (se 1 (by rfl) ⟨870686, by rfl⟩ : syracuseStep 1160915 = 1741373) B1741373
theorem B1160945 : Blo 770335 1160945 := bstep (se 2 (by rfl) ⟨435354, by rfl⟩ : syracuseStep 1160945 = 870709) B870709
theorem B1160963 : Blo 770335 1160963 := bstep (se 1 (by rfl) ⟨870722, by rfl⟩ : syracuseStep 1160963 = 1741445) B1741445
theorem B1160993 : Blo 770335 1160993 := bstep (se 2 (by rfl) ⟨435372, by rfl⟩ : syracuseStep 1160993 = 870745) B870745
theorem B1161011 : Blo 770335 1161011 := bstep (se 1 (by rfl) ⟨870758, by rfl⟩ : syracuseStep 1161011 = 1741517) B1741517
theorem B1161041 : Blo 770335 1161041 := bstep (se 2 (by rfl) ⟨435390, by rfl⟩ : syracuseStep 1161041 = 870781) B870781
theorem B1161059 : Blo 770335 1161059 := bstep (se 1 (by rfl) ⟨870794, by rfl⟩ : syracuseStep 1161059 = 1741589) B1741589
theorem B1161089 : Blo 770335 1161089 := bstep (se 2 (by rfl) ⟨435408, by rfl⟩ : syracuseStep 1161089 = 870817) B870817
theorem B1161107 : Blo 770335 1161107 := bstep (se 1 (by rfl) ⟨870830, by rfl⟩ : syracuseStep 1161107 = 1741661) B1741661
theorem B1161137 : Blo 770335 1161137 := bstep (se 2 (by rfl) ⟨435426, by rfl⟩ : syracuseStep 1161137 = 870853) B870853
theorem B1161155 : Blo 770335 1161155 := bstep (se 1 (by rfl) ⟨870866, by rfl⟩ : syracuseStep 1161155 = 1741733) B1741733
theorem B5027789 : Blo 770335 5027789 := bstep (se 3 (by rfl) ⟨942710, by rfl⟩ : syracuseStep 5027789 = 1885421) B1885421
theorem B2602961 : Blo 770335 2602961 := bstep (se 2 (by rfl) ⟨976110, by rfl⟩ : syracuseStep 2602961 = 1952221) B1952221
theorem B1161185 : Blo 770335 1161185 := bstep (se 2 (by rfl) ⟨435444, by rfl⟩ : syracuseStep 1161185 = 870889) B870889
theorem B1161203 : Blo 770335 1161203 := bstep (se 1 (by rfl) ⟨870902, by rfl⟩ : syracuseStep 1161203 = 1741805) B1741805
theorem B2930701 : Blo 770335 2930701 := bstep (se 3 (by rfl) ⟨549506, by rfl⟩ : syracuseStep 2930701 = 1099013) B1099013
theorem B1161233 : Blo 770335 1161233 := bstep (se 2 (by rfl) ⟨435462, by rfl⟩ : syracuseStep 1161233 = 870925) B870925
theorem B1161251 : Blo 770335 1161251 := bstep (se 1 (by rfl) ⟨870938, by rfl⟩ : syracuseStep 1161251 = 1741877) B1741877
theorem B2504753 : Blo 770335 2504753 := bstep (se 2 (by rfl) ⟨939282, by rfl⟩ : syracuseStep 2504753 = 1878565) B1878565
theorem B35665973 : Blo 770335 35665973 := bstep (se 5 (by rfl) ⟨1671842, by rfl⟩ : syracuseStep 35665973 = 3343685) B3343685
theorem B1161281 : Blo 770335 1161281 := bstep (se 2 (by rfl) ⟨435480, by rfl⟩ : syracuseStep 1161281 = 870961) B870961
theorem B1161299 : Blo 770335 1161299 := bstep (se 1 (by rfl) ⟨870974, by rfl⟩ : syracuseStep 1161299 = 1741949) B1741949
theorem B1161329 : Blo 770335 1161329 := bstep (se 2 (by rfl) ⟨435498, by rfl⟩ : syracuseStep 1161329 = 870997) B870997
theorem B1161347 : Blo 770335 1161347 := bstep (se 1 (by rfl) ⟨871010, by rfl⟩ : syracuseStep 1161347 = 1742021) B1742021
theorem B1161377 : Blo 770335 1161377 := bstep (se 2 (by rfl) ⟨435516, by rfl⟩ : syracuseStep 1161377 = 871033) B871033
theorem B3291299 : Blo 770335 3291299 := bstep (se 1 (by rfl) ⟨2468474, by rfl⟩ : syracuseStep 3291299 = 4936949) B4936949
theorem B1161395 : Blo 770335 1161395 := bstep (se 1 (by rfl) ⟨871046, by rfl⟩ : syracuseStep 1161395 = 1742093) B1742093
theorem B1161425 : Blo 770335 1161425 := bstep (se 2 (by rfl) ⟨435534, by rfl⟩ : syracuseStep 1161425 = 871069) B871069
theorem B1161443 : Blo 770335 1161443 := bstep (se 1 (by rfl) ⟨871082, by rfl⟩ : syracuseStep 1161443 = 1742165) B1742165
theorem B1161473 : Blo 770335 1161473 := bstep (se 2 (by rfl) ⟨435552, by rfl⟩ : syracuseStep 1161473 = 871105) B871105
theorem B1161491 : Blo 770335 1161491 := bstep (se 1 (by rfl) ⟨871118, by rfl⟩ : syracuseStep 1161491 = 1742237) B1742237
theorem B866659 : Blo 770335 866659 := bstep (se 1 (by rfl) ⟨649994, by rfl⟩ : syracuseStep 866659 = 1299989) B1299989
theorem B2603501 : Blo 770335 2603501 := bstep (se 3 (by rfl) ⟨488156, by rfl⟩ : syracuseStep 2603501 = 976313) B976313
theorem B866803 : Blo 770335 866803 := bstep (se 1 (by rfl) ⟨650102, by rfl⟩ : syracuseStep 866803 = 1300205) B1300205
theorem B2603555 : Blo 770335 2603555 := bstep (se 1 (by rfl) ⟨1952666, by rfl⟩ : syracuseStep 2603555 = 3905333) B3905333
theorem B1391185 : Blo 770335 1391185 := bstep (se 2 (by rfl) ⟨521694, by rfl⟩ : syracuseStep 1391185 = 1043389) B1043389
theorem B866947 : Blo 770335 866947 := bstep (se 1 (by rfl) ⟨650210, by rfl⟩ : syracuseStep 866947 = 1300421) B1300421
theorem B8043235 : Blo 770335 8043235 := bstep (se 1 (by rfl) ⟨6032426, by rfl⟩ : syracuseStep 8043235 = 12064853) B12064853
theorem B3717859 : Blo 770335 3717859 := bstep (se 1 (by rfl) ⟨2788394, by rfl⟩ : syracuseStep 3717859 = 5576789) B5576789
theorem B1653475 : Blo 770335 1653475 := bstep (se 1 (by rfl) ⟨1240106, by rfl⟩ : syracuseStep 1653475 = 2480213) B2480213
theorem B867091 : Blo 770335 867091 := bstep (se 1 (by rfl) ⟨650318, by rfl⟩ : syracuseStep 867091 = 1300637) B1300637
theorem B2931491 : Blo 770335 2931491 := bstep (se 1 (by rfl) ⟨2198618, by rfl⟩ : syracuseStep 2931491 = 4397237) B4397237
theorem B2603825 : Blo 770335 2603825 := bstep (se 2 (by rfl) ⟨976434, by rfl⟩ : syracuseStep 2603825 = 1952869) B1952869
theorem B867235 : Blo 770335 867235 := bstep (se 1 (by rfl) ⟨650426, by rfl⟩ : syracuseStep 867235 = 1300853) B1300853
theorem B867379 : Blo 770335 867379 := bstep (se 1 (by rfl) ⟨650534, by rfl⟩ : syracuseStep 867379 = 1301069) B1301069
theorem B2473037 : Blo 770335 2473037 := bstep (se 3 (by rfl) ⟨463694, by rfl⟩ : syracuseStep 2473037 = 927389) B927389
theorem B1096849 : Blo 770335 1096849 := bstep (se 2 (by rfl) ⟨411318, by rfl⟩ : syracuseStep 1096849 = 822637) B822637
theorem B2636945 : Blo 770335 2636945 := bstep (se 2 (by rfl) ⟨988854, by rfl⟩ : syracuseStep 2636945 = 1977709) B1977709
theorem B867523 : Blo 770335 867523 := bstep (se 1 (by rfl) ⟨650642, by rfl⟩ : syracuseStep 867523 = 1301285) B1301285
theorem B1981649 : Blo 770335 1981649 := bstep (se 2 (by rfl) ⟨743118, by rfl⟩ : syracuseStep 1981649 = 1486237) B1486237
theorem B2604365 : Blo 770335 2604365 := bstep (se 3 (by rfl) ⟨488318, by rfl⟩ : syracuseStep 2604365 = 976637) B976637
theorem B867667 : Blo 770335 867667 := bstep (se 1 (by rfl) ⟨650750, by rfl⟩ : syracuseStep 867667 = 1301501) B1301501
theorem B2604419 : Blo 770335 2604419 := bstep (se 1 (by rfl) ⟨1953314, by rfl⟩ : syracuseStep 2604419 = 3906629) B3906629
theorem B4406669 : Blo 770335 4406669 := bstep (se 3 (by rfl) ⟨826250, by rfl⟩ : syracuseStep 4406669 = 1652501) B1652501
theorem B2932145 : Blo 770335 2932145 := bstep (se 2 (by rfl) ⟨1099554, by rfl⟩ : syracuseStep 2932145 = 2199109) B2199109
theorem B7421381 : Blo 770335 7421381 := bstep (se 4 (by rfl) ⟨695754, by rfl⟩ : syracuseStep 7421381 = 1391509) B1391509
theorem B867811 : Blo 770335 867811 := bstep (se 1 (by rfl) ⟨650858, by rfl⟩ : syracuseStep 867811 = 1301717) B1301717
theorem B3915377 : Blo 770335 3915377 := bstep (se 2 (by rfl) ⟨1468266, by rfl⟩ : syracuseStep 3915377 = 2936533) B2936533
theorem B867955 : Blo 770335 867955 := bstep (se 1 (by rfl) ⟨650966, by rfl⟩ : syracuseStep 867955 = 1301933) B1301933
theorem B2604689 : Blo 770335 2604689 := bstep (se 2 (by rfl) ⟨976758, by rfl⟩ : syracuseStep 2604689 = 1953517) B1953517
theorem B868099 : Blo 770335 868099 := bstep (se 1 (by rfl) ⟨651074, by rfl⟩ : syracuseStep 868099 = 1302149) B1302149
theorem B1097555 : Blo 770335 1097555 := bstep (se 1 (by rfl) ⟨823166, by rfl⟩ : syracuseStep 1097555 = 1646333) B1646333
theorem B868243 : Blo 770335 868243 := bstep (se 1 (by rfl) ⟨651182, by rfl⟩ : syracuseStep 868243 = 1302365) B1302365
theorem B1392547 : Blo 770335 1392547 := bstep (se 1 (by rfl) ⟨1044410, by rfl⟩ : syracuseStep 1392547 = 2088821) B2088821
theorem B1392611 : Blo 770335 1392611 := bstep (se 1 (by rfl) ⟨1044458, by rfl⟩ : syracuseStep 1392611 = 2088917) B2088917
theorem B868387 : Blo 770335 868387 := bstep (se 1 (by rfl) ⟨651290, by rfl⟩ : syracuseStep 868387 = 1302581) B1302581
theorem B1392785 : Blo 770335 1392785 := bstep (se 2 (by rfl) ⟨522294, by rfl⟩ : syracuseStep 1392785 = 1044589) B1044589
theorem B2605229 : Blo 770335 2605229 := bstep (se 3 (by rfl) ⟨488480, by rfl⟩ : syracuseStep 2605229 = 976961) B976961
theorem B868531 : Blo 770335 868531 := bstep (se 1 (by rfl) ⟨651398, by rfl⟩ : syracuseStep 868531 = 1302797) B1302797
theorem B2605283 : Blo 770335 2605283 := bstep (se 1 (by rfl) ⟨1953962, by rfl⟩ : syracuseStep 2605283 = 3907925) B3907925
theorem B770339 : Blo 770335 770339 := bstep (se 1 (by rfl) ⟨577754, by rfl⟩ : syracuseStep 770339 = 1155509) B1155509
theorem B770355 : Blo 770335 770355 := bstep (se 1 (by rfl) ⟨577766, by rfl⟩ : syracuseStep 770355 = 1155533) B1155533
theorem B770371 : Blo 770335 770371 := bstep (se 1 (by rfl) ⟨577778, by rfl⟩ : syracuseStep 770371 = 1155557) B1155557
theorem B868675 : Blo 770335 868675 := bstep (se 1 (by rfl) ⟨651506, by rfl⟩ : syracuseStep 868675 = 1303013) B1303013
theorem B2474317 : Blo 770335 2474317 := bstep (se 3 (by rfl) ⟨463934, by rfl⟩ : syracuseStep 2474317 = 927869) B927869
theorem B770387 : Blo 770335 770387 := bstep (se 1 (by rfl) ⟨577790, by rfl⟩ : syracuseStep 770387 = 1155581) B1155581
theorem B770403 : Blo 770335 770403 := bstep (se 1 (by rfl) ⟨577802, by rfl⟩ : syracuseStep 770403 = 1155605) B1155605
theorem B1950065 : Blo 770335 1950065 := bstep (se 2 (by rfl) ⟨731274, by rfl⟩ : syracuseStep 1950065 = 1462549) B1462549
theorem B770419 : Blo 770335 770419 := bstep (se 1 (by rfl) ⟨577814, by rfl⟩ : syracuseStep 770419 = 1155629) B1155629
theorem B770435 : Blo 770335 770435 := bstep (se 1 (by rfl) ⟨577826, by rfl⟩ : syracuseStep 770435 = 1155653) B1155653
theorem B770451 : Blo 770335 770451 := bstep (se 1 (by rfl) ⟨577838, by rfl⟩ : syracuseStep 770451 = 1155677) B1155677
theorem B1950115 : Blo 770335 1950115 := bstep (se 1 (by rfl) ⟨1462586, by rfl⟩ : syracuseStep 1950115 = 2925173) B2925173
theorem B770467 : Blo 770335 770467 := bstep (se 1 (by rfl) ⟨577850, by rfl⟩ : syracuseStep 770467 = 1155701) B1155701
theorem B770483 : Blo 770335 770483 := bstep (se 1 (by rfl) ⟨577862, by rfl⟩ : syracuseStep 770483 = 1155725) B1155725
theorem B10011061 : Blo 770335 10011061 := bstep (se 5 (by rfl) ⟨469268, by rfl⟩ : syracuseStep 10011061 = 938537) B938537
theorem B770499 : Blo 770335 770499 := bstep (se 1 (by rfl) ⟨577874, by rfl⟩ : syracuseStep 770499 = 1155749) B1155749
theorem B1098193 : Blo 770335 1098193 := bstep (se 2 (by rfl) ⟨411822, by rfl⟩ : syracuseStep 1098193 = 823645) B823645
theorem B770515 : Blo 770335 770515 := bstep (se 1 (by rfl) ⟨577886, by rfl⟩ : syracuseStep 770515 = 1155773) B1155773
theorem B868819 : Blo 770335 868819 := bstep (se 1 (by rfl) ⟨651614, by rfl⟩ : syracuseStep 868819 = 1303229) B1303229
theorem B770531 : Blo 770335 770531 := bstep (se 1 (by rfl) ⟨577898, by rfl⟩ : syracuseStep 770531 = 1155797) B1155797
theorem B2605553 : Blo 770335 2605553 := bstep (se 2 (by rfl) ⟨977082, by rfl⟩ : syracuseStep 2605553 = 1954165) B1954165
theorem B770547 : Blo 770335 770547 := bstep (se 1 (by rfl) ⟨577910, by rfl⟩ : syracuseStep 770547 = 1155821) B1155821
theorem B770563 : Blo 770335 770563 := bstep (se 1 (by rfl) ⟨577922, by rfl⟩ : syracuseStep 770563 = 1155845) B1155845
theorem B770579 : Blo 770335 770579 := bstep (se 1 (by rfl) ⟨577934, by rfl⟩ : syracuseStep 770579 = 1155869) B1155869
theorem B770595 : Blo 770335 770595 := bstep (se 1 (by rfl) ⟨577946, by rfl⟩ : syracuseStep 770595 = 1155893) B1155893
theorem B1950257 : Blo 770335 1950257 := bstep (se 2 (by rfl) ⟨731346, by rfl⟩ : syracuseStep 1950257 = 1462693) B1462693
theorem B3129905 : Blo 770335 3129905 := bstep (se 2 (by rfl) ⟨1173714, by rfl⟩ : syracuseStep 3129905 = 2347429) B2347429
theorem B770611 : Blo 770335 770611 := bstep (se 1 (by rfl) ⟨577958, by rfl⟩ : syracuseStep 770611 = 1155917) B1155917
theorem B770627 : Blo 770335 770627 := bstep (se 1 (by rfl) ⟨577970, by rfl⟩ : syracuseStep 770627 = 1155941) B1155941
theorem B1098307 : Blo 770335 1098307 := bstep (se 1 (by rfl) ⟨823730, by rfl⟩ : syracuseStep 1098307 = 1647461) B1647461
theorem B770643 : Blo 770335 770643 := bstep (se 1 (by rfl) ⟨577982, by rfl⟩ : syracuseStep 770643 = 1155965) B1155965
theorem B770659 : Blo 770335 770659 := bstep (se 1 (by rfl) ⟨577994, by rfl⟩ : syracuseStep 770659 = 1155989) B1155989
theorem B868963 : Blo 770335 868963 := bstep (se 1 (by rfl) ⟨651722, by rfl⟩ : syracuseStep 868963 = 1303445) B1303445
theorem B770675 : Blo 770335 770675 := bstep (se 1 (by rfl) ⟨578006, by rfl⟩ : syracuseStep 770675 = 1156013) B1156013
theorem B770691 : Blo 770335 770691 := bstep (se 1 (by rfl) ⟨578018, by rfl⟩ : syracuseStep 770691 = 1156037) B1156037
theorem B4178573 : Blo 770335 4178573 := bstep (se 3 (by rfl) ⟨783482, by rfl⟩ : syracuseStep 4178573 = 1566965) B1566965
theorem B770707 : Blo 770335 770707 := bstep (se 1 (by rfl) ⟨578030, by rfl⟩ : syracuseStep 770707 = 1156061) B1156061
theorem B770723 : Blo 770335 770723 := bstep (se 1 (by rfl) ⟨578042, by rfl⟩ : syracuseStep 770723 = 1156085) B1156085
theorem B770739 : Blo 770335 770739 := bstep (se 1 (by rfl) ⟨578054, by rfl⟩ : syracuseStep 770739 = 1156109) B1156109
theorem B770755 : Blo 770335 770755 := bstep (se 1 (by rfl) ⟨578066, by rfl⟩ : syracuseStep 770755 = 1156133) B1156133
theorem B770771 : Blo 770335 770771 := bstep (se 1 (by rfl) ⟨578078, by rfl⟩ : syracuseStep 770771 = 1156157) B1156157
theorem B770787 : Blo 770335 770787 := bstep (se 1 (by rfl) ⟨578090, by rfl⟩ : syracuseStep 770787 = 1156181) B1156181
theorem B4702961 : Blo 770335 4702961 := bstep (se 2 (by rfl) ⟨1763610, by rfl⟩ : syracuseStep 4702961 = 3527221) B3527221
theorem B770803 : Blo 770335 770803 := bstep (se 1 (by rfl) ⟨578102, by rfl⟩ : syracuseStep 770803 = 1156205) B1156205
theorem B869107 : Blo 770335 869107 := bstep (se 1 (by rfl) ⟨651830, by rfl⟩ : syracuseStep 869107 = 1303661) B1303661
theorem B770819 : Blo 770335 770819 := bstep (se 1 (by rfl) ⟨578114, by rfl⟩ : syracuseStep 770819 = 1156229) B1156229
theorem B770835 : Blo 770335 770835 := bstep (se 1 (by rfl) ⟨578126, by rfl⟩ : syracuseStep 770835 = 1156253) B1156253
theorem B770851 : Blo 770335 770851 := bstep (se 1 (by rfl) ⟨578138, by rfl⟩ : syracuseStep 770851 = 1156277) B1156277
theorem B770867 : Blo 770335 770867 := bstep (se 1 (by rfl) ⟨578150, by rfl⟩ : syracuseStep 770867 = 1156301) B1156301
theorem B8799029 : Blo 770335 8799029 := bstep (se 5 (by rfl) ⟨412454, by rfl⟩ : syracuseStep 8799029 = 824909) B824909
theorem B770883 : Blo 770335 770883 := bstep (se 1 (by rfl) ⟨578162, by rfl⟩ : syracuseStep 770883 = 1156325) B1156325
theorem B2474819 : Blo 770335 2474819 := bstep (se 1 (by rfl) ⟨1856114, by rfl⟩ : syracuseStep 2474819 = 3712229) B3712229
theorem B770899 : Blo 770335 770899 := bstep (se 1 (by rfl) ⟨578174, by rfl⟩ : syracuseStep 770899 = 1156349) B1156349
theorem B770915 : Blo 770335 770915 := bstep (se 1 (by rfl) ⟨578186, by rfl⟩ : syracuseStep 770915 = 1156373) B1156373
theorem B2933603 : Blo 770335 2933603 := bstep (se 1 (by rfl) ⟨2200202, by rfl⟩ : syracuseStep 2933603 = 4400405) B4400405
theorem B1885027 : Blo 770335 1885027 := bstep (se 1 (by rfl) ⟨1413770, by rfl⟩ : syracuseStep 1885027 = 2827541) B2827541
theorem B2933617 : Blo 770335 2933617 := bstep (se 2 (by rfl) ⟨1100106, by rfl⟩ : syracuseStep 2933617 = 2200213) B2200213
theorem B770931 : Blo 770335 770931 := bstep (se 1 (by rfl) ⟨578198, by rfl⟩ : syracuseStep 770931 = 1156397) B1156397
theorem B770947 : Blo 770335 770947 := bstep (se 1 (by rfl) ⟨578210, by rfl⟩ : syracuseStep 770947 = 1156421) B1156421
theorem B869251 : Blo 770335 869251 := bstep (se 1 (by rfl) ⟨651938, by rfl⟩ : syracuseStep 869251 = 1303877) B1303877
theorem B770963 : Blo 770335 770963 := bstep (se 1 (by rfl) ⟨578222, by rfl⟩ : syracuseStep 770963 = 1156445) B1156445
theorem B770979 : Blo 770335 770979 := bstep (se 1 (by rfl) ⟨578234, by rfl⟩ : syracuseStep 770979 = 1156469) B1156469
theorem B770995 : Blo 770335 770995 := bstep (se 1 (by rfl) ⟨578246, by rfl⟩ : syracuseStep 770995 = 1156493) B1156493
theorem B1852355 : Blo 770335 1852355 := bstep (se 1 (by rfl) ⟨1389266, by rfl⟩ : syracuseStep 1852355 = 2778533) B2778533
theorem B771011 : Blo 770335 771011 := bstep (se 1 (by rfl) ⟨578258, by rfl⟩ : syracuseStep 771011 = 1156517) B1156517
theorem B771027 : Blo 770335 771027 := bstep (se 1 (by rfl) ⟨578270, by rfl⟩ : syracuseStep 771027 = 1156541) B1156541
theorem B771043 : Blo 770335 771043 := bstep (se 1 (by rfl) ⟨578282, by rfl⟩ : syracuseStep 771043 = 1156565) B1156565
theorem B771059 : Blo 770335 771059 := bstep (se 1 (by rfl) ⟨578294, by rfl⟩ : syracuseStep 771059 = 1156589) B1156589
theorem B771075 : Blo 770335 771075 := bstep (se 1 (by rfl) ⟨578306, by rfl⟩ : syracuseStep 771075 = 1156613) B1156613
theorem B836611 : Blo 770335 836611 := bstep (se 1 (by rfl) ⟨627458, by rfl⟩ : syracuseStep 836611 = 1254917) B1254917
theorem B2606093 : Blo 770335 2606093 := bstep (se 3 (by rfl) ⟨488642, by rfl⟩ : syracuseStep 2606093 = 977285) B977285
theorem B1852433 : Blo 770335 1852433 := bstep (se 2 (by rfl) ⟨694662, by rfl⟩ : syracuseStep 1852433 = 1389325) B1389325
theorem B771091 : Blo 770335 771091 := bstep (se 1 (by rfl) ⟨578318, by rfl⟩ : syracuseStep 771091 = 1156637) B1156637
theorem B869395 : Blo 770335 869395 := bstep (se 1 (by rfl) ⟨652046, by rfl⟩ : syracuseStep 869395 = 1304093) B1304093
theorem B771107 : Blo 770335 771107 := bstep (se 1 (by rfl) ⟨578330, by rfl⟩ : syracuseStep 771107 = 1156661) B1156661
theorem B3916835 : Blo 770335 3916835 := bstep (se 1 (by rfl) ⟨2937626, by rfl⟩ : syracuseStep 3916835 = 5875253) B5875253
theorem B771123 : Blo 770335 771123 := bstep (se 1 (by rfl) ⟨578342, by rfl⟩ : syracuseStep 771123 = 1156685) B1156685
theorem B771139 : Blo 770335 771139 := bstep (se 1 (by rfl) ⟨578354, by rfl⟩ : syracuseStep 771139 = 1156709) B1156709
theorem B2606147 : Blo 770335 2606147 := bstep (se 1 (by rfl) ⟨1954610, by rfl⟩ : syracuseStep 2606147 = 3909221) B3909221
theorem B771155 : Blo 770335 771155 := bstep (se 1 (by rfl) ⟨578366, by rfl⟩ : syracuseStep 771155 = 1156733) B1156733
theorem B771171 : Blo 770335 771171 := bstep (se 1 (by rfl) ⟨578378, by rfl⟩ : syracuseStep 771171 = 1156757) B1156757
theorem B771187 : Blo 770335 771187 := bstep (se 1 (by rfl) ⟨578390, by rfl⟩ : syracuseStep 771187 = 1156781) B1156781
theorem B771203 : Blo 770335 771203 := bstep (se 1 (by rfl) ⟨578402, by rfl⟩ : syracuseStep 771203 = 1156805) B1156805
theorem B771219 : Blo 770335 771219 := bstep (se 1 (by rfl) ⟨578414, by rfl⟩ : syracuseStep 771219 = 1156829) B1156829
theorem B771235 : Blo 770335 771235 := bstep (se 1 (by rfl) ⟨578426, by rfl⟩ : syracuseStep 771235 = 1156853) B1156853
theorem B869539 : Blo 770335 869539 := bstep (se 1 (by rfl) ⟨652154, by rfl⟩ : syracuseStep 869539 = 1304309) B1304309
theorem B771251 : Blo 770335 771251 := bstep (se 1 (by rfl) ⟨578438, by rfl⟩ : syracuseStep 771251 = 1156877) B1156877
theorem B771267 : Blo 770335 771267 := bstep (se 1 (by rfl) ⟨578450, by rfl⟩ : syracuseStep 771267 = 1156901) B1156901
theorem B1852625 : Blo 770335 1852625 := bstep (se 2 (by rfl) ⟨694734, by rfl⟩ : syracuseStep 1852625 = 1389469) B1389469
theorem B771283 : Blo 770335 771283 := bstep (se 1 (by rfl) ⟨578462, by rfl⟩ : syracuseStep 771283 = 1156925) B1156925
theorem B771299 : Blo 770335 771299 := bstep (se 1 (by rfl) ⟨578474, by rfl⟩ : syracuseStep 771299 = 1156949) B1156949
theorem B771315 : Blo 770335 771315 := bstep (se 1 (by rfl) ⟨578486, by rfl⟩ : syracuseStep 771315 = 1156973) B1156973
theorem B771331 : Blo 770335 771331 := bstep (se 1 (by rfl) ⟨578498, by rfl⟩ : syracuseStep 771331 = 1156997) B1156997
theorem B771347 : Blo 770335 771347 := bstep (se 1 (by rfl) ⟨578510, by rfl⟩ : syracuseStep 771347 = 1157021) B1157021
theorem B771363 : Blo 770335 771363 := bstep (se 1 (by rfl) ⟨578522, by rfl⟩ : syracuseStep 771363 = 1157045) B1157045
theorem B771379 : Blo 770335 771379 := bstep (se 1 (by rfl) ⟨578534, by rfl⟩ : syracuseStep 771379 = 1157069) B1157069
theorem B869683 : Blo 770335 869683 := bstep (se 1 (by rfl) ⟨652262, by rfl⟩ : syracuseStep 869683 = 1304525) B1304525
theorem B771395 : Blo 770335 771395 := bstep (se 1 (by rfl) ⟨578546, by rfl⟩ : syracuseStep 771395 = 1157093) B1157093
theorem B2606417 : Blo 770335 2606417 := bstep (se 2 (by rfl) ⟨977406, by rfl⟩ : syracuseStep 2606417 = 1954813) B1954813
theorem B771411 : Blo 770335 771411 := bstep (se 1 (by rfl) ⟨578558, by rfl⟩ : syracuseStep 771411 = 1157117) B1157117
theorem B5850467 : Blo 770335 5850467 := bstep (se 1 (by rfl) ⟨4387850, by rfl⟩ : syracuseStep 5850467 = 8775701) B8775701
theorem B771427 : Blo 770335 771427 := bstep (se 1 (by rfl) ⟨578570, by rfl⟩ : syracuseStep 771427 = 1157141) B1157141
theorem B771443 : Blo 770335 771443 := bstep (se 1 (by rfl) ⟨578582, by rfl⟩ : syracuseStep 771443 = 1157165) B1157165
theorem B771459 : Blo 770335 771459 := bstep (se 1 (by rfl) ⟨578594, by rfl⟩ : syracuseStep 771459 = 1157189) B1157189
theorem B771475 : Blo 770335 771475 := bstep (se 1 (by rfl) ⟨578606, by rfl⟩ : syracuseStep 771475 = 1157213) B1157213
theorem B771491 : Blo 770335 771491 := bstep (se 1 (by rfl) ⟨578618, by rfl⟩ : syracuseStep 771491 = 1157237) B1157237
theorem B771507 : Blo 770335 771507 := bstep (se 1 (by rfl) ⟨578630, by rfl⟩ : syracuseStep 771507 = 1157261) B1157261
theorem B771523 : Blo 770335 771523 := bstep (se 1 (by rfl) ⟨578642, by rfl⟩ : syracuseStep 771523 = 1157285) B1157285
theorem B869827 : Blo 770335 869827 := bstep (se 1 (by rfl) ⟨652370, by rfl⟩ : syracuseStep 869827 = 1304741) B1304741
theorem B771539 : Blo 770335 771539 := bstep (se 1 (by rfl) ⟨578654, by rfl⟩ : syracuseStep 771539 = 1157309) B1157309
theorem B771555 : Blo 770335 771555 := bstep (se 1 (by rfl) ⟨578666, by rfl⟩ : syracuseStep 771555 = 1157333) B1157333
theorem B1852913 : Blo 770335 1852913 := bstep (se 2 (by rfl) ⟨694842, by rfl⟩ : syracuseStep 1852913 = 1389685) B1389685
theorem B771571 : Blo 770335 771571 := bstep (se 1 (by rfl) ⟨578678, by rfl⟩ : syracuseStep 771571 = 1157357) B1157357
theorem B771587 : Blo 770335 771587 := bstep (se 1 (by rfl) ⟨578690, by rfl⟩ : syracuseStep 771587 = 1157381) B1157381
theorem B1951249 : Blo 770335 1951249 := bstep (se 2 (by rfl) ⟨731718, by rfl⟩ : syracuseStep 1951249 = 1463437) B1463437
theorem B771603 : Blo 770335 771603 := bstep (se 1 (by rfl) ⟨578702, by rfl⟩ : syracuseStep 771603 = 1157405) B1157405
theorem B771619 : Blo 770335 771619 := bstep (se 1 (by rfl) ⟨578714, by rfl⟩ : syracuseStep 771619 = 1157429) B1157429
theorem B771635 : Blo 770335 771635 := bstep (se 1 (by rfl) ⟨578726, by rfl⟩ : syracuseStep 771635 = 1157453) B1157453
theorem B771651 : Blo 770335 771651 := bstep (se 1 (by rfl) ⟨578738, by rfl⟩ : syracuseStep 771651 = 1157477) B1157477
theorem B4408901 : Blo 770335 4408901 := bstep (se 4 (by rfl) ⟨413334, by rfl⟩ : syracuseStep 4408901 = 826669) B826669
theorem B771667 : Blo 770335 771667 := bstep (se 1 (by rfl) ⟨578750, by rfl⟩ : syracuseStep 771667 = 1157501) B1157501
theorem B869971 : Blo 770335 869971 := bstep (se 1 (by rfl) ⟨652478, by rfl⟩ : syracuseStep 869971 = 1304957) B1304957
theorem B771683 : Blo 770335 771683 := bstep (se 1 (by rfl) ⟨578762, by rfl⟩ : syracuseStep 771683 = 1157525) B1157525
theorem B771699 : Blo 770335 771699 := bstep (se 1 (by rfl) ⟨578774, by rfl⟩ : syracuseStep 771699 = 1157549) B1157549
theorem B771715 : Blo 770335 771715 := bstep (se 1 (by rfl) ⟨578786, by rfl⟩ : syracuseStep 771715 = 1157573) B1157573
theorem B771731 : Blo 770335 771731 := bstep (se 1 (by rfl) ⟨578798, by rfl⟩ : syracuseStep 771731 = 1157597) B1157597
theorem B771747 : Blo 770335 771747 := bstep (se 1 (by rfl) ⟨578810, by rfl⟩ : syracuseStep 771747 = 1157621) B1157621
theorem B771763 : Blo 770335 771763 := bstep (se 1 (by rfl) ⟨578822, by rfl⟩ : syracuseStep 771763 = 1157645) B1157645
theorem B771779 : Blo 770335 771779 := bstep (se 1 (by rfl) ⟨578834, by rfl⟩ : syracuseStep 771779 = 1157669) B1157669
theorem B771795 : Blo 770335 771795 := bstep (se 1 (by rfl) ⟨578846, by rfl⟩ : syracuseStep 771795 = 1157693) B1157693
theorem B771811 : Blo 770335 771811 := bstep (se 1 (by rfl) ⟨578858, by rfl⟩ : syracuseStep 771811 = 1157717) B1157717
theorem B870115 : Blo 770335 870115 := bstep (se 1 (by rfl) ⟨652586, by rfl⟩ : syracuseStep 870115 = 1305173) B1305173
theorem B771827 : Blo 770335 771827 := bstep (se 1 (by rfl) ⟨578870, by rfl⟩ : syracuseStep 771827 = 1157741) B1157741
theorem B771843 : Blo 770335 771843 := bstep (se 1 (by rfl) ⟨578882, by rfl⟩ : syracuseStep 771843 = 1157765) B1157765
theorem B1984259 : Blo 770335 1984259 := bstep (se 1 (by rfl) ⟨1488194, by rfl⟩ : syracuseStep 1984259 = 2976389) B2976389
theorem B3294989 : Blo 770335 3294989 := bstep (se 3 (by rfl) ⟨617810, by rfl⟩ : syracuseStep 3294989 = 1235621) B1235621
theorem B5654285 : Blo 770335 5654285 := bstep (se 3 (by rfl) ⟨1060178, by rfl⟩ : syracuseStep 5654285 = 2120357) B2120357
theorem B771859 : Blo 770335 771859 := bstep (se 1 (by rfl) ⟨578894, by rfl⟩ : syracuseStep 771859 = 1157789) B1157789
theorem B1951523 : Blo 770335 1951523 := bstep (se 1 (by rfl) ⟨1463642, by rfl⟩ : syracuseStep 1951523 = 2927285) B2927285
theorem B771875 : Blo 770335 771875 := bstep (se 1 (by rfl) ⟨578906, by rfl⟩ : syracuseStep 771875 = 1157813) B1157813
theorem B3295025 : Blo 770335 3295025 := bstep (se 2 (by rfl) ⟨1235634, by rfl⟩ : syracuseStep 3295025 = 2471269) B2471269
theorem B771891 : Blo 770335 771891 := bstep (se 1 (by rfl) ⟨578918, by rfl⟩ : syracuseStep 771891 = 1157837) B1157837
theorem B771907 : Blo 770335 771907 := bstep (se 1 (by rfl) ⟨578930, by rfl⟩ : syracuseStep 771907 = 1157861) B1157861
theorem B3917645 : Blo 770335 3917645 := bstep (se 3 (by rfl) ⟨734558, by rfl⟩ : syracuseStep 3917645 = 1469117) B1469117
theorem B771923 : Blo 770335 771923 := bstep (se 1 (by rfl) ⟨578942, by rfl⟩ : syracuseStep 771923 = 1157885) B1157885
theorem B771939 : Blo 770335 771939 := bstep (se 1 (by rfl) ⟨578954, by rfl⟩ : syracuseStep 771939 = 1157909) B1157909
theorem B2606957 : Blo 770335 2606957 := bstep (se 3 (by rfl) ⟨488804, by rfl⟩ : syracuseStep 2606957 = 977609) B977609
theorem B771955 : Blo 770335 771955 := bstep (se 1 (by rfl) ⟨578966, by rfl⟩ : syracuseStep 771955 = 1157933) B1157933
theorem B870259 : Blo 770335 870259 := bstep (se 1 (by rfl) ⟨652694, by rfl⟩ : syracuseStep 870259 = 1305389) B1305389
theorem B771971 : Blo 770335 771971 := bstep (se 1 (by rfl) ⟨578978, by rfl⟩ : syracuseStep 771971 = 1157957) B1157957
theorem B1099651 : Blo 770335 1099651 := bstep (se 1 (by rfl) ⟨824738, by rfl⟩ : syracuseStep 1099651 = 1649477) B1649477
theorem B771987 : Blo 770335 771987 := bstep (se 1 (by rfl) ⟨578990, by rfl⟩ : syracuseStep 771987 = 1157981) B1157981
theorem B772003 : Blo 770335 772003 := bstep (se 1 (by rfl) ⟨579002, by rfl⟩ : syracuseStep 772003 = 1158005) B1158005
theorem B2607011 : Blo 770335 2607011 := bstep (se 1 (by rfl) ⟨1955258, by rfl⟩ : syracuseStep 2607011 = 3910517) B3910517
theorem B772019 : Blo 770335 772019 := bstep (se 1 (by rfl) ⟨579014, by rfl⟩ : syracuseStep 772019 = 1158029) B1158029
theorem B772035 : Blo 770335 772035 := bstep (se 1 (by rfl) ⟨579026, by rfl⟩ : syracuseStep 772035 = 1158053) B1158053
theorem B772051 : Blo 770335 772051 := bstep (se 1 (by rfl) ⟨579038, by rfl⟩ : syracuseStep 772051 = 1158077) B1158077
theorem B12503011 : Blo 770335 12503011 := bstep (se 1 (by rfl) ⟨9377258, by rfl⟩ : syracuseStep 12503011 = 18754517) B18754517
theorem B1951715 : Blo 770335 1951715 := bstep (se 1 (by rfl) ⟨1463786, by rfl⟩ : syracuseStep 1951715 = 2927573) B2927573
theorem B772067 : Blo 770335 772067 := bstep (se 1 (by rfl) ⟨579050, by rfl⟩ : syracuseStep 772067 = 1158101) B1158101
theorem B772083 : Blo 770335 772083 := bstep (se 1 (by rfl) ⟨579062, by rfl⟩ : syracuseStep 772083 = 1158125) B1158125
theorem B772099 : Blo 770335 772099 := bstep (se 1 (by rfl) ⟨579074, by rfl⟩ : syracuseStep 772099 = 1158149) B1158149
theorem B870403 : Blo 770335 870403 := bstep (se 1 (by rfl) ⟨652802, by rfl⟩ : syracuseStep 870403 = 1305605) B1305605
theorem B772115 : Blo 770335 772115 := bstep (se 1 (by rfl) ⟨579086, by rfl⟩ : syracuseStep 772115 = 1158173) B1158173
theorem B772131 : Blo 770335 772131 := bstep (se 1 (by rfl) ⟨579098, by rfl⟩ : syracuseStep 772131 = 1158197) B1158197
theorem B772147 : Blo 770335 772147 := bstep (se 1 (by rfl) ⟨579110, by rfl⟩ : syracuseStep 772147 = 1158221) B1158221
theorem B772163 : Blo 770335 772163 := bstep (se 1 (by rfl) ⟨579122, by rfl⟩ : syracuseStep 772163 = 1158245) B1158245
theorem B772179 : Blo 770335 772179 := bstep (se 1 (by rfl) ⟨579134, by rfl⟩ : syracuseStep 772179 = 1158269) B1158269
theorem B772195 : Blo 770335 772195 := bstep (se 1 (by rfl) ⟨579146, by rfl⟩ : syracuseStep 772195 = 1158293) B1158293
theorem B772211 : Blo 770335 772211 := bstep (se 1 (by rfl) ⟨579158, by rfl⟩ : syracuseStep 772211 = 1158317) B1158317
theorem B772227 : Blo 770335 772227 := bstep (se 1 (by rfl) ⟨579170, by rfl⟩ : syracuseStep 772227 = 1158341) B1158341
theorem B2476163 : Blo 770335 2476163 := bstep (se 1 (by rfl) ⟨1857122, by rfl⟩ : syracuseStep 2476163 = 3714245) B3714245
theorem B772243 : Blo 770335 772243 := bstep (se 1 (by rfl) ⟨579182, by rfl⟩ : syracuseStep 772243 = 1158365) B1158365
theorem B870547 : Blo 770335 870547 := bstep (se 1 (by rfl) ⟨652910, by rfl⟩ : syracuseStep 870547 = 1305821) B1305821
theorem B772259 : Blo 770335 772259 := bstep (se 1 (by rfl) ⟨579194, by rfl⟩ : syracuseStep 772259 = 1158389) B1158389
theorem B2607281 : Blo 770335 2607281 := bstep (se 2 (by rfl) ⟨977730, by rfl⟩ : syracuseStep 2607281 = 1955461) B1955461
theorem B772275 : Blo 770335 772275 := bstep (se 1 (by rfl) ⟨579206, by rfl⟩ : syracuseStep 772275 = 1158413) B1158413
theorem B772291 : Blo 770335 772291 := bstep (se 1 (by rfl) ⟨579218, by rfl⟩ : syracuseStep 772291 = 1158437) B1158437
theorem B772307 : Blo 770335 772307 := bstep (se 1 (by rfl) ⟨579230, by rfl⟩ : syracuseStep 772307 = 1158461) B1158461
theorem B772323 : Blo 770335 772323 := bstep (se 1 (by rfl) ⟨579242, by rfl⟩ : syracuseStep 772323 = 1158485) B1158485
theorem B4409585 : Blo 770335 4409585 := bstep (se 2 (by rfl) ⟨1653594, by rfl⟩ : syracuseStep 4409585 = 3307189) B3307189
theorem B772339 : Blo 770335 772339 := bstep (se 1 (by rfl) ⟨579254, by rfl⟩ : syracuseStep 772339 = 1158509) B1158509
theorem B772355 : Blo 770335 772355 := bstep (se 1 (by rfl) ⟨579266, by rfl⟩ : syracuseStep 772355 = 1158533) B1158533
theorem B772371 : Blo 770335 772371 := bstep (se 1 (by rfl) ⟨579278, by rfl⟩ : syracuseStep 772371 = 1158557) B1158557
theorem B772387 : Blo 770335 772387 := bstep (se 1 (by rfl) ⟨579290, by rfl⟩ : syracuseStep 772387 = 1158581) B1158581
theorem B2935075 : Blo 770335 2935075 := bstep (se 1 (by rfl) ⟨2201306, by rfl⟩ : syracuseStep 2935075 = 4402613) B4402613
theorem B870691 : Blo 770335 870691 := bstep (se 1 (by rfl) ⟨653018, by rfl⟩ : syracuseStep 870691 = 1306037) B1306037
theorem B772403 : Blo 770335 772403 := bstep (se 1 (by rfl) ⟨579302, by rfl⟩ : syracuseStep 772403 = 1158605) B1158605
theorem B772419 : Blo 770335 772419 := bstep (se 1 (by rfl) ⟨579314, by rfl⟩ : syracuseStep 772419 = 1158629) B1158629
theorem B772435 : Blo 770335 772435 := bstep (se 1 (by rfl) ⟨579326, by rfl⟩ : syracuseStep 772435 = 1158653) B1158653
theorem B772451 : Blo 770335 772451 := bstep (se 1 (by rfl) ⟨579338, by rfl⟩ : syracuseStep 772451 = 1158677) B1158677
theorem B772467 : Blo 770335 772467 := bstep (se 1 (by rfl) ⟨579350, by rfl⟩ : syracuseStep 772467 = 1158701) B1158701
theorem B772483 : Blo 770335 772483 := bstep (se 1 (by rfl) ⟨579362, by rfl⟩ : syracuseStep 772483 = 1158725) B1158725
theorem B772499 : Blo 770335 772499 := bstep (se 1 (by rfl) ⟨579374, by rfl⟩ : syracuseStep 772499 = 1158749) B1158749
theorem B772515 : Blo 770335 772515 := bstep (se 1 (by rfl) ⟨579386, by rfl⟩ : syracuseStep 772515 = 1158773) B1158773
theorem B772531 : Blo 770335 772531 := bstep (se 1 (by rfl) ⟨579398, by rfl⟩ : syracuseStep 772531 = 1158797) B1158797
theorem B870835 : Blo 770335 870835 := bstep (se 1 (by rfl) ⟨653126, by rfl⟩ : syracuseStep 870835 = 1306253) B1306253
theorem B772547 : Blo 770335 772547 := bstep (se 1 (by rfl) ⟨579410, by rfl⟩ : syracuseStep 772547 = 1158821) B1158821
theorem B772563 : Blo 770335 772563 := bstep (se 1 (by rfl) ⟨579422, by rfl⟩ : syracuseStep 772563 = 1158845) B1158845
theorem B772579 : Blo 770335 772579 := bstep (se 1 (by rfl) ⟨579434, by rfl⟩ : syracuseStep 772579 = 1158869) B1158869
theorem B772595 : Blo 770335 772595 := bstep (se 1 (by rfl) ⟨579446, by rfl⟩ : syracuseStep 772595 = 1158893) B1158893
theorem B772611 : Blo 770335 772611 := bstep (se 1 (by rfl) ⟨579458, by rfl⟩ : syracuseStep 772611 = 1158917) B1158917
theorem B2509325 : Blo 770335 2509325 := bstep (se 3 (by rfl) ⟨470498, by rfl⟩ : syracuseStep 2509325 = 940997) B940997
theorem B772627 : Blo 770335 772627 := bstep (se 1 (by rfl) ⟨579470, by rfl⟩ : syracuseStep 772627 = 1158941) B1158941
theorem B772643 : Blo 770335 772643 := bstep (se 1 (by rfl) ⟨579482, by rfl⟩ : syracuseStep 772643 = 1158965) B1158965
theorem B1395235 : Blo 770335 1395235 := bstep (se 1 (by rfl) ⟨1046426, by rfl⟩ : syracuseStep 1395235 = 2092853) B2092853
theorem B772659 : Blo 770335 772659 := bstep (se 1 (by rfl) ⟨579494, by rfl⟩ : syracuseStep 772659 = 1158989) B1158989
theorem B772675 : Blo 770335 772675 := bstep (se 1 (by rfl) ⟨579506, by rfl⟩ : syracuseStep 772675 = 1159013) B1159013
theorem B870979 : Blo 770335 870979 := bstep (se 1 (by rfl) ⟨653234, by rfl⟩ : syracuseStep 870979 = 1306469) B1306469
theorem B772691 : Blo 770335 772691 := bstep (se 1 (by rfl) ⟨579518, by rfl⟩ : syracuseStep 772691 = 1159037) B1159037
theorem B772707 : Blo 770335 772707 := bstep (se 1 (by rfl) ⟨579530, by rfl⟩ : syracuseStep 772707 = 1159061) B1159061
theorem B772723 : Blo 770335 772723 := bstep (se 1 (by rfl) ⟨579542, by rfl⟩ : syracuseStep 772723 = 1159085) B1159085
theorem B772739 : Blo 770335 772739 := bstep (se 1 (by rfl) ⟨579554, by rfl⟩ : syracuseStep 772739 = 1159109) B1159109
theorem B772755 : Blo 770335 772755 := bstep (se 1 (by rfl) ⟨579566, by rfl⟩ : syracuseStep 772755 = 1159133) B1159133
theorem B772771 : Blo 770335 772771 := bstep (se 1 (by rfl) ⟨579578, by rfl⟩ : syracuseStep 772771 = 1159157) B1159157
theorem B772787 : Blo 770335 772787 := bstep (se 1 (by rfl) ⟨579590, by rfl⟩ : syracuseStep 772787 = 1159181) B1159181
theorem B772803 : Blo 770335 772803 := bstep (se 1 (by rfl) ⟨579602, by rfl⟩ : syracuseStep 772803 = 1159205) B1159205
theorem B2607821 : Blo 770335 2607821 := bstep (se 3 (by rfl) ⟨488966, by rfl⟩ : syracuseStep 2607821 = 977933) B977933
theorem B772819 : Blo 770335 772819 := bstep (se 1 (by rfl) ⟨579614, by rfl⟩ : syracuseStep 772819 = 1159229) B1159229
theorem B871123 : Blo 770335 871123 := bstep (se 1 (by rfl) ⟨653342, by rfl⟩ : syracuseStep 871123 = 1306685) B1306685
theorem B772835 : Blo 770335 772835 := bstep (se 1 (by rfl) ⟨579626, by rfl⟩ : syracuseStep 772835 = 1159253) B1159253
theorem B772851 : Blo 770335 772851 := bstep (se 1 (by rfl) ⟨579638, by rfl⟩ : syracuseStep 772851 = 1159277) B1159277
theorem B2607875 : Blo 770335 2607875 := bstep (se 1 (by rfl) ⟨1955906, by rfl⟩ : syracuseStep 2607875 = 3911813) B3911813
theorem B772867 : Blo 770335 772867 := bstep (se 1 (by rfl) ⟨579650, by rfl⟩ : syracuseStep 772867 = 1159301) B1159301
theorem B772883 : Blo 770335 772883 := bstep (se 1 (by rfl) ⟨579662, by rfl⟩ : syracuseStep 772883 = 1159325) B1159325
theorem B772899 : Blo 770335 772899 := bstep (se 1 (by rfl) ⟨579674, by rfl⟩ : syracuseStep 772899 = 1159349) B1159349
theorem B3132209 : Blo 770335 3132209 := bstep (se 2 (by rfl) ⟨1174578, by rfl⟩ : syracuseStep 3132209 = 2349157) B2349157
theorem B772915 : Blo 770335 772915 := bstep (se 1 (by rfl) ⟨579686, by rfl⟩ : syracuseStep 772915 = 1159373) B1159373
theorem B772931 : Blo 770335 772931 := bstep (se 1 (by rfl) ⟨579698, by rfl⟩ : syracuseStep 772931 = 1159397) B1159397
theorem B772947 : Blo 770335 772947 := bstep (se 1 (by rfl) ⟨579710, by rfl⟩ : syracuseStep 772947 = 1159421) B1159421
theorem B772963 : Blo 770335 772963 := bstep (se 1 (by rfl) ⟨579722, by rfl⟩ : syracuseStep 772963 = 1159445) B1159445
theorem B772979 : Blo 770335 772979 := bstep (se 1 (by rfl) ⟨579734, by rfl⟩ : syracuseStep 772979 = 1159469) B1159469
theorem B772995 : Blo 770335 772995 := bstep (se 1 (by rfl) ⟨579746, by rfl⟩ : syracuseStep 772995 = 1159493) B1159493
theorem B1952657 : Blo 770335 1952657 := bstep (se 2 (by rfl) ⟨732246, by rfl⟩ : syracuseStep 1952657 = 1464493) B1464493
theorem B773011 : Blo 770335 773011 := bstep (se 1 (by rfl) ⟨579758, by rfl⟩ : syracuseStep 773011 = 1159517) B1159517
theorem B773027 : Blo 770335 773027 := bstep (se 1 (by rfl) ⟨579770, by rfl⟩ : syracuseStep 773027 = 1159541) B1159541
theorem B3132337 : Blo 770335 3132337 := bstep (se 2 (by rfl) ⟨1174626, by rfl⟩ : syracuseStep 3132337 = 2349253) B2349253
theorem B773043 : Blo 770335 773043 := bstep (se 1 (by rfl) ⟨579782, by rfl⟩ : syracuseStep 773043 = 1159565) B1159565
theorem B1952707 : Blo 770335 1952707 := bstep (se 1 (by rfl) ⟨1464530, by rfl⟩ : syracuseStep 1952707 = 2929061) B2929061
theorem B773059 : Blo 770335 773059 := bstep (se 1 (by rfl) ⟨579794, by rfl⟩ : syracuseStep 773059 = 1159589) B1159589
theorem B773075 : Blo 770335 773075 := bstep (se 1 (by rfl) ⟨579806, by rfl⟩ : syracuseStep 773075 = 1159613) B1159613
theorem B773091 : Blo 770335 773091 := bstep (se 1 (by rfl) ⟨579818, by rfl⟩ : syracuseStep 773091 = 1159637) B1159637
theorem B1100785 : Blo 770335 1100785 := bstep (se 2 (by rfl) ⟨412794, by rfl⟩ : syracuseStep 1100785 = 825589) B825589
theorem B773107 : Blo 770335 773107 := bstep (se 1 (by rfl) ⟨579830, by rfl⟩ : syracuseStep 773107 = 1159661) B1159661
theorem B773123 : Blo 770335 773123 := bstep (se 1 (by rfl) ⟨579842, by rfl⟩ : syracuseStep 773123 = 1159685) B1159685
theorem B2608145 : Blo 770335 2608145 := bstep (se 2 (by rfl) ⟨978054, by rfl⟩ : syracuseStep 2608145 = 1956109) B1956109
theorem B773139 : Blo 770335 773139 := bstep (se 1 (by rfl) ⟨579854, by rfl⟩ : syracuseStep 773139 = 1159709) B1159709
theorem B773155 : Blo 770335 773155 := bstep (se 1 (by rfl) ⟨579866, by rfl⟩ : syracuseStep 773155 = 1159733) B1159733
theorem B773171 : Blo 770335 773171 := bstep (se 1 (by rfl) ⟨579878, by rfl⟩ : syracuseStep 773171 = 1159757) B1159757
theorem B773187 : Blo 770335 773187 := bstep (se 1 (by rfl) ⟨579890, by rfl⟩ : syracuseStep 773187 = 1159781) B1159781
theorem B1952849 : Blo 770335 1952849 := bstep (se 2 (by rfl) ⟨732318, by rfl⟩ : syracuseStep 1952849 = 1464637) B1464637
theorem B1100881 : Blo 770335 1100881 := bstep (se 2 (by rfl) ⟨412830, by rfl⟩ : syracuseStep 1100881 = 825661) B825661
theorem B773203 : Blo 770335 773203 := bstep (se 1 (by rfl) ⟨579902, by rfl⟩ : syracuseStep 773203 = 1159805) B1159805
theorem B2477137 : Blo 770335 2477137 := bstep (se 2 (by rfl) ⟨928926, by rfl⟩ : syracuseStep 2477137 = 1857853) B1857853
theorem B773219 : Blo 770335 773219 := bstep (se 1 (by rfl) ⟨579914, by rfl⟩ : syracuseStep 773219 = 1159829) B1159829
theorem B773235 : Blo 770335 773235 := bstep (se 1 (by rfl) ⟨579926, by rfl⟩ : syracuseStep 773235 = 1159853) B1159853
theorem B773251 : Blo 770335 773251 := bstep (se 1 (by rfl) ⟨579938, by rfl⟩ : syracuseStep 773251 = 1159877) B1159877
theorem B773267 : Blo 770335 773267 := bstep (se 1 (by rfl) ⟨579950, by rfl⟩ : syracuseStep 773267 = 1159901) B1159901
theorem B773283 : Blo 770335 773283 := bstep (se 1 (by rfl) ⟨579962, by rfl⟩ : syracuseStep 773283 = 1159925) B1159925
theorem B773299 : Blo 770335 773299 := bstep (se 1 (by rfl) ⟨579974, by rfl⟩ : syracuseStep 773299 = 1159949) B1159949
theorem B773315 : Blo 770335 773315 := bstep (se 1 (by rfl) ⟨579986, by rfl⟩ : syracuseStep 773315 = 1159973) B1159973
theorem B773331 : Blo 770335 773331 := bstep (se 1 (by rfl) ⟨579998, by rfl⟩ : syracuseStep 773331 = 1159997) B1159997
theorem B773347 : Blo 770335 773347 := bstep (se 1 (by rfl) ⟨580010, by rfl⟩ : syracuseStep 773347 = 1160021) B1160021
theorem B773363 : Blo 770335 773363 := bstep (se 1 (by rfl) ⟨580022, by rfl⟩ : syracuseStep 773363 = 1160045) B1160045
theorem B773379 : Blo 770335 773379 := bstep (se 1 (by rfl) ⟨580034, by rfl⟩ : syracuseStep 773379 = 1160069) B1160069
theorem B773395 : Blo 770335 773395 := bstep (se 1 (by rfl) ⟨580046, by rfl⟩ : syracuseStep 773395 = 1160093) B1160093
theorem B773411 : Blo 770335 773411 := bstep (se 1 (by rfl) ⟨580058, by rfl⟩ : syracuseStep 773411 = 1160117) B1160117
theorem B773427 : Blo 770335 773427 := bstep (se 1 (by rfl) ⟨580070, by rfl⟩ : syracuseStep 773427 = 1160141) B1160141
theorem B773443 : Blo 770335 773443 := bstep (se 1 (by rfl) ⟨580082, by rfl⟩ : syracuseStep 773443 = 1160165) B1160165
theorem B2477393 : Blo 770335 2477393 := bstep (se 2 (by rfl) ⟨929022, by rfl⟩ : syracuseStep 2477393 = 1858045) B1858045
theorem B773459 : Blo 770335 773459 := bstep (se 1 (by rfl) ⟨580094, by rfl⟩ : syracuseStep 773459 = 1160189) B1160189
theorem B773475 : Blo 770335 773475 := bstep (se 1 (by rfl) ⟨580106, by rfl⟩ : syracuseStep 773475 = 1160213) B1160213
theorem B773491 : Blo 770335 773491 := bstep (se 1 (by rfl) ⟨580118, by rfl⟩ : syracuseStep 773491 = 1160237) B1160237
theorem B773507 : Blo 770335 773507 := bstep (se 1 (by rfl) ⟨580130, by rfl⟩ : syracuseStep 773507 = 1160261) B1160261
theorem B773523 : Blo 770335 773523 := bstep (se 1 (by rfl) ⟨580142, by rfl⟩ : syracuseStep 773523 = 1160285) B1160285
theorem B773539 : Blo 770335 773539 := bstep (se 1 (by rfl) ⟨580154, by rfl⟩ : syracuseStep 773539 = 1160309) B1160309
theorem B773555 : Blo 770335 773555 := bstep (se 1 (by rfl) ⟨580166, by rfl⟩ : syracuseStep 773555 = 1160333) B1160333
theorem B773571 : Blo 770335 773571 := bstep (se 1 (by rfl) ⟨580178, by rfl⟩ : syracuseStep 773571 = 1160357) B1160357
theorem B773587 : Blo 770335 773587 := bstep (se 1 (by rfl) ⟨580190, by rfl⟩ : syracuseStep 773587 = 1160381) B1160381
theorem B773603 : Blo 770335 773603 := bstep (se 1 (by rfl) ⟨580202, by rfl⟩ : syracuseStep 773603 = 1160405) B1160405
theorem B773619 : Blo 770335 773619 := bstep (se 1 (by rfl) ⟨580214, by rfl⟩ : syracuseStep 773619 = 1160429) B1160429
theorem B773635 : Blo 770335 773635 := bstep (se 1 (by rfl) ⟨580226, by rfl⟩ : syracuseStep 773635 = 1160453) B1160453
theorem B773651 : Blo 770335 773651 := bstep (se 1 (by rfl) ⟨580238, by rfl⟩ : syracuseStep 773651 = 1160477) B1160477
theorem B773667 : Blo 770335 773667 := bstep (se 1 (by rfl) ⟨580250, by rfl⟩ : syracuseStep 773667 = 1160501) B1160501
theorem B2608685 : Blo 770335 2608685 := bstep (se 3 (by rfl) ⟨489128, by rfl⟩ : syracuseStep 2608685 = 978257) B978257
theorem B773683 : Blo 770335 773683 := bstep (se 1 (by rfl) ⟨580262, by rfl⟩ : syracuseStep 773683 = 1160525) B1160525
theorem B1101377 : Blo 770335 1101377 := bstep (se 2 (by rfl) ⟨413016, by rfl⟩ : syracuseStep 1101377 = 826033) B826033
theorem B773699 : Blo 770335 773699 := bstep (se 1 (by rfl) ⟨580274, by rfl⟩ : syracuseStep 773699 = 1160549) B1160549
theorem B773715 : Blo 770335 773715 := bstep (se 1 (by rfl) ⟨580286, by rfl⟩ : syracuseStep 773715 = 1160573) B1160573
theorem B2608739 : Blo 770335 2608739 := bstep (se 1 (by rfl) ⟨1956554, by rfl⟩ : syracuseStep 2608739 = 3913109) B3913109
theorem B773731 : Blo 770335 773731 := bstep (se 1 (by rfl) ⟨580298, by rfl⟩ : syracuseStep 773731 = 1160597) B1160597
theorem B773747 : Blo 770335 773747 := bstep (se 1 (by rfl) ⟨580310, by rfl⟩ : syracuseStep 773747 = 1160621) B1160621
theorem B773763 : Blo 770335 773763 := bstep (se 1 (by rfl) ⟨580322, by rfl⟩ : syracuseStep 773763 = 1160645) B1160645
theorem B773779 : Blo 770335 773779 := bstep (se 1 (by rfl) ⟨580334, by rfl⟩ : syracuseStep 773779 = 1160669) B1160669
theorem B773795 : Blo 770335 773795 := bstep (se 1 (by rfl) ⟨580346, by rfl⟩ : syracuseStep 773795 = 1160693) B1160693
theorem B773811 : Blo 770335 773811 := bstep (se 1 (by rfl) ⟨580358, by rfl⟩ : syracuseStep 773811 = 1160717) B1160717
theorem B773827 : Blo 770335 773827 := bstep (se 1 (by rfl) ⟨580370, by rfl⟩ : syracuseStep 773827 = 1160741) B1160741
theorem B773843 : Blo 770335 773843 := bstep (se 1 (by rfl) ⟨580382, by rfl⟩ : syracuseStep 773843 = 1160765) B1160765
theorem B5557987 : Blo 770335 5557987 := bstep (se 1 (by rfl) ⟨4168490, by rfl⟩ : syracuseStep 5557987 = 8336981) B8336981
theorem B773859 : Blo 770335 773859 := bstep (se 1 (by rfl) ⟨580394, by rfl⟩ : syracuseStep 773859 = 1160789) B1160789
theorem B773875 : Blo 770335 773875 := bstep (se 1 (by rfl) ⟨580406, by rfl⟩ : syracuseStep 773875 = 1160813) B1160813
theorem B773891 : Blo 770335 773891 := bstep (se 1 (by rfl) ⟨580418, by rfl⟩ : syracuseStep 773891 = 1160837) B1160837
theorem B773907 : Blo 770335 773907 := bstep (se 1 (by rfl) ⟨580430, by rfl⟩ : syracuseStep 773907 = 1160861) B1160861
theorem B773923 : Blo 770335 773923 := bstep (se 1 (by rfl) ⟨580442, by rfl⟩ : syracuseStep 773923 = 1160885) B1160885
theorem B773939 : Blo 770335 773939 := bstep (se 1 (by rfl) ⟨580454, by rfl⟩ : syracuseStep 773939 = 1160909) B1160909
theorem B773955 : Blo 770335 773955 := bstep (se 1 (by rfl) ⟨580466, by rfl⟩ : syracuseStep 773955 = 1160933) B1160933
theorem B773971 : Blo 770335 773971 := bstep (se 1 (by rfl) ⟨580478, by rfl⟩ : syracuseStep 773971 = 1160957) B1160957
theorem B773987 : Blo 770335 773987 := bstep (se 1 (by rfl) ⟨580490, by rfl⟩ : syracuseStep 773987 = 1160981) B1160981
theorem B2609009 : Blo 770335 2609009 := bstep (se 2 (by rfl) ⟨978378, by rfl⟩ : syracuseStep 2609009 = 1956757) B1956757
theorem B774003 : Blo 770335 774003 := bstep (se 1 (by rfl) ⟨580502, by rfl⟩ : syracuseStep 774003 = 1161005) B1161005
theorem B774019 : Blo 770335 774019 := bstep (se 1 (by rfl) ⟨580514, by rfl⟩ : syracuseStep 774019 = 1161029) B1161029
theorem B774035 : Blo 770335 774035 := bstep (se 1 (by rfl) ⟨580526, by rfl⟩ : syracuseStep 774035 = 1161053) B1161053
theorem B774051 : Blo 770335 774051 := bstep (se 1 (by rfl) ⟨580538, by rfl⟩ : syracuseStep 774051 = 1161077) B1161077
theorem B774067 : Blo 770335 774067 := bstep (se 1 (by rfl) ⟨580550, by rfl⟩ : syracuseStep 774067 = 1161101) B1161101
theorem B774083 : Blo 770335 774083 := bstep (se 1 (by rfl) ⟨580562, by rfl⟩ : syracuseStep 774083 = 1161125) B1161125
theorem B774099 : Blo 770335 774099 := bstep (se 1 (by rfl) ⟨580574, by rfl⟩ : syracuseStep 774099 = 1161149) B1161149
theorem B774115 : Blo 770335 774115 := bstep (se 1 (by rfl) ⟨580586, by rfl⟩ : syracuseStep 774115 = 1161173) B1161173
theorem B774131 : Blo 770335 774131 := bstep (se 1 (by rfl) ⟨580598, by rfl⟩ : syracuseStep 774131 = 1161197) B1161197
theorem B774147 : Blo 770335 774147 := bstep (se 1 (by rfl) ⟨580610, by rfl⟩ : syracuseStep 774147 = 1161221) B1161221
theorem B7032845 : Blo 770335 7032845 := bstep (se 3 (by rfl) ⟨1318658, by rfl⟩ : syracuseStep 7032845 = 2637317) B2637317
theorem B774163 : Blo 770335 774163 := bstep (se 1 (by rfl) ⟨580622, by rfl⟩ : syracuseStep 774163 = 1161245) B1161245
theorem B774179 : Blo 770335 774179 := bstep (se 1 (by rfl) ⟨580634, by rfl⟩ : syracuseStep 774179 = 1161269) B1161269
theorem B1953841 : Blo 770335 1953841 := bstep (se 2 (by rfl) ⟨732690, by rfl⟩ : syracuseStep 1953841 = 1465381) B1465381
theorem B774195 : Blo 770335 774195 := bstep (se 1 (by rfl) ⟨580646, by rfl⟩ : syracuseStep 774195 = 1161293) B1161293
theorem B774211 : Blo 770335 774211 := bstep (se 1 (by rfl) ⟨580658, by rfl⟩ : syracuseStep 774211 = 1161317) B1161317
theorem B774227 : Blo 770335 774227 := bstep (se 1 (by rfl) ⟨580670, by rfl⟩ : syracuseStep 774227 = 1161341) B1161341
theorem B774243 : Blo 770335 774243 := bstep (se 1 (by rfl) ⟨580682, by rfl⟩ : syracuseStep 774243 = 1161365) B1161365
theorem B774259 : Blo 770335 774259 := bstep (se 1 (by rfl) ⟨580694, by rfl⟩ : syracuseStep 774259 = 1161389) B1161389
theorem B774275 : Blo 770335 774275 := bstep (se 1 (by rfl) ⟨580706, by rfl⟩ : syracuseStep 774275 = 1161413) B1161413
theorem B774291 : Blo 770335 774291 := bstep (se 1 (by rfl) ⟨580718, by rfl⟩ : syracuseStep 774291 = 1161437) B1161437
theorem B774307 : Blo 770335 774307 := bstep (se 1 (by rfl) ⟨580730, by rfl⟩ : syracuseStep 774307 = 1161461) B1161461
theorem B774323 : Blo 770335 774323 := bstep (se 1 (by rfl) ⟨580742, by rfl⟩ : syracuseStep 774323 = 1161485) B1161485
theorem B1954115 : Blo 770335 1954115 := bstep (se 1 (by rfl) ⟨1465586, by rfl⟩ : syracuseStep 1954115 = 2931173) B2931173
theorem B2609549 : Blo 770335 2609549 := bstep (se 3 (by rfl) ⟨489290, by rfl⟩ : syracuseStep 2609549 = 978581) B978581
theorem B1102243 : Blo 770335 1102243 := bstep (se 1 (by rfl) ⟨826682, by rfl⟩ : syracuseStep 1102243 = 1653365) B1653365
theorem B2478509 : Blo 770335 2478509 := bstep (se 3 (by rfl) ⟨464720, by rfl⟩ : syracuseStep 2478509 = 929441) B929441
theorem B2609603 : Blo 770335 2609603 := bstep (se 1 (by rfl) ⟨1957202, by rfl⟩ : syracuseStep 2609603 = 3914405) B3914405
theorem B2937293 : Blo 770335 2937293 := bstep (se 3 (by rfl) ⟨550742, by rfl⟩ : syracuseStep 2937293 = 1101485) B1101485
theorem B1462769 : Blo 770335 1462769 := bstep (se 2 (by rfl) ⟨548538, by rfl⟩ : syracuseStep 1462769 = 1097077) B1097077
theorem B1954307 : Blo 770335 1954307 := bstep (se 1 (by rfl) ⟨1465730, by rfl⟩ : syracuseStep 1954307 = 2931461) B2931461
theorem B1102339 : Blo 770335 1102339 := bstep (se 1 (by rfl) ⟨826754, by rfl⟩ : syracuseStep 1102339 = 1653509) B1653509
theorem B2511395 : Blo 770335 2511395 := bstep (se 1 (by rfl) ⟨1883546, by rfl⟩ : syracuseStep 2511395 = 3767093) B3767093
theorem B938659 : Blo 770335 938659 := bstep (se 1 (by rfl) ⟨703994, by rfl⟩ : syracuseStep 938659 = 1407989) B1407989
theorem B2609873 : Blo 770335 2609873 := bstep (se 2 (by rfl) ⟨978702, by rfl⟩ : syracuseStep 2609873 = 1957405) B1957405
theorem B3134321 : Blo 770335 3134321 := bstep (se 2 (by rfl) ⟨1175370, by rfl⟩ : syracuseStep 3134321 = 2350741) B2350741
theorem B3134413 : Blo 770335 3134413 := bstep (se 3 (by rfl) ⟨587702, by rfl⟩ : syracuseStep 3134413 = 1175405) B1175405
theorem B1234129 : Blo 770335 1234129 := bstep (se 2 (by rfl) ⟨462798, by rfl⟩ : syracuseStep 1234129 = 925597) B925597
theorem B2610413 : Blo 770335 2610413 := bstep (se 3 (by rfl) ⟨489452, by rfl⟩ : syracuseStep 2610413 = 978905) B978905
theorem B2610467 : Blo 770335 2610467 := bstep (se 1 (by rfl) ⟨1957850, by rfl⟩ : syracuseStep 2610467 = 3915701) B3915701
theorem B2086193 : Blo 770335 2086193 := bstep (se 2 (by rfl) ⟨782322, by rfl⟩ : syracuseStep 2086193 = 1564645) B1564645
theorem B1463665 : Blo 770335 1463665 := bstep (se 2 (by rfl) ⟨548874, by rfl⟩ : syracuseStep 1463665 = 1097749) B1097749
theorem B1955249 : Blo 770335 1955249 := bstep (se 2 (by rfl) ⟨733218, by rfl⟩ : syracuseStep 1955249 = 1466437) B1466437
theorem B1955299 : Blo 770335 1955299 := bstep (se 1 (by rfl) ⟨1466474, by rfl⟩ : syracuseStep 1955299 = 2932949) B2932949
theorem B1299955 : Blo 770335 1299955 := bstep (se 1 (by rfl) ⟨974966, by rfl⟩ : syracuseStep 1299955 = 1949933) B1949933
theorem B1463825 : Blo 770335 1463825 := bstep (se 2 (by rfl) ⟨548934, by rfl⟩ : syracuseStep 1463825 = 1097869) B1097869
theorem B2610737 : Blo 770335 2610737 := bstep (se 2 (by rfl) ⟨979026, by rfl⟩ : syracuseStep 2610737 = 1958053) B1958053
theorem B1955441 : Blo 770335 1955441 := bstep (se 2 (by rfl) ⟨733290, by rfl⟩ : syracuseStep 1955441 = 1466581) B1466581
theorem B1300097 : Blo 770335 1300097 := bstep (se 2 (by rfl) ⟨487536, by rfl⟩ : syracuseStep 1300097 = 975073) B975073
theorem B2086573 : Blo 770335 2086573 := bstep (se 3 (by rfl) ⟨391232, by rfl⟩ : syracuseStep 2086573 = 782465) B782465
theorem B8345285 : Blo 770335 8345285 := bstep (se 4 (by rfl) ⟨782370, by rfl⟩ : syracuseStep 8345285 = 1564741) B1564741
theorem B5297861 : Blo 770335 5297861 := bstep (se 4 (by rfl) ⟨496674, by rfl⟩ : syracuseStep 5297861 = 993349) B993349
theorem B2479853 : Blo 770335 2479853 := bstep (se 3 (by rfl) ⟨464972, by rfl⟩ : syracuseStep 2479853 = 929945) B929945
theorem B1300225 : Blo 770335 1300225 := bstep (se 2 (by rfl) ⟨487584, by rfl⟩ : syracuseStep 1300225 = 975169) B975169
theorem B1300259 : Blo 770335 1300259 := bstep (se 1 (by rfl) ⟨975194, by rfl⟩ : syracuseStep 1300259 = 1950389) B1950389
theorem B1234801 : Blo 770335 1234801 := bstep (se 2 (by rfl) ⟨463050, by rfl⟩ : syracuseStep 1234801 = 926101) B926101
theorem B1300387 : Blo 770335 1300387 := bstep (se 1 (by rfl) ⟨975290, by rfl⟩ : syracuseStep 1300387 = 1950581) B1950581
theorem B1464227 : Blo 770335 1464227 := bstep (se 1 (by rfl) ⟨1098170, by rfl⟩ : syracuseStep 1464227 = 2196341) B2196341
theorem B3299363 : Blo 770335 3299363 := bstep (se 1 (by rfl) ⟨2474522, by rfl⟩ : syracuseStep 3299363 = 4949045) B4949045
theorem B1300529 : Blo 770335 1300529 := bstep (se 2 (by rfl) ⟨487698, by rfl⟩ : syracuseStep 1300529 = 975397) B975397
theorem B2611277 : Blo 770335 2611277 := bstep (se 3 (by rfl) ⟨489614, by rfl⟩ : syracuseStep 2611277 = 979229) B979229
theorem B2611331 : Blo 770335 2611331 := bstep (se 1 (by rfl) ⟨1958498, by rfl⟩ : syracuseStep 2611331 = 3916997) B3916997
theorem B2480291 : Blo 770335 2480291 := bstep (se 1 (by rfl) ⟨1860218, by rfl⟩ : syracuseStep 2480291 = 3720437) B3720437
theorem B1300657 : Blo 770335 1300657 := bstep (se 2 (by rfl) ⟨487746, by rfl⟩ : syracuseStep 1300657 = 975493) B975493
theorem B1300691 : Blo 770335 1300691 := bstep (se 1 (by rfl) ⟨975518, by rfl⟩ : syracuseStep 1300691 = 1951037) B1951037
theorem B1300819 : Blo 770335 1300819 := bstep (se 1 (by rfl) ⟨975614, by rfl⟩ : syracuseStep 1300819 = 1951229) B1951229
theorem B9525617 : Blo 770335 9525617 := bstep (se 2 (by rfl) ⟨3572106, by rfl⟩ : syracuseStep 9525617 = 7144213) B7144213
theorem B2611601 : Blo 770335 2611601 := bstep (se 2 (by rfl) ⟨979350, by rfl⟩ : syracuseStep 2611601 = 1958701) B1958701
theorem B1300961 : Blo 770335 1300961 := bstep (se 2 (by rfl) ⟨487860, by rfl⟩ : syracuseStep 1300961 = 975721) B975721
theorem B3135971 : Blo 770335 3135971 := bstep (se 1 (by rfl) ⟨2351978, by rfl⟩ : syracuseStep 3135971 = 4703957) B4703957
theorem B4184581 : Blo 770335 4184581 := bstep (se 4 (by rfl) ⟨392304, by rfl⟩ : syracuseStep 4184581 = 784609) B784609
theorem B5855813 : Blo 770335 5855813 := bstep (se 4 (by rfl) ⟨548982, by rfl⟩ : syracuseStep 5855813 = 1097965) B1097965
theorem B1956433 : Blo 770335 1956433 := bstep (se 2 (by rfl) ⟨733662, by rfl⟩ : syracuseStep 1956433 = 1467325) B1467325
theorem B1301089 : Blo 770335 1301089 := bstep (se 2 (by rfl) ⟨487908, by rfl⟩ : syracuseStep 1301089 = 975817) B975817
theorem B1301123 : Blo 770335 1301123 := bstep (se 1 (by rfl) ⟨975842, by rfl⟩ : syracuseStep 1301123 = 1951685) B1951685
theorem B1301251 : Blo 770335 1301251 := bstep (se 1 (by rfl) ⟨975938, by rfl⟩ : syracuseStep 1301251 = 1951877) B1951877
theorem B1465123 : Blo 770335 1465123 := bstep (se 1 (by rfl) ⟨1098842, by rfl⟩ : syracuseStep 1465123 = 2197685) B2197685
theorem B1956707 : Blo 770335 1956707 := bstep (se 1 (by rfl) ⟨1467530, by rfl⟩ : syracuseStep 1956707 = 2935061) B2935061
theorem B7035761 : Blo 770335 7035761 := bstep (se 2 (by rfl) ⟨2638410, by rfl⟩ : syracuseStep 7035761 = 5276821) B5276821
theorem B4709261 : Blo 770335 4709261 := bstep (se 3 (by rfl) ⟨882986, by rfl⟩ : syracuseStep 4709261 = 1765973) B1765973
theorem B1301393 : Blo 770335 1301393 := bstep (se 2 (by rfl) ⟨488022, by rfl⟩ : syracuseStep 1301393 = 976045) B976045
theorem B2612141 : Blo 770335 2612141 := bstep (se 3 (by rfl) ⟨489776, by rfl⟩ : syracuseStep 2612141 = 979553) B979553
theorem B1235891 : Blo 770335 1235891 := bstep (se 1 (by rfl) ⟨926918, by rfl⟩ : syracuseStep 1235891 = 1853837) B1853837
theorem B1465283 : Blo 770335 1465283 := bstep (se 1 (by rfl) ⟨1098962, by rfl⟩ : syracuseStep 1465283 = 2197925) B2197925
theorem B2612195 : Blo 770335 2612195 := bstep (se 1 (by rfl) ⟨1959146, by rfl⟩ : syracuseStep 2612195 = 3918293) B3918293
theorem B5790733 : Blo 770335 5790733 := bstep (se 3 (by rfl) ⟨1085762, by rfl⟩ : syracuseStep 5790733 = 2171525) B2171525
theorem B1301521 : Blo 770335 1301521 := bstep (se 2 (by rfl) ⟨488070, by rfl⟩ : syracuseStep 1301521 = 976141) B976141
theorem B1956899 : Blo 770335 1956899 := bstep (se 1 (by rfl) ⟨1467674, by rfl⟩ : syracuseStep 1956899 = 2935349) B2935349
theorem B1301555 : Blo 770335 1301555 := bstep (se 1 (by rfl) ⟨976166, by rfl⟩ : syracuseStep 1301555 = 1952333) B1952333
theorem B1301683 : Blo 770335 1301683 := bstep (se 1 (by rfl) ⟨976262, by rfl⟩ : syracuseStep 1301683 = 1952525) B1952525
theorem B1236179 : Blo 770335 1236179 := bstep (se 1 (by rfl) ⟨927134, by rfl⟩ : syracuseStep 1236179 = 1854269) B1854269
theorem B2612465 : Blo 770335 2612465 := bstep (se 2 (by rfl) ⟨979674, by rfl⟩ : syracuseStep 2612465 = 1959349) B1959349
theorem B1301825 : Blo 770335 1301825 := bstep (se 2 (by rfl) ⟨488184, by rfl⟩ : syracuseStep 1301825 = 976369) B976369
theorem B2088355 : Blo 770335 2088355 := bstep (se 1 (by rfl) ⟨1566266, by rfl⟩ : syracuseStep 2088355 = 3132533) B3132533
theorem B1301953 : Blo 770335 1301953 := bstep (se 2 (by rfl) ⟨488232, by rfl⟩ : syracuseStep 1301953 = 976465) B976465
theorem B1301987 : Blo 770335 1301987 := bstep (se 1 (by rfl) ⟨976490, by rfl⟩ : syracuseStep 1301987 = 1952981) B1952981
theorem B1302115 : Blo 770335 1302115 := bstep (se 1 (by rfl) ⟨976586, by rfl⟩ : syracuseStep 1302115 = 1953173) B1953173
theorem B11886193 : Blo 770335 11886193 := bstep (se 2 (by rfl) ⟨4457322, by rfl⟩ : syracuseStep 11886193 = 8914645) B8914645
theorem B1236595 : Blo 770335 1236595 := bstep (se 1 (by rfl) ⟨927446, by rfl⟩ : syracuseStep 1236595 = 1854893) B1854893
theorem B1302257 : Blo 770335 1302257 := bstep (se 2 (by rfl) ⟨488346, by rfl⟩ : syracuseStep 1302257 = 976693) B976693
theorem B2613005 : Blo 770335 2613005 := bstep (se 3 (by rfl) ⟨489938, by rfl⟩ : syracuseStep 2613005 = 979877) B979877
theorem B2613059 : Blo 770335 2613059 := bstep (se 1 (by rfl) ⟨1959794, by rfl⟩ : syracuseStep 2613059 = 3919589) B3919589
theorem B2350957 : Blo 770335 2350957 := bstep (se 3 (by rfl) ⟨440804, by rfl⟩ : syracuseStep 2350957 = 881609) B881609
theorem B1302385 : Blo 770335 1302385 := bstep (se 2 (by rfl) ⟨488394, by rfl⟩ : syracuseStep 1302385 = 976789) B976789
theorem B1236865 : Blo 770335 1236865 := bstep (se 2 (by rfl) ⟨463824, by rfl⟩ : syracuseStep 1236865 = 927649) B927649
theorem B1302419 : Blo 770335 1302419 := bstep (se 1 (by rfl) ⟨976814, by rfl⟩ : syracuseStep 1302419 = 1953629) B1953629
theorem B1957841 : Blo 770335 1957841 := bstep (se 2 (by rfl) ⟨734190, by rfl⟩ : syracuseStep 1957841 = 1468381) B1468381
theorem B1466353 : Blo 770335 1466353 := bstep (se 2 (by rfl) ⟨549882, by rfl⟩ : syracuseStep 1466353 = 1099765) B1099765
theorem B1957891 : Blo 770335 1957891 := bstep (se 1 (by rfl) ⟨1468418, by rfl⟩ : syracuseStep 1957891 = 2936837) B2936837
theorem B1302547 : Blo 770335 1302547 := bstep (se 1 (by rfl) ⟨976910, by rfl⟩ : syracuseStep 1302547 = 1953821) B1953821
theorem B2613329 : Blo 770335 2613329 := bstep (se 2 (by rfl) ⟨979998, by rfl⟩ : syracuseStep 2613329 = 1959997) B1959997
theorem B1237121 : Blo 770335 1237121 := bstep (se 2 (by rfl) ⟨463920, by rfl⟩ : syracuseStep 1237121 = 927841) B927841
theorem B1958033 : Blo 770335 1958033 := bstep (se 2 (by rfl) ⟨734262, by rfl⟩ : syracuseStep 1958033 = 1468525) B1468525
theorem B1302689 : Blo 770335 1302689 := bstep (se 2 (by rfl) ⟨488508, by rfl⟩ : syracuseStep 1302689 = 977017) B977017
theorem B1302817 : Blo 770335 1302817 := bstep (se 2 (by rfl) ⟨488556, by rfl⟩ : syracuseStep 1302817 = 977113) B977113
theorem B1302851 : Blo 770335 1302851 := bstep (se 1 (by rfl) ⟨977138, by rfl⟩ : syracuseStep 1302851 = 1954277) B1954277
theorem B975235 : Blo 770335 975235 := bstep (se 1 (by rfl) ⟨731426, by rfl⟩ : syracuseStep 975235 = 1462853) B1462853
theorem B2646413 : Blo 770335 2646413 := bstep (se 3 (by rfl) ⟨496202, by rfl⟩ : syracuseStep 2646413 = 992405) B992405
theorem B1302979 : Blo 770335 1302979 := bstep (se 1 (by rfl) ⟨977234, by rfl⟩ : syracuseStep 1302979 = 1954469) B1954469
theorem B975331 : Blo 770335 975331 := bstep (se 1 (by rfl) ⟨731498, by rfl⟩ : syracuseStep 975331 = 1462997) B1462997
theorem B1303121 : Blo 770335 1303121 := bstep (se 2 (by rfl) ⟨488670, by rfl⟩ : syracuseStep 1303121 = 977341) B977341
theorem B1303249 : Blo 770335 1303249 := bstep (se 2 (by rfl) ⟨488718, by rfl⟩ : syracuseStep 1303249 = 977437) B977437
theorem B1303283 : Blo 770335 1303283 := bstep (se 1 (by rfl) ⟨977462, by rfl⟩ : syracuseStep 1303283 = 1954925) B1954925
theorem B1237825 : Blo 770335 1237825 := bstep (se 2 (by rfl) ⟨464184, by rfl⟩ : syracuseStep 1237825 = 928369) B928369
theorem B1172291 : Blo 770335 1172291 := bstep (se 1 (by rfl) ⟨879218, by rfl⟩ : syracuseStep 1172291 = 1758437) B1758437
theorem B1303411 : Blo 770335 1303411 := bstep (se 1 (by rfl) ⟨977558, by rfl⟩ : syracuseStep 1303411 = 1955117) B1955117
theorem B975827 : Blo 770335 975827 := bstep (se 1 (by rfl) ⟨731870, by rfl⟩ : syracuseStep 975827 = 1463741) B1463741
theorem B1303553 : Blo 770335 1303553 := bstep (se 2 (by rfl) ⟨488832, by rfl⟩ : syracuseStep 1303553 = 977665) B977665
theorem B1467409 : Blo 770335 1467409 := bstep (se 2 (by rfl) ⟨550278, by rfl⟩ : syracuseStep 1467409 = 1100557) B1100557
theorem B2090033 : Blo 770335 2090033 := bstep (se 2 (by rfl) ⟨783762, by rfl⟩ : syracuseStep 2090033 = 1567525) B1567525
theorem B1959025 : Blo 770335 1959025 := bstep (se 2 (by rfl) ⟨734634, by rfl⟩ : syracuseStep 1959025 = 1469269) B1469269
theorem B1303681 : Blo 770335 1303681 := bstep (se 2 (by rfl) ⟨488880, by rfl⟩ : syracuseStep 1303681 = 977761) B977761
theorem B2647181 : Blo 770335 2647181 := bstep (se 3 (by rfl) ⟨496346, by rfl⟩ : syracuseStep 2647181 = 992693) B992693
theorem B1303715 : Blo 770335 1303715 := bstep (se 1 (by rfl) ⟨977786, by rfl⟩ : syracuseStep 1303715 = 1955573) B1955573
theorem B1303843 : Blo 770335 1303843 := bstep (se 1 (by rfl) ⟨977882, by rfl⟩ : syracuseStep 1303843 = 1955765) B1955765
theorem B2647345 : Blo 770335 2647345 := bstep (se 2 (by rfl) ⟨992754, by rfl⟩ : syracuseStep 2647345 = 1985509) B1985509
theorem B1041745 : Blo 770335 1041745 := bstep (se 2 (by rfl) ⟨390654, by rfl⟩ : syracuseStep 1041745 = 781309) B781309
theorem B1959299 : Blo 770335 1959299 := bstep (se 1 (by rfl) ⟨1469474, by rfl⟩ : syracuseStep 1959299 = 2938949) B2938949
theorem B1467811 : Blo 770335 1467811 := bstep (se 1 (by rfl) ⟨1100858, by rfl⟩ : syracuseStep 1467811 = 2201717) B2201717
theorem B1303985 : Blo 770335 1303985 := bstep (se 2 (by rfl) ⟨488994, by rfl⟩ : syracuseStep 1303985 = 977989) B977989
theorem B4941253 : Blo 770335 4941253 := bstep (se 4 (by rfl) ⟨463242, by rfl⟩ : syracuseStep 4941253 = 926485) B926485
theorem B1467857 : Blo 770335 1467857 := bstep (se 2 (by rfl) ⟨550446, by rfl⟩ : syracuseStep 1467857 = 1100893) B1100893
theorem B1304113 : Blo 770335 1304113 := bstep (se 2 (by rfl) ⟨489042, by rfl⟩ : syracuseStep 1304113 = 978085) B978085
theorem B1959491 : Blo 770335 1959491 := bstep (se 1 (by rfl) ⟨1469618, by rfl⟩ : syracuseStep 1959491 = 2939237) B2939237
theorem B1304147 : Blo 770335 1304147 := bstep (se 1 (by rfl) ⟨978110, by rfl⟩ : syracuseStep 1304147 = 1956221) B1956221
theorem B2090605 : Blo 770335 2090605 := bstep (se 3 (by rfl) ⟨391988, by rfl⟩ : syracuseStep 2090605 = 783977) B783977
theorem B2385539 : Blo 770335 2385539 := bstep (se 1 (by rfl) ⟨1789154, by rfl⟩ : syracuseStep 2385539 = 3578309) B3578309
theorem B976531 : Blo 770335 976531 := bstep (se 1 (by rfl) ⟨732398, by rfl⟩ : syracuseStep 976531 = 1464797) B1464797
theorem B3303089 : Blo 770335 3303089 := bstep (se 2 (by rfl) ⟨1238658, by rfl⟩ : syracuseStep 3303089 = 2477317) B2477317
theorem B1238723 : Blo 770335 1238723 := bstep (se 1 (by rfl) ⟨929042, by rfl⟩ : syracuseStep 1238723 = 1858085) B1858085
theorem B1304275 : Blo 770335 1304275 := bstep (se 1 (by rfl) ⟨978206, by rfl⟩ : syracuseStep 1304275 = 1956413) B1956413
theorem B1468145 : Blo 770335 1468145 := bstep (se 2 (by rfl) ⟨550554, by rfl⟩ : syracuseStep 1468145 = 1101109) B1101109
theorem B976627 : Blo 770335 976627 := bstep (se 1 (by rfl) ⟨732470, by rfl⟩ : syracuseStep 976627 = 1464941) B1464941
theorem B2090755 : Blo 770335 2090755 := bstep (se 1 (by rfl) ⟨1568066, by rfl⟩ : syracuseStep 2090755 = 3136133) B3136133
theorem B1304417 : Blo 770335 1304417 := bstep (se 2 (by rfl) ⟨489156, by rfl⟩ : syracuseStep 1304417 = 978313) B978313
theorem B1238915 : Blo 770335 1238915 := bstep (se 1 (by rfl) ⟨929186, by rfl⟩ : syracuseStep 1238915 = 1858373) B1858373
theorem B1566641 : Blo 770335 1566641 := bstep (se 2 (by rfl) ⟨587490, by rfl⟩ : syracuseStep 1566641 = 1174981) B1174981
theorem B1304545 : Blo 770335 1304545 := bstep (se 2 (by rfl) ⟨489204, by rfl⟩ : syracuseStep 1304545 = 978409) B978409
theorem B1304579 : Blo 770335 1304579 := bstep (se 1 (by rfl) ⟨978434, by rfl⟩ : syracuseStep 1304579 = 1956869) B1956869
theorem B1173521 : Blo 770335 1173521 := bstep (se 2 (by rfl) ⟨440070, by rfl⟩ : syracuseStep 1173521 = 880141) B880141
theorem B1042465 : Blo 770335 1042465 := bstep (se 2 (by rfl) ⟨390924, by rfl⟩ : syracuseStep 1042465 = 781849) B781849
theorem B1304707 : Blo 770335 1304707 := bstep (se 1 (by rfl) ⟨978530, by rfl⟩ : syracuseStep 1304707 = 1957061) B1957061
theorem B977123 : Blo 770335 977123 := bstep (se 1 (by rfl) ⟨732842, by rfl⟩ : syracuseStep 977123 = 1465685) B1465685
theorem B25389283 : Blo 770335 25389283 := bstep (se 1 (by rfl) ⟨19041962, by rfl⟩ : syracuseStep 25389283 = 38083925) B38083925
theorem B1304849 : Blo 770335 1304849 := bstep (se 2 (by rfl) ⟨489318, by rfl⟩ : syracuseStep 1304849 = 978637) B978637
theorem B1304977 : Blo 770335 1304977 := bstep (se 2 (by rfl) ⟨489366, by rfl⟩ : syracuseStep 1304977 = 978733) B978733
theorem B1305011 : Blo 770335 1305011 := bstep (se 1 (by rfl) ⟨978758, by rfl⟩ : syracuseStep 1305011 = 1957517) B1957517
theorem B1468867 : Blo 770335 1468867 := bstep (se 1 (by rfl) ⟨1101650, by rfl⟩ : syracuseStep 1468867 = 2203301) B2203301
theorem B1305139 : Blo 770335 1305139 := bstep (se 1 (by rfl) ⟨978854, by rfl⟩ : syracuseStep 1305139 = 1957709) B1957709
theorem B1305281 : Blo 770335 1305281 := bstep (se 2 (by rfl) ⟨489480, by rfl⟩ : syracuseStep 1305281 = 978961) B978961
theorem B5073635 : Blo 770335 5073635 := bstep (se 1 (by rfl) ⟨3805226, by rfl⟩ : syracuseStep 5073635 = 7610453) B7610453
theorem B1305409 : Blo 770335 1305409 := bstep (se 2 (by rfl) ⟨489528, by rfl⟩ : syracuseStep 1305409 = 979057) B979057
theorem B2091857 : Blo 770335 2091857 := bstep (se 2 (by rfl) ⟨784446, by rfl⟩ : syracuseStep 2091857 = 1568893) B1568893
theorem B1239889 : Blo 770335 1239889 := bstep (se 2 (by rfl) ⟨464958, by rfl⟩ : syracuseStep 1239889 = 929917) B929917
theorem B1305443 : Blo 770335 1305443 := bstep (se 1 (by rfl) ⟨979082, by rfl⟩ : syracuseStep 1305443 = 1958165) B1958165
theorem B1469315 : Blo 770335 1469315 := bstep (se 1 (by rfl) ⟨1101986, by rfl⟩ : syracuseStep 1469315 = 2203973) B2203973
theorem B977827 : Blo 770335 977827 := bstep (se 1 (by rfl) ⟨733370, by rfl⟩ : syracuseStep 977827 = 1466741) B1466741
theorem B1305571 : Blo 770335 1305571 := bstep (se 1 (by rfl) ⟨979178, by rfl⟩ : syracuseStep 1305571 = 1958357) B1958357
theorem B977923 : Blo 770335 977923 := bstep (se 1 (by rfl) ⟨733442, by rfl⟩ : syracuseStep 977923 = 1466885) B1466885
theorem B1305713 : Blo 770335 1305713 := bstep (se 2 (by rfl) ⟨489642, by rfl⟩ : syracuseStep 1305713 = 979285) B979285
theorem B1469603 : Blo 770335 1469603 := bstep (se 1 (by rfl) ⟨1102202, by rfl⟩ : syracuseStep 1469603 = 2204405) B2204405
theorem B10022129 : Blo 770335 10022129 := bstep (se 2 (by rfl) ⟨3758298, by rfl⟩ : syracuseStep 10022129 = 7516597) B7516597
theorem B1305841 : Blo 770335 1305841 := bstep (se 2 (by rfl) ⟨489690, by rfl⟩ : syracuseStep 1305841 = 979381) B979381
theorem B1240337 : Blo 770335 1240337 := bstep (se 2 (by rfl) ⟨465126, by rfl⟩ : syracuseStep 1240337 = 930253) B930253
theorem B1305875 : Blo 770335 1305875 := bstep (se 1 (by rfl) ⟨979406, by rfl⟩ : syracuseStep 1305875 = 1958813) B1958813
theorem B6581573 : Blo 770335 6581573 := bstep (se 4 (by rfl) ⟨617022, by rfl⟩ : syracuseStep 6581573 = 1234045) B1234045
theorem B1306003 : Blo 770335 1306003 := bstep (se 1 (by rfl) ⟨979502, by rfl⟩ : syracuseStep 1306003 = 1959005) B1959005
theorem B5270989 : Blo 770335 5270989 := bstep (se 3 (by rfl) ⟨988310, by rfl⟩ : syracuseStep 5270989 = 1976621) B1976621
theorem B978419 : Blo 770335 978419 := bstep (se 1 (by rfl) ⟨733814, by rfl⟩ : syracuseStep 978419 = 1467629) B1467629
theorem B1306145 : Blo 770335 1306145 := bstep (se 2 (by rfl) ⟨489804, by rfl⟩ : syracuseStep 1306145 = 979609) B979609
theorem B3010097 : Blo 770335 3010097 := bstep (se 2 (by rfl) ⟨1128786, by rfl⟩ : syracuseStep 3010097 = 2257573) B2257573
theorem B1306273 : Blo 770335 1306273 := bstep (se 2 (by rfl) ⟨489852, by rfl⟩ : syracuseStep 1306273 = 979705) B979705
theorem B1306307 : Blo 770335 1306307 := bstep (se 1 (by rfl) ⟨979730, by rfl⟩ : syracuseStep 1306307 = 1959461) B1959461
theorem B1306435 : Blo 770335 1306435 := bstep (se 1 (by rfl) ⟨979826, by rfl⟩ : syracuseStep 1306435 = 1959653) B1959653
theorem B10579909 : Blo 770335 10579909 := bstep (se 4 (by rfl) ⟨991866, by rfl⟩ : syracuseStep 10579909 = 1983733) B1983733
theorem B1306577 : Blo 770335 1306577 := bstep (se 2 (by rfl) ⟨489966, by rfl⟩ : syracuseStep 1306577 = 979933) B979933
theorem B1044481 : Blo 770335 1044481 := bstep (se 2 (by rfl) ⟨391680, by rfl⟩ : syracuseStep 1044481 = 783361) B783361
theorem B3305549 : Blo 770335 3305549 := bstep (se 3 (by rfl) ⟨619790, by rfl⟩ : syracuseStep 3305549 = 1239581) B1239581
theorem B2977955 : Blo 770335 2977955 := bstep (se 1 (by rfl) ⟨2233466, by rfl⟩ : syracuseStep 2977955 = 4466933) B4466933
theorem B979123 : Blo 770335 979123 := bstep (se 1 (by rfl) ⟨734342, by rfl⟩ : syracuseStep 979123 = 1468685) B1468685
theorem B8810693 : Blo 770335 8810693 := bstep (se 4 (by rfl) ⟨826002, by rfl⟩ : syracuseStep 8810693 = 1652005) B1652005
theorem B2224369 : Blo 770335 2224369 := bstep (se 2 (by rfl) ⟨834138, by rfl⟩ : syracuseStep 2224369 = 1668277) B1668277
theorem B5861645 : Blo 770335 5861645 := bstep (se 3 (by rfl) ⟨1099058, by rfl⟩ : syracuseStep 5861645 = 2198117) B2198117
theorem B979219 : Blo 770335 979219 := bstep (se 1 (by rfl) ⟨734414, by rfl⟩ : syracuseStep 979219 = 1468829) B1468829
theorem B782627 : Blo 770335 782627 := bstep (se 1 (by rfl) ⟨586970, by rfl⟩ : syracuseStep 782627 = 1173941) B1173941
theorem B979715 : Blo 770335 979715 := bstep (se 1 (by rfl) ⟨734786, by rfl⟩ : syracuseStep 979715 = 1469573) B1469573
theorem B4944739 : Blo 770335 4944739 := bstep (se 1 (by rfl) ⟨3708554, by rfl⟩ : syracuseStep 4944739 = 7417109) B7417109
theorem B1733489 : Blo 770335 1733489 := bstep (se 2 (by rfl) ⟨650058, by rfl⟩ : syracuseStep 1733489 = 1300117) B1300117
theorem B1733507 : Blo 770335 1733507 := bstep (se 1 (by rfl) ⟨1300130, by rfl⟩ : syracuseStep 1733507 = 2600261) B2600261
theorem B1733777 : Blo 770335 1733777 := bstep (se 2 (by rfl) ⟨650166, by rfl⟩ : syracuseStep 1733777 = 1300333) B1300333
theorem B1733795 : Blo 770335 1733795 := bstep (se 1 (by rfl) ⟨1300346, by rfl⟩ : syracuseStep 1733795 = 2600693) B2600693
theorem B783523 : Blo 770335 783523 := bstep (se 1 (by rfl) ⟨587642, by rfl⟩ : syracuseStep 783523 = 1175285) B1175285
theorem B1045811 : Blo 770335 1045811 := bstep (se 1 (by rfl) ⟨784358, by rfl⟩ : syracuseStep 1045811 = 1568717) B1568717
theorem B3306865 : Blo 770335 3306865 := bstep (se 2 (by rfl) ⟨1240074, by rfl⟩ : syracuseStep 3306865 = 2480149) B2480149
theorem B1734065 : Blo 770335 1734065 := bstep (se 2 (by rfl) ⟨650274, by rfl⟩ : syracuseStep 1734065 = 1300549) B1300549
theorem B1734083 : Blo 770335 1734083 := bstep (se 1 (by rfl) ⟨1300562, by rfl⟩ : syracuseStep 1734083 = 2601125) B2601125
theorem B1046081 : Blo 770335 1046081 := bstep (se 2 (by rfl) ⟨392280, by rfl⟩ : syracuseStep 1046081 = 784561) B784561
theorem B1734353 : Blo 770335 1734353 := bstep (se 2 (by rfl) ⟨650382, by rfl⟩ : syracuseStep 1734353 = 1300765) B1300765
theorem B1734371 : Blo 770335 1734371 := bstep (se 1 (by rfl) ⟨1300778, by rfl⟩ : syracuseStep 1734371 = 2601557) B2601557
theorem B6256369 : Blo 770335 6256369 := bstep (se 2 (by rfl) ⟨2346138, by rfl⟩ : syracuseStep 6256369 = 4692277) B4692277
theorem B8025925 : Blo 770335 8025925 := bstep (se 4 (by rfl) ⟨752430, by rfl⟩ : syracuseStep 8025925 = 1504861) B1504861
theorem B2783089 : Blo 770335 2783089 := bstep (se 2 (by rfl) ⟨1043658, by rfl⟩ : syracuseStep 2783089 = 2087317) B2087317
theorem B4388741 : Blo 770335 4388741 := bstep (se 4 (by rfl) ⟨411444, by rfl⟩ : syracuseStep 4388741 = 822889) B822889
theorem B1734641 : Blo 770335 1734641 := bstep (se 2 (by rfl) ⟨650490, by rfl⟩ : syracuseStep 1734641 = 1300981) B1300981
theorem B1734659 : Blo 770335 1734659 := bstep (se 1 (by rfl) ⟨1300994, by rfl⟩ : syracuseStep 1734659 = 2601989) B2601989
theorem B1734929 : Blo 770335 1734929 := bstep (se 2 (by rfl) ⟨650598, by rfl⟩ : syracuseStep 1734929 = 1301197) B1301197
theorem B1734947 : Blo 770335 1734947 := bstep (se 1 (by rfl) ⟨1301210, by rfl⟩ : syracuseStep 1734947 = 2602421) B2602421
theorem B784739 : Blo 770335 784739 := bstep (se 1 (by rfl) ⟨588554, by rfl⟩ : syracuseStep 784739 = 1177109) B1177109
theorem B1931779 : Blo 770335 1931779 := bstep (se 1 (by rfl) ⟨1448834, by rfl⟩ : syracuseStep 1931779 = 2897669) B2897669
theorem B1735217 : Blo 770335 1735217 := bstep (se 2 (by rfl) ⟨650706, by rfl⟩ : syracuseStep 1735217 = 1301413) B1301413
theorem B15039029 : Blo 770335 15039029 := bstep (se 5 (by rfl) ⟨704954, by rfl⟩ : syracuseStep 15039029 = 1409909) B1409909
theorem B1735235 : Blo 770335 1735235 := bstep (se 1 (by rfl) ⟨1301426, by rfl⟩ : syracuseStep 1735235 = 2602853) B2602853
theorem B1735505 : Blo 770335 1735505 := bstep (se 2 (by rfl) ⟨650814, by rfl⟩ : syracuseStep 1735505 = 1301629) B1301629
theorem B1735523 : Blo 770335 1735523 := bstep (se 1 (by rfl) ⟨1301642, by rfl⟩ : syracuseStep 1735523 = 2603285) B2603285
theorem B2194381 : Blo 770335 2194381 := bstep (se 3 (by rfl) ⟨411446, by rfl⟩ : syracuseStep 2194381 = 822893) B822893
theorem B1735793 : Blo 770335 1735793 := bstep (se 2 (by rfl) ⟨650922, by rfl⟩ : syracuseStep 1735793 = 1301845) B1301845
theorem B5864561 : Blo 770335 5864561 := bstep (se 2 (by rfl) ⟨2199210, by rfl⟩ : syracuseStep 5864561 = 4398421) B4398421
theorem B1735811 : Blo 770335 1735811 := bstep (se 1 (by rfl) ⟨1301858, by rfl⟩ : syracuseStep 1735811 = 2603717) B2603717
theorem B2194609 : Blo 770335 2194609 := bstep (se 2 (by rfl) ⟨822978, by rfl⟩ : syracuseStep 2194609 = 1645957) B1645957
theorem B2194769 : Blo 770335 2194769 := bstep (se 2 (by rfl) ⟨823038, by rfl⟩ : syracuseStep 2194769 = 1646077) B1646077
theorem B1736081 : Blo 770335 1736081 := bstep (se 2 (by rfl) ⟨651030, by rfl⟩ : syracuseStep 1736081 = 1302061) B1302061
theorem B1736099 : Blo 770335 1736099 := bstep (se 1 (by rfl) ⟨1302074, by rfl⟩ : syracuseStep 1736099 = 2604149) B2604149
theorem B2194883 : Blo 770335 2194883 := bstep (se 1 (by rfl) ⟨1646162, by rfl⟩ : syracuseStep 2194883 = 3292325) B3292325
theorem B4816397 : Blo 770335 4816397 := bstep (se 3 (by rfl) ⟨903074, by rfl⟩ : syracuseStep 4816397 = 1806149) B1806149
theorem B13205105 : Blo 770335 13205105 := bstep (se 2 (by rfl) ⟨4951914, by rfl⟩ : syracuseStep 13205105 = 9903829) B9903829
theorem B1736369 : Blo 770335 1736369 := bstep (se 2 (by rfl) ⟨651138, by rfl⟩ : syracuseStep 1736369 = 1302277) B1302277
theorem B1736387 : Blo 770335 1736387 := bstep (se 1 (by rfl) ⟨1302290, by rfl⟩ : syracuseStep 1736387 = 2604581) B2604581
theorem B1736657 : Blo 770335 1736657 := bstep (se 2 (by rfl) ⟨651246, by rfl⟩ : syracuseStep 1736657 = 1302493) B1302493
theorem B1736675 : Blo 770335 1736675 := bstep (se 1 (by rfl) ⟨1302506, by rfl⟩ : syracuseStep 1736675 = 2605013) B2605013
theorem B1736729 : Blo 770335 1736729 := bstep (se 2 (by rfl) ⟨651273, by rfl⟩ : syracuseStep 1736729 = 1302547) B1302547
theorem B19005475 : Blo 770335 19005475 := bstep (se 1 (by rfl) ⟨14254106, by rfl⟩ : syracuseStep 19005475 = 28508213) B28508213
theorem B1736819 : Blo 770335 1736819 := bstep (se 1 (by rfl) ⟨1302614, by rfl⟩ : syracuseStep 1736819 = 2605229) B2605229
theorem B1736855 : Blo 770335 1736855 := bstep (se 1 (by rfl) ⟨1302641, by rfl⟩ : syracuseStep 1736855 = 2605283) B2605283
theorem B11108593 : Blo 770335 11108593 := bstep (se 2 (by rfl) ⟨4165722, by rfl⟩ : syracuseStep 11108593 = 8331445) B8331445
theorem B1737035 : Blo 770335 1737035 := bstep (se 1 (by rfl) ⟨1302776, by rfl⟩ : syracuseStep 1737035 = 2605553) B2605553
theorem B1737089 : Blo 770335 1737089 := bstep (se 2 (by rfl) ⟨651408, by rfl⟩ : syracuseStep 1737089 = 1302817) B1302817
theorem B2785715 : Blo 770335 2785715 := bstep (se 1 (by rfl) ⟨2089286, by rfl⟩ : syracuseStep 2785715 = 4178573) B4178573
theorem B5866019 : Blo 770335 5866019 := bstep (se 1 (by rfl) ⟨4399514, by rfl⟩ : syracuseStep 5866019 = 8799029) B8799029
theorem B10551883 : Blo 770335 10551883 := bstep (se 1 (by rfl) ⟨7913912, by rfl⟩ : syracuseStep 10551883 = 15827825) B15827825
theorem B1737305 : Blo 770335 1737305 := bstep (se 2 (by rfl) ⟨651489, by rfl⟩ : syracuseStep 1737305 = 1302979) B1302979
theorem B1737395 : Blo 770335 1737395 := bstep (se 1 (by rfl) ⟨1303046, by rfl⟩ : syracuseStep 1737395 = 2606093) B2606093
theorem B1737431 : Blo 770335 1737431 := bstep (se 1 (by rfl) ⟨1303073, by rfl⟩ : syracuseStep 1737431 = 2606147) B2606147
theorem B29721329 : Blo 770335 29721329 := bstep (se 2 (by rfl) ⟨11145498, by rfl⟩ : syracuseStep 29721329 = 22290997) B22290997
theorem B1737611 : Blo 770335 1737611 := bstep (se 1 (by rfl) ⟨1303208, by rfl⟩ : syracuseStep 1737611 = 2606417) B2606417
theorem B3900311 : Blo 770335 3900311 := bstep (se 1 (by rfl) ⟨2925233, by rfl⟩ : syracuseStep 3900311 = 5850467) B5850467
theorem B1737665 : Blo 770335 1737665 := bstep (se 2 (by rfl) ⟨651624, by rfl⟩ : syracuseStep 1737665 = 1303249) B1303249
theorem B5637221 : Blo 770335 5637221 := bstep (se 4 (by rfl) ⟨528489, by rfl⟩ : syracuseStep 5637221 = 1056979) B1056979
theorem B1737881 : Blo 770335 1737881 := bstep (se 2 (by rfl) ⟨651705, by rfl⟩ : syracuseStep 1737881 = 1303411) B1303411
theorem B2196659 : Blo 770335 2196659 := bstep (se 1 (by rfl) ⟨1647494, by rfl⟩ : syracuseStep 2196659 = 3294989) B3294989
theorem B3769523 : Blo 770335 3769523 := bstep (se 1 (by rfl) ⟨2827142, by rfl⟩ : syracuseStep 3769523 = 5654285) B5654285
theorem B2196683 : Blo 770335 2196683 := bstep (se 1 (by rfl) ⟨1647512, by rfl⟩ : syracuseStep 2196683 = 3295025) B3295025
theorem B1737971 : Blo 770335 1737971 := bstep (se 1 (by rfl) ⟨1303478, by rfl⟩ : syracuseStep 1737971 = 2606957) B2606957
theorem B1738007 : Blo 770335 1738007 := bstep (se 1 (by rfl) ⟨1303505, by rfl⟩ : syracuseStep 1738007 = 2607011) B2607011
theorem B1738187 : Blo 770335 1738187 := bstep (se 1 (by rfl) ⟨1303640, by rfl⟩ : syracuseStep 1738187 = 2607281) B2607281
theorem B1738241 : Blo 770335 1738241 := bstep (se 2 (by rfl) ⟨651840, by rfl⟩ : syracuseStep 1738241 = 1303681) B1303681
theorem B1672883 : Blo 770335 1672883 := bstep (se 1 (by rfl) ⟨1254662, by rfl⟩ : syracuseStep 1672883 = 2509325) B2509325
theorem B1738457 : Blo 770335 1738457 := bstep (se 2 (by rfl) ⟨651921, by rfl⟩ : syracuseStep 1738457 = 1303843) B1303843
theorem B1738547 : Blo 770335 1738547 := bstep (se 1 (by rfl) ⟨1303910, by rfl⟩ : syracuseStep 1738547 = 2607821) B2607821
theorem B1738583 : Blo 770335 1738583 := bstep (se 1 (by rfl) ⟨1303937, by rfl⟩ : syracuseStep 1738583 = 2607875) B2607875
theorem B25692005 : Blo 770335 25692005 := bstep (se 4 (by rfl) ⟨2408625, by rfl⟩ : syracuseStep 25692005 = 4817251) B4817251
theorem B6588337 : Blo 770335 6588337 := bstep (se 2 (by rfl) ⟨2470626, by rfl⟩ : syracuseStep 6588337 = 4941253) B4941253
theorem B2197469 : Blo 770335 2197469 := bstep (se 3 (by rfl) ⟨412025, by rfl⟩ : syracuseStep 2197469 = 824051) B824051
theorem B1738763 : Blo 770335 1738763 := bstep (se 1 (by rfl) ⟨1304072, by rfl⟩ : syracuseStep 1738763 = 2608145) B2608145
theorem B1738817 : Blo 770335 1738817 := bstep (se 2 (by rfl) ⟨652056, by rfl⟩ : syracuseStep 1738817 = 1304113) B1304113
theorem B2787473 : Blo 770335 2787473 := bstep (se 2 (by rfl) ⟨1045302, by rfl⟩ : syracuseStep 2787473 = 2090605) B2090605
theorem B2230465 : Blo 770335 2230465 := bstep (se 2 (by rfl) ⟨836424, by rfl⟩ : syracuseStep 2230465 = 1672849) B1672849
theorem B1739033 : Blo 770335 1739033 := bstep (se 2 (by rfl) ⟨652137, by rfl⟩ : syracuseStep 1739033 = 1304275) B1304275
theorem B1739123 : Blo 770335 1739123 := bstep (se 1 (by rfl) ⟨1304342, by rfl⟩ : syracuseStep 1739123 = 2608685) B2608685
theorem B1739159 : Blo 770335 1739159 := bstep (se 1 (by rfl) ⟨1304369, by rfl⟩ : syracuseStep 1739159 = 2608739) B2608739
theorem B9406937 : Blo 770335 9406937 := bstep (se 2 (by rfl) ⟨3527601, by rfl⟩ : syracuseStep 9406937 = 7055203) B7055203
theorem B4393547 : Blo 770335 4393547 := bstep (se 1 (by rfl) ⟨3295160, by rfl⟩ : syracuseStep 4393547 = 6590321) B6590321
theorem B1739339 : Blo 770335 1739339 := bstep (se 1 (by rfl) ⟨1304504, by rfl⟩ : syracuseStep 1739339 = 2609009) B2609009
theorem B1739393 : Blo 770335 1739393 := bstep (se 2 (by rfl) ⟨652272, by rfl⟩ : syracuseStep 1739393 = 1304545) B1304545
theorem B4688563 : Blo 770335 4688563 := bstep (se 1 (by rfl) ⟨3516422, by rfl⟩ : syracuseStep 4688563 = 7032845) B7032845
theorem B1739609 : Blo 770335 1739609 := bstep (se 2 (by rfl) ⟨652353, by rfl⟩ : syracuseStep 1739609 = 1304707) B1304707
theorem B7441253 : Blo 770335 7441253 := bstep (se 4 (by rfl) ⟨697617, by rfl⟩ : syracuseStep 7441253 = 1395235) B1395235
theorem B1739699 : Blo 770335 1739699 := bstep (se 1 (by rfl) ⟨1304774, by rfl⟩ : syracuseStep 1739699 = 2609549) B2609549
theorem B1739735 : Blo 770335 1739735 := bstep (se 1 (by rfl) ⟨1304801, by rfl⟩ : syracuseStep 1739735 = 2609603) B2609603
theorem B33852377 : Blo 770335 33852377 := bstep (se 2 (by rfl) ⟨12694641, by rfl⟩ : syracuseStep 33852377 = 25389283) B25389283
theorem B1674263 : Blo 770335 1674263 := bstep (se 1 (by rfl) ⟨1255697, by rfl⟩ : syracuseStep 1674263 = 2511395) B2511395
theorem B1739915 : Blo 770335 1739915 := bstep (se 1 (by rfl) ⟨1304936, by rfl⟩ : syracuseStep 1739915 = 2609873) B2609873
theorem B1739969 : Blo 770335 1739969 := bstep (se 2 (by rfl) ⟨652488, by rfl⟩ : syracuseStep 1739969 = 1304977) B1304977
theorem B1740185 : Blo 770335 1740185 := bstep (se 2 (by rfl) ⟨652569, by rfl⟩ : syracuseStep 1740185 = 1305139) B1305139
theorem B2788829 : Blo 770335 2788829 := bstep (se 3 (by rfl) ⟨522905, by rfl⟩ : syracuseStep 2788829 = 1045811) B1045811
theorem B1740275 : Blo 770335 1740275 := bstep (se 1 (by rfl) ⟨1305206, by rfl⟩ : syracuseStep 1740275 = 2610413) B2610413
theorem B1740311 : Blo 770335 1740311 := bstep (se 1 (by rfl) ⟨1305233, by rfl⟩ : syracuseStep 1740311 = 2610467) B2610467
theorem B1740491 : Blo 770335 1740491 := bstep (se 1 (by rfl) ⟨1305368, by rfl⟩ : syracuseStep 1740491 = 2610737) B2610737
theorem B2199257 : Blo 770335 2199257 := bstep (se 2 (by rfl) ⟨824721, by rfl⟩ : syracuseStep 2199257 = 1649443) B1649443
theorem B1740545 : Blo 770335 1740545 := bstep (se 2 (by rfl) ⟨652704, by rfl⟩ : syracuseStep 1740545 = 1305409) B1305409
theorem B1740761 : Blo 770335 1740761 := bstep (se 2 (by rfl) ⟨652785, by rfl⟩ : syracuseStep 1740761 = 1305571) B1305571
theorem B2199575 : Blo 770335 2199575 := bstep (se 1 (by rfl) ⟨1649681, by rfl⟩ : syracuseStep 2199575 = 3299363) B3299363
theorem B1740851 : Blo 770335 1740851 := bstep (se 1 (by rfl) ⟨1305638, by rfl⟩ : syracuseStep 1740851 = 2611277) B2611277
theorem B1740887 : Blo 770335 1740887 := bstep (se 1 (by rfl) ⟨1305665, by rfl⟩ : syracuseStep 1740887 = 2611331) B2611331
theorem B2789549 : Blo 770335 2789549 := bstep (se 3 (by rfl) ⟨523040, by rfl⟩ : syracuseStep 2789549 = 1046081) B1046081
theorem B1741067 : Blo 770335 1741067 := bstep (se 1 (by rfl) ⟨1305800, by rfl⟩ : syracuseStep 1741067 = 2611601) B2611601
theorem B1741121 : Blo 770335 1741121 := bstep (se 2 (by rfl) ⟨652920, by rfl⟩ : syracuseStep 1741121 = 1305841) B1305841
theorem B3903875 : Blo 770335 3903875 := bstep (se 1 (by rfl) ⟨2927906, by rfl⟩ : syracuseStep 3903875 = 5855813) B5855813
theorem B1741337 : Blo 770335 1741337 := bstep (se 2 (by rfl) ⟨653001, by rfl⟩ : syracuseStep 1741337 = 1306003) B1306003
theorem B4690507 : Blo 770335 4690507 := bstep (se 1 (by rfl) ⟨3517880, by rfl⟩ : syracuseStep 4690507 = 7035761) B7035761
theorem B1741427 : Blo 770335 1741427 := bstep (se 1 (by rfl) ⟨1306070, by rfl⟩ : syracuseStep 1741427 = 2612141) B2612141
theorem B823927 : Blo 770335 823927 := bstep (se 1 (by rfl) ⟨617945, by rfl⟩ : syracuseStep 823927 = 1235891) B1235891
theorem B1741463 : Blo 770335 1741463 := bstep (se 1 (by rfl) ⟨1306097, by rfl⟩ : syracuseStep 1741463 = 2612195) B2612195
theorem B2200385 : Blo 770335 2200385 := bstep (se 2 (by rfl) ⟨825144, by rfl⟩ : syracuseStep 2200385 = 1650289) B1650289
theorem B1741643 : Blo 770335 1741643 := bstep (se 1 (by rfl) ⟨1306232, by rfl⟩ : syracuseStep 1741643 = 2612465) B2612465
theorem B1741697 : Blo 770335 1741697 := bstep (se 2 (by rfl) ⟨653136, by rfl⟩ : syracuseStep 1741697 = 1306273) B1306273
theorem B1741913 : Blo 770335 1741913 := bstep (se 2 (by rfl) ⟨653217, by rfl⟩ : syracuseStep 1741913 = 1306435) B1306435
theorem B1742003 : Blo 770335 1742003 := bstep (se 1 (by rfl) ⟨1306502, by rfl⟩ : syracuseStep 1742003 = 2613005) B2613005
theorem B13407437 : Blo 770335 13407437 := bstep (se 3 (by rfl) ⟨2513894, by rfl⟩ : syracuseStep 13407437 = 5027789) B5027789
theorem B1742039 : Blo 770335 1742039 := bstep (se 1 (by rfl) ⟨1306529, by rfl⟩ : syracuseStep 1742039 = 2613059) B2613059
theorem B4461925 : Blo 770335 4461925 := bstep (se 4 (by rfl) ⟨418305, by rfl⟩ : syracuseStep 4461925 = 836611) B836611
theorem B1742219 : Blo 770335 1742219 := bstep (se 1 (by rfl) ⟨1306664, by rfl⟩ : syracuseStep 1742219 = 2613329) B2613329
theorem B824747 : Blo 770335 824747 := bstep (se 1 (by rfl) ⟨618560, by rfl⟩ : syracuseStep 824747 = 1237121) B1237121
theorem B3348119 : Blo 770335 3348119 := bstep (se 1 (by rfl) ⟨2511089, by rfl⟩ : syracuseStep 3348119 = 5022179) B5022179
theorem B5871365 : Blo 770335 5871365 := bstep (se 4 (by rfl) ⟨550440, by rfl⟩ : syracuseStep 5871365 = 1100881) B1100881
theorem B1251545 : Blo 770335 1251545 := bstep (se 2 (by rfl) ⟨469329, by rfl⟩ : syracuseStep 1251545 = 938659) B938659
theorem B2202059 : Blo 770335 2202059 := bstep (se 1 (by rfl) ⟨1651544, by rfl⟩ : syracuseStep 2202059 = 3303089) B3303089
theorem B825815 : Blo 770335 825815 := bstep (se 1 (by rfl) ⟨619361, by rfl⟩ : syracuseStep 825815 = 1238723) B1238723
theorem B6592985 : Blo 770335 6592985 := bstep (se 2 (by rfl) ⟨2472369, by rfl⟩ : syracuseStep 6592985 = 4944739) B4944739
theorem B1645505 : Blo 770335 1645505 := bstep (se 2 (by rfl) ⟨617064, by rfl⟩ : syracuseStep 1645505 = 1234129) B1234129
theorem B826891 : Blo 770335 826891 := bstep (se 1 (by rfl) ⟨620168, by rfl⟩ : syracuseStep 826891 = 1240337) B1240337
theorem B2006731 : Blo 770335 2006731 := bstep (se 1 (by rfl) ⟨1505048, by rfl⟩ : syracuseStep 2006731 = 3010097) B3010097
theorem B2203357 : Blo 770335 2203357 := bstep (se 3 (by rfl) ⟨413129, by rfl⟩ : syracuseStep 2203357 = 826259) B826259
theorem B1646401 : Blo 770335 1646401 := bstep (se 2 (by rfl) ⟨617400, by rfl⟩ : syracuseStep 1646401 = 1234801) B1234801
theorem B3710785 : Blo 770335 3710785 := bstep (se 2 (by rfl) ⟨1391544, by rfl⟩ : syracuseStep 3710785 = 2783089) B2783089
theorem B3907601 : Blo 770335 3907601 := bstep (se 2 (by rfl) ⟨1465350, by rfl⟩ : syracuseStep 3907601 = 2930701) B2930701
theorem B2203699 : Blo 770335 2203699 := bstep (se 1 (by rfl) ⟨1652774, by rfl⟩ : syracuseStep 2203699 = 3305549) B3305549
theorem B4464715 : Blo 770335 4464715 := bstep (se 1 (by rfl) ⟨3348536, by rfl⟩ : syracuseStep 4464715 = 6697073) B6697073
theorem B5873795 : Blo 770335 5873795 := bstep (se 1 (by rfl) ⟨4405346, by rfl⟩ : syracuseStep 5873795 = 8810693) B8810693
theorem B1646743 : Blo 770335 1646743 := bstep (se 1 (by rfl) ⟨1235057, by rfl⟩ : syracuseStep 1646743 = 2470115) B2470115
theorem B3907763 : Blo 770335 3907763 := bstep (se 1 (by rfl) ⟨2930822, by rfl⟩ : syracuseStep 3907763 = 5861645) B5861645
theorem B1155545 : Blo 770335 1155545 := bstep (se 2 (by rfl) ⟨433329, by rfl⟩ : syracuseStep 1155545 = 866659) B866659
theorem B1155659 : Blo 770335 1155659 := bstep (se 1 (by rfl) ⟨866744, by rfl⟩ : syracuseStep 1155659 = 1733489) B1733489
theorem B1155671 : Blo 770335 1155671 := bstep (se 1 (by rfl) ⟨866753, by rfl⟩ : syracuseStep 1155671 = 1733507) B1733507
theorem B1155737 : Blo 770335 1155737 := bstep (se 2 (by rfl) ⟨433401, by rfl⟩ : syracuseStep 1155737 = 866803) B866803
theorem B5579441 : Blo 770335 5579441 := bstep (se 2 (by rfl) ⟨2092290, by rfl⟩ : syracuseStep 5579441 = 4184581) B4184581
theorem B1647307 : Blo 770335 1647307 := bstep (se 1 (by rfl) ⟨1235480, by rfl⟩ : syracuseStep 1647307 = 2470961) B2470961
theorem B1155851 : Blo 770335 1155851 := bstep (se 1 (by rfl) ⟨866888, by rfl⟩ : syracuseStep 1155851 = 1733777) B1733777
theorem B1155863 : Blo 770335 1155863 := bstep (se 1 (by rfl) ⟨866897, by rfl⟩ : syracuseStep 1155863 = 1733795) B1733795
theorem B1155929 : Blo 770335 1155929 := bstep (se 2 (by rfl) ⟨433473, by rfl⟩ : syracuseStep 1155929 = 866947) B866947
theorem B7054181 : Blo 770335 7054181 := bstep (se 4 (by rfl) ⟨661329, by rfl⟩ : syracuseStep 7054181 = 1322659) B1322659
theorem B5808997 : Blo 770335 5808997 := bstep (se 4 (by rfl) ⟨544593, by rfl⟩ : syracuseStep 5808997 = 1089187) B1089187
theorem B1156043 : Blo 770335 1156043 := bstep (se 1 (by rfl) ⟨867032, by rfl⟩ : syracuseStep 1156043 = 1734065) B1734065
theorem B1156055 : Blo 770335 1156055 := bstep (se 1 (by rfl) ⟨867041, by rfl⟩ : syracuseStep 1156055 = 1734083) B1734083
theorem B4957145 : Blo 770335 4957145 := bstep (se 2 (by rfl) ⟨1858929, by rfl⟩ : syracuseStep 4957145 = 3717859) B3717859
theorem B2204633 : Blo 770335 2204633 := bstep (se 2 (by rfl) ⟨826737, by rfl⟩ : syracuseStep 2204633 = 1653475) B1653475
theorem B1156121 : Blo 770335 1156121 := bstep (se 2 (by rfl) ⟨433545, by rfl⟩ : syracuseStep 1156121 = 867091) B867091
theorem B1156235 : Blo 770335 1156235 := bstep (se 1 (by rfl) ⟨867176, by rfl⟩ : syracuseStep 1156235 = 1734353) B1734353
theorem B1156247 : Blo 770335 1156247 := bstep (se 1 (by rfl) ⟨867185, by rfl⟩ : syracuseStep 1156247 = 1734371) B1734371
theorem B1156313 : Blo 770335 1156313 := bstep (se 2 (by rfl) ⟨433617, by rfl⟩ : syracuseStep 1156313 = 867235) B867235
theorem B2925827 : Blo 770335 2925827 := bstep (se 1 (by rfl) ⟨2194370, by rfl⟩ : syracuseStep 2925827 = 4388741) B4388741
theorem B33367301 : Blo 770335 33367301 := bstep (se 4 (by rfl) ⟨3128184, by rfl⟩ : syracuseStep 33367301 = 6256369) B6256369
theorem B2925841 : Blo 770335 2925841 := bstep (se 2 (by rfl) ⟨1097190, by rfl⟩ : syracuseStep 2925841 = 2194381) B2194381
theorem B1156427 : Blo 770335 1156427 := bstep (se 1 (by rfl) ⟨867320, by rfl⟩ : syracuseStep 1156427 = 1734641) B1734641
theorem B1156439 : Blo 770335 1156439 := bstep (se 1 (by rfl) ⟨867329, by rfl⟩ : syracuseStep 1156439 = 1734659) B1734659
theorem B11150693 : Blo 770335 11150693 := bstep (se 4 (by rfl) ⟨1045377, by rfl⟩ : syracuseStep 11150693 = 2090755) B2090755
theorem B1156505 : Blo 770335 1156505 := bstep (se 2 (by rfl) ⟨433689, by rfl⟩ : syracuseStep 1156505 = 867379) B867379
theorem B1156619 : Blo 770335 1156619 := bstep (se 1 (by rfl) ⟨867464, by rfl⟩ : syracuseStep 1156619 = 1734929) B1734929
theorem B1156631 : Blo 770335 1156631 := bstep (se 1 (by rfl) ⟨867473, by rfl⟩ : syracuseStep 1156631 = 1734947) B1734947
theorem B2926145 : Blo 770335 2926145 := bstep (se 2 (by rfl) ⟨1097304, by rfl⟩ : syracuseStep 2926145 = 2194609) B2194609
theorem B1156697 : Blo 770335 1156697 := bstep (se 2 (by rfl) ⟨433761, by rfl⟩ : syracuseStep 1156697 = 867523) B867523
theorem B1156811 : Blo 770335 1156811 := bstep (se 1 (by rfl) ⟨867608, by rfl⟩ : syracuseStep 1156811 = 1735217) B1735217
theorem B1156823 : Blo 770335 1156823 := bstep (se 1 (by rfl) ⟨867617, by rfl⟩ : syracuseStep 1156823 = 1735235) B1735235
theorem B1156889 : Blo 770335 1156889 := bstep (se 2 (by rfl) ⟨433833, by rfl⟩ : syracuseStep 1156889 = 867667) B867667
theorem B1157003 : Blo 770335 1157003 := bstep (se 1 (by rfl) ⟨867752, by rfl⟩ : syracuseStep 1157003 = 1735505) B1735505
theorem B1157015 : Blo 770335 1157015 := bstep (se 1 (by rfl) ⟨867761, by rfl⟩ : syracuseStep 1157015 = 1735523) B1735523
theorem B1157081 : Blo 770335 1157081 := bstep (se 2 (by rfl) ⟨433905, by rfl⟩ : syracuseStep 1157081 = 867811) B867811
theorem B1648691 : Blo 770335 1648691 := bstep (se 1 (by rfl) ⟨1236518, by rfl⟩ : syracuseStep 1648691 = 2473037) B2473037
theorem B1157195 : Blo 770335 1157195 := bstep (se 1 (by rfl) ⟨867896, by rfl⟩ : syracuseStep 1157195 = 1735793) B1735793
theorem B3909707 : Blo 770335 3909707 := bstep (se 1 (by rfl) ⟨2932280, by rfl⟩ : syracuseStep 3909707 = 5864561) B5864561
theorem B1157207 : Blo 770335 1157207 := bstep (se 1 (by rfl) ⟨867905, by rfl⟩ : syracuseStep 1157207 = 1735811) B1735811
theorem B1321099 : Blo 770335 1321099 := bstep (se 1 (by rfl) ⟨990824, by rfl⟩ : syracuseStep 1321099 = 1981649) B1981649
theorem B1157273 : Blo 770335 1157273 := bstep (se 2 (by rfl) ⟨433977, by rfl⟩ : syracuseStep 1157273 = 867955) B867955
theorem B1648793 : Blo 770335 1648793 := bstep (se 2 (by rfl) ⟨618297, by rfl⟩ : syracuseStep 1648793 = 1236595) B1236595
theorem B2926813 : Blo 770335 2926813 := bstep (se 3 (by rfl) ⟨548777, by rfl⟩ : syracuseStep 2926813 = 1097555) B1097555
theorem B1157387 : Blo 770335 1157387 := bstep (se 1 (by rfl) ⟨868040, by rfl⟩ : syracuseStep 1157387 = 1736081) B1736081
theorem B1157399 : Blo 770335 1157399 := bstep (se 1 (by rfl) ⟨868049, by rfl⟩ : syracuseStep 1157399 = 1736099) B1736099
theorem B1157465 : Blo 770335 1157465 := bstep (se 2 (by rfl) ⟨434049, by rfl⟩ : syracuseStep 1157465 = 868099) B868099
theorem B1157579 : Blo 770335 1157579 := bstep (se 1 (by rfl) ⟨868184, by rfl⟩ : syracuseStep 1157579 = 1736369) B1736369
theorem B1157591 : Blo 770335 1157591 := bstep (se 1 (by rfl) ⟨868193, by rfl⟩ : syracuseStep 1157591 = 1736387) B1736387
theorem B1649153 : Blo 770335 1649153 := bstep (se 2 (by rfl) ⟨618432, by rfl⟩ : syracuseStep 1649153 = 1236865) B1236865
theorem B1157657 : Blo 770335 1157657 := bstep (se 2 (by rfl) ⟨434121, by rfl⟩ : syracuseStep 1157657 = 868243) B868243
theorem B3713629 : Blo 770335 3713629 := bstep (se 3 (by rfl) ⟨696305, by rfl⟩ : syracuseStep 3713629 = 1392611) B1392611
theorem B1157771 : Blo 770335 1157771 := bstep (se 1 (by rfl) ⟨868328, by rfl⟩ : syracuseStep 1157771 = 1736657) B1736657
theorem B1157783 : Blo 770335 1157783 := bstep (se 1 (by rfl) ⟨868337, by rfl⟩ : syracuseStep 1157783 = 1736675) B1736675
theorem B1157849 : Blo 770335 1157849 := bstep (se 2 (by rfl) ⟨434193, by rfl⟩ : syracuseStep 1157849 = 868387) B868387
theorem B928523 : Blo 770335 928523 := bstep (se 1 (by rfl) ⟨696392, by rfl⟩ : syracuseStep 928523 = 1392785) B1392785
theorem B1157963 : Blo 770335 1157963 := bstep (se 1 (by rfl) ⟨868472, by rfl⟩ : syracuseStep 1157963 = 1736945) B1736945
theorem B1157975 : Blo 770335 1157975 := bstep (se 1 (by rfl) ⟨868481, by rfl⟩ : syracuseStep 1157975 = 1736963) B1736963
theorem B1158041 : Blo 770335 1158041 := bstep (se 2 (by rfl) ⟨434265, by rfl⟩ : syracuseStep 1158041 = 868531) B868531
theorem B2599883 : Blo 770335 2599883 := bstep (se 1 (by rfl) ⟨1949912, by rfl⟩ : syracuseStep 2599883 = 3899825) B3899825
theorem B1158155 : Blo 770335 1158155 := bstep (se 1 (by rfl) ⟨868616, by rfl⟩ : syracuseStep 1158155 = 1737233) B1737233
theorem B1158167 : Blo 770335 1158167 := bstep (se 1 (by rfl) ⟨868625, by rfl⟩ : syracuseStep 1158167 = 1737251) B1737251
theorem B1485899 : Blo 770335 1485899 := bstep (se 1 (by rfl) ⟨1114424, by rfl⟩ : syracuseStep 1485899 = 2228849) B2228849
theorem B1158233 : Blo 770335 1158233 := bstep (se 2 (by rfl) ⟨434337, by rfl⟩ : syracuseStep 1158233 = 868675) B868675
theorem B1158347 : Blo 770335 1158347 := bstep (se 1 (by rfl) ⟨868760, by rfl⟩ : syracuseStep 1158347 = 1737521) B1737521
theorem B1158359 : Blo 770335 1158359 := bstep (se 1 (by rfl) ⟨868769, by rfl⟩ : syracuseStep 1158359 = 1737539) B1737539
theorem B1649879 : Blo 770335 1649879 := bstep (se 1 (by rfl) ⟨1237409, by rfl⟩ : syracuseStep 1649879 = 2474819) B2474819
theorem B2600153 : Blo 770335 2600153 := bstep (se 2 (by rfl) ⟨975057, by rfl⟩ : syracuseStep 2600153 = 1950115) B1950115
theorem B13348081 : Blo 770335 13348081 := bstep (se 2 (by rfl) ⟨5005530, by rfl⟩ : syracuseStep 13348081 = 10011061) B10011061
theorem B1158425 : Blo 770335 1158425 := bstep (se 2 (by rfl) ⟨434409, by rfl⟩ : syracuseStep 1158425 = 868819) B868819
theorem B1158539 : Blo 770335 1158539 := bstep (se 1 (by rfl) ⟨868904, by rfl⟩ : syracuseStep 1158539 = 1737809) B1737809
theorem B1158551 : Blo 770335 1158551 := bstep (se 1 (by rfl) ⟨868913, by rfl⟩ : syracuseStep 1158551 = 1737827) B1737827
theorem B5877197 : Blo 770335 5877197 := bstep (se 3 (by rfl) ⟨1101974, by rfl⟩ : syracuseStep 5877197 = 2203949) B2203949
theorem B2928089 : Blo 770335 2928089 := bstep (se 2 (by rfl) ⟨1098033, by rfl⟩ : syracuseStep 2928089 = 2196067) B2196067
theorem B1158617 : Blo 770335 1158617 := bstep (se 2 (by rfl) ⟨434481, by rfl⟩ : syracuseStep 1158617 = 868963) B868963
theorem B1158731 : Blo 770335 1158731 := bstep (se 1 (by rfl) ⟨869048, by rfl⟩ : syracuseStep 1158731 = 1738097) B1738097
theorem B1158743 : Blo 770335 1158743 := bstep (se 1 (by rfl) ⟨869057, by rfl⟩ : syracuseStep 1158743 = 1738115) B1738115
theorem B1158809 : Blo 770335 1158809 := bstep (se 2 (by rfl) ⟨434553, by rfl⟩ : syracuseStep 1158809 = 869107) B869107
theorem B4697779 : Blo 770335 4697779 := bstep (se 1 (by rfl) ⟨3523334, by rfl⟩ : syracuseStep 4697779 = 7046669) B7046669
theorem B1158923 : Blo 770335 1158923 := bstep (se 1 (by rfl) ⟨869192, by rfl⟩ : syracuseStep 1158923 = 1738385) B1738385
theorem B1158935 : Blo 770335 1158935 := bstep (se 1 (by rfl) ⟨869201, by rfl⟩ : syracuseStep 1158935 = 1738403) B1738403
theorem B3911489 : Blo 770335 3911489 := bstep (se 2 (by rfl) ⟨1466808, by rfl⟩ : syracuseStep 3911489 = 2933617) B2933617
theorem B1322839 : Blo 770335 1322839 := bstep (se 1 (by rfl) ⟨992129, by rfl⟩ : syracuseStep 1322839 = 1984259) B1984259
theorem B1159001 : Blo 770335 1159001 := bstep (se 2 (by rfl) ⟨434625, by rfl⟩ : syracuseStep 1159001 = 869251) B869251
theorem B2600855 : Blo 770335 2600855 := bstep (se 1 (by rfl) ⟨1950641, by rfl⟩ : syracuseStep 2600855 = 3901283) B3901283
theorem B5877683 : Blo 770335 5877683 := bstep (se 1 (by rfl) ⟨4408262, by rfl⟩ : syracuseStep 5877683 = 8816525) B8816525
theorem B1159115 : Blo 770335 1159115 := bstep (se 1 (by rfl) ⟨869336, by rfl⟩ : syracuseStep 1159115 = 1738673) B1738673
theorem B1159127 : Blo 770335 1159127 := bstep (se 1 (by rfl) ⟨869345, by rfl⟩ : syracuseStep 1159127 = 1738691) B1738691
theorem B12496913 : Blo 770335 12496913 := bstep (se 2 (by rfl) ⟨4686342, by rfl⟩ : syracuseStep 12496913 = 9372685) B9372685
theorem B1159193 : Blo 770335 1159193 := bstep (se 2 (by rfl) ⟨434697, by rfl⟩ : syracuseStep 1159193 = 869395) B869395
theorem B1650775 : Blo 770335 1650775 := bstep (se 1 (by rfl) ⟨1238081, by rfl⟩ : syracuseStep 1650775 = 2476163) B2476163
theorem B1159307 : Blo 770335 1159307 := bstep (se 1 (by rfl) ⟨869480, by rfl⟩ : syracuseStep 1159307 = 1738961) B1738961
theorem B1159319 : Blo 770335 1159319 := bstep (se 1 (by rfl) ⟨869489, by rfl⟩ : syracuseStep 1159319 = 1738979) B1738979
theorem B1159385 : Blo 770335 1159385 := bstep (se 2 (by rfl) ⟨434769, by rfl⟩ : syracuseStep 1159385 = 869539) B869539
theorem B1323289 : Blo 770335 1323289 := bstep (se 2 (by rfl) ⟨496233, by rfl⟩ : syracuseStep 1323289 = 992467) B992467
theorem B1159499 : Blo 770335 1159499 := bstep (se 1 (by rfl) ⟨869624, by rfl⟩ : syracuseStep 1159499 = 1739249) B1739249
theorem B1159511 : Blo 770335 1159511 := bstep (se 1 (by rfl) ⟨869633, by rfl⟩ : syracuseStep 1159511 = 1739267) B1739267
theorem B1159577 : Blo 770335 1159577 := bstep (se 2 (by rfl) ⟨434841, by rfl⟩ : syracuseStep 1159577 = 869683) B869683
theorem B2601395 : Blo 770335 2601395 := bstep (se 1 (by rfl) ⟨1951046, by rfl⟩ : syracuseStep 2601395 = 3902093) B3902093
theorem B13218227 : Blo 770335 13218227 := bstep (se 1 (by rfl) ⟨9913670, by rfl⟩ : syracuseStep 13218227 = 19827341) B19827341
theorem B1388993 : Blo 770335 1388993 := bstep (se 2 (by rfl) ⟨520872, by rfl⟩ : syracuseStep 1388993 = 1041745) B1041745
theorem B1159691 : Blo 770335 1159691 := bstep (se 1 (by rfl) ⟨869768, by rfl⟩ : syracuseStep 1159691 = 1739537) B1739537
theorem B1159703 : Blo 770335 1159703 := bstep (se 1 (by rfl) ⟨869777, by rfl⟩ : syracuseStep 1159703 = 1739555) B1739555
theorem B1159769 : Blo 770335 1159769 := bstep (se 2 (by rfl) ⟨434913, by rfl⟩ : syracuseStep 1159769 = 869827) B869827
theorem B4698755 : Blo 770335 4698755 := bstep (se 1 (by rfl) ⟨3524066, by rfl⟩ : syracuseStep 4698755 = 7048133) B7048133
theorem B2601665 : Blo 770335 2601665 := bstep (se 2 (by rfl) ⟨975624, by rfl⟩ : syracuseStep 2601665 = 1951249) B1951249
theorem B1159883 : Blo 770335 1159883 := bstep (se 1 (by rfl) ⟨869912, by rfl⟩ : syracuseStep 1159883 = 1739825) B1739825
theorem B1159895 : Blo 770335 1159895 := bstep (se 1 (by rfl) ⟨869921, by rfl⟩ : syracuseStep 1159895 = 1739843) B1739843
theorem B1159961 : Blo 770335 1159961 := bstep (se 2 (by rfl) ⟨434985, by rfl⟩ : syracuseStep 1159961 = 869971) B869971
theorem B3126109 : Blo 770335 3126109 := bstep (se 3 (by rfl) ⟨586145, by rfl⟩ : syracuseStep 3126109 = 1172291) B1172291
theorem B1651595 : Blo 770335 1651595 := bstep (se 1 (by rfl) ⟨1238696, by rfl⟩ : syracuseStep 1651595 = 2477393) B2477393
theorem B1160075 : Blo 770335 1160075 := bstep (se 1 (by rfl) ⟨870056, by rfl⟩ : syracuseStep 1160075 = 1740113) B1740113
theorem B1160087 : Blo 770335 1160087 := bstep (se 1 (by rfl) ⟨870065, by rfl⟩ : syracuseStep 1160087 = 1740131) B1740131
theorem B1160153 : Blo 770335 1160153 := bstep (se 2 (by rfl) ⟨435057, by rfl⟩ : syracuseStep 1160153 = 870115) B870115
theorem B2929715 : Blo 770335 2929715 := bstep (se 1 (by rfl) ⟨2197286, by rfl⟩ : syracuseStep 2929715 = 4394573) B4394573
theorem B2929729 : Blo 770335 2929729 := bstep (se 2 (by rfl) ⟨1098648, by rfl⟩ : syracuseStep 2929729 = 2197297) B2197297
theorem B1160267 : Blo 770335 1160267 := bstep (se 1 (by rfl) ⟨870200, by rfl⟩ : syracuseStep 1160267 = 1740401) B1740401
theorem B1160279 : Blo 770335 1160279 := bstep (se 1 (by rfl) ⟨870209, by rfl⟩ : syracuseStep 1160279 = 1740419) B1740419
theorem B1160345 : Blo 770335 1160345 := bstep (se 2 (by rfl) ⟨435129, by rfl⟩ : syracuseStep 1160345 = 870259) B870259
theorem B2602205 : Blo 770335 2602205 := bstep (se 3 (by rfl) ⟨487913, by rfl⟩ : syracuseStep 2602205 = 975827) B975827
theorem B1160459 : Blo 770335 1160459 := bstep (se 1 (by rfl) ⟨870344, by rfl⟩ : syracuseStep 1160459 = 1740689) B1740689
theorem B1160471 : Blo 770335 1160471 := bstep (se 1 (by rfl) ⟨870353, by rfl⟩ : syracuseStep 1160471 = 1740707) B1740707
theorem B1160537 : Blo 770335 1160537 := bstep (se 2 (by rfl) ⟨435201, by rfl⟩ : syracuseStep 1160537 = 870403) B870403
theorem B10302821 : Blo 770335 10302821 := bstep (se 4 (by rfl) ⟨965889, by rfl⟩ : syracuseStep 10302821 = 1931779) B1931779
theorem B5879141 : Blo 770335 5879141 := bstep (se 4 (by rfl) ⟨551169, by rfl⟩ : syracuseStep 5879141 = 1102339) B1102339
theorem B1389953 : Blo 770335 1389953 := bstep (se 2 (by rfl) ⟨521232, by rfl⟩ : syracuseStep 1389953 = 1042465) B1042465
theorem B1160651 : Blo 770335 1160651 := bstep (se 1 (by rfl) ⟨870488, by rfl⟩ : syracuseStep 1160651 = 1740977) B1740977
theorem B1160663 : Blo 770335 1160663 := bstep (se 1 (by rfl) ⟨870497, by rfl⟩ : syracuseStep 1160663 = 1740995) B1740995
theorem B2471447 : Blo 770335 2471447 := bstep (se 1 (by rfl) ⟨1853585, by rfl⟩ : syracuseStep 2471447 = 3707171) B3707171
theorem B1160729 : Blo 770335 1160729 := bstep (se 2 (by rfl) ⟨435273, by rfl⟩ : syracuseStep 1160729 = 870547) B870547
theorem B1652339 : Blo 770335 1652339 := bstep (se 1 (by rfl) ⟨1239254, by rfl⟩ : syracuseStep 1652339 = 2478509) B2478509
theorem B1160843 : Blo 770335 1160843 := bstep (se 1 (by rfl) ⟨870632, by rfl⟩ : syracuseStep 1160843 = 1741265) B1741265
theorem B1160855 : Blo 770335 1160855 := bstep (se 1 (by rfl) ⟨870641, by rfl⟩ : syracuseStep 1160855 = 1741283) B1741283
theorem B7059149 : Blo 770335 7059149 := bstep (se 3 (by rfl) ⟨1323590, by rfl⟩ : syracuseStep 7059149 = 2647181) B2647181
theorem B3913433 : Blo 770335 3913433 := bstep (se 2 (by rfl) ⟨1467537, by rfl⟩ : syracuseStep 3913433 = 2935075) B2935075
theorem B1160921 : Blo 770335 1160921 := bstep (se 2 (by rfl) ⟨435345, by rfl⟩ : syracuseStep 1160921 = 870691) B870691
theorem B2471755 : Blo 770335 2471755 := bstep (se 1 (by rfl) ⟨1853816, by rfl⟩ : syracuseStep 2471755 = 3707633) B3707633
theorem B1161035 : Blo 770335 1161035 := bstep (se 1 (by rfl) ⟨870776, by rfl⟩ : syracuseStep 1161035 = 1741553) B1741553
theorem B5879627 : Blo 770335 5879627 := bstep (se 1 (by rfl) ⟨4409720, by rfl⟩ : syracuseStep 5879627 = 8819441) B8819441
theorem B1161047 : Blo 770335 1161047 := bstep (se 1 (by rfl) ⟨870785, by rfl⟩ : syracuseStep 1161047 = 1741571) B1741571
theorem B3291025 : Blo 770335 3291025 := bstep (se 2 (by rfl) ⟨1234134, by rfl⟩ : syracuseStep 3291025 = 2468269) B2468269
theorem B1161113 : Blo 770335 1161113 := bstep (se 2 (by rfl) ⟨435417, by rfl⟩ : syracuseStep 1161113 = 870835) B870835
theorem B1161227 : Blo 770335 1161227 := bstep (se 1 (by rfl) ⟨870920, by rfl⟩ : syracuseStep 1161227 = 1741841) B1741841
theorem B1161239 : Blo 770335 1161239 := bstep (se 1 (by rfl) ⟨870929, by rfl⟩ : syracuseStep 1161239 = 1741859) B1741859
theorem B1161305 : Blo 770335 1161305 := bstep (se 2 (by rfl) ⟨435489, by rfl⟩ : syracuseStep 1161305 = 870979) B870979
theorem B1161419 : Blo 770335 1161419 := bstep (se 1 (by rfl) ⟨871064, by rfl⟩ : syracuseStep 1161419 = 1742129) B1742129
theorem B1161431 : Blo 770335 1161431 := bstep (se 1 (by rfl) ⟨871073, by rfl⟩ : syracuseStep 1161431 = 1742147) B1742147
theorem B1161497 : Blo 770335 1161497 := bstep (se 2 (by rfl) ⟨435561, by rfl⟩ : syracuseStep 1161497 = 871123) B871123
theorem B2603339 : Blo 770335 2603339 := bstep (se 1 (by rfl) ⟨1952504, by rfl⟩ : syracuseStep 2603339 = 3905009) B3905009
theorem B866731 : Blo 770335 866731 := bstep (se 1 (by rfl) ⟨650048, by rfl⟩ : syracuseStep 866731 = 1300097) B1300097
theorem B1653185 : Blo 770335 1653185 := bstep (se 2 (by rfl) ⟨619944, by rfl⟩ : syracuseStep 1653185 = 1239889) B1239889
theorem B866839 : Blo 770335 866839 := bstep (se 1 (by rfl) ⟨650129, by rfl⟩ : syracuseStep 866839 = 1300259) B1300259
theorem B4176449 : Blo 770335 4176449 := bstep (se 2 (by rfl) ⟨1566168, by rfl⟩ : syracuseStep 4176449 = 3132337) B3132337
theorem B2603609 : Blo 770335 2603609 := bstep (se 2 (by rfl) ⟨976353, by rfl⟩ : syracuseStep 2603609 = 1952707) B1952707
theorem B834187 : Blo 770335 834187 := bstep (se 1 (by rfl) ⟨625640, by rfl⟩ : syracuseStep 834187 = 1251281) B1251281
theorem B867019 : Blo 770335 867019 := bstep (se 1 (by rfl) ⟨650264, by rfl⟩ : syracuseStep 867019 = 1300529) B1300529
theorem B1653527 : Blo 770335 1653527 := bstep (se 1 (by rfl) ⟨1240145, by rfl⟩ : syracuseStep 1653527 = 2480291) B2480291
theorem B867127 : Blo 770335 867127 := bstep (se 1 (by rfl) ⟨650345, by rfl⟩ : syracuseStep 867127 = 1300691) B1300691
theorem B2931659 : Blo 770335 2931659 := bstep (se 1 (by rfl) ⟨2198744, by rfl⟩ : syracuseStep 2931659 = 4397489) B4397489
theorem B2931673 : Blo 770335 2931673 := bstep (se 2 (by rfl) ⟨1099377, by rfl⟩ : syracuseStep 2931673 = 2198755) B2198755
theorem B867307 : Blo 770335 867307 := bstep (se 1 (by rfl) ⟨650480, by rfl⟩ : syracuseStep 867307 = 1300961) B1300961
theorem B6601733 : Blo 770335 6601733 := bstep (se 4 (by rfl) ⟨618912, by rfl⟩ : syracuseStep 6601733 = 1237825) B1237825
theorem B867415 : Blo 770335 867415 := bstep (se 1 (by rfl) ⟨650561, by rfl⟩ : syracuseStep 867415 = 1301123) B1301123
theorem B867595 : Blo 770335 867595 := bstep (se 1 (by rfl) ⟨650696, by rfl⟩ : syracuseStep 867595 = 1301393) B1301393
theorem B7027985 : Blo 770335 7027985 := bstep (se 2 (by rfl) ⟨2635494, by rfl⟩ : syracuseStep 7027985 = 5270989) B5270989
theorem B2604311 : Blo 770335 2604311 := bstep (se 1 (by rfl) ⟨1953233, by rfl⟩ : syracuseStep 2604311 = 3906467) B3906467
theorem B3915053 : Blo 770335 3915053 := bstep (se 3 (by rfl) ⟨734072, by rfl⟩ : syracuseStep 3915053 = 1468145) B1468145
theorem B867703 : Blo 770335 867703 := bstep (se 1 (by rfl) ⟨650777, by rfl⟩ : syracuseStep 867703 = 1301555) B1301555
theorem B171589013 : Blo 770335 171589013 := bstep (se 6 (by rfl) ⟨4021617, by rfl⟩ : syracuseStep 171589013 = 8043235) B8043235
theorem B1097111 : Blo 770335 1097111 := bstep (se 1 (by rfl) ⟨822833, by rfl⟩ : syracuseStep 1097111 = 1645667) B1645667
theorem B867883 : Blo 770335 867883 := bstep (se 1 (by rfl) ⟨650912, by rfl⟩ : syracuseStep 867883 = 1301825) B1301825
theorem B3128963 : Blo 770335 3128963 := bstep (se 1 (by rfl) ⟨2346722, by rfl⟩ : syracuseStep 3128963 = 4693445) B4693445
theorem B867991 : Blo 770335 867991 := bstep (se 1 (by rfl) ⟨650993, by rfl⟩ : syracuseStep 867991 = 1301987) B1301987
theorem B6602417 : Blo 770335 6602417 := bstep (se 2 (by rfl) ⟨2475906, by rfl⟩ : syracuseStep 6602417 = 4951813) B4951813
theorem B835307 : Blo 770335 835307 := bstep (se 1 (by rfl) ⟨626480, by rfl⟩ : syracuseStep 835307 = 1252961) B1252961
theorem B2604851 : Blo 770335 2604851 := bstep (se 1 (by rfl) ⟨1953638, by rfl⟩ : syracuseStep 2604851 = 3907277) B3907277
theorem B868171 : Blo 770335 868171 := bstep (se 1 (by rfl) ⟨651128, by rfl⟩ : syracuseStep 868171 = 1302257) B1302257
theorem B2932631 : Blo 770335 2932631 := bstep (se 1 (by rfl) ⟨2199473, by rfl⟩ : syracuseStep 2932631 = 4398947) B4398947
theorem B14106545 : Blo 770335 14106545 := bstep (se 2 (by rfl) ⟨5289954, by rfl⟩ : syracuseStep 14106545 = 10579909) B10579909
theorem B2473907 : Blo 770335 2473907 := bstep (se 1 (by rfl) ⟨1855430, by rfl⟩ : syracuseStep 2473907 = 3710861) B3710861
theorem B868279 : Blo 770335 868279 := bstep (se 1 (by rfl) ⟨651209, by rfl⟩ : syracuseStep 868279 = 1302419) B1302419
theorem B1392641 : Blo 770335 1392641 := bstep (se 2 (by rfl) ⟨522240, by rfl⟩ : syracuseStep 1392641 = 1044481) B1044481
theorem B2605121 : Blo 770335 2605121 := bstep (se 2 (by rfl) ⟨976920, by rfl⟩ : syracuseStep 2605121 = 1953841) B1953841
theorem B30883909 : Blo 770335 30883909 := bstep (se 4 (by rfl) ⟨2895366, by rfl⟩ : syracuseStep 30883909 = 5790733) B5790733
theorem B868459 : Blo 770335 868459 := bstep (se 1 (by rfl) ⟨651344, by rfl⟩ : syracuseStep 868459 = 1302689) B1302689
theorem B4178051 : Blo 770335 4178051 := bstep (se 1 (by rfl) ⟨3133538, by rfl⟩ : syracuseStep 4178051 = 6267077) B6267077
theorem B868567 : Blo 770335 868567 := bstep (se 1 (by rfl) ⟨651425, by rfl⟩ : syracuseStep 868567 = 1302851) B1302851
theorem B770347 : Blo 770335 770347 := bstep (se 1 (by rfl) ⟨577760, by rfl⟩ : syracuseStep 770347 = 1155521) B1155521
theorem B770359 : Blo 770335 770359 := bstep (se 1 (by rfl) ⟨577769, by rfl⟩ : syracuseStep 770359 = 1155539) B1155539
theorem B2965825 : Blo 770335 2965825 := bstep (se 2 (by rfl) ⟨1112184, by rfl⟩ : syracuseStep 2965825 = 2224369) B2224369
theorem B770379 : Blo 770335 770379 := bstep (se 1 (by rfl) ⟨577784, by rfl⟩ : syracuseStep 770379 = 1155569) B1155569
theorem B770391 : Blo 770335 770391 := bstep (se 1 (by rfl) ⟨577793, by rfl⟩ : syracuseStep 770391 = 1155587) B1155587
theorem B770411 : Blo 770335 770411 := bstep (se 1 (by rfl) ⟨577808, by rfl⟩ : syracuseStep 770411 = 1155617) B1155617
theorem B770423 : Blo 770335 770423 := bstep (se 1 (by rfl) ⟨577817, by rfl⟩ : syracuseStep 770423 = 1155635) B1155635
theorem B770443 : Blo 770335 770443 := bstep (se 1 (by rfl) ⟨577832, by rfl⟩ : syracuseStep 770443 = 1155665) B1155665
theorem B868747 : Blo 770335 868747 := bstep (se 1 (by rfl) ⟨651560, by rfl⟩ : syracuseStep 868747 = 1303121) B1303121
theorem B770455 : Blo 770335 770455 := bstep (se 1 (by rfl) ⟨577841, by rfl⟩ : syracuseStep 770455 = 1155683) B1155683
theorem B770475 : Blo 770335 770475 := bstep (se 1 (by rfl) ⟨577856, by rfl⟩ : syracuseStep 770475 = 1155713) B1155713
theorem B3129779 : Blo 770335 3129779 := bstep (se 1 (by rfl) ⟨2347334, by rfl⟩ : syracuseStep 3129779 = 4694669) B4694669
theorem B770487 : Blo 770335 770487 := bstep (se 1 (by rfl) ⟨577865, by rfl⟩ : syracuseStep 770487 = 1155731) B1155731
theorem B770507 : Blo 770335 770507 := bstep (se 1 (by rfl) ⟨577880, by rfl⟩ : syracuseStep 770507 = 1155761) B1155761
theorem B770519 : Blo 770335 770519 := bstep (se 1 (by rfl) ⟨577889, by rfl⟩ : syracuseStep 770519 = 1155779) B1155779
theorem B770539 : Blo 770335 770539 := bstep (se 1 (by rfl) ⟨577904, by rfl⟩ : syracuseStep 770539 = 1155809) B1155809
theorem B770551 : Blo 770335 770551 := bstep (se 1 (by rfl) ⟨577913, by rfl⟩ : syracuseStep 770551 = 1155827) B1155827
theorem B868855 : Blo 770335 868855 := bstep (se 1 (by rfl) ⟨651641, by rfl⟩ : syracuseStep 868855 = 1303283) B1303283
theorem B770571 : Blo 770335 770571 := bstep (se 1 (by rfl) ⟨577928, by rfl⟩ : syracuseStep 770571 = 1155857) B1155857
theorem B770583 : Blo 770335 770583 := bstep (se 1 (by rfl) ⟨577937, by rfl⟩ : syracuseStep 770583 = 1155875) B1155875
theorem B770603 : Blo 770335 770603 := bstep (se 1 (by rfl) ⟨577952, by rfl⟩ : syracuseStep 770603 = 1155905) B1155905
theorem B770615 : Blo 770335 770615 := bstep (se 1 (by rfl) ⟨577961, by rfl⟩ : syracuseStep 770615 = 1155923) B1155923
theorem B770635 : Blo 770335 770635 := bstep (se 1 (by rfl) ⟨577976, by rfl⟩ : syracuseStep 770635 = 1155953) B1155953
theorem B770647 : Blo 770335 770647 := bstep (se 1 (by rfl) ⟨577985, by rfl⟩ : syracuseStep 770647 = 1155971) B1155971
theorem B2605661 : Blo 770335 2605661 := bstep (se 3 (by rfl) ⟨488561, by rfl⟩ : syracuseStep 2605661 = 977123) B977123
theorem B770667 : Blo 770335 770667 := bstep (se 1 (by rfl) ⟨578000, by rfl⟩ : syracuseStep 770667 = 1156001) B1156001
theorem B770679 : Blo 770335 770679 := bstep (se 1 (by rfl) ⟨578009, by rfl⟩ : syracuseStep 770679 = 1156019) B1156019
theorem B770699 : Blo 770335 770699 := bstep (se 1 (by rfl) ⟨578024, by rfl⟩ : syracuseStep 770699 = 1156049) B1156049
theorem B770711 : Blo 770335 770711 := bstep (se 1 (by rfl) ⟨578033, by rfl⟩ : syracuseStep 770711 = 1156067) B1156067
theorem B770731 : Blo 770335 770731 := bstep (se 1 (by rfl) ⟨578048, by rfl⟩ : syracuseStep 770731 = 1156097) B1156097
theorem B869035 : Blo 770335 869035 := bstep (se 1 (by rfl) ⟨651776, by rfl⟩ : syracuseStep 869035 = 1303553) B1303553
theorem B6603443 : Blo 770335 6603443 := bstep (se 1 (by rfl) ⟨4952582, by rfl⟩ : syracuseStep 6603443 = 9905165) B9905165
theorem B770743 : Blo 770335 770743 := bstep (se 1 (by rfl) ⟨578057, by rfl⟩ : syracuseStep 770743 = 1156115) B1156115
theorem B770763 : Blo 770335 770763 := bstep (se 1 (by rfl) ⟨578072, by rfl⟩ : syracuseStep 770763 = 1156145) B1156145
theorem B1393355 : Blo 770335 1393355 := bstep (se 1 (by rfl) ⟨1045016, by rfl⟩ : syracuseStep 1393355 = 2090033) B2090033
theorem B770775 : Blo 770335 770775 := bstep (se 1 (by rfl) ⟨578081, by rfl⟩ : syracuseStep 770775 = 1156163) B1156163
theorem B770795 : Blo 770335 770795 := bstep (se 1 (by rfl) ⟨578096, by rfl⟩ : syracuseStep 770795 = 1156193) B1156193
theorem B40682225 : Blo 770335 40682225 := bstep (se 2 (by rfl) ⟨15255834, by rfl⟩ : syracuseStep 40682225 = 30511669) B30511669
theorem B770807 : Blo 770335 770807 := bstep (se 1 (by rfl) ⟨578105, by rfl⟩ : syracuseStep 770807 = 1156211) B1156211
theorem B770827 : Blo 770335 770827 := bstep (se 1 (by rfl) ⟨578120, by rfl⟩ : syracuseStep 770827 = 1156241) B1156241
theorem B770839 : Blo 770335 770839 := bstep (se 1 (by rfl) ⟨578129, by rfl⟩ : syracuseStep 770839 = 1156259) B1156259
theorem B869143 : Blo 770335 869143 := bstep (se 1 (by rfl) ⟨651857, by rfl⟩ : syracuseStep 869143 = 1303715) B1303715
theorem B770859 : Blo 770335 770859 := bstep (se 1 (by rfl) ⟨578144, by rfl⟩ : syracuseStep 770859 = 1156289) B1156289
theorem B770871 : Blo 770335 770871 := bstep (se 1 (by rfl) ⟨578153, by rfl⟩ : syracuseStep 770871 = 1156307) B1156307
theorem B3294017 : Blo 770335 3294017 := bstep (se 2 (by rfl) ⟨1235256, by rfl⟩ : syracuseStep 3294017 = 2470513) B2470513
theorem B770891 : Blo 770335 770891 := bstep (se 1 (by rfl) ⟨578168, by rfl⟩ : syracuseStep 770891 = 1156337) B1156337
theorem B770903 : Blo 770335 770903 := bstep (se 1 (by rfl) ⟨578177, by rfl⟩ : syracuseStep 770903 = 1156355) B1156355
theorem B4178789 : Blo 770335 4178789 := bstep (se 4 (by rfl) ⟨391761, by rfl⟩ : syracuseStep 4178789 = 783523) B783523
theorem B770923 : Blo 770335 770923 := bstep (se 1 (by rfl) ⟨578192, by rfl⟩ : syracuseStep 770923 = 1156385) B1156385
theorem B770935 : Blo 770335 770935 := bstep (se 1 (by rfl) ⟨578201, by rfl⟩ : syracuseStep 770935 = 1156403) B1156403
theorem B770955 : Blo 770335 770955 := bstep (se 1 (by rfl) ⟨578216, by rfl⟩ : syracuseStep 770955 = 1156433) B1156433
theorem B770967 : Blo 770335 770967 := bstep (se 1 (by rfl) ⟨578225, by rfl⟩ : syracuseStep 770967 = 1156451) B1156451
theorem B770987 : Blo 770335 770987 := bstep (se 1 (by rfl) ⟨578240, by rfl⟩ : syracuseStep 770987 = 1156481) B1156481
theorem B770999 : Blo 770335 770999 := bstep (se 1 (by rfl) ⟨578249, by rfl⟩ : syracuseStep 770999 = 1156499) B1156499
theorem B771019 : Blo 770335 771019 := bstep (se 1 (by rfl) ⟨578264, by rfl⟩ : syracuseStep 771019 = 1156529) B1156529
theorem B869323 : Blo 770335 869323 := bstep (se 1 (by rfl) ⟨651992, by rfl⟩ : syracuseStep 869323 = 1303985) B1303985
theorem B771031 : Blo 770335 771031 := bstep (se 1 (by rfl) ⟨578273, by rfl⟩ : syracuseStep 771031 = 1156547) B1156547
theorem B771051 : Blo 770335 771051 := bstep (se 1 (by rfl) ⟨578288, by rfl⟩ : syracuseStep 771051 = 1156577) B1156577
theorem B771063 : Blo 770335 771063 := bstep (se 1 (by rfl) ⟨578297, by rfl⟩ : syracuseStep 771063 = 1156595) B1156595
theorem B771083 : Blo 770335 771083 := bstep (se 1 (by rfl) ⟨578312, by rfl⟩ : syracuseStep 771083 = 1156625) B1156625
theorem B1950743 : Blo 770335 1950743 := bstep (se 1 (by rfl) ⟨1463057, by rfl⟩ : syracuseStep 1950743 = 2926115) B2926115
theorem B771095 : Blo 770335 771095 := bstep (se 1 (by rfl) ⟨578321, by rfl⟩ : syracuseStep 771095 = 1156643) B1156643
theorem B771115 : Blo 770335 771115 := bstep (se 1 (by rfl) ⟨578336, by rfl⟩ : syracuseStep 771115 = 1156673) B1156673
theorem B771127 : Blo 770335 771127 := bstep (se 1 (by rfl) ⟨578345, by rfl⟩ : syracuseStep 771127 = 1156691) B1156691
theorem B869431 : Blo 770335 869431 := bstep (se 1 (by rfl) ⟨652073, by rfl⟩ : syracuseStep 869431 = 1304147) B1304147
theorem B771147 : Blo 770335 771147 := bstep (se 1 (by rfl) ⟨578360, by rfl⟩ : syracuseStep 771147 = 1156721) B1156721
theorem B771159 : Blo 770335 771159 := bstep (se 1 (by rfl) ⟨578369, by rfl⟩ : syracuseStep 771159 = 1156739) B1156739
theorem B1590359 : Blo 770335 1590359 := bstep (se 1 (by rfl) ⟨1192769, by rfl⟩ : syracuseStep 1590359 = 2385539) B2385539
theorem B771179 : Blo 770335 771179 := bstep (se 1 (by rfl) ⟨578384, by rfl⟩ : syracuseStep 771179 = 1156769) B1156769
theorem B771191 : Blo 770335 771191 := bstep (se 1 (by rfl) ⟨578393, by rfl⟩ : syracuseStep 771191 = 1156787) B1156787
theorem B2933891 : Blo 770335 2933891 := bstep (se 1 (by rfl) ⟨2200418, by rfl⟩ : syracuseStep 2933891 = 4400837) B4400837
theorem B771211 : Blo 770335 771211 := bstep (se 1 (by rfl) ⟨578408, by rfl⟩ : syracuseStep 771211 = 1156817) B1156817
theorem B771223 : Blo 770335 771223 := bstep (se 1 (by rfl) ⟨578417, by rfl⟩ : syracuseStep 771223 = 1156835) B1156835
theorem B771243 : Blo 770335 771243 := bstep (se 1 (by rfl) ⟨578432, by rfl⟩ : syracuseStep 771243 = 1156865) B1156865
theorem B771255 : Blo 770335 771255 := bstep (se 1 (by rfl) ⟨578441, by rfl⟩ : syracuseStep 771255 = 1156883) B1156883
theorem B771275 : Blo 770335 771275 := bstep (se 1 (by rfl) ⟨578456, by rfl⟩ : syracuseStep 771275 = 1156913) B1156913
theorem B771287 : Blo 770335 771287 := bstep (se 1 (by rfl) ⟨578465, by rfl⟩ : syracuseStep 771287 = 1156931) B1156931
theorem B771307 : Blo 770335 771307 := bstep (se 1 (by rfl) ⟨578480, by rfl⟩ : syracuseStep 771307 = 1156961) B1156961
theorem B869611 : Blo 770335 869611 := bstep (se 1 (by rfl) ⟨652208, by rfl⟩ : syracuseStep 869611 = 1304417) B1304417
theorem B771319 : Blo 770335 771319 := bstep (se 1 (by rfl) ⟨578489, by rfl⟩ : syracuseStep 771319 = 1156979) B1156979
theorem B771339 : Blo 770335 771339 := bstep (se 1 (by rfl) ⟨578504, by rfl⟩ : syracuseStep 771339 = 1157009) B1157009
theorem B4179217 : Blo 770335 4179217 := bstep (se 2 (by rfl) ⟨1567206, by rfl⟩ : syracuseStep 4179217 = 3134413) B3134413
theorem B771351 : Blo 770335 771351 := bstep (se 1 (by rfl) ⟨578513, by rfl⟩ : syracuseStep 771351 = 1157027) B1157027
theorem B771371 : Blo 770335 771371 := bstep (se 1 (by rfl) ⟨578528, by rfl⟩ : syracuseStep 771371 = 1157057) B1157057
theorem B771383 : Blo 770335 771383 := bstep (se 1 (by rfl) ⟨578537, by rfl⟩ : syracuseStep 771383 = 1157075) B1157075
theorem B771403 : Blo 770335 771403 := bstep (se 1 (by rfl) ⟨578552, by rfl⟩ : syracuseStep 771403 = 1157105) B1157105
theorem B869719 : Blo 770335 869719 := bstep (se 1 (by rfl) ⟨652289, by rfl⟩ : syracuseStep 869719 = 1304579) B1304579
theorem B771415 : Blo 770335 771415 := bstep (se 1 (by rfl) ⟨578561, by rfl⟩ : syracuseStep 771415 = 1157123) B1157123
theorem B771435 : Blo 770335 771435 := bstep (se 1 (by rfl) ⟨578576, by rfl⟩ : syracuseStep 771435 = 1157153) B1157153
theorem B771447 : Blo 770335 771447 := bstep (se 1 (by rfl) ⟨578585, by rfl⟩ : syracuseStep 771447 = 1157171) B1157171
theorem B771467 : Blo 770335 771467 := bstep (se 1 (by rfl) ⟨578600, by rfl⟩ : syracuseStep 771467 = 1157201) B1157201
theorem B771479 : Blo 770335 771479 := bstep (se 1 (by rfl) ⟨578609, by rfl⟩ : syracuseStep 771479 = 1157219) B1157219
theorem B771499 : Blo 770335 771499 := bstep (se 1 (by rfl) ⟨578624, by rfl⟩ : syracuseStep 771499 = 1157249) B1157249
theorem B771511 : Blo 770335 771511 := bstep (se 1 (by rfl) ⟨578633, by rfl⟩ : syracuseStep 771511 = 1157267) B1157267
theorem B771531 : Blo 770335 771531 := bstep (se 1 (by rfl) ⟨578648, by rfl⟩ : syracuseStep 771531 = 1157297) B1157297
theorem B771543 : Blo 770335 771543 := bstep (se 1 (by rfl) ⟨578657, by rfl⟩ : syracuseStep 771543 = 1157315) B1157315
theorem B771563 : Blo 770335 771563 := bstep (se 1 (by rfl) ⟨578672, by rfl⟩ : syracuseStep 771563 = 1157345) B1157345
theorem B771575 : Blo 770335 771575 := bstep (se 1 (by rfl) ⟨578681, by rfl⟩ : syracuseStep 771575 = 1157363) B1157363
theorem B771595 : Blo 770335 771595 := bstep (se 1 (by rfl) ⟨578696, by rfl⟩ : syracuseStep 771595 = 1157393) B1157393
theorem B869899 : Blo 770335 869899 := bstep (se 1 (by rfl) ⟨652424, by rfl⟩ : syracuseStep 869899 = 1304849) B1304849
theorem B771607 : Blo 770335 771607 := bstep (se 1 (by rfl) ⟨578705, by rfl⟩ : syracuseStep 771607 = 1157411) B1157411
theorem B771627 : Blo 770335 771627 := bstep (se 1 (by rfl) ⟨578720, by rfl⟩ : syracuseStep 771627 = 1157441) B1157441
theorem B771639 : Blo 770335 771639 := bstep (se 1 (by rfl) ⟨578729, by rfl⟩ : syracuseStep 771639 = 1157459) B1157459
theorem B771659 : Blo 770335 771659 := bstep (se 1 (by rfl) ⟨578744, by rfl⟩ : syracuseStep 771659 = 1157489) B1157489
theorem B771671 : Blo 770335 771671 := bstep (se 1 (by rfl) ⟨578753, by rfl⟩ : syracuseStep 771671 = 1157507) B1157507
theorem B771691 : Blo 770335 771691 := bstep (se 1 (by rfl) ⟨578768, by rfl⟩ : syracuseStep 771691 = 1157537) B1157537
theorem B771703 : Blo 770335 771703 := bstep (se 1 (by rfl) ⟨578777, by rfl⟩ : syracuseStep 771703 = 1157555) B1157555
theorem B870007 : Blo 770335 870007 := bstep (se 1 (by rfl) ⟨652505, by rfl⟩ : syracuseStep 870007 = 1305011) B1305011
theorem B771723 : Blo 770335 771723 := bstep (se 1 (by rfl) ⟨578792, by rfl⟩ : syracuseStep 771723 = 1157585) B1157585
theorem B771735 : Blo 770335 771735 := bstep (se 1 (by rfl) ⟨578801, by rfl⟩ : syracuseStep 771735 = 1157603) B1157603
theorem B771755 : Blo 770335 771755 := bstep (se 1 (by rfl) ⟨578816, by rfl⟩ : syracuseStep 771755 = 1157633) B1157633
theorem B1951411 : Blo 770335 1951411 := bstep (se 1 (by rfl) ⟨1463558, by rfl⟩ : syracuseStep 1951411 = 2927117) B2927117
theorem B771767 : Blo 770335 771767 := bstep (se 1 (by rfl) ⟨578825, by rfl⟩ : syracuseStep 771767 = 1157651) B1157651
theorem B771787 : Blo 770335 771787 := bstep (se 1 (by rfl) ⟨578840, by rfl⟩ : syracuseStep 771787 = 1157681) B1157681
theorem B2606795 : Blo 770335 2606795 := bstep (se 1 (by rfl) ⟨1955096, by rfl⟩ : syracuseStep 2606795 = 3910193) B3910193
theorem B771799 : Blo 770335 771799 := bstep (se 1 (by rfl) ⟨578849, by rfl⟩ : syracuseStep 771799 = 1157699) B1157699
theorem B771819 : Blo 770335 771819 := bstep (se 1 (by rfl) ⟨578864, by rfl⟩ : syracuseStep 771819 = 1157729) B1157729
theorem B771831 : Blo 770335 771831 := bstep (se 1 (by rfl) ⟨578873, by rfl⟩ : syracuseStep 771831 = 1157747) B1157747
theorem B771851 : Blo 770335 771851 := bstep (se 1 (by rfl) ⟨578888, by rfl⟩ : syracuseStep 771851 = 1157777) B1157777
theorem B771863 : Blo 770335 771863 := bstep (se 1 (by rfl) ⟨578897, by rfl⟩ : syracuseStep 771863 = 1157795) B1157795
theorem B771883 : Blo 770335 771883 := bstep (se 1 (by rfl) ⟨578912, by rfl⟩ : syracuseStep 771883 = 1157825) B1157825
theorem B870187 : Blo 770335 870187 := bstep (se 1 (by rfl) ⟨652640, by rfl⟩ : syracuseStep 870187 = 1305281) B1305281
theorem B771895 : Blo 770335 771895 := bstep (se 1 (by rfl) ⟨578921, by rfl⟩ : syracuseStep 771895 = 1157843) B1157843
theorem B1951553 : Blo 770335 1951553 := bstep (se 2 (by rfl) ⟨731832, by rfl⟩ : syracuseStep 1951553 = 1463665) B1463665
theorem B4409153 : Blo 770335 4409153 := bstep (se 2 (by rfl) ⟨1653432, by rfl⟩ : syracuseStep 4409153 = 3306865) B3306865
theorem B771915 : Blo 770335 771915 := bstep (se 1 (by rfl) ⟨578936, by rfl⟩ : syracuseStep 771915 = 1157873) B1157873
theorem B771927 : Blo 770335 771927 := bstep (se 1 (by rfl) ⟨578945, by rfl⟩ : syracuseStep 771927 = 1157891) B1157891
theorem B771947 : Blo 770335 771947 := bstep (se 1 (by rfl) ⟨578960, by rfl⟩ : syracuseStep 771947 = 1157921) B1157921
theorem B771959 : Blo 770335 771959 := bstep (se 1 (by rfl) ⟨578969, by rfl⟩ : syracuseStep 771959 = 1157939) B1157939
theorem B771979 : Blo 770335 771979 := bstep (se 1 (by rfl) ⟨578984, by rfl⟩ : syracuseStep 771979 = 1157969) B1157969
theorem B771991 : Blo 770335 771991 := bstep (se 1 (by rfl) ⟨578993, by rfl⟩ : syracuseStep 771991 = 1157987) B1157987
theorem B870295 : Blo 770335 870295 := bstep (se 1 (by rfl) ⟨652721, by rfl⟩ : syracuseStep 870295 = 1305443) B1305443
theorem B772011 : Blo 770335 772011 := bstep (se 1 (by rfl) ⟨579008, by rfl⟩ : syracuseStep 772011 = 1158017) B1158017
theorem B772023 : Blo 770335 772023 := bstep (se 1 (by rfl) ⟨579017, by rfl⟩ : syracuseStep 772023 = 1158035) B1158035
theorem B772043 : Blo 770335 772043 := bstep (se 1 (by rfl) ⟨579032, by rfl⟩ : syracuseStep 772043 = 1158065) B1158065
theorem B772055 : Blo 770335 772055 := bstep (se 1 (by rfl) ⟨579041, by rfl⟩ : syracuseStep 772055 = 1158083) B1158083
theorem B2607065 : Blo 770335 2607065 := bstep (se 2 (by rfl) ⟨977649, by rfl⟩ : syracuseStep 2607065 = 1955299) B1955299
theorem B772075 : Blo 770335 772075 := bstep (se 1 (by rfl) ⟨579056, by rfl⟩ : syracuseStep 772075 = 1158113) B1158113
theorem B772087 : Blo 770335 772087 := bstep (se 1 (by rfl) ⟨579065, by rfl⟩ : syracuseStep 772087 = 1158131) B1158131
theorem B772107 : Blo 770335 772107 := bstep (se 1 (by rfl) ⟨579080, by rfl⟩ : syracuseStep 772107 = 1158161) B1158161
theorem B772119 : Blo 770335 772119 := bstep (se 1 (by rfl) ⟨579089, by rfl⟩ : syracuseStep 772119 = 1158179) B1158179
theorem B772139 : Blo 770335 772139 := bstep (se 1 (by rfl) ⟨579104, by rfl⟩ : syracuseStep 772139 = 1158209) B1158209
theorem B772151 : Blo 770335 772151 := bstep (se 1 (by rfl) ⟨579113, by rfl⟩ : syracuseStep 772151 = 1158227) B1158227
theorem B772171 : Blo 770335 772171 := bstep (se 1 (by rfl) ⟨579128, by rfl⟩ : syracuseStep 772171 = 1158257) B1158257
theorem B870475 : Blo 770335 870475 := bstep (se 1 (by rfl) ⟨652856, by rfl⟩ : syracuseStep 870475 = 1305713) B1305713
theorem B772183 : Blo 770335 772183 := bstep (se 1 (by rfl) ⟨579137, by rfl⟩ : syracuseStep 772183 = 1158275) B1158275
theorem B772203 : Blo 770335 772203 := bstep (se 1 (by rfl) ⟨579152, by rfl⟩ : syracuseStep 772203 = 1158305) B1158305
theorem B772215 : Blo 770335 772215 := bstep (se 1 (by rfl) ⟨579161, by rfl⟩ : syracuseStep 772215 = 1158323) B1158323
theorem B772235 : Blo 770335 772235 := bstep (se 1 (by rfl) ⟨579176, by rfl⟩ : syracuseStep 772235 = 1158353) B1158353
theorem B772247 : Blo 770335 772247 := bstep (se 1 (by rfl) ⟨579185, by rfl⟩ : syracuseStep 772247 = 1158371) B1158371
theorem B772267 : Blo 770335 772267 := bstep (se 1 (by rfl) ⟨579200, by rfl⟩ : syracuseStep 772267 = 1158401) B1158401
theorem B772279 : Blo 770335 772279 := bstep (se 1 (by rfl) ⟨579209, by rfl⟩ : syracuseStep 772279 = 1158419) B1158419
theorem B870583 : Blo 770335 870583 := bstep (se 1 (by rfl) ⟨652937, by rfl⟩ : syracuseStep 870583 = 1305875) B1305875
theorem B772299 : Blo 770335 772299 := bstep (se 1 (by rfl) ⟨579224, by rfl⟩ : syracuseStep 772299 = 1158449) B1158449
theorem B772311 : Blo 770335 772311 := bstep (se 1 (by rfl) ⟨579233, by rfl⟩ : syracuseStep 772311 = 1158467) B1158467
theorem B1099993 : Blo 770335 1099993 := bstep (se 2 (by rfl) ⟨412497, by rfl⟩ : syracuseStep 1099993 = 824995) B824995
theorem B772331 : Blo 770335 772331 := bstep (se 1 (by rfl) ⟨579248, by rfl⟩ : syracuseStep 772331 = 1158497) B1158497
theorem B772343 : Blo 770335 772343 := bstep (se 1 (by rfl) ⟨579257, by rfl⟩ : syracuseStep 772343 = 1158515) B1158515
theorem B772363 : Blo 770335 772363 := bstep (se 1 (by rfl) ⟨579272, by rfl⟩ : syracuseStep 772363 = 1158545) B1158545
theorem B772375 : Blo 770335 772375 := bstep (se 1 (by rfl) ⟨579281, by rfl⟩ : syracuseStep 772375 = 1158563) B1158563
theorem B772395 : Blo 770335 772395 := bstep (se 1 (by rfl) ⟨579296, by rfl⟩ : syracuseStep 772395 = 1158593) B1158593
theorem B772407 : Blo 770335 772407 := bstep (se 1 (by rfl) ⟨579305, by rfl⟩ : syracuseStep 772407 = 1158611) B1158611
theorem B772427 : Blo 770335 772427 := bstep (se 1 (by rfl) ⟨579320, by rfl⟩ : syracuseStep 772427 = 1158641) B1158641
theorem B772439 : Blo 770335 772439 := bstep (se 1 (by rfl) ⟨579329, by rfl⟩ : syracuseStep 772439 = 1158659) B1158659
theorem B772459 : Blo 770335 772459 := bstep (se 1 (by rfl) ⟨579344, by rfl⟩ : syracuseStep 772459 = 1158689) B1158689
theorem B870763 : Blo 770335 870763 := bstep (se 1 (by rfl) ⟨653072, by rfl⟩ : syracuseStep 870763 = 1306145) B1306145
theorem B772471 : Blo 770335 772471 := bstep (se 1 (by rfl) ⟨579353, by rfl⟩ : syracuseStep 772471 = 1158707) B1158707
theorem B772491 : Blo 770335 772491 := bstep (se 1 (by rfl) ⟨579368, by rfl⟩ : syracuseStep 772491 = 1158737) B1158737
theorem B772503 : Blo 770335 772503 := bstep (se 1 (by rfl) ⟨579377, by rfl⟩ : syracuseStep 772503 = 1158755) B1158755
theorem B772523 : Blo 770335 772523 := bstep (se 1 (by rfl) ⟨579392, by rfl⟩ : syracuseStep 772523 = 1158785) B1158785
theorem B10701233 : Blo 770335 10701233 := bstep (se 2 (by rfl) ⟨4012962, by rfl⟩ : syracuseStep 10701233 = 8025925) B8025925
theorem B772535 : Blo 770335 772535 := bstep (se 1 (by rfl) ⟨579401, by rfl⟩ : syracuseStep 772535 = 1158803) B1158803
theorem B772555 : Blo 770335 772555 := bstep (se 1 (by rfl) ⟨579416, by rfl⟩ : syracuseStep 772555 = 1158833) B1158833
theorem B772567 : Blo 770335 772567 := bstep (se 1 (by rfl) ⟨579425, by rfl⟩ : syracuseStep 772567 = 1158851) B1158851
theorem B870871 : Blo 770335 870871 := bstep (se 1 (by rfl) ⟨653153, by rfl⟩ : syracuseStep 870871 = 1306307) B1306307
theorem B772587 : Blo 770335 772587 := bstep (se 1 (by rfl) ⟨579440, by rfl⟩ : syracuseStep 772587 = 1158881) B1158881
theorem B772599 : Blo 770335 772599 := bstep (se 1 (by rfl) ⟨579449, by rfl⟩ : syracuseStep 772599 = 1158899) B1158899
theorem B772619 : Blo 770335 772619 := bstep (se 1 (by rfl) ⟨579464, by rfl⟩ : syracuseStep 772619 = 1158929) B1158929
theorem B772631 : Blo 770335 772631 := bstep (se 1 (by rfl) ⟨579473, by rfl⟩ : syracuseStep 772631 = 1158947) B1158947
theorem B772651 : Blo 770335 772651 := bstep (se 1 (by rfl) ⟨579488, by rfl⟩ : syracuseStep 772651 = 1158977) B1158977
theorem B772663 : Blo 770335 772663 := bstep (se 1 (by rfl) ⟨579497, by rfl⟩ : syracuseStep 772663 = 1158995) B1158995
theorem B772683 : Blo 770335 772683 := bstep (se 1 (by rfl) ⟨579512, by rfl⟩ : syracuseStep 772683 = 1159025) B1159025
theorem B772695 : Blo 770335 772695 := bstep (se 1 (by rfl) ⟨579521, by rfl⟩ : syracuseStep 772695 = 1159043) B1159043
theorem B772715 : Blo 770335 772715 := bstep (se 1 (by rfl) ⟨579536, by rfl⟩ : syracuseStep 772715 = 1159073) B1159073
theorem B772727 : Blo 770335 772727 := bstep (se 1 (by rfl) ⟨579545, by rfl⟩ : syracuseStep 772727 = 1159091) B1159091
theorem B772747 : Blo 770335 772747 := bstep (se 1 (by rfl) ⟨579560, by rfl⟩ : syracuseStep 772747 = 1159121) B1159121
theorem B871051 : Blo 770335 871051 := bstep (se 1 (by rfl) ⟨653288, by rfl⟩ : syracuseStep 871051 = 1306577) B1306577
theorem B2607767 : Blo 770335 2607767 := bstep (se 1 (by rfl) ⟨1955825, by rfl⟩ : syracuseStep 2607767 = 3911651) B3911651
theorem B772759 : Blo 770335 772759 := bstep (se 1 (by rfl) ⟨579569, by rfl⟩ : syracuseStep 772759 = 1159139) B1159139
theorem B772779 : Blo 770335 772779 := bstep (se 1 (by rfl) ⟨579584, by rfl⟩ : syracuseStep 772779 = 1159169) B1159169
theorem B772791 : Blo 770335 772791 := bstep (se 1 (by rfl) ⟨579593, by rfl⟩ : syracuseStep 772791 = 1159187) B1159187
theorem B772811 : Blo 770335 772811 := bstep (se 1 (by rfl) ⟨579608, by rfl⟩ : syracuseStep 772811 = 1159217) B1159217
theorem B772823 : Blo 770335 772823 := bstep (se 1 (by rfl) ⟨579617, by rfl⟩ : syracuseStep 772823 = 1159235) B1159235
theorem B772843 : Blo 770335 772843 := bstep (se 1 (by rfl) ⟨579632, by rfl⟩ : syracuseStep 772843 = 1159265) B1159265
theorem B772855 : Blo 770335 772855 := bstep (se 1 (by rfl) ⟨579641, by rfl⟩ : syracuseStep 772855 = 1159283) B1159283
theorem B772875 : Blo 770335 772875 := bstep (se 1 (by rfl) ⟨579656, by rfl⟩ : syracuseStep 772875 = 1159313) B1159313
theorem B772887 : Blo 770335 772887 := bstep (se 1 (by rfl) ⟨579665, by rfl⟩ : syracuseStep 772887 = 1159331) B1159331
theorem B1985303 : Blo 770335 1985303 := bstep (se 1 (by rfl) ⟨1488977, by rfl⟩ : syracuseStep 1985303 = 2977955) B2977955
theorem B772907 : Blo 770335 772907 := bstep (se 1 (by rfl) ⟨579680, by rfl⟩ : syracuseStep 772907 = 1159361) B1159361
theorem B772919 : Blo 770335 772919 := bstep (se 1 (by rfl) ⟨579689, by rfl⟩ : syracuseStep 772919 = 1159379) B1159379
theorem B772939 : Blo 770335 772939 := bstep (se 1 (by rfl) ⟨579704, by rfl⟩ : syracuseStep 772939 = 1159409) B1159409
theorem B772951 : Blo 770335 772951 := bstep (se 1 (by rfl) ⟨579713, by rfl⟩ : syracuseStep 772951 = 1159427) B1159427
theorem B772971 : Blo 770335 772971 := bstep (se 1 (by rfl) ⟨579728, by rfl⟩ : syracuseStep 772971 = 1159457) B1159457
theorem B772983 : Blo 770335 772983 := bstep (se 1 (by rfl) ⟨579737, by rfl⟩ : syracuseStep 772983 = 1159475) B1159475
theorem B773003 : Blo 770335 773003 := bstep (se 1 (by rfl) ⟨579752, by rfl⟩ : syracuseStep 773003 = 1159505) B1159505
theorem B773015 : Blo 770335 773015 := bstep (se 1 (by rfl) ⟨579761, by rfl⟩ : syracuseStep 773015 = 1159523) B1159523
theorem B773035 : Blo 770335 773035 := bstep (se 1 (by rfl) ⟨579776, by rfl⟩ : syracuseStep 773035 = 1159553) B1159553
theorem B773047 : Blo 770335 773047 := bstep (se 1 (by rfl) ⟨579785, by rfl⟩ : syracuseStep 773047 = 1159571) B1159571
theorem B773067 : Blo 770335 773067 := bstep (se 1 (by rfl) ⟨579800, by rfl⟩ : syracuseStep 773067 = 1159601) B1159601
theorem B773079 : Blo 770335 773079 := bstep (se 1 (by rfl) ⟨579809, by rfl⟩ : syracuseStep 773079 = 1159619) B1159619
theorem B773099 : Blo 770335 773099 := bstep (se 1 (by rfl) ⟨579824, by rfl⟩ : syracuseStep 773099 = 1159649) B1159649
theorem B773111 : Blo 770335 773111 := bstep (se 1 (by rfl) ⟨579833, by rfl⟩ : syracuseStep 773111 = 1159667) B1159667
theorem B773131 : Blo 770335 773131 := bstep (se 1 (by rfl) ⟨579848, by rfl⟩ : syracuseStep 773131 = 1159697) B1159697
theorem B773143 : Blo 770335 773143 := bstep (se 1 (by rfl) ⟨579857, by rfl⟩ : syracuseStep 773143 = 1159715) B1159715
theorem B773163 : Blo 770335 773163 := bstep (se 1 (by rfl) ⟨579872, by rfl⟩ : syracuseStep 773163 = 1159745) B1159745
theorem B1952819 : Blo 770335 1952819 := bstep (se 1 (by rfl) ⟨1464614, by rfl⟩ : syracuseStep 1952819 = 2929229) B2929229
theorem B773175 : Blo 770335 773175 := bstep (se 1 (by rfl) ⟨579881, by rfl⟩ : syracuseStep 773175 = 1159763) B1159763
theorem B773195 : Blo 770335 773195 := bstep (se 1 (by rfl) ⟨579896, by rfl⟩ : syracuseStep 773195 = 1159793) B1159793
theorem B773207 : Blo 770335 773207 := bstep (se 1 (by rfl) ⟨579905, by rfl⟩ : syracuseStep 773207 = 1159811) B1159811
theorem B3918941 : Blo 770335 3918941 := bstep (se 3 (by rfl) ⟨734801, by rfl⟩ : syracuseStep 3918941 = 1469603) B1469603
theorem B773227 : Blo 770335 773227 := bstep (se 1 (by rfl) ⟨579920, by rfl⟩ : syracuseStep 773227 = 1159841) B1159841
theorem B773239 : Blo 770335 773239 := bstep (se 1 (by rfl) ⟨579929, by rfl⟩ : syracuseStep 773239 = 1159859) B1159859
theorem B773259 : Blo 770335 773259 := bstep (se 1 (by rfl) ⟨579944, by rfl⟩ : syracuseStep 773259 = 1159889) B1159889
theorem B773271 : Blo 770335 773271 := bstep (se 1 (by rfl) ⟨579953, by rfl⟩ : syracuseStep 773271 = 1159907) B1159907
theorem B773291 : Blo 770335 773291 := bstep (se 1 (by rfl) ⟨579968, by rfl⟩ : syracuseStep 773291 = 1159937) B1159937
theorem B2608307 : Blo 770335 2608307 := bstep (se 1 (by rfl) ⟨1956230, by rfl⟩ : syracuseStep 2608307 = 3912461) B3912461
theorem B773303 : Blo 770335 773303 := bstep (se 1 (by rfl) ⟨579977, by rfl⟩ : syracuseStep 773303 = 1159955) B1159955
theorem B773323 : Blo 770335 773323 := bstep (se 1 (by rfl) ⟨579992, by rfl⟩ : syracuseStep 773323 = 1159985) B1159985
theorem B773335 : Blo 770335 773335 := bstep (se 1 (by rfl) ⟨580001, by rfl⟩ : syracuseStep 773335 = 1160003) B1160003
theorem B3296477 : Blo 770335 3296477 := bstep (se 3 (by rfl) ⟨618089, by rfl⟩ : syracuseStep 3296477 = 1236179) B1236179
theorem B773355 : Blo 770335 773355 := bstep (se 1 (by rfl) ⟨580016, by rfl⟩ : syracuseStep 773355 = 1160033) B1160033
theorem B773367 : Blo 770335 773367 := bstep (se 1 (by rfl) ⟨580025, by rfl⟩ : syracuseStep 773367 = 1160051) B1160051
theorem B773387 : Blo 770335 773387 := bstep (se 1 (by rfl) ⟨580040, by rfl⟩ : syracuseStep 773387 = 1160081) B1160081
theorem B773399 : Blo 770335 773399 := bstep (se 1 (by rfl) ⟨580049, by rfl⟩ : syracuseStep 773399 = 1160099) B1160099
theorem B773419 : Blo 770335 773419 := bstep (se 1 (by rfl) ⟨580064, by rfl⟩ : syracuseStep 773419 = 1160129) B1160129
theorem B773431 : Blo 770335 773431 := bstep (se 1 (by rfl) ⟨580073, by rfl⟩ : syracuseStep 773431 = 1160147) B1160147
theorem B773451 : Blo 770335 773451 := bstep (se 1 (by rfl) ⟨580088, by rfl⟩ : syracuseStep 773451 = 1160177) B1160177
theorem B773463 : Blo 770335 773463 := bstep (se 1 (by rfl) ⟨580097, by rfl⟩ : syracuseStep 773463 = 1160195) B1160195
theorem B773483 : Blo 770335 773483 := bstep (se 1 (by rfl) ⟨580112, by rfl⟩ : syracuseStep 773483 = 1160225) B1160225
theorem B773495 : Blo 770335 773495 := bstep (se 1 (by rfl) ⟨580121, by rfl⟩ : syracuseStep 773495 = 1160243) B1160243
theorem B773515 : Blo 770335 773515 := bstep (se 1 (by rfl) ⟨580136, by rfl⟩ : syracuseStep 773515 = 1160273) B1160273
theorem B773527 : Blo 770335 773527 := bstep (se 1 (by rfl) ⟨580145, by rfl⟩ : syracuseStep 773527 = 1160291) B1160291
theorem B773547 : Blo 770335 773547 := bstep (se 1 (by rfl) ⟨580160, by rfl⟩ : syracuseStep 773547 = 1160321) B1160321
theorem B773559 : Blo 770335 773559 := bstep (se 1 (by rfl) ⟨580169, by rfl⟩ : syracuseStep 773559 = 1160339) B1160339
theorem B1854913 : Blo 770335 1854913 := bstep (se 2 (by rfl) ⟨695592, by rfl⟩ : syracuseStep 1854913 = 1391185) B1391185
theorem B2608577 : Blo 770335 2608577 := bstep (se 2 (by rfl) ⟨978216, by rfl⟩ : syracuseStep 2608577 = 1956433) B1956433
theorem B773579 : Blo 770335 773579 := bstep (se 1 (by rfl) ⟨580184, by rfl⟩ : syracuseStep 773579 = 1160369) B1160369
theorem B773591 : Blo 770335 773591 := bstep (se 1 (by rfl) ⟨580193, by rfl⟩ : syracuseStep 773591 = 1160387) B1160387
theorem B773611 : Blo 770335 773611 := bstep (se 1 (by rfl) ⟨580208, by rfl⟩ : syracuseStep 773611 = 1160417) B1160417
theorem B773623 : Blo 770335 773623 := bstep (se 1 (by rfl) ⟨580217, by rfl⟩ : syracuseStep 773623 = 1160435) B1160435
theorem B773643 : Blo 770335 773643 := bstep (se 1 (by rfl) ⟨580232, by rfl⟩ : syracuseStep 773643 = 1160465) B1160465
theorem B773655 : Blo 770335 773655 := bstep (se 1 (by rfl) ⟨580241, by rfl⟩ : syracuseStep 773655 = 1160483) B1160483
theorem B773675 : Blo 770335 773675 := bstep (se 1 (by rfl) ⟨580256, by rfl⟩ : syracuseStep 773675 = 1160513) B1160513
theorem B773687 : Blo 770335 773687 := bstep (se 1 (by rfl) ⟨580265, by rfl⟩ : syracuseStep 773687 = 1160531) B1160531
theorem B1953355 : Blo 770335 1953355 := bstep (se 1 (by rfl) ⟨1465016, by rfl⟩ : syracuseStep 1953355 = 2930033) B2930033
theorem B773707 : Blo 770335 773707 := bstep (se 1 (by rfl) ⟨580280, by rfl⟩ : syracuseStep 773707 = 1160561) B1160561
theorem B773719 : Blo 770335 773719 := bstep (se 1 (by rfl) ⟨580289, by rfl⟩ : syracuseStep 773719 = 1160579) B1160579
theorem B773739 : Blo 770335 773739 := bstep (se 1 (by rfl) ⟨580304, by rfl⟩ : syracuseStep 773739 = 1160609) B1160609
theorem B773751 : Blo 770335 773751 := bstep (se 1 (by rfl) ⟨580313, by rfl⟩ : syracuseStep 773751 = 1160627) B1160627
theorem B1101451 : Blo 770335 1101451 := bstep (se 1 (by rfl) ⟨826088, by rfl⟩ : syracuseStep 1101451 = 1652177) B1652177
theorem B773771 : Blo 770335 773771 := bstep (se 1 (by rfl) ⟨580328, by rfl⟩ : syracuseStep 773771 = 1160657) B1160657
theorem B773783 : Blo 770335 773783 := bstep (se 1 (by rfl) ⟨580337, by rfl⟩ : syracuseStep 773783 = 1160675) B1160675
theorem B773803 : Blo 770335 773803 := bstep (se 1 (by rfl) ⟨580352, by rfl⟩ : syracuseStep 773803 = 1160705) B1160705
theorem B773815 : Blo 770335 773815 := bstep (se 1 (by rfl) ⟨580361, by rfl⟩ : syracuseStep 773815 = 1160723) B1160723
theorem B773835 : Blo 770335 773835 := bstep (se 1 (by rfl) ⟨580376, by rfl⟩ : syracuseStep 773835 = 1160753) B1160753
theorem B773847 : Blo 770335 773847 := bstep (se 1 (by rfl) ⟨580385, by rfl⟩ : syracuseStep 773847 = 1160771) B1160771
theorem B1953497 : Blo 770335 1953497 := bstep (se 2 (by rfl) ⟨732561, by rfl⟩ : syracuseStep 1953497 = 1465123) B1465123
theorem B773867 : Blo 770335 773867 := bstep (se 1 (by rfl) ⟨580400, by rfl⟩ : syracuseStep 773867 = 1160801) B1160801
theorem B773879 : Blo 770335 773879 := bstep (se 1 (by rfl) ⟨580409, by rfl⟩ : syracuseStep 773879 = 1160819) B1160819
theorem B773899 : Blo 770335 773899 := bstep (se 1 (by rfl) ⟨580424, by rfl⟩ : syracuseStep 773899 = 1160849) B1160849
theorem B773911 : Blo 770335 773911 := bstep (se 1 (by rfl) ⟨580433, by rfl⟩ : syracuseStep 773911 = 1160867) B1160867
theorem B773931 : Blo 770335 773931 := bstep (se 1 (by rfl) ⟨580448, by rfl⟩ : syracuseStep 773931 = 1160897) B1160897
theorem B773943 : Blo 770335 773943 := bstep (se 1 (by rfl) ⟨580457, by rfl⟩ : syracuseStep 773943 = 1160915) B1160915
theorem B773963 : Blo 770335 773963 := bstep (se 1 (by rfl) ⟨580472, by rfl⟩ : syracuseStep 773963 = 1160945) B1160945
theorem B773975 : Blo 770335 773975 := bstep (se 1 (by rfl) ⟨580481, by rfl⟩ : syracuseStep 773975 = 1160963) B1160963
theorem B29642597 : Blo 770335 29642597 := bstep (se 4 (by rfl) ⟨2778993, by rfl⟩ : syracuseStep 29642597 = 5557987) B5557987
theorem B773995 : Blo 770335 773995 := bstep (se 1 (by rfl) ⟨580496, by rfl⟩ : syracuseStep 773995 = 1160993) B1160993
theorem B774007 : Blo 770335 774007 := bstep (se 1 (by rfl) ⟨580505, by rfl⟩ : syracuseStep 774007 = 1161011) B1161011
theorem B774027 : Blo 770335 774027 := bstep (se 1 (by rfl) ⟨580520, by rfl⟩ : syracuseStep 774027 = 1161041) B1161041
theorem B774039 : Blo 770335 774039 := bstep (se 1 (by rfl) ⟨580529, by rfl⟩ : syracuseStep 774039 = 1161059) B1161059
theorem B774059 : Blo 770335 774059 := bstep (se 1 (by rfl) ⟨580544, by rfl⟩ : syracuseStep 774059 = 1161089) B1161089
theorem B774071 : Blo 770335 774071 := bstep (se 1 (by rfl) ⟨580553, by rfl⟩ : syracuseStep 774071 = 1161107) B1161107
theorem B774091 : Blo 770335 774091 := bstep (se 1 (by rfl) ⟨580568, by rfl⟩ : syracuseStep 774091 = 1161137) B1161137
theorem B774103 : Blo 770335 774103 := bstep (se 1 (by rfl) ⟨580577, by rfl⟩ : syracuseStep 774103 = 1161155) B1161155
theorem B2609117 : Blo 770335 2609117 := bstep (se 3 (by rfl) ⟨489209, by rfl⟩ : syracuseStep 2609117 = 978419) B978419
theorem B774123 : Blo 770335 774123 := bstep (se 1 (by rfl) ⟨580592, by rfl⟩ : syracuseStep 774123 = 1161185) B1161185
theorem B774135 : Blo 770335 774135 := bstep (se 1 (by rfl) ⟨580601, by rfl⟩ : syracuseStep 774135 = 1161203) B1161203
theorem B774155 : Blo 770335 774155 := bstep (se 1 (by rfl) ⟨580616, by rfl⟩ : syracuseStep 774155 = 1161233) B1161233
theorem B774167 : Blo 770335 774167 := bstep (se 1 (by rfl) ⟨580625, by rfl⟩ : syracuseStep 774167 = 1161251) B1161251
theorem B23777315 : Blo 770335 23777315 := bstep (se 1 (by rfl) ⟨17832986, by rfl⟩ : syracuseStep 23777315 = 35665973) B35665973
theorem B774187 : Blo 770335 774187 := bstep (se 1 (by rfl) ⟨580640, by rfl⟩ : syracuseStep 774187 = 1161281) B1161281
theorem B774199 : Blo 770335 774199 := bstep (se 1 (by rfl) ⟨580649, by rfl⟩ : syracuseStep 774199 = 1161299) B1161299
theorem B774219 : Blo 770335 774219 := bstep (se 1 (by rfl) ⟨580664, by rfl⟩ : syracuseStep 774219 = 1161329) B1161329
theorem B774231 : Blo 770335 774231 := bstep (se 1 (by rfl) ⟨580673, by rfl⟩ : syracuseStep 774231 = 1161347) B1161347
theorem B774251 : Blo 770335 774251 := bstep (se 1 (by rfl) ⟨580688, by rfl⟩ : syracuseStep 774251 = 1161377) B1161377
theorem B774263 : Blo 770335 774263 := bstep (se 1 (by rfl) ⟨580697, by rfl⟩ : syracuseStep 774263 = 1161395) B1161395
theorem B774283 : Blo 770335 774283 := bstep (se 1 (by rfl) ⟨580712, by rfl⟩ : syracuseStep 774283 = 1161425) B1161425
theorem B774295 : Blo 770335 774295 := bstep (se 1 (by rfl) ⟨580721, by rfl⟩ : syracuseStep 774295 = 1161443) B1161443
theorem B774315 : Blo 770335 774315 := bstep (se 1 (by rfl) ⟨580736, by rfl⟩ : syracuseStep 774315 = 1161473) B1161473
theorem B2937005 : Blo 770335 2937005 := bstep (se 3 (by rfl) ⟨550688, by rfl⟩ : syracuseStep 2937005 = 1101377) B1101377
theorem B774327 : Blo 770335 774327 := bstep (se 1 (by rfl) ⟨580745, by rfl⟩ : syracuseStep 774327 = 1161491) B1161491
theorem B1462465 : Blo 770335 1462465 := bstep (se 2 (by rfl) ⟨548424, by rfl⟩ : syracuseStep 1462465 = 1096849) B1096849
theorem B6607169 : Blo 770335 6607169 := bstep (se 2 (by rfl) ⟨2477688, by rfl⟩ : syracuseStep 6607169 = 4955377) B4955377
theorem B1954327 : Blo 770335 1954327 := bstep (se 1 (by rfl) ⟨1465745, by rfl⟩ : syracuseStep 1954327 = 2931491) B2931491
theorem B1757963 : Blo 770335 1757963 := bstep (se 1 (by rfl) ⟨1318472, by rfl⟩ : syracuseStep 1757963 = 2636945) B2636945
theorem B15848257 : Blo 770335 15848257 := bstep (se 2 (by rfl) ⟨5943096, by rfl⟩ : syracuseStep 15848257 = 11886193) B11886193
theorem B1463179 : Blo 770335 1463179 := bstep (se 1 (by rfl) ⟨1097384, by rfl⟩ : syracuseStep 1463179 = 2194769) B2194769
theorem B2937779 : Blo 770335 2937779 := bstep (se 1 (by rfl) ⟨2203334, by rfl⟩ : syracuseStep 2937779 = 4406669) B4406669
theorem B1954763 : Blo 770335 1954763 := bstep (se 1 (by rfl) ⟨1466072, by rfl⟩ : syracuseStep 1954763 = 2932145) B2932145
theorem B1463255 : Blo 770335 1463255 := bstep (se 1 (by rfl) ⟨1097441, by rfl⟩ : syracuseStep 1463255 = 2194883) B2194883
theorem B8803403 : Blo 770335 8803403 := bstep (se 1 (by rfl) ⟨6602552, by rfl⟩ : syracuseStep 8803403 = 13205105) B13205105
theorem B2610251 : Blo 770335 2610251 := bstep (se 1 (by rfl) ⟨1957688, by rfl⟩ : syracuseStep 2610251 = 3915377) B3915377
theorem B11293789 : Blo 770335 11293789 := bstep (se 3 (by rfl) ⟨2117585, by rfl⟩ : syracuseStep 11293789 = 4235171) B4235171
theorem B3134609 : Blo 770335 3134609 := bstep (se 2 (by rfl) ⟨1175478, by rfl⟩ : syracuseStep 3134609 = 2350957) B2350957
theorem B1856729 : Blo 770335 1856729 := bstep (se 2 (by rfl) ⟨696273, by rfl⟩ : syracuseStep 1856729 = 1392547) B1392547
theorem B1955137 : Blo 770335 1955137 := bstep (se 2 (by rfl) ⟨733176, by rfl⟩ : syracuseStep 1955137 = 1466353) B1466353
theorem B2610521 : Blo 770335 2610521 := bstep (se 2 (by rfl) ⟨978945, by rfl⟩ : syracuseStep 2610521 = 1957891) B1957891
theorem B1300043 : Blo 770335 1300043 := bstep (se 1 (by rfl) ⟨975032, by rfl⟩ : syracuseStep 1300043 = 1950065) B1950065
theorem B1463923 : Blo 770335 1463923 := bstep (se 1 (by rfl) ⟨1097942, by rfl⟩ : syracuseStep 1463923 = 2195885) B2195885
theorem B1300171 : Blo 770335 1300171 := bstep (se 1 (by rfl) ⟨975128, by rfl⟩ : syracuseStep 1300171 = 1950257) B1950257
theorem B2086603 : Blo 770335 2086603 := bstep (se 1 (by rfl) ⟨1564952, by rfl⟩ : syracuseStep 2086603 = 3129905) B3129905
theorem B3299075 : Blo 770335 3299075 := bstep (se 1 (by rfl) ⟨2474306, by rfl⟩ : syracuseStep 3299075 = 4948613) B4948613
theorem B1464151 : Blo 770335 1464151 := bstep (se 1 (by rfl) ⟨1098113, by rfl⟩ : syracuseStep 1464151 = 2196227) B2196227
theorem B1300313 : Blo 770335 1300313 := bstep (se 2 (by rfl) ⟨487617, by rfl⟩ : syracuseStep 1300313 = 975235) B975235
theorem B1955735 : Blo 770335 1955735 := bstep (se 1 (by rfl) ⟨1466801, by rfl⟩ : syracuseStep 1955735 = 2933603) B2933603
theorem B1464257 : Blo 770335 1464257 := bstep (se 2 (by rfl) ⟨549096, by rfl⟩ : syracuseStep 1464257 = 1098193) B1098193
theorem B1300441 : Blo 770335 1300441 := bstep (se 2 (by rfl) ⟨487665, by rfl⟩ : syracuseStep 1300441 = 975331) B975331
theorem B1234955 : Blo 770335 1234955 := bstep (se 1 (by rfl) ⟨926216, by rfl⟩ : syracuseStep 1234955 = 1852433) B1852433
theorem B2611223 : Blo 770335 2611223 := bstep (se 1 (by rfl) ⟨1958417, by rfl⟩ : syracuseStep 2611223 = 3916835) B3916835
theorem B1464409 : Blo 770335 1464409 := bstep (se 2 (by rfl) ⟨549153, by rfl⟩ : syracuseStep 1464409 = 1098307) B1098307
theorem B1235083 : Blo 770335 1235083 := bstep (se 1 (by rfl) ⟨926312, by rfl⟩ : syracuseStep 1235083 = 1852625) B1852625
theorem B1235225 : Blo 770335 1235225 := bstep (se 2 (by rfl) ⟨463209, by rfl⟩ : syracuseStep 1235225 = 926419) B926419
theorem B2939267 : Blo 770335 2939267 := bstep (se 1 (by rfl) ⟨2204450, by rfl⟩ : syracuseStep 2939267 = 4408901) B4408901
theorem B2513369 : Blo 770335 2513369 := bstep (se 2 (by rfl) ⟨942513, by rfl⟩ : syracuseStep 2513369 = 1885027) B1885027
theorem B1301015 : Blo 770335 1301015 := bstep (se 1 (by rfl) ⟨975761, by rfl⟩ : syracuseStep 1301015 = 1951523) B1951523
theorem B2611763 : Blo 770335 2611763 := bstep (se 1 (by rfl) ⟨1958822, by rfl⟩ : syracuseStep 2611763 = 3917645) B3917645
theorem B2415193 : Blo 770335 2415193 := bstep (se 2 (by rfl) ⟨905697, by rfl⟩ : syracuseStep 2415193 = 1811395) B1811395
theorem B1301143 : Blo 770335 1301143 := bstep (se 1 (by rfl) ⟨975857, by rfl⟩ : syracuseStep 1301143 = 1951715) B1951715
theorem B1956545 : Blo 770335 1956545 := bstep (se 2 (by rfl) ⟨733704, by rfl⟩ : syracuseStep 1956545 = 1467409) B1467409
theorem B6675149 : Blo 770335 6675149 := bstep (se 3 (by rfl) ⟨1251590, by rfl⟩ : syracuseStep 6675149 = 2503181) B2503181
theorem B2612033 : Blo 770335 2612033 := bstep (se 2 (by rfl) ⟨979512, by rfl⟩ : syracuseStep 2612033 = 1959025) B1959025
theorem B2939723 : Blo 770335 2939723 := bstep (se 1 (by rfl) ⟨2204792, by rfl⟩ : syracuseStep 2939723 = 4409585) B4409585
theorem B3431347 : Blo 770335 3431347 := bstep (se 1 (by rfl) ⟨2573510, by rfl⟩ : syracuseStep 3431347 = 5147021) B5147021
theorem B2939921 : Blo 770335 2939921 := bstep (se 2 (by rfl) ⟨1102470, by rfl⟩ : syracuseStep 2939921 = 2204941) B2204941
theorem B1858583 : Blo 770335 1858583 := bstep (se 1 (by rfl) ⟨1393937, by rfl⟩ : syracuseStep 1858583 = 2787875) B2787875
theorem B3529793 : Blo 770335 3529793 := bstep (se 2 (by rfl) ⟨1323672, by rfl⟩ : syracuseStep 3529793 = 2647345) B2647345
theorem B13196357 : Blo 770335 13196357 := bstep (se 4 (by rfl) ⟨1237158, by rfl⟩ : syracuseStep 13196357 = 2474317) B2474317
theorem B2088139 : Blo 770335 2088139 := bstep (se 1 (by rfl) ⟨1566104, by rfl⟩ : syracuseStep 2088139 = 3132209) B3132209
theorem B1957081 : Blo 770335 1957081 := bstep (se 2 (by rfl) ⟨733905, by rfl⟩ : syracuseStep 1957081 = 1467811) B1467811
theorem B1301771 : Blo 770335 1301771 := bstep (se 1 (by rfl) ⟨976328, by rfl⟩ : syracuseStep 1301771 = 1952657) B1952657
theorem B12541229 : Blo 770335 12541229 := bstep (se 3 (by rfl) ⟨2351480, by rfl⟩ : syracuseStep 12541229 = 4702961) B4702961
theorem B1858891 : Blo 770335 1858891 := bstep (se 1 (by rfl) ⟨1394168, by rfl⟩ : syracuseStep 1858891 = 2788337) B2788337
theorem B1236313 : Blo 770335 1236313 := bstep (se 2 (by rfl) ⟨463617, by rfl⟩ : syracuseStep 1236313 = 927235) B927235
theorem B2612573 : Blo 770335 2612573 := bstep (se 3 (by rfl) ⟨489857, by rfl⟩ : syracuseStep 2612573 = 979715) B979715
theorem B1465715 : Blo 770335 1465715 := bstep (se 1 (by rfl) ⟨1099286, by rfl⟩ : syracuseStep 1465715 = 2198573) B2198573
theorem B1301899 : Blo 770335 1301899 := bstep (se 1 (by rfl) ⟨976424, by rfl⟩ : syracuseStep 1301899 = 1952849) B1952849
theorem B1465867 : Blo 770335 1465867 := bstep (se 1 (by rfl) ⟨1099400, by rfl⟩ : syracuseStep 1465867 = 2198801) B2198801
theorem B5856785 : Blo 770335 5856785 := bstep (se 2 (by rfl) ⟨2196294, by rfl⟩ : syracuseStep 5856785 = 4392589) B4392589
theorem B941591 : Blo 770335 941591 := bstep (se 1 (by rfl) ⟨706193, by rfl⟩ : syracuseStep 941591 = 1412387) B1412387
theorem B1302041 : Blo 770335 1302041 := bstep (se 2 (by rfl) ⟨488265, by rfl⟩ : syracuseStep 1302041 = 976531) B976531
theorem B1302169 : Blo 770335 1302169 := bstep (se 2 (by rfl) ⟨488313, by rfl⟩ : syracuseStep 1302169 = 976627) B976627
theorem B1859275 : Blo 770335 1859275 := bstep (se 1 (by rfl) ⟨1394456, by rfl⟩ : syracuseStep 1859275 = 2788913) B2788913
theorem B1466201 : Blo 770335 1466201 := bstep (se 2 (by rfl) ⟨549825, by rfl⟩ : syracuseStep 1466201 = 1099651) B1099651
theorem B4939613 : Blo 770335 4939613 := bstep (se 3 (by rfl) ⟨926177, by rfl⟩ : syracuseStep 4939613 = 1852355) B1852355
theorem B1859507 : Blo 770335 1859507 := bstep (se 1 (by rfl) ⟨1394630, by rfl⟩ : syracuseStep 1859507 = 2789261) B2789261
theorem B16670681 : Blo 770335 16670681 := bstep (se 2 (by rfl) ⟨6251505, by rfl⟩ : syracuseStep 16670681 = 12503011) B12503011
theorem B1302743 : Blo 770335 1302743 := bstep (se 1 (by rfl) ⟨977057, by rfl⟩ : syracuseStep 1302743 = 1954115) B1954115
theorem B1958195 : Blo 770335 1958195 := bstep (se 1 (by rfl) ⟨1468646, by rfl⟩ : syracuseStep 1958195 = 2937293) B2937293
theorem B975179 : Blo 770335 975179 := bstep (se 1 (by rfl) ⟨731384, by rfl⟩ : syracuseStep 975179 = 1462769) B1462769
theorem B1302871 : Blo 770335 1302871 := bstep (se 1 (by rfl) ⟨977153, by rfl⟩ : syracuseStep 1302871 = 1954307) B1954307
theorem B8348021 : Blo 770335 8348021 := bstep (se 5 (by rfl) ⟨391313, by rfl⟩ : syracuseStep 8348021 = 782627) B782627
theorem B1466839 : Blo 770335 1466839 := bstep (se 1 (by rfl) ⟨1100129, by rfl⟩ : syracuseStep 1466839 = 2200259) B2200259
theorem B2089547 : Blo 770335 2089547 := bstep (se 1 (by rfl) ⟨1567160, by rfl⟩ : syracuseStep 2089547 = 3134321) B3134321
theorem B1958489 : Blo 770335 1958489 := bstep (se 2 (by rfl) ⟨734433, by rfl⟩ : syracuseStep 1958489 = 1468867) B1468867
theorem B5563181 : Blo 770335 5563181 := bstep (se 3 (by rfl) ⟨1043096, by rfl⟩ : syracuseStep 5563181 = 2086193) B2086193
theorem B1303499 : Blo 770335 1303499 := bstep (se 1 (by rfl) ⟨977624, by rfl⟩ : syracuseStep 1303499 = 1955249) B1955249
theorem B975883 : Blo 770335 975883 := bstep (se 1 (by rfl) ⟨731912, by rfl⟩ : syracuseStep 975883 = 1463825) B1463825
theorem B1303627 : Blo 770335 1303627 := bstep (se 1 (by rfl) ⟨977720, by rfl⟩ : syracuseStep 1303627 = 1955441) B1955441
theorem B5563523 : Blo 770335 5563523 := bstep (se 1 (by rfl) ⟨4172642, by rfl⟩ : syracuseStep 5563523 = 8345285) B8345285
theorem B3531907 : Blo 770335 3531907 := bstep (se 1 (by rfl) ⟨2648930, by rfl⟩ : syracuseStep 3531907 = 5297861) B5297861
theorem B1303769 : Blo 770335 1303769 := bstep (se 2 (by rfl) ⟨488913, by rfl⟩ : syracuseStep 1303769 = 977827) B977827
theorem B1467659 : Blo 770335 1467659 := bstep (se 1 (by rfl) ⟨1100744, by rfl⟩ : syracuseStep 1467659 = 2201489) B2201489
theorem B976151 : Blo 770335 976151 := bstep (se 1 (by rfl) ⟨732113, by rfl⟩ : syracuseStep 976151 = 1464227) B1464227
theorem B4941101 : Blo 770335 4941101 := bstep (se 3 (by rfl) ⟨926456, by rfl⟩ : syracuseStep 4941101 = 1852913) B1852913
theorem B1467713 : Blo 770335 1467713 := bstep (se 2 (by rfl) ⟨550392, by rfl⟩ : syracuseStep 1467713 = 1100785) B1100785
theorem B1303897 : Blo 770335 1303897 := bstep (se 2 (by rfl) ⟨488961, by rfl⟩ : syracuseStep 1303897 = 977923) B977923
theorem B3302849 : Blo 770335 3302849 := bstep (se 2 (by rfl) ⟨1238568, by rfl⟩ : syracuseStep 3302849 = 2477137) B2477137
theorem B6350411 : Blo 770335 6350411 := bstep (se 1 (by rfl) ⟨4762808, by rfl⟩ : syracuseStep 6350411 = 9525617) B9525617
theorem B2090647 : Blo 770335 2090647 := bstep (se 1 (by rfl) ⟨1567985, by rfl⟩ : syracuseStep 2090647 = 3135971) B3135971
theorem B1304471 : Blo 770335 1304471 := bstep (se 1 (by rfl) ⟨978353, by rfl⟩ : syracuseStep 1304471 = 1956707) B1956707
theorem B3139507 : Blo 770335 3139507 := bstep (se 1 (by rfl) ⟨2354630, by rfl⟩ : syracuseStep 3139507 = 4709261) B4709261
theorem B6612941 : Blo 770335 6612941 := bstep (se 3 (by rfl) ⟨1239926, by rfl⟩ : syracuseStep 6612941 = 2479853) B2479853
theorem B976855 : Blo 770335 976855 := bstep (se 1 (by rfl) ⟨732641, by rfl⟩ : syracuseStep 976855 = 1465283) B1465283
theorem B1304599 : Blo 770335 1304599 := bstep (se 1 (by rfl) ⟨978449, by rfl⟩ : syracuseStep 1304599 = 1956899) B1956899
theorem B878635 : Blo 770335 878635 := bstep (se 1 (by rfl) ⟨658976, by rfl⟩ : syracuseStep 878635 = 1317953) B1317953
theorem B1468631 : Blo 770335 1468631 := bstep (se 1 (by rfl) ⟨1101473, by rfl⟩ : syracuseStep 1468631 = 2202947) B2202947
theorem B3303773 : Blo 770335 3303773 := bstep (se 3 (by rfl) ⟨619457, by rfl⟩ : syracuseStep 3303773 = 1238915) B1238915
theorem B2779571 : Blo 770335 2779571 := bstep (se 1 (by rfl) ⟨2084678, by rfl⟩ : syracuseStep 2779571 = 4169357) B4169357
theorem B1305227 : Blo 770335 1305227 := bstep (se 1 (by rfl) ⟨978920, by rfl⟩ : syracuseStep 1305227 = 1957841) B1957841
theorem B1469171 : Blo 770335 1469171 := bstep (se 1 (by rfl) ⟨1101878, by rfl⟩ : syracuseStep 1469171 = 2203757) B2203757
theorem B1305355 : Blo 770335 1305355 := bstep (se 1 (by rfl) ⟨979016, by rfl⟩ : syracuseStep 1305355 = 1958033) B1958033
theorem B1305497 : Blo 770335 1305497 := bstep (se 2 (by rfl) ⟨489561, by rfl⟩ : syracuseStep 1305497 = 979123) B979123
theorem B1764275 : Blo 770335 1764275 := bstep (se 1 (by rfl) ⟨1323206, by rfl⟩ : syracuseStep 1764275 = 2646413) B2646413
theorem B1305625 : Blo 770335 1305625 := bstep (se 2 (by rfl) ⟨489609, by rfl⟩ : syracuseStep 1305625 = 979219) B979219
theorem B1469657 : Blo 770335 1469657 := bstep (se 2 (by rfl) ⟨551121, by rfl⟩ : syracuseStep 1469657 = 1102243) B1102243
theorem B5860673 : Blo 770335 5860673 := bstep (se 2 (by rfl) ⟨2197752, by rfl⟩ : syracuseStep 5860673 = 4395505) B4395505
theorem B1306199 : Blo 770335 1306199 := bstep (se 1 (by rfl) ⟨979649, by rfl⟩ : syracuseStep 1306199 = 1959299) B1959299
theorem B2092637 : Blo 770335 2092637 := bstep (se 3 (by rfl) ⟨392369, by rfl⟩ : syracuseStep 2092637 = 784739) B784739
theorem B4025987 : Blo 770335 4025987 := bstep (se 1 (by rfl) ⟨3019490, by rfl⟩ : syracuseStep 4025987 = 6038981) B6038981
theorem B978571 : Blo 770335 978571 := bstep (se 1 (by rfl) ⟨733928, by rfl⟩ : syracuseStep 978571 = 1467857) B1467857
theorem B1306327 : Blo 770335 1306327 := bstep (se 1 (by rfl) ⟨979745, by rfl⟩ : syracuseStep 1306327 = 1959491) B1959491
theorem B16674659 : Blo 770335 16674659 := bstep (se 1 (by rfl) ⟨12505994, by rfl⟩ : syracuseStep 16674659 = 25011989) B25011989
theorem B1044427 : Blo 770335 1044427 := bstep (se 1 (by rfl) ⟨783320, by rfl⟩ : syracuseStep 1044427 = 1566641) B1566641
theorem B782347 : Blo 770335 782347 := bstep (se 1 (by rfl) ⟨586760, by rfl⟩ : syracuseStep 782347 = 1173521) B1173521
theorem B880651 : Blo 770335 880651 := bstep (se 1 (by rfl) ⟨660488, by rfl⟩ : syracuseStep 880651 = 1320977) B1320977
theorem B4944023 : Blo 770335 4944023 := bstep (se 1 (by rfl) ⟨3708017, by rfl⟩ : syracuseStep 4944023 = 7416035) B7416035
theorem B979543 : Blo 770335 979543 := bstep (se 1 (by rfl) ⟨734657, by rfl⟩ : syracuseStep 979543 = 1469315) B1469315
theorem B13529693 : Blo 770335 13529693 := bstep (se 3 (by rfl) ⟨2536817, by rfl⟩ : syracuseStep 13529693 = 5073635) B5073635
theorem B1733273 : Blo 770335 1733273 := bstep (se 2 (by rfl) ⟨649977, by rfl⟩ : syracuseStep 1733273 = 1299955) B1299955
theorem B1733363 : Blo 770335 1733363 := bstep (se 1 (by rfl) ⟨1300022, by rfl⟩ : syracuseStep 1733363 = 2600045) B2600045
theorem B1733399 : Blo 770335 1733399 := bstep (se 1 (by rfl) ⟨1300049, by rfl⟩ : syracuseStep 1733399 = 2600099) B2600099
theorem B6681419 : Blo 770335 6681419 := bstep (se 1 (by rfl) ⟨5011064, by rfl⟩ : syracuseStep 6681419 = 10022129) B10022129
theorem B4387715 : Blo 770335 4387715 := bstep (se 1 (by rfl) ⟨3290786, by rfl⟩ : syracuseStep 4387715 = 6581573) B6581573
theorem B2782097 : Blo 770335 2782097 := bstep (se 2 (by rfl) ⟨1043286, by rfl⟩ : syracuseStep 2782097 = 2086573) B2086573
theorem B1733579 : Blo 770335 1733579 := bstep (se 1 (by rfl) ⟨1300184, by rfl⟩ : syracuseStep 1733579 = 2600369) B2600369
theorem B1733633 : Blo 770335 1733633 := bstep (se 2 (by rfl) ⟨650112, by rfl⟩ : syracuseStep 1733633 = 1300225) B1300225
theorem B1733849 : Blo 770335 1733849 := bstep (se 2 (by rfl) ⟨650193, by rfl⟩ : syracuseStep 1733849 = 1300387) B1300387
theorem B5862617 : Blo 770335 5862617 := bstep (se 2 (by rfl) ⟨2198481, by rfl⟩ : syracuseStep 5862617 = 4396963) B4396963
theorem B1733939 : Blo 770335 1733939 := bstep (se 1 (by rfl) ⟨1300454, by rfl⟩ : syracuseStep 1733939 = 2600909) B2600909
theorem B1733975 : Blo 770335 1733975 := bstep (se 1 (by rfl) ⟨1300481, by rfl⟩ : syracuseStep 1733975 = 2600963) B2600963
theorem B1734155 : Blo 770335 1734155 := bstep (se 1 (by rfl) ⟨1300616, by rfl⟩ : syracuseStep 1734155 = 2601233) B2601233
theorem B1734209 : Blo 770335 1734209 := bstep (se 2 (by rfl) ⟨650328, by rfl⟩ : syracuseStep 1734209 = 1300657) B1300657
theorem B3307139 : Blo 770335 3307139 := bstep (se 1 (by rfl) ⟨2480354, by rfl⟩ : syracuseStep 3307139 = 4960709) B4960709
theorem B1734425 : Blo 770335 1734425 := bstep (se 2 (by rfl) ⟨650409, by rfl⟩ : syracuseStep 1734425 = 1300819) B1300819
theorem B1734515 : Blo 770335 1734515 := bstep (se 1 (by rfl) ⟨1300886, by rfl⟩ : syracuseStep 1734515 = 2601773) B2601773
theorem B1734551 : Blo 770335 1734551 := bstep (se 1 (by rfl) ⟨1300913, by rfl⟩ : syracuseStep 1734551 = 2601827) B2601827
theorem B35682227 : Blo 770335 35682227 := bstep (se 1 (by rfl) ⟨26761670, by rfl⟩ : syracuseStep 35682227 = 53523341) B53523341
theorem B1734731 : Blo 770335 1734731 := bstep (se 1 (by rfl) ⟨1301048, by rfl⟩ : syracuseStep 1734731 = 2602097) B2602097
theorem B1734785 : Blo 770335 1734785 := bstep (se 2 (by rfl) ⟨650544, by rfl⟩ : syracuseStep 1734785 = 1301089) B1301089
theorem B22313141 : Blo 770335 22313141 := bstep (se 5 (by rfl) ⟨1045928, by rfl⟩ : syracuseStep 22313141 = 2091857) B2091857
theorem B1735001 : Blo 770335 1735001 := bstep (se 2 (by rfl) ⟨650625, by rfl⟩ : syracuseStep 1735001 = 1301251) B1301251
theorem B1735091 : Blo 770335 1735091 := bstep (se 1 (by rfl) ⟨1301318, by rfl⟩ : syracuseStep 1735091 = 2602637) B2602637
theorem B1735127 : Blo 770335 1735127 := bstep (se 1 (by rfl) ⟨1301345, by rfl⟩ : syracuseStep 1735127 = 2602691) B2602691
theorem B1735307 : Blo 770335 1735307 := bstep (se 1 (by rfl) ⟨1301480, by rfl⟩ : syracuseStep 1735307 = 2602961) B2602961
theorem B1735361 : Blo 770335 1735361 := bstep (se 2 (by rfl) ⟨650760, by rfl⟩ : syracuseStep 1735361 = 1301521) B1301521
theorem B1669835 : Blo 770335 1669835 := bstep (se 1 (by rfl) ⟨1252376, by rfl⟩ : syracuseStep 1669835 = 2504753) B2504753
theorem B2194199 : Blo 770335 2194199 := bstep (se 1 (by rfl) ⟨1645649, by rfl⟩ : syracuseStep 2194199 = 3291299) B3291299
theorem B1735577 : Blo 770335 1735577 := bstep (se 2 (by rfl) ⟨650841, by rfl⟩ : syracuseStep 1735577 = 1301683) B1301683
theorem B1735667 : Blo 770335 1735667 := bstep (se 1 (by rfl) ⟨1301750, by rfl⟩ : syracuseStep 1735667 = 2603501) B2603501
theorem B1735703 : Blo 770335 1735703 := bstep (se 1 (by rfl) ⟨1301777, by rfl⟩ : syracuseStep 1735703 = 2603555) B2603555
theorem B10026019 : Blo 770335 10026019 := bstep (se 1 (by rfl) ⟨7519514, by rfl⟩ : syracuseStep 10026019 = 15039029) B15039029
theorem B1735883 : Blo 770335 1735883 := bstep (se 1 (by rfl) ⟨1301912, by rfl⟩ : syracuseStep 1735883 = 2603825) B2603825
theorem B2784473 : Blo 770335 2784473 := bstep (se 2 (by rfl) ⟨1044177, by rfl⟩ : syracuseStep 2784473 = 2088355) B2088355
theorem B1735937 : Blo 770335 1735937 := bstep (se 2 (by rfl) ⟨650976, by rfl⟩ : syracuseStep 1735937 = 1301953) B1301953
theorem B4685273 : Blo 770335 4685273 := bstep (se 2 (by rfl) ⟨1756977, by rfl⟩ : syracuseStep 4685273 = 3513955) B3513955
theorem B1736153 : Blo 770335 1736153 := bstep (se 2 (by rfl) ⟨651057, by rfl⟩ : syracuseStep 1736153 = 1302115) B1302115
theorem B1736243 : Blo 770335 1736243 := bstep (se 1 (by rfl) ⟨1302182, by rfl⟩ : syracuseStep 1736243 = 2604365) B2604365
theorem B2195009 : Blo 770335 2195009 := bstep (se 2 (by rfl) ⟨823128, by rfl⟩ : syracuseStep 2195009 = 1646257) B1646257
theorem B1736279 : Blo 770335 1736279 := bstep (se 1 (by rfl) ⟨1302209, by rfl⟩ : syracuseStep 1736279 = 2604419) B2604419
theorem B4947587 : Blo 770335 4947587 := bstep (se 1 (by rfl) ⟨3710690, by rfl⟩ : syracuseStep 4947587 = 7421381) B7421381
theorem B3210931 : Blo 770335 3210931 := bstep (se 1 (by rfl) ⟨2408198, by rfl⟩ : syracuseStep 3210931 = 4816397) B4816397
theorem B1736459 : Blo 770335 1736459 := bstep (se 1 (by rfl) ⟨1302344, by rfl⟩ : syracuseStep 1736459 = 2604689) B2604689
theorem B1736513 : Blo 770335 1736513 := bstep (se 2 (by rfl) ⟨651192, by rfl⟩ : syracuseStep 1736513 = 1302385) B1302385
theorem B1736747 : Blo 770335 1736747 := bstep (se 1 (by rfl) ⟨1302560, by rfl⟩ : syracuseStep 1736747 = 2605121) B2605121
theorem B5865533 : Blo 770335 5865533 := bstep (se 3 (by rfl) ⟨1099787, by rfl⟩ : syracuseStep 5865533 = 2199575) B2199575
theorem B2785367 : Blo 770335 2785367 := bstep (se 1 (by rfl) ⟨2089025, by rfl⟩ : syracuseStep 2785367 = 4178051) B4178051
theorem B2195657 : Blo 770335 2195657 := bstep (se 2 (by rfl) ⟨823371, by rfl⟩ : syracuseStep 2195657 = 1646743) B1646743
theorem B14811457 : Blo 770335 14811457 := bstep (se 2 (by rfl) ⟨5554296, by rfl⟩ : syracuseStep 14811457 = 11108593) B11108593
theorem B1737107 : Blo 770335 1737107 := bstep (se 1 (by rfl) ⟨1302830, by rfl⟩ : syracuseStep 1737107 = 2605661) B2605661
theorem B1737161 : Blo 770335 1737161 := bstep (se 2 (by rfl) ⟨651435, by rfl⟩ : syracuseStep 1737161 = 1302871) B1302871
theorem B2196011 : Blo 770335 2196011 := bstep (se 1 (by rfl) ⟨1647008, by rfl⟩ : syracuseStep 2196011 = 3294017) B3294017
theorem B2785859 : Blo 770335 2785859 := bstep (se 1 (by rfl) ⟨2089394, by rfl⟩ : syracuseStep 2785859 = 4178789) B4178789
theorem B7045861 : Blo 770335 7045861 := bstep (se 4 (by rfl) ⟨660549, by rfl⟩ : syracuseStep 7045861 = 1321099) B1321099
theorem B2196409 : Blo 770335 2196409 := bstep (se 2 (by rfl) ⟨823653, by rfl⟩ : syracuseStep 2196409 = 1647307) B1647307
theorem B1115255 : Blo 770335 1115255 := bstep (se 1 (by rfl) ⟨836441, by rfl⟩ : syracuseStep 1115255 = 1672883) B1672883
theorem B1737863 : Blo 770335 1737863 := bstep (se 1 (by rfl) ⟨1303397, by rfl⟩ : syracuseStep 1737863 = 2606795) B2606795
theorem B3703981 : Blo 770335 3703981 := bstep (se 3 (by rfl) ⟨694496, by rfl⟩ : syracuseStep 3703981 = 1388993) B1388993
theorem B1738043 : Blo 770335 1738043 := bstep (se 1 (by rfl) ⟨1303532, by rfl⟩ : syracuseStep 1738043 = 2607065) B2607065
theorem B1738169 : Blo 770335 1738169 := bstep (se 2 (by rfl) ⟨651813, by rfl⟩ : syracuseStep 1738169 = 1303627) B1303627
theorem B36079181 : Blo 770335 36079181 := bstep (se 3 (by rfl) ⟨6764846, by rfl⟩ : syracuseStep 36079181 = 13529693) B13529693
theorem B3901121 : Blo 770335 3901121 := bstep (se 2 (by rfl) ⟨1462920, by rfl⟩ : syracuseStep 3901121 = 2925841) B2925841
theorem B5572289 : Blo 770335 5572289 := bstep (se 2 (by rfl) ⟨2089608, by rfl⟩ : syracuseStep 5572289 = 4179217) B4179217
theorem B1738511 : Blo 770335 1738511 := bstep (se 1 (by rfl) ⟨1303883, by rfl⟩ : syracuseStep 1738511 = 2607767) B2607767
theorem B1738529 : Blo 770335 1738529 := bstep (se 2 (by rfl) ⟨651948, by rfl⟩ : syracuseStep 1738529 = 1303897) B1303897
theorem B1116175 : Blo 770335 1116175 := bstep (se 1 (by rfl) ⟨837131, by rfl⟩ : syracuseStep 1116175 = 1674263) B1674263
theorem B4687901 : Blo 770335 4687901 := bstep (se 3 (by rfl) ⟨878981, by rfl⟩ : syracuseStep 4687901 = 1757963) B1757963
theorem B1738871 : Blo 770335 1738871 := bstep (se 1 (by rfl) ⟨1304153, by rfl⟩ : syracuseStep 1738871 = 2608307) B2608307
theorem B2197651 : Blo 770335 2197651 := bstep (se 1 (by rfl) ⟨1648238, by rfl⟩ : syracuseStep 2197651 = 3296477) B3296477
theorem B2787529 : Blo 770335 2787529 := bstep (se 2 (by rfl) ⟨1045323, by rfl⟩ : syracuseStep 2787529 = 2090647) B2090647
theorem B1739051 : Blo 770335 1739051 := bstep (se 1 (by rfl) ⟨1304288, by rfl⟩ : syracuseStep 1739051 = 2608577) B2608577
theorem B8784449 : Blo 770335 8784449 := bstep (se 2 (by rfl) ⟨3294168, by rfl⟩ : syracuseStep 8784449 = 6588337) B6588337
theorem B19761731 : Blo 770335 19761731 := bstep (se 1 (by rfl) ⟨14821298, by rfl⟩ : syracuseStep 19761731 = 29642597) B29642597
theorem B1739411 : Blo 770335 1739411 := bstep (se 1 (by rfl) ⟨1304558, by rfl⟩ : syracuseStep 1739411 = 2609117) B2609117
theorem B1739465 : Blo 770335 1739465 := bstep (se 2 (by rfl) ⟨652299, by rfl⟩ : syracuseStep 1739465 = 1304599) B1304599
theorem B3902417 : Blo 770335 3902417 := bstep (se 2 (by rfl) ⟨1463406, by rfl⟩ : syracuseStep 3902417 = 2926813) B2926813
theorem B12881029 : Blo 770335 12881029 := bstep (se 4 (by rfl) ⟨1207596, by rfl⟩ : syracuseStep 12881029 = 2415193) B2415193
theorem B4951277 : Blo 770335 4951277 := bstep (se 3 (by rfl) ⟨928364, by rfl⟩ : syracuseStep 4951277 = 1856729) B1856729
theorem B5868935 : Blo 770335 5868935 := bstep (se 1 (by rfl) ⟨4401701, by rfl⟩ : syracuseStep 5868935 = 8803403) B8803403
theorem B1740167 : Blo 770335 1740167 := bstep (se 1 (by rfl) ⟨1305125, by rfl⟩ : syracuseStep 1740167 = 2610251) B2610251
theorem B4951505 : Blo 770335 4951505 := bstep (se 2 (by rfl) ⟨1856814, by rfl⟩ : syracuseStep 4951505 = 3713629) B3713629
theorem B1740347 : Blo 770335 1740347 := bstep (se 1 (by rfl) ⟨1305260, by rfl⟩ : syracuseStep 1740347 = 2610521) B2610521
theorem B1740473 : Blo 770335 1740473 := bstep (se 2 (by rfl) ⟨652677, by rfl⟩ : syracuseStep 1740473 = 1305355) B1305355
theorem B2199325 : Blo 770335 2199325 := bstep (se 3 (by rfl) ⟨412373, by rfl⟩ : syracuseStep 2199325 = 824747) B824747
theorem B2199383 : Blo 770335 2199383 := bstep (se 1 (by rfl) ⟨1649537, by rfl⟩ : syracuseStep 2199383 = 3299075) B3299075
theorem B823303 : Blo 770335 823303 := bstep (se 1 (by rfl) ⟨617477, by rfl⟩ : syracuseStep 823303 = 1234955) B1234955
theorem B1740815 : Blo 770335 1740815 := bstep (se 1 (by rfl) ⟨1305611, by rfl⟩ : syracuseStep 1740815 = 2611223) B2611223
theorem B1740833 : Blo 770335 1740833 := bstep (se 2 (by rfl) ⟨652812, by rfl⟩ : syracuseStep 1740833 = 1305625) B1305625
theorem B823483 : Blo 770335 823483 := bstep (se 1 (by rfl) ⟨617612, by rfl⟩ : syracuseStep 823483 = 1235225) B1235225
theorem B4395323 : Blo 770335 4395323 := bstep (se 1 (by rfl) ⟨3296492, by rfl⟩ : syracuseStep 4395323 = 6592985) B6592985
theorem B1675579 : Blo 770335 1675579 := bstep (se 1 (by rfl) ⟨1256684, by rfl⟩ : syracuseStep 1675579 = 2513369) B2513369
theorem B17797441 : Blo 770335 17797441 := bstep (se 2 (by rfl) ⟨6674040, by rfl⟩ : syracuseStep 17797441 = 13348081) B13348081
theorem B1741175 : Blo 770335 1741175 := bstep (se 1 (by rfl) ⟨1305881, by rfl⟩ : syracuseStep 1741175 = 2611763) B2611763
theorem B1741355 : Blo 770335 1741355 := bstep (se 1 (by rfl) ⟨1306016, by rfl⟩ : syracuseStep 1741355 = 2612033) B2612033
theorem B8360819 : Blo 770335 8360819 := bstep (se 1 (by rfl) ⟨6270614, by rfl⟩ : syracuseStep 8360819 = 12541229) B12541229
theorem B1741715 : Blo 770335 1741715 := bstep (se 1 (by rfl) ⟨1306286, by rfl⟩ : syracuseStep 1741715 = 2612573) B2612573
theorem B6263705 : Blo 770335 6263705 := bstep (se 2 (by rfl) ⟨2348889, by rfl⟩ : syracuseStep 6263705 = 4697779) B4697779
theorem B1741769 : Blo 770335 1741769 := bstep (se 2 (by rfl) ⟨653163, by rfl⟩ : syracuseStep 1741769 = 1306327) B1306327
theorem B3904523 : Blo 770335 3904523 := bstep (se 1 (by rfl) ⟨2928392, by rfl⟩ : syracuseStep 3904523 = 5856785) B5856785
theorem B3904685 : Blo 770335 3904685 := bstep (se 3 (by rfl) ⟨732128, by rfl⟩ : syracuseStep 3904685 = 1464257) B1464257
theorem B11113787 : Blo 770335 11113787 := bstep (se 1 (by rfl) ⟨8335340, by rfl⟩ : syracuseStep 11113787 = 16670681) B16670681
theorem B2201033 : Blo 770335 2201033 := bstep (se 2 (by rfl) ⟨825387, by rfl⟩ : syracuseStep 2201033 = 1650775) B1650775
theorem B4396781 : Blo 770335 4396781 := bstep (se 3 (by rfl) ⟨824396, by rfl⟩ : syracuseStep 4396781 = 1648793) B1648793
theorem B3708787 : Blo 770335 3708787 := bstep (se 1 (by rfl) ⟨2781590, by rfl⟩ : syracuseStep 3708787 = 5563181) B5563181
theorem B2201899 : Blo 770335 2201899 := bstep (se 1 (by rfl) ⟨1651424, by rfl⟩ : syracuseStep 2201899 = 3302849) B3302849
theorem B4168145 : Blo 770335 4168145 := bstep (se 2 (by rfl) ⟨1563054, by rfl⟩ : syracuseStep 4168145 = 3126109) B3126109
theorem B2202173 : Blo 770335 2202173 := bstep (se 3 (by rfl) ⟨412907, by rfl⟩ : syracuseStep 2202173 = 825815) B825815
theorem B3906305 : Blo 770335 3906305 := bstep (se 2 (by rfl) ⟨1464864, by rfl⟩ : syracuseStep 3906305 = 2929729) B2929729
theorem B2202515 : Blo 770335 2202515 := bstep (se 1 (by rfl) ⟨1651886, by rfl⟩ : syracuseStep 2202515 = 3303773) B3303773
theorem B6593669 : Blo 770335 6593669 := bstep (se 4 (by rfl) ⟨618156, by rfl⟩ : syracuseStep 6593669 = 1236313) B1236313
theorem B990599 : Blo 770335 990599 := bstep (se 1 (by rfl) ⟨742949, by rfl⟩ : syracuseStep 990599 = 1485899) B1485899
theorem B3907115 : Blo 770335 3907115 := bstep (se 1 (by rfl) ⟨2930336, by rfl⟩ : syracuseStep 3907115 = 5860673) B5860673
theorem B11116439 : Blo 770335 11116439 := bstep (se 1 (by rfl) ⟨8337329, by rfl⟩ : syracuseStep 11116439 = 16674659) B16674659
theorem B8331275 : Blo 770335 8331275 := bstep (se 1 (by rfl) ⟨6248456, by rfl⟩ : syracuseStep 8331275 = 12496913) B12496913
theorem B4956221 : Blo 770335 4956221 := bstep (se 3 (by rfl) ⟨929291, by rfl⟩ : syracuseStep 4956221 = 1858583) B1858583
theorem B1646777 : Blo 770335 1646777 := bstep (se 2 (by rfl) ⟨617541, by rfl⟩ : syracuseStep 1646777 = 1235083) B1235083
theorem B1155515 : Blo 770335 1155515 := bstep (se 1 (by rfl) ⟨866636, by rfl⟩ : syracuseStep 1155515 = 1733273) B1733273
theorem B1155575 : Blo 770335 1155575 := bstep (se 1 (by rfl) ⟨866681, by rfl⟩ : syracuseStep 1155575 = 1733363) B1733363
theorem B1155599 : Blo 770335 1155599 := bstep (se 1 (by rfl) ⟨866699, by rfl⟩ : syracuseStep 1155599 = 1733399) B1733399
theorem B1155641 : Blo 770335 1155641 := bstep (se 2 (by rfl) ⟨433365, by rfl⟩ : syracuseStep 1155641 = 866731) B866731
theorem B2925143 : Blo 770335 2925143 := bstep (se 1 (by rfl) ⟨2193857, by rfl⟩ : syracuseStep 2925143 = 4387715) B4387715
theorem B1155719 : Blo 770335 1155719 := bstep (se 1 (by rfl) ⟨866789, by rfl⟩ : syracuseStep 1155719 = 1733579) B1733579
theorem B1155755 : Blo 770335 1155755 := bstep (se 1 (by rfl) ⟨866816, by rfl⟩ : syracuseStep 1155755 = 1733633) B1733633
theorem B1155785 : Blo 770335 1155785 := bstep (se 2 (by rfl) ⟨433419, by rfl⟩ : syracuseStep 1155785 = 866839) B866839
theorem B1155899 : Blo 770335 1155899 := bstep (se 1 (by rfl) ⟨866924, by rfl⟩ : syracuseStep 1155899 = 1733849) B1733849
theorem B3908411 : Blo 770335 3908411 := bstep (se 1 (by rfl) ⟨2931308, by rfl⟩ : syracuseStep 3908411 = 5862617) B5862617
theorem B1155959 : Blo 770335 1155959 := bstep (se 1 (by rfl) ⟨866969, by rfl⟩ : syracuseStep 1155959 = 1733939) B1733939
theorem B1155983 : Blo 770335 1155983 := bstep (se 1 (by rfl) ⟨866987, by rfl⟩ : syracuseStep 1155983 = 1733975) B1733975
theorem B926635 : Blo 770335 926635 := bstep (se 1 (by rfl) ⟨694976, by rfl⟩ : syracuseStep 926635 = 1389953) B1389953
theorem B1156025 : Blo 770335 1156025 := bstep (se 2 (by rfl) ⟨433509, by rfl⟩ : syracuseStep 1156025 = 867019) B867019
theorem B3908573 : Blo 770335 3908573 := bstep (se 3 (by rfl) ⟨732857, by rfl⟩ : syracuseStep 3908573 = 1465715) B1465715
theorem B1156103 : Blo 770335 1156103 := bstep (se 1 (by rfl) ⟨867077, by rfl⟩ : syracuseStep 1156103 = 1734155) B1734155
theorem B1647631 : Blo 770335 1647631 := bstep (se 1 (by rfl) ⟨1235723, by rfl⟩ : syracuseStep 1647631 = 2471447) B2471447
theorem B1156139 : Blo 770335 1156139 := bstep (se 1 (by rfl) ⟨867104, by rfl⟩ : syracuseStep 1156139 = 1734209) B1734209
theorem B2925629 : Blo 770335 2925629 := bstep (se 3 (by rfl) ⟨548555, by rfl⟩ : syracuseStep 2925629 = 1097111) B1097111
theorem B1156169 : Blo 770335 1156169 := bstep (se 2 (by rfl) ⟨433563, by rfl⟩ : syracuseStep 1156169 = 867127) B867127
theorem B2204759 : Blo 770335 2204759 := bstep (se 1 (by rfl) ⟨1653569, by rfl⟩ : syracuseStep 2204759 = 3307139) B3307139
theorem B1156283 : Blo 770335 1156283 := bstep (se 1 (by rfl) ⟨867212, by rfl⟩ : syracuseStep 1156283 = 1734425) B1734425
theorem B1156343 : Blo 770335 1156343 := bstep (se 1 (by rfl) ⟨867257, by rfl⟩ : syracuseStep 1156343 = 1734515) B1734515
theorem B1156367 : Blo 770335 1156367 := bstep (se 1 (by rfl) ⟨867275, by rfl⟩ : syracuseStep 1156367 = 1734551) B1734551
theorem B3908897 : Blo 770335 3908897 := bstep (se 2 (by rfl) ⟨1465836, by rfl⟩ : syracuseStep 3908897 = 2931673) B2931673
theorem B1156409 : Blo 770335 1156409 := bstep (se 2 (by rfl) ⟨433653, by rfl⟩ : syracuseStep 1156409 = 867307) B867307
theorem B1156487 : Blo 770335 1156487 := bstep (se 1 (by rfl) ⟨867365, by rfl⟩ : syracuseStep 1156487 = 1734731) B1734731
theorem B1156523 : Blo 770335 1156523 := bstep (se 1 (by rfl) ⟨867392, by rfl⟩ : syracuseStep 1156523 = 1734785) B1734785
theorem B1156553 : Blo 770335 1156553 := bstep (se 2 (by rfl) ⟨433707, by rfl⟩ : syracuseStep 1156553 = 867415) B867415
theorem B1156667 : Blo 770335 1156667 := bstep (se 1 (by rfl) ⟨867500, by rfl⟩ : syracuseStep 1156667 = 1735001) B1735001
theorem B1156727 : Blo 770335 1156727 := bstep (se 1 (by rfl) ⟨867545, by rfl⟩ : syracuseStep 1156727 = 1735091) B1735091
theorem B1156751 : Blo 770335 1156751 := bstep (se 1 (by rfl) ⟨867563, by rfl⟩ : syracuseStep 1156751 = 1735127) B1735127
theorem B1156793 : Blo 770335 1156793 := bstep (se 2 (by rfl) ⟨433797, by rfl⟩ : syracuseStep 1156793 = 867595) B867595
theorem B1156871 : Blo 770335 1156871 := bstep (se 1 (by rfl) ⟨867653, by rfl⟩ : syracuseStep 1156871 = 1735307) B1735307
theorem B1156907 : Blo 770335 1156907 := bstep (se 1 (by rfl) ⟨867680, by rfl⟩ : syracuseStep 1156907 = 1735361) B1735361
theorem B1156937 : Blo 770335 1156937 := bstep (se 2 (by rfl) ⟨433851, by rfl⟩ : syracuseStep 1156937 = 867703) B867703
theorem B1157051 : Blo 770335 1157051 := bstep (se 1 (by rfl) ⟨867788, by rfl⟩ : syracuseStep 1157051 = 1735577) B1735577
theorem B1157111 : Blo 770335 1157111 := bstep (se 1 (by rfl) ⟨867833, by rfl⟩ : syracuseStep 1157111 = 1735667) B1735667
theorem B4401155 : Blo 770335 4401155 := bstep (se 1 (by rfl) ⟨3300866, by rfl⟩ : syracuseStep 4401155 = 6601733) B6601733
theorem B1157135 : Blo 770335 1157135 := bstep (se 1 (by rfl) ⟨867851, by rfl⟩ : syracuseStep 1157135 = 1735703) B1735703
theorem B1157177 : Blo 770335 1157177 := bstep (se 2 (by rfl) ⟨433941, by rfl⟩ : syracuseStep 1157177 = 867883) B867883
theorem B1157255 : Blo 770335 1157255 := bstep (se 1 (by rfl) ⟨867941, by rfl⟩ : syracuseStep 1157255 = 1735883) B1735883
theorem B1157291 : Blo 770335 1157291 := bstep (se 1 (by rfl) ⟨867968, by rfl⟩ : syracuseStep 1157291 = 1735937) B1735937
theorem B1157321 : Blo 770335 1157321 := bstep (se 2 (by rfl) ⟨433995, by rfl⟩ : syracuseStep 1157321 = 867991) B867991
theorem B3909869 : Blo 770335 3909869 := bstep (se 3 (by rfl) ⟨733100, by rfl⟩ : syracuseStep 3909869 = 1466201) B1466201
theorem B3123515 : Blo 770335 3123515 := bstep (se 1 (by rfl) ⟨2342636, by rfl⟩ : syracuseStep 3123515 = 4685273) B4685273
theorem B1157435 : Blo 770335 1157435 := bstep (se 1 (by rfl) ⟨868076, by rfl⟩ : syracuseStep 1157435 = 1736153) B1736153
theorem B1157495 : Blo 770335 1157495 := bstep (se 1 (by rfl) ⟨868121, by rfl⟩ : syracuseStep 1157495 = 1736243) B1736243
theorem B1157519 : Blo 770335 1157519 := bstep (se 1 (by rfl) ⟨868139, by rfl⟩ : syracuseStep 1157519 = 1736279) B1736279
theorem B1157561 : Blo 770335 1157561 := bstep (se 2 (by rfl) ⟨434085, by rfl⟩ : syracuseStep 1157561 = 868171) B868171
theorem B4401611 : Blo 770335 4401611 := bstep (se 1 (by rfl) ⟨3301208, by rfl⟩ : syracuseStep 4401611 = 6602417) B6602417
theorem B6597085 : Blo 770335 6597085 := bstep (se 3 (by rfl) ⟨1236953, by rfl⟩ : syracuseStep 6597085 = 2473907) B2473907
theorem B1157639 : Blo 770335 1157639 := bstep (se 1 (by rfl) ⟨868229, by rfl⟩ : syracuseStep 1157639 = 1736459) B1736459
theorem B1157675 : Blo 770335 1157675 := bstep (se 1 (by rfl) ⟨868256, by rfl⟩ : syracuseStep 1157675 = 1736513) B1736513
theorem B1157705 : Blo 770335 1157705 := bstep (se 2 (by rfl) ⟨434139, by rfl⟩ : syracuseStep 1157705 = 868279) B868279
theorem B928427 : Blo 770335 928427 := bstep (se 1 (by rfl) ⟨696320, by rfl⟩ : syracuseStep 928427 = 1392641) B1392641
theorem B1157819 : Blo 770335 1157819 := bstep (se 1 (by rfl) ⟨868364, by rfl⟩ : syracuseStep 1157819 = 1736729) B1736729
theorem B25340633 : Blo 770335 25340633 := bstep (se 2 (by rfl) ⟨9502737, by rfl⟩ : syracuseStep 25340633 = 19005475) B19005475
theorem B4696805 : Blo 770335 4696805 := bstep (se 4 (by rfl) ⟨440325, by rfl⟩ : syracuseStep 4696805 = 880651) B880651
theorem B1157879 : Blo 770335 1157879 := bstep (se 1 (by rfl) ⟨868409, by rfl⟩ : syracuseStep 1157879 = 1736819) B1736819
theorem B1157903 : Blo 770335 1157903 := bstep (se 1 (by rfl) ⟨868427, by rfl⟩ : syracuseStep 1157903 = 1736855) B1736855
theorem B1157945 : Blo 770335 1157945 := bstep (se 2 (by rfl) ⟨434229, by rfl⟩ : syracuseStep 1157945 = 868459) B868459
theorem B1158023 : Blo 770335 1158023 := bstep (se 1 (by rfl) ⟨868517, by rfl⟩ : syracuseStep 1158023 = 1737035) B1737035
theorem B1158059 : Blo 770335 1158059 := bstep (se 1 (by rfl) ⟨868544, by rfl⟩ : syracuseStep 1158059 = 1737089) B1737089
theorem B1158089 : Blo 770335 1158089 := bstep (se 2 (by rfl) ⟨434283, by rfl⟩ : syracuseStep 1158089 = 868567) B868567
theorem B3910679 : Blo 770335 3910679 := bstep (se 1 (by rfl) ⟨2933009, by rfl⟩ : syracuseStep 3910679 = 5866019) B5866019
theorem B1158203 : Blo 770335 1158203 := bstep (se 1 (by rfl) ⟨868652, by rfl⟩ : syracuseStep 1158203 = 1737305) B1737305
theorem B1158263 : Blo 770335 1158263 := bstep (se 1 (by rfl) ⟨868697, by rfl⟩ : syracuseStep 1158263 = 1737395) B1737395
theorem B4402295 : Blo 770335 4402295 := bstep (se 1 (by rfl) ⟨3301721, by rfl⟩ : syracuseStep 4402295 = 6603443) B6603443
theorem B928903 : Blo 770335 928903 := bstep (se 1 (by rfl) ⟨696677, by rfl⟩ : syracuseStep 928903 = 1393355) B1393355
theorem B1158287 : Blo 770335 1158287 := bstep (se 1 (by rfl) ⟨868715, by rfl⟩ : syracuseStep 1158287 = 1737431) B1737431
theorem B1158329 : Blo 770335 1158329 := bstep (se 2 (by rfl) ⟨434373, by rfl⟩ : syracuseStep 1158329 = 868747) B868747
theorem B1158407 : Blo 770335 1158407 := bstep (se 1 (by rfl) ⟨868805, by rfl⟩ : syracuseStep 1158407 = 1737611) B1737611
theorem B2600207 : Blo 770335 2600207 := bstep (se 1 (by rfl) ⟨1950155, by rfl⟩ : syracuseStep 2600207 = 3900311) B3900311
theorem B1158443 : Blo 770335 1158443 := bstep (se 1 (by rfl) ⟨868832, by rfl⟩ : syracuseStep 1158443 = 1737665) B1737665
theorem B1158473 : Blo 770335 1158473 := bstep (se 2 (by rfl) ⟨434427, by rfl⟩ : syracuseStep 1158473 = 868855) B868855
theorem B14069177 : Blo 770335 14069177 := bstep (se 2 (by rfl) ⟨5275941, by rfl⟩ : syracuseStep 14069177 = 10551883) B10551883
theorem B1158587 : Blo 770335 1158587 := bstep (se 1 (by rfl) ⟨868940, by rfl⟩ : syracuseStep 1158587 = 1737881) B1737881
theorem B1158647 : Blo 770335 1158647 := bstep (se 1 (by rfl) ⟨868985, by rfl⟩ : syracuseStep 1158647 = 1737971) B1737971
theorem B1158671 : Blo 770335 1158671 := bstep (se 1 (by rfl) ⟨869003, by rfl⟩ : syracuseStep 1158671 = 1738007) B1738007
theorem B2600477 : Blo 770335 2600477 := bstep (se 3 (by rfl) ⟨487589, by rfl⟩ : syracuseStep 2600477 = 975179) B975179
theorem B1158713 : Blo 770335 1158713 := bstep (se 2 (by rfl) ⟨434517, by rfl⟩ : syracuseStep 1158713 = 869035) B869035
theorem B1158791 : Blo 770335 1158791 := bstep (se 1 (by rfl) ⟨869093, by rfl⟩ : syracuseStep 1158791 = 1738187) B1738187
theorem B1158827 : Blo 770335 1158827 := bstep (se 1 (by rfl) ⟨869120, by rfl⟩ : syracuseStep 1158827 = 1738241) B1738241
theorem B1158857 : Blo 770335 1158857 := bstep (se 2 (by rfl) ⟨434571, by rfl⟩ : syracuseStep 1158857 = 869143) B869143
theorem B7745329 : Blo 770335 7745329 := bstep (se 2 (by rfl) ⟨2904498, by rfl⟩ : syracuseStep 7745329 = 5808997) B5808997
theorem B1158971 : Blo 770335 1158971 := bstep (se 1 (by rfl) ⟨869228, by rfl⟩ : syracuseStep 1158971 = 1738457) B1738457
theorem B1159031 : Blo 770335 1159031 := bstep (se 1 (by rfl) ⟨869273, by rfl⟩ : syracuseStep 1159031 = 1738547) B1738547
theorem B1159055 : Blo 770335 1159055 := bstep (se 1 (by rfl) ⟨869291, by rfl⟩ : syracuseStep 1159055 = 1738583) B1738583
theorem B1159097 : Blo 770335 1159097 := bstep (se 2 (by rfl) ⟨434661, by rfl⟩ : syracuseStep 1159097 = 869323) B869323
theorem B1159175 : Blo 770335 1159175 := bstep (se 1 (by rfl) ⟨869381, by rfl⟩ : syracuseStep 1159175 = 1738763) B1738763
theorem B1159211 : Blo 770335 1159211 := bstep (se 1 (by rfl) ⟨869408, by rfl⟩ : syracuseStep 1159211 = 1738817) B1738817
theorem B1159241 : Blo 770335 1159241 := bstep (se 2 (by rfl) ⟨434715, by rfl⟩ : syracuseStep 1159241 = 869431) B869431
theorem B1159355 : Blo 770335 1159355 := bstep (se 1 (by rfl) ⟨869516, by rfl⟩ : syracuseStep 1159355 = 1739033) B1739033
theorem B1159415 : Blo 770335 1159415 := bstep (se 1 (by rfl) ⟨869561, by rfl⟩ : syracuseStep 1159415 = 1739123) B1739123
theorem B1159439 : Blo 770335 1159439 := bstep (se 1 (by rfl) ⟨869579, by rfl⟩ : syracuseStep 1159439 = 1739159) B1739159
theorem B1159481 : Blo 770335 1159481 := bstep (se 2 (by rfl) ⟨434805, by rfl⟩ : syracuseStep 1159481 = 869611) B869611
theorem B6271291 : Blo 770335 6271291 := bstep (se 1 (by rfl) ⟨4703468, by rfl⟩ : syracuseStep 6271291 = 9406937) B9406937
theorem B2929031 : Blo 770335 2929031 := bstep (se 1 (by rfl) ⟨2196773, by rfl⟩ : syracuseStep 2929031 = 4393547) B4393547
theorem B1159559 : Blo 770335 1159559 := bstep (se 1 (by rfl) ⟨869669, by rfl⟩ : syracuseStep 1159559 = 1739339) B1739339
theorem B1159595 : Blo 770335 1159595 := bstep (se 1 (by rfl) ⟨869696, by rfl⟩ : syracuseStep 1159595 = 1739393) B1739393
theorem B1159625 : Blo 770335 1159625 := bstep (se 2 (by rfl) ⟨434859, by rfl⟩ : syracuseStep 1159625 = 869719) B869719
theorem B1323535 : Blo 770335 1323535 := bstep (se 1 (by rfl) ⟨992651, by rfl⟩ : syracuseStep 1323535 = 1985303) B1985303
theorem B1159739 : Blo 770335 1159739 := bstep (se 1 (by rfl) ⟨869804, by rfl⟩ : syracuseStep 1159739 = 1739609) B1739609
theorem B4960835 : Blo 770335 4960835 := bstep (se 1 (by rfl) ⟨3720626, by rfl⟩ : syracuseStep 4960835 = 7441253) B7441253
theorem B1159799 : Blo 770335 1159799 := bstep (se 1 (by rfl) ⟨869849, by rfl⟩ : syracuseStep 1159799 = 1739699) B1739699
theorem B1159823 : Blo 770335 1159823 := bstep (se 1 (by rfl) ⟨869867, by rfl⟩ : syracuseStep 1159823 = 1739735) B1739735
theorem B1159865 : Blo 770335 1159865 := bstep (se 2 (by rfl) ⟨434949, by rfl⟩ : syracuseStep 1159865 = 869899) B869899
theorem B1159943 : Blo 770335 1159943 := bstep (se 1 (by rfl) ⟨869957, by rfl⟩ : syracuseStep 1159943 = 1739915) B1739915
theorem B1159979 : Blo 770335 1159979 := bstep (se 1 (by rfl) ⟨869984, by rfl⟩ : syracuseStep 1159979 = 1739969) B1739969
theorem B1160009 : Blo 770335 1160009 := bstep (se 2 (by rfl) ⟨435003, by rfl⟩ : syracuseStep 1160009 = 870007) B870007
theorem B2601881 : Blo 770335 2601881 := bstep (se 2 (by rfl) ⟨975705, by rfl⟩ : syracuseStep 2601881 = 1951411) B1951411
theorem B1160123 : Blo 770335 1160123 := bstep (se 1 (by rfl) ⟨870092, by rfl⟩ : syracuseStep 1160123 = 1740185) B1740185
theorem B1160183 : Blo 770335 1160183 := bstep (se 1 (by rfl) ⟨870137, by rfl⟩ : syracuseStep 1160183 = 1740275) B1740275
theorem B1160207 : Blo 770335 1160207 := bstep (se 1 (by rfl) ⟨870155, by rfl⟩ : syracuseStep 1160207 = 1740311) B1740311
theorem B4404253 : Blo 770335 4404253 := bstep (se 3 (by rfl) ⟨825797, by rfl⟩ : syracuseStep 4404253 = 1651595) B1651595
theorem B1160249 : Blo 770335 1160249 := bstep (se 2 (by rfl) ⟨435093, by rfl⟩ : syracuseStep 1160249 = 870187) B870187
theorem B1160327 : Blo 770335 1160327 := bstep (se 1 (by rfl) ⟨870245, by rfl⟩ : syracuseStep 1160327 = 1740491) B1740491
theorem B1160363 : Blo 770335 1160363 := bstep (se 1 (by rfl) ⟨870272, by rfl⟩ : syracuseStep 1160363 = 1740545) B1740545
theorem B1160393 : Blo 770335 1160393 := bstep (se 2 (by rfl) ⟨435147, by rfl⟩ : syracuseStep 1160393 = 870295) B870295
theorem B1160507 : Blo 770335 1160507 := bstep (se 1 (by rfl) ⟨870380, by rfl⟩ : syracuseStep 1160507 = 1740761) B1740761
theorem B1160567 : Blo 770335 1160567 := bstep (se 1 (by rfl) ⟨870425, by rfl⟩ : syracuseStep 1160567 = 1740851) B1740851
theorem B1160591 : Blo 770335 1160591 := bstep (se 1 (by rfl) ⟨870443, by rfl⟩ : syracuseStep 1160591 = 1740887) B1740887
theorem B1160633 : Blo 770335 1160633 := bstep (se 2 (by rfl) ⟨435237, by rfl⟩ : syracuseStep 1160633 = 870475) B870475
theorem B1160711 : Blo 770335 1160711 := bstep (se 1 (by rfl) ⟨870533, by rfl⟩ : syracuseStep 1160711 = 1741067) B1741067
theorem B4404779 : Blo 770335 4404779 := bstep (se 1 (by rfl) ⟨3303584, by rfl⟩ : syracuseStep 4404779 = 6607169) B6607169
theorem B1160747 : Blo 770335 1160747 := bstep (se 1 (by rfl) ⟨870560, by rfl⟩ : syracuseStep 1160747 = 1741121) B1741121
theorem B1160777 : Blo 770335 1160777 := bstep (se 2 (by rfl) ⟨435291, by rfl⟩ : syracuseStep 1160777 = 870583) B870583
theorem B2602583 : Blo 770335 2602583 := bstep (se 1 (by rfl) ⟨1951937, by rfl⟩ : syracuseStep 2602583 = 3903875) B3903875
theorem B1160891 : Blo 770335 1160891 := bstep (se 1 (by rfl) ⟨870668, by rfl⟩ : syracuseStep 1160891 = 1741337) B1741337
theorem B1160951 : Blo 770335 1160951 := bstep (se 1 (by rfl) ⟨870713, by rfl⟩ : syracuseStep 1160951 = 1741427) B1741427
theorem B1160975 : Blo 770335 1160975 := bstep (se 1 (by rfl) ⟨870731, by rfl⟩ : syracuseStep 1160975 = 1741463) B1741463
theorem B1161017 : Blo 770335 1161017 := bstep (se 2 (by rfl) ⟨435381, by rfl⟩ : syracuseStep 1161017 = 870763) B870763
theorem B1161095 : Blo 770335 1161095 := bstep (se 1 (by rfl) ⟨870821, by rfl⟩ : syracuseStep 1161095 = 1741643) B1741643
theorem B1161131 : Blo 770335 1161131 := bstep (se 1 (by rfl) ⟨870848, by rfl⟩ : syracuseStep 1161131 = 1741697) B1741697
theorem B1161161 : Blo 770335 1161161 := bstep (se 2 (by rfl) ⟨435435, by rfl⟩ : syracuseStep 1161161 = 870871) B870871
theorem B3913757 : Blo 770335 3913757 := bstep (se 3 (by rfl) ⟨733829, by rfl⟩ : syracuseStep 3913757 = 1467659) B1467659
theorem B1161275 : Blo 770335 1161275 := bstep (se 1 (by rfl) ⟨870956, by rfl⟩ : syracuseStep 1161275 = 1741913) B1741913
theorem B2603069 : Blo 770335 2603069 := bstep (se 3 (by rfl) ⟨488075, by rfl⟩ : syracuseStep 2603069 = 976151) B976151
theorem B1161335 : Blo 770335 1161335 := bstep (se 1 (by rfl) ⟨871001, by rfl⟩ : syracuseStep 1161335 = 1742003) B1742003
theorem B1161359 : Blo 770335 1161359 := bstep (se 1 (by rfl) ⟨871019, by rfl⟩ : syracuseStep 1161359 = 1742039) B1742039
theorem B1161401 : Blo 770335 1161401 := bstep (se 2 (by rfl) ⟨435525, by rfl⟩ : syracuseStep 1161401 = 871051) B871051
theorem B1161479 : Blo 770335 1161479 := bstep (se 1 (by rfl) ⟨871109, by rfl⟩ : syracuseStep 1161479 = 1742219) B1742219
theorem B866695 : Blo 770335 866695 := bstep (se 1 (by rfl) ⟨650021, by rfl⟩ : syracuseStep 866695 = 1300043) B1300043
theorem B3914243 : Blo 770335 3914243 := bstep (se 1 (by rfl) ⟨2935682, by rfl⟩ : syracuseStep 3914243 = 5871365) B5871365
theorem B866875 : Blo 770335 866875 := bstep (se 1 (by rfl) ⟨650156, by rfl⟩ : syracuseStep 866875 = 1300313) B1300313
theorem B4406237 : Blo 770335 4406237 := bstep (se 3 (by rfl) ⟨826169, by rfl⟩ : syracuseStep 4406237 = 1652339) B1652339
theorem B867343 : Blo 770335 867343 := bstep (se 1 (by rfl) ⟨650507, by rfl⟩ : syracuseStep 867343 = 1301015) B1301015
theorem B8928317 : Blo 770335 8928317 := bstep (se 3 (by rfl) ⟨1674059, by rfl⟩ : syracuseStep 8928317 = 3348119) B3348119
theorem B2473217 : Blo 770335 2473217 := bstep (se 2 (by rfl) ⟨927456, by rfl⟩ : syracuseStep 2473217 = 1854913) B1854913
theorem B1097003 : Blo 770335 1097003 := bstep (se 1 (by rfl) ⟨822752, by rfl⟩ : syracuseStep 1097003 = 1645505) B1645505
theorem B8797571 : Blo 770335 8797571 := bstep (se 1 (by rfl) ⟨6598178, by rfl⟩ : syracuseStep 8797571 = 13196357) B13196357
theorem B2604473 : Blo 770335 2604473 := bstep (se 2 (by rfl) ⟨976677, by rfl⟩ : syracuseStep 2604473 = 1953355) B1953355
theorem B867847 : Blo 770335 867847 := bstep (se 1 (by rfl) ⟨650885, by rfl⟩ : syracuseStep 867847 = 1301771) B1301771
theorem B868027 : Blo 770335 868027 := bstep (se 1 (by rfl) ⟨651020, by rfl⟩ : syracuseStep 868027 = 1302041) B1302041
theorem B3293075 : Blo 770335 3293075 := bstep (se 1 (by rfl) ⟨2469806, by rfl⟩ : syracuseStep 3293075 = 4939613) B4939613
theorem B1392569 : Blo 770335 1392569 := bstep (se 2 (by rfl) ⟨522213, by rfl⟩ : syracuseStep 1392569 = 1044427) B1044427
theorem B2605067 : Blo 770335 2605067 := bstep (se 1 (by rfl) ⟨1953800, by rfl⟩ : syracuseStep 2605067 = 3907601) B3907601
theorem B3915863 : Blo 770335 3915863 := bstep (se 1 (by rfl) ⟨2936897, by rfl⟩ : syracuseStep 3915863 = 5873795) B5873795
theorem B2605175 : Blo 770335 2605175 := bstep (se 1 (by rfl) ⟨1953881, by rfl⟩ : syracuseStep 2605175 = 3907763) B3907763
theorem B868495 : Blo 770335 868495 := bstep (se 1 (by rfl) ⟨651371, by rfl⟩ : syracuseStep 868495 = 1302743) B1302743
theorem B1949953 : Blo 770335 1949953 := bstep (se 2 (by rfl) ⟨731232, by rfl⟩ : syracuseStep 1949953 = 1462465) B1462465
theorem B770363 : Blo 770335 770363 := bstep (se 1 (by rfl) ⟨577772, by rfl⟩ : syracuseStep 770363 = 1155545) B1155545
theorem B770439 : Blo 770335 770439 := bstep (se 1 (by rfl) ⟨577829, by rfl⟩ : syracuseStep 770439 = 1155659) B1155659
theorem B1393031 : Blo 770335 1393031 := bstep (se 1 (by rfl) ⟨1044773, by rfl⟩ : syracuseStep 1393031 = 2089547) B2089547
theorem B770447 : Blo 770335 770447 := bstep (se 1 (by rfl) ⟨577835, by rfl⟩ : syracuseStep 770447 = 1155671) B1155671
theorem B770491 : Blo 770335 770491 := bstep (se 1 (by rfl) ⟨577868, by rfl⟩ : syracuseStep 770491 = 1155737) B1155737
theorem B3719627 : Blo 770335 3719627 := bstep (se 1 (by rfl) ⟨2789720, by rfl⟩ : syracuseStep 3719627 = 5579441) B5579441
theorem B770567 : Blo 770335 770567 := bstep (se 1 (by rfl) ⟨577925, by rfl⟩ : syracuseStep 770567 = 1155851) B1155851
theorem B770575 : Blo 770335 770575 := bstep (se 1 (by rfl) ⟨577931, by rfl⟩ : syracuseStep 770575 = 1155863) B1155863
theorem B770619 : Blo 770335 770619 := bstep (se 1 (by rfl) ⟨577964, by rfl⟩ : syracuseStep 770619 = 1155929) B1155929
theorem B3916349 : Blo 770335 3916349 := bstep (se 3 (by rfl) ⟨734315, by rfl⟩ : syracuseStep 3916349 = 1468631) B1468631
theorem B4702787 : Blo 770335 4702787 := bstep (se 1 (by rfl) ⟨3527090, by rfl⟩ : syracuseStep 4702787 = 7054181) B7054181
theorem B770695 : Blo 770335 770695 := bstep (se 1 (by rfl) ⟨578021, by rfl⟩ : syracuseStep 770695 = 1156043) B1156043
theorem B868999 : Blo 770335 868999 := bstep (se 1 (by rfl) ⟨651749, by rfl⟩ : syracuseStep 868999 = 1303499) B1303499
theorem B770703 : Blo 770335 770703 := bstep (se 1 (by rfl) ⟨578027, by rfl⟩ : syracuseStep 770703 = 1156055) B1156055
theorem B770747 : Blo 770335 770747 := bstep (se 1 (by rfl) ⟨578060, by rfl⟩ : syracuseStep 770747 = 1156121) B1156121
theorem B2605769 : Blo 770335 2605769 := bstep (se 2 (by rfl) ⟨977163, by rfl⟩ : syracuseStep 2605769 = 1954327) B1954327
theorem B770823 : Blo 770335 770823 := bstep (se 1 (by rfl) ⟨578117, by rfl⟩ : syracuseStep 770823 = 1156235) B1156235
theorem B770831 : Blo 770335 770831 := bstep (se 1 (by rfl) ⟨578123, by rfl⟩ : syracuseStep 770831 = 1156247) B1156247
theorem B770875 : Blo 770335 770875 := bstep (se 1 (by rfl) ⟨578156, by rfl⟩ : syracuseStep 770875 = 1156313) B1156313
theorem B869179 : Blo 770335 869179 := bstep (se 1 (by rfl) ⟨651884, by rfl⟩ : syracuseStep 869179 = 1303769) B1303769
theorem B1098569 : Blo 770335 1098569 := bstep (se 2 (by rfl) ⟨411963, by rfl⟩ : syracuseStep 1098569 = 823927) B823927
theorem B1950551 : Blo 770335 1950551 := bstep (se 1 (by rfl) ⟨1462913, by rfl⟩ : syracuseStep 1950551 = 2925827) B2925827
theorem B3294067 : Blo 770335 3294067 := bstep (se 1 (by rfl) ⟨2470550, by rfl⟩ : syracuseStep 3294067 = 4941101) B4941101
theorem B770951 : Blo 770335 770951 := bstep (se 1 (by rfl) ⟨578213, by rfl⟩ : syracuseStep 770951 = 1156427) B1156427
theorem B770959 : Blo 770335 770959 := bstep (se 1 (by rfl) ⟨578219, by rfl⟩ : syracuseStep 770959 = 1156439) B1156439
theorem B771003 : Blo 770335 771003 := bstep (se 1 (by rfl) ⟨578252, by rfl⟩ : syracuseStep 771003 = 1156505) B1156505
theorem B771079 : Blo 770335 771079 := bstep (se 1 (by rfl) ⟨578309, by rfl⟩ : syracuseStep 771079 = 1156619) B1156619
theorem B771087 : Blo 770335 771087 := bstep (se 1 (by rfl) ⟨578315, by rfl⟩ : syracuseStep 771087 = 1156631) B1156631
theorem B1950763 : Blo 770335 1950763 := bstep (se 1 (by rfl) ⟨1463072, by rfl⟩ : syracuseStep 1950763 = 2926145) B2926145
theorem B771131 : Blo 770335 771131 := bstep (se 1 (by rfl) ⟨578348, by rfl⟩ : syracuseStep 771131 = 1156697) B1156697
theorem B771207 : Blo 770335 771207 := bstep (se 1 (by rfl) ⟨578405, by rfl⟩ : syracuseStep 771207 = 1156811) B1156811
theorem B771215 : Blo 770335 771215 := bstep (se 1 (by rfl) ⟨578411, by rfl⟩ : syracuseStep 771215 = 1156823) B1156823
theorem B1950905 : Blo 770335 1950905 := bstep (se 2 (by rfl) ⟨731589, by rfl⟩ : syracuseStep 1950905 = 1463179) B1463179
theorem B771259 : Blo 770335 771259 := bstep (se 1 (by rfl) ⟨578444, by rfl⟩ : syracuseStep 771259 = 1156889) B1156889
theorem B771335 : Blo 770335 771335 := bstep (se 1 (by rfl) ⟨578501, by rfl⟩ : syracuseStep 771335 = 1157003) B1157003
theorem B771343 : Blo 770335 771343 := bstep (se 1 (by rfl) ⟨578507, by rfl⟩ : syracuseStep 771343 = 1157015) B1157015
theorem B869647 : Blo 770335 869647 := bstep (se 1 (by rfl) ⟨652235, by rfl⟩ : syracuseStep 869647 = 1304471) B1304471
theorem B4408627 : Blo 770335 4408627 := bstep (se 1 (by rfl) ⟨3306470, by rfl⟩ : syracuseStep 4408627 = 6612941) B6612941
theorem B771387 : Blo 770335 771387 := bstep (se 1 (by rfl) ⟨578540, by rfl⟩ : syracuseStep 771387 = 1157081) B1157081
theorem B1099127 : Blo 770335 1099127 := bstep (se 1 (by rfl) ⟨824345, by rfl⟩ : syracuseStep 1099127 = 1648691) B1648691
theorem B771463 : Blo 770335 771463 := bstep (se 1 (by rfl) ⟨578597, by rfl⟩ : syracuseStep 771463 = 1157195) B1157195
theorem B2606471 : Blo 770335 2606471 := bstep (se 1 (by rfl) ⟨1954853, by rfl⟩ : syracuseStep 2606471 = 3909707) B3909707
theorem B771471 : Blo 770335 771471 := bstep (se 1 (by rfl) ⟨578603, by rfl⟩ : syracuseStep 771471 = 1157207) B1157207
theorem B771515 : Blo 770335 771515 := bstep (se 1 (by rfl) ⟨578636, by rfl⟩ : syracuseStep 771515 = 1157273) B1157273
theorem B15058385 : Blo 770335 15058385 := bstep (se 2 (by rfl) ⟨5646894, by rfl⟩ : syracuseStep 15058385 = 11293789) B11293789
theorem B771591 : Blo 770335 771591 := bstep (se 1 (by rfl) ⟨578693, by rfl⟩ : syracuseStep 771591 = 1157387) B1157387
theorem B771599 : Blo 770335 771599 := bstep (se 1 (by rfl) ⟨578699, by rfl⟩ : syracuseStep 771599 = 1157399) B1157399
theorem B771643 : Blo 770335 771643 := bstep (se 1 (by rfl) ⟨578732, by rfl⟩ : syracuseStep 771643 = 1157465) B1157465
theorem B1853047 : Blo 770335 1853047 := bstep (se 1 (by rfl) ⟨1389785, by rfl⟩ : syracuseStep 1853047 = 2779571) B2779571
theorem B771719 : Blo 770335 771719 := bstep (se 1 (by rfl) ⟨578789, by rfl⟩ : syracuseStep 771719 = 1157579) B1157579
theorem B771727 : Blo 770335 771727 := bstep (se 1 (by rfl) ⟨578795, by rfl⟩ : syracuseStep 771727 = 1157591) B1157591
theorem B1099435 : Blo 770335 1099435 := bstep (se 1 (by rfl) ⟨824576, by rfl⟩ : syracuseStep 1099435 = 1649153) B1649153
theorem B771771 : Blo 770335 771771 := bstep (se 1 (by rfl) ⟨578828, by rfl⟩ : syracuseStep 771771 = 1157657) B1157657
theorem B2606849 : Blo 770335 2606849 := bstep (se 2 (by rfl) ⟨977568, by rfl⟩ : syracuseStep 2606849 = 1955137) B1955137
theorem B771847 : Blo 770335 771847 := bstep (se 1 (by rfl) ⟨578885, by rfl⟩ : syracuseStep 771847 = 1157771) B1157771
theorem B870151 : Blo 770335 870151 := bstep (se 1 (by rfl) ⟨652613, by rfl⟩ : syracuseStep 870151 = 1305227) B1305227
theorem B771855 : Blo 770335 771855 := bstep (se 1 (by rfl) ⟨578891, by rfl⟩ : syracuseStep 771855 = 1157783) B1157783
theorem B5949233 : Blo 770335 5949233 := bstep (se 2 (by rfl) ⟨2230962, by rfl⟩ : syracuseStep 5949233 = 4461925) B4461925
theorem B771899 : Blo 770335 771899 := bstep (se 1 (by rfl) ⟨578924, by rfl⟩ : syracuseStep 771899 = 1157849) B1157849
theorem B771975 : Blo 770335 771975 := bstep (se 1 (by rfl) ⟨578981, by rfl⟩ : syracuseStep 771975 = 1157963) B1157963
theorem B771983 : Blo 770335 771983 := bstep (se 1 (by rfl) ⟨578987, by rfl⟩ : syracuseStep 771983 = 1157975) B1157975
theorem B772027 : Blo 770335 772027 := bstep (se 1 (by rfl) ⟨579020, by rfl⟩ : syracuseStep 772027 = 1158041) B1158041
theorem B870331 : Blo 770335 870331 := bstep (se 1 (by rfl) ⟨652748, by rfl⟩ : syracuseStep 870331 = 1305497) B1305497
theorem B772103 : Blo 770335 772103 := bstep (se 1 (by rfl) ⟨579077, by rfl⟩ : syracuseStep 772103 = 1158155) B1158155
theorem B772111 : Blo 770335 772111 := bstep (se 1 (by rfl) ⟨579083, by rfl⟩ : syracuseStep 772111 = 1158167) B1158167
theorem B2476061 : Blo 770335 2476061 := bstep (se 3 (by rfl) ⟨464261, by rfl⟩ : syracuseStep 2476061 = 928523) B928523
theorem B772155 : Blo 770335 772155 := bstep (se 1 (by rfl) ⟨579116, by rfl⟩ : syracuseStep 772155 = 1158233) B1158233
theorem B772231 : Blo 770335 772231 := bstep (se 1 (by rfl) ⟨579173, by rfl⟩ : syracuseStep 772231 = 1158347) B1158347
theorem B772239 : Blo 770335 772239 := bstep (se 1 (by rfl) ⟨579179, by rfl⟩ : syracuseStep 772239 = 1158359) B1158359
theorem B1099919 : Blo 770335 1099919 := bstep (se 1 (by rfl) ⟨824939, by rfl⟩ : syracuseStep 1099919 = 1649879) B1649879
theorem B1951897 : Blo 770335 1951897 := bstep (se 2 (by rfl) ⟨731961, by rfl⟩ : syracuseStep 1951897 = 1463923) B1463923
theorem B772283 : Blo 770335 772283 := bstep (se 1 (by rfl) ⟨579212, by rfl⟩ : syracuseStep 772283 = 1158425) B1158425
theorem B772359 : Blo 770335 772359 := bstep (se 1 (by rfl) ⟨579269, by rfl⟩ : syracuseStep 772359 = 1158539) B1158539
theorem B772367 : Blo 770335 772367 := bstep (se 1 (by rfl) ⟨579275, by rfl⟩ : syracuseStep 772367 = 1158551) B1158551
theorem B3918131 : Blo 770335 3918131 := bstep (se 1 (by rfl) ⟨2938598, by rfl⟩ : syracuseStep 3918131 = 5877197) B5877197
theorem B1952059 : Blo 770335 1952059 := bstep (se 1 (by rfl) ⟨1464044, by rfl⟩ : syracuseStep 1952059 = 2928089) B2928089
theorem B772411 : Blo 770335 772411 := bstep (se 1 (by rfl) ⟨579308, by rfl⟩ : syracuseStep 772411 = 1158617) B1158617
theorem B772487 : Blo 770335 772487 := bstep (se 1 (by rfl) ⟨579365, by rfl⟩ : syracuseStep 772487 = 1158731) B1158731
theorem B772495 : Blo 770335 772495 := bstep (se 1 (by rfl) ⟨579371, by rfl⟩ : syracuseStep 772495 = 1158743) B1158743
theorem B870799 : Blo 770335 870799 := bstep (se 1 (by rfl) ⟨653099, by rfl⟩ : syracuseStep 870799 = 1306199) B1306199
theorem B1395091 : Blo 770335 1395091 := bstep (se 1 (by rfl) ⟨1046318, by rfl⟩ : syracuseStep 1395091 = 2092637) B2092637
theorem B3295673 : Blo 770335 3295673 := bstep (se 2 (by rfl) ⟨1235877, by rfl⟩ : syracuseStep 3295673 = 2471755) B2471755
theorem B772539 : Blo 770335 772539 := bstep (se 1 (by rfl) ⟨579404, by rfl⟩ : syracuseStep 772539 = 1158809) B1158809
theorem B1952201 : Blo 770335 1952201 := bstep (se 2 (by rfl) ⟨732075, by rfl⟩ : syracuseStep 1952201 = 1464151) B1464151
theorem B4704733 : Blo 770335 4704733 := bstep (se 3 (by rfl) ⟨882137, by rfl⟩ : syracuseStep 4704733 = 1764275) B1764275
theorem B772615 : Blo 770335 772615 := bstep (se 1 (by rfl) ⟨579461, by rfl⟩ : syracuseStep 772615 = 1158923) B1158923
theorem B772623 : Blo 770335 772623 := bstep (se 1 (by rfl) ⟨579467, by rfl⟩ : syracuseStep 772623 = 1158935) B1158935
theorem B2607659 : Blo 770335 2607659 := bstep (se 1 (by rfl) ⟨1955744, by rfl⟩ : syracuseStep 2607659 = 3911489) B3911489
theorem B772667 : Blo 770335 772667 := bstep (se 1 (by rfl) ⟨579500, by rfl⟩ : syracuseStep 772667 = 1159001) B1159001
theorem B3918455 : Blo 770335 3918455 := bstep (se 1 (by rfl) ⟨2938841, by rfl⟩ : syracuseStep 3918455 = 5877683) B5877683
theorem B772743 : Blo 770335 772743 := bstep (se 1 (by rfl) ⟨579557, by rfl⟩ : syracuseStep 772743 = 1159115) B1159115
theorem B772751 : Blo 770335 772751 := bstep (se 1 (by rfl) ⟨579563, by rfl⟩ : syracuseStep 772751 = 1159127) B1159127
theorem B772795 : Blo 770335 772795 := bstep (se 1 (by rfl) ⟨579596, by rfl⟩ : syracuseStep 772795 = 1159193) B1159193
theorem B4410085 : Blo 770335 4410085 := bstep (se 4 (by rfl) ⟨413445, by rfl⟩ : syracuseStep 4410085 = 826891) B826891
theorem B772871 : Blo 770335 772871 := bstep (se 1 (by rfl) ⟨579653, by rfl⟩ : syracuseStep 772871 = 1159307) B1159307
theorem B3296015 : Blo 770335 3296015 := bstep (se 1 (by rfl) ⟨2472011, by rfl⟩ : syracuseStep 3296015 = 4944023) B4944023
theorem B772879 : Blo 770335 772879 := bstep (se 1 (by rfl) ⟨579659, by rfl⟩ : syracuseStep 772879 = 1159319) B1159319
theorem B1952545 : Blo 770335 1952545 := bstep (se 2 (by rfl) ⟨732204, by rfl⟩ : syracuseStep 1952545 = 1464409) B1464409
theorem B772923 : Blo 770335 772923 := bstep (se 1 (by rfl) ⟨579692, by rfl⟩ : syracuseStep 772923 = 1159385) B1159385
theorem B772999 : Blo 770335 772999 := bstep (se 1 (by rfl) ⟨579749, by rfl⟩ : syracuseStep 772999 = 1159499) B1159499
theorem B773007 : Blo 770335 773007 := bstep (se 1 (by rfl) ⟨579755, by rfl⟩ : syracuseStep 773007 = 1159511) B1159511
theorem B773051 : Blo 770335 773051 := bstep (se 1 (by rfl) ⟨579788, by rfl⟩ : syracuseStep 773051 = 1159577) B1159577
theorem B773127 : Blo 770335 773127 := bstep (se 1 (by rfl) ⟨579845, by rfl⟩ : syracuseStep 773127 = 1159691) B1159691
theorem B773135 : Blo 770335 773135 := bstep (se 1 (by rfl) ⟨579851, by rfl⟩ : syracuseStep 773135 = 1159703) B1159703
theorem B773179 : Blo 770335 773179 := bstep (se 1 (by rfl) ⟨579884, by rfl⟩ : syracuseStep 773179 = 1159769) B1159769
theorem B3132503 : Blo 770335 3132503 := bstep (se 1 (by rfl) ⟨2349377, by rfl⟩ : syracuseStep 3132503 = 4698755) B4698755
theorem B773255 : Blo 770335 773255 := bstep (se 1 (by rfl) ⟨579941, by rfl⟩ : syracuseStep 773255 = 1159883) B1159883
theorem B773263 : Blo 770335 773263 := bstep (se 1 (by rfl) ⟨579947, by rfl⟩ : syracuseStep 773263 = 1159895) B1159895
theorem B773307 : Blo 770335 773307 := bstep (se 1 (by rfl) ⟨579980, by rfl⟩ : syracuseStep 773307 = 1159961) B1159961
theorem B773383 : Blo 770335 773383 := bstep (se 1 (by rfl) ⟨580037, by rfl⟩ : syracuseStep 773383 = 1160075) B1160075
theorem B1854731 : Blo 770335 1854731 := bstep (se 1 (by rfl) ⟨1391048, by rfl⟩ : syracuseStep 1854731 = 2782097) B2782097
theorem B773391 : Blo 770335 773391 := bstep (se 1 (by rfl) ⟨580043, by rfl⟩ : syracuseStep 773391 = 1160087) B1160087
theorem B773435 : Blo 770335 773435 := bstep (se 1 (by rfl) ⟨580076, by rfl⟩ : syracuseStep 773435 = 1160153) B1160153
theorem B1953143 : Blo 770335 1953143 := bstep (se 1 (by rfl) ⟨1464857, by rfl⟩ : syracuseStep 1953143 = 2929715) B2929715
theorem B773511 : Blo 770335 773511 := bstep (se 1 (by rfl) ⟨580133, by rfl⟩ : syracuseStep 773511 = 1160267) B1160267
theorem B773519 : Blo 770335 773519 := bstep (se 1 (by rfl) ⟨580139, by rfl⟩ : syracuseStep 773519 = 1160279) B1160279
theorem B773563 : Blo 770335 773563 := bstep (se 1 (by rfl) ⟨580172, by rfl⟩ : syracuseStep 773563 = 1160345) B1160345
theorem B773639 : Blo 770335 773639 := bstep (se 1 (by rfl) ⟨580229, by rfl⟩ : syracuseStep 773639 = 1160459) B1160459
theorem B773647 : Blo 770335 773647 := bstep (se 1 (by rfl) ⟨580235, by rfl⟩ : syracuseStep 773647 = 1160471) B1160471
theorem B773691 : Blo 770335 773691 := bstep (se 1 (by rfl) ⟨580268, by rfl⟩ : syracuseStep 773691 = 1160537) B1160537
theorem B6868547 : Blo 770335 6868547 := bstep (se 1 (by rfl) ⟨5151410, by rfl⟩ : syracuseStep 6868547 = 10302821) B10302821
theorem B3919427 : Blo 770335 3919427 := bstep (se 1 (by rfl) ⟨2939570, by rfl⟩ : syracuseStep 3919427 = 5879141) B5879141
theorem B773767 : Blo 770335 773767 := bstep (se 1 (by rfl) ⟨580325, by rfl⟩ : syracuseStep 773767 = 1160651) B1160651
theorem B773775 : Blo 770335 773775 := bstep (se 1 (by rfl) ⟨580331, by rfl⟩ : syracuseStep 773775 = 1160663) B1160663
theorem B773819 : Blo 770335 773819 := bstep (se 1 (by rfl) ⟨580364, by rfl⟩ : syracuseStep 773819 = 1160729) B1160729
theorem B11128549 : Blo 770335 11128549 := bstep (se 4 (by rfl) ⟨1043301, by rfl⟩ : syracuseStep 11128549 = 2086603) B2086603
theorem B773895 : Blo 770335 773895 := bstep (se 1 (by rfl) ⟨580421, by rfl⟩ : syracuseStep 773895 = 1160843) B1160843
theorem B773903 : Blo 770335 773903 := bstep (se 1 (by rfl) ⟨580427, by rfl⟩ : syracuseStep 773903 = 1160855) B1160855
theorem B4706099 : Blo 770335 4706099 := bstep (se 1 (by rfl) ⟨3529574, by rfl⟩ : syracuseStep 4706099 = 7059149) B7059149
theorem B2608955 : Blo 770335 2608955 := bstep (se 1 (by rfl) ⟨1956716, by rfl⟩ : syracuseStep 2608955 = 3913433) B3913433
theorem B773947 : Blo 770335 773947 := bstep (se 1 (by rfl) ⟨580460, by rfl⟩ : syracuseStep 773947 = 1160921) B1160921
theorem B774023 : Blo 770335 774023 := bstep (se 1 (by rfl) ⟨580517, by rfl⟩ : syracuseStep 774023 = 1161035) B1161035
theorem B3919751 : Blo 770335 3919751 := bstep (se 1 (by rfl) ⟨2939813, by rfl⟩ : syracuseStep 3919751 = 5879627) B5879627
theorem B774031 : Blo 770335 774031 := bstep (se 1 (by rfl) ⟨580523, by rfl⟩ : syracuseStep 774031 = 1161047) B1161047
theorem B774075 : Blo 770335 774075 := bstep (se 1 (by rfl) ⟨580556, by rfl⟩ : syracuseStep 774075 = 1161113) B1161113
theorem B774151 : Blo 770335 774151 := bstep (se 1 (by rfl) ⟨580613, by rfl⟩ : syracuseStep 774151 = 1161227) B1161227
theorem B774159 : Blo 770335 774159 := bstep (se 1 (by rfl) ⟨580619, by rfl⟩ : syracuseStep 774159 = 1161239) B1161239
theorem B774203 : Blo 770335 774203 := bstep (se 1 (by rfl) ⟨580652, by rfl⟩ : syracuseStep 774203 = 1161305) B1161305
theorem B2510909 : Blo 770335 2510909 := bstep (se 3 (by rfl) ⟨470795, by rfl⟩ : syracuseStep 2510909 = 941591) B941591
theorem B774279 : Blo 770335 774279 := bstep (se 1 (by rfl) ⟨580709, by rfl⟩ : syracuseStep 774279 = 1161419) B1161419
theorem B774287 : Blo 770335 774287 := bstep (se 1 (by rfl) ⟨580715, by rfl⟩ : syracuseStep 774287 = 1161431) B1161431
theorem B774331 : Blo 770335 774331 := bstep (se 1 (by rfl) ⟨580748, by rfl⟩ : syracuseStep 774331 = 1161497) B1161497
theorem B2609441 : Blo 770335 2609441 := bstep (se 2 (by rfl) ⟨978540, by rfl⟩ : syracuseStep 2609441 = 1957081) B1957081
theorem B1102123 : Blo 770335 1102123 := bstep (se 1 (by rfl) ⟨826592, by rfl⟩ : syracuseStep 1102123 = 1653185) B1653185
theorem B8343901 : Blo 770335 8343901 := bstep (se 3 (by rfl) ⟨1564481, by rfl⟩ : syracuseStep 8343901 = 3128963) B3128963
theorem B2478521 : Blo 770335 2478521 := bstep (se 2 (by rfl) ⟨929445, by rfl⟩ : syracuseStep 2478521 = 1858891) B1858891
theorem B1462799 : Blo 770335 1462799 := bstep (se 1 (by rfl) ⟨1097099, by rfl⟩ : syracuseStep 1462799 = 2194199) B2194199
theorem B1102351 : Blo 770335 1102351 := bstep (se 1 (by rfl) ⟨826763, by rfl⟩ : syracuseStep 1102351 = 1653527) B1653527
theorem B1954439 : Blo 770335 1954439 := bstep (se 1 (by rfl) ⟨1465829, by rfl⟩ : syracuseStep 1954439 = 2931659) B2931659
theorem B1954489 : Blo 770335 1954489 := bstep (se 2 (by rfl) ⟨732933, by rfl⟩ : syracuseStep 1954489 = 1465867) B1465867
theorem B1856315 : Blo 770335 1856315 := bstep (se 1 (by rfl) ⟨1392236, by rfl⟩ : syracuseStep 1856315 = 2784473) B2784473
theorem B2610035 : Blo 770335 2610035 := bstep (se 1 (by rfl) ⟨1957526, by rfl⟩ : syracuseStep 2610035 = 3915053) B3915053
theorem B4281241 : Blo 770335 4281241 := bstep (se 2 (by rfl) ⟨1605465, by rfl⟩ : syracuseStep 4281241 = 3210931) B3210931
theorem B2675641 : Blo 770335 2675641 := bstep (se 2 (by rfl) ⟨1003365, by rfl⟩ : syracuseStep 2675641 = 2006731) B2006731
theorem B2479033 : Blo 770335 2479033 := bstep (se 2 (by rfl) ⟨929637, by rfl⟩ : syracuseStep 2479033 = 1859275) B1859275
theorem B2937809 : Blo 770335 2937809 := bstep (se 2 (by rfl) ⟨1101678, by rfl⟩ : syracuseStep 2937809 = 2203357) B2203357
theorem B1463339 : Blo 770335 1463339 := bstep (se 1 (by rfl) ⟨1097504, by rfl⟩ : syracuseStep 1463339 = 2195009) B2195009
theorem B3298391 : Blo 770335 3298391 := bstep (se 1 (by rfl) ⟨2473793, by rfl⟩ : syracuseStep 3298391 = 4947587) B4947587
theorem B1955087 : Blo 770335 1955087 := bstep (se 1 (by rfl) ⟨1466315, by rfl⟩ : syracuseStep 1955087 = 2932631) B2932631
theorem B2938265 : Blo 770335 2938265 := bstep (se 2 (by rfl) ⟨1101849, by rfl⟩ : syracuseStep 2938265 = 2203699) B2203699
theorem B41178545 : Blo 770335 41178545 := bstep (se 2 (by rfl) ⟨15441954, by rfl⟩ : syracuseStep 41178545 = 30883909) B30883909
theorem B5952953 : Blo 770335 5952953 := bstep (se 2 (by rfl) ⟨2232357, by rfl⟩ : syracuseStep 5952953 = 4464715) B4464715
theorem B2086519 : Blo 770335 2086519 := bstep (se 1 (by rfl) ⟨1564889, by rfl⟩ : syracuseStep 2086519 = 3129779) B3129779
theorem B1857143 : Blo 770335 1857143 := bstep (se 1 (by rfl) ⟨1392857, by rfl⟩ : syracuseStep 1857143 = 2785715) B2785715
theorem B3954433 : Blo 770335 3954433 := bstep (se 2 (by rfl) ⟨1482912, by rfl⟩ : syracuseStep 3954433 = 2965825) B2965825
theorem B27121483 : Blo 770335 27121483 := bstep (se 1 (by rfl) ⟨20341112, by rfl⟩ : syracuseStep 27121483 = 40682225) B40682225
theorem B19814219 : Blo 770335 19814219 := bstep (se 1 (by rfl) ⟨14860664, by rfl⟩ : syracuseStep 19814219 = 29721329) B29721329
theorem B1955785 : Blo 770335 1955785 := bstep (se 2 (by rfl) ⟨733419, by rfl⟩ : syracuseStep 1955785 = 1466839) B1466839
theorem B1300495 : Blo 770335 1300495 := bstep (se 1 (by rfl) ⟨975371, by rfl⟩ : syracuseStep 1300495 = 1950743) B1950743
theorem B3758147 : Blo 770335 3758147 := bstep (se 1 (by rfl) ⟨2818610, by rfl⟩ : syracuseStep 3758147 = 5637221) B5637221
theorem B1955927 : Blo 770335 1955927 := bstep (se 1 (by rfl) ⟨1466945, by rfl⟩ : syracuseStep 1955927 = 2933891) B2933891
theorem B2513015 : Blo 770335 2513015 := bstep (se 1 (by rfl) ⟨1884761, by rfl⟩ : syracuseStep 2513015 = 3769523) B3769523
theorem B1464455 : Blo 770335 1464455 := bstep (se 1 (by rfl) ⟨1098341, by rfl⟩ : syracuseStep 1464455 = 2196683) B2196683
theorem B16963829 : Blo 770335 16963829 := bstep (se 5 (by rfl) ⟨795179, by rfl⟩ : syracuseStep 16963829 = 1590359) B1590359
theorem B1301035 : Blo 770335 1301035 := bstep (se 1 (by rfl) ⟨975776, by rfl⟩ : syracuseStep 1301035 = 1951553) B1951553
theorem B2939435 : Blo 770335 2939435 := bstep (se 1 (by rfl) ⟨2204576, by rfl⟩ : syracuseStep 2939435 = 4409153) B4409153
theorem B1464979 : Blo 770335 1464979 := bstep (se 1 (by rfl) ⟨1098734, by rfl⟩ : syracuseStep 1464979 = 2197469) B2197469
theorem B1301177 : Blo 770335 1301177 := bstep (se 2 (by rfl) ⟨487941, by rfl⟩ : syracuseStep 1301177 = 975883) B975883
theorem B1858315 : Blo 770335 1858315 := bstep (se 1 (by rfl) ⟨1393736, by rfl⟩ : syracuseStep 1858315 = 2787473) B2787473
theorem B7134155 : Blo 770335 7134155 := bstep (se 1 (by rfl) ⟨5350616, by rfl⟩ : syracuseStep 7134155 = 10701233) B10701233
theorem B1301879 : Blo 770335 1301879 := bstep (se 1 (by rfl) ⟨976409, by rfl⟩ : syracuseStep 1301879 = 1952819) B1952819
theorem B2612627 : Blo 770335 2612627 := bstep (se 1 (by rfl) ⟨1959470, by rfl⟩ : syracuseStep 2612627 = 3918941) B3918941
theorem B1859219 : Blo 770335 1859219 := bstep (se 1 (by rfl) ⟨1394414, by rfl⟩ : syracuseStep 1859219 = 2788829) B2788829
theorem B1302331 : Blo 770335 1302331 := bstep (se 1 (by rfl) ⟨976748, by rfl⟩ : syracuseStep 1302331 = 1953497) B1953497
theorem B1466171 : Blo 770335 1466171 := bstep (se 1 (by rfl) ⟨1099628, by rfl⟩ : syracuseStep 1466171 = 2199257) B2199257
theorem B4186009 : Blo 770335 4186009 := bstep (se 2 (by rfl) ⟨1569753, by rfl⟩ : syracuseStep 4186009 = 3139507) B3139507
theorem B1302473 : Blo 770335 1302473 := bstep (se 2 (by rfl) ⟨488427, by rfl⟩ : syracuseStep 1302473 = 976855) B976855
theorem B15851543 : Blo 770335 15851543 := bstep (se 1 (by rfl) ⟨11888657, by rfl⟩ : syracuseStep 15851543 = 23777315) B23777315
theorem B1171513 : Blo 770335 1171513 := bstep (se 2 (by rfl) ⟨439317, by rfl⟩ : syracuseStep 1171513 = 878635) B878635
theorem B1958003 : Blo 770335 1958003 := bstep (se 1 (by rfl) ⟨1468502, by rfl⟩ : syracuseStep 1958003 = 2937005) B2937005
theorem B1859699 : Blo 770335 1859699 := bstep (se 1 (by rfl) ⟨1394774, by rfl⟩ : syracuseStep 1859699 = 2789549) B2789549
theorem B2973953 : Blo 770335 2973953 := bstep (se 2 (by rfl) ⟨1115232, by rfl⟩ : syracuseStep 2973953 = 2230465) B2230465
theorem B1466657 : Blo 770335 1466657 := bstep (se 2 (by rfl) ⟨549996, by rfl⟩ : syracuseStep 1466657 = 1099993) B1099993
theorem B14836061 : Blo 770335 14836061 := bstep (se 3 (by rfl) ⟨2781761, by rfl⟩ : syracuseStep 14836061 = 5563523) B5563523
theorem B5857757 : Blo 770335 5857757 := bstep (se 3 (by rfl) ⟨1098329, by rfl⟩ : syracuseStep 5857757 = 2196659) B2196659
theorem B1466923 : Blo 770335 1466923 := bstep (se 1 (by rfl) ⟨1100192, by rfl⟩ : syracuseStep 1466923 = 2200385) B2200385
theorem B1958519 : Blo 770335 1958519 := bstep (se 1 (by rfl) ⟨1468889, by rfl⟩ : syracuseStep 1958519 = 2937779) B2937779
theorem B1303175 : Blo 770335 1303175 := bstep (se 1 (by rfl) ⟨977381, by rfl⟩ : syracuseStep 1303175 = 1954763) B1954763
theorem B975503 : Blo 770335 975503 := bstep (se 1 (by rfl) ⟨731627, by rfl⟩ : syracuseStep 975503 = 1463255) B1463255
theorem B2089739 : Blo 770335 2089739 := bstep (se 1 (by rfl) ⟨1567304, by rfl⟩ : syracuseStep 2089739 = 3134609) B3134609
theorem B8938291 : Blo 770335 8938291 := bstep (se 1 (by rfl) ⟨6703718, by rfl⟩ : syracuseStep 8938291 = 13407437) B13407437
theorem B6251417 : Blo 770335 6251417 := bstep (se 2 (by rfl) ⟨2344281, by rfl⟩ : syracuseStep 6251417 = 4688563) B4688563
theorem B1303823 : Blo 770335 1303823 := bstep (se 1 (by rfl) ⟨977867, by rfl⟩ : syracuseStep 1303823 = 1955735) B1955735
theorem B16934429 : Blo 770335 16934429 := bstep (se 3 (by rfl) ⟨3175205, by rfl⟩ : syracuseStep 16934429 = 6350411) B6350411
theorem B1959511 : Blo 770335 1959511 := bstep (se 1 (by rfl) ⟨1469633, by rfl⟩ : syracuseStep 1959511 = 2939267) B2939267
theorem B1468039 : Blo 770335 1468039 := bstep (se 1 (by rfl) ⟨1101029, by rfl⟩ : syracuseStep 1468039 = 2202059) B2202059
theorem B1304363 : Blo 770335 1304363 := bstep (se 1 (by rfl) ⟨978272, by rfl⟩ : syracuseStep 1304363 = 1956545) B1956545
theorem B4450099 : Blo 770335 4450099 := bstep (se 1 (by rfl) ⟨3337574, by rfl⟩ : syracuseStep 4450099 = 6675149) B6675149
theorem B1959815 : Blo 770335 1959815 := bstep (se 1 (by rfl) ⟨1469861, by rfl⟩ : syracuseStep 1959815 = 2939723) B2939723
theorem B1959947 : Blo 770335 1959947 := bstep (se 1 (by rfl) ⟨1469960, by rfl⟩ : syracuseStep 1959947 = 2939921) B2939921
theorem B2353195 : Blo 770335 2353195 := bstep (se 1 (by rfl) ⟨1764896, by rfl⟩ : syracuseStep 2353195 = 3529793) B3529793
theorem B1304761 : Blo 770335 1304761 := bstep (se 2 (by rfl) ⟨489285, by rfl⟩ : syracuseStep 1304761 = 978571) B978571
theorem B1468601 : Blo 770335 1468601 := bstep (se 2 (by rfl) ⟨550725, by rfl⟩ : syracuseStep 1468601 = 1101451) B1101451
theorem B68512013 : Blo 770335 68512013 := bstep (se 3 (by rfl) ⟨12846002, by rfl⟩ : syracuseStep 68512013 = 25692005) B25692005
theorem B1763785 : Blo 770335 1763785 := bstep (se 2 (by rfl) ⟨661419, by rfl⟩ : syracuseStep 1763785 = 1322839) B1322839
theorem B1239671 : Blo 770335 1239671 := bstep (se 1 (by rfl) ⟨929753, by rfl⟩ : syracuseStep 1239671 = 1859507) B1859507
theorem B1043129 : Blo 770335 1043129 := bstep (se 2 (by rfl) ⟨391173, by rfl⟩ : syracuseStep 1043129 = 782347) B782347
theorem B1305463 : Blo 770335 1305463 := bstep (se 1 (by rfl) ⟨979097, by rfl⟩ : syracuseStep 1305463 = 1958195) B1958195
theorem B5565347 : Blo 770335 5565347 := bstep (se 1 (by rfl) ⟨4174010, by rfl⟩ : syracuseStep 5565347 = 8348021) B8348021
theorem B1764385 : Blo 770335 1764385 := bstep (se 2 (by rfl) ⟨661644, by rfl⟩ : syracuseStep 1764385 = 1323289) B1323289
theorem B1305659 : Blo 770335 1305659 := bstep (se 1 (by rfl) ⟨979244, by rfl⟩ : syracuseStep 1305659 = 1958489) B1958489
theorem B3337453 : Blo 770335 3337453 := bstep (se 3 (by rfl) ⟨625772, by rfl⟩ : syracuseStep 3337453 = 1251545) B1251545
theorem B3304763 : Blo 770335 3304763 := bstep (se 1 (by rfl) ⟨2478572, by rfl⟩ : syracuseStep 3304763 = 4957145) B4957145
theorem B1469755 : Blo 770335 1469755 := bstep (se 1 (by rfl) ⟨1102316, by rfl⟩ : syracuseStep 1469755 = 2204633) B2204633
theorem B18836837 : Blo 770335 18836837 := bstep (se 4 (by rfl) ⟨1765953, by rfl⟩ : syracuseStep 18836837 = 3531907) B3531907
theorem B6254009 : Blo 770335 6254009 := bstep (se 2 (by rfl) ⟨2345253, by rfl⟩ : syracuseStep 6254009 = 4690507) B4690507
theorem B1306057 : Blo 770335 1306057 := bstep (se 2 (by rfl) ⟨489771, by rfl⟩ : syracuseStep 1306057 = 979543) B979543
theorem B22244867 : Blo 770335 22244867 := bstep (se 1 (by rfl) ⟨16683650, by rfl⟩ : syracuseStep 22244867 = 33367301) B33367301
theorem B978475 : Blo 770335 978475 := bstep (se 1 (by rfl) ⟨733856, by rfl⟩ : syracuseStep 978475 = 1467713) B1467713
theorem B7433795 : Blo 770335 7433795 := bstep (se 1 (by rfl) ⟨5575346, by rfl⟩ : syracuseStep 7433795 = 11150693) B11150693
theorem B21131009 : Blo 770335 21131009 := bstep (se 2 (by rfl) ⟨7924128, by rfl⟩ : syracuseStep 21131009 = 15848257) B15848257
theorem B979447 : Blo 770335 979447 := bstep (se 1 (by rfl) ⟨734585, by rfl⟩ : syracuseStep 979447 = 1469171) B1469171
theorem B4452893 : Blo 770335 4452893 := bstep (se 3 (by rfl) ⟨834917, by rfl⟩ : syracuseStep 4452893 = 1669835) B1669835
theorem B1733255 : Blo 770335 1733255 := bstep (se 1 (by rfl) ⟨1299941, by rfl⟩ : syracuseStep 1733255 = 2599883) B2599883
theorem B1733435 : Blo 770335 1733435 := bstep (se 1 (by rfl) ⟨1300076, by rfl⟩ : syracuseStep 1733435 = 2600153) B2600153
theorem B979771 : Blo 770335 979771 := bstep (se 1 (by rfl) ⟨734828, by rfl⟩ : syracuseStep 979771 = 1469657) B1469657
theorem B1733561 : Blo 770335 1733561 := bstep (se 2 (by rfl) ⟨650085, by rfl⟩ : syracuseStep 1733561 = 1300171) B1300171
theorem B2683991 : Blo 770335 2683991 := bstep (se 1 (by rfl) ⟨2012993, by rfl⟩ : syracuseStep 2683991 = 4025987) B4025987
theorem B8909941 : Blo 770335 8909941 := bstep (se 5 (by rfl) ⟨417653, by rfl⟩ : syracuseStep 8909941 = 835307) B835307
theorem B4388033 : Blo 770335 4388033 := bstep (se 2 (by rfl) ⟨1645512, by rfl⟩ : syracuseStep 4388033 = 3291025) B3291025
theorem B90273005 : Blo 770335 90273005 := bstep (se 3 (by rfl) ⟨16926188, by rfl⟩ : syracuseStep 90273005 = 33852377) B33852377
theorem B1733903 : Blo 770335 1733903 := bstep (se 1 (by rfl) ⟨1300427, by rfl⟩ : syracuseStep 1733903 = 2600855) B2600855
theorem B1733921 : Blo 770335 1733921 := bstep (se 2 (by rfl) ⟨650220, by rfl⟩ : syracuseStep 1733921 = 1300441) B1300441
theorem B1734263 : Blo 770335 1734263 := bstep (se 1 (by rfl) ⟨1300697, by rfl⟩ : syracuseStep 1734263 = 2601395) B2601395
theorem B8812151 : Blo 770335 8812151 := bstep (se 1 (by rfl) ⟨6609113, by rfl⟩ : syracuseStep 8812151 = 13218227) B13218227
theorem B1734443 : Blo 770335 1734443 := bstep (se 1 (by rfl) ⟨1300832, by rfl⟩ : syracuseStep 1734443 = 2601665) B2601665
theorem B4454279 : Blo 770335 4454279 := bstep (se 1 (by rfl) ⟨3340709, by rfl⟩ : syracuseStep 4454279 = 6681419) B6681419
theorem B18741293 : Blo 770335 18741293 := bstep (se 3 (by rfl) ⟨3513992, by rfl⟩ : syracuseStep 18741293 = 7027985) B7027985
theorem B1734803 : Blo 770335 1734803 := bstep (se 1 (by rfl) ⟨1301102, by rfl⟩ : syracuseStep 1734803 = 2602205) B2602205
theorem B1112249 : Blo 770335 1112249 := bstep (se 2 (by rfl) ⟨417093, by rfl⟩ : syracuseStep 1112249 = 834187) B834187
theorem B1734857 : Blo 770335 1734857 := bstep (se 2 (by rfl) ⟨650571, by rfl⟩ : syracuseStep 1734857 = 1301143) B1301143
theorem B73202069 : Blo 770335 73202069 := bstep (se 6 (by rfl) ⟨1715673, by rfl⟩ : syracuseStep 73202069 = 3431347) B3431347
theorem B23788151 : Blo 770335 23788151 := bstep (se 1 (by rfl) ⟨17841113, by rfl⟩ : syracuseStep 23788151 = 35682227) B35682227
theorem B13368025 : Blo 770335 13368025 := bstep (se 2 (by rfl) ⟨5013009, by rfl⟩ : syracuseStep 13368025 = 10026019) B10026019
theorem B14875427 : Blo 770335 14875427 := bstep (se 1 (by rfl) ⟨11156570, by rfl⟩ : syracuseStep 14875427 = 22313141) B22313141
theorem B1735559 : Blo 770335 1735559 := bstep (se 1 (by rfl) ⟨1301669, by rfl⟩ : syracuseStep 1735559 = 2603339) B2603339
theorem B2784185 : Blo 770335 2784185 := bstep (se 2 (by rfl) ⟨1044069, by rfl⟩ : syracuseStep 2784185 = 2088139) B2088139
theorem B2784299 : Blo 770335 2784299 := bstep (se 1 (by rfl) ⟨2088224, by rfl⟩ : syracuseStep 2784299 = 4176449) B4176449
theorem B1735739 : Blo 770335 1735739 := bstep (se 1 (by rfl) ⟨1301804, by rfl⟩ : syracuseStep 1735739 = 2603609) B2603609
theorem B1735865 : Blo 770335 1735865 := bstep (se 2 (by rfl) ⟨650949, by rfl⟩ : syracuseStep 1735865 = 1301899) B1301899
theorem B1736207 : Blo 770335 1736207 := bstep (se 1 (by rfl) ⟨1302155, by rfl⟩ : syracuseStep 1736207 = 2604311) B2604311
theorem B1736225 : Blo 770335 1736225 := bstep (se 2 (by rfl) ⟨651084, by rfl⟩ : syracuseStep 1736225 = 1302169) B1302169
theorem B114392675 : Blo 770335 114392675 := bstep (se 1 (by rfl) ⟨85794506, by rfl⟩ : syracuseStep 114392675 = 171589013) B171589013
theorem B2195201 : Blo 770335 2195201 := bstep (se 2 (by rfl) ⟨823200, by rfl⟩ : syracuseStep 2195201 = 1646401) B1646401
theorem B4947713 : Blo 770335 4947713 := bstep (se 2 (by rfl) ⟨1855392, by rfl⟩ : syracuseStep 4947713 = 3710785) B3710785
theorem B1736567 : Blo 770335 1736567 := bstep (se 1 (by rfl) ⟨1302425, by rfl⟩ : syracuseStep 1736567 = 2604851) B2604851
theorem B9404363 : Blo 770335 9404363 := bstep (se 1 (by rfl) ⟨7053272, by rfl⟩ : syracuseStep 9404363 = 14106545) B14106545
theorem B1736711 : Blo 770335 1736711 := bstep (se 1 (by rfl) ⟨1302533, by rfl⟩ : syracuseStep 1736711 = 2605067) B2605067
theorem B4390949 : Blo 770335 4390949 := bstep (se 4 (by rfl) ⟨411651, by rfl⟩ : syracuseStep 4390949 = 823303) B823303
theorem B42270781 : Blo 770335 42270781 := bstep (se 3 (by rfl) ⟨7925771, by rfl⟩ : syracuseStep 42270781 = 15851543) B15851543
theorem B1736783 : Blo 770335 1736783 := bstep (se 1 (by rfl) ⟨1302587, by rfl⟩ : syracuseStep 1736783 = 2605175) B2605175
theorem B12550373 : Blo 770335 12550373 := bstep (se 4 (by rfl) ⟨1176597, by rfl⟩ : syracuseStep 12550373 = 2353195) B2353195
theorem B1737179 : Blo 770335 1737179 := bstep (se 1 (by rfl) ⟨1302884, by rfl⟩ : syracuseStep 1737179 = 2605769) B2605769
theorem B4391405 : Blo 770335 4391405 := bstep (se 3 (by rfl) ⟨823388, by rfl⟩ : syracuseStep 4391405 = 1646777) B1646777
theorem B7930541 : Blo 770335 7930541 := bstep (se 3 (by rfl) ⟨1486976, by rfl⟩ : syracuseStep 7930541 = 2973953) B2973953
theorem B1737647 : Blo 770335 1737647 := bstep (se 1 (by rfl) ⟨1303235, by rfl⟩ : syracuseStep 1737647 = 2606471) B2606471
theorem B24052787 : Blo 770335 24052787 := bstep (se 1 (by rfl) ⟨18039590, by rfl⟩ : syracuseStep 24052787 = 36079181) B36079181
theorem B4392089 : Blo 770335 4392089 := bstep (se 2 (by rfl) ⟨1647033, by rfl⟩ : syracuseStep 4392089 = 3294067) B3294067
theorem B1737899 : Blo 770335 1737899 := bstep (se 1 (by rfl) ⟨1303424, by rfl⟩ : syracuseStep 1737899 = 2606849) B2606849
theorem B3966155 : Blo 770335 3966155 := bstep (se 1 (by rfl) ⟨2974616, by rfl⟩ : syracuseStep 3966155 = 5949233) B5949233
theorem B3900797 : Blo 770335 3900797 := bstep (se 3 (by rfl) ⟨731399, by rfl⟩ : syracuseStep 3900797 = 1462799) B1462799
theorem B2197115 : Blo 770335 2197115 := bstep (se 1 (by rfl) ⟨1647836, by rfl⟩ : syracuseStep 2197115 = 3295673) B3295673
theorem B1738439 : Blo 770335 1738439 := bstep (se 1 (by rfl) ⟨1303829, by rfl⟩ : syracuseStep 1738439 = 2607659) B2607659
theorem B13174487 : Blo 770335 13174487 := bstep (se 1 (by rfl) ⟨9880865, by rfl⟩ : syracuseStep 13174487 = 19761731) B19761731
theorem B2197343 : Blo 770335 2197343 := bstep (se 1 (by rfl) ⟨1648007, by rfl⟩ : syracuseStep 2197343 = 3296015) B3296015
theorem B5572637 : Blo 770335 5572637 := bstep (se 3 (by rfl) ⟨1044869, by rfl⟩ : syracuseStep 5572637 = 2089739) B2089739
theorem B4950173 : Blo 770335 4950173 := bstep (se 3 (by rfl) ⟨928157, by rfl⟩ : syracuseStep 4950173 = 1856315) B1856315
theorem B5933465 : Blo 770335 5933465 := bstep (se 2 (by rfl) ⟨2225049, by rfl⟩ : syracuseStep 5933465 = 4450099) B4450099
theorem B1739303 : Blo 770335 1739303 := bstep (se 1 (by rfl) ⟨1304477, by rfl⟩ : syracuseStep 1739303 = 2608955) B2608955
theorem B1673939 : Blo 770335 1673939 := bstep (se 1 (by rfl) ⟨1255454, by rfl⟩ : syracuseStep 1673939 = 2510909) B2510909
theorem B1739627 : Blo 770335 1739627 := bstep (se 1 (by rfl) ⟨1304720, by rfl⟩ : syracuseStep 1739627 = 2609441) B2609441
theorem B1739681 : Blo 770335 1739681 := bstep (se 2 (by rfl) ⟨652380, by rfl⟩ : syracuseStep 1739681 = 1304761) B1304761
theorem B5573879 : Blo 770335 5573879 := bstep (se 1 (by rfl) ⟨4180409, by rfl⟩ : syracuseStep 5573879 = 8360819) B8360819
theorem B1740023 : Blo 770335 1740023 := bstep (se 1 (by rfl) ⟨1305017, by rfl⟩ : syracuseStep 1740023 = 2610035) B2610035
theorem B2198927 : Blo 770335 2198927 := bstep (se 1 (by rfl) ⟨1649195, by rfl⟩ : syracuseStep 2198927 = 3298391) B3298391
theorem B7409191 : Blo 770335 7409191 := bstep (se 1 (by rfl) ⟨5556893, by rfl⟩ : syracuseStep 7409191 = 11113787) B11113787
theorem B3968635 : Blo 770335 3968635 := bstep (se 1 (by rfl) ⟨2976476, by rfl⟩ : syracuseStep 3968635 = 5952953) B5952953
theorem B1740617 : Blo 770335 1740617 := bstep (se 2 (by rfl) ⟨652731, by rfl⟩ : syracuseStep 1740617 = 1305463) B1305463
theorem B5869421 : Blo 770335 5869421 := bstep (se 3 (by rfl) ⟨1100516, by rfl⟩ : syracuseStep 5869421 = 2201033) B2201033
theorem B13209479 : Blo 770335 13209479 := bstep (se 1 (by rfl) ⟨9907109, by rfl⟩ : syracuseStep 13209479 = 19814219) B19814219
theorem B1675343 : Blo 770335 1675343 := bstep (se 1 (by rfl) ⟨1256507, by rfl⟩ : syracuseStep 1675343 = 2513015) B2513015
theorem B11309219 : Blo 770335 11309219 := bstep (se 1 (by rfl) ⟨8481914, by rfl⟩ : syracuseStep 11309219 = 16963829) B16963829
theorem B17174705 : Blo 770335 17174705 := bstep (se 2 (by rfl) ⟨6440514, by rfl⟩ : syracuseStep 17174705 = 12881029) B12881029
theorem B1741409 : Blo 770335 1741409 := bstep (se 2 (by rfl) ⟨653028, by rfl⟩ : syracuseStep 1741409 = 1306057) B1306057
theorem B4756103 : Blo 770335 4756103 := bstep (se 1 (by rfl) ⟨3567077, by rfl⟩ : syracuseStep 4756103 = 7134155) B7134155
theorem B4395779 : Blo 770335 4395779 := bstep (se 1 (by rfl) ⟨3296834, by rfl⟩ : syracuseStep 4395779 = 6593669) B6593669
theorem B1741751 : Blo 770335 1741751 := bstep (se 1 (by rfl) ⟨1306313, by rfl⟩ : syracuseStep 1741751 = 2612627) B2612627
theorem B10327105 : Blo 770335 10327105 := bstep (se 2 (by rfl) ⟨3872664, by rfl⟩ : syracuseStep 10327105 = 7745329) B7745329
theorem B7410959 : Blo 770335 7410959 := bstep (se 1 (by rfl) ⟨5558219, by rfl⟩ : syracuseStep 7410959 = 11116439) B11116439
theorem B8787365 : Blo 770335 8787365 := bstep (se 4 (by rfl) ⟨823815, by rfl⟩ : syracuseStep 8787365 = 1647631) B1647631
theorem B9410053 : Blo 770335 9410053 := bstep (se 4 (by rfl) ⟨882192, by rfl⟩ : syracuseStep 9410053 = 1764385) B1764385
theorem B3905171 : Blo 770335 3905171 := bstep (se 1 (by rfl) ⟨2928878, by rfl⟩ : syracuseStep 3905171 = 5857757) B5857757
theorem B8361721 : Blo 770335 8361721 := bstep (se 2 (by rfl) ⟨3135645, by rfl⟩ : syracuseStep 8361721 = 6271291) B6271291
theorem B2234105 : Blo 770335 2234105 := bstep (se 2 (by rfl) ⟨837789, by rfl⟩ : syracuseStep 2234105 = 1675579) B1675579
theorem B23729921 : Blo 770335 23729921 := bstep (se 2 (by rfl) ⟨8898720, by rfl⟩ : syracuseStep 23729921 = 17797441) B17797441
theorem B4167611 : Blo 770335 4167611 := bstep (se 1 (by rfl) ⟨3125708, by rfl⟩ : syracuseStep 4167611 = 6251417) B6251417
theorem B5708321 : Blo 770335 5708321 := bstep (se 2 (by rfl) ⟨2140620, by rfl⟩ : syracuseStep 5708321 = 4281241) B4281241
theorem B11115053 : Blo 770335 11115053 := bstep (se 3 (by rfl) ⟨2084072, by rfl⟩ : syracuseStep 11115053 = 4168145) B4168145
theorem B5872337 : Blo 770335 5872337 := bstep (se 2 (by rfl) ⟨2202126, by rfl⟩ : syracuseStep 5872337 = 4404253) B4404253
theorem B826447 : Blo 770335 826447 := bstep (se 1 (by rfl) ⟨619835, by rfl⟩ : syracuseStep 826447 = 1239671) B1239671
theorem B12524813 : Blo 770335 12524813 := bstep (se 3 (by rfl) ⟨2348402, by rfl⟩ : syracuseStep 12524813 = 4696805) B4696805
theorem B3710231 : Blo 770335 3710231 := bstep (se 1 (by rfl) ⟨2782673, by rfl⟩ : syracuseStep 3710231 = 5565347) B5565347
theorem B2203175 : Blo 770335 2203175 := bstep (se 1 (by rfl) ⟨1652381, by rfl⟩ : syracuseStep 2203175 = 3304763) B3304763
theorem B12557891 : Blo 770335 12557891 := bstep (se 1 (by rfl) ⟨9418418, by rfl⟩ : syracuseStep 12557891 = 18836837) B18836837
theorem B9379451 : Blo 770335 9379451 := bstep (se 1 (by rfl) ⟨7034588, by rfl⟩ : syracuseStep 9379451 = 14069177) B14069177
theorem B4169339 : Blo 770335 4169339 := bstep (se 1 (by rfl) ⟨3127004, by rfl⟩ : syracuseStep 4169339 = 6254009) B6254009
theorem B4955863 : Blo 770335 4955863 := bstep (se 1 (by rfl) ⟨3716897, by rfl⟩ : syracuseStep 4955863 = 7433795) B7433795
theorem B1155503 : Blo 770335 1155503 := bstep (se 1 (by rfl) ⟨866627, by rfl⟩ : syracuseStep 1155503 = 1733255) B1733255
theorem B1155593 : Blo 770335 1155593 := bstep (se 2 (by rfl) ⟨433347, by rfl⟩ : syracuseStep 1155593 = 866695) B866695
theorem B1155623 : Blo 770335 1155623 := bstep (se 1 (by rfl) ⟨866717, by rfl⟩ : syracuseStep 1155623 = 1733435) B1733435
theorem B1155707 : Blo 770335 1155707 := bstep (se 1 (by rfl) ⟨866780, by rfl⟩ : syracuseStep 1155707 = 1733561) B1733561
theorem B1155833 : Blo 770335 1155833 := bstep (se 2 (by rfl) ⟨433437, by rfl⟩ : syracuseStep 1155833 = 866875) B866875
theorem B2925341 : Blo 770335 2925341 := bstep (se 3 (by rfl) ⟨548501, by rfl⟩ : syracuseStep 2925341 = 1097003) B1097003
theorem B2925355 : Blo 770335 2925355 := bstep (se 1 (by rfl) ⟨2194016, by rfl⟩ : syracuseStep 2925355 = 4388033) B4388033
theorem B1155935 : Blo 770335 1155935 := bstep (se 1 (by rfl) ⟨866951, by rfl⟩ : syracuseStep 1155935 = 1733903) B1733903
theorem B1155947 : Blo 770335 1155947 := bstep (se 1 (by rfl) ⟨866960, by rfl⟩ : syracuseStep 1155947 = 1733921) B1733921
theorem B1156175 : Blo 770335 1156175 := bstep (se 1 (by rfl) ⟨867131, by rfl⟩ : syracuseStep 1156175 = 1734263) B1734263
theorem B5874767 : Blo 770335 5874767 := bstep (se 1 (by rfl) ⟨4406075, by rfl⟩ : syracuseStep 5874767 = 8812151) B8812151
theorem B1156295 : Blo 770335 1156295 := bstep (se 1 (by rfl) ⟨867221, by rfl⟩ : syracuseStep 1156295 = 1734443) B1734443
theorem B1156457 : Blo 770335 1156457 := bstep (se 2 (by rfl) ⟨433671, by rfl⟩ : syracuseStep 1156457 = 867343) B867343
theorem B12494195 : Blo 770335 12494195 := bstep (se 1 (by rfl) ⟨9370646, by rfl⟩ : syracuseStep 12494195 = 18741293) B18741293
theorem B1156535 : Blo 770335 1156535 := bstep (se 1 (by rfl) ⟨867401, by rfl⟩ : syracuseStep 1156535 = 1734803) B1734803
theorem B1156571 : Blo 770335 1156571 := bstep (se 1 (by rfl) ⟨867428, by rfl⟩ : syracuseStep 1156571 = 1734857) B1734857
theorem B48801379 : Blo 770335 48801379 := bstep (se 1 (by rfl) ⟨36601034, by rfl⟩ : syracuseStep 48801379 = 73202069) B73202069
theorem B1157039 : Blo 770335 1157039 := bstep (se 1 (by rfl) ⟨867779, by rfl⟩ : syracuseStep 1157039 = 1735559) B1735559
theorem B1157129 : Blo 770335 1157129 := bstep (se 2 (by rfl) ⟨433923, by rfl⟩ : syracuseStep 1157129 = 867847) B867847
theorem B1157159 : Blo 770335 1157159 := bstep (se 1 (by rfl) ⟨867869, by rfl⟩ : syracuseStep 1157159 = 1735739) B1735739
theorem B1157243 : Blo 770335 1157243 := bstep (se 1 (by rfl) ⟨867932, by rfl⟩ : syracuseStep 1157243 = 1735865) B1735865
theorem B1648811 : Blo 770335 1648811 := bstep (se 1 (by rfl) ⟨1236608, by rfl⟩ : syracuseStep 1648811 = 2473217) B2473217
theorem B1157369 : Blo 770335 1157369 := bstep (se 2 (by rfl) ⟨434013, by rfl⟩ : syracuseStep 1157369 = 868027) B868027
theorem B1157471 : Blo 770335 1157471 := bstep (se 1 (by rfl) ⟨868103, by rfl⟩ : syracuseStep 1157471 = 1736207) B1736207
theorem B1157483 : Blo 770335 1157483 := bstep (se 1 (by rfl) ⟨868112, by rfl⟩ : syracuseStep 1157483 = 1736225) B1736225
theorem B76261783 : Blo 770335 76261783 := bstep (se 1 (by rfl) ⟨57196337, by rfl⟩ : syracuseStep 76261783 = 114392675) B114392675
theorem B5581345 : Blo 770335 5581345 := bstep (se 2 (by rfl) ⟨2093004, by rfl⟩ : syracuseStep 5581345 = 4186009) B4186009
theorem B1157711 : Blo 770335 1157711 := bstep (se 1 (by rfl) ⟨868283, by rfl⟩ : syracuseStep 1157711 = 1736567) B1736567
theorem B928379 : Blo 770335 928379 := bstep (se 1 (by rfl) ⟨696284, by rfl⟩ : syracuseStep 928379 = 1392569) B1392569
theorem B6269575 : Blo 770335 6269575 := bstep (se 1 (by rfl) ⟨4702181, by rfl⟩ : syracuseStep 6269575 = 9404363) B9404363
theorem B1157831 : Blo 770335 1157831 := bstep (se 1 (by rfl) ⟨868373, by rfl⟩ : syracuseStep 1157831 = 1736747) B1736747
theorem B3910355 : Blo 770335 3910355 := bstep (se 1 (by rfl) ⟨2932766, by rfl⟩ : syracuseStep 3910355 = 5865533) B5865533
theorem B1157993 : Blo 770335 1157993 := bstep (se 2 (by rfl) ⟨434247, by rfl⟩ : syracuseStep 1157993 = 868495) B868495
theorem B928687 : Blo 770335 928687 := bstep (se 1 (by rfl) ⟨696515, by rfl⟩ : syracuseStep 928687 = 1393031) B1393031
theorem B1158071 : Blo 770335 1158071 := bstep (se 1 (by rfl) ⟨868553, by rfl⟩ : syracuseStep 1158071 = 1737107) B1737107
theorem B1158107 : Blo 770335 1158107 := bstep (se 1 (by rfl) ⟨868580, by rfl⟩ : syracuseStep 1158107 = 1737161) B1737161
theorem B2599937 : Blo 770335 2599937 := bstep (se 2 (by rfl) ⟨974976, by rfl⟩ : syracuseStep 2599937 = 1949953) B1949953
theorem B1158575 : Blo 770335 1158575 := bstep (se 1 (by rfl) ⟨868931, by rfl⟩ : syracuseStep 1158575 = 1737863) B1737863
theorem B1158665 : Blo 770335 1158665 := bstep (se 2 (by rfl) ⟨434499, by rfl⟩ : syracuseStep 1158665 = 868999) B868999
theorem B1158695 : Blo 770335 1158695 := bstep (se 1 (by rfl) ⟨869021, by rfl⟩ : syracuseStep 1158695 = 1738043) B1738043
theorem B1158779 : Blo 770335 1158779 := bstep (se 1 (by rfl) ⟨869084, by rfl⟩ : syracuseStep 1158779 = 1738169) B1738169
theorem B10038923 : Blo 770335 10038923 := bstep (se 1 (by rfl) ⟨7529192, by rfl⟩ : syracuseStep 10038923 = 15058385) B15058385
theorem B1158905 : Blo 770335 1158905 := bstep (se 2 (by rfl) ⟨434589, by rfl⟩ : syracuseStep 1158905 = 869179) B869179
theorem B2600747 : Blo 770335 2600747 := bstep (se 1 (by rfl) ⟨1950560, by rfl⟩ : syracuseStep 2600747 = 3901121) B3901121
theorem B3714859 : Blo 770335 3714859 := bstep (se 1 (by rfl) ⟨2786144, by rfl⟩ : syracuseStep 3714859 = 5572289) B5572289
theorem B1159007 : Blo 770335 1159007 := bstep (se 1 (by rfl) ⟨869255, by rfl⟩ : syracuseStep 1159007 = 1738511) B1738511
theorem B1159019 : Blo 770335 1159019 := bstep (se 1 (by rfl) ⟨869264, by rfl⟩ : syracuseStep 1159019 = 1738529) B1738529
theorem B2928545 : Blo 770335 2928545 := bstep (se 2 (by rfl) ⟨1098204, by rfl⟩ : syracuseStep 2928545 = 2196409) B2196409
theorem B3125267 : Blo 770335 3125267 := bstep (se 1 (by rfl) ⟨2343950, by rfl⟩ : syracuseStep 3125267 = 4687901) B4687901
theorem B1650707 : Blo 770335 1650707 := bstep (se 1 (by rfl) ⟨1238030, by rfl⟩ : syracuseStep 1650707 = 2476061) B2476061
theorem B2601017 : Blo 770335 2601017 := bstep (se 2 (by rfl) ⟨975381, by rfl⟩ : syracuseStep 2601017 = 1950763) B1950763
theorem B1159247 : Blo 770335 1159247 := bstep (se 1 (by rfl) ⟨869435, by rfl⟩ : syracuseStep 1159247 = 1738871) B1738871
theorem B1159367 : Blo 770335 1159367 := bstep (se 1 (by rfl) ⟨869525, by rfl⟩ : syracuseStep 1159367 = 1739051) B1739051
theorem B1159529 : Blo 770335 1159529 := bstep (se 2 (by rfl) ⟨434823, by rfl⟩ : syracuseStep 1159529 = 869647) B869647
theorem B2601341 : Blo 770335 2601341 := bstep (se 3 (by rfl) ⟨487751, by rfl⟩ : syracuseStep 2601341 = 975503) B975503
theorem B5878169 : Blo 770335 5878169 := bstep (se 2 (by rfl) ⟨2204313, by rfl⟩ : syracuseStep 5878169 = 4408627) B4408627
theorem B1159607 : Blo 770335 1159607 := bstep (se 1 (by rfl) ⟨869705, by rfl⟩ : syracuseStep 1159607 = 1739411) B1739411
theorem B1159643 : Blo 770335 1159643 := bstep (se 1 (by rfl) ⟨869732, by rfl⟩ : syracuseStep 1159643 = 1739465) B1739465
theorem B2601611 : Blo 770335 2601611 := bstep (se 1 (by rfl) ⟨1951208, by rfl⟩ : syracuseStep 2601611 = 3902417) B3902417
theorem B2929517 : Blo 770335 2929517 := bstep (se 3 (by rfl) ⟨549284, by rfl⟩ : syracuseStep 2929517 = 1098569) B1098569
theorem B3912623 : Blo 770335 3912623 := bstep (se 1 (by rfl) ⟨2934467, by rfl⟩ : syracuseStep 3912623 = 5868935) B5868935
theorem B1160111 : Blo 770335 1160111 := bstep (se 1 (by rfl) ⟨870083, by rfl⟩ : syracuseStep 1160111 = 1740167) B1740167
theorem B1160201 : Blo 770335 1160201 := bstep (se 2 (by rfl) ⟨435075, by rfl⟩ : syracuseStep 1160201 = 870151) B870151
theorem B1160231 : Blo 770335 1160231 := bstep (se 1 (by rfl) ⟨870173, by rfl⟩ : syracuseStep 1160231 = 1740347) B1740347
theorem B1160315 : Blo 770335 1160315 := bstep (se 1 (by rfl) ⟨870236, by rfl⟩ : syracuseStep 1160315 = 1740473) B1740473
theorem B1160441 : Blo 770335 1160441 := bstep (se 2 (by rfl) ⟨435165, by rfl⟩ : syracuseStep 1160441 = 870331) B870331
theorem B1160543 : Blo 770335 1160543 := bstep (se 1 (by rfl) ⟨870407, by rfl⟩ : syracuseStep 1160543 = 1740815) B1740815
theorem B1488233 : Blo 770335 1488233 := bstep (se 2 (by rfl) ⟨558087, by rfl⟩ : syracuseStep 1488233 = 1116175) B1116175
theorem B1160555 : Blo 770335 1160555 := bstep (se 1 (by rfl) ⟨870416, by rfl⟩ : syracuseStep 1160555 = 1740833) B1740833
theorem B2930201 : Blo 770335 2930201 := bstep (se 2 (by rfl) ⟨1098825, by rfl⟩ : syracuseStep 2930201 = 2197651) B2197651
theorem B2602529 : Blo 770335 2602529 := bstep (se 2 (by rfl) ⟨975948, by rfl⟩ : syracuseStep 2602529 = 1951897) B1951897
theorem B2930215 : Blo 770335 2930215 := bstep (se 1 (by rfl) ⟨2197661, by rfl⟩ : syracuseStep 2930215 = 4395323) B4395323
theorem B1160783 : Blo 770335 1160783 := bstep (se 1 (by rfl) ⟨870587, by rfl⟩ : syracuseStep 1160783 = 1741175) B1741175
theorem B3716705 : Blo 770335 3716705 := bstep (se 2 (by rfl) ⟨1393764, by rfl⟩ : syracuseStep 3716705 = 2787529) B2787529
theorem B1652347 : Blo 770335 1652347 := bstep (se 1 (by rfl) ⟨1239260, by rfl⟩ : syracuseStep 1652347 = 2478521) B2478521
theorem B1160903 : Blo 770335 1160903 := bstep (se 1 (by rfl) ⟨870677, by rfl⟩ : syracuseStep 1160903 = 1741355) B1741355
theorem B2602745 : Blo 770335 2602745 := bstep (se 2 (by rfl) ⟨976029, by rfl⟩ : syracuseStep 2602745 = 1952059) B1952059
theorem B1161065 : Blo 770335 1161065 := bstep (se 2 (by rfl) ⟨435399, by rfl⟩ : syracuseStep 1161065 = 870799) B870799
theorem B1161143 : Blo 770335 1161143 := bstep (se 1 (by rfl) ⟨870857, by rfl⟩ : syracuseStep 1161143 = 1741715) B1741715
theorem B4175803 : Blo 770335 4175803 := bstep (se 1 (by rfl) ⟨3131852, by rfl⟩ : syracuseStep 4175803 = 6263705) B6263705
theorem B8796113 : Blo 770335 8796113 := bstep (se 2 (by rfl) ⟨3298542, by rfl⟩ : syracuseStep 8796113 = 6597085) B6597085
theorem B6272977 : Blo 770335 6272977 := bstep (se 2 (by rfl) ⟨2352366, by rfl⟩ : syracuseStep 6272977 = 4704733) B4704733
theorem B1161179 : Blo 770335 1161179 := bstep (se 1 (by rfl) ⟨870884, by rfl⟩ : syracuseStep 1161179 = 1741769) B1741769
theorem B2603015 : Blo 770335 2603015 := bstep (se 1 (by rfl) ⟨1952261, by rfl⟩ : syracuseStep 2603015 = 3904523) B3904523
theorem B2603123 : Blo 770335 2603123 := bstep (se 1 (by rfl) ⟨1952342, by rfl⟩ : syracuseStep 2603123 = 3904685) B3904685
theorem B5880113 : Blo 770335 5880113 := bstep (se 2 (by rfl) ⟨2205042, by rfl⟩ : syracuseStep 5880113 = 4410085) B4410085
theorem B2931005 : Blo 770335 2931005 := bstep (se 3 (by rfl) ⟨549563, by rfl⟩ : syracuseStep 2931005 = 1099127) B1099127
theorem B2603393 : Blo 770335 2603393 := bstep (se 2 (by rfl) ⟨976272, by rfl⟩ : syracuseStep 2603393 = 1952545) B1952545
theorem B2931187 : Blo 770335 2931187 := bstep (se 1 (by rfl) ⟨2198390, by rfl⟩ : syracuseStep 2931187 = 4396781) B4396781
theorem B2505431 : Blo 770335 2505431 := bstep (se 1 (by rfl) ⟨1879073, by rfl⟩ : syracuseStep 2505431 = 3758147) B3758147
theorem B10566389 : Blo 770335 10566389 := bstep (se 5 (by rfl) ⟨495299, by rfl⟩ : syracuseStep 10566389 = 990599) B990599
theorem B867451 : Blo 770335 867451 := bstep (se 1 (by rfl) ⟨650588, by rfl⟩ : syracuseStep 867451 = 1301177) B1301177
theorem B2604203 : Blo 770335 2604203 := bstep (se 1 (by rfl) ⟨1953152, by rfl⟩ : syracuseStep 2604203 = 3906305) B3906305
theorem B867919 : Blo 770335 867919 := bstep (se 1 (by rfl) ⟨650939, by rfl⟩ : syracuseStep 867919 = 1301879) B1301879
theorem B2604743 : Blo 770335 2604743 := bstep (se 1 (by rfl) ⟨1953557, by rfl⟩ : syracuseStep 2604743 = 3907115) B3907115
theorem B2932433 : Blo 770335 2932433 := bstep (se 2 (by rfl) ⟨1099662, by rfl⟩ : syracuseStep 2932433 = 2199325) B2199325
theorem B868315 : Blo 770335 868315 := bstep (se 1 (by rfl) ⟨651236, by rfl⟩ : syracuseStep 868315 = 1302473) B1302473
theorem B5554183 : Blo 770335 5554183 := bstep (se 1 (by rfl) ⟨4165637, by rfl⟩ : syracuseStep 5554183 = 8331275) B8331275
theorem B1097977 : Blo 770335 1097977 := bstep (se 2 (by rfl) ⟨411741, by rfl⟩ : syracuseStep 1097977 = 823483) B823483
theorem B770343 : Blo 770335 770343 := bstep (se 1 (by rfl) ⟨577757, by rfl⟩ : syracuseStep 770343 = 1155515) B1155515
theorem B770383 : Blo 770335 770383 := bstep (se 1 (by rfl) ⟨577787, by rfl⟩ : syracuseStep 770383 = 1155575) B1155575
theorem B770399 : Blo 770335 770399 := bstep (se 1 (by rfl) ⟨577799, by rfl⟩ : syracuseStep 770399 = 1155599) B1155599
theorem B770427 : Blo 770335 770427 := bstep (se 1 (by rfl) ⟨577820, by rfl⟩ : syracuseStep 770427 = 1155641) B1155641
theorem B2933117 : Blo 770335 2933117 := bstep (se 3 (by rfl) ⟨549959, by rfl⟩ : syracuseStep 2933117 = 1099919) B1099919
theorem B1950095 : Blo 770335 1950095 := bstep (se 1 (by rfl) ⟨1462571, by rfl⟩ : syracuseStep 1950095 = 2925143) B2925143
theorem B770479 : Blo 770335 770479 := bstep (se 1 (by rfl) ⟨577859, by rfl⟩ : syracuseStep 770479 = 1155719) B1155719
theorem B868783 : Blo 770335 868783 := bstep (se 1 (by rfl) ⟨651587, by rfl⟩ : syracuseStep 868783 = 1303175) B1303175
theorem B770503 : Blo 770335 770503 := bstep (se 1 (by rfl) ⟨577877, by rfl⟩ : syracuseStep 770503 = 1155755) B1155755
theorem B11125201 : Blo 770335 11125201 := bstep (se 2 (by rfl) ⟨4171950, by rfl⟩ : syracuseStep 11125201 = 8343901) B8343901
theorem B770523 : Blo 770335 770523 := bstep (se 1 (by rfl) ⟨577892, by rfl⟩ : syracuseStep 770523 = 1155785) B1155785
theorem B2965997 : Blo 770335 2965997 := bstep (se 3 (by rfl) ⟨556124, by rfl⟩ : syracuseStep 2965997 = 1112249) B1112249
theorem B770599 : Blo 770335 770599 := bstep (se 1 (by rfl) ⟨577949, by rfl⟩ : syracuseStep 770599 = 1155899) B1155899
theorem B2605607 : Blo 770335 2605607 := bstep (se 1 (by rfl) ⟨1954205, by rfl⟩ : syracuseStep 2605607 = 3908411) B3908411
theorem B770639 : Blo 770335 770639 := bstep (se 1 (by rfl) ⟨577979, by rfl⟩ : syracuseStep 770639 = 1155959) B1155959
theorem B770655 : Blo 770335 770655 := bstep (se 1 (by rfl) ⟨577991, by rfl⟩ : syracuseStep 770655 = 1155983) B1155983
theorem B770683 : Blo 770335 770683 := bstep (se 1 (by rfl) ⟨578012, by rfl⟩ : syracuseStep 770683 = 1156025) B1156025
theorem B2605715 : Blo 770335 2605715 := bstep (se 1 (by rfl) ⟨1954286, by rfl⟩ : syracuseStep 2605715 = 3908573) B3908573
theorem B770735 : Blo 770335 770735 := bstep (se 1 (by rfl) ⟨578051, by rfl⟩ : syracuseStep 770735 = 1156103) B1156103
theorem B770759 : Blo 770335 770759 := bstep (se 1 (by rfl) ⟨578069, by rfl⟩ : syracuseStep 770759 = 1156139) B1156139
theorem B1950419 : Blo 770335 1950419 := bstep (se 1 (by rfl) ⟨1462814, by rfl⟩ : syracuseStep 1950419 = 2925629) B2925629
theorem B770779 : Blo 770335 770779 := bstep (se 1 (by rfl) ⟨578084, by rfl⟩ : syracuseStep 770779 = 1156169) B1156169
theorem B770855 : Blo 770335 770855 := bstep (se 1 (by rfl) ⟨578141, by rfl⟩ : syracuseStep 770855 = 1156283) B1156283
theorem B770895 : Blo 770335 770895 := bstep (se 1 (by rfl) ⟨578171, by rfl⟩ : syracuseStep 770895 = 1156343) B1156343
theorem B770911 : Blo 770335 770911 := bstep (se 1 (by rfl) ⟨578183, by rfl⟩ : syracuseStep 770911 = 1156367) B1156367
theorem B869215 : Blo 770335 869215 := bstep (se 1 (by rfl) ⟨651911, by rfl⟩ : syracuseStep 869215 = 1303823) B1303823
theorem B2605931 : Blo 770335 2605931 := bstep (se 1 (by rfl) ⟨1954448, by rfl⟩ : syracuseStep 2605931 = 3908897) B3908897
theorem B770939 : Blo 770335 770939 := bstep (se 1 (by rfl) ⟨578204, by rfl⟩ : syracuseStep 770939 = 1156409) B1156409
theorem B2605985 : Blo 770335 2605985 := bstep (se 2 (by rfl) ⟨977244, by rfl⟩ : syracuseStep 2605985 = 1954489) B1954489
theorem B770991 : Blo 770335 770991 := bstep (se 1 (by rfl) ⟨578243, by rfl⟩ : syracuseStep 770991 = 1156487) B1156487
theorem B771015 : Blo 770335 771015 := bstep (se 1 (by rfl) ⟨578261, by rfl⟩ : syracuseStep 771015 = 1156523) B1156523
theorem B771035 : Blo 770335 771035 := bstep (se 1 (by rfl) ⟨578276, by rfl⟩ : syracuseStep 771035 = 1156553) B1156553
theorem B11289619 : Blo 770335 11289619 := bstep (se 1 (by rfl) ⟨8467214, by rfl⟩ : syracuseStep 11289619 = 16934429) B16934429
theorem B771111 : Blo 770335 771111 := bstep (se 1 (by rfl) ⟨578333, by rfl⟩ : syracuseStep 771111 = 1156667) B1156667
theorem B771151 : Blo 770335 771151 := bstep (se 1 (by rfl) ⟨578363, by rfl⟩ : syracuseStep 771151 = 1156727) B1156727
theorem B771167 : Blo 770335 771167 := bstep (se 1 (by rfl) ⟨578375, by rfl⟩ : syracuseStep 771167 = 1156751) B1156751
theorem B771195 : Blo 770335 771195 := bstep (se 1 (by rfl) ⟨578396, by rfl⟩ : syracuseStep 771195 = 1156793) B1156793
theorem B771247 : Blo 770335 771247 := bstep (se 1 (by rfl) ⟨578435, by rfl⟩ : syracuseStep 771247 = 1156871) B1156871
theorem B771271 : Blo 770335 771271 := bstep (se 1 (by rfl) ⟨578453, by rfl⟩ : syracuseStep 771271 = 1156907) B1156907
theorem B869575 : Blo 770335 869575 := bstep (se 1 (by rfl) ⟨652181, by rfl⟩ : syracuseStep 869575 = 1304363) B1304363
theorem B771291 : Blo 770335 771291 := bstep (se 1 (by rfl) ⟨578468, by rfl⟩ : syracuseStep 771291 = 1156937) B1156937
theorem B771367 : Blo 770335 771367 := bstep (se 1 (by rfl) ⟨578525, by rfl⟩ : syracuseStep 771367 = 1157051) B1157051
theorem B771407 : Blo 770335 771407 := bstep (se 1 (by rfl) ⟨578555, by rfl⟩ : syracuseStep 771407 = 1157111) B1157111
theorem B2934103 : Blo 770335 2934103 := bstep (se 1 (by rfl) ⟨2200577, by rfl⟩ : syracuseStep 2934103 = 4401155) B4401155
theorem B771423 : Blo 770335 771423 := bstep (se 1 (by rfl) ⟨578567, by rfl⟩ : syracuseStep 771423 = 1157135) B1157135
theorem B771451 : Blo 770335 771451 := bstep (se 1 (by rfl) ⟨578588, by rfl⟩ : syracuseStep 771451 = 1157177) B1157177
theorem B771503 : Blo 770335 771503 := bstep (se 1 (by rfl) ⟨578627, by rfl⟩ : syracuseStep 771503 = 1157255) B1157255
theorem B771527 : Blo 770335 771527 := bstep (se 1 (by rfl) ⟨578645, by rfl⟩ : syracuseStep 771527 = 1157291) B1157291
theorem B771547 : Blo 770335 771547 := bstep (se 1 (by rfl) ⟨578660, by rfl⟩ : syracuseStep 771547 = 1157321) B1157321
theorem B11879921 : Blo 770335 11879921 := bstep (se 2 (by rfl) ⟨4454970, by rfl⟩ : syracuseStep 11879921 = 8909941) B8909941
theorem B2606579 : Blo 770335 2606579 := bstep (se 1 (by rfl) ⟨1954934, by rfl⟩ : syracuseStep 2606579 = 3909869) B3909869
theorem B2082343 : Blo 770335 2082343 := bstep (se 1 (by rfl) ⟨1561757, by rfl⟩ : syracuseStep 2082343 = 3123515) B3123515
theorem B771623 : Blo 770335 771623 := bstep (se 1 (by rfl) ⟨578717, by rfl⟩ : syracuseStep 771623 = 1157435) B1157435
theorem B771663 : Blo 770335 771663 := bstep (se 1 (by rfl) ⟨578747, by rfl⟩ : syracuseStep 771663 = 1157495) B1157495
theorem B771679 : Blo 770335 771679 := bstep (se 1 (by rfl) ⟨578759, by rfl⟩ : syracuseStep 771679 = 1157519) B1157519
theorem B771707 : Blo 770335 771707 := bstep (se 1 (by rfl) ⟨578780, by rfl⟩ : syracuseStep 771707 = 1157561) B1157561
theorem B2934407 : Blo 770335 2934407 := bstep (se 1 (by rfl) ⟨2200805, by rfl⟩ : syracuseStep 2934407 = 4401611) B4401611
theorem B771759 : Blo 770335 771759 := bstep (se 1 (by rfl) ⟨578819, by rfl⟩ : syracuseStep 771759 = 1157639) B1157639
theorem B771783 : Blo 770335 771783 := bstep (se 1 (by rfl) ⟨578837, by rfl⟩ : syracuseStep 771783 = 1157675) B1157675
theorem B771803 : Blo 770335 771803 := bstep (se 1 (by rfl) ⟨578852, by rfl⟩ : syracuseStep 771803 = 1157705) B1157705
theorem B2475805 : Blo 770335 2475805 := bstep (se 3 (by rfl) ⟨464213, by rfl⟩ : syracuseStep 2475805 = 928427) B928427
theorem B771879 : Blo 770335 771879 := bstep (se 1 (by rfl) ⟨578909, by rfl⟩ : syracuseStep 771879 = 1157819) B1157819
theorem B16893755 : Blo 770335 16893755 := bstep (se 1 (by rfl) ⟨12670316, by rfl⟩ : syracuseStep 16893755 = 25340633) B25340633
theorem B771919 : Blo 770335 771919 := bstep (se 1 (by rfl) ⟨578939, by rfl⟩ : syracuseStep 771919 = 1157879) B1157879
theorem B771935 : Blo 770335 771935 := bstep (se 1 (by rfl) ⟨578951, by rfl⟩ : syracuseStep 771935 = 1157903) B1157903
theorem B771963 : Blo 770335 771963 := bstep (se 1 (by rfl) ⟨578972, by rfl⟩ : syracuseStep 771963 = 1157945) B1157945
theorem B772015 : Blo 770335 772015 := bstep (se 1 (by rfl) ⟨579011, by rfl⟩ : syracuseStep 772015 = 1158023) B1158023
theorem B772039 : Blo 770335 772039 := bstep (se 1 (by rfl) ⟨579029, by rfl⟩ : syracuseStep 772039 = 1158059) B1158059
theorem B772059 : Blo 770335 772059 := bstep (se 1 (by rfl) ⟨579044, by rfl⟩ : syracuseStep 772059 = 1158089) B1158089
theorem B2607119 : Blo 770335 2607119 := bstep (se 1 (by rfl) ⟨1955339, by rfl⟩ : syracuseStep 2607119 = 3910679) B3910679
theorem B772135 : Blo 770335 772135 := bstep (se 1 (by rfl) ⟨579101, by rfl⟩ : syracuseStep 772135 = 1158203) B1158203
theorem B870439 : Blo 770335 870439 := bstep (se 1 (by rfl) ⟨652829, by rfl⟩ : syracuseStep 870439 = 1305659) B1305659
theorem B772175 : Blo 770335 772175 := bstep (se 1 (by rfl) ⟨579131, by rfl⟩ : syracuseStep 772175 = 1158263) B1158263
theorem B2934863 : Blo 770335 2934863 := bstep (se 1 (by rfl) ⟨2201147, by rfl⟩ : syracuseStep 2934863 = 4402295) B4402295
theorem B772191 : Blo 770335 772191 := bstep (se 1 (by rfl) ⟨579143, by rfl⟩ : syracuseStep 772191 = 1158287) B1158287
theorem B772219 : Blo 770335 772219 := bstep (se 1 (by rfl) ⟨579164, by rfl⟩ : syracuseStep 772219 = 1158329) B1158329
theorem B772271 : Blo 770335 772271 := bstep (se 1 (by rfl) ⟨579203, by rfl⟩ : syracuseStep 772271 = 1158407) B1158407
theorem B772295 : Blo 770335 772295 := bstep (se 1 (by rfl) ⟨579221, by rfl⟩ : syracuseStep 772295 = 1158443) B1158443
theorem B772315 : Blo 770335 772315 := bstep (se 1 (by rfl) ⟨579236, by rfl⟩ : syracuseStep 772315 = 1158473) B1158473
theorem B772391 : Blo 770335 772391 := bstep (se 1 (by rfl) ⟨579293, by rfl⟩ : syracuseStep 772391 = 1158587) B1158587
theorem B772431 : Blo 770335 772431 := bstep (se 1 (by rfl) ⟨579323, by rfl⟩ : syracuseStep 772431 = 1158647) B1158647
theorem B14829911 : Blo 770335 14829911 := bstep (se 1 (by rfl) ⟨11122433, by rfl⟩ : syracuseStep 14829911 = 22244867) B22244867
theorem B772447 : Blo 770335 772447 := bstep (se 1 (by rfl) ⟨579335, by rfl⟩ : syracuseStep 772447 = 1158671) B1158671
theorem B772475 : Blo 770335 772475 := bstep (se 1 (by rfl) ⟨579356, by rfl⟩ : syracuseStep 772475 = 1158713) B1158713
theorem B772527 : Blo 770335 772527 := bstep (se 1 (by rfl) ⟨579395, by rfl⟩ : syracuseStep 772527 = 1158791) B1158791
theorem B36161977 : Blo 770335 36161977 := bstep (se 2 (by rfl) ⟨13560741, by rfl⟩ : syracuseStep 36161977 = 27121483) B27121483
theorem B772551 : Blo 770335 772551 := bstep (se 1 (by rfl) ⟨579413, by rfl⟩ : syracuseStep 772551 = 1158827) B1158827
theorem B772571 : Blo 770335 772571 := bstep (se 1 (by rfl) ⟨579428, by rfl⟩ : syracuseStep 772571 = 1158857) B1158857
theorem B772647 : Blo 770335 772647 := bstep (se 1 (by rfl) ⟨579485, by rfl⟩ : syracuseStep 772647 = 1158971) B1158971
theorem B772687 : Blo 770335 772687 := bstep (se 1 (by rfl) ⟨579515, by rfl⟩ : syracuseStep 772687 = 1159031) B1159031
theorem B772703 : Blo 770335 772703 := bstep (se 1 (by rfl) ⟨579527, by rfl⟩ : syracuseStep 772703 = 1159055) B1159055
theorem B2607713 : Blo 770335 2607713 := bstep (se 2 (by rfl) ⟨977892, by rfl⟩ : syracuseStep 2607713 = 1955785) B1955785
theorem B772731 : Blo 770335 772731 := bstep (se 1 (by rfl) ⟨579548, by rfl⟩ : syracuseStep 772731 = 1159097) B1159097
theorem B772783 : Blo 770335 772783 := bstep (se 1 (by rfl) ⟨579587, by rfl⟩ : syracuseStep 772783 = 1159175) B1159175
theorem B772807 : Blo 770335 772807 := bstep (se 1 (by rfl) ⟨579605, by rfl⟩ : syracuseStep 772807 = 1159211) B1159211
theorem B772827 : Blo 770335 772827 := bstep (se 1 (by rfl) ⟨579620, by rfl⟩ : syracuseStep 772827 = 1159241) B1159241
theorem B7424797 : Blo 770335 7424797 := bstep (se 3 (by rfl) ⟨1392149, by rfl⟩ : syracuseStep 7424797 = 2784299) B2784299
theorem B772903 : Blo 770335 772903 := bstep (se 1 (by rfl) ⟨579677, by rfl⟩ : syracuseStep 772903 = 1159355) B1159355
theorem B772943 : Blo 770335 772943 := bstep (se 1 (by rfl) ⟨579707, by rfl⟩ : syracuseStep 772943 = 1159415) B1159415
theorem B772959 : Blo 770335 772959 := bstep (se 1 (by rfl) ⟨579719, by rfl⟩ : syracuseStep 772959 = 1159439) B1159439
theorem B772987 : Blo 770335 772987 := bstep (se 1 (by rfl) ⟨579740, by rfl⟩ : syracuseStep 772987 = 1159481) B1159481
theorem B1952687 : Blo 770335 1952687 := bstep (se 1 (by rfl) ⟨1464515, by rfl⟩ : syracuseStep 1952687 = 2929031) B2929031
theorem B773039 : Blo 770335 773039 := bstep (se 1 (by rfl) ⟨579779, by rfl⟩ : syracuseStep 773039 = 1159559) B1159559
theorem B773063 : Blo 770335 773063 := bstep (se 1 (by rfl) ⟨579797, by rfl⟩ : syracuseStep 773063 = 1159595) B1159595
theorem B773083 : Blo 770335 773083 := bstep (se 1 (by rfl) ⟨579812, by rfl⟩ : syracuseStep 773083 = 1159625) B1159625
theorem B2968595 : Blo 770335 2968595 := bstep (se 1 (by rfl) ⟨2226446, by rfl⟩ : syracuseStep 2968595 = 4452893) B4452893
theorem B773159 : Blo 770335 773159 := bstep (se 1 (by rfl) ⟨579869, by rfl⟩ : syracuseStep 773159 = 1159739) B1159739
theorem B2935865 : Blo 770335 2935865 := bstep (se 2 (by rfl) ⟨1100949, by rfl⟩ : syracuseStep 2935865 = 2201899) B2201899
theorem B773199 : Blo 770335 773199 := bstep (se 1 (by rfl) ⟨579899, by rfl⟩ : syracuseStep 773199 = 1159799) B1159799
theorem B773215 : Blo 770335 773215 := bstep (se 1 (by rfl) ⟨579911, by rfl⟩ : syracuseStep 773215 = 1159823) B1159823
theorem B773243 : Blo 770335 773243 := bstep (se 1 (by rfl) ⟨579932, by rfl⟩ : syracuseStep 773243 = 1159865) B1159865
theorem B773295 : Blo 770335 773295 := bstep (se 1 (by rfl) ⟨579971, by rfl⟩ : syracuseStep 773295 = 1159943) B1159943
theorem B773319 : Blo 770335 773319 := bstep (se 1 (by rfl) ⟨579989, by rfl⟩ : syracuseStep 773319 = 1159979) B1159979
theorem B773339 : Blo 770335 773339 := bstep (se 1 (by rfl) ⟨580004, by rfl⟩ : syracuseStep 773339 = 1160009) B1160009
theorem B9882917 : Blo 770335 9882917 := bstep (se 4 (by rfl) ⟨926523, by rfl⟩ : syracuseStep 9882917 = 1853047) B1853047
theorem B773415 : Blo 770335 773415 := bstep (se 1 (by rfl) ⟨580061, by rfl⟩ : syracuseStep 773415 = 1160123) B1160123
theorem B773455 : Blo 770335 773455 := bstep (se 1 (by rfl) ⟨580091, by rfl⟩ : syracuseStep 773455 = 1160183) B1160183
theorem B773471 : Blo 770335 773471 := bstep (se 1 (by rfl) ⟨580103, by rfl⟩ : syracuseStep 773471 = 1160207) B1160207
theorem B773499 : Blo 770335 773499 := bstep (se 1 (by rfl) ⟨580124, by rfl⟩ : syracuseStep 773499 = 1160249) B1160249
theorem B1789327 : Blo 770335 1789327 := bstep (se 1 (by rfl) ⟨1341995, by rfl⟩ : syracuseStep 1789327 = 2683991) B2683991
theorem B773551 : Blo 770335 773551 := bstep (se 1 (by rfl) ⟨580163, by rfl⟩ : syracuseStep 773551 = 1160327) B1160327
theorem B773575 : Blo 770335 773575 := bstep (se 1 (by rfl) ⟨580181, by rfl⟩ : syracuseStep 773575 = 1160363) B1160363
theorem B773595 : Blo 770335 773595 := bstep (se 1 (by rfl) ⟨580196, by rfl⟩ : syracuseStep 773595 = 1160393) B1160393
theorem B60182003 : Blo 770335 60182003 := bstep (se 1 (by rfl) ⟨45136502, by rfl⟩ : syracuseStep 60182003 = 90273005) B90273005
theorem B1953305 : Blo 770335 1953305 := bstep (se 2 (by rfl) ⟨732489, by rfl⟩ : syracuseStep 1953305 = 1464979) B1464979
theorem B773671 : Blo 770335 773671 := bstep (se 1 (by rfl) ⟨580253, by rfl⟩ : syracuseStep 773671 = 1160507) B1160507
theorem B773711 : Blo 770335 773711 := bstep (se 1 (by rfl) ⟨580283, by rfl⟩ : syracuseStep 773711 = 1160567) B1160567
theorem B773727 : Blo 770335 773727 := bstep (se 1 (by rfl) ⟨580295, by rfl⟩ : syracuseStep 773727 = 1160591) B1160591
theorem B773755 : Blo 770335 773755 := bstep (se 1 (by rfl) ⟨580316, by rfl⟩ : syracuseStep 773755 = 1160633) B1160633
theorem B773807 : Blo 770335 773807 := bstep (se 1 (by rfl) ⟨580355, by rfl⟩ : syracuseStep 773807 = 1160711) B1160711
theorem B2477753 : Blo 770335 2477753 := bstep (se 2 (by rfl) ⟨929157, by rfl⟩ : syracuseStep 2477753 = 1858315) B1858315
theorem B2936519 : Blo 770335 2936519 := bstep (se 1 (by rfl) ⟨2202389, by rfl⟩ : syracuseStep 2936519 = 4404779) B4404779
theorem B773831 : Blo 770335 773831 := bstep (se 1 (by rfl) ⟨580373, by rfl⟩ : syracuseStep 773831 = 1160747) B1160747
theorem B773851 : Blo 770335 773851 := bstep (se 1 (by rfl) ⟨580388, by rfl⟩ : syracuseStep 773851 = 1160777) B1160777
theorem B773927 : Blo 770335 773927 := bstep (se 1 (by rfl) ⟨580445, by rfl⟩ : syracuseStep 773927 = 1160891) B1160891
theorem B773967 : Blo 770335 773967 := bstep (se 1 (by rfl) ⟨580475, by rfl⟩ : syracuseStep 773967 = 1160951) B1160951
theorem B773983 : Blo 770335 773983 := bstep (se 1 (by rfl) ⟨580487, by rfl⟩ : syracuseStep 773983 = 1160975) B1160975
theorem B774011 : Blo 770335 774011 := bstep (se 1 (by rfl) ⟨580508, by rfl⟩ : syracuseStep 774011 = 1161017) B1161017
theorem B2969519 : Blo 770335 2969519 := bstep (se 1 (by rfl) ⟨2227139, by rfl⟩ : syracuseStep 2969519 = 4454279) B4454279
theorem B774063 : Blo 770335 774063 := bstep (se 1 (by rfl) ⟨580547, by rfl⟩ : syracuseStep 774063 = 1161095) B1161095
theorem B774087 : Blo 770335 774087 := bstep (se 1 (by rfl) ⟨580565, by rfl⟩ : syracuseStep 774087 = 1161131) B1161131
theorem B774107 : Blo 770335 774107 := bstep (se 1 (by rfl) ⟨580580, by rfl⟩ : syracuseStep 774107 = 1161161) B1161161
theorem B2609171 : Blo 770335 2609171 := bstep (se 1 (by rfl) ⟨1956878, by rfl⟩ : syracuseStep 2609171 = 3913757) B3913757
theorem B774183 : Blo 770335 774183 := bstep (se 1 (by rfl) ⟨580637, by rfl⟩ : syracuseStep 774183 = 1161275) B1161275
theorem B774223 : Blo 770335 774223 := bstep (se 1 (by rfl) ⟨580667, by rfl⟩ : syracuseStep 774223 = 1161335) B1161335
theorem B774239 : Blo 770335 774239 := bstep (se 1 (by rfl) ⟨580679, by rfl⟩ : syracuseStep 774239 = 1161359) B1161359
theorem B774267 : Blo 770335 774267 := bstep (se 1 (by rfl) ⟨580700, by rfl⟩ : syracuseStep 774267 = 1161401) B1161401
theorem B774319 : Blo 770335 774319 := bstep (se 1 (by rfl) ⟨580739, by rfl⟩ : syracuseStep 774319 = 1161479) B1161479
theorem B2609495 : Blo 770335 2609495 := bstep (se 1 (by rfl) ⟨1957121, by rfl⟩ : syracuseStep 2609495 = 3914243) B3914243
theorem B9916951 : Blo 770335 9916951 := bstep (se 1 (by rfl) ⟨7437713, by rfl⟩ : syracuseStep 9916951 = 14875427) B14875427
theorem B1856123 : Blo 770335 1856123 := bstep (se 1 (by rfl) ⟨1392092, by rfl⟩ : syracuseStep 1856123 = 2784185) B2784185
theorem B2937491 : Blo 770335 2937491 := bstep (se 1 (by rfl) ⟨2203118, by rfl⟩ : syracuseStep 2937491 = 4406237) B4406237
theorem B5853869 : Blo 770335 5853869 := bstep (se 3 (by rfl) ⟨1097600, by rfl⟩ : syracuseStep 5853869 = 2195201) B2195201
theorem B5952211 : Blo 770335 5952211 := bstep (se 1 (by rfl) ⟨4464158, by rfl⟩ : syracuseStep 5952211 = 8928317) B8928317
theorem B3298475 : Blo 770335 3298475 := bstep (se 1 (by rfl) ⟨2473856, by rfl⟩ : syracuseStep 3298475 = 4947713) B4947713
theorem B2610575 : Blo 770335 2610575 := bstep (se 1 (by rfl) ⟨1957931, by rfl⟩ : syracuseStep 2610575 = 3915863) B3915863
theorem B1562017 : Blo 770335 1562017 := bstep (se 2 (by rfl) ⟨585756, by rfl⟩ : syracuseStep 1562017 = 1171513) B1171513
theorem B1463771 : Blo 770335 1463771 := bstep (se 1 (by rfl) ⟨1097828, by rfl⟩ : syracuseStep 1463771 = 2195657) B2195657
theorem B7427645 : Blo 770335 7427645 := bstep (se 3 (by rfl) ⟨1392683, by rfl⟩ : syracuseStep 7427645 = 2785367) B2785367
theorem B2479751 : Blo 770335 2479751 := bstep (se 1 (by rfl) ⟨1859813, by rfl⟩ : syracuseStep 2479751 = 3719627) B3719627
theorem B1464007 : Blo 770335 1464007 := bstep (se 1 (by rfl) ⟨1098005, by rfl⟩ : syracuseStep 1464007 = 2196011) B2196011
theorem B2610899 : Blo 770335 2610899 := bstep (se 1 (by rfl) ⟨1958174, by rfl⟩ : syracuseStep 2610899 = 3916349) B3916349
theorem B1857239 : Blo 770335 1857239 := bstep (se 1 (by rfl) ⟨1392929, by rfl⟩ : syracuseStep 1857239 = 2785859) B2785859
theorem B3135191 : Blo 770335 3135191 := bstep (se 1 (by rfl) ⟨2351393, by rfl⟩ : syracuseStep 3135191 = 4702787) B4702787
theorem B19748609 : Blo 770335 19748609 := bstep (se 2 (by rfl) ⟨7405728, by rfl⟩ : syracuseStep 19748609 = 14811457) B14811457
theorem B1300367 : Blo 770335 1300367 := bstep (se 1 (by rfl) ⟨975275, by rfl⟩ : syracuseStep 1300367 = 1950551) B1950551
theorem B1955897 : Blo 770335 1955897 := bstep (se 2 (by rfl) ⟨733461, by rfl⟩ : syracuseStep 1955897 = 1466923) B1466923
theorem B1300603 : Blo 770335 1300603 := bstep (se 1 (by rfl) ⟨975452, by rfl⟩ : syracuseStep 1300603 = 1950905) B1950905
theorem B9394481 : Blo 770335 9394481 := bstep (se 2 (by rfl) ⟨3522930, by rfl⟩ : syracuseStep 9394481 = 7045861) B7045861
theorem B11917721 : Blo 770335 11917721 := bstep (se 2 (by rfl) ⟨4469145, by rfl⟩ : syracuseStep 11917721 = 8938291) B8938291
theorem B1235513 : Blo 770335 1235513 := bstep (se 2 (by rfl) ⟨463317, by rfl⟩ : syracuseStep 1235513 = 926635) B926635
theorem B2612087 : Blo 770335 2612087 := bstep (se 1 (by rfl) ⟨1959065, by rfl⟩ : syracuseStep 2612087 = 3918131) B3918131
theorem B4938641 : Blo 770335 4938641 := bstep (se 2 (by rfl) ⟨1851990, by rfl⟩ : syracuseStep 4938641 = 3703981) B3703981
theorem B1301467 : Blo 770335 1301467 := bstep (se 1 (by rfl) ⟨976100, by rfl⟩ : syracuseStep 1301467 = 1952201) B1952201
theorem B5856299 : Blo 770335 5856299 := bstep (se 1 (by rfl) ⟨4392224, by rfl⟩ : syracuseStep 5856299 = 8784449) B8784449
theorem B2612303 : Blo 770335 2612303 := bstep (se 1 (by rfl) ⟨1959227, by rfl⟩ : syracuseStep 2612303 = 3918455) B3918455
theorem B2088335 : Blo 770335 2088335 := bstep (se 1 (by rfl) ⟨1566251, by rfl⟩ : syracuseStep 2088335 = 3132503) B3132503
theorem B2612681 : Blo 770335 2612681 := bstep (se 2 (by rfl) ⟨979755, by rfl⟩ : syracuseStep 2612681 = 1959511) B1959511
theorem B3300851 : Blo 770335 3300851 := bstep (se 1 (by rfl) ⟨2475638, by rfl⟩ : syracuseStep 3300851 = 4951277) B4951277
theorem B1236487 : Blo 770335 1236487 := bstep (se 1 (by rfl) ⟨927365, by rfl⟩ : syracuseStep 1236487 = 1854731) B1854731
theorem B1957385 : Blo 770335 1957385 := bstep (se 2 (by rfl) ⟨734019, by rfl⟩ : syracuseStep 1957385 = 1468039) B1468039
theorem B1465913 : Blo 770335 1465913 := bstep (se 2 (by rfl) ⟨549717, by rfl⟩ : syracuseStep 1465913 = 1099435) B1099435
theorem B1302095 : Blo 770335 1302095 := bstep (se 1 (by rfl) ⟨976571, by rfl⟩ : syracuseStep 1302095 = 1953143) B1953143
theorem B3301003 : Blo 770335 3301003 := bstep (se 1 (by rfl) ⟨2475752, by rfl⟩ : syracuseStep 3301003 = 4951505) B4951505
theorem B4579031 : Blo 770335 4579031 := bstep (se 1 (by rfl) ⟨3434273, by rfl⟩ : syracuseStep 4579031 = 6868547) B6868547
theorem B2612951 : Blo 770335 2612951 := bstep (se 1 (by rfl) ⟨1959713, by rfl⟩ : syracuseStep 2612951 = 3919427) B3919427
theorem B3137399 : Blo 770335 3137399 := bstep (se 1 (by rfl) ⟨2353049, by rfl⟩ : syracuseStep 3137399 = 4706099) B4706099
theorem B1466255 : Blo 770335 1466255 := bstep (se 1 (by rfl) ⟨1099691, by rfl⟩ : syracuseStep 1466255 = 2199383) B2199383
theorem B2613167 : Blo 770335 2613167 := bstep (se 1 (by rfl) ⟨1959875, by rfl⟩ : syracuseStep 2613167 = 3919751) B3919751
theorem B2974013 : Blo 770335 2974013 := bstep (se 3 (by rfl) ⟨557627, by rfl⟩ : syracuseStep 2974013 = 1115255) B1115255
theorem B1302959 : Blo 770335 1302959 := bstep (se 1 (by rfl) ⟨977219, by rfl⟩ : syracuseStep 1302959 = 1954439) B1954439
theorem B1860121 : Blo 770335 1860121 := bstep (se 2 (by rfl) ⟨697545, by rfl⟩ : syracuseStep 1860121 = 1395091) B1395091
theorem B2351713 : Blo 770335 2351713 := bstep (se 2 (by rfl) ⟨881892, by rfl⟩ : syracuseStep 2351713 = 1763785) B1763785
theorem B1958539 : Blo 770335 1958539 := bstep (se 1 (by rfl) ⟨1468904, by rfl⟩ : syracuseStep 1958539 = 2937809) B2937809
theorem B975559 : Blo 770335 975559 := bstep (se 1 (by rfl) ⟨731669, by rfl⟩ : syracuseStep 975559 = 1463339) B1463339
theorem B1303391 : Blo 770335 1303391 := bstep (se 1 (by rfl) ⟨977543, by rfl⟩ : syracuseStep 1303391 = 1955087) B1955087
theorem B1958843 : Blo 770335 1958843 := bstep (se 1 (by rfl) ⟨1469132, by rfl⟩ : syracuseStep 1958843 = 2938265) B2938265
theorem B27452363 : Blo 770335 27452363 := bstep (se 1 (by rfl) ⟨20589272, by rfl⟩ : syracuseStep 27452363 = 41178545) B41178545
theorem B1238095 : Blo 770335 1238095 := bstep (se 1 (by rfl) ⟨928571, by rfl⟩ : syracuseStep 1238095 = 1857143) B1857143
theorem B1303951 : Blo 770335 1303951 := bstep (se 1 (by rfl) ⟨977963, by rfl⟩ : syracuseStep 1303951 = 1955927) B1955927
theorem B976303 : Blo 770335 976303 := bstep (se 1 (by rfl) ⟨732227, by rfl⟩ : syracuseStep 976303 = 1464455) B1464455
theorem B1238537 : Blo 770335 1238537 := bstep (se 2 (by rfl) ⟨464451, by rfl⟩ : syracuseStep 1238537 = 928903) B928903
theorem B4449937 : Blo 770335 4449937 := bstep (se 2 (by rfl) ⟨1668726, by rfl⟩ : syracuseStep 4449937 = 3337453) B3337453
theorem B1959623 : Blo 770335 1959623 := bstep (se 1 (by rfl) ⟨1469717, by rfl⟩ : syracuseStep 1959623 = 2939435) B2939435
theorem B1468115 : Blo 770335 1468115 := bstep (se 1 (by rfl) ⟨1101086, by rfl⟩ : syracuseStep 1468115 = 2202173) B2202173
theorem B1959673 : Blo 770335 1959673 := bstep (se 2 (by rfl) ⟨734877, by rfl⟩ : syracuseStep 1959673 = 1469755) B1469755
theorem B1468343 : Blo 770335 1468343 := bstep (se 1 (by rfl) ⟨1101257, by rfl⟩ : syracuseStep 1468343 = 2202515) B2202515
theorem B1304633 : Blo 770335 1304633 := bstep (se 2 (by rfl) ⟨489237, by rfl⟩ : syracuseStep 1304633 = 978475) B978475
theorem B14838065 : Blo 770335 14838065 := bstep (se 2 (by rfl) ⟨5564274, by rfl⟩ : syracuseStep 14838065 = 11128549) B11128549
theorem B1239479 : Blo 770335 1239479 := bstep (se 1 (by rfl) ⟨929609, by rfl⟩ : syracuseStep 1239479 = 1859219) B1859219
theorem B977447 : Blo 770335 977447 := bstep (se 1 (by rfl) ⟨733085, by rfl⟩ : syracuseStep 977447 = 1466171) B1466171
theorem B3304147 : Blo 770335 3304147 := bstep (se 1 (by rfl) ⟨2478110, by rfl⟩ : syracuseStep 3304147 = 4956221) B4956221
theorem B1305335 : Blo 770335 1305335 := bstep (se 1 (by rfl) ⟨979001, by rfl⟩ : syracuseStep 1305335 = 1958003) B1958003
theorem B1239799 : Blo 770335 1239799 := bstep (se 1 (by rfl) ⟨929849, by rfl⟩ : syracuseStep 1239799 = 1859699) B1859699
theorem B977771 : Blo 770335 977771 := bstep (se 1 (by rfl) ⟨733328, by rfl⟩ : syracuseStep 977771 = 1466657) B1466657
theorem B9890707 : Blo 770335 9890707 := bstep (se 1 (by rfl) ⟨7418030, by rfl⟩ : syracuseStep 9890707 = 14836061) B14836061
theorem B1469497 : Blo 770335 1469497 := bstep (se 2 (by rfl) ⟨551061, by rfl⟩ : syracuseStep 1469497 = 1102123) B1102123
theorem B1305679 : Blo 770335 1305679 := bstep (se 1 (by rfl) ⟨979259, by rfl⟩ : syracuseStep 1305679 = 1958519) B1958519
theorem B1305929 : Blo 770335 1305929 := bstep (se 2 (by rfl) ⟨489723, by rfl⟩ : syracuseStep 1305929 = 979447) B979447
theorem B1764713 : Blo 770335 1764713 := bstep (se 2 (by rfl) ⟨661767, by rfl⟩ : syracuseStep 1764713 = 1323535) B1323535
theorem B1469801 : Blo 770335 1469801 := bstep (se 2 (by rfl) ⟨551175, by rfl⟩ : syracuseStep 1469801 = 1102351) B1102351
theorem B1469839 : Blo 770335 1469839 := bstep (se 1 (by rfl) ⟨1102379, by rfl⟩ : syracuseStep 1469839 = 2204759) B2204759
theorem B1306361 : Blo 770335 1306361 := bstep (se 2 (by rfl) ⟨489885, by rfl⟩ : syracuseStep 1306361 = 979771) B979771
theorem B3567521 : Blo 770335 3567521 := bstep (se 2 (by rfl) ⟨1337820, by rfl⟩ : syracuseStep 3567521 = 2675641) B2675641
theorem B3305377 : Blo 770335 3305377 := bstep (se 2 (by rfl) ⟨1239516, by rfl⟩ : syracuseStep 3305377 = 2479033) B2479033
theorem B1306543 : Blo 770335 1306543 := bstep (se 1 (by rfl) ⟨979907, by rfl⟩ : syracuseStep 1306543 = 1959815) B1959815
theorem B1306631 : Blo 770335 1306631 := bstep (se 1 (by rfl) ⟨979973, by rfl⟩ : syracuseStep 1306631 = 1959947) B1959947
theorem B979067 : Blo 770335 979067 := bstep (se 1 (by rfl) ⟨734300, by rfl⟩ : syracuseStep 979067 = 1468601) B1468601
theorem B45674675 : Blo 770335 45674675 := bstep (se 1 (by rfl) ⟨34256006, by rfl⟩ : syracuseStep 45674675 = 68512013) B68512013
theorem B2781677 : Blo 770335 2781677 := bstep (se 3 (by rfl) ⟨521564, by rfl⟩ : syracuseStep 2781677 = 1043129) B1043129
theorem B2782025 : Blo 770335 2782025 := bstep (se 2 (by rfl) ⟨1043259, by rfl⟩ : syracuseStep 2782025 = 2086519) B2086519
theorem B1733471 : Blo 770335 1733471 := bstep (se 1 (by rfl) ⟨1300103, by rfl⟩ : syracuseStep 1733471 = 2600207) B2600207
theorem B5272577 : Blo 770335 5272577 := bstep (se 2 (by rfl) ⟨1977216, by rfl⟩ : syracuseStep 5272577 = 3954433) B3954433
theorem B1733651 : Blo 770335 1733651 := bstep (se 1 (by rfl) ⟨1300238, by rfl⟩ : syracuseStep 1733651 = 2600477) B2600477
theorem B4945049 : Blo 770335 4945049 := bstep (se 2 (by rfl) ⟨1854393, by rfl⟩ : syracuseStep 4945049 = 3708787) B3708787
theorem B14087339 : Blo 770335 14087339 := bstep (se 1 (by rfl) ⟨10565504, by rfl⟩ : syracuseStep 14087339 = 21131009) B21131009
theorem B1733993 : Blo 770335 1733993 := bstep (se 2 (by rfl) ⟨650247, by rfl⟩ : syracuseStep 1733993 = 1300495) B1300495
theorem B3307223 : Blo 770335 3307223 := bstep (se 1 (by rfl) ⟨2480417, by rfl⟩ : syracuseStep 3307223 = 4960835) B4960835
theorem B1734587 : Blo 770335 1734587 := bstep (se 1 (by rfl) ⟨1300940, by rfl⟩ : syracuseStep 1734587 = 2601881) B2601881
theorem B1734713 : Blo 770335 1734713 := bstep (se 2 (by rfl) ⟨650517, by rfl⟩ : syracuseStep 1734713 = 1301035) B1301035
theorem B17824033 : Blo 770335 17824033 := bstep (se 2 (by rfl) ⟨6684012, by rfl⟩ : syracuseStep 17824033 = 13368025) B13368025
theorem B1735055 : Blo 770335 1735055 := bstep (se 1 (by rfl) ⟨1301291, by rfl⟩ : syracuseStep 1735055 = 2602583) B2602583
theorem B1735379 : Blo 770335 1735379 := bstep (se 1 (by rfl) ⟨1301534, by rfl⟩ : syracuseStep 1735379 = 2603069) B2603069
theorem B15858767 : Blo 770335 15858767 := bstep (se 1 (by rfl) ⟨11894075, by rfl⟩ : syracuseStep 15858767 = 23788151) B23788151
theorem B5865047 : Blo 770335 5865047 := bstep (se 1 (by rfl) ⟨4398785, by rfl⟩ : syracuseStep 5865047 = 8797571) B8797571
theorem B1736315 : Blo 770335 1736315 := bstep (se 1 (by rfl) ⟨1302236, by rfl⟩ : syracuseStep 1736315 = 2604473) B2604473
theorem B8781533 : Blo 770335 8781533 := bstep (se 3 (by rfl) ⟨1646537, by rfl⟩ : syracuseStep 8781533 = 3293075) B3293075
theorem B1736441 : Blo 770335 1736441 := bstep (se 2 (by rfl) ⟨651165, by rfl⟩ : syracuseStep 1736441 = 1302331) B1302331
theorem B7405577 : Blo 770335 7405577 := bstep (se 2 (by rfl) ⟨2777091, by rfl⟩ : syracuseStep 7405577 = 5554183) B5554183
theorem B56361041 : Blo 770335 56361041 := bstep (se 2 (by rfl) ⟨21135390, by rfl⟩ : syracuseStep 56361041 = 42270781) B42270781
theorem B1737071 : Blo 770335 1737071 := bstep (se 1 (by rfl) ⟨1302803, by rfl⟩ : syracuseStep 1737071 = 2605607) B2605607
theorem B1737143 : Blo 770335 1737143 := bstep (se 1 (by rfl) ⟨1302857, by rfl⟩ : syracuseStep 1737143 = 2605715) B2605715
theorem B1737287 : Blo 770335 1737287 := bstep (se 1 (by rfl) ⟨1302965, by rfl⟩ : syracuseStep 1737287 = 2605931) B2605931
theorem B1737323 : Blo 770335 1737323 := bstep (se 1 (by rfl) ⟨1302992, by rfl⟩ : syracuseStep 1737323 = 2605985) B2605985
theorem B1737719 : Blo 770335 1737719 := bstep (se 1 (by rfl) ⟨1303289, by rfl⟩ : syracuseStep 1737719 = 2606579) B2606579
theorem B3900473 : Blo 770335 3900473 := bstep (se 2 (by rfl) ⟨1462677, by rfl⟩ : syracuseStep 3900473 = 2925355) B2925355
theorem B8782991 : Blo 770335 8782991 := bstep (se 1 (by rfl) ⟨6587243, by rfl⟩ : syracuseStep 8782991 = 13174487) B13174487
theorem B1738079 : Blo 770335 1738079 := bstep (se 1 (by rfl) ⟨1303559, by rfl⟩ : syracuseStep 1738079 = 2607119) B2607119
theorem B95061509 : Blo 770335 95061509 := bstep (se 4 (by rfl) ⟨8912016, by rfl⟩ : syracuseStep 95061509 = 17824033) B17824033
theorem B1738475 : Blo 770335 1738475 := bstep (se 1 (by rfl) ⟨1303856, by rfl⟩ : syracuseStep 1738475 = 2607713) B2607713
theorem B1738601 : Blo 770335 1738601 := bstep (se 2 (by rfl) ⟨651975, by rfl⟩ : syracuseStep 1738601 = 1303951) B1303951
theorem B5933249 : Blo 770335 5933249 := bstep (se 2 (by rfl) ⟨2224968, by rfl⟩ : syracuseStep 5933249 = 4449937) B4449937
theorem B6588611 : Blo 770335 6588611 := bstep (se 1 (by rfl) ⟨4941458, by rfl⟩ : syracuseStep 6588611 = 9882917) B9882917
theorem B73206301 : Blo 770335 73206301 := bstep (se 3 (by rfl) ⟨13726181, by rfl⟩ : syracuseStep 73206301 = 27452363) B27452363
theorem B1739447 : Blo 770335 1739447 := bstep (se 1 (by rfl) ⟨1304585, by rfl⟩ : syracuseStep 1739447 = 2609171) B2609171
theorem B7539479 : Blo 770335 7539479 := bstep (se 1 (by rfl) ⟨5654609, by rfl⟩ : syracuseStep 7539479 = 11309219) B11309219
theorem B1739663 : Blo 770335 1739663 := bstep (se 1 (by rfl) ⟨1304747, by rfl⟩ : syracuseStep 1739663 = 2609495) B2609495
theorem B3902579 : Blo 770335 3902579 := bstep (se 1 (by rfl) ⟨2926934, by rfl⟩ : syracuseStep 3902579 = 5853869) B5853869
theorem B101682377 : Blo 770335 101682377 := bstep (se 2 (by rfl) ⟨38130891, by rfl⟩ : syracuseStep 101682377 = 76261783) B76261783
theorem B7441793 : Blo 770335 7441793 := bstep (se 2 (by rfl) ⟨2790672, by rfl⟩ : syracuseStep 7441793 = 5581345) B5581345
theorem B2198983 : Blo 770335 2198983 := bstep (se 1 (by rfl) ⟨1649237, by rfl⟩ : syracuseStep 2198983 = 3298475) B3298475
theorem B8359433 : Blo 770335 8359433 := bstep (se 2 (by rfl) ⟨3134787, by rfl⟩ : syracuseStep 8359433 = 6269575) B6269575
theorem B1740383 : Blo 770335 1740383 := bstep (se 1 (by rfl) ⟨1305287, by rfl⟩ : syracuseStep 1740383 = 2610575) B2610575
theorem B3968621 : Blo 770335 3968621 := bstep (se 3 (by rfl) ⟨744116, by rfl⟩ : syracuseStep 3968621 = 1488233) B1488233
theorem B9899729 : Blo 770335 9899729 := bstep (se 2 (by rfl) ⟨3712398, by rfl⟩ : syracuseStep 9899729 = 7424797) B7424797
theorem B4951763 : Blo 770335 4951763 := bstep (se 1 (by rfl) ⟨3713822, by rfl⟩ : syracuseStep 4951763 = 7427645) B7427645
theorem B1740599 : Blo 770335 1740599 := bstep (se 1 (by rfl) ⟨1305449, by rfl⟩ : syracuseStep 1740599 = 2610899) B2610899
theorem B3903389 : Blo 770335 3903389 := bstep (se 3 (by rfl) ⟨731885, by rfl⟩ : syracuseStep 3903389 = 1463771) B1463771
theorem B1740905 : Blo 770335 1740905 := bstep (se 2 (by rfl) ⟨652839, by rfl⟩ : syracuseStep 1740905 = 1305679) B1305679
theorem B3805547 : Blo 770335 3805547 := bstep (se 1 (by rfl) ⟨2854160, by rfl⟩ : syracuseStep 3805547 = 5708321) B5708321
theorem B7410035 : Blo 770335 7410035 := bstep (se 1 (by rfl) ⟨5557526, by rfl⟩ : syracuseStep 7410035 = 11115053) B11115053
theorem B8360509 : Blo 770335 8360509 := bstep (se 3 (by rfl) ⟨1567595, by rfl⟩ : syracuseStep 8360509 = 3135191) B3135191
theorem B1741391 : Blo 770335 1741391 := bstep (se 1 (by rfl) ⟨1306043, by rfl⟩ : syracuseStep 1741391 = 2612087) B2612087
theorem B3904199 : Blo 770335 3904199 := bstep (se 1 (by rfl) ⟨2928149, by rfl⟩ : syracuseStep 3904199 = 5856299) B5856299
theorem B1741535 : Blo 770335 1741535 := bstep (se 1 (by rfl) ⟨1306151, by rfl⟩ : syracuseStep 1741535 = 2612303) B2612303
theorem B1741787 : Blo 770335 1741787 := bstep (se 1 (by rfl) ⟨1306340, by rfl⟩ : syracuseStep 1741787 = 2612681) B2612681
theorem B2200567 : Blo 770335 2200567 := bstep (se 1 (by rfl) ⟨1650425, by rfl⟩ : syracuseStep 2200567 = 3300851) B3300851
theorem B4953145 : Blo 770335 4953145 := bstep (se 2 (by rfl) ⟨1857429, by rfl⟩ : syracuseStep 4953145 = 3714859) B3714859
theorem B3052687 : Blo 770335 3052687 := bstep (se 1 (by rfl) ⟨2289515, by rfl⟩ : syracuseStep 3052687 = 4579031) B4579031
theorem B1741967 : Blo 770335 1741967 := bstep (se 1 (by rfl) ⟨1306475, by rfl⟩ : syracuseStep 1741967 = 2612951) B2612951
theorem B1742057 : Blo 770335 1742057 := bstep (se 2 (by rfl) ⟨653271, by rfl⟩ : syracuseStep 1742057 = 1306543) B1306543
theorem B1742111 : Blo 770335 1742111 := bstep (se 1 (by rfl) ⟨1306583, by rfl⟩ : syracuseStep 1742111 = 2613167) B2613167
theorem B8329463 : Blo 770335 8329463 := bstep (se 1 (by rfl) ⟨6247097, by rfl⟩ : syracuseStep 8329463 = 12494195) B12494195
theorem B13769473 : Blo 770335 13769473 := bstep (se 2 (by rfl) ⟨5163552, by rfl⟩ : syracuseStep 13769473 = 10327105) B10327105
theorem B826319 : Blo 770335 826319 := bstep (se 1 (by rfl) ⟨619739, by rfl⟩ : syracuseStep 826319 = 1239479) B1239479
theorem B4463837 : Blo 770335 4463837 := bstep (se 3 (by rfl) ⟨836969, by rfl⟩ : syracuseStep 4463837 = 1673939) B1673939
theorem B3906953 : Blo 770335 3906953 := bstep (se 2 (by rfl) ⟨1465107, by rfl⟩ : syracuseStep 3906953 = 2930215) B2930215
theorem B2203129 : Blo 770335 2203129 := bstep (se 2 (by rfl) ⟨826173, by rfl⟩ : syracuseStep 2203129 = 1652347) B1652347
theorem B11148961 : Blo 770335 11148961 := bstep (se 2 (by rfl) ⟨4180860, by rfl⟩ : syracuseStep 11148961 = 8361721) B8361721
theorem B6692615 : Blo 770335 6692615 := bstep (se 1 (by rfl) ⟨5019461, by rfl⟩ : syracuseStep 6692615 = 10038923) B10038923
theorem B8363969 : Blo 770335 8363969 := bstep (se 2 (by rfl) ⟨3136488, by rfl⟩ : syracuseStep 8363969 = 6272977) B6272977
theorem B30449783 : Blo 770335 30449783 := bstep (se 1 (by rfl) ⟨22837337, by rfl⟩ : syracuseStep 30449783 = 45674675) B45674675
theorem B1155647 : Blo 770335 1155647 := bstep (se 1 (by rfl) ⟨866735, by rfl⟩ : syracuseStep 1155647 = 1733471) B1733471
theorem B3908249 : Blo 770335 3908249 := bstep (se 2 (by rfl) ⟨1465593, by rfl⟩ : syracuseStep 3908249 = 2931187) B2931187
theorem B3515051 : Blo 770335 3515051 := bstep (se 1 (by rfl) ⟨2636288, by rfl⟩ : syracuseStep 3515051 = 5272577) B5272577
theorem B1155767 : Blo 770335 1155767 := bstep (se 1 (by rfl) ⟨866825, by rfl⟩ : syracuseStep 1155767 = 1733651) B1733651
theorem B1155995 : Blo 770335 1155995 := bstep (se 1 (by rfl) ⟨866996, by rfl⟩ : syracuseStep 1155995 = 1733993) B1733993
theorem B2204815 : Blo 770335 2204815 := bstep (se 1 (by rfl) ⟨1653611, by rfl⟩ : syracuseStep 2204815 = 3307223) B3307223
theorem B1156391 : Blo 770335 1156391 := bstep (se 1 (by rfl) ⟨867293, by rfl⟩ : syracuseStep 1156391 = 1734587) B1734587
theorem B1156475 : Blo 770335 1156475 := bstep (se 1 (by rfl) ⟨867356, by rfl⟩ : syracuseStep 1156475 = 1734713) B1734713
theorem B1156601 : Blo 770335 1156601 := bstep (se 2 (by rfl) ⟨433725, by rfl⟩ : syracuseStep 1156601 = 867451) B867451
theorem B1156703 : Blo 770335 1156703 := bstep (se 1 (by rfl) ⟨867527, by rfl⟩ : syracuseStep 1156703 = 1735055) B1735055
theorem B1156919 : Blo 770335 1156919 := bstep (se 1 (by rfl) ⟨867689, by rfl⟩ : syracuseStep 1156919 = 1735379) B1735379
theorem B1648649 : Blo 770335 1648649 := bstep (se 2 (by rfl) ⟨618243, by rfl⟩ : syracuseStep 1648649 = 1236487) B1236487
theorem B1157225 : Blo 770335 1157225 := bstep (se 2 (by rfl) ⟨433959, by rfl⟩ : syracuseStep 1157225 = 867919) B867919
theorem B4401337 : Blo 770335 4401337 := bstep (se 2 (by rfl) ⟨1650501, by rfl⟩ : syracuseStep 4401337 = 3301003) B3301003
theorem B3910031 : Blo 770335 3910031 := bstep (se 1 (by rfl) ⟨2932523, by rfl⟩ : syracuseStep 3910031 = 5865047) B5865047
theorem B1157543 : Blo 770335 1157543 := bstep (se 1 (by rfl) ⟨868157, by rfl⟩ : syracuseStep 1157543 = 1736315) B1736315
theorem B9513389 : Blo 770335 9513389 := bstep (se 3 (by rfl) ⟨1783760, by rfl⟩ : syracuseStep 9513389 = 3567521) B3567521
theorem B1157627 : Blo 770335 1157627 := bstep (se 1 (by rfl) ⟨868220, by rfl⟩ : syracuseStep 1157627 = 1736441) B1736441
theorem B1157753 : Blo 770335 1157753 := bstep (se 2 (by rfl) ⟨434157, by rfl⟩ : syracuseStep 1157753 = 868315) B868315
theorem B1157807 : Blo 770335 1157807 := bstep (se 1 (by rfl) ⟨868355, by rfl⟩ : syracuseStep 1157807 = 1736711) B1736711
theorem B2927299 : Blo 770335 2927299 := bstep (se 1 (by rfl) ⟨2195474, by rfl⟩ : syracuseStep 2927299 = 4390949) B4390949
theorem B1157855 : Blo 770335 1157855 := bstep (se 1 (by rfl) ⟨868391, by rfl⟩ : syracuseStep 1157855 = 1736783) B1736783
theorem B8366915 : Blo 770335 8366915 := bstep (se 1 (by rfl) ⟨6275186, by rfl⟩ : syracuseStep 8366915 = 12550373) B12550373
theorem B4467581 : Blo 770335 4467581 := bstep (se 3 (by rfl) ⟨837671, by rfl⟩ : syracuseStep 4467581 = 1675343) B1675343
theorem B1158119 : Blo 770335 1158119 := bstep (se 1 (by rfl) ⟨868589, by rfl⟩ : syracuseStep 1158119 = 1737179) B1737179
theorem B1977331 : Blo 770335 1977331 := bstep (se 1 (by rfl) ⟨1482998, by rfl⟩ : syracuseStep 1977331 = 2965997) B2965997
theorem B2927603 : Blo 770335 2927603 := bstep (se 1 (by rfl) ⟨2195702, by rfl⟩ : syracuseStep 2927603 = 4391405) B4391405
theorem B5287027 : Blo 770335 5287027 := bstep (se 1 (by rfl) ⟨3965270, by rfl⟩ : syracuseStep 5287027 = 7930541) B7930541
theorem B1158377 : Blo 770335 1158377 := bstep (se 2 (by rfl) ⟨434391, by rfl⟩ : syracuseStep 1158377 = 868783) B868783
theorem B1158431 : Blo 770335 1158431 := bstep (se 1 (by rfl) ⟨868823, by rfl⟩ : syracuseStep 1158431 = 1737647) B1737647
theorem B16035191 : Blo 770335 16035191 := bstep (se 1 (by rfl) ⟨12026393, by rfl⟩ : syracuseStep 16035191 = 24052787) B24052787
theorem B2928059 : Blo 770335 2928059 := bstep (se 1 (by rfl) ⟨2196044, by rfl⟩ : syracuseStep 2928059 = 4392089) B4392089
theorem B1158599 : Blo 770335 1158599 := bstep (se 1 (by rfl) ⟨868949, by rfl⟩ : syracuseStep 1158599 = 1737899) B1737899
theorem B2600531 : Blo 770335 2600531 := bstep (se 1 (by rfl) ⟨1950398, by rfl⟩ : syracuseStep 2600531 = 3900797) B3900797
theorem B1158953 : Blo 770335 1158953 := bstep (se 2 (by rfl) ⟨434607, by rfl⟩ : syracuseStep 1158953 = 869215) B869215
theorem B1158959 : Blo 770335 1158959 := bstep (se 1 (by rfl) ⟨869219, by rfl⟩ : syracuseStep 1158959 = 1738439) B1738439
theorem B3715091 : Blo 770335 3715091 := bstep (se 1 (by rfl) ⟨2786318, by rfl⟩ : syracuseStep 3715091 = 5572637) B5572637
theorem B15052825 : Blo 770335 15052825 := bstep (se 2 (by rfl) ⟨5644809, by rfl⟩ : syracuseStep 15052825 = 11289619) B11289619
theorem B1650793 : Blo 770335 1650793 := bstep (se 2 (by rfl) ⟨619047, by rfl⟩ : syracuseStep 1650793 = 1238095) B1238095
theorem B1159433 : Blo 770335 1159433 := bstep (se 2 (by rfl) ⟨434787, by rfl⟩ : syracuseStep 1159433 = 869575) B869575
theorem B1159535 : Blo 770335 1159535 := bstep (se 1 (by rfl) ⟨869651, by rfl⟩ : syracuseStep 1159535 = 1739303) B1739303
theorem B3912137 : Blo 770335 3912137 := bstep (se 2 (by rfl) ⟨1467051, by rfl⟩ : syracuseStep 3912137 = 2934103) B2934103
theorem B1159751 : Blo 770335 1159751 := bstep (se 1 (by rfl) ⟨869813, by rfl⟩ : syracuseStep 1159751 = 1739627) B1739627
theorem B1159787 : Blo 770335 1159787 := bstep (se 1 (by rfl) ⟨869840, by rfl⟩ : syracuseStep 1159787 = 1739681) B1739681
theorem B1979063 : Blo 770335 1979063 := bstep (se 1 (by rfl) ⟨1484297, by rfl⟩ : syracuseStep 1979063 = 2968595) B2968595
theorem B3715919 : Blo 770335 3715919 := bstep (se 1 (by rfl) ⟨2786939, by rfl⟩ : syracuseStep 3715919 = 5573879) B5573879
theorem B1160015 : Blo 770335 1160015 := bstep (se 1 (by rfl) ⟨870011, by rfl⟩ : syracuseStep 1160015 = 1740023) B1740023
theorem B40121335 : Blo 770335 40121335 := bstep (se 1 (by rfl) ⟨30091001, by rfl⟩ : syracuseStep 40121335 = 60182003) B60182003
theorem B1651835 : Blo 770335 1651835 := bstep (se 1 (by rfl) ⟨1238876, by rfl⟩ : syracuseStep 1651835 = 2477753) B2477753
theorem B1160411 : Blo 770335 1160411 := bstep (se 1 (by rfl) ⟨870308, by rfl⟩ : syracuseStep 1160411 = 1740617) B1740617
theorem B3912947 : Blo 770335 3912947 := bstep (se 1 (by rfl) ⟨2934710, by rfl⟩ : syracuseStep 3912947 = 5869421) B5869421
theorem B1160585 : Blo 770335 1160585 := bstep (se 2 (by rfl) ⟨435219, by rfl⟩ : syracuseStep 1160585 = 870439) B870439
theorem B1160939 : Blo 770335 1160939 := bstep (se 1 (by rfl) ⟨870704, by rfl⟩ : syracuseStep 1160939 = 1741409) B1741409
theorem B2930519 : Blo 770335 2930519 := bstep (se 1 (by rfl) ⟨2197889, by rfl⟩ : syracuseStep 2930519 = 4395779) B4395779
theorem B48215969 : Blo 770335 48215969 := bstep (se 2 (by rfl) ⟨18080988, by rfl⟩ : syracuseStep 48215969 = 36161977) B36161977
theorem B1161167 : Blo 770335 1161167 := bstep (se 1 (by rfl) ⟨870875, by rfl⟩ : syracuseStep 1161167 = 1741751) B1741751
theorem B4405529 : Blo 770335 4405529 := bstep (se 2 (by rfl) ⟨1652073, by rfl⟩ : syracuseStep 4405529 = 3304147) B3304147
theorem B1653065 : Blo 770335 1653065 := bstep (se 2 (by rfl) ⟨619899, by rfl⟩ : syracuseStep 1653065 = 1239799) B1239799
theorem B1653167 : Blo 770335 1653167 := bstep (se 1 (by rfl) ⟨1239875, by rfl⟩ : syracuseStep 1653167 = 2479751) B2479751
theorem B2603447 : Blo 770335 2603447 := bstep (se 1 (by rfl) ⟨1952585, by rfl⟩ : syracuseStep 2603447 = 3905171) B3905171
theorem B1489403 : Blo 770335 1489403 := bstep (se 1 (by rfl) ⟨1117052, by rfl⟩ : syracuseStep 1489403 = 2234105) B2234105
theorem B13187609 : Blo 770335 13187609 := bstep (se 2 (by rfl) ⟨4945353, by rfl⟩ : syracuseStep 13187609 = 9890707) B9890707
theorem B866911 : Blo 770335 866911 := bstep (se 1 (by rfl) ⟨650183, by rfl⟩ : syracuseStep 866911 = 1300367) B1300367
theorem B7945147 : Blo 770335 7945147 := bstep (se 1 (by rfl) ⟨5958860, by rfl⟩ : syracuseStep 7945147 = 11917721) B11917721
theorem B3914891 : Blo 770335 3914891 := bstep (se 1 (by rfl) ⟨2936168, by rfl⟩ : syracuseStep 3914891 = 5872337) B5872337
theorem B3292427 : Blo 770335 3292427 := bstep (se 1 (by rfl) ⟨2469320, by rfl⟩ : syracuseStep 3292427 = 4938641) B4938641
theorem B9878921 : Blo 770335 9878921 := bstep (se 2 (by rfl) ⟨3704595, by rfl⟩ : syracuseStep 9878921 = 7409191) B7409191
theorem B5291513 : Blo 770335 5291513 := bstep (se 2 (by rfl) ⟨1984317, by rfl⟩ : syracuseStep 5291513 = 3968635) B3968635
theorem B2473487 : Blo 770335 2473487 := bstep (se 1 (by rfl) ⟨1855115, by rfl⟩ : syracuseStep 2473487 = 3710231) B3710231
theorem B1392223 : Blo 770335 1392223 := bstep (se 1 (by rfl) ⟨1044167, by rfl⟩ : syracuseStep 1392223 = 2088335) B2088335
theorem B8371927 : Blo 770335 8371927 := bstep (se 1 (by rfl) ⟨6278945, by rfl⟩ : syracuseStep 8371927 = 12557891) B12557891
theorem B868063 : Blo 770335 868063 := bstep (se 1 (by rfl) ⟨651047, by rfl⟩ : syracuseStep 868063 = 1302095) B1302095
theorem B4407169 : Blo 770335 4407169 := bstep (se 2 (by rfl) ⟨1652688, by rfl⟩ : syracuseStep 4407169 = 3305377) B3305377
theorem B1982675 : Blo 770335 1982675 := bstep (se 1 (by rfl) ⟨1487006, by rfl⟩ : syracuseStep 1982675 = 2974013) B2974013
theorem B770335 : Blo 770335 770335 := bstep (se 1 (by rfl) ⟨577751, by rfl⟩ : syracuseStep 770335 = 1155503) B1155503
theorem B868639 : Blo 770335 868639 := bstep (se 1 (by rfl) ⟨651479, by rfl⟩ : syracuseStep 868639 = 1302959) B1302959
theorem B770395 : Blo 770335 770395 := bstep (se 1 (by rfl) ⟨577796, by rfl⟩ : syracuseStep 770395 = 1155593) B1155593
theorem B770415 : Blo 770335 770415 := bstep (se 1 (by rfl) ⟨577811, by rfl⟩ : syracuseStep 770415 = 1155623) B1155623
theorem B770471 : Blo 770335 770471 := bstep (se 1 (by rfl) ⟨577853, by rfl⟩ : syracuseStep 770471 = 1155707) B1155707
theorem B770555 : Blo 770335 770555 := bstep (se 1 (by rfl) ⟨577916, by rfl⟩ : syracuseStep 770555 = 1155833) B1155833
theorem B1950227 : Blo 770335 1950227 := bstep (se 1 (by rfl) ⟨1462670, by rfl⟩ : syracuseStep 1950227 = 2925341) B2925341
theorem B770623 : Blo 770335 770623 := bstep (se 1 (by rfl) ⟨577967, by rfl⟩ : syracuseStep 770623 = 1155935) B1155935
theorem B868927 : Blo 770335 868927 := bstep (se 1 (by rfl) ⟨651695, by rfl⟩ : syracuseStep 868927 = 1303391) B1303391
theorem B770631 : Blo 770335 770631 := bstep (se 1 (by rfl) ⟨577973, by rfl⟩ : syracuseStep 770631 = 1155947) B1155947
theorem B13222601 : Blo 770335 13222601 := bstep (se 2 (by rfl) ⟨4958475, by rfl⟩ : syracuseStep 13222601 = 9916951) B9916951
theorem B770783 : Blo 770335 770783 := bstep (se 1 (by rfl) ⟨578087, by rfl⟩ : syracuseStep 770783 = 1156175) B1156175
theorem B3916511 : Blo 770335 3916511 := bstep (se 1 (by rfl) ⟨2937383, by rfl⟩ : syracuseStep 3916511 = 5874767) B5874767
theorem B25051949 : Blo 770335 25051949 := bstep (se 3 (by rfl) ⟨4697240, by rfl⟩ : syracuseStep 25051949 = 9394481) B9394481
theorem B770863 : Blo 770335 770863 := bstep (se 1 (by rfl) ⟨578147, by rfl⟩ : syracuseStep 770863 = 1156295) B1156295
theorem B770971 : Blo 770335 770971 := bstep (se 1 (by rfl) ⟨578228, by rfl⟩ : syracuseStep 770971 = 1156457) B1156457
theorem B771023 : Blo 770335 771023 := bstep (se 1 (by rfl) ⟨578267, by rfl⟩ : syracuseStep 771023 = 1156535) B1156535
theorem B771047 : Blo 770335 771047 := bstep (se 1 (by rfl) ⟨578285, by rfl⟩ : syracuseStep 771047 = 1156571) B1156571
theorem B771359 : Blo 770335 771359 := bstep (se 1 (by rfl) ⟨578519, by rfl⟩ : syracuseStep 771359 = 1157039) B1157039
theorem B771419 : Blo 770335 771419 := bstep (se 1 (by rfl) ⟨578564, by rfl⟩ : syracuseStep 771419 = 1157129) B1157129
theorem B771439 : Blo 770335 771439 := bstep (se 1 (by rfl) ⟨578579, by rfl⟩ : syracuseStep 771439 = 1157159) B1157159
theorem B869755 : Blo 770335 869755 := bstep (se 1 (by rfl) ⟨652316, by rfl⟩ : syracuseStep 869755 = 1304633) B1304633
theorem B771495 : Blo 770335 771495 := bstep (se 1 (by rfl) ⟨578621, by rfl⟩ : syracuseStep 771495 = 1157243) B1157243
theorem B2606525 : Blo 770335 2606525 := bstep (se 3 (by rfl) ⟨488723, by rfl⟩ : syracuseStep 2606525 = 977447) B977447
theorem B1099207 : Blo 770335 1099207 := bstep (se 1 (by rfl) ⟨824405, by rfl⟩ : syracuseStep 1099207 = 1648811) B1648811
theorem B3294701 : Blo 770335 3294701 := bstep (se 3 (by rfl) ⟨617756, by rfl⟩ : syracuseStep 3294701 = 1235513) B1235513
theorem B771579 : Blo 770335 771579 := bstep (se 1 (by rfl) ⟨578684, by rfl⟩ : syracuseStep 771579 = 1157369) B1157369
theorem B771647 : Blo 770335 771647 := bstep (se 1 (by rfl) ⟨578735, by rfl⟩ : syracuseStep 771647 = 1157471) B1157471
theorem B771655 : Blo 770335 771655 := bstep (se 1 (by rfl) ⟨578741, by rfl⟩ : syracuseStep 771655 = 1157483) B1157483
theorem B2475677 : Blo 770335 2475677 := bstep (se 3 (by rfl) ⟨464189, by rfl⟩ : syracuseStep 2475677 = 928379) B928379
theorem B771807 : Blo 770335 771807 := bstep (se 1 (by rfl) ⟨578855, by rfl⟩ : syracuseStep 771807 = 1157711) B1157711
theorem B771887 : Blo 770335 771887 := bstep (se 1 (by rfl) ⟨578915, by rfl⟩ : syracuseStep 771887 = 1157831) B1157831
theorem B2606903 : Blo 770335 2606903 := bstep (se 1 (by rfl) ⟨1955177, by rfl⟩ : syracuseStep 2606903 = 3910355) B3910355
theorem B870223 : Blo 770335 870223 := bstep (se 1 (by rfl) ⟨652667, by rfl⟩ : syracuseStep 870223 = 1305335) B1305335
theorem B2082689 : Blo 770335 2082689 := bstep (se 2 (by rfl) ⟨781008, by rfl⟩ : syracuseStep 2082689 = 1562017) B1562017
theorem B771995 : Blo 770335 771995 := bstep (se 1 (by rfl) ⟨578996, by rfl⟩ : syracuseStep 771995 = 1157993) B1157993
theorem B772047 : Blo 770335 772047 := bstep (se 1 (by rfl) ⟨579035, by rfl⟩ : syracuseStep 772047 = 1158071) B1158071
theorem B772071 : Blo 770335 772071 := bstep (se 1 (by rfl) ⟨579053, by rfl⟩ : syracuseStep 772071 = 1158107) B1158107
theorem B870619 : Blo 770335 870619 := bstep (se 1 (by rfl) ⟨652964, by rfl⟩ : syracuseStep 870619 = 1305929) B1305929
theorem B1952009 : Blo 770335 1952009 := bstep (se 2 (by rfl) ⟨732003, by rfl⟩ : syracuseStep 1952009 = 1464007) B1464007
theorem B2607389 : Blo 770335 2607389 := bstep (se 3 (by rfl) ⟨488885, by rfl⟩ : syracuseStep 2607389 = 977771) B977771
theorem B772383 : Blo 770335 772383 := bstep (se 1 (by rfl) ⟨579287, by rfl⟩ : syracuseStep 772383 = 1158575) B1158575
theorem B772443 : Blo 770335 772443 := bstep (se 1 (by rfl) ⟨579332, by rfl⟩ : syracuseStep 772443 = 1158665) B1158665
theorem B772463 : Blo 770335 772463 := bstep (se 1 (by rfl) ⟨579347, by rfl⟩ : syracuseStep 772463 = 1158695) B1158695
theorem B772519 : Blo 770335 772519 := bstep (se 1 (by rfl) ⟨579389, by rfl⟩ : syracuseStep 772519 = 1158779) B1158779
theorem B772603 : Blo 770335 772603 := bstep (se 1 (by rfl) ⟨579452, by rfl⟩ : syracuseStep 772603 = 1158905) B1158905
theorem B870907 : Blo 770335 870907 := bstep (se 1 (by rfl) ⟨653180, by rfl⟩ : syracuseStep 870907 = 1306361) B1306361
theorem B772671 : Blo 770335 772671 := bstep (se 1 (by rfl) ⟨579503, by rfl⟩ : syracuseStep 772671 = 1159007) B1159007
theorem B772679 : Blo 770335 772679 := bstep (se 1 (by rfl) ⟨579509, by rfl⟩ : syracuseStep 772679 = 1159019) B1159019
theorem B1952363 : Blo 770335 1952363 := bstep (se 1 (by rfl) ⟨1464272, by rfl⟩ : syracuseStep 1952363 = 2928545) B2928545
theorem B871087 : Blo 770335 871087 := bstep (se 1 (by rfl) ⟨653315, by rfl⟩ : syracuseStep 871087 = 1306631) B1306631
theorem B2083511 : Blo 770335 2083511 := bstep (se 1 (by rfl) ⟨1562633, by rfl⟩ : syracuseStep 2083511 = 3125267) B3125267
theorem B1100471 : Blo 770335 1100471 := bstep (se 1 (by rfl) ⟨825353, by rfl⟩ : syracuseStep 1100471 = 1650707) B1650707
theorem B772831 : Blo 770335 772831 := bstep (se 1 (by rfl) ⟨579623, by rfl⟩ : syracuseStep 772831 = 1159247) B1159247
theorem B772911 : Blo 770335 772911 := bstep (se 1 (by rfl) ⟨579683, by rfl⟩ : syracuseStep 772911 = 1159367) B1159367
theorem B773019 : Blo 770335 773019 := bstep (se 1 (by rfl) ⟨579764, by rfl⟩ : syracuseStep 773019 = 1159529) B1159529
theorem B3918779 : Blo 770335 3918779 := bstep (se 1 (by rfl) ⟨2939084, by rfl⟩ : syracuseStep 3918779 = 5878169) B5878169
theorem B773071 : Blo 770335 773071 := bstep (se 1 (by rfl) ⟨579803, by rfl⟩ : syracuseStep 773071 = 1159607) B1159607
theorem B773095 : Blo 770335 773095 := bstep (se 1 (by rfl) ⟨579821, by rfl⟩ : syracuseStep 773095 = 1159643) B1159643
theorem B1854451 : Blo 770335 1854451 := bstep (se 1 (by rfl) ⟨1390838, by rfl⟩ : syracuseStep 1854451 = 2781677) B2781677
theorem B1854683 : Blo 770335 1854683 := bstep (se 1 (by rfl) ⟨1391012, by rfl⟩ : syracuseStep 1854683 = 2782025) B2782025
theorem B1953011 : Blo 770335 1953011 := bstep (se 1 (by rfl) ⟨1464758, by rfl⟩ : syracuseStep 1953011 = 2929517) B2929517
theorem B2608415 : Blo 770335 2608415 := bstep (se 1 (by rfl) ⟨1956311, by rfl⟩ : syracuseStep 2608415 = 3912623) B3912623
theorem B773407 : Blo 770335 773407 := bstep (se 1 (by rfl) ⟨580055, by rfl⟩ : syracuseStep 773407 = 1160111) B1160111
theorem B773467 : Blo 770335 773467 := bstep (se 1 (by rfl) ⟨580100, by rfl⟩ : syracuseStep 773467 = 1160201) B1160201
theorem B773487 : Blo 770335 773487 := bstep (se 1 (by rfl) ⟨580115, by rfl⟩ : syracuseStep 773487 = 1160231) B1160231
theorem B773543 : Blo 770335 773543 := bstep (se 1 (by rfl) ⟨580157, by rfl⟩ : syracuseStep 773543 = 1160315) B1160315
theorem B3296699 : Blo 770335 3296699 := bstep (se 1 (by rfl) ⟨2472524, by rfl⟩ : syracuseStep 3296699 = 4945049) B4945049
theorem B9391559 : Blo 770335 9391559 := bstep (se 1 (by rfl) ⟨7043669, by rfl⟩ : syracuseStep 9391559 = 14087339) B14087339
theorem B773627 : Blo 770335 773627 := bstep (se 1 (by rfl) ⟨580220, by rfl⟩ : syracuseStep 773627 = 1160441) B1160441
theorem B773695 : Blo 770335 773695 := bstep (se 1 (by rfl) ⟨580271, by rfl⟩ : syracuseStep 773695 = 1160543) B1160543
theorem B773703 : Blo 770335 773703 := bstep (se 1 (by rfl) ⟨580277, by rfl⟩ : syracuseStep 773703 = 1160555) B1160555
theorem B1953467 : Blo 770335 1953467 := bstep (se 1 (by rfl) ⟨1465100, by rfl⟩ : syracuseStep 1953467 = 2930201) B2930201
theorem B773855 : Blo 770335 773855 := bstep (se 1 (by rfl) ⟨580391, by rfl⟩ : syracuseStep 773855 = 1160783) B1160783
theorem B2477803 : Blo 770335 2477803 := bstep (se 1 (by rfl) ⟨1858352, by rfl⟩ : syracuseStep 2477803 = 3716705) B3716705
theorem B773935 : Blo 770335 773935 := bstep (se 1 (by rfl) ⟨580451, by rfl⟩ : syracuseStep 773935 = 1160903) B1160903
theorem B774043 : Blo 770335 774043 := bstep (se 1 (by rfl) ⟨580532, by rfl⟩ : syracuseStep 774043 = 1161065) B1161065
theorem B774095 : Blo 770335 774095 := bstep (se 1 (by rfl) ⟨580571, by rfl⟩ : syracuseStep 774095 = 1161143) B1161143
theorem B774119 : Blo 770335 774119 := bstep (se 1 (by rfl) ⟨580589, by rfl⟩ : syracuseStep 774119 = 1161179) B1161179
theorem B1101929 : Blo 770335 1101929 := bstep (se 2 (by rfl) ⟨413223, by rfl⟩ : syracuseStep 1101929 = 826447) B826447
theorem B3920075 : Blo 770335 3920075 := bstep (se 1 (by rfl) ⟨2940056, by rfl⟩ : syracuseStep 3920075 = 5880113) B5880113
theorem B1954003 : Blo 770335 1954003 := bstep (se 1 (by rfl) ⟨1465502, by rfl⟩ : syracuseStep 1954003 = 2931005) B2931005
theorem B10572511 : Blo 770335 10572511 := bstep (se 1 (by rfl) ⟨7929383, by rfl⟩ : syracuseStep 10572511 = 15858767) B15858767
theorem B6607817 : Blo 770335 6607817 := bstep (se 2 (by rfl) ⟨2477931, by rfl⟩ : syracuseStep 6607817 = 4955863) B4955863
theorem B7918717 : Blo 770335 7918717 := bstep (se 3 (by rfl) ⟨1484759, by rfl⟩ : syracuseStep 7918717 = 2969519) B2969519
theorem B1954955 : Blo 770335 1954955 := bstep (se 1 (by rfl) ⟨1466216, by rfl⟩ : syracuseStep 1954955 = 2932433) B2932433
theorem B5854355 : Blo 770335 5854355 := bstep (se 1 (by rfl) ⟨4390766, by rfl⟩ : syracuseStep 5854355 = 8781533) B8781533
theorem B1955411 : Blo 770335 1955411 := bstep (se 1 (by rfl) ⟨1466558, by rfl⟩ : syracuseStep 1955411 = 2933117) B2933117
theorem B1300063 : Blo 770335 1300063 := bstep (se 1 (by rfl) ⟨975047, by rfl⟩ : syracuseStep 1300063 = 1950095) B1950095
theorem B2610845 : Blo 770335 2610845 := bstep (se 3 (by rfl) ⟨489533, by rfl⟩ : syracuseStep 2610845 = 979067) B979067
theorem B1463969 : Blo 770335 1463969 := bstep (se 2 (by rfl) ⟨548988, by rfl⟩ : syracuseStep 1463969 = 1097977) B1097977
theorem B1300279 : Blo 770335 1300279 := bstep (se 1 (by rfl) ⟨975209, by rfl⟩ : syracuseStep 1300279 = 1950419) B1950419
theorem B14833601 : Blo 770335 14833601 := bstep (se 2 (by rfl) ⟨5562600, by rfl⟩ : syracuseStep 14833601 = 11125201) B11125201
theorem B2480161 : Blo 770335 2480161 := bstep (se 2 (by rfl) ⟨930060, by rfl⟩ : syracuseStep 2480161 = 1860121) B1860121
theorem B3135617 : Blo 770335 3135617 := bstep (se 2 (by rfl) ⟨1175856, by rfl⟩ : syracuseStep 3135617 = 2351713) B2351713
theorem B2644103 : Blo 770335 2644103 := bstep (se 1 (by rfl) ⟨1983077, by rfl⟩ : syracuseStep 2644103 = 3966155) B3966155
theorem B2611385 : Blo 770335 2611385 := bstep (se 2 (by rfl) ⟨979269, by rfl⟩ : syracuseStep 2611385 = 1958539) B1958539
theorem B1300745 : Blo 770335 1300745 := bstep (se 2 (by rfl) ⟨487779, by rfl⟩ : syracuseStep 1300745 = 975559) B975559
theorem B7919947 : Blo 770335 7919947 := bstep (se 1 (by rfl) ⟨5939960, by rfl⟩ : syracuseStep 7919947 = 11879921) B11879921
theorem B1464743 : Blo 770335 1464743 := bstep (se 1 (by rfl) ⟨1098557, by rfl⟩ : syracuseStep 1464743 = 2197115) B2197115
theorem B1956271 : Blo 770335 1956271 := bstep (se 1 (by rfl) ⟨1467203, by rfl⟩ : syracuseStep 1956271 = 2934407) B2934407
theorem B11262503 : Blo 770335 11262503 := bstep (se 1 (by rfl) ⟨8446877, by rfl⟩ : syracuseStep 11262503 = 16893755) B16893755
theorem B1464895 : Blo 770335 1464895 := bstep (se 1 (by rfl) ⟨1098671, by rfl⟩ : syracuseStep 1464895 = 2197343) B2197343
theorem B1956575 : Blo 770335 1956575 := bstep (se 1 (by rfl) ⟨1467431, by rfl⟩ : syracuseStep 1956575 = 2934863) B2934863
theorem B3300115 : Blo 770335 3300115 := bstep (se 1 (by rfl) ⟨2475086, by rfl⟩ : syracuseStep 3300115 = 4950173) B4950173
theorem B9886607 : Blo 770335 9886607 := bstep (se 1 (by rfl) ⟨7414955, by rfl⟩ : syracuseStep 9886607 = 14829911) B14829911
theorem B3955643 : Blo 770335 3955643 := bstep (se 1 (by rfl) ⟨2966732, by rfl⟩ : syracuseStep 3955643 = 5933465) B5933465
theorem B183196853 : Blo 770335 183196853 := bstep (se 5 (by rfl) ⟨8587352, by rfl⟩ : syracuseStep 183196853 = 17174705) B17174705
theorem B1301737 : Blo 770335 1301737 := bstep (se 2 (by rfl) ⟨488151, by rfl⟩ : syracuseStep 1301737 = 976303) B976303
theorem B1301791 : Blo 770335 1301791 := bstep (se 1 (by rfl) ⟨976343, by rfl⟩ : syracuseStep 1301791 = 1952687) B1952687
theorem B1957243 : Blo 770335 1957243 := bstep (se 1 (by rfl) ⟨1467932, by rfl⟩ : syracuseStep 1957243 = 2935865) B2935865
theorem B2776457 : Blo 770335 2776457 := bstep (se 2 (by rfl) ⟨1041171, by rfl⟩ : syracuseStep 2776457 = 2082343) B2082343
theorem B65068505 : Blo 770335 65068505 := bstep (se 2 (by rfl) ⟨24400689, by rfl⟩ : syracuseStep 65068505 = 48801379) B48801379
theorem B1465951 : Blo 770335 1465951 := bstep (se 1 (by rfl) ⟨1099463, by rfl⟩ : syracuseStep 1465951 = 2198927) B2198927
theorem B2612897 : Blo 770335 2612897 := bstep (se 2 (by rfl) ⟨979836, by rfl⟩ : syracuseStep 2612897 = 1959673) B1959673
theorem B1302203 : Blo 770335 1302203 := bstep (se 1 (by rfl) ⟨976652, by rfl⟩ : syracuseStep 1302203 = 1953305) B1953305
theorem B3301073 : Blo 770335 3301073 := bstep (se 2 (by rfl) ⟨1237902, by rfl⟩ : syracuseStep 3301073 = 2475805) B2475805
theorem B1957679 : Blo 770335 1957679 := bstep (se 1 (by rfl) ⟨1468259, by rfl⟩ : syracuseStep 1957679 = 2936519) B2936519
theorem B8806319 : Blo 770335 8806319 := bstep (se 1 (by rfl) ⟨6604739, by rfl⟩ : syracuseStep 8806319 = 13209479) B13209479
theorem B1237415 : Blo 770335 1237415 := bstep (se 1 (by rfl) ⟨928061, by rfl⟩ : syracuseStep 1237415 = 1856123) B1856123
theorem B3170735 : Blo 770335 3170735 := bstep (se 1 (by rfl) ⟨2378051, by rfl⟩ : syracuseStep 3170735 = 4756103) B4756103
theorem B1958327 : Blo 770335 1958327 := bstep (se 1 (by rfl) ⟨1468745, by rfl⟩ : syracuseStep 1958327 = 2937491) B2937491
theorem B4940639 : Blo 770335 4940639 := bstep (se 1 (by rfl) ⟨3705479, by rfl⟩ : syracuseStep 4940639 = 7410959) B7410959
theorem B5858243 : Blo 770335 5858243 := bstep (se 1 (by rfl) ⟨4393682, by rfl⟩ : syracuseStep 5858243 = 8787365) B8787365
theorem B31745125 : Blo 770335 31745125 := bstep (se 4 (by rfl) ⟨2976105, by rfl⟩ : syracuseStep 31745125 = 5952211) B5952211
theorem B1238159 : Blo 770335 1238159 := bstep (se 1 (by rfl) ⟨928619, by rfl⟩ : syracuseStep 1238159 = 1857239) B1857239
theorem B13165739 : Blo 770335 13165739 := bstep (se 1 (by rfl) ⟨9874304, by rfl⟩ : syracuseStep 13165739 = 19748609) B19748609
theorem B15819947 : Blo 770335 15819947 := bstep (se 1 (by rfl) ⟨11864960, by rfl⟩ : syracuseStep 15819947 = 23729921) B23729921
theorem B1238249 : Blo 770335 1238249 := bstep (se 2 (by rfl) ⟨464343, by rfl⟩ : syracuseStep 1238249 = 928687) B928687
theorem B2778407 : Blo 770335 2778407 := bstep (se 1 (by rfl) ⟨2083805, by rfl⟩ : syracuseStep 2778407 = 4167611) B4167611
theorem B3302765 : Blo 770335 3302765 := bstep (se 3 (by rfl) ⟨619268, by rfl⟩ : syracuseStep 3302765 = 1238537) B1238537
theorem B1303931 : Blo 770335 1303931 := bstep (se 1 (by rfl) ⟨977948, by rfl⟩ : syracuseStep 1303931 = 1955897) B1955897
theorem B1959329 : Blo 770335 1959329 := bstep (se 2 (by rfl) ⟨734748, by rfl⟩ : syracuseStep 1959329 = 1469497) B1469497
theorem B2385769 : Blo 770335 2385769 := bstep (se 2 (by rfl) ⟨894663, by rfl⟩ : syracuseStep 2385769 = 1789327) B1789327
theorem B1959785 : Blo 770335 1959785 := bstep (se 2 (by rfl) ⟨734919, by rfl⟩ : syracuseStep 1959785 = 1469839) B1469839
theorem B8349875 : Blo 770335 8349875 := bstep (se 1 (by rfl) ⟨6262406, by rfl⟩ : syracuseStep 8349875 = 12524813) B12524813
theorem B1304923 : Blo 770335 1304923 := bstep (se 1 (by rfl) ⟨978692, by rfl⟩ : syracuseStep 1304923 = 1957385) B1957385
theorem B1468783 : Blo 770335 1468783 := bstep (se 1 (by rfl) ⟨1101587, by rfl⟩ : syracuseStep 1468783 = 2203175) B2203175
theorem B977275 : Blo 770335 977275 := bstep (se 1 (by rfl) ⟨732956, by rfl⟩ : syracuseStep 977275 = 1465913) B1465913
theorem B6252967 : Blo 770335 6252967 := bstep (se 1 (by rfl) ⟨4689725, by rfl⟩ : syracuseStep 6252967 = 9379451) B9379451
theorem B2779559 : Blo 770335 2779559 := bstep (se 1 (by rfl) ⟨2084669, by rfl⟩ : syracuseStep 2779559 = 4169339) B4169339
theorem B2091599 : Blo 770335 2091599 := bstep (se 1 (by rfl) ⟨1568699, by rfl⟩ : syracuseStep 2091599 = 3137399) B3137399
theorem B977503 : Blo 770335 977503 := bstep (se 1 (by rfl) ⟨733127, by rfl⟩ : syracuseStep 977503 = 1466255) B1466255
theorem B1305895 : Blo 770335 1305895 := bstep (se 1 (by rfl) ⟨979421, by rfl⟩ : syracuseStep 1305895 = 1958843) B1958843
theorem B1306415 : Blo 770335 1306415 := bstep (se 1 (by rfl) ⟨979811, by rfl⟩ : syracuseStep 1306415 = 1959623) B1959623
theorem B978743 : Blo 770335 978743 := bstep (se 1 (by rfl) ⟨734057, by rfl⟩ : syracuseStep 978743 = 1468115) B1468115
theorem B978895 : Blo 770335 978895 := bstep (se 1 (by rfl) ⟨734171, by rfl⟩ : syracuseStep 978895 = 1468343) B1468343
theorem B9892043 : Blo 770335 9892043 := bstep (se 1 (by rfl) ⟨7419032, by rfl⟩ : syracuseStep 9892043 = 14838065) B14838065
theorem B6681149 : Blo 770335 6681149 := bstep (se 3 (by rfl) ⟨1252715, by rfl⟩ : syracuseStep 6681149 = 2505431) B2505431
theorem B1733291 : Blo 770335 1733291 := bstep (se 1 (by rfl) ⟨1299968, by rfl⟩ : syracuseStep 1733291 = 2599937) B2599937
theorem B12546737 : Blo 770335 12546737 := bstep (se 2 (by rfl) ⟨4705026, by rfl⟩ : syracuseStep 12546737 = 9410053) B9410053
theorem B1176475 : Blo 770335 1176475 := bstep (se 1 (by rfl) ⟨882356, by rfl⟩ : syracuseStep 1176475 = 1764713) B1764713
theorem B979867 : Blo 770335 979867 := bstep (se 1 (by rfl) ⟨734900, by rfl⟩ : syracuseStep 979867 = 1469801) B1469801
theorem B1733831 : Blo 770335 1733831 := bstep (se 1 (by rfl) ⟨1300373, by rfl⟩ : syracuseStep 1733831 = 2600747) B2600747
theorem B5567737 : Blo 770335 5567737 := bstep (se 2 (by rfl) ⟨2087901, by rfl⟩ : syracuseStep 5567737 = 4175803) B4175803
theorem B1734011 : Blo 770335 1734011 := bstep (se 1 (by rfl) ⟨1300508, by rfl⟩ : syracuseStep 1734011 = 2601017) B2601017
theorem B1734137 : Blo 770335 1734137 := bstep (se 2 (by rfl) ⟨650301, by rfl⟩ : syracuseStep 1734137 = 1300603) B1300603
theorem B1734227 : Blo 770335 1734227 := bstep (se 1 (by rfl) ⟨1300670, by rfl⟩ : syracuseStep 1734227 = 2601341) B2601341
theorem B1734407 : Blo 770335 1734407 := bstep (se 1 (by rfl) ⟨1300805, by rfl⟩ : syracuseStep 1734407 = 2601611) B2601611
theorem B1735019 : Blo 770335 1735019 := bstep (se 1 (by rfl) ⟨1301264, by rfl⟩ : syracuseStep 1735019 = 2602529) B2602529
theorem B1735163 : Blo 770335 1735163 := bstep (se 1 (by rfl) ⟨1301372, by rfl⟩ : syracuseStep 1735163 = 2602745) B2602745
theorem B1735289 : Blo 770335 1735289 := bstep (se 2 (by rfl) ⟨650733, by rfl⟩ : syracuseStep 1735289 = 1301467) B1301467
theorem B5864075 : Blo 770335 5864075 := bstep (se 1 (by rfl) ⟨4398056, by rfl⟩ : syracuseStep 5864075 = 8796113) B8796113
theorem B1735343 : Blo 770335 1735343 := bstep (se 1 (by rfl) ⟨1301507, by rfl⟩ : syracuseStep 1735343 = 2603015) B2603015
theorem B1735415 : Blo 770335 1735415 := bstep (se 1 (by rfl) ⟨1301561, by rfl⟩ : syracuseStep 1735415 = 2603123) B2603123
theorem B1735595 : Blo 770335 1735595 := bstep (se 1 (by rfl) ⟨1301696, by rfl⟩ : syracuseStep 1735595 = 2603393) B2603393
theorem B7044259 : Blo 770335 7044259 := bstep (se 1 (by rfl) ⟨5283194, by rfl⟩ : syracuseStep 7044259 = 10566389) B10566389
theorem B1736135 : Blo 770335 1736135 := bstep (se 1 (by rfl) ⟨1302101, by rfl⟩ : syracuseStep 1736135 = 2604203) B2604203
theorem B1736495 : Blo 770335 1736495 := bstep (se 1 (by rfl) ⟨1302371, by rfl⟩ : syracuseStep 1736495 = 2604743) B2604743
theorem B8815067 : Blo 770335 8815067 := bstep (se 1 (by rfl) ⟨6611300, by rfl⟩ : syracuseStep 8815067 = 13222601) B13222601
theorem B1737683 : Blo 770335 1737683 := bstep (se 1 (by rfl) ⟨1303262, by rfl⟩ : syracuseStep 1737683 = 2606525) B2606525
theorem B2196467 : Blo 770335 2196467 := bstep (se 1 (by rfl) ⟨1647350, by rfl⟩ : syracuseStep 2196467 = 3294701) B3294701
theorem B63374339 : Blo 770335 63374339 := bstep (se 1 (by rfl) ⟨47530754, by rfl⟩ : syracuseStep 63374339 = 95061509) B95061509
theorem B1737935 : Blo 770335 1737935 := bstep (se 1 (by rfl) ⟨1303451, by rfl⟩ : syracuseStep 1737935 = 2606903) B2606903
theorem B4392407 : Blo 770335 4392407 := bstep (se 1 (by rfl) ⟨3294305, by rfl⟩ : syracuseStep 4392407 = 6588611) B6588611
theorem B1738259 : Blo 770335 1738259 := bstep (se 1 (by rfl) ⟨1303694, by rfl⟩ : syracuseStep 1738259 = 2607389) B2607389
theorem B42239717 : Blo 770335 42239717 := bstep (se 4 (by rfl) ⟨3959973, by rfl⟩ : syracuseStep 42239717 = 7919947) B7919947
theorem B1738943 : Blo 770335 1738943 := bstep (se 1 (by rfl) ⟨1304207, by rfl⟩ : syracuseStep 1738943 = 2608415) B2608415
theorem B2197799 : Blo 770335 2197799 := bstep (se 1 (by rfl) ⟨1648349, by rfl⟩ : syracuseStep 2197799 = 3296699) B3296699
theorem B5572955 : Blo 770335 5572955 := bstep (se 1 (by rfl) ⟨4179716, by rfl⟩ : syracuseStep 5572955 = 8359433) B8359433
theorem B3181025 : Blo 770335 3181025 := bstep (se 2 (by rfl) ⟨1192884, by rfl⟩ : syracuseStep 3181025 = 2385769) B2385769
theorem B5868449 : Blo 770335 5868449 := bstep (se 2 (by rfl) ⟨2200668, by rfl⟩ : syracuseStep 5868449 = 4401337) B4401337
theorem B1739897 : Blo 770335 1739897 := bstep (se 2 (by rfl) ⟨652461, by rfl⟩ : syracuseStep 1739897 = 1304923) B1304923
theorem B3902903 : Blo 770335 3902903 := bstep (se 1 (by rfl) ⟨2927177, by rfl⟩ : syracuseStep 3902903 = 5854355) B5854355
theorem B3903065 : Blo 770335 3903065 := bstep (se 2 (by rfl) ⟨1463649, by rfl⟩ : syracuseStep 3903065 = 2927299) B2927299
theorem B1740563 : Blo 770335 1740563 := bstep (se 1 (by rfl) ⟨1305422, by rfl⟩ : syracuseStep 1740563 = 2610845) B2610845
theorem B1740923 : Blo 770335 1740923 := bstep (se 1 (by rfl) ⟨1305692, by rfl⟩ : syracuseStep 1740923 = 2611385) B2611385
theorem B7049369 : Blo 770335 7049369 := bstep (se 2 (by rfl) ⟨2643513, by rfl⟩ : syracuseStep 7049369 = 5287027) B5287027
theorem B1741193 : Blo 770335 1741193 := bstep (se 2 (by rfl) ⟨652947, by rfl⟩ : syracuseStep 1741193 = 1305895) B1305895
theorem B6591071 : Blo 770335 6591071 := bstep (se 1 (by rfl) ⟨4943303, by rfl⟩ : syracuseStep 6591071 = 9886607) B9886607
theorem B122131235 : Blo 770335 122131235 := bstep (se 1 (by rfl) ⟨91598426, by rfl⟩ : syracuseStep 122131235 = 183196853) B183196853
theorem B42374117 : Blo 770335 42374117 := bstep (se 4 (by rfl) ⟨3972573, by rfl⟩ : syracuseStep 42374117 = 7945147) B7945147
theorem B1741931 : Blo 770335 1741931 := bstep (se 1 (by rfl) ⟨1306448, by rfl⟩ : syracuseStep 1741931 = 2612897) B2612897
theorem B2200715 : Blo 770335 2200715 := bstep (se 1 (by rfl) ⟨1650536, by rfl⟩ : syracuseStep 2200715 = 3301073) B3301073
theorem B4461743 : Blo 770335 4461743 := bstep (se 1 (by rfl) ⟨3346307, by rfl⟩ : syracuseStep 4461743 = 6692615) B6692615
theorem B5870879 : Blo 770335 5870879 := bstep (se 1 (by rfl) ⟨4403159, by rfl⟩ : syracuseStep 5870879 = 8806319) B8806319
theorem B5575979 : Blo 770335 5575979 := bstep (se 1 (by rfl) ⟨4181984, by rfl⟩ : syracuseStep 5575979 = 8363969) B8363969
theorem B2201057 : Blo 770335 2201057 := bstep (se 2 (by rfl) ⟨825396, by rfl⟩ : syracuseStep 2201057 = 1650793) B1650793
theorem B3905495 : Blo 770335 3905495 := bstep (se 1 (by rfl) ⟨2929121, by rfl⟩ : syracuseStep 3905495 = 5858243) B5858243
theorem B11147345 : Blo 770335 11147345 := bstep (se 2 (by rfl) ⟨4180254, by rfl⟩ : syracuseStep 11147345 = 8360509) B8360509
theorem B825439 : Blo 770335 825439 := bstep (se 1 (by rfl) ⟨619079, by rfl⟩ : syracuseStep 825439 = 1238159) B1238159
theorem B825499 : Blo 770335 825499 := bstep (se 1 (by rfl) ⟨619124, by rfl⟩ : syracuseStep 825499 = 1238249) B1238249
theorem B2201843 : Blo 770335 2201843 := bstep (se 1 (by rfl) ⟨1651382, by rfl⟩ : syracuseStep 2201843 = 3302765) B3302765
theorem B14096681 : Blo 770335 14096681 := bstep (se 2 (by rfl) ⟨5286255, by rfl⟩ : syracuseStep 14096681 = 10572511) B10572511
theorem B3905981 : Blo 770335 3905981 := bstep (se 3 (by rfl) ⟨732371, by rfl⟩ : syracuseStep 3905981 = 1464743) B1464743
theorem B10558289 : Blo 770335 10558289 := bstep (se 2 (by rfl) ⟨3959358, by rfl⟩ : syracuseStep 10558289 = 7918717) B7918717
theorem B4070249 : Blo 770335 4070249 := bstep (se 2 (by rfl) ⟨1526343, by rfl⟩ : syracuseStep 4070249 = 3052687) B3052687
theorem B5577943 : Blo 770335 5577943 := bstep (se 1 (by rfl) ⟨4183457, by rfl⟩ : syracuseStep 5577943 = 8366915) B8366915
theorem B10690127 : Blo 770335 10690127 := bstep (se 1 (by rfl) ⟨8017595, by rfl⟩ : syracuseStep 10690127 = 16035191) B16035191
theorem B2203517 : Blo 770335 2203517 := bstep (se 3 (by rfl) ⟨413159, by rfl⟩ : syracuseStep 2203517 = 826319) B826319
theorem B6594695 : Blo 770335 6594695 := bstep (se 1 (by rfl) ⟨4946021, by rfl⟩ : syracuseStep 6594695 = 9892043) B9892043
theorem B1155527 : Blo 770335 1155527 := bstep (se 1 (by rfl) ⟨866645, by rfl⟩ : syracuseStep 1155527 = 1733291) B1733291
theorem B8364491 : Blo 770335 8364491 := bstep (se 1 (by rfl) ⟨6273368, by rfl⟩ : syracuseStep 8364491 = 12546737) B12546737
theorem B1319375 : Blo 770335 1319375 := bstep (se 1 (by rfl) ⟨989531, by rfl⟩ : syracuseStep 1319375 = 1979063) B1979063
theorem B1155881 : Blo 770335 1155881 := bstep (se 2 (by rfl) ⟨433455, by rfl⟩ : syracuseStep 1155881 = 866911) B866911
theorem B1155887 : Blo 770335 1155887 := bstep (se 1 (by rfl) ⟨866915, by rfl⟩ : syracuseStep 1155887 = 1733831) B1733831
theorem B1156007 : Blo 770335 1156007 := bstep (se 1 (by rfl) ⟨867005, by rfl⟩ : syracuseStep 1156007 = 1734011) B1734011
theorem B1156091 : Blo 770335 1156091 := bstep (se 1 (by rfl) ⟨867068, by rfl⟩ : syracuseStep 1156091 = 1734137) B1734137
theorem B18359297 : Blo 770335 18359297 := bstep (se 2 (by rfl) ⟨6884736, by rfl⟩ : syracuseStep 18359297 = 13769473) B13769473
theorem B4400153 : Blo 770335 4400153 := bstep (se 2 (by rfl) ⟨1650057, by rfl⟩ : syracuseStep 4400153 = 3300115) B3300115
theorem B1156151 : Blo 770335 1156151 := bstep (se 1 (by rfl) ⟨867113, by rfl⟩ : syracuseStep 1156151 = 1734227) B1734227
theorem B1156271 : Blo 770335 1156271 := bstep (se 1 (by rfl) ⟨867203, by rfl⟩ : syracuseStep 1156271 = 1734407) B1734407
theorem B25044157 : Blo 770335 25044157 := bstep (se 3 (by rfl) ⟨4695779, by rfl⟩ : syracuseStep 25044157 = 9391559) B9391559
theorem B1156679 : Blo 770335 1156679 := bstep (se 1 (by rfl) ⟨867509, by rfl⟩ : syracuseStep 1156679 = 1735019) B1735019
theorem B1156775 : Blo 770335 1156775 := bstep (se 1 (by rfl) ⟨867581, by rfl⟩ : syracuseStep 1156775 = 1735163) B1735163
theorem B992935 : Blo 770335 992935 := bstep (se 1 (by rfl) ⟨744701, by rfl⟩ : syracuseStep 992935 = 1489403) B1489403
theorem B8791739 : Blo 770335 8791739 := bstep (se 1 (by rfl) ⟨6593804, by rfl⟩ : syracuseStep 8791739 = 13187609) B13187609
theorem B1156859 : Blo 770335 1156859 := bstep (se 1 (by rfl) ⟨867644, by rfl⟩ : syracuseStep 1156859 = 1735289) B1735289
theorem B3909383 : Blo 770335 3909383 := bstep (se 1 (by rfl) ⟨2932037, by rfl⟩ : syracuseStep 3909383 = 5864075) B5864075
theorem B1156895 : Blo 770335 1156895 := bstep (se 1 (by rfl) ⟨867671, by rfl⟩ : syracuseStep 1156895 = 1735343) B1735343
theorem B1156943 : Blo 770335 1156943 := bstep (se 1 (by rfl) ⟨867707, by rfl⟩ : syracuseStep 1156943 = 1735415) B1735415
theorem B1157063 : Blo 770335 1157063 := bstep (se 1 (by rfl) ⟨867797, by rfl⟩ : syracuseStep 1157063 = 1735595) B1735595
theorem B1157417 : Blo 770335 1157417 := bstep (se 2 (by rfl) ⟨434031, by rfl⟩ : syracuseStep 1157417 = 868063) B868063
theorem B1157423 : Blo 770335 1157423 := bstep (se 1 (by rfl) ⟨868067, by rfl⟩ : syracuseStep 1157423 = 1736135) B1736135
theorem B1648991 : Blo 770335 1648991 := bstep (se 1 (by rfl) ⟨1236743, by rfl⟩ : syracuseStep 1648991 = 2473487) B2473487
theorem B5876225 : Blo 770335 5876225 := bstep (se 2 (by rfl) ⟨2203584, by rfl⟩ : syracuseStep 5876225 = 4407169) B4407169
theorem B1157663 : Blo 770335 1157663 := bstep (se 1 (by rfl) ⟨868247, by rfl⟩ : syracuseStep 1157663 = 1736495) B1736495
theorem B1158047 : Blo 770335 1158047 := bstep (se 1 (by rfl) ⟨868535, by rfl⟩ : syracuseStep 1158047 = 1737071) B1737071
theorem B1158095 : Blo 770335 1158095 := bstep (se 1 (by rfl) ⟨868571, by rfl⟩ : syracuseStep 1158095 = 1737143) B1737143
theorem B1158185 : Blo 770335 1158185 := bstep (se 2 (by rfl) ⟨434319, by rfl⟩ : syracuseStep 1158185 = 868639) B868639
theorem B1158191 : Blo 770335 1158191 := bstep (se 1 (by rfl) ⟨868643, by rfl⟩ : syracuseStep 1158191 = 1737287) B1737287
theorem B1158215 : Blo 770335 1158215 := bstep (se 1 (by rfl) ⟨868661, by rfl⟩ : syracuseStep 1158215 = 1737323) B1737323
theorem B5287133 : Blo 770335 5287133 := bstep (se 3 (by rfl) ⟨991337, by rfl⟩ : syracuseStep 5287133 = 1982675) B1982675
theorem B1158479 : Blo 770335 1158479 := bstep (se 1 (by rfl) ⟨868859, by rfl⟩ : syracuseStep 1158479 = 1737719) B1737719
theorem B2600315 : Blo 770335 2600315 := bstep (se 1 (by rfl) ⟨1950236, by rfl⟩ : syracuseStep 2600315 = 3900473) B3900473
theorem B1158569 : Blo 770335 1158569 := bstep (se 2 (by rfl) ⟨434463, by rfl⟩ : syracuseStep 1158569 = 868927) B868927
theorem B1158719 : Blo 770335 1158719 := bstep (se 1 (by rfl) ⟨869039, by rfl⟩ : syracuseStep 1158719 = 1738079) B1738079
theorem B1650451 : Blo 770335 1650451 := bstep (se 1 (by rfl) ⟨1237838, by rfl⟩ : syracuseStep 1650451 = 2475677) B2475677
theorem B1158983 : Blo 770335 1158983 := bstep (se 1 (by rfl) ⟨869237, by rfl⟩ : syracuseStep 1158983 = 1738475) B1738475
theorem B1159067 : Blo 770335 1159067 := bstep (se 1 (by rfl) ⟨869300, by rfl⟩ : syracuseStep 1159067 = 1738601) B1738601
theorem B1388459 : Blo 770335 1388459 := bstep (se 1 (by rfl) ⟨1041344, by rfl⟩ : syracuseStep 1388459 = 2082689) B2082689
theorem B1389007 : Blo 770335 1389007 := bstep (se 1 (by rfl) ⟨1041755, by rfl⟩ : syracuseStep 1389007 = 2083511) B2083511
theorem B1159631 : Blo 770335 1159631 := bstep (se 1 (by rfl) ⟨869723, by rfl⟩ : syracuseStep 1159631 = 1739447) B1739447
theorem B1159673 : Blo 770335 1159673 := bstep (se 2 (by rfl) ⟨434877, by rfl⟩ : syracuseStep 1159673 = 869755) B869755
theorem B5026319 : Blo 770335 5026319 := bstep (se 1 (by rfl) ⟨3769739, by rfl⟩ : syracuseStep 5026319 = 7539479) B7539479
theorem B1159775 : Blo 770335 1159775 := bstep (se 1 (by rfl) ⟨869831, by rfl⟩ : syracuseStep 1159775 = 1739663) B1739663
theorem B2601719 : Blo 770335 2601719 := bstep (se 1 (by rfl) ⟨1951289, by rfl⟩ : syracuseStep 2601719 = 3902579) B3902579
theorem B4961195 : Blo 770335 4961195 := bstep (se 1 (by rfl) ⟨3720896, by rfl⟩ : syracuseStep 4961195 = 7441793) B7441793
theorem B1160255 : Blo 770335 1160255 := bstep (se 1 (by rfl) ⟨870191, by rfl⟩ : syracuseStep 1160255 = 1740383) B1740383
theorem B1160297 : Blo 770335 1160297 := bstep (se 2 (by rfl) ⟨435111, by rfl⟩ : syracuseStep 1160297 = 870223) B870223
theorem B6599819 : Blo 770335 6599819 := bstep (se 1 (by rfl) ⟨4949864, by rfl⟩ : syracuseStep 6599819 = 9899729) B9899729
theorem B1160399 : Blo 770335 1160399 := bstep (se 1 (by rfl) ⟨870299, by rfl⟩ : syracuseStep 1160399 = 1740599) B1740599
theorem B2602259 : Blo 770335 2602259 := bstep (se 1 (by rfl) ⟨1951694, by rfl⟩ : syracuseStep 2602259 = 3903389) B3903389
theorem B1160603 : Blo 770335 1160603 := bstep (se 1 (by rfl) ⟨870452, by rfl⟩ : syracuseStep 1160603 = 1740905) B1740905
theorem B1160825 : Blo 770335 1160825 := bstep (se 2 (by rfl) ⟨435309, by rfl⟩ : syracuseStep 1160825 = 870619) B870619
theorem B1160927 : Blo 770335 1160927 := bstep (se 1 (by rfl) ⟨870695, by rfl⟩ : syracuseStep 1160927 = 1741391) B1741391
theorem B2602799 : Blo 770335 2602799 := bstep (se 1 (by rfl) ⟨1952099, by rfl⟩ : syracuseStep 2602799 = 3904199) B3904199
theorem B1161023 : Blo 770335 1161023 := bstep (se 1 (by rfl) ⟨870767, by rfl⟩ : syracuseStep 1161023 = 1741535) B1741535
theorem B8337289 : Blo 770335 8337289 := bstep (se 2 (by rfl) ⟨3126483, by rfl⟩ : syracuseStep 8337289 = 6252967) B6252967
theorem B4405211 : Blo 770335 4405211 := bstep (se 1 (by rfl) ⟨3303908, by rfl⟩ : syracuseStep 4405211 = 6607817) B6607817
theorem B1161191 : Blo 770335 1161191 := bstep (se 1 (by rfl) ⟨870893, by rfl⟩ : syracuseStep 1161191 = 1741787) B1741787
theorem B1161209 : Blo 770335 1161209 := bstep (se 2 (by rfl) ⟨435453, by rfl⟩ : syracuseStep 1161209 = 870907) B870907
theorem B1161311 : Blo 770335 1161311 := bstep (se 1 (by rfl) ⟨870983, by rfl⟩ : syracuseStep 1161311 = 1741967) B1741967
theorem B1161371 : Blo 770335 1161371 := bstep (se 1 (by rfl) ⟨871028, by rfl⟩ : syracuseStep 1161371 = 1742057) B1742057
theorem B1161407 : Blo 770335 1161407 := bstep (se 1 (by rfl) ⟨871055, by rfl⟩ : syracuseStep 1161407 = 1742111) B1742111
theorem B1161449 : Blo 770335 1161449 := bstep (se 2 (by rfl) ⟨435543, by rfl⟩ : syracuseStep 1161449 = 871087) B871087
theorem B2636441 : Blo 770335 2636441 := bstep (se 2 (by rfl) ⟨988665, by rfl⟩ : syracuseStep 2636441 = 1977331) B1977331
theorem B2472601 : Blo 770335 2472601 := bstep (se 2 (by rfl) ⟨927225, by rfl⟩ : syracuseStep 2472601 = 1854451) B1854451
theorem B5552975 : Blo 770335 5552975 := bstep (se 1 (by rfl) ⟨4164731, by rfl⟩ : syracuseStep 5552975 = 8329463) B8329463
theorem B867163 : Blo 770335 867163 := bstep (se 1 (by rfl) ⟨650372, by rfl⟩ : syracuseStep 867163 = 1300745) B1300745
theorem B2931977 : Blo 770335 2931977 := bstep (se 2 (by rfl) ⟨1099491, by rfl⟩ : syracuseStep 2931977 = 2198983) B2198983
theorem B2637095 : Blo 770335 2637095 := bstep (se 1 (by rfl) ⟨1977821, by rfl⟩ : syracuseStep 2637095 = 3955643) B3955643
theorem B2604635 : Blo 770335 2604635 := bstep (se 1 (by rfl) ⟨1953476, by rfl⟩ : syracuseStep 2604635 = 3906953) B3906953
theorem B868135 : Blo 770335 868135 := bstep (se 1 (by rfl) ⟨651101, by rfl⟩ : syracuseStep 868135 = 1302203) B1302203
theorem B20070433 : Blo 770335 20070433 := bstep (se 2 (by rfl) ⟨7526412, by rfl⟩ : syracuseStep 20070433 = 15052825) B15052825
theorem B20299855 : Blo 770335 20299855 := bstep (se 1 (by rfl) ⟨15224891, by rfl⟩ : syracuseStep 20299855 = 30449783) B30449783
theorem B2605337 : Blo 770335 2605337 := bstep (se 2 (by rfl) ⟨977001, by rfl⟩ : syracuseStep 2605337 = 1954003) B1954003
theorem B2113823 : Blo 770335 2113823 := bstep (se 1 (by rfl) ⟨1585367, by rfl⟩ : syracuseStep 2113823 = 3170735) B3170735
theorem B770431 : Blo 770335 770431 := bstep (se 1 (by rfl) ⟨577823, by rfl⟩ : syracuseStep 770431 = 1155647) B1155647
theorem B2605499 : Blo 770335 2605499 := bstep (se 1 (by rfl) ⟨1954124, by rfl⟩ : syracuseStep 2605499 = 3908249) B3908249
theorem B2343367 : Blo 770335 2343367 := bstep (se 1 (by rfl) ⟨1757525, by rfl⟩ : syracuseStep 2343367 = 3515051) B3515051
theorem B770511 : Blo 770335 770511 := bstep (se 1 (by rfl) ⟨577883, by rfl⟩ : syracuseStep 770511 = 1155767) B1155767
theorem B3293759 : Blo 770335 3293759 := bstep (se 1 (by rfl) ⟨2470319, by rfl⟩ : syracuseStep 3293759 = 4940639) B4940639
theorem B770663 : Blo 770335 770663 := bstep (se 1 (by rfl) ⟨577997, by rfl⟩ : syracuseStep 770663 = 1155995) B1155995
theorem B1852271 : Blo 770335 1852271 := bstep (se 1 (by rfl) ⟨1389203, by rfl⟩ : syracuseStep 1852271 = 2778407) B2778407
theorem B770927 : Blo 770335 770927 := bstep (se 1 (by rfl) ⟨578195, by rfl⟩ : syracuseStep 770927 = 1156391) B1156391
theorem B770983 : Blo 770335 770983 := bstep (se 1 (by rfl) ⟨578237, by rfl⟩ : syracuseStep 770983 = 1156475) B1156475
theorem B869287 : Blo 770335 869287 := bstep (se 1 (by rfl) ⟨651965, by rfl⟩ : syracuseStep 869287 = 1303931) B1303931
theorem B771067 : Blo 770335 771067 := bstep (se 1 (by rfl) ⟨578300, by rfl⟩ : syracuseStep 771067 = 1156601) B1156601
theorem B771135 : Blo 770335 771135 := bstep (se 1 (by rfl) ⟨578351, by rfl⟩ : syracuseStep 771135 = 1156703) B1156703
theorem B4408445 : Blo 770335 4408445 := bstep (se 3 (by rfl) ⟨826583, by rfl⟩ : syracuseStep 4408445 = 1653167) B1653167
theorem B771279 : Blo 770335 771279 := bstep (se 1 (by rfl) ⟨578459, by rfl⟩ : syracuseStep 771279 = 1156919) B1156919
theorem B53495113 : Blo 770335 53495113 := bstep (se 2 (by rfl) ⟨20060667, by rfl⟩ : syracuseStep 53495113 = 40121335) B40121335
theorem B2934089 : Blo 770335 2934089 := bstep (se 2 (by rfl) ⟨1100283, by rfl⟩ : syracuseStep 2934089 = 2200567) B2200567
theorem B1099099 : Blo 770335 1099099 := bstep (se 1 (by rfl) ⟨824324, by rfl⟩ : syracuseStep 1099099 = 1648649) B1648649
theorem B771483 : Blo 770335 771483 := bstep (se 1 (by rfl) ⟨578612, by rfl⟩ : syracuseStep 771483 = 1157225) B1157225
theorem B6604193 : Blo 770335 6604193 := bstep (se 2 (by rfl) ⟨2476572, by rfl⟩ : syracuseStep 6604193 = 4953145) B4953145
theorem B30033341 : Blo 770335 30033341 := bstep (se 3 (by rfl) ⟨5631251, by rfl⟩ : syracuseStep 30033341 = 11262503) B11262503
theorem B2606687 : Blo 770335 2606687 := bstep (se 1 (by rfl) ⟨1955015, by rfl⟩ : syracuseStep 2606687 = 3910031) B3910031
theorem B1853039 : Blo 770335 1853039 := bstep (se 1 (by rfl) ⟨1389779, by rfl⟩ : syracuseStep 1853039 = 2779559) B2779559
theorem B771695 : Blo 770335 771695 := bstep (se 1 (by rfl) ⟨578771, by rfl⟩ : syracuseStep 771695 = 1157543) B1157543
theorem B6342259 : Blo 770335 6342259 := bstep (se 1 (by rfl) ⟨4756694, by rfl⟩ : syracuseStep 6342259 = 9513389) B9513389
theorem B7423649 : Blo 770335 7423649 := bstep (se 2 (by rfl) ⟨2783868, by rfl⟩ : syracuseStep 7423649 = 5567737) B5567737
theorem B771751 : Blo 770335 771751 := bstep (se 1 (by rfl) ⟨578813, by rfl⟩ : syracuseStep 771751 = 1157627) B1157627
theorem B1394399 : Blo 770335 1394399 := bstep (se 1 (by rfl) ⟨1045799, by rfl⟩ : syracuseStep 1394399 = 2091599) B2091599
theorem B771835 : Blo 770335 771835 := bstep (se 1 (by rfl) ⟨578876, by rfl⟩ : syracuseStep 771835 = 1157753) B1157753
theorem B771871 : Blo 770335 771871 := bstep (se 1 (by rfl) ⟨578903, by rfl⟩ : syracuseStep 771871 = 1157807) B1157807
theorem B2934589 : Blo 770335 2934589 := bstep (se 3 (by rfl) ⟨550235, by rfl⟩ : syracuseStep 2934589 = 1100471) B1100471
theorem B771903 : Blo 770335 771903 := bstep (se 1 (by rfl) ⟨578927, by rfl⟩ : syracuseStep 771903 = 1157855) B1157855
theorem B772079 : Blo 770335 772079 := bstep (se 1 (by rfl) ⟨579059, by rfl⟩ : syracuseStep 772079 = 1158119) B1158119
theorem B1951735 : Blo 770335 1951735 := bstep (se 1 (by rfl) ⟨1463801, by rfl⟩ : syracuseStep 1951735 = 2927603) B2927603
theorem B772251 : Blo 770335 772251 := bstep (se 1 (by rfl) ⟨579188, by rfl⟩ : syracuseStep 772251 = 1158377) B1158377
theorem B772287 : Blo 770335 772287 := bstep (se 1 (by rfl) ⟨579215, by rfl⟩ : syracuseStep 772287 = 1158431) B1158431
theorem B1952039 : Blo 770335 1952039 := bstep (se 1 (by rfl) ⟨1464029, by rfl⟩ : syracuseStep 1952039 = 2928059) B2928059
theorem B772399 : Blo 770335 772399 := bstep (se 1 (by rfl) ⟨579299, by rfl⟩ : syracuseStep 772399 = 1158599) B1158599
theorem B772635 : Blo 770335 772635 := bstep (se 1 (by rfl) ⟨579476, by rfl⟩ : syracuseStep 772635 = 1158953) B1158953
theorem B772639 : Blo 770335 772639 := bstep (se 1 (by rfl) ⟨579479, by rfl⟩ : syracuseStep 772639 = 1158959) B1158959
theorem B870943 : Blo 770335 870943 := bstep (se 1 (by rfl) ⟨653207, by rfl⟩ : syracuseStep 870943 = 1306415) B1306415
theorem B2476727 : Blo 770335 2476727 := bstep (se 1 (by rfl) ⟨1857545, by rfl⟩ : syracuseStep 2476727 = 3715091) B3715091
theorem B772955 : Blo 770335 772955 := bstep (se 1 (by rfl) ⟨579716, by rfl⟩ : syracuseStep 772955 = 1159433) B1159433
theorem B773023 : Blo 770335 773023 := bstep (se 1 (by rfl) ⟨579767, by rfl⟩ : syracuseStep 773023 = 1159535) B1159535
theorem B2608091 : Blo 770335 2608091 := bstep (se 1 (by rfl) ⟨1956068, by rfl⟩ : syracuseStep 2608091 = 3912137) B3912137
theorem B773167 : Blo 770335 773167 := bstep (se 1 (by rfl) ⟨579875, by rfl⟩ : syracuseStep 773167 = 1159751) B1159751
theorem B773191 : Blo 770335 773191 := bstep (se 1 (by rfl) ⟨579893, by rfl⟩ : syracuseStep 773191 = 1159787) B1159787
theorem B2477279 : Blo 770335 2477279 := bstep (se 1 (by rfl) ⟨1857959, by rfl⟩ : syracuseStep 2477279 = 3715919) B3715919
theorem B773343 : Blo 770335 773343 := bstep (se 1 (by rfl) ⟨580007, by rfl⟩ : syracuseStep 773343 = 1160015) B1160015
theorem B2608361 : Blo 770335 2608361 := bstep (se 2 (by rfl) ⟨978135, by rfl⟩ : syracuseStep 2608361 = 1956271) B1956271
theorem B1101223 : Blo 770335 1101223 := bstep (se 1 (by rfl) ⟨825917, by rfl⟩ : syracuseStep 1101223 = 1651835) B1651835
theorem B1953193 : Blo 770335 1953193 := bstep (se 2 (by rfl) ⟨732447, by rfl⟩ : syracuseStep 1953193 = 1464895) B1464895
theorem B773607 : Blo 770335 773607 := bstep (se 1 (by rfl) ⟨580205, by rfl⟩ : syracuseStep 773607 = 1160411) B1160411
theorem B2608631 : Blo 770335 2608631 := bstep (se 1 (by rfl) ⟨1956473, by rfl⟩ : syracuseStep 2608631 = 3912947) B3912947
theorem B773723 : Blo 770335 773723 := bstep (se 1 (by rfl) ⟨580292, by rfl⟩ : syracuseStep 773723 = 1160585) B1160585
theorem B773959 : Blo 770335 773959 := bstep (se 1 (by rfl) ⟨580469, by rfl⟩ : syracuseStep 773959 = 1160939) B1160939
theorem B1953679 : Blo 770335 1953679 := bstep (se 1 (by rfl) ⟨1465259, by rfl⟩ : syracuseStep 1953679 = 2930519) B2930519
theorem B774111 : Blo 770335 774111 := bstep (se 1 (by rfl) ⟨580583, by rfl⟩ : syracuseStep 774111 = 1161167) B1161167
theorem B2937019 : Blo 770335 2937019 := bstep (se 1 (by rfl) ⟨2202764, by rfl⟩ : syracuseStep 2937019 = 4405529) B4405529
theorem B9392345 : Blo 770335 9392345 := bstep (se 2 (by rfl) ⟨3522129, by rfl⟩ : syracuseStep 9392345 = 7044259) B7044259
theorem B1102043 : Blo 770335 1102043 := bstep (se 1 (by rfl) ⟨826532, by rfl⟩ : syracuseStep 1102043 = 1653065) B1653065
theorem B2609657 : Blo 770335 2609657 := bstep (se 2 (by rfl) ⟨978621, by rfl⟩ : syracuseStep 2609657 = 1957243) B1957243
theorem B2937505 : Blo 770335 2937505 := bstep (se 2 (by rfl) ⟨1101564, by rfl⟩ : syracuseStep 2937505 = 2203129) B2203129
theorem B2609927 : Blo 770335 2609927 := bstep (se 1 (by rfl) ⟨1957445, by rfl⟩ : syracuseStep 2609927 = 3914891) B3914891
theorem B1954601 : Blo 770335 1954601 := bstep (se 2 (by rfl) ⟨732975, by rfl⟩ : syracuseStep 1954601 = 1465951) B1465951
theorem B1856297 : Blo 770335 1856297 := bstep (se 2 (by rfl) ⟨696111, by rfl⟩ : syracuseStep 1856297 = 1392223) B1392223
theorem B2609981 : Blo 770335 2609981 := bstep (se 3 (by rfl) ⟨489371, by rfl⟩ : syracuseStep 2609981 = 978743) B978743
theorem B14865281 : Blo 770335 14865281 := bstep (se 2 (by rfl) ⟨5574480, by rfl⟩ : syracuseStep 14865281 = 11148961) B11148961
theorem B11162569 : Blo 770335 11162569 := bstep (se 2 (by rfl) ⟨4185963, by rfl⟩ : syracuseStep 11162569 = 8371927) B8371927
theorem B3527675 : Blo 770335 3527675 := bstep (se 1 (by rfl) ⟨2645756, by rfl⟩ : syracuseStep 3527675 = 5291513) B5291513
theorem B4937051 : Blo 770335 4937051 := bstep (se 1 (by rfl) ⟨3702788, by rfl⟩ : syracuseStep 4937051 = 7405577) B7405577
theorem B37574027 : Blo 770335 37574027 := bstep (se 1 (by rfl) ⟨28180520, by rfl⟩ : syracuseStep 37574027 = 56361041) B56361041
theorem B2938477 : Blo 770335 2938477 := bstep (se 3 (by rfl) ⟨550964, by rfl⟩ : syracuseStep 2938477 = 1101929) B1101929
theorem B1300151 : Blo 770335 1300151 := bstep (se 1 (by rfl) ⟨975113, by rfl⟩ : syracuseStep 1300151 = 1950227) B1950227
theorem B2611007 : Blo 770335 2611007 := bstep (se 1 (by rfl) ⟨1958255, by rfl⟩ : syracuseStep 2611007 = 3916511) B3916511
theorem B16701299 : Blo 770335 16701299 := bstep (se 1 (by rfl) ⟨12525974, by rfl⟩ : syracuseStep 16701299 = 25051949) B25051949
theorem B5855327 : Blo 770335 5855327 := bstep (se 1 (by rfl) ⟨4391495, by rfl⟩ : syracuseStep 5855327 = 8782991) B8782991
theorem B10148125 : Blo 770335 10148125 := bstep (se 3 (by rfl) ⟨1902773, by rfl⟩ : syracuseStep 10148125 = 3805547) B3805547
theorem B3299773 : Blo 770335 3299773 := bstep (se 3 (by rfl) ⟨618707, by rfl⟩ : syracuseStep 3299773 = 1237415) B1237415
theorem B3955499 : Blo 770335 3955499 := bstep (se 1 (by rfl) ⟨2966624, by rfl⟩ : syracuseStep 3955499 = 5933249) B5933249
theorem B42326833 : Blo 770335 42326833 := bstep (se 2 (by rfl) ⟨15872562, by rfl⟩ : syracuseStep 42326833 = 31745125) B31745125
theorem B1301339 : Blo 770335 1301339 := bstep (se 1 (by rfl) ⟨976004, by rfl⟩ : syracuseStep 1301339 = 1952009) B1952009
theorem B2939753 : Blo 770335 2939753 := bstep (se 2 (by rfl) ⟨1102407, by rfl⟩ : syracuseStep 2939753 = 2204815) B2204815
theorem B1301575 : Blo 770335 1301575 := bstep (se 1 (by rfl) ⟨976181, by rfl⟩ : syracuseStep 1301575 = 1952363) B1952363
theorem B1465609 : Blo 770335 1465609 := bstep (se 2 (by rfl) ⟨549603, by rfl⟩ : syracuseStep 1465609 = 1099207) B1099207
theorem B2612519 : Blo 770335 2612519 := bstep (se 1 (by rfl) ⟨1959389, by rfl⟩ : syracuseStep 2612519 = 3918779) B3918779
theorem B67788251 : Blo 770335 67788251 := bstep (se 1 (by rfl) ⟨50841188, by rfl⟩ : syracuseStep 67788251 = 101682377) B101682377
theorem B1236455 : Blo 770335 1236455 := bstep (se 1 (by rfl) ⟨927341, by rfl⟩ : syracuseStep 1236455 = 1854683) B1854683
theorem B1302007 : Blo 770335 1302007 := bstep (se 1 (by rfl) ⟨976505, by rfl⟩ : syracuseStep 1302007 = 1953011) B1953011
theorem B2645747 : Blo 770335 2645747 := bstep (se 1 (by rfl) ⟨1984310, by rfl⟩ : syracuseStep 2645747 = 3968621) B3968621
theorem B1302311 : Blo 770335 1302311 := bstep (se 1 (by rfl) ⟨976733, by rfl⟩ : syracuseStep 1302311 = 1953467) B1953467
theorem B3301175 : Blo 770335 3301175 := bstep (se 1 (by rfl) ⟨2475881, by rfl⟩ : syracuseStep 3301175 = 4951763) B4951763
theorem B2613383 : Blo 770335 2613383 := bstep (se 1 (by rfl) ⟨1960037, by rfl⟩ : syracuseStep 2613383 = 3920075) B3920075
theorem B4940023 : Blo 770335 4940023 := bstep (se 1 (by rfl) ⟨3705017, by rfl⟩ : syracuseStep 4940023 = 7410035) B7410035
theorem B1958377 : Blo 770335 1958377 := bstep (se 2 (by rfl) ⟨734391, by rfl⟩ : syracuseStep 1958377 = 1468783) B1468783
theorem B1303033 : Blo 770335 1303033 := bstep (se 2 (by rfl) ⟨488637, by rfl⟩ : syracuseStep 1303033 = 977275) B977275
theorem B97608401 : Blo 770335 97608401 := bstep (se 2 (by rfl) ⟨36603150, by rfl⟩ : syracuseStep 97608401 = 73206301) B73206301
theorem B1303303 : Blo 770335 1303303 := bstep (se 1 (by rfl) ⟨977477, by rfl⟩ : syracuseStep 1303303 = 1954955) B1954955
theorem B1303337 : Blo 770335 1303337 := bstep (se 2 (by rfl) ⟨488751, by rfl⟩ : syracuseStep 1303337 = 977503) B977503
theorem B1303607 : Blo 770335 1303607 := bstep (se 1 (by rfl) ⟨977705, by rfl⟩ : syracuseStep 1303607 = 1955411) B1955411
theorem B975979 : Blo 770335 975979 := bstep (se 1 (by rfl) ⟨731984, by rfl⟩ : syracuseStep 975979 = 1463969) B1463969
theorem B9889067 : Blo 770335 9889067 := bstep (se 1 (by rfl) ⟨7416800, by rfl⟩ : syracuseStep 9889067 = 14833601) B14833601
theorem B2090411 : Blo 770335 2090411 := bstep (se 1 (by rfl) ⟨1567808, by rfl⟩ : syracuseStep 2090411 = 3135617) B3135617
theorem B1762735 : Blo 770335 1762735 := bstep (se 1 (by rfl) ⟨1322051, by rfl⟩ : syracuseStep 1762735 = 2644103) B2644103
theorem B1304383 : Blo 770335 1304383 := bstep (se 1 (by rfl) ⟨978287, by rfl⟩ : syracuseStep 1304383 = 1956575) B1956575
theorem B2975891 : Blo 770335 2975891 := bstep (se 1 (by rfl) ⟨2231918, by rfl⟩ : syracuseStep 2975891 = 4463837) B4463837
theorem B3303737 : Blo 770335 3303737 := bstep (se 2 (by rfl) ⟨1238901, by rfl⟩ : syracuseStep 3303737 = 2477803) B2477803
theorem B43379003 : Blo 770335 43379003 := bstep (se 1 (by rfl) ⟨32534252, by rfl⟩ : syracuseStep 43379003 = 65068505) B65068505
theorem B1305119 : Blo 770335 1305119 := bstep (se 1 (by rfl) ⟨978839, by rfl⟩ : syracuseStep 1305119 = 1957679) B1957679
theorem B1305193 : Blo 770335 1305193 := bstep (se 2 (by rfl) ⟨489447, by rfl⟩ : syracuseStep 1305193 = 978895) B978895
theorem B1305551 : Blo 770335 1305551 := bstep (se 1 (by rfl) ⟨979163, by rfl⟩ : syracuseStep 1305551 = 1958327) B1958327
theorem B8777159 : Blo 770335 8777159 := bstep (se 1 (by rfl) ⟨6582869, by rfl⟩ : syracuseStep 8777159 = 13165739) B13165739
theorem B10546631 : Blo 770335 10546631 := bstep (se 1 (by rfl) ⟨7909973, by rfl⟩ : syracuseStep 10546631 = 15819947) B15819947
theorem B1306219 : Blo 770335 1306219 := bstep (se 1 (by rfl) ⟨979664, by rfl⟩ : syracuseStep 1306219 = 1959329) B1959329
theorem B1306489 : Blo 770335 1306489 := bstep (se 2 (by rfl) ⟨489933, by rfl⟩ : syracuseStep 1306489 = 979867) B979867
theorem B1306523 : Blo 770335 1306523 := bstep (se 1 (by rfl) ⟨979892, by rfl⟩ : syracuseStep 1306523 = 1959785) B1959785
theorem B5566583 : Blo 770335 5566583 := bstep (se 1 (by rfl) ⟨4174937, by rfl⟩ : syracuseStep 5566583 = 8349875) B8349875
theorem B2978387 : Blo 770335 2978387 := bstep (se 1 (by rfl) ⟨2233790, by rfl⟩ : syracuseStep 2978387 = 4467581) B4467581
theorem B1733417 : Blo 770335 1733417 := bstep (se 2 (by rfl) ⟨650031, by rfl⟩ : syracuseStep 1733417 = 1300063) B1300063
theorem B1733687 : Blo 770335 1733687 := bstep (se 1 (by rfl) ⟨1300265, by rfl⟩ : syracuseStep 1733687 = 2600531) B2600531
theorem B1733705 : Blo 770335 1733705 := bstep (se 2 (by rfl) ⟨650139, by rfl⟩ : syracuseStep 1733705 = 1300279) B1300279
theorem B3306881 : Blo 770335 3306881 := bstep (se 2 (by rfl) ⟨1240080, by rfl⟩ : syracuseStep 3306881 = 2480161) B2480161
theorem B4454099 : Blo 770335 4454099 := bstep (se 1 (by rfl) ⟨3340574, by rfl⟩ : syracuseStep 4454099 = 6681149) B6681149
theorem B25098133 : Blo 770335 25098133 := bstep (se 6 (by rfl) ⟨588237, by rfl⟩ : syracuseStep 25098133 = 1176475) B1176475
theorem B7403885 : Blo 770335 7403885 := bstep (se 3 (by rfl) ⟨1388228, by rfl⟩ : syracuseStep 7403885 = 2776457) B2776457
theorem B32143979 : Blo 770335 32143979 := bstep (se 1 (by rfl) ⟨24107984, by rfl⟩ : syracuseStep 32143979 = 48215969) B48215969
theorem B1735631 : Blo 770335 1735631 := bstep (se 1 (by rfl) ⟨1301723, by rfl⟩ : syracuseStep 1735631 = 2603447) B2603447
theorem B1735649 : Blo 770335 1735649 := bstep (se 2 (by rfl) ⟨650868, by rfl⟩ : syracuseStep 1735649 = 1301737) B1301737
theorem B1735721 : Blo 770335 1735721 := bstep (se 2 (by rfl) ⟨650895, by rfl⟩ : syracuseStep 1735721 = 1301791) B1301791
theorem B2194951 : Blo 770335 2194951 := bstep (se 1 (by rfl) ⟨1646213, by rfl⟩ : syracuseStep 2194951 = 3292427) B3292427
theorem B6585947 : Blo 770335 6585947 := bstep (se 1 (by rfl) ⟨4939460, by rfl⟩ : syracuseStep 6585947 = 9878921) B9878921
theorem B27066473 : Blo 770335 27066473 := bstep (se 2 (by rfl) ⟨10149927, by rfl⟩ : syracuseStep 27066473 = 20299855) B20299855
theorem B1736891 : Blo 770335 1736891 := bstep (se 1 (by rfl) ⟨1302668, by rfl⟩ : syracuseStep 1736891 = 2605337) B2605337
theorem B1409215 : Blo 770335 1409215 := bstep (se 1 (by rfl) ⟨1056911, by rfl⟩ : syracuseStep 1409215 = 2113823) B2113823
theorem B1736999 : Blo 770335 1736999 := bstep (se 1 (by rfl) ⟨1302749, by rfl⟩ : syracuseStep 1736999 = 2605499) B2605499
theorem B6586697 : Blo 770335 6586697 := bstep (se 2 (by rfl) ⟨2470011, by rfl⟩ : syracuseStep 6586697 = 4940023) B4940023
theorem B2195839 : Blo 770335 2195839 := bstep (se 1 (by rfl) ⟨1646879, by rfl⟩ : syracuseStep 2195839 = 3293759) B3293759
theorem B1737377 : Blo 770335 1737377 := bstep (se 2 (by rfl) ⟨651516, by rfl⟩ : syracuseStep 1737377 = 1303033) B1303033
theorem B20022227 : Blo 770335 20022227 := bstep (se 1 (by rfl) ⟨15016670, by rfl⟩ : syracuseStep 20022227 = 30033341) B30033341
theorem B1737737 : Blo 770335 1737737 := bstep (se 2 (by rfl) ⟨651651, by rfl⟩ : syracuseStep 1737737 = 1303303) B1303303
theorem B1737791 : Blo 770335 1737791 := bstep (se 1 (by rfl) ⟨1303343, by rfl⟩ : syracuseStep 1737791 = 2606687) B2606687
theorem B4949099 : Blo 770335 4949099 := bstep (se 1 (by rfl) ⟨3711824, by rfl⟩ : syracuseStep 4949099 = 7423649) B7423649
theorem B33392209 : Blo 770335 33392209 := bstep (se 2 (by rfl) ⟨12522078, by rfl⟩ : syracuseStep 33392209 = 25044157) B25044157
theorem B1738727 : Blo 770335 1738727 := bstep (se 1 (by rfl) ⟨1304045, by rfl⟩ : syracuseStep 1738727 = 2608091) B2608091
theorem B8456345 : Blo 770335 8456345 := bstep (se 2 (by rfl) ⟨3171129, by rfl⟩ : syracuseStep 8456345 = 6342259) B6342259
theorem B1738907 : Blo 770335 1738907 := bstep (se 1 (by rfl) ⟨1304180, by rfl⟩ : syracuseStep 1738907 = 2608361) B2608361
theorem B1739087 : Blo 770335 1739087 := bstep (se 1 (by rfl) ⟨1304315, by rfl⟩ : syracuseStep 1739087 = 2608631) B2608631
theorem B7408037 : Blo 770335 7408037 := bstep (se 4 (by rfl) ⟨694503, by rfl⟩ : syracuseStep 7408037 = 1389007) B1389007
theorem B1739177 : Blo 770335 1739177 := bstep (se 2 (by rfl) ⟨652191, by rfl⟩ : syracuseStep 1739177 = 1304383) B1304383
theorem B6261563 : Blo 770335 6261563 := bstep (se 1 (by rfl) ⟨4696172, by rfl⟩ : syracuseStep 6261563 = 9392345) B9392345
theorem B1739771 : Blo 770335 1739771 := bstep (se 1 (by rfl) ⟨1304828, by rfl⟩ : syracuseStep 1739771 = 2609657) B2609657
theorem B4394047 : Blo 770335 4394047 := bstep (se 1 (by rfl) ⟨3295535, by rfl⟩ : syracuseStep 4394047 = 6591071) B6591071
theorem B1739951 : Blo 770335 1739951 := bstep (se 1 (by rfl) ⟨1304963, by rfl⟩ : syracuseStep 1739951 = 2609927) B2609927
theorem B1739987 : Blo 770335 1739987 := bstep (se 1 (by rfl) ⟨1304990, by rfl⟩ : syracuseStep 1739987 = 2609981) B2609981
theorem B28249411 : Blo 770335 28249411 := bstep (se 1 (by rfl) ⟨21187058, by rfl⟩ : syracuseStep 28249411 = 42374117) B42374117
theorem B1740257 : Blo 770335 1740257 := bstep (se 2 (by rfl) ⟨652596, by rfl⟩ : syracuseStep 1740257 = 1305193) B1305193
theorem B1740671 : Blo 770335 1740671 := bstep (se 1 (by rfl) ⟨1305503, by rfl⟩ : syracuseStep 1740671 = 2611007) B2611007
theorem B3903551 : Blo 770335 3903551 := bstep (se 1 (by rfl) ⟨2927663, by rfl⟩ : syracuseStep 3903551 = 5855327) B5855327
theorem B1741625 : Blo 770335 1741625 := bstep (se 2 (by rfl) ⟨653109, by rfl⟩ : syracuseStep 1741625 = 1306219) B1306219
theorem B1741679 : Blo 770335 1741679 := bstep (se 1 (by rfl) ⟨1306259, by rfl⟩ : syracuseStep 1741679 = 2612519) B2612519
theorem B45192167 : Blo 770335 45192167 := bstep (se 1 (by rfl) ⟨33894125, by rfl⟩ : syracuseStep 45192167 = 67788251) B67788251
theorem B824303 : Blo 770335 824303 := bstep (se 1 (by rfl) ⟨618227, by rfl⟩ : syracuseStep 824303 = 1236455) B1236455
theorem B2200601 : Blo 770335 2200601 := bstep (se 2 (by rfl) ⟨825225, by rfl⟩ : syracuseStep 2200601 = 1650451) B1650451
theorem B1741985 : Blo 770335 1741985 := bstep (se 2 (by rfl) ⟨653244, by rfl⟩ : syracuseStep 1741985 = 1306489) B1306489
theorem B2200783 : Blo 770335 2200783 := bstep (se 1 (by rfl) ⟨1650587, by rfl⟩ : syracuseStep 2200783 = 3301175) B3301175
theorem B4396463 : Blo 770335 4396463 := bstep (se 1 (by rfl) ⟨3297347, by rfl⟩ : syracuseStep 4396463 = 6594695) B6594695
theorem B1742255 : Blo 770335 1742255 := bstep (se 1 (by rfl) ⟨1306691, by rfl⟩ : syracuseStep 1742255 = 2613383) B2613383
theorem B5576327 : Blo 770335 5576327 := bstep (se 1 (by rfl) ⟨4182245, by rfl⟩ : syracuseStep 5576327 = 8364491) B8364491
theorem B115677341 : Blo 770335 115677341 := bstep (se 3 (by rfl) ⟨21689501, by rfl⟩ : syracuseStep 115677341 = 43379003) B43379003
theorem B6592711 : Blo 770335 6592711 := bstep (se 1 (by rfl) ⟨4944533, by rfl⟩ : syracuseStep 6592711 = 9889067) B9889067
theorem B14883425 : Blo 770335 14883425 := bstep (se 2 (by rfl) ⟨5581284, by rfl⟩ : syracuseStep 14883425 = 11162569) B11162569
theorem B2202491 : Blo 770335 2202491 := bstep (se 1 (by rfl) ⟨1651868, by rfl⟩ : syracuseStep 2202491 = 3303737) B3303737
theorem B11116385 : Blo 770335 11116385 := bstep (se 2 (by rfl) ⟨4168644, by rfl⟩ : syracuseStep 11116385 = 8337289) B8337289
theorem B33464177 : Blo 770335 33464177 := bstep (se 2 (by rfl) ⟨12549066, by rfl⟩ : syracuseStep 33464177 = 25098133) B25098133
theorem B3711055 : Blo 770335 3711055 := bstep (se 1 (by rfl) ⟨2783291, by rfl⟩ : syracuseStep 3711055 = 5566583) B5566583
theorem B3350879 : Blo 770335 3350879 := bstep (se 1 (by rfl) ⟨2513159, by rfl⟩ : syracuseStep 3350879 = 5026319) B5026319
theorem B1155611 : Blo 770335 1155611 := bstep (se 1 (by rfl) ⟨866708, by rfl⟩ : syracuseStep 1155611 = 1733417) B1733417
theorem B14099021 : Blo 770335 14099021 := bstep (se 3 (by rfl) ⟨2643566, by rfl⟩ : syracuseStep 14099021 = 5287133) B5287133
theorem B4399697 : Blo 770335 4399697 := bstep (se 2 (by rfl) ⟨1649886, by rfl⟩ : syracuseStep 4399697 = 3299773) B3299773
theorem B1155791 : Blo 770335 1155791 := bstep (se 1 (by rfl) ⟨866843, by rfl⟩ : syracuseStep 1155791 = 1733687) B1733687
theorem B1155803 : Blo 770335 1155803 := bstep (se 1 (by rfl) ⟨866852, by rfl⟩ : syracuseStep 1155803 = 1733705) B1733705
theorem B4399879 : Blo 770335 4399879 := bstep (se 1 (by rfl) ⟨3299909, by rfl⟩ : syracuseStep 4399879 = 6599819) B6599819
theorem B2204587 : Blo 770335 2204587 := bstep (se 1 (by rfl) ⟨1653440, by rfl⟩ : syracuseStep 2204587 = 3306881) B3306881
theorem B56435777 : Blo 770335 56435777 := bstep (se 2 (by rfl) ⟨21163416, by rfl⟩ : syracuseStep 56435777 = 42326833) B42326833
theorem B1156217 : Blo 770335 1156217 := bstep (se 2 (by rfl) ⟨433581, by rfl⟩ : syracuseStep 1156217 = 867163) B867163
theorem B1157087 : Blo 770335 1157087 := bstep (se 1 (by rfl) ⟨867815, by rfl⟩ : syracuseStep 1157087 = 1735631) B1735631
theorem B1157099 : Blo 770335 1157099 := bstep (se 1 (by rfl) ⟨867824, by rfl⟩ : syracuseStep 1157099 = 1735649) B1735649
theorem B2926601 : Blo 770335 2926601 := bstep (se 2 (by rfl) ⟨1097475, by rfl⟩ : syracuseStep 2926601 = 2194951) B2194951
theorem B1157147 : Blo 770335 1157147 := bstep (se 1 (by rfl) ⟨867860, by rfl⟩ : syracuseStep 1157147 = 1735721) B1735721
theorem B1157513 : Blo 770335 1157513 := bstep (se 2 (by rfl) ⟨434067, by rfl⟩ : syracuseStep 1157513 = 868135) B868135
theorem B5876711 : Blo 770335 5876711 := bstep (se 1 (by rfl) ⟨4407533, by rfl⟩ : syracuseStep 5876711 = 8815067) B8815067
theorem B3124489 : Blo 770335 3124489 := bstep (se 2 (by rfl) ⟨1171683, by rfl⟩ : syracuseStep 3124489 = 2343367) B2343367
theorem B1158455 : Blo 770335 1158455 := bstep (se 1 (by rfl) ⟨868841, by rfl⟩ : syracuseStep 1158455 = 1737683) B1737683
theorem B1158623 : Blo 770335 1158623 := bstep (se 1 (by rfl) ⟨868967, by rfl⟩ : syracuseStep 1158623 = 1737935) B1737935
theorem B4402795 : Blo 770335 4402795 := bstep (se 1 (by rfl) ⟨3302096, by rfl⟩ : syracuseStep 4402795 = 6604193) B6604193
theorem B2928271 : Blo 770335 2928271 := bstep (se 1 (by rfl) ⟨2196203, by rfl⟩ : syracuseStep 2928271 = 4392407) B4392407
theorem B1158839 : Blo 770335 1158839 := bstep (se 1 (by rfl) ⟨869129, by rfl⟩ : syracuseStep 1158839 = 1738259) B1738259
theorem B929599 : Blo 770335 929599 := bstep (se 1 (by rfl) ⟨697199, by rfl⟩ : syracuseStep 929599 = 1394399) B1394399
theorem B28159811 : Blo 770335 28159811 := bstep (se 1 (by rfl) ⟨21119858, by rfl⟩ : syracuseStep 28159811 = 42239717) B42239717
theorem B3518333 : Blo 770335 3518333 := bstep (se 3 (by rfl) ⟨659687, by rfl⟩ : syracuseStep 3518333 = 1319375) B1319375
theorem B1159049 : Blo 770335 1159049 := bstep (se 2 (by rfl) ⟨434643, by rfl⟩ : syracuseStep 1159049 = 869287) B869287
theorem B1159295 : Blo 770335 1159295 := bstep (se 1 (by rfl) ⟨869471, by rfl⟩ : syracuseStep 1159295 = 1738943) B1738943
theorem B3715303 : Blo 770335 3715303 := bstep (se 1 (by rfl) ⟨2786477, by rfl⟩ : syracuseStep 3715303 = 5572955) B5572955
theorem B1651151 : Blo 770335 1651151 := bstep (se 1 (by rfl) ⟨1238363, by rfl⟩ : syracuseStep 1651151 = 2476727) B2476727
theorem B3912299 : Blo 770335 3912299 := bstep (se 1 (by rfl) ⟨2934224, by rfl⟩ : syracuseStep 3912299 = 5868449) B5868449
theorem B1159931 : Blo 770335 1159931 := bstep (se 1 (by rfl) ⟨869948, by rfl⟩ : syracuseStep 1159931 = 1739897) B1739897
theorem B1651519 : Blo 770335 1651519 := bstep (se 1 (by rfl) ⟨1238639, by rfl⟩ : syracuseStep 1651519 = 2477279) B2477279
theorem B1323913 : Blo 770335 1323913 := bstep (se 2 (by rfl) ⟨496467, by rfl⟩ : syracuseStep 1323913 = 992935) B992935
theorem B2601935 : Blo 770335 2601935 := bstep (se 1 (by rfl) ⟨1951451, by rfl⟩ : syracuseStep 2601935 = 3902903) B3902903
theorem B2602043 : Blo 770335 2602043 := bstep (se 1 (by rfl) ⟨1951532, by rfl⟩ : syracuseStep 2602043 = 3903065) B3903065
theorem B3912785 : Blo 770335 3912785 := bstep (se 2 (by rfl) ⟨1467294, by rfl⟩ : syracuseStep 3912785 = 2934589) B2934589
theorem B1160375 : Blo 770335 1160375 := bstep (se 1 (by rfl) ⟨870281, by rfl⟩ : syracuseStep 1160375 = 1740563) B1740563
theorem B2602313 : Blo 770335 2602313 := bstep (se 2 (by rfl) ⟨975867, by rfl⟩ : syracuseStep 2602313 = 1951735) B1951735
theorem B168998237 : Blo 770335 168998237 := bstep (se 3 (by rfl) ⟨31687169, by rfl⟩ : syracuseStep 168998237 = 63374339) B63374339
theorem B1160615 : Blo 770335 1160615 := bstep (se 1 (by rfl) ⟨870461, by rfl⟩ : syracuseStep 1160615 = 1740923) B1740923
theorem B4699579 : Blo 770335 4699579 := bstep (se 1 (by rfl) ⟨3524684, by rfl⟩ : syracuseStep 4699579 = 7049369) B7049369
theorem B1160795 : Blo 770335 1160795 := bstep (se 1 (by rfl) ⟨870596, by rfl⟩ : syracuseStep 1160795 = 1741193) B1741193
theorem B9910187 : Blo 770335 9910187 := bstep (se 1 (by rfl) ⟨7432640, by rfl⟩ : syracuseStep 9910187 = 14865281) B14865281
theorem B1161257 : Blo 770335 1161257 := bstep (se 2 (by rfl) ⟨435471, by rfl⟩ : syracuseStep 1161257 = 870943) B870943
theorem B1161287 : Blo 770335 1161287 := bstep (se 1 (by rfl) ⟨870965, by rfl⟩ : syracuseStep 1161287 = 1741931) B1741931
theorem B3913919 : Blo 770335 3913919 := bstep (se 1 (by rfl) ⟨2935439, by rfl⟩ : syracuseStep 3913919 = 5870879) B5870879
theorem B3291367 : Blo 770335 3291367 := bstep (se 1 (by rfl) ⟨2468525, by rfl⟩ : syracuseStep 3291367 = 4937051) B4937051
theorem B25049351 : Blo 770335 25049351 := bstep (se 1 (by rfl) ⟨18787013, by rfl⟩ : syracuseStep 25049351 = 37574027) B37574027
theorem B866767 : Blo 770335 866767 := bstep (se 1 (by rfl) ⟨650075, by rfl⟩ : syracuseStep 866767 = 1300151) B1300151
theorem B2603663 : Blo 770335 2603663 := bstep (se 1 (by rfl) ⟨1952747, by rfl⟩ : syracuseStep 2603663 = 3905495) B3905495
theorem B2603987 : Blo 770335 2603987 := bstep (se 1 (by rfl) ⟨1952990, by rfl⟩ : syracuseStep 2603987 = 3905981) B3905981
theorem B2636999 : Blo 770335 2636999 := bstep (se 1 (by rfl) ⟨1977749, by rfl⟩ : syracuseStep 2636999 = 3955499) B3955499
theorem B2604257 : Blo 770335 2604257 := bstep (se 2 (by rfl) ⟨976596, by rfl⟩ : syracuseStep 2604257 = 1953193) B1953193
theorem B867559 : Blo 770335 867559 := bstep (se 1 (by rfl) ⟨650669, by rfl⟩ : syracuseStep 867559 = 1301339) B1301339
theorem B7126751 : Blo 770335 7126751 := bstep (se 1 (by rfl) ⟨5345063, by rfl⟩ : syracuseStep 7126751 = 10690127) B10690127
theorem B2604905 : Blo 770335 2604905 := bstep (se 2 (by rfl) ⟨976839, by rfl⟩ : syracuseStep 2604905 = 1953679) B1953679
theorem B868207 : Blo 770335 868207 := bstep (se 1 (by rfl) ⟨651155, by rfl⟩ : syracuseStep 868207 = 1302311) B1302311
theorem B3916025 : Blo 770335 3916025 := bstep (se 2 (by rfl) ⟨1468509, by rfl⟩ : syracuseStep 3916025 = 2937019) B2937019
theorem B770351 : Blo 770335 770351 := bstep (se 1 (by rfl) ⟨577763, by rfl⟩ : syracuseStep 770351 = 1155527) B1155527
theorem B770587 : Blo 770335 770587 := bstep (se 1 (by rfl) ⟨577940, by rfl⟩ : syracuseStep 770587 = 1155881) B1155881
theorem B868891 : Blo 770335 868891 := bstep (se 1 (by rfl) ⟨651668, by rfl⟩ : syracuseStep 868891 = 1303337) B1303337
theorem B770591 : Blo 770335 770591 := bstep (se 1 (by rfl) ⟨577943, by rfl⟩ : syracuseStep 770591 = 1155887) B1155887
theorem B770671 : Blo 770335 770671 := bstep (se 1 (by rfl) ⟨578003, by rfl⟩ : syracuseStep 770671 = 1156007) B1156007
theorem B770727 : Blo 770335 770727 := bstep (se 1 (by rfl) ⟨578045, by rfl⟩ : syracuseStep 770727 = 1156091) B1156091
theorem B12239531 : Blo 770335 12239531 := bstep (se 1 (by rfl) ⟨9179648, by rfl⟩ : syracuseStep 12239531 = 18359297) B18359297
theorem B2933435 : Blo 770335 2933435 := bstep (se 1 (by rfl) ⟨2200076, by rfl⟩ : syracuseStep 2933435 = 4400153) B4400153
theorem B770767 : Blo 770335 770767 := bstep (se 1 (by rfl) ⟨578075, by rfl⟩ : syracuseStep 770767 = 1156151) B1156151
theorem B869071 : Blo 770335 869071 := bstep (se 1 (by rfl) ⟨651803, by rfl⟩ : syracuseStep 869071 = 1303607) B1303607
theorem B770847 : Blo 770335 770847 := bstep (se 1 (by rfl) ⟨578135, by rfl⟩ : syracuseStep 770847 = 1156271) B1156271
theorem B3916673 : Blo 770335 3916673 := bstep (se 2 (by rfl) ⟨1468752, by rfl⟩ : syracuseStep 3916673 = 2937505) B2937505
theorem B1393607 : Blo 770335 1393607 := bstep (se 1 (by rfl) ⟨1045205, by rfl⟩ : syracuseStep 1393607 = 2090411) B2090411
theorem B771119 : Blo 770335 771119 := bstep (se 1 (by rfl) ⟨578339, by rfl⟩ : syracuseStep 771119 = 1156679) B1156679
theorem B771183 : Blo 770335 771183 := bstep (se 1 (by rfl) ⟨578387, by rfl⟩ : syracuseStep 771183 = 1156775) B1156775
theorem B771239 : Blo 770335 771239 := bstep (se 1 (by rfl) ⟨578429, by rfl⟩ : syracuseStep 771239 = 1156859) B1156859
theorem B2606255 : Blo 770335 2606255 := bstep (se 1 (by rfl) ⟨1954691, by rfl⟩ : syracuseStep 2606255 = 3909383) B3909383
theorem B771263 : Blo 770335 771263 := bstep (se 1 (by rfl) ⟨578447, by rfl⟩ : syracuseStep 771263 = 1156895) B1156895
theorem B771295 : Blo 770335 771295 := bstep (se 1 (by rfl) ⟨578471, by rfl⟩ : syracuseStep 771295 = 1156943) B1156943
theorem B771375 : Blo 770335 771375 := bstep (se 1 (by rfl) ⟨578531, by rfl⟩ : syracuseStep 771375 = 1157063) B1157063
theorem B771611 : Blo 770335 771611 := bstep (se 1 (by rfl) ⟨578708, by rfl⟩ : syracuseStep 771611 = 1157417) B1157417
theorem B771615 : Blo 770335 771615 := bstep (se 1 (by rfl) ⟨578711, by rfl⟩ : syracuseStep 771615 = 1157423) B1157423
theorem B1099327 : Blo 770335 1099327 := bstep (se 1 (by rfl) ⟨824495, by rfl⟩ : syracuseStep 1099327 = 1648991) B1648991
theorem B3917483 : Blo 770335 3917483 := bstep (se 1 (by rfl) ⟨2938112, by rfl⟩ : syracuseStep 3917483 = 5876225) B5876225
theorem B771775 : Blo 770335 771775 := bstep (se 1 (by rfl) ⟨578831, by rfl⟩ : syracuseStep 771775 = 1157663) B1157663
theorem B870079 : Blo 770335 870079 := bstep (se 1 (by rfl) ⟨652559, by rfl⟩ : syracuseStep 870079 = 1305119) B1305119
theorem B772031 : Blo 770335 772031 := bstep (se 1 (by rfl) ⟨579023, by rfl⟩ : syracuseStep 772031 = 1158047) B1158047
theorem B772063 : Blo 770335 772063 := bstep (se 1 (by rfl) ⟨579047, by rfl⟩ : syracuseStep 772063 = 1158095) B1158095
theorem B870367 : Blo 770335 870367 := bstep (se 1 (by rfl) ⟨652775, by rfl⟩ : syracuseStep 870367 = 1305551) B1305551
theorem B772123 : Blo 770335 772123 := bstep (se 1 (by rfl) ⟨579092, by rfl⟩ : syracuseStep 772123 = 1158185) B1158185
theorem B772127 : Blo 770335 772127 := bstep (se 1 (by rfl) ⟨579095, by rfl⟩ : syracuseStep 772127 = 1158191) B1158191
theorem B772143 : Blo 770335 772143 := bstep (se 1 (by rfl) ⟨579107, by rfl⟩ : syracuseStep 772143 = 1158215) B1158215
theorem B3917969 : Blo 770335 3917969 := bstep (se 2 (by rfl) ⟨1469238, by rfl⟩ : syracuseStep 3917969 = 2938477) B2938477
theorem B772319 : Blo 770335 772319 := bstep (se 1 (by rfl) ⟨579239, by rfl⟩ : syracuseStep 772319 = 1158479) B1158479
theorem B772379 : Blo 770335 772379 := bstep (se 1 (by rfl) ⟨579284, by rfl⟩ : syracuseStep 772379 = 1158569) B1158569
theorem B5851439 : Blo 770335 5851439 := bstep (se 1 (by rfl) ⟨4388579, by rfl⟩ : syracuseStep 5851439 = 8777159) B8777159
theorem B7031087 : Blo 770335 7031087 := bstep (se 1 (by rfl) ⟨5273315, by rfl⟩ : syracuseStep 7031087 = 10546631) B10546631
theorem B772479 : Blo 770335 772479 := bstep (se 1 (by rfl) ⟨579359, by rfl⟩ : syracuseStep 772479 = 1158719) B1158719
theorem B772655 : Blo 770335 772655 := bstep (se 1 (by rfl) ⟨579491, by rfl⟩ : syracuseStep 772655 = 1158983) B1158983
theorem B772711 : Blo 770335 772711 := bstep (se 1 (by rfl) ⟨579533, by rfl⟩ : syracuseStep 772711 = 1159067) B1159067
theorem B871015 : Blo 770335 871015 := bstep (se 1 (by rfl) ⟨653261, by rfl⟩ : syracuseStep 871015 = 1306523) B1306523
theorem B1100585 : Blo 770335 1100585 := bstep (se 2 (by rfl) ⟨412719, by rfl⟩ : syracuseStep 1100585 = 825439) B825439
theorem B1100665 : Blo 770335 1100665 := bstep (se 2 (by rfl) ⟨412749, by rfl⟩ : syracuseStep 1100665 = 825499) B825499
theorem B773087 : Blo 770335 773087 := bstep (se 1 (by rfl) ⟨579815, by rfl⟩ : syracuseStep 773087 = 1159631) B1159631
theorem B773115 : Blo 770335 773115 := bstep (se 1 (by rfl) ⟨579836, by rfl⟩ : syracuseStep 773115 = 1159673) B1159673
theorem B1985591 : Blo 770335 1985591 := bstep (se 1 (by rfl) ⟨1489193, by rfl⟩ : syracuseStep 1985591 = 2978387) B2978387
theorem B773183 : Blo 770335 773183 := bstep (se 1 (by rfl) ⟨579887, by rfl⟩ : syracuseStep 773183 = 1159775) B1159775
theorem B773503 : Blo 770335 773503 := bstep (se 1 (by rfl) ⟨580127, by rfl⟩ : syracuseStep 773503 = 1160255) B1160255
theorem B773531 : Blo 770335 773531 := bstep (se 1 (by rfl) ⟨580148, by rfl⟩ : syracuseStep 773531 = 1160297) B1160297
theorem B7032253 : Blo 770335 7032253 := bstep (se 3 (by rfl) ⟨1318547, by rfl⟩ : syracuseStep 7032253 = 2637095) B2637095
theorem B773599 : Blo 770335 773599 := bstep (se 1 (by rfl) ⟨580199, by rfl⟩ : syracuseStep 773599 = 1160399) B1160399
theorem B3296801 : Blo 770335 3296801 := bstep (se 2 (by rfl) ⟨1236300, by rfl⟩ : syracuseStep 3296801 = 2472601) B2472601
theorem B773735 : Blo 770335 773735 := bstep (se 1 (by rfl) ⟨580301, by rfl⟩ : syracuseStep 773735 = 1160603) B1160603
theorem B773883 : Blo 770335 773883 := bstep (se 1 (by rfl) ⟨580412, by rfl⟩ : syracuseStep 773883 = 1160825) B1160825
theorem B2969399 : Blo 770335 2969399 := bstep (se 1 (by rfl) ⟨2227049, by rfl⟩ : syracuseStep 2969399 = 4454099) B4454099
theorem B773951 : Blo 770335 773951 := bstep (se 1 (by rfl) ⟨580463, by rfl⟩ : syracuseStep 773951 = 1160927) B1160927
theorem B774015 : Blo 770335 774015 := bstep (se 1 (by rfl) ⟨580511, by rfl⟩ : syracuseStep 774015 = 1161023) B1161023
theorem B2936807 : Blo 770335 2936807 := bstep (se 1 (by rfl) ⟨2202605, by rfl⟩ : syracuseStep 2936807 = 4405211) B4405211
theorem B774127 : Blo 770335 774127 := bstep (se 1 (by rfl) ⟨580595, by rfl⟩ : syracuseStep 774127 = 1161191) B1161191
theorem B774139 : Blo 770335 774139 := bstep (se 1 (by rfl) ⟨580604, by rfl⟩ : syracuseStep 774139 = 1161209) B1161209
theorem B774207 : Blo 770335 774207 := bstep (se 1 (by rfl) ⟨580655, by rfl⟩ : syracuseStep 774207 = 1161311) B1161311
theorem B774247 : Blo 770335 774247 := bstep (se 1 (by rfl) ⟨580685, by rfl⟩ : syracuseStep 774247 = 1161371) B1161371
theorem B774271 : Blo 770335 774271 := bstep (se 1 (by rfl) ⟨580703, by rfl⟩ : syracuseStep 774271 = 1161407) B1161407
theorem B774299 : Blo 770335 774299 := bstep (se 1 (by rfl) ⟨580724, by rfl⟩ : syracuseStep 774299 = 1161449) B1161449
theorem B4935923 : Blo 770335 4935923 := bstep (se 1 (by rfl) ⟨3701942, by rfl⟩ : syracuseStep 4935923 = 7403885) B7403885
theorem B1954145 : Blo 770335 1954145 := bstep (se 2 (by rfl) ⟨732804, by rfl⟩ : syracuseStep 1954145 = 1465609) B1465609
theorem B1757627 : Blo 770335 1757627 := bstep (se 1 (by rfl) ⟨1318220, by rfl⟩ : syracuseStep 1757627 = 2636441) B2636441
theorem B1954651 : Blo 770335 1954651 := bstep (se 1 (by rfl) ⟨1465988, by rfl⟩ : syracuseStep 1954651 = 2931977) B2931977
theorem B26760577 : Blo 770335 26760577 := bstep (se 2 (by rfl) ⟨10035216, by rfl⟩ : syracuseStep 26760577 = 20070433) B20070433
theorem B2938781 : Blo 770335 2938781 := bstep (se 3 (by rfl) ⟨551021, by rfl⟩ : syracuseStep 2938781 = 1102043) B1102043
theorem B1234847 : Blo 770335 1234847 := bstep (se 1 (by rfl) ⟨926135, by rfl⟩ : syracuseStep 1234847 = 1852271) B1852271
theorem B2611169 : Blo 770335 2611169 := bstep (se 2 (by rfl) ⟨979188, by rfl⟩ : syracuseStep 2611169 = 1958377) B1958377
theorem B1464311 : Blo 770335 1464311 := bstep (se 1 (by rfl) ⟨1098233, by rfl⟩ : syracuseStep 1464311 = 2196467) B2196467
theorem B2938963 : Blo 770335 2938963 := bstep (se 1 (by rfl) ⟨2204222, by rfl⟩ : syracuseStep 2938963 = 4408445) B4408445
theorem B1956059 : Blo 770335 1956059 := bstep (se 1 (by rfl) ⟨1467044, by rfl⟩ : syracuseStep 1956059 = 2934089) B2934089
theorem B1235359 : Blo 770335 1235359 := bstep (se 1 (by rfl) ⟨926519, by rfl⟩ : syracuseStep 1235359 = 1853039) B1853039
theorem B1301305 : Blo 770335 1301305 := bstep (se 2 (by rfl) ⟨487989, by rfl⟩ : syracuseStep 1301305 = 975979) B975979
theorem B1301359 : Blo 770335 1301359 := bstep (se 1 (by rfl) ⟨976019, by rfl⟩ : syracuseStep 1301359 = 1952039) B1952039
theorem B1465199 : Blo 770335 1465199 := bstep (se 1 (by rfl) ⟨1098899, by rfl⟩ : syracuseStep 1465199 = 2197799) B2197799
theorem B31742837 : Blo 770335 31742837 := bstep (se 5 (by rfl) ⟨1487945, by rfl⟩ : syracuseStep 31742837 = 2975891) B2975891
theorem B71326817 : Blo 770335 71326817 := bstep (se 2 (by rfl) ⟨26747556, by rfl⟩ : syracuseStep 71326817 = 53495113) B53495113
theorem B1465465 : Blo 770335 1465465 := bstep (se 2 (by rfl) ⟨549549, by rfl⟩ : syracuseStep 1465465 = 1099099) B1099099
theorem B2350313 : Blo 770335 2350313 := bstep (se 2 (by rfl) ⟨881367, by rfl⟩ : syracuseStep 2350313 = 1762735) B1762735
theorem B81420823 : Blo 770335 81420823 := bstep (se 1 (by rfl) ⟨61065617, by rfl⟩ : syracuseStep 81420823 = 122131235) B122131235
theorem B1303067 : Blo 770335 1303067 := bstep (se 1 (by rfl) ⟨977300, by rfl⟩ : syracuseStep 1303067 = 1954601) B1954601
theorem B1237531 : Blo 770335 1237531 := bstep (se 1 (by rfl) ⟨928148, by rfl⟩ : syracuseStep 1237531 = 1856297) B1856297
theorem B2351783 : Blo 770335 2351783 := bstep (se 1 (by rfl) ⟨1763837, by rfl⟩ : syracuseStep 2351783 = 3527675) B3527675
theorem B1467143 : Blo 770335 1467143 := bstep (se 1 (by rfl) ⟨1100357, by rfl⟩ : syracuseStep 1467143 = 2200715) B2200715
theorem B14869277 : Blo 770335 14869277 := bstep (se 3 (by rfl) ⟨2787989, by rfl⟩ : syracuseStep 14869277 = 5575979) B5575979
theorem B2974495 : Blo 770335 2974495 := bstep (se 1 (by rfl) ⟨2230871, by rfl⟩ : syracuseStep 2974495 = 4461743) B4461743
theorem B1467371 : Blo 770335 1467371 := bstep (se 1 (by rfl) ⟨1100528, by rfl⟩ : syracuseStep 1467371 = 2201057) B2201057
theorem B11134199 : Blo 770335 11134199 := bstep (se 1 (by rfl) ⟨8350649, by rfl⟩ : syracuseStep 11134199 = 16701299) B16701299
theorem B7431563 : Blo 770335 7431563 := bstep (se 1 (by rfl) ⟨5573672, by rfl⟩ : syracuseStep 7431563 = 11147345) B11147345
theorem B1467895 : Blo 770335 1467895 := bstep (se 1 (by rfl) ⟨1100921, by rfl⟩ : syracuseStep 1467895 = 2201843) B2201843
theorem B9397787 : Blo 770335 9397787 := bstep (se 1 (by rfl) ⟨7048340, by rfl⟩ : syracuseStep 9397787 = 14096681) B14096681
theorem B1468297 : Blo 770335 1468297 := bstep (se 2 (by rfl) ⟨550611, by rfl⟩ : syracuseStep 1468297 = 1101223) B1101223
theorem B7038859 : Blo 770335 7038859 := bstep (se 1 (by rfl) ⟨5279144, by rfl⟩ : syracuseStep 7038859 = 10558289) B10558289
theorem B2713499 : Blo 770335 2713499 := bstep (se 1 (by rfl) ⟨2035124, by rfl⟩ : syracuseStep 2713499 = 4070249) B4070249
theorem B1959835 : Blo 770335 1959835 := bstep (se 1 (by rfl) ⟨1469876, by rfl⟩ : syracuseStep 1959835 = 2939753) B2939753
theorem B1763831 : Blo 770335 1763831 := bstep (se 1 (by rfl) ⟨1322873, by rfl⟩ : syracuseStep 1763831 = 2645747) B2645747
theorem B1469011 : Blo 770335 1469011 := bstep (se 1 (by rfl) ⟨1101758, by rfl⟩ : syracuseStep 1469011 = 2203517) B2203517
theorem B65072267 : Blo 770335 65072267 := bstep (se 1 (by rfl) ⟨48804200, by rfl⟩ : syracuseStep 65072267 = 97608401) B97608401
theorem B5861159 : Blo 770335 5861159 := bstep (se 1 (by rfl) ⟨4395869, by rfl⟩ : syracuseStep 5861159 = 8791739) B8791739
theorem B8482733 : Blo 770335 8482733 := bstep (se 3 (by rfl) ⟨1590512, by rfl⟩ : syracuseStep 8482733 = 3181025) B3181025
theorem B1733543 : Blo 770335 1733543 := bstep (se 1 (by rfl) ⟨1300157, by rfl⟩ : syracuseStep 1733543 = 2600315) B2600315
theorem B13530833 : Blo 770335 13530833 := bstep (se 2 (by rfl) ⟨5074062, by rfl⟩ : syracuseStep 13530833 = 10148125) B10148125
theorem B1734479 : Blo 770335 1734479 := bstep (se 1 (by rfl) ⟨1300859, by rfl⟩ : syracuseStep 1734479 = 2601719) B2601719
theorem B3307463 : Blo 770335 3307463 := bstep (se 1 (by rfl) ⟨2480597, by rfl⟩ : syracuseStep 3307463 = 4961195) B4961195
theorem B1734839 : Blo 770335 1734839 := bstep (se 1 (by rfl) ⟨1301129, by rfl⟩ : syracuseStep 1734839 = 2602259) B2602259
theorem B1735199 : Blo 770335 1735199 := bstep (se 1 (by rfl) ⟨1301399, by rfl⟩ : syracuseStep 1735199 = 2602799) B2602799
theorem B1735433 : Blo 770335 1735433 := bstep (se 2 (by rfl) ⟨650787, by rfl⟩ : syracuseStep 1735433 = 1301575) B1301575
theorem B7437257 : Blo 770335 7437257 := bstep (se 2 (by rfl) ⟨2788971, by rfl⟩ : syracuseStep 7437257 = 5577943) B5577943
theorem B21429319 : Blo 770335 21429319 := bstep (se 1 (by rfl) ⟨16071989, by rfl⟩ : syracuseStep 21429319 = 32143979) B32143979
theorem B3701983 : Blo 770335 3701983 := bstep (se 1 (by rfl) ⟨2776487, by rfl⟩ : syracuseStep 3701983 = 5552975) B5552975
theorem B1736009 : Blo 770335 1736009 := bstep (se 2 (by rfl) ⟨651003, by rfl⟩ : syracuseStep 1736009 = 1302007) B1302007
theorem B4390631 : Blo 770335 4390631 := bstep (se 1 (by rfl) ⟨3292973, by rfl⟩ : syracuseStep 4390631 = 6585947) B6585947
theorem B1736423 : Blo 770335 1736423 := bstep (se 1 (by rfl) ⟨1302317, by rfl⟩ : syracuseStep 1736423 = 2604635) B2604635
theorem B3702557 : Blo 770335 3702557 := bstep (se 3 (by rfl) ⟨694229, by rfl⟩ : syracuseStep 3702557 = 1388459) B1388459
theorem B4948073 : Blo 770335 4948073 := bstep (se 2 (by rfl) ⟨1855527, by rfl⟩ : syracuseStep 4948073 = 3711055) B3711055
theorem B4391131 : Blo 770335 4391131 := bstep (se 1 (by rfl) ⟨3293348, by rfl⟩ : syracuseStep 4391131 = 6586697) B6586697
theorem B8159687 : Blo 770335 8159687 := bstep (se 1 (by rfl) ⟨6119765, by rfl⟩ : syracuseStep 8159687 = 12239531) B12239531
theorem B108561097 : Blo 770335 108561097 := bstep (se 2 (by rfl) ⟨40710411, by rfl⟩ : syracuseStep 108561097 = 81420823) B81420823
theorem B1737503 : Blo 770335 1737503 := bstep (se 1 (by rfl) ⟨1303127, by rfl⟩ : syracuseStep 1737503 = 2606255) B2606255
theorem B5866505 : Blo 770335 5866505 := bstep (se 2 (by rfl) ⟨2199939, by rfl⟩ : syracuseStep 5866505 = 4399879) B4399879
theorem B3965993 : Blo 770335 3965993 := bstep (se 2 (by rfl) ⟨1487247, by rfl⟩ : syracuseStep 3965993 = 2974495) B2974495
theorem B5637563 : Blo 770335 5637563 := bstep (se 1 (by rfl) ⟨4228172, by rfl⟩ : syracuseStep 5637563 = 8456345) B8456345
theorem B3900959 : Blo 770335 3900959 := bstep (se 1 (by rfl) ⟨2925719, by rfl⟩ : syracuseStep 3900959 = 5851439) B5851439
theorem B4687391 : Blo 770335 4687391 := bstep (se 1 (by rfl) ⟨3515543, by rfl⟩ : syracuseStep 4687391 = 7031087) B7031087
theorem B2197867 : Blo 770335 2197867 := bstep (se 1 (by rfl) ⟨1648400, by rfl⟩ : syracuseStep 2197867 = 3296801) B3296801
theorem B2198141 : Blo 770335 2198141 := bstep (se 3 (by rfl) ⟨412151, by rfl⟩ : syracuseStep 2198141 = 824303) B824303
theorem B823231 : Blo 770335 823231 := bstep (se 1 (by rfl) ⟨617423, by rfl⟩ : syracuseStep 823231 = 1234847) B1234847
theorem B1740779 : Blo 770335 1740779 := bstep (se 1 (by rfl) ⟨1305584, by rfl⟩ : syracuseStep 1740779 = 2611169) B2611169
theorem B4165985 : Blo 770335 4165985 := bstep (se 2 (by rfl) ⟨1562244, by rfl⟩ : syracuseStep 4165985 = 3124489) B3124489
theorem B9376337 : Blo 770335 9376337 := bstep (se 2 (by rfl) ⟨3516126, by rfl⟩ : syracuseStep 9376337 = 7032253) B7032253
theorem B47551211 : Blo 770335 47551211 := bstep (se 1 (by rfl) ⟨35663408, by rfl⟩ : syracuseStep 47551211 = 71326817) B71326817
theorem B5870393 : Blo 770335 5870393 := bstep (se 2 (by rfl) ⟨2201397, by rfl⟩ : syracuseStep 5870393 = 4402795) B4402795
theorem B3904361 : Blo 770335 3904361 := bstep (se 2 (by rfl) ⟨1464135, by rfl⟩ : syracuseStep 3904361 = 2928271) B2928271
theorem B7410923 : Blo 770335 7410923 := bstep (se 1 (by rfl) ⟨5558192, by rfl⟩ : syracuseStep 7410923 = 11116385) B11116385
theorem B2233919 : Blo 770335 2233919 := bstep (se 1 (by rfl) ⟨1675439, by rfl⟩ : syracuseStep 2233919 = 3350879) B3350879
theorem B4953737 : Blo 770335 4953737 := bstep (se 2 (by rfl) ⟨1857651, by rfl⟩ : syracuseStep 4953737 = 3715303) B3715303
theorem B37623851 : Blo 770335 37623851 := bstep (se 1 (by rfl) ⟨28217888, by rfl⟩ : syracuseStep 37623851 = 56435777) B56435777
theorem B4954375 : Blo 770335 4954375 := bstep (se 1 (by rfl) ⟨3715781, by rfl⟩ : syracuseStep 4954375 = 7431563) B7431563
theorem B2202025 : Blo 770335 2202025 := bstep (se 2 (by rfl) ⟨825759, by rfl⟩ : syracuseStep 2202025 = 1651519) B1651519
theorem B1808999 : Blo 770335 1808999 := bstep (se 1 (by rfl) ⟨1356749, by rfl⟩ : syracuseStep 1808999 = 2713499) B2713499
theorem B6266105 : Blo 770335 6266105 := bstep (se 2 (by rfl) ⟨2349789, by rfl⟩ : syracuseStep 6266105 = 4699579) B4699579
theorem B5873309 : Blo 770335 5873309 := bstep (se 3 (by rfl) ⟨1101245, by rfl⟩ : syracuseStep 5873309 = 2202491) B2202491
theorem B3907439 : Blo 770335 3907439 := bstep (se 1 (by rfl) ⟨2930579, by rfl⟩ : syracuseStep 3907439 = 5861159) B5861159
theorem B8790281 : Blo 770335 8790281 := bstep (se 2 (by rfl) ⟨3296355, by rfl⟩ : syracuseStep 8790281 = 6592711) B6592711
theorem B1647145 : Blo 770335 1647145 := bstep (se 2 (by rfl) ⟨617679, by rfl⟩ : syracuseStep 1647145 = 1235359) B1235359
theorem B1155689 : Blo 770335 1155689 := bstep (se 2 (by rfl) ⟨433383, by rfl⟩ : syracuseStep 1155689 = 866767) B866767
theorem B1155695 : Blo 770335 1155695 := bstep (se 1 (by rfl) ⟨866771, by rfl⟩ : syracuseStep 1155695 = 1733543) B1733543
theorem B112665491 : Blo 770335 112665491 := bstep (se 1 (by rfl) ⟨84499118, by rfl⟩ : syracuseStep 112665491 = 168998237) B168998237
theorem B9020555 : Blo 770335 9020555 := bstep (se 1 (by rfl) ⟨6765416, by rfl⟩ : syracuseStep 9020555 = 13530833) B13530833
theorem B1156319 : Blo 770335 1156319 := bstep (se 1 (by rfl) ⟨867239, by rfl⟩ : syracuseStep 1156319 = 1734479) B1734479
theorem B2204975 : Blo 770335 2204975 := bstep (se 1 (by rfl) ⟨1653731, by rfl⟩ : syracuseStep 2204975 = 3307463) B3307463
theorem B1156559 : Blo 770335 1156559 := bstep (se 1 (by rfl) ⟨867419, by rfl⟩ : syracuseStep 1156559 = 1734839) B1734839
theorem B1156745 : Blo 770335 1156745 := bstep (se 2 (by rfl) ⟨433779, by rfl⟩ : syracuseStep 1156745 = 867559) B867559
theorem B4957861 : Blo 770335 4957861 := bstep (se 4 (by rfl) ⟨464799, by rfl⟩ : syracuseStep 4957861 = 929599) B929599
theorem B1156799 : Blo 770335 1156799 := bstep (se 1 (by rfl) ⟨867599, by rfl⟩ : syracuseStep 1156799 = 1735199) B1735199
theorem B1156955 : Blo 770335 1156955 := bstep (se 1 (by rfl) ⟨867716, by rfl⟩ : syracuseStep 1156955 = 1735433) B1735433
theorem B4958171 : Blo 770335 4958171 := bstep (se 1 (by rfl) ⟨3718628, by rfl⟩ : syracuseStep 4958171 = 7437257) B7437257
theorem B9873485 : Blo 770335 9873485 := bstep (se 3 (by rfl) ⟨1851278, by rfl⟩ : syracuseStep 9873485 = 3702557) B3702557
theorem B1157339 : Blo 770335 1157339 := bstep (se 1 (by rfl) ⟨868004, by rfl⟩ : syracuseStep 1157339 = 1736009) B1736009
theorem B1157609 : Blo 770335 1157609 := bstep (se 2 (by rfl) ⟨434103, by rfl⟩ : syracuseStep 1157609 = 868207) B868207
theorem B2927087 : Blo 770335 2927087 := bstep (se 1 (by rfl) ⟨2195315, by rfl⟩ : syracuseStep 2927087 = 4390631) B4390631
theorem B1157615 : Blo 770335 1157615 := bstep (se 1 (by rfl) ⟨868211, by rfl⟩ : syracuseStep 1157615 = 1736423) B1736423
theorem B1157927 : Blo 770335 1157927 := bstep (se 1 (by rfl) ⟨868445, by rfl⟩ : syracuseStep 1157927 = 1736891) B1736891
theorem B1157999 : Blo 770335 1157999 := bstep (se 1 (by rfl) ⟨868499, by rfl⟩ : syracuseStep 1157999 = 1736999) B1736999
theorem B1878953 : Blo 770335 1878953 := bstep (se 2 (by rfl) ⟨704607, by rfl⟩ : syracuseStep 1878953 = 1409215) B1409215
theorem B1158251 : Blo 770335 1158251 := bstep (se 1 (by rfl) ⟨868688, by rfl⟩ : syracuseStep 1158251 = 1737377) B1737377
theorem B2927785 : Blo 770335 2927785 := bstep (se 2 (by rfl) ⟨1097919, by rfl⟩ : syracuseStep 2927785 = 2195839) B2195839
theorem B929071 : Blo 770335 929071 := bstep (se 1 (by rfl) ⟨696803, by rfl⟩ : syracuseStep 929071 = 1393607) B1393607
theorem B13348151 : Blo 770335 13348151 := bstep (se 1 (by rfl) ⟨10011113, by rfl⟩ : syracuseStep 13348151 = 20022227) B20022227
theorem B1158491 : Blo 770335 1158491 := bstep (se 1 (by rfl) ⟨868868, by rfl⟩ : syracuseStep 1158491 = 1737737) B1737737
theorem B1158521 : Blo 770335 1158521 := bstep (se 2 (by rfl) ⟨434445, by rfl⟩ : syracuseStep 1158521 = 868891) B868891
theorem B1650041 : Blo 770335 1650041 := bstep (se 2 (by rfl) ⟨618765, by rfl⟩ : syracuseStep 1650041 = 1237531) B1237531
theorem B1158527 : Blo 770335 1158527 := bstep (se 1 (by rfl) ⟨868895, by rfl⟩ : syracuseStep 1158527 = 1737791) B1737791
theorem B1158761 : Blo 770335 1158761 := bstep (se 2 (by rfl) ⟨434535, by rfl⟩ : syracuseStep 1158761 = 869071) B869071
theorem B4403069 : Blo 770335 4403069 := bstep (se 3 (by rfl) ⟨825575, by rfl⟩ : syracuseStep 4403069 = 1651151) B1651151
theorem B1159151 : Blo 770335 1159151 := bstep (se 1 (by rfl) ⟨869363, by rfl⟩ : syracuseStep 1159151 = 1738727) B1738727
theorem B1159271 : Blo 770335 1159271 := bstep (se 1 (by rfl) ⟨869453, by rfl⟩ : syracuseStep 1159271 = 1738907) B1738907
theorem B1159391 : Blo 770335 1159391 := bstep (se 1 (by rfl) ⟨869543, by rfl⟩ : syracuseStep 1159391 = 1739087) B1739087
theorem B1159451 : Blo 770335 1159451 := bstep (se 1 (by rfl) ⟨869588, by rfl⟩ : syracuseStep 1159451 = 1739177) B1739177
theorem B4174375 : Blo 770335 4174375 := bstep (se 1 (by rfl) ⟨3130781, by rfl⟩ : syracuseStep 4174375 = 6261563) B6261563
theorem B1159847 : Blo 770335 1159847 := bstep (se 1 (by rfl) ⟨869885, by rfl⟩ : syracuseStep 1159847 = 1739771) B1739771
theorem B1159967 : Blo 770335 1159967 := bstep (se 1 (by rfl) ⟨869975, by rfl⟩ : syracuseStep 1159967 = 1739951) B1739951
theorem B1159991 : Blo 770335 1159991 := bstep (se 1 (by rfl) ⟨869993, by rfl⟩ : syracuseStep 1159991 = 1739987) B1739987
theorem B1160105 : Blo 770335 1160105 := bstep (se 2 (by rfl) ⟨435039, by rfl⟩ : syracuseStep 1160105 = 870079) B870079
theorem B1160171 : Blo 770335 1160171 := bstep (se 1 (by rfl) ⟨870128, by rfl⟩ : syracuseStep 1160171 = 1740257) B1740257
theorem B9385145 : Blo 770335 9385145 := bstep (se 2 (by rfl) ⟨3519429, by rfl⟩ : syracuseStep 9385145 = 7038859) B7038859
theorem B1160447 : Blo 770335 1160447 := bstep (se 1 (by rfl) ⟨870335, by rfl⟩ : syracuseStep 1160447 = 1740671) B1740671
theorem B1160489 : Blo 770335 1160489 := bstep (se 2 (by rfl) ⟨435183, by rfl⟩ : syracuseStep 1160489 = 870367) B870367
theorem B2602367 : Blo 770335 2602367 := bstep (se 1 (by rfl) ⟨1951775, by rfl⟩ : syracuseStep 2602367 = 3903551) B3903551
theorem B3290615 : Blo 770335 3290615 := bstep (se 1 (by rfl) ⟨2467961, by rfl⟩ : syracuseStep 3290615 = 4935923) B4935923
theorem B1161083 : Blo 770335 1161083 := bstep (se 1 (by rfl) ⟨870812, by rfl⟩ : syracuseStep 1161083 = 1741625) B1741625
theorem B1161119 : Blo 770335 1161119 := bstep (se 1 (by rfl) ⟨870839, by rfl⟩ : syracuseStep 1161119 = 1741679) B1741679
theorem B30128111 : Blo 770335 30128111 := bstep (se 1 (by rfl) ⟨22596083, by rfl⟩ : syracuseStep 30128111 = 45192167) B45192167
theorem B1161323 : Blo 770335 1161323 := bstep (se 1 (by rfl) ⟨870992, by rfl⟩ : syracuseStep 1161323 = 1741985) B1741985
theorem B1161353 : Blo 770335 1161353 := bstep (se 2 (by rfl) ⟨435507, by rfl⟩ : syracuseStep 1161353 = 871015) B871015
theorem B2930975 : Blo 770335 2930975 := bstep (se 1 (by rfl) ⟨2198231, by rfl⟩ : syracuseStep 2930975 = 4396463) B4396463
theorem B1161503 : Blo 770335 1161503 := bstep (se 1 (by rfl) ⟨871127, by rfl⟩ : syracuseStep 1161503 = 1742255) B1742255
theorem B3717551 : Blo 770335 3717551 := bstep (se 1 (by rfl) ⟨2788163, by rfl⟩ : syracuseStep 3717551 = 5576327) B5576327
theorem B77118227 : Blo 770335 77118227 := bstep (se 1 (by rfl) ⟨57838670, by rfl⟩ : syracuseStep 77118227 = 115677341) B115677341
theorem B37665881 : Blo 770335 37665881 := bstep (se 2 (by rfl) ⟨14124705, by rfl⟩ : syracuseStep 37665881 = 28249411) B28249411
theorem B770407 : Blo 770335 770407 := bstep (se 1 (by rfl) ⟨577805, by rfl⟩ : syracuseStep 770407 = 1155611) B1155611
theorem B868711 : Blo 770335 868711 := bstep (se 1 (by rfl) ⟨651533, by rfl⟩ : syracuseStep 868711 = 1303067) B1303067
theorem B2933131 : Blo 770335 2933131 := bstep (se 1 (by rfl) ⟨2199848, by rfl⟩ : syracuseStep 2933131 = 4399697) B4399697
theorem B770527 : Blo 770335 770527 := bstep (se 1 (by rfl) ⟨577895, by rfl⟩ : syracuseStep 770527 = 1155791) B1155791
theorem B770535 : Blo 770335 770535 := bstep (se 1 (by rfl) ⟨577901, by rfl⟩ : syracuseStep 770535 = 1155803) B1155803
theorem B9912851 : Blo 770335 9912851 := bstep (se 1 (by rfl) ⟨7434638, by rfl⟩ : syracuseStep 9912851 = 14869277) B14869277
theorem B770811 : Blo 770335 770811 := bstep (se 1 (by rfl) ⟨578108, by rfl⟩ : syracuseStep 770811 = 1156217) B1156217
theorem B7422799 : Blo 770335 7422799 := bstep (se 1 (by rfl) ⟨5567099, by rfl⟩ : syracuseStep 7422799 = 11134199) B11134199
theorem B2606201 : Blo 770335 2606201 := bstep (se 2 (by rfl) ⟨977325, by rfl⟩ : syracuseStep 2606201 = 1954651) B1954651
theorem B771391 : Blo 770335 771391 := bstep (se 1 (by rfl) ⟨578543, by rfl⟩ : syracuseStep 771391 = 1157087) B1157087
theorem B771399 : Blo 770335 771399 := bstep (se 1 (by rfl) ⟨578549, by rfl⟩ : syracuseStep 771399 = 1157099) B1157099
theorem B1951067 : Blo 770335 1951067 := bstep (se 1 (by rfl) ⟨1463300, by rfl⟩ : syracuseStep 1951067 = 2926601) B2926601
theorem B771431 : Blo 770335 771431 := bstep (se 1 (by rfl) ⟨578573, by rfl⟩ : syracuseStep 771431 = 1157147) B1157147
theorem B771675 : Blo 770335 771675 := bstep (se 1 (by rfl) ⟨578756, by rfl⟩ : syracuseStep 771675 = 1157513) B1157513
theorem B2934377 : Blo 770335 2934377 := bstep (se 2 (by rfl) ⟨1100391, by rfl⟩ : syracuseStep 2934377 = 2200783) B2200783
theorem B3917807 : Blo 770335 3917807 := bstep (se 1 (by rfl) ⟨2938355, by rfl⟩ : syracuseStep 3917807 = 5876711) B5876711
theorem B2934893 : Blo 770335 2934893 := bstep (se 3 (by rfl) ⟨550292, by rfl⟩ : syracuseStep 2934893 = 1100585) B1100585
theorem B772303 : Blo 770335 772303 := bstep (se 1 (by rfl) ⟨579227, by rfl⟩ : syracuseStep 772303 = 1158455) B1158455
theorem B772415 : Blo 770335 772415 := bstep (se 1 (by rfl) ⟨579311, by rfl⟩ : syracuseStep 772415 = 1158623) B1158623
theorem B772559 : Blo 770335 772559 := bstep (se 1 (by rfl) ⟨579419, by rfl⟩ : syracuseStep 772559 = 1158839) B1158839
theorem B2345555 : Blo 770335 2345555 := bstep (se 1 (by rfl) ⟨1759166, by rfl⟩ : syracuseStep 2345555 = 3518333) B3518333
theorem B772699 : Blo 770335 772699 := bstep (se 1 (by rfl) ⟨579524, by rfl⟩ : syracuseStep 772699 = 1159049) B1159049
theorem B5655155 : Blo 770335 5655155 := bstep (se 1 (by rfl) ⟨4241366, by rfl⟩ : syracuseStep 5655155 = 8482733) B8482733
theorem B772863 : Blo 770335 772863 := bstep (se 1 (by rfl) ⟨579647, by rfl⟩ : syracuseStep 772863 = 1159295) B1159295
theorem B3918617 : Blo 770335 3918617 := bstep (se 2 (by rfl) ⟨1469481, by rfl⟩ : syracuseStep 3918617 = 2938963) B2938963
theorem B5294909 : Blo 770335 5294909 := bstep (se 3 (by rfl) ⟨992795, by rfl⟩ : syracuseStep 5294909 = 1985591) B1985591
theorem B2608199 : Blo 770335 2608199 := bstep (se 1 (by rfl) ⟨1956149, by rfl⟩ : syracuseStep 2608199 = 3912299) B3912299
theorem B773287 : Blo 770335 773287 := bstep (se 1 (by rfl) ⟨579965, by rfl⟩ : syracuseStep 773287 = 1159931) B1159931
theorem B2608523 : Blo 770335 2608523 := bstep (se 1 (by rfl) ⟨1956392, by rfl⟩ : syracuseStep 2608523 = 3912785) B3912785
theorem B773583 : Blo 770335 773583 := bstep (se 1 (by rfl) ⟨580187, by rfl⟩ : syracuseStep 773583 = 1160375) B1160375
theorem B773743 : Blo 770335 773743 := bstep (se 1 (by rfl) ⟨580307, by rfl⟩ : syracuseStep 773743 = 1160615) B1160615
theorem B773863 : Blo 770335 773863 := bstep (se 1 (by rfl) ⟨580397, by rfl⟩ : syracuseStep 773863 = 1160795) B1160795
theorem B6606791 : Blo 770335 6606791 := bstep (se 1 (by rfl) ⟨4955093, by rfl⟩ : syracuseStep 6606791 = 9910187) B9910187
theorem B774171 : Blo 770335 774171 := bstep (se 1 (by rfl) ⟨580628, by rfl⟩ : syracuseStep 774171 = 1161257) B1161257
theorem B774191 : Blo 770335 774191 := bstep (se 1 (by rfl) ⟨580643, by rfl⟩ : syracuseStep 774191 = 1161287) B1161287
theorem B2609279 : Blo 770335 2609279 := bstep (se 1 (by rfl) ⟨1956959, by rfl⟩ : syracuseStep 2609279 = 3913919) B3913919
theorem B1953953 : Blo 770335 1953953 := bstep (se 2 (by rfl) ⟨732732, by rfl⟩ : syracuseStep 1953953 = 1465465) B1465465
theorem B16699567 : Blo 770335 16699567 := bstep (se 1 (by rfl) ⟨12524675, by rfl⟩ : syracuseStep 16699567 = 25049351) B25049351
theorem B4935977 : Blo 770335 4935977 := bstep (se 2 (by rfl) ⟨1850991, by rfl⟩ : syracuseStep 4935977 = 3701983) B3701983
theorem B1757999 : Blo 770335 1757999 := bstep (se 1 (by rfl) ⟨1318499, by rfl⟩ : syracuseStep 1757999 = 2636999) B2636999
theorem B7918397 : Blo 770335 7918397 := bstep (se 3 (by rfl) ⟨1484699, by rfl⟩ : syracuseStep 7918397 = 2969399) B2969399
theorem B18044315 : Blo 770335 18044315 := bstep (se 1 (by rfl) ⟨13533236, by rfl⟩ : syracuseStep 18044315 = 27066473) B27066473
theorem B2610683 : Blo 770335 2610683 := bstep (se 1 (by rfl) ⟨1958012, by rfl⟩ : syracuseStep 2610683 = 3916025) B3916025
theorem B1955623 : Blo 770335 1955623 := bstep (se 1 (by rfl) ⟨1466717, by rfl⟩ : syracuseStep 1955623 = 2933435) B2933435
theorem B2611115 : Blo 770335 2611115 := bstep (se 1 (by rfl) ⟨1958336, by rfl⟩ : syracuseStep 2611115 = 3916673) B3916673
theorem B3299399 : Blo 770335 3299399 := bstep (se 1 (by rfl) ⟨2474549, by rfl⟩ : syracuseStep 3299399 = 4949099) B4949099
theorem B2611655 : Blo 770335 2611655 := bstep (se 1 (by rfl) ⟨1958741, by rfl⟩ : syracuseStep 2611655 = 3917483) B3917483
theorem B2939449 : Blo 770335 2939449 := bstep (se 2 (by rfl) ⟨1102293, by rfl⟩ : syracuseStep 2939449 = 2204587) B2204587
theorem B2611979 : Blo 770335 2611979 := bstep (se 1 (by rfl) ⟨1958984, by rfl⟩ : syracuseStep 2611979 = 3917969) B3917969
theorem B4938691 : Blo 770335 4938691 := bstep (se 1 (by rfl) ⟨3704018, by rfl⟩ : syracuseStep 4938691 = 7408037) B7408037
theorem B1957193 : Blo 770335 1957193 := bstep (se 2 (by rfl) ⟨733947, by rfl⟩ : syracuseStep 1957193 = 1467895) B1467895
theorem B1465769 : Blo 770335 1465769 := bstep (se 2 (by rfl) ⟨549663, by rfl⟩ : syracuseStep 1465769 = 1099327) B1099327
theorem B44522945 : Blo 770335 44522945 := bstep (se 2 (by rfl) ⟨16696104, by rfl⟩ : syracuseStep 44522945 = 33392209) B33392209
theorem B1957729 : Blo 770335 1957729 := bstep (se 2 (by rfl) ⟨734148, by rfl⟩ : syracuseStep 1957729 = 1468297) B1468297
theorem B2613113 : Blo 770335 2613113 := bstep (se 2 (by rfl) ⟨979917, by rfl⟩ : syracuseStep 2613113 = 1959835) B1959835
theorem B1957871 : Blo 770335 1957871 := bstep (se 1 (by rfl) ⟨1468403, by rfl⟩ : syracuseStep 1957871 = 2936807) B2936807
theorem B1302763 : Blo 770335 1302763 := bstep (se 1 (by rfl) ⟨977072, by rfl⟩ : syracuseStep 1302763 = 1954145) B1954145
theorem B1171751 : Blo 770335 1171751 := bstep (se 1 (by rfl) ⟨878813, by rfl⟩ : syracuseStep 1171751 = 1757627) B1757627
theorem B1467067 : Blo 770335 1467067 := bstep (se 1 (by rfl) ⟨1100300, by rfl⟩ : syracuseStep 1467067 = 2200601) B2200601
theorem B1958681 : Blo 770335 1958681 := bstep (se 2 (by rfl) ⟨734505, by rfl⟩ : syracuseStep 1958681 = 1469011) B1469011
theorem B1467553 : Blo 770335 1467553 := bstep (se 2 (by rfl) ⟨550332, by rfl⟩ : syracuseStep 1467553 = 1100665) B1100665
theorem B1959187 : Blo 770335 1959187 := bstep (se 1 (by rfl) ⟨1469390, by rfl⟩ : syracuseStep 1959187 = 2938781) B2938781
theorem B976207 : Blo 770335 976207 := bstep (se 1 (by rfl) ⟨732155, by rfl⟩ : syracuseStep 976207 = 1464311) B1464311
theorem B25060765 : Blo 770335 25060765 := bstep (se 3 (by rfl) ⟨4698893, by rfl⟩ : syracuseStep 25060765 = 9397787) B9397787
theorem B5858729 : Blo 770335 5858729 := bstep (se 2 (by rfl) ⟨2197023, by rfl⟩ : syracuseStep 5858729 = 4394047) B4394047
theorem B1304039 : Blo 770335 1304039 := bstep (se 1 (by rfl) ⟨978029, by rfl⟩ : syracuseStep 1304039 = 1956059) B1956059
theorem B9922283 : Blo 770335 9922283 := bstep (se 1 (by rfl) ⟨7441712, by rfl⟩ : syracuseStep 9922283 = 14883425) B14883425
theorem B976799 : Blo 770335 976799 := bstep (se 1 (by rfl) ⟨732599, by rfl⟩ : syracuseStep 976799 = 1465199) B1465199
theorem B21161891 : Blo 770335 21161891 := bstep (se 1 (by rfl) ⟨15871418, by rfl⟩ : syracuseStep 21161891 = 31742837) B31742837
theorem B1566875 : Blo 770335 1566875 := bstep (se 1 (by rfl) ⟨1175156, by rfl⟩ : syracuseStep 1566875 = 2350313) B2350313
theorem B22309451 : Blo 770335 22309451 := bstep (se 1 (by rfl) ⟨16732088, by rfl⟩ : syracuseStep 22309451 = 33464177) B33464177
theorem B9399347 : Blo 770335 9399347 := bstep (se 1 (by rfl) ⟨7049510, by rfl⟩ : syracuseStep 9399347 = 14099021) B14099021
theorem B1567855 : Blo 770335 1567855 := bstep (se 1 (by rfl) ⟨1175891, by rfl⟩ : syracuseStep 1567855 = 2351783) B2351783
theorem B978095 : Blo 770335 978095 := bstep (se 1 (by rfl) ⟨733571, by rfl⟩ : syracuseStep 978095 = 1467143) B1467143
theorem B978247 : Blo 770335 978247 := bstep (se 1 (by rfl) ⟨733685, by rfl⟩ : syracuseStep 978247 = 1467371) B1467371
theorem B1765217 : Blo 770335 1765217 := bstep (se 2 (by rfl) ⟨661956, by rfl⟩ : syracuseStep 1765217 = 1323913) B1323913
theorem B1175887 : Blo 770335 1175887 := bstep (se 1 (by rfl) ⟨881915, by rfl⟩ : syracuseStep 1175887 = 1763831) B1763831
theorem B35680769 : Blo 770335 35680769 := bstep (se 2 (by rfl) ⟨13380288, by rfl⟩ : syracuseStep 35680769 = 26760577) B26760577
theorem B43381511 : Blo 770335 43381511 := bstep (se 1 (by rfl) ⟨32536133, by rfl⟩ : syracuseStep 43381511 = 65072267) B65072267
theorem B18773207 : Blo 770335 18773207 := bstep (se 1 (by rfl) ⟨14079905, by rfl⟩ : syracuseStep 18773207 = 28159811) B28159811
theorem B4388489 : Blo 770335 4388489 := bstep (se 2 (by rfl) ⟨1645683, by rfl⟩ : syracuseStep 4388489 = 3291367) B3291367
theorem B1734623 : Blo 770335 1734623 := bstep (se 1 (by rfl) ⟨1300967, by rfl⟩ : syracuseStep 1734623 = 2601935) B2601935
theorem B1734695 : Blo 770335 1734695 := bstep (se 1 (by rfl) ⟨1301021, by rfl⟩ : syracuseStep 1734695 = 2602043) B2602043
theorem B1734875 : Blo 770335 1734875 := bstep (se 1 (by rfl) ⟨1301156, by rfl⟩ : syracuseStep 1734875 = 2602313) B2602313
theorem B1735073 : Blo 770335 1735073 := bstep (se 2 (by rfl) ⟨650652, by rfl⟩ : syracuseStep 1735073 = 1301305) B1301305
theorem B1735145 : Blo 770335 1735145 := bstep (se 2 (by rfl) ⟨650679, by rfl⟩ : syracuseStep 1735145 = 1301359) B1301359
theorem B28572425 : Blo 770335 28572425 := bstep (se 2 (by rfl) ⟨10714659, by rfl⟩ : syracuseStep 28572425 = 21429319) B21429319
theorem B1735775 : Blo 770335 1735775 := bstep (se 1 (by rfl) ⟨1301831, by rfl⟩ : syracuseStep 1735775 = 2603663) B2603663
theorem B19004669 : Blo 770335 19004669 := bstep (se 3 (by rfl) ⟨3563375, by rfl⟩ : syracuseStep 19004669 = 7126751) B7126751
theorem B1735991 : Blo 770335 1735991 := bstep (se 1 (by rfl) ⟨1301993, by rfl⟩ : syracuseStep 1735991 = 2603987) B2603987
theorem B1736171 : Blo 770335 1736171 := bstep (se 1 (by rfl) ⟨1302128, by rfl⟩ : syracuseStep 1736171 = 2604257) B2604257
theorem B1736603 : Blo 770335 1736603 := bstep (se 1 (by rfl) ⟨1302452, by rfl⟩ : syracuseStep 1736603 = 2604905) B2604905
theorem B5439791 : Blo 770335 5439791 := bstep (se 1 (by rfl) ⟨4079843, by rfl⟩ : syracuseStep 5439791 = 8159687) B8159687
theorem B1737017 : Blo 770335 1737017 := bstep (se 2 (by rfl) ⟨651381, by rfl⟩ : syracuseStep 1737017 = 1302763) B1302763
theorem B2196193 : Blo 770335 2196193 := bstep (se 2 (by rfl) ⟨823572, by rfl⟩ : syracuseStep 2196193 = 1647145) B1647145
theorem B1737467 : Blo 770335 1737467 := bstep (se 1 (by rfl) ⟨1303100, by rfl⟩ : syracuseStep 1737467 = 2606201) B2606201
theorem B9897065 : Blo 770335 9897065 := bstep (se 2 (by rfl) ⟨3711399, by rfl⟩ : syracuseStep 9897065 = 7422799) B7422799
theorem B1738799 : Blo 770335 1738799 := bstep (se 1 (by rfl) ⟨1304099, by rfl⟩ : syracuseStep 1738799 = 2608199) B2608199
theorem B1739015 : Blo 770335 1739015 := bstep (se 1 (by rfl) ⟨1304261, by rfl⟩ : syracuseStep 1739015 = 2608523) B2608523
theorem B1739519 : Blo 770335 1739519 := bstep (se 1 (by rfl) ⟨1304639, by rfl⟩ : syracuseStep 1739519 = 2609279) B2609279
theorem B5278931 : Blo 770335 5278931 := bstep (se 1 (by rfl) ⟨3959198, by rfl⟩ : syracuseStep 5278931 = 7918397) B7918397
theorem B12029543 : Blo 770335 12029543 := bstep (se 1 (by rfl) ⟨9022157, by rfl⟩ : syracuseStep 12029543 = 18044315) B18044315
theorem B1740455 : Blo 770335 1740455 := bstep (se 1 (by rfl) ⟨1305341, by rfl⟩ : syracuseStep 1740455 = 2610683) B2610683
theorem B1740743 : Blo 770335 1740743 := bstep (se 1 (by rfl) ⟨1305557, by rfl⟩ : syracuseStep 1740743 = 2611115) B2611115
theorem B2199599 : Blo 770335 2199599 := bstep (se 1 (by rfl) ⟨1649699, by rfl⟩ : syracuseStep 2199599 = 3299399) B3299399
theorem B3903713 : Blo 770335 3903713 := bstep (se 2 (by rfl) ⟨1463892, by rfl⟩ : syracuseStep 3903713 = 2927785) B2927785
theorem B1741103 : Blo 770335 1741103 := bstep (se 1 (by rfl) ⟨1305827, by rfl⟩ : syracuseStep 1741103 = 2611655) B2611655
theorem B1741319 : Blo 770335 1741319 := bstep (se 1 (by rfl) ⟨1305989, by rfl⟩ : syracuseStep 1741319 = 2611979) B2611979
theorem B1742075 : Blo 770335 1742075 := bstep (se 1 (by rfl) ⟨1306556, by rfl⟩ : syracuseStep 1742075 = 2613113) B2613113
theorem B8361893 : Blo 770335 8361893 := bstep (se 4 (by rfl) ⟨783927, by rfl⟩ : syracuseStep 8361893 = 1567855) B1567855
theorem B75110327 : Blo 770335 75110327 := bstep (se 1 (by rfl) ⟨56332745, by rfl⟩ : syracuseStep 75110327 = 112665491) B112665491
theorem B3905819 : Blo 770335 3905819 := bstep (se 1 (by rfl) ⟨2929364, by rfl⟩ : syracuseStep 3905819 = 5858729) B5858729
theorem B15080413 : Blo 770335 15080413 := bstep (se 3 (by rfl) ⟨2827577, by rfl⟩ : syracuseStep 15080413 = 5655155) B5655155
theorem B6266231 : Blo 770335 6266231 := bstep (se 1 (by rfl) ⟨4699673, by rfl⟩ : syracuseStep 6266231 = 9399347) B9399347
theorem B2925659 : Blo 770335 2925659 := bstep (se 1 (by rfl) ⟨2194244, by rfl⟩ : syracuseStep 2925659 = 4388489) B4388489
theorem B1156415 : Blo 770335 1156415 := bstep (se 1 (by rfl) ⟨867311, by rfl⟩ : syracuseStep 1156415 = 1734623) B1734623
theorem B1156463 : Blo 770335 1156463 := bstep (se 1 (by rfl) ⟨867347, by rfl⟩ : syracuseStep 1156463 = 1734695) B1734695
theorem B1156583 : Blo 770335 1156583 := bstep (se 1 (by rfl) ⟨867437, by rfl⟩ : syracuseStep 1156583 = 1734875) B1734875
theorem B1156715 : Blo 770335 1156715 := bstep (se 1 (by rfl) ⟨867536, by rfl⟩ : syracuseStep 1156715 = 1735073) B1735073
theorem B1156763 : Blo 770335 1156763 := bstep (se 1 (by rfl) ⟨867572, by rfl⟩ : syracuseStep 1156763 = 1735145) B1735145
theorem B19048283 : Blo 770335 19048283 := bstep (se 1 (by rfl) ⟨14286212, by rfl⟩ : syracuseStep 19048283 = 28572425) B28572425
theorem B25110587 : Blo 770335 25110587 := bstep (se 1 (by rfl) ⟨18832940, by rfl⟩ : syracuseStep 25110587 = 37665881) B37665881
theorem B1157183 : Blo 770335 1157183 := bstep (se 1 (by rfl) ⟨867887, by rfl⟩ : syracuseStep 1157183 = 1735775) B1735775
theorem B1157327 : Blo 770335 1157327 := bstep (se 1 (by rfl) ⟨867995, by rfl⟩ : syracuseStep 1157327 = 1735991) B1735991
theorem B1157447 : Blo 770335 1157447 := bstep (se 1 (by rfl) ⟨868085, by rfl⟩ : syracuseStep 1157447 = 1736171) B1736171
theorem B1157735 : Blo 770335 1157735 := bstep (se 1 (by rfl) ⟨868301, by rfl⟩ : syracuseStep 1157735 = 1736603) B1736603
theorem B1158281 : Blo 770335 1158281 := bstep (se 2 (by rfl) ⟨434355, by rfl⟩ : syracuseStep 1158281 = 868711) B868711
theorem B3910841 : Blo 770335 3910841 := bstep (se 2 (by rfl) ⟨1466565, by rfl⟩ : syracuseStep 3910841 = 2933131) B2933131
theorem B1158335 : Blo 770335 1158335 := bstep (se 1 (by rfl) ⟨868751, by rfl⟩ : syracuseStep 1158335 = 1737503) B1737503
theorem B3911003 : Blo 770335 3911003 := bstep (se 1 (by rfl) ⟨2933252, by rfl⟩ : syracuseStep 3911003 = 5866505) B5866505
theorem B3124669 : Blo 770335 3124669 := bstep (se 3 (by rfl) ⟨585875, by rfl⟩ : syracuseStep 3124669 = 1171751) B1171751
theorem B144748129 : Blo 770335 144748129 := bstep (se 2 (by rfl) ⟨54280548, by rfl⟩ : syracuseStep 144748129 = 108561097) B108561097
theorem B2600639 : Blo 770335 2600639 := bstep (se 1 (by rfl) ⟨1950479, by rfl⟩ : syracuseStep 2600639 = 3900959) B3900959
theorem B3124927 : Blo 770335 3124927 := bstep (se 1 (by rfl) ⟨2343695, by rfl⟩ : syracuseStep 3124927 = 4687391) B4687391
theorem B4404527 : Blo 770335 4404527 := bstep (se 1 (by rfl) ⟨3303395, by rfl⟩ : syracuseStep 4404527 = 6606791) B6606791
theorem B1160519 : Blo 770335 1160519 := bstep (se 1 (by rfl) ⟨870389, by rfl⟩ : syracuseStep 1160519 = 1740779) B1740779
theorem B3290651 : Blo 770335 3290651 := bstep (se 1 (by rfl) ⟨2467988, by rfl⟩ : syracuseStep 3290651 = 4935977) B4935977
theorem B2930489 : Blo 770335 2930489 := bstep (se 2 (by rfl) ⟨1098933, by rfl⟩ : syracuseStep 2930489 = 2197867) B2197867
theorem B31700807 : Blo 770335 31700807 := bstep (se 1 (by rfl) ⟨23775605, by rfl⟩ : syracuseStep 31700807 = 47551211) B47551211
theorem B3913595 : Blo 770335 3913595 := bstep (se 1 (by rfl) ⟨2935196, by rfl⟩ : syracuseStep 3913595 = 5870393) B5870393
theorem B2602907 : Blo 770335 2602907 := bstep (se 1 (by rfl) ⟨1952180, by rfl⟩ : syracuseStep 2602907 = 3904361) B3904361
theorem B1489279 : Blo 770335 1489279 := bstep (se 1 (by rfl) ⟨1116959, by rfl⟩ : syracuseStep 1489279 = 2233919) B2233919
theorem B25082567 : Blo 770335 25082567 := bstep (se 1 (by rfl) ⟨18811925, by rfl⟩ : syracuseStep 25082567 = 37623851) B37623851
theorem B4177403 : Blo 770335 4177403 := bstep (se 1 (by rfl) ⟨3133052, by rfl⟩ : syracuseStep 4177403 = 6266105) B6266105
theorem B2604797 : Blo 770335 2604797 := bstep (se 3 (by rfl) ⟨488399, by rfl⟩ : syracuseStep 2604797 = 976799) B976799
theorem B3915539 : Blo 770335 3915539 := bstep (se 1 (by rfl) ⟨2936654, by rfl⟩ : syracuseStep 3915539 = 5873309) B5873309
theorem B2604959 : Blo 770335 2604959 := bstep (se 1 (by rfl) ⟨1953719, by rfl⟩ : syracuseStep 2604959 = 3907439) B3907439
theorem B1097641 : Blo 770335 1097641 := bstep (se 2 (by rfl) ⟨411615, by rfl⟩ : syracuseStep 1097641 = 823231) B823231
theorem B22266089 : Blo 770335 22266089 := bstep (se 2 (by rfl) ⟨8349783, by rfl⟩ : syracuseStep 22266089 = 16699567) B16699567
theorem B770459 : Blo 770335 770459 := bstep (se 1 (by rfl) ⟨577844, by rfl⟩ : syracuseStep 770459 = 1155689) B1155689
theorem B770463 : Blo 770335 770463 := bstep (se 1 (by rfl) ⟨577847, by rfl⟩ : syracuseStep 770463 = 1155695) B1155695
theorem B6013703 : Blo 770335 6013703 := bstep (se 1 (by rfl) ⟨4510277, by rfl⟩ : syracuseStep 6013703 = 9020555) B9020555
theorem B770879 : Blo 770335 770879 := bstep (se 1 (by rfl) ⟨578159, by rfl⟩ : syracuseStep 770879 = 1156319) B1156319
theorem B771039 : Blo 770335 771039 := bstep (se 1 (by rfl) ⟨578279, by rfl⟩ : syracuseStep 771039 = 1156559) B1156559
theorem B869359 : Blo 770335 869359 := bstep (se 1 (by rfl) ⟨652019, by rfl⟩ : syracuseStep 869359 = 1304039) B1304039
theorem B771163 : Blo 770335 771163 := bstep (se 1 (by rfl) ⟨578372, by rfl⟩ : syracuseStep 771163 = 1156745) B1156745
theorem B771199 : Blo 770335 771199 := bstep (se 1 (by rfl) ⟨578399, by rfl⟩ : syracuseStep 771199 = 1156799) B1156799
theorem B771303 : Blo 770335 771303 := bstep (se 1 (by rfl) ⟨578477, by rfl⟩ : syracuseStep 771303 = 1156955) B1156955
theorem B14107927 : Blo 770335 14107927 := bstep (se 1 (by rfl) ⟨10580945, by rfl⟩ : syracuseStep 14107927 = 21161891) B21161891
theorem B771559 : Blo 770335 771559 := bstep (se 1 (by rfl) ⟨578669, by rfl⟩ : syracuseStep 771559 = 1157339) B1157339
theorem B771739 : Blo 770335 771739 := bstep (se 1 (by rfl) ⟨578804, by rfl⟩ : syracuseStep 771739 = 1157609) B1157609
theorem B1951391 : Blo 770335 1951391 := bstep (se 1 (by rfl) ⟨1463543, by rfl⟩ : syracuseStep 1951391 = 2927087) B2927087
theorem B771743 : Blo 770335 771743 := bstep (se 1 (by rfl) ⟨578807, by rfl⟩ : syracuseStep 771743 = 1157615) B1157615
theorem B771951 : Blo 770335 771951 := bstep (se 1 (by rfl) ⟨578963, by rfl⟩ : syracuseStep 771951 = 1157927) B1157927
theorem B771999 : Blo 770335 771999 := bstep (se 1 (by rfl) ⟨578999, by rfl⟩ : syracuseStep 771999 = 1157999) B1157999
theorem B772167 : Blo 770335 772167 := bstep (se 1 (by rfl) ⟨579125, by rfl⟩ : syracuseStep 772167 = 1158251) B1158251
theorem B8898767 : Blo 770335 8898767 := bstep (se 1 (by rfl) ⟨6674075, by rfl⟩ : syracuseStep 8898767 = 13348151) B13348151
theorem B772327 : Blo 770335 772327 := bstep (se 1 (by rfl) ⟨579245, by rfl⟩ : syracuseStep 772327 = 1158491) B1158491
theorem B772347 : Blo 770335 772347 := bstep (se 1 (by rfl) ⟨579260, by rfl⟩ : syracuseStep 772347 = 1158521) B1158521
theorem B1100027 : Blo 770335 1100027 := bstep (se 1 (by rfl) ⟨825020, by rfl⟩ : syracuseStep 1100027 = 1650041) B1650041
theorem B772351 : Blo 770335 772351 := bstep (se 1 (by rfl) ⟨579263, by rfl⟩ : syracuseStep 772351 = 1158527) B1158527
theorem B2607497 : Blo 770335 2607497 := bstep (se 2 (by rfl) ⟨977811, by rfl⟩ : syracuseStep 2607497 = 1955623) B1955623
theorem B772507 : Blo 770335 772507 := bstep (se 1 (by rfl) ⟨579380, by rfl⟩ : syracuseStep 772507 = 1158761) B1158761
theorem B2935379 : Blo 770335 2935379 := bstep (se 1 (by rfl) ⟨2201534, by rfl⟩ : syracuseStep 2935379 = 4403069) B4403069
theorem B772767 : Blo 770335 772767 := bstep (se 1 (by rfl) ⟨579575, by rfl⟩ : syracuseStep 772767 = 1159151) B1159151
theorem B772847 : Blo 770335 772847 := bstep (se 1 (by rfl) ⟨579635, by rfl⟩ : syracuseStep 772847 = 1159271) B1159271
theorem B772927 : Blo 770335 772927 := bstep (se 1 (by rfl) ⟨579695, by rfl⟩ : syracuseStep 772927 = 1159391) B1159391
theorem B772967 : Blo 770335 772967 := bstep (se 1 (by rfl) ⟨579725, by rfl⟩ : syracuseStep 772967 = 1159451) B1159451
theorem B6605833 : Blo 770335 6605833 := bstep (se 2 (by rfl) ⟨2477187, by rfl⟩ : syracuseStep 6605833 = 4954375) B4954375
theorem B773231 : Blo 770335 773231 := bstep (se 1 (by rfl) ⟨579923, by rfl⟩ : syracuseStep 773231 = 1159847) B1159847
theorem B2608253 : Blo 770335 2608253 := bstep (se 3 (by rfl) ⟨489047, by rfl⟩ : syracuseStep 2608253 = 978095) B978095
theorem B28921007 : Blo 770335 28921007 := bstep (se 1 (by rfl) ⟨21690755, by rfl⟩ : syracuseStep 28921007 = 43381511) B43381511
theorem B773311 : Blo 770335 773311 := bstep (se 1 (by rfl) ⟨579983, by rfl⟩ : syracuseStep 773311 = 1159967) B1159967
theorem B773327 : Blo 770335 773327 := bstep (se 1 (by rfl) ⟨579995, by rfl⟩ : syracuseStep 773327 = 1159991) B1159991
theorem B2936033 : Blo 770335 2936033 := bstep (se 2 (by rfl) ⟨1101012, by rfl⟩ : syracuseStep 2936033 = 2202025) B2202025
theorem B773403 : Blo 770335 773403 := bstep (se 1 (by rfl) ⟨580052, by rfl⟩ : syracuseStep 773403 = 1160105) B1160105
theorem B773447 : Blo 770335 773447 := bstep (se 1 (by rfl) ⟨580085, by rfl⟩ : syracuseStep 773447 = 1160171) B1160171
theorem B3919265 : Blo 770335 3919265 := bstep (se 2 (by rfl) ⟨1469724, by rfl⟩ : syracuseStep 3919265 = 2939449) B2939449
theorem B773631 : Blo 770335 773631 := bstep (se 1 (by rfl) ⟨580223, by rfl⟩ : syracuseStep 773631 = 1160447) B1160447
theorem B773659 : Blo 770335 773659 := bstep (se 1 (by rfl) ⟨580244, by rfl⟩ : syracuseStep 773659 = 1160489) B1160489
theorem B774055 : Blo 770335 774055 := bstep (se 1 (by rfl) ⟨580541, by rfl⟩ : syracuseStep 774055 = 1161083) B1161083
theorem B774079 : Blo 770335 774079 := bstep (se 1 (by rfl) ⟨580559, by rfl⟩ : syracuseStep 774079 = 1161119) B1161119
theorem B774215 : Blo 770335 774215 := bstep (se 1 (by rfl) ⟨580661, by rfl⟩ : syracuseStep 774215 = 1161323) B1161323
theorem B774235 : Blo 770335 774235 := bstep (se 1 (by rfl) ⟨580676, by rfl⟩ : syracuseStep 774235 = 1161353) B1161353
theorem B1953983 : Blo 770335 1953983 := bstep (se 1 (by rfl) ⟨1465487, by rfl⟩ : syracuseStep 1953983 = 2930975) B2930975
theorem B774335 : Blo 770335 774335 := bstep (se 1 (by rfl) ⟨580751, by rfl⟩ : syracuseStep 774335 = 1161503) B1161503
theorem B2478367 : Blo 770335 2478367 := bstep (se 1 (by rfl) ⟨1858775, by rfl⟩ : syracuseStep 2478367 = 3717551) B3717551
theorem B12669779 : Blo 770335 12669779 := bstep (se 1 (by rfl) ⟨9502334, by rfl⟩ : syracuseStep 12669779 = 19004669) B19004669
theorem B2610305 : Blo 770335 2610305 := bstep (se 2 (by rfl) ⟨978864, by rfl⟩ : syracuseStep 2610305 = 1957729) B1957729
theorem B3298715 : Blo 770335 3298715 := bstep (se 1 (by rfl) ⟨2474036, by rfl⟩ : syracuseStep 3298715 = 4948073) B4948073
theorem B5854841 : Blo 770335 5854841 := bstep (se 2 (by rfl) ⟨2195565, by rfl⟩ : syracuseStep 5854841 = 4391131) B4391131
theorem B6608567 : Blo 770335 6608567 := bstep (se 1 (by rfl) ⟨4956425, by rfl⟩ : syracuseStep 6608567 = 9912851) B9912851
theorem B2643995 : Blo 770335 2643995 := bstep (se 1 (by rfl) ⟨1982996, by rfl⟩ : syracuseStep 2643995 = 3965993) B3965993
theorem B1300711 : Blo 770335 1300711 := bstep (se 1 (by rfl) ⟨975533, by rfl⟩ : syracuseStep 1300711 = 1951067) B1951067
theorem B1956089 : Blo 770335 1956089 := bstep (se 2 (by rfl) ⟨733533, by rfl⟩ : syracuseStep 1956089 = 1467067) B1467067
theorem B3758375 : Blo 770335 3758375 := bstep (se 1 (by rfl) ⟨2818781, by rfl⟩ : syracuseStep 3758375 = 5637563) B5637563
theorem B1956251 : Blo 770335 1956251 := bstep (se 1 (by rfl) ⟨1467188, by rfl⟩ : syracuseStep 1956251 = 2934377) B2934377
theorem B2611871 : Blo 770335 2611871 := bstep (se 1 (by rfl) ⟨1958903, by rfl⟩ : syracuseStep 2611871 = 3917807) B3917807
theorem B1956595 : Blo 770335 1956595 := bstep (se 1 (by rfl) ⟨1467446, by rfl⟩ : syracuseStep 1956595 = 2934893) B2934893
theorem B1956737 : Blo 770335 1956737 := bstep (se 2 (by rfl) ⟨733776, by rfl⟩ : syracuseStep 1956737 = 1467553) B1467553
theorem B2612249 : Blo 770335 2612249 := bstep (se 2 (by rfl) ⟨979593, by rfl⟩ : syracuseStep 2612249 = 1959187) B1959187
theorem B1465427 : Blo 770335 1465427 := bstep (se 1 (by rfl) ⟨1099070, by rfl⟩ : syracuseStep 1465427 = 2198141) B2198141
theorem B1301609 : Blo 770335 1301609 := bstep (se 2 (by rfl) ⟨488103, by rfl⟩ : syracuseStep 1301609 = 976207) B976207
theorem B2612411 : Blo 770335 2612411 := bstep (se 1 (by rfl) ⟨1959308, by rfl⟩ : syracuseStep 2612411 = 3918617) B3918617
theorem B33414353 : Blo 770335 33414353 := bstep (se 2 (by rfl) ⟨12530382, by rfl⟩ : syracuseStep 33414353 = 25060765) B25060765
theorem B3529939 : Blo 770335 3529939 := bstep (se 1 (by rfl) ⟨2647454, by rfl⟩ : syracuseStep 3529939 = 5294909) B5294909
theorem B6610481 : Blo 770335 6610481 := bstep (se 2 (by rfl) ⟨2478930, by rfl⟩ : syracuseStep 6610481 = 4957861) B4957861
theorem B1302635 : Blo 770335 1302635 := bstep (se 1 (by rfl) ⟨976976, by rfl⟩ : syracuseStep 1302635 = 1953953) B1953953
theorem B2777323 : Blo 770335 2777323 := bstep (se 1 (by rfl) ⟨2082992, by rfl⟩ : syracuseStep 2777323 = 4165985) B4165985
theorem B6250891 : Blo 770335 6250891 := bstep (se 1 (by rfl) ⟨4688168, by rfl⟩ : syracuseStep 6250891 = 9376337) B9376337
theorem B1171999 : Blo 770335 1171999 := bstep (se 1 (by rfl) ⟨878999, by rfl⟩ : syracuseStep 1171999 = 1757999) B1757999
theorem B4940615 : Blo 770335 4940615 := bstep (se 1 (by rfl) ⟨3705461, by rfl⟩ : syracuseStep 4940615 = 7410923) B7410923
theorem B3302491 : Blo 770335 3302491 := bstep (se 1 (by rfl) ⟨2476868, by rfl⟩ : syracuseStep 3302491 = 4953737) B4953737
theorem B1238761 : Blo 770335 1238761 := bstep (se 2 (by rfl) ⟨464535, by rfl⟩ : syracuseStep 1238761 = 929071) B929071
theorem B1205999 : Blo 770335 1205999 := bstep (se 1 (by rfl) ⟨904499, by rfl⟩ : syracuseStep 1205999 = 1808999) B1808999
theorem B1304329 : Blo 770335 1304329 := bstep (se 2 (by rfl) ⟨489123, by rfl⟩ : syracuseStep 1304329 = 978247) B978247
theorem B1304795 : Blo 770335 1304795 := bstep (se 1 (by rfl) ⟨978596, by rfl⟩ : syracuseStep 1304795 = 1957193) B1957193
theorem B977179 : Blo 770335 977179 := bstep (se 1 (by rfl) ⟨732884, by rfl⟩ : syracuseStep 977179 = 1465769) B1465769
theorem B29681963 : Blo 770335 29681963 := bstep (se 1 (by rfl) ⟨22261472, by rfl⟩ : syracuseStep 29681963 = 44522945) B44522945
theorem B1305247 : Blo 770335 1305247 := bstep (se 1 (by rfl) ⟨978935, by rfl⟩ : syracuseStep 1305247 = 1957871) B1957871
theorem B5860187 : Blo 770335 5860187 := bstep (se 1 (by rfl) ⟨4395140, by rfl⟩ : syracuseStep 5860187 = 8790281) B8790281
theorem B1567849 : Blo 770335 1567849 := bstep (se 2 (by rfl) ⟨587943, by rfl⟩ : syracuseStep 1567849 = 1175887) B1175887
theorem B1305787 : Blo 770335 1305787 := bstep (se 1 (by rfl) ⟨979340, by rfl⟩ : syracuseStep 1305787 = 1958681) B1958681
theorem B5565833 : Blo 770335 5565833 := bstep (se 2 (by rfl) ⟨2087187, by rfl⟩ : syracuseStep 5565833 = 4174375) B4174375
theorem B1469983 : Blo 770335 1469983 := bstep (se 1 (by rfl) ⟨1102487, by rfl⟩ : syracuseStep 1469983 = 2204975) B2204975
theorem B6614855 : Blo 770335 6614855 := bstep (se 1 (by rfl) ⟨4961141, by rfl⟩ : syracuseStep 6614855 = 9922283) B9922283
theorem B3305447 : Blo 770335 3305447 := bstep (se 1 (by rfl) ⟨2479085, by rfl⟩ : syracuseStep 3305447 = 4958171) B4958171
theorem B6582323 : Blo 770335 6582323 := bstep (se 1 (by rfl) ⟨4936742, by rfl⟩ : syracuseStep 6582323 = 9873485) B9873485
theorem B1044583 : Blo 770335 1044583 := bstep (se 1 (by rfl) ⟨783437, by rfl⟩ : syracuseStep 1044583 = 1566875) B1566875
theorem B6254813 : Blo 770335 6254813 := bstep (se 3 (by rfl) ⟨1172777, by rfl⟩ : syracuseStep 6254813 = 2345555) B2345555
theorem B14872967 : Blo 770335 14872967 := bstep (se 1 (by rfl) ⟨11154725, by rfl⟩ : syracuseStep 14872967 = 22309451) B22309451
theorem B5010541 : Blo 770335 5010541 := bstep (se 3 (by rfl) ⟨939476, by rfl⟩ : syracuseStep 5010541 = 1878953) B1878953
theorem B1176811 : Blo 770335 1176811 := bstep (se 1 (by rfl) ⟨882608, by rfl⟩ : syracuseStep 1176811 = 1765217) B1765217
theorem B23787179 : Blo 770335 23787179 := bstep (se 1 (by rfl) ⟨17840384, by rfl⟩ : syracuseStep 23787179 = 35680769) B35680769
theorem B6256763 : Blo 770335 6256763 := bstep (se 1 (by rfl) ⟨4692572, by rfl⟩ : syracuseStep 6256763 = 9385145) B9385145
theorem B12515471 : Blo 770335 12515471 := bstep (se 1 (by rfl) ⟨9386603, by rfl⟩ : syracuseStep 12515471 = 18773207) B18773207
theorem B1734911 : Blo 770335 1734911 := bstep (se 1 (by rfl) ⟨1301183, by rfl⟩ : syracuseStep 1734911 = 2602367) B2602367
theorem B2193743 : Blo 770335 2193743 := bstep (se 1 (by rfl) ⟨1645307, by rfl⟩ : syracuseStep 2193743 = 3290615) B3290615
theorem B6584921 : Blo 770335 6584921 := bstep (se 2 (by rfl) ⟨2469345, by rfl⟩ : syracuseStep 6584921 = 4938691) B4938691
theorem B20085407 : Blo 770335 20085407 := bstep (se 1 (by rfl) ⟨15064055, by rfl⟩ : syracuseStep 20085407 = 30128111) B30128111
theorem B51412151 : Blo 770335 51412151 := bstep (se 1 (by rfl) ⟨38559113, by rfl⟩ : syracuseStep 51412151 = 77118227) B77118227
theorem B14844059 : Blo 770335 14844059 := bstep (se 1 (by rfl) ⟨11133044, by rfl⟩ : syracuseStep 14844059 = 22266089) B22266089
theorem B3703097 : Blo 770335 3703097 := bstep (se 2 (by rfl) ⟨1388661, by rfl⟩ : syracuseStep 3703097 = 2777323) B2777323
theorem B5571109 : Blo 770335 5571109 := bstep (se 4 (by rfl) ⟨522291, by rfl⟩ : syracuseStep 5571109 = 1044583) B1044583
theorem B5932511 : Blo 770335 5932511 := bstep (se 1 (by rfl) ⟨4449383, by rfl⟩ : syracuseStep 5932511 = 8898767) B8898767
theorem B1738331 : Blo 770335 1738331 := bstep (se 1 (by rfl) ⟨1303748, by rfl⟩ : syracuseStep 1738331 = 2607497) B2607497
theorem B18810569 : Blo 770335 18810569 := bstep (se 2 (by rfl) ⟨7053963, by rfl⟩ : syracuseStep 18810569 = 14107927) B14107927
theorem B1738835 : Blo 770335 1738835 := bstep (se 1 (by rfl) ⟨1304126, by rfl⟩ : syracuseStep 1738835 = 2608253) B2608253
theorem B1739105 : Blo 770335 1739105 := bstep (se 2 (by rfl) ⟨652164, by rfl⟩ : syracuseStep 1739105 = 1304329) B1304329
theorem B1740203 : Blo 770335 1740203 := bstep (se 1 (by rfl) ⟨1305152, by rfl⟩ : syracuseStep 1740203 = 2610305) B2610305
theorem B1740329 : Blo 770335 1740329 := bstep (se 2 (by rfl) ⟨652623, by rfl⟩ : syracuseStep 1740329 = 1305247) B1305247
theorem B2199143 : Blo 770335 2199143 := bstep (se 1 (by rfl) ⟨1649357, by rfl⟩ : syracuseStep 2199143 = 3298715) B3298715
theorem B3903227 : Blo 770335 3903227 := bstep (se 1 (by rfl) ⟨2927420, by rfl⟩ : syracuseStep 3903227 = 5854841) B5854841
theorem B5574595 : Blo 770335 5574595 := bstep (se 1 (by rfl) ⟨4180946, by rfl⟩ : syracuseStep 5574595 = 8361893) B8361893
theorem B50073551 : Blo 770335 50073551 := bstep (se 1 (by rfl) ⟨37555163, by rfl⟩ : syracuseStep 50073551 = 75110327) B75110327
theorem B1741049 : Blo 770335 1741049 := bstep (se 2 (by rfl) ⟨652893, by rfl⟩ : syracuseStep 1741049 = 1305787) B1305787
theorem B1741247 : Blo 770335 1741247 := bstep (se 1 (by rfl) ⟨1305935, by rfl⟩ : syracuseStep 1741247 = 2611871) B2611871
theorem B4166225 : Blo 770335 4166225 := bstep (se 2 (by rfl) ⟨1562334, by rfl⟩ : syracuseStep 4166225 = 3124669) B3124669
theorem B1741499 : Blo 770335 1741499 := bstep (se 1 (by rfl) ⟨1306124, by rfl⟩ : syracuseStep 1741499 = 2612249) B2612249
theorem B1741607 : Blo 770335 1741607 := bstep (se 1 (by rfl) ⟨1306205, by rfl⟩ : syracuseStep 1741607 = 2612411) B2612411
theorem B4166569 : Blo 770335 4166569 := bstep (se 2 (by rfl) ⟨1562463, by rfl⟩ : syracuseStep 4166569 = 3124927) B3124927
theorem B3906791 : Blo 770335 3906791 := bstep (se 1 (by rfl) ⟨2930093, by rfl⟩ : syracuseStep 3906791 = 5860187) B5860187
theorem B3710555 : Blo 770335 3710555 := bstep (se 1 (by rfl) ⟨2782916, by rfl⟩ : syracuseStep 3710555 = 5565833) B5565833
theorem B2203631 : Blo 770335 2203631 := bstep (se 1 (by rfl) ⟨1652723, by rfl⟩ : syracuseStep 2203631 = 3305447) B3305447
theorem B4169875 : Blo 770335 4169875 := bstep (se 1 (by rfl) ⟨3127406, by rfl⟩ : syracuseStep 4169875 = 6254813) B6254813
theorem B4171175 : Blo 770335 4171175 := bstep (se 1 (by rfl) ⟨3128381, by rfl⟩ : syracuseStep 4171175 = 6256763) B6256763
theorem B1156607 : Blo 770335 1156607 := bstep (se 1 (by rfl) ⟨867455, by rfl⟩ : syracuseStep 1156607 = 1734911) B1734911
theorem B16721711 : Blo 770335 16721711 := bstep (se 1 (by rfl) ⟨12541283, by rfl⟩ : syracuseStep 16721711 = 25082567) B25082567
theorem B1158011 : Blo 770335 1158011 := bstep (se 1 (by rfl) ⟨868508, by rfl⟩ : syracuseStep 1158011 = 1737017) B1737017
theorem B1158311 : Blo 770335 1158311 := bstep (se 1 (by rfl) ⟨868733, by rfl⟩ : syracuseStep 1158311 = 1737467) B1737467
theorem B8334521 : Blo 770335 8334521 := bstep (se 2 (by rfl) ⟨3125445, by rfl⟩ : syracuseStep 8334521 = 6250891) B6250891
theorem B6598043 : Blo 770335 6598043 := bstep (se 1 (by rfl) ⟨4948532, by rfl⟩ : syracuseStep 6598043 = 9897065) B9897065
theorem B2928257 : Blo 770335 2928257 := bstep (se 2 (by rfl) ⟨1098096, by rfl⟩ : syracuseStep 2928257 = 2196193) B2196193
theorem B1159145 : Blo 770335 1159145 := bstep (se 2 (by rfl) ⟨434679, by rfl⟩ : syracuseStep 1159145 = 869359) B869359
theorem B1159199 : Blo 770335 1159199 := bstep (se 1 (by rfl) ⟨869399, by rfl⟩ : syracuseStep 1159199 = 1738799) B1738799
theorem B4403321 : Blo 770335 4403321 := bstep (se 2 (by rfl) ⟨1651245, by rfl⟩ : syracuseStep 4403321 = 3302491) B3302491
theorem B1159343 : Blo 770335 1159343 := bstep (se 1 (by rfl) ⟨869507, by rfl⟩ : syracuseStep 1159343 = 1739015) B1739015
theorem B1159679 : Blo 770335 1159679 := bstep (se 1 (by rfl) ⟨869759, by rfl⟩ : syracuseStep 1159679 = 1739519) B1739519
theorem B16036541 : Blo 770335 16036541 := bstep (se 3 (by rfl) ⟨3006851, by rfl⟩ : syracuseStep 16036541 = 6013703) B6013703
theorem B3519287 : Blo 770335 3519287 := bstep (se 1 (by rfl) ⟨2639465, by rfl⟩ : syracuseStep 3519287 = 5278931) B5278931
theorem B1651681 : Blo 770335 1651681 := bstep (se 2 (by rfl) ⟨619380, by rfl⟩ : syracuseStep 1651681 = 1238761) B1238761
theorem B1160303 : Blo 770335 1160303 := bstep (se 1 (by rfl) ⟨870227, by rfl⟩ : syracuseStep 1160303 = 1740455) B1740455
theorem B1160495 : Blo 770335 1160495 := bstep (se 1 (by rfl) ⟨870371, by rfl⟩ : syracuseStep 1160495 = 1740743) B1740743
theorem B2602475 : Blo 770335 2602475 := bstep (se 1 (by rfl) ⟨1951856, by rfl⟩ : syracuseStep 2602475 = 3903713) B3903713
theorem B1160735 : Blo 770335 1160735 := bstep (se 1 (by rfl) ⟨870551, by rfl⟩ : syracuseStep 1160735 = 1741103) B1741103
theorem B1160879 : Blo 770335 1160879 := bstep (se 1 (by rfl) ⟨870659, by rfl⟩ : syracuseStep 1160879 = 1741319) B1741319
theorem B1161383 : Blo 770335 1161383 := bstep (se 1 (by rfl) ⟨871037, by rfl⟩ : syracuseStep 1161383 = 1742075) B1742075
theorem B4405711 : Blo 770335 4405711 := bstep (se 1 (by rfl) ⟨3304283, by rfl⟩ : syracuseStep 4405711 = 6608567) B6608567
theorem B2603879 : Blo 770335 2603879 := bstep (se 1 (by rfl) ⟨1952909, by rfl⟩ : syracuseStep 2603879 = 3905819) B3905819
theorem B2505583 : Blo 770335 2505583 := bstep (se 1 (by rfl) ⟨1879187, by rfl⟩ : syracuseStep 2505583 = 3758375) B3758375
theorem B867739 : Blo 770335 867739 := bstep (se 1 (by rfl) ⟨650804, by rfl⟩ : syracuseStep 867739 = 1301609) B1301609
theorem B4177487 : Blo 770335 4177487 := bstep (se 1 (by rfl) ⟨3133115, by rfl⟩ : syracuseStep 4177487 = 6266231) B6266231
theorem B4406987 : Blo 770335 4406987 := bstep (se 1 (by rfl) ⟨3305240, by rfl⟩ : syracuseStep 4406987 = 6610481) B6610481
theorem B868423 : Blo 770335 868423 := bstep (se 1 (by rfl) ⟨651317, by rfl⟩ : syracuseStep 868423 = 1302635) B1302635
theorem B66961565 : Blo 770335 66961565 := bstep (se 3 (by rfl) ⟨12555293, by rfl⟩ : syracuseStep 66961565 = 25110587) B25110587
theorem B3293743 : Blo 770335 3293743 := bstep (se 1 (by rfl) ⟨2470307, by rfl⟩ : syracuseStep 3293743 = 4940615) B4940615
theorem B26722885 : Blo 770335 26722885 := bstep (se 4 (by rfl) ⟨2505270, by rfl⟩ : syracuseStep 26722885 = 5010541) B5010541
theorem B2933405 : Blo 770335 2933405 := bstep (se 3 (by rfl) ⟨550013, by rfl⟩ : syracuseStep 2933405 = 1100027) B1100027
theorem B1950439 : Blo 770335 1950439 := bstep (se 1 (by rfl) ⟨1462829, by rfl⟩ : syracuseStep 1950439 = 2925659) B2925659
theorem B5849981 : Blo 770335 5849981 := bstep (se 3 (by rfl) ⟨1096871, by rfl⟩ : syracuseStep 5849981 = 2193743) B2193743
theorem B770943 : Blo 770335 770943 := bstep (se 1 (by rfl) ⟨578207, by rfl⟩ : syracuseStep 770943 = 1156415) B1156415
theorem B770975 : Blo 770335 770975 := bstep (se 1 (by rfl) ⟨578231, by rfl⟩ : syracuseStep 770975 = 1156463) B1156463
theorem B771055 : Blo 770335 771055 := bstep (se 1 (by rfl) ⟨578291, by rfl⟩ : syracuseStep 771055 = 1156583) B1156583
theorem B771143 : Blo 770335 771143 := bstep (se 1 (by rfl) ⟨578357, by rfl⟩ : syracuseStep 771143 = 1156715) B1156715
theorem B771175 : Blo 770335 771175 := bstep (se 1 (by rfl) ⟨578381, by rfl⟩ : syracuseStep 771175 = 1156763) B1156763
theorem B803999 : Blo 770335 803999 := bstep (se 1 (by rfl) ⟨602999, by rfl⟩ : syracuseStep 803999 = 1205999) B1205999
theorem B6276325 : Blo 770335 6276325 := bstep (se 4 (by rfl) ⟨588405, by rfl⟩ : syracuseStep 6276325 = 1176811) B1176811
theorem B12698855 : Blo 770335 12698855 := bstep (se 1 (by rfl) ⟨9524141, by rfl⟩ : syracuseStep 12698855 = 19048283) B19048283
theorem B771455 : Blo 770335 771455 := bstep (se 1 (by rfl) ⟨578591, by rfl⟩ : syracuseStep 771455 = 1157183) B1157183
theorem B771551 : Blo 770335 771551 := bstep (se 1 (by rfl) ⟨578663, by rfl⟩ : syracuseStep 771551 = 1157327) B1157327
theorem B869863 : Blo 770335 869863 := bstep (se 1 (by rfl) ⟨652397, by rfl⟩ : syracuseStep 869863 = 1304795) B1304795
theorem B771631 : Blo 770335 771631 := bstep (se 1 (by rfl) ⟨578723, by rfl⟩ : syracuseStep 771631 = 1157447) B1157447
theorem B771823 : Blo 770335 771823 := bstep (se 1 (by rfl) ⟨578867, by rfl⟩ : syracuseStep 771823 = 1157735) B1157735
theorem B772187 : Blo 770335 772187 := bstep (se 1 (by rfl) ⟨579140, by rfl⟩ : syracuseStep 772187 = 1158281) B1158281
theorem B2607227 : Blo 770335 2607227 := bstep (se 1 (by rfl) ⟨1955420, by rfl⟩ : syracuseStep 2607227 = 3910841) B3910841
theorem B772223 : Blo 770335 772223 := bstep (se 1 (by rfl) ⟨579167, by rfl⟩ : syracuseStep 772223 = 1158335) B1158335
theorem B2607335 : Blo 770335 2607335 := bstep (se 1 (by rfl) ⟨1955501, by rfl⟩ : syracuseStep 2607335 = 3911003) B3911003
theorem B4409903 : Blo 770335 4409903 := bstep (se 1 (by rfl) ⟨3307427, by rfl⟩ : syracuseStep 4409903 = 6614855) B6614855
theorem B9915311 : Blo 770335 9915311 := bstep (se 1 (by rfl) ⟨7436483, by rfl⟩ : syracuseStep 9915311 = 14872967) B14872967
theorem B77122685 : Blo 770335 77122685 := bstep (se 3 (by rfl) ⟨14460503, by rfl⟩ : syracuseStep 77122685 = 28921007) B28921007
theorem B1985705 : Blo 770335 1985705 := bstep (se 2 (by rfl) ⟨744639, by rfl⟩ : syracuseStep 1985705 = 1489279) B1489279
theorem B2936351 : Blo 770335 2936351 := bstep (se 1 (by rfl) ⟨2202263, by rfl⟩ : syracuseStep 2936351 = 4404527) B4404527
theorem B773679 : Blo 770335 773679 := bstep (se 1 (by rfl) ⟨580259, by rfl⟩ : syracuseStep 773679 = 1160519) B1160519
theorem B2608793 : Blo 770335 2608793 := bstep (se 2 (by rfl) ⟨978297, by rfl⟩ : syracuseStep 2608793 = 1956595) B1956595
theorem B1953659 : Blo 770335 1953659 := bstep (se 1 (by rfl) ⟨1465244, by rfl⟩ : syracuseStep 1953659 = 2930489) B2930489
theorem B2609063 : Blo 770335 2609063 := bstep (se 1 (by rfl) ⟨1956797, by rfl⟩ : syracuseStep 2609063 = 3913595) B3913595
theorem B20107217 : Blo 770335 20107217 := bstep (se 2 (by rfl) ⟨7540206, by rfl⟩ : syracuseStep 20107217 = 15080413) B15080413
theorem B8343647 : Blo 770335 8343647 := bstep (se 1 (by rfl) ⟨6257735, by rfl⟩ : syracuseStep 8343647 = 12515471) B12515471
theorem B4706585 : Blo 770335 4706585 := bstep (se 2 (by rfl) ⟨1764969, by rfl⟩ : syracuseStep 4706585 = 3529939) B3529939
theorem B13390271 : Blo 770335 13390271 := bstep (se 1 (by rfl) ⟨10042703, by rfl⟩ : syracuseStep 13390271 = 20085407) B20085407
theorem B2610359 : Blo 770335 2610359 := bstep (se 1 (by rfl) ⟨1957769, by rfl⟩ : syracuseStep 2610359 = 3915539) B3915539
theorem B1463521 : Blo 770335 1463521 := bstep (se 2 (by rfl) ⟨548820, by rfl⟩ : syracuseStep 1463521 = 1097641) B1097641
theorem B3626527 : Blo 770335 3626527 := bstep (se 1 (by rfl) ⟨2719895, by rfl⟩ : syracuseStep 3626527 = 5439791) B5439791
theorem B1300927 : Blo 770335 1300927 := bstep (se 1 (by rfl) ⟨975695, by rfl⟩ : syracuseStep 1300927 = 1951391) B1951391
theorem B1956919 : Blo 770335 1956919 := bstep (se 1 (by rfl) ⟨1467689, by rfl⟩ : syracuseStep 1956919 = 2935379) B2935379
theorem B1957355 : Blo 770335 1957355 := bstep (se 1 (by rfl) ⟨1468016, by rfl⟩ : syracuseStep 1957355 = 2936033) B2936033
theorem B2612843 : Blo 770335 2612843 := bstep (se 1 (by rfl) ⟨1959632, by rfl⟩ : syracuseStep 2612843 = 3919265) B3919265
theorem B8019695 : Blo 770335 8019695 := bstep (se 1 (by rfl) ⟨6014771, by rfl⟩ : syracuseStep 8019695 = 12029543) B12029543
theorem B1466399 : Blo 770335 1466399 := bstep (se 1 (by rfl) ⟨1099799, by rfl⟩ : syracuseStep 1466399 = 2199599) B2199599
theorem B1302655 : Blo 770335 1302655 := bstep (se 1 (by rfl) ⟨976991, by rfl⟩ : syracuseStep 1302655 = 1953983) B1953983
theorem B6250661 : Blo 770335 6250661 := bstep (se 4 (by rfl) ⟨585999, by rfl⟩ : syracuseStep 6250661 = 1171999) B1171999
theorem B1302905 : Blo 770335 1302905 := bstep (se 2 (by rfl) ⟨488589, by rfl⟩ : syracuseStep 1302905 = 977179) B977179
theorem B8446519 : Blo 770335 8446519 := bstep (se 1 (by rfl) ⟨6334889, by rfl⟩ : syracuseStep 8446519 = 12669779) B12669779
theorem B8807777 : Blo 770335 8807777 := bstep (se 2 (by rfl) ⟨3302916, by rfl⟩ : syracuseStep 8807777 = 6605833) B6605833
theorem B1762663 : Blo 770335 1762663 := bstep (se 1 (by rfl) ⟨1321997, by rfl⟩ : syracuseStep 1762663 = 2643995) B2643995
theorem B2090465 : Blo 770335 2090465 := bstep (se 2 (by rfl) ⟨783924, by rfl⟩ : syracuseStep 2090465 = 1567849) B1567849
theorem B1304059 : Blo 770335 1304059 := bstep (se 1 (by rfl) ⟨978044, by rfl⟩ : syracuseStep 1304059 = 1956089) B1956089
theorem B1304167 : Blo 770335 1304167 := bstep (se 1 (by rfl) ⟨978125, by rfl⟩ : syracuseStep 1304167 = 1956251) B1956251
theorem B1304491 : Blo 770335 1304491 := bstep (se 1 (by rfl) ⟨978368, by rfl⟩ : syracuseStep 1304491 = 1956737) B1956737
theorem B1959977 : Blo 770335 1959977 := bstep (se 2 (by rfl) ⟨734991, by rfl⟩ : syracuseStep 1959977 = 1469983) B1469983
theorem B976951 : Blo 770335 976951 := bstep (se 1 (by rfl) ⟨732713, by rfl⟩ : syracuseStep 976951 = 1465427) B1465427
theorem B192997505 : Blo 770335 192997505 := bstep (se 2 (by rfl) ⟨72374064, by rfl⟩ : syracuseStep 192997505 = 144748129) B144748129
theorem B22276235 : Blo 770335 22276235 := bstep (se 1 (by rfl) ⟨16707176, by rfl⟩ : syracuseStep 22276235 = 33414353) B33414353
theorem B3304489 : Blo 770335 3304489 := bstep (se 2 (by rfl) ⟨1239183, by rfl⟩ : syracuseStep 3304489 = 2478367) B2478367
theorem B19787975 : Blo 770335 19787975 := bstep (se 1 (by rfl) ⟨14840981, by rfl⟩ : syracuseStep 19787975 = 29681963) B29681963
theorem B1733759 : Blo 770335 1733759 := bstep (se 1 (by rfl) ⟨1300319, by rfl⟩ : syracuseStep 1733759 = 2600639) B2600639
theorem B4388215 : Blo 770335 4388215 := bstep (se 1 (by rfl) ⟨3291161, by rfl⟩ : syracuseStep 4388215 = 6582323) B6582323
theorem B1734281 : Blo 770335 1734281 := bstep (se 2 (by rfl) ⟨650355, by rfl⟩ : syracuseStep 1734281 = 1300711) B1300711
theorem B2193767 : Blo 770335 2193767 := bstep (se 1 (by rfl) ⟨1645325, by rfl⟩ : syracuseStep 2193767 = 3290651) B3290651
theorem B15858119 : Blo 770335 15858119 := bstep (se 1 (by rfl) ⟨11893589, by rfl⟩ : syracuseStep 15858119 = 23787179) B23787179
theorem B21133871 : Blo 770335 21133871 := bstep (se 1 (by rfl) ⟨15850403, by rfl⟩ : syracuseStep 21133871 = 31700807) B31700807
theorem B1735271 : Blo 770335 1735271 := bstep (se 1 (by rfl) ⟨1301453, by rfl⟩ : syracuseStep 1735271 = 2602907) B2602907
theorem B4389947 : Blo 770335 4389947 := bstep (se 1 (by rfl) ⟨3292460, by rfl⟩ : syracuseStep 4389947 = 6584921) B6584921
theorem B34274767 : Blo 770335 34274767 := bstep (se 1 (by rfl) ⟨25706075, by rfl⟩ : syracuseStep 34274767 = 51412151) B51412151
theorem B2784935 : Blo 770335 2784935 := bstep (se 1 (by rfl) ⟨2088701, by rfl⟩ : syracuseStep 2784935 = 4177403) B4177403
theorem B1736531 : Blo 770335 1736531 := bstep (se 1 (by rfl) ⟨1302398, by rfl⟩ : syracuseStep 1736531 = 2604797) B2604797
theorem B1736639 : Blo 770335 1736639 := bstep (se 1 (by rfl) ⟨1302479, by rfl⟩ : syracuseStep 1736639 = 2604959) B2604959
theorem B9896039 : Blo 770335 9896039 := bstep (se 1 (by rfl) ⟨7422029, by rfl⟩ : syracuseStep 9896039 = 14844059) B14844059
theorem B1736873 : Blo 770335 1736873 := bstep (se 2 (by rfl) ⟨651327, by rfl⟩ : syracuseStep 1736873 = 1302655) B1302655
theorem B3899987 : Blo 770335 3899987 := bstep (se 1 (by rfl) ⟨2924990, by rfl⟩ : syracuseStep 3899987 = 5849981) B5849981
theorem B4391657 : Blo 770335 4391657 := bstep (se 2 (by rfl) ⟨1646871, by rfl⟩ : syracuseStep 4391657 = 3293743) B3293743
theorem B1738151 : Blo 770335 1738151 := bstep (se 1 (by rfl) ⟨1303613, by rfl⟩ : syracuseStep 1738151 = 2607227) B2607227
theorem B1738223 : Blo 770335 1738223 := bstep (se 1 (by rfl) ⟨1303667, by rfl⟩ : syracuseStep 1738223 = 2607335) B2607335
theorem B1738745 : Blo 770335 1738745 := bstep (se 2 (by rfl) ⟨652029, by rfl⟩ : syracuseStep 1738745 = 1304059) B1304059
theorem B51415123 : Blo 770335 51415123 := bstep (se 1 (by rfl) ⟨38561342, by rfl⟩ : syracuseStep 51415123 = 77122685) B77122685
theorem B1738889 : Blo 770335 1738889 := bstep (se 2 (by rfl) ⟨652083, by rfl⟩ : syracuseStep 1738889 = 1304167) B1304167
theorem B1739195 : Blo 770335 1739195 := bstep (se 1 (by rfl) ⟨1304396, by rfl⟩ : syracuseStep 1739195 = 2608793) B2608793
theorem B1739321 : Blo 770335 1739321 := bstep (se 2 (by rfl) ⟨652245, by rfl⟩ : syracuseStep 1739321 = 1304491) B1304491
theorem B1739375 : Blo 770335 1739375 := bstep (se 1 (by rfl) ⟨1304531, by rfl⟩ : syracuseStep 1739375 = 2609063) B2609063
theorem B13404811 : Blo 770335 13404811 := bstep (se 1 (by rfl) ⟨10053608, by rfl⟩ : syracuseStep 13404811 = 20107217) B20107217
theorem B1740239 : Blo 770335 1740239 := bstep (se 1 (by rfl) ⟨1305179, by rfl⟩ : syracuseStep 1740239 = 2610359) B2610359
theorem B1741895 : Blo 770335 1741895 := bstep (se 1 (by rfl) ⟨1306421, by rfl⟩ : syracuseStep 1741895 = 2612843) B2612843
theorem B4167107 : Blo 770335 4167107 := bstep (se 1 (by rfl) ⟨3125330, by rfl⟩ : syracuseStep 4167107 = 6250661) B6250661
theorem B514660013 : Blo 770335 514660013 := bstep (se 3 (by rfl) ⟨96498752, by rfl⟩ : syracuseStep 514660013 = 192997505) B192997505
theorem B5871851 : Blo 770335 5871851 := bstep (se 1 (by rfl) ⟨4403888, by rfl⟩ : syracuseStep 5871851 = 8807777) B8807777
theorem B11147807 : Blo 770335 11147807 := bstep (se 1 (by rfl) ⟨8360855, by rfl⟩ : syracuseStep 11147807 = 16721711) B16721711
theorem B2202241 : Blo 770335 2202241 := bstep (se 2 (by rfl) ⟨825840, by rfl⟩ : syracuseStep 2202241 = 1651681) B1651681
theorem B14850823 : Blo 770335 14850823 := bstep (se 1 (by rfl) ⟨11138117, by rfl⟩ : syracuseStep 14850823 = 22276235) B22276235
theorem B4398695 : Blo 770335 4398695 := bstep (se 1 (by rfl) ⟨3299021, by rfl⟩ : syracuseStep 4398695 = 6598043) B6598043
theorem B10691027 : Blo 770335 10691027 := bstep (se 1 (by rfl) ⟨8018270, by rfl⟩ : syracuseStep 10691027 = 16036541) B16036541
theorem B5874281 : Blo 770335 5874281 := bstep (se 2 (by rfl) ⟨2202855, by rfl⟩ : syracuseStep 5874281 = 4405711) B4405711
theorem B1155839 : Blo 770335 1155839 := bstep (se 1 (by rfl) ⟨866879, by rfl⟩ : syracuseStep 1155839 = 1733759) B1733759
theorem B1156187 : Blo 770335 1156187 := bstep (se 1 (by rfl) ⟨867140, by rfl⟩ : syracuseStep 1156187 = 1734281) B1734281
theorem B1156847 : Blo 770335 1156847 := bstep (se 1 (by rfl) ⟨867635, by rfl⟩ : syracuseStep 1156847 = 1735271) B1735271
theorem B1156985 : Blo 770335 1156985 := bstep (se 2 (by rfl) ⟨433869, by rfl⟩ : syracuseStep 1156985 = 867739) B867739
theorem B2926631 : Blo 770335 2926631 := bstep (se 1 (by rfl) ⟨2194973, by rfl⟩ : syracuseStep 2926631 = 4389947) B4389947
theorem B1157687 : Blo 770335 1157687 := bstep (se 1 (by rfl) ⟨868265, by rfl⟩ : syracuseStep 1157687 = 1736531) B1736531
theorem B1157759 : Blo 770335 1157759 := bstep (se 1 (by rfl) ⟨868319, by rfl⟩ : syracuseStep 1157759 = 1736639) B1736639
theorem B1157897 : Blo 770335 1157897 := bstep (se 2 (by rfl) ⟨434211, by rfl⟩ : syracuseStep 1157897 = 868423) B868423
theorem B44641043 : Blo 770335 44641043 := bstep (se 1 (by rfl) ⟨33480782, by rfl⟩ : syracuseStep 44641043 = 66961565) B66961565
theorem B2468731 : Blo 770335 2468731 := bstep (se 1 (by rfl) ⟨1851548, by rfl⟩ : syracuseStep 2468731 = 3703097) B3703097
theorem B35630513 : Blo 770335 35630513 := bstep (se 2 (by rfl) ⟨13361442, by rfl⟩ : syracuseStep 35630513 = 26722885) B26722885
theorem B8465903 : Blo 770335 8465903 := bstep (se 1 (by rfl) ⟨6349427, by rfl⟩ : syracuseStep 8465903 = 12698855) B12698855
theorem B2600585 : Blo 770335 2600585 := bstep (se 2 (by rfl) ⟨975219, by rfl⟩ : syracuseStep 2600585 = 1950439) B1950439
theorem B1158887 : Blo 770335 1158887 := bstep (se 1 (by rfl) ⟨869165, by rfl⟩ : syracuseStep 1158887 = 1738331) B1738331
theorem B1159223 : Blo 770335 1159223 := bstep (se 1 (by rfl) ⟨869417, by rfl⟩ : syracuseStep 1159223 = 1738835) B1738835
theorem B1159403 : Blo 770335 1159403 := bstep (se 1 (by rfl) ⟨869552, by rfl⟩ : syracuseStep 1159403 = 1739105) B1739105
theorem B8368433 : Blo 770335 8368433 := bstep (se 2 (by rfl) ⟨3138162, by rfl⟩ : syracuseStep 8368433 = 6276325) B6276325
theorem B1159817 : Blo 770335 1159817 := bstep (se 2 (by rfl) ⟨434931, by rfl⟩ : syracuseStep 1159817 = 869863) B869863
theorem B1323803 : Blo 770335 1323803 := bstep (se 1 (by rfl) ⟨992852, by rfl⟩ : syracuseStep 1323803 = 1985705) B1985705
theorem B1160135 : Blo 770335 1160135 := bstep (se 1 (by rfl) ⟨870101, by rfl⟩ : syracuseStep 1160135 = 1740203) B1740203
theorem B1160219 : Blo 770335 1160219 := bstep (se 1 (by rfl) ⟨870164, by rfl⟩ : syracuseStep 1160219 = 1740329) B1740329
theorem B2602151 : Blo 770335 2602151 := bstep (se 1 (by rfl) ⟨1951613, by rfl⟩ : syracuseStep 2602151 = 3903227) B3903227
theorem B1160699 : Blo 770335 1160699 := bstep (se 1 (by rfl) ⟨870524, by rfl⟩ : syracuseStep 1160699 = 1741049) B1741049
theorem B8926847 : Blo 770335 8926847 := bstep (se 1 (by rfl) ⟨6695135, by rfl⟩ : syracuseStep 8926847 = 13390271) B13390271
theorem B1160831 : Blo 770335 1160831 := bstep (se 1 (by rfl) ⟨870623, by rfl⟩ : syracuseStep 1160831 = 1741247) B1741247
theorem B2143997 : Blo 770335 2143997 := bstep (se 3 (by rfl) ⟨401999, by rfl⟩ : syracuseStep 2143997 = 803999) B803999
theorem B1160999 : Blo 770335 1160999 := bstep (se 1 (by rfl) ⟨870749, by rfl⟩ : syracuseStep 1160999 = 1741499) B1741499
theorem B1161071 : Blo 770335 1161071 := bstep (se 1 (by rfl) ⟨870803, by rfl⟩ : syracuseStep 1161071 = 1741607) B1741607
theorem B4405985 : Blo 770335 4405985 := bstep (se 2 (by rfl) ⟨1652244, by rfl⟩ : syracuseStep 4405985 = 3304489) B3304489
theorem B2604527 : Blo 770335 2604527 := bstep (se 1 (by rfl) ⟨1953395, by rfl⟩ : syracuseStep 2604527 = 3906791) B3906791
theorem B2473703 : Blo 770335 2473703 := bstep (se 1 (by rfl) ⟨1855277, by rfl⟩ : syracuseStep 2473703 = 3710555) B3710555
theorem B868603 : Blo 770335 868603 := bstep (se 1 (by rfl) ⟨651452, by rfl⟩ : syracuseStep 868603 = 1302905) B1302905
theorem B1393643 : Blo 770335 1393643 := bstep (se 1 (by rfl) ⟨1045232, by rfl⟩ : syracuseStep 1393643 = 2090465) B2090465
theorem B771071 : Blo 770335 771071 := bstep (se 1 (by rfl) ⟨578303, by rfl⟩ : syracuseStep 771071 = 1156607) B1156607
theorem B5555425 : Blo 770335 5555425 := bstep (se 2 (by rfl) ⟨2083284, by rfl⟩ : syracuseStep 5555425 = 4166569) B4166569
theorem B1951361 : Blo 770335 1951361 := bstep (se 2 (by rfl) ⟨731760, by rfl⟩ : syracuseStep 1951361 = 1463521) B1463521
theorem B5850953 : Blo 770335 5850953 := bstep (se 2 (by rfl) ⟨2194107, by rfl⟩ : syracuseStep 5850953 = 4388215) B4388215
theorem B772007 : Blo 770335 772007 := bstep (se 1 (by rfl) ⟨579005, by rfl⟩ : syracuseStep 772007 = 1158011) B1158011
theorem B4835369 : Blo 770335 4835369 := bstep (se 2 (by rfl) ⟨1813263, by rfl⟩ : syracuseStep 4835369 = 3626527) B3626527
theorem B772207 : Blo 770335 772207 := bstep (se 1 (by rfl) ⟨579155, by rfl⟩ : syracuseStep 772207 = 1158311) B1158311
theorem B5556347 : Blo 770335 5556347 := bstep (se 1 (by rfl) ⟨4167260, by rfl⟩ : syracuseStep 5556347 = 8334521) B8334521
theorem B1952171 : Blo 770335 1952171 := bstep (se 1 (by rfl) ⟨1464128, by rfl⟩ : syracuseStep 1952171 = 2928257) B2928257
theorem B772763 : Blo 770335 772763 := bstep (se 1 (by rfl) ⟨579572, by rfl⟩ : syracuseStep 772763 = 1159145) B1159145
theorem B772799 : Blo 770335 772799 := bstep (se 1 (by rfl) ⟨579599, by rfl⟩ : syracuseStep 772799 = 1159199) B1159199
theorem B2935547 : Blo 770335 2935547 := bstep (se 1 (by rfl) ⟨2201660, by rfl⟩ : syracuseStep 2935547 = 4403321) B4403321
theorem B772895 : Blo 770335 772895 := bstep (se 1 (by rfl) ⟨579671, by rfl⟩ : syracuseStep 772895 = 1159343) B1159343
theorem B13191983 : Blo 770335 13191983 := bstep (se 1 (by rfl) ⟨9893987, by rfl⟩ : syracuseStep 13191983 = 19787975) B19787975
theorem B773119 : Blo 770335 773119 := bstep (se 1 (by rfl) ⟨579839, by rfl⟩ : syracuseStep 773119 = 1159679) B1159679
theorem B2346191 : Blo 770335 2346191 := bstep (se 1 (by rfl) ⟨1759643, by rfl⟩ : syracuseStep 2346191 = 3519287) B3519287
theorem B773535 : Blo 770335 773535 := bstep (se 1 (by rfl) ⟨580151, by rfl⟩ : syracuseStep 773535 = 1160303) B1160303
theorem B773663 : Blo 770335 773663 := bstep (se 1 (by rfl) ⟨580247, by rfl⟩ : syracuseStep 773663 = 1160495) B1160495
theorem B773823 : Blo 770335 773823 := bstep (se 1 (by rfl) ⟨580367, by rfl⟩ : syracuseStep 773823 = 1160735) B1160735
theorem B773919 : Blo 770335 773919 := bstep (se 1 (by rfl) ⟨580439, by rfl⟩ : syracuseStep 773919 = 1160879) B1160879
theorem B2609225 : Blo 770335 2609225 := bstep (se 2 (by rfl) ⟨978459, by rfl⟩ : syracuseStep 2609225 = 1956919) B1956919
theorem B774255 : Blo 770335 774255 := bstep (se 1 (by rfl) ⟨580691, by rfl⟩ : syracuseStep 774255 = 1161383) B1161383
theorem B1462511 : Blo 770335 1462511 := bstep (se 1 (by rfl) ⟨1096883, by rfl⟩ : syracuseStep 1462511 = 2193767) B2193767
theorem B10572079 : Blo 770335 10572079 := bstep (se 1 (by rfl) ⟨7929059, by rfl⟩ : syracuseStep 10572079 = 15858119) B15858119
theorem B45699689 : Blo 770335 45699689 := bstep (se 2 (by rfl) ⟨17137383, by rfl⟩ : syracuseStep 45699689 = 34274767) B34274767
theorem B21385853 : Blo 770335 21385853 := bstep (se 3 (by rfl) ⟨4009847, by rfl⟩ : syracuseStep 21385853 = 8019695) B8019695
theorem B1856623 : Blo 770335 1856623 := bstep (se 1 (by rfl) ⟨1392467, by rfl⟩ : syracuseStep 1856623 = 2784935) B2784935
theorem B2937991 : Blo 770335 2937991 := bstep (se 1 (by rfl) ⟨2203493, by rfl⟩ : syracuseStep 2937991 = 4406987) B4406987
theorem B5559833 : Blo 770335 5559833 := bstep (se 2 (by rfl) ⟨2084937, by rfl⟩ : syracuseStep 5559833 = 4169875) B4169875
theorem B1955603 : Blo 770335 1955603 := bstep (se 1 (by rfl) ⟨1466702, by rfl⟩ : syracuseStep 1955603 = 2933405) B2933405
theorem B7428145 : Blo 770335 7428145 := bstep (se 2 (by rfl) ⟨2785554, by rfl⟩ : syracuseStep 7428145 = 5571109) B5571109
theorem B11262025 : Blo 770335 11262025 := bstep (se 2 (by rfl) ⟨4223259, by rfl⟩ : syracuseStep 11262025 = 8446519) B8446519
theorem B3955007 : Blo 770335 3955007 := bstep (se 1 (by rfl) ⟨2966255, by rfl⟩ : syracuseStep 3955007 = 5932511) B5932511
theorem B12540379 : Blo 770335 12540379 := bstep (se 1 (by rfl) ⟨9405284, by rfl⟩ : syracuseStep 12540379 = 18810569) B18810569
theorem B2939935 : Blo 770335 2939935 := bstep (se 1 (by rfl) ⟨2204951, by rfl⟩ : syracuseStep 2939935 = 4409903) B4409903
theorem B2350217 : Blo 770335 2350217 := bstep (se 2 (by rfl) ⟨881331, by rfl⟩ : syracuseStep 2350217 = 1762663) B1762663
theorem B6610207 : Blo 770335 6610207 := bstep (se 1 (by rfl) ⟨4957655, by rfl⟩ : syracuseStep 6610207 = 9915311) B9915311
theorem B1957567 : Blo 770335 1957567 := bstep (se 1 (by rfl) ⟨1468175, by rfl⟩ : syracuseStep 1957567 = 2936351) B2936351
theorem B1466095 : Blo 770335 1466095 := bstep (se 1 (by rfl) ⟨1099571, by rfl⟩ : syracuseStep 1466095 = 2199143) B2199143
theorem B1302439 : Blo 770335 1302439 := bstep (se 1 (by rfl) ⟨976829, by rfl⟩ : syracuseStep 1302439 = 1953659) B1953659
theorem B33382367 : Blo 770335 33382367 := bstep (se 1 (by rfl) ⟨25036775, by rfl⟩ : syracuseStep 33382367 = 50073551) B50073551
theorem B5562431 : Blo 770335 5562431 := bstep (se 1 (by rfl) ⟨4171823, by rfl⟩ : syracuseStep 5562431 = 8343647) B8343647
theorem B1302601 : Blo 770335 1302601 := bstep (se 2 (by rfl) ⟨488475, by rfl⟩ : syracuseStep 1302601 = 976951) B976951
theorem B3137723 : Blo 770335 3137723 := bstep (se 1 (by rfl) ⟨2353292, by rfl⟩ : syracuseStep 3137723 = 4706585) B4706585
theorem B2777483 : Blo 770335 2777483 := bstep (se 1 (by rfl) ⟨2083112, by rfl⟩ : syracuseStep 2777483 = 4166225) B4166225
theorem B1304903 : Blo 770335 1304903 := bstep (se 1 (by rfl) ⟨978677, by rfl⟩ : syracuseStep 1304903 = 1957355) B1957355
theorem B7432793 : Blo 770335 7432793 := bstep (se 2 (by rfl) ⟨2787297, by rfl⟩ : syracuseStep 7432793 = 5574595) B5574595
theorem B1469087 : Blo 770335 1469087 := bstep (se 1 (by rfl) ⟨1101815, by rfl⟩ : syracuseStep 1469087 = 2203631) B2203631
theorem B977599 : Blo 770335 977599 := bstep (se 1 (by rfl) ⟨733199, by rfl⟩ : syracuseStep 977599 = 1466399) B1466399
theorem B2780783 : Blo 770335 2780783 := bstep (se 1 (by rfl) ⟨2085587, by rfl⟩ : syracuseStep 2780783 = 4171175) B4171175
theorem B1306651 : Blo 770335 1306651 := bstep (se 1 (by rfl) ⟨979988, by rfl⟩ : syracuseStep 1306651 = 1959977) B1959977
theorem B1734569 : Blo 770335 1734569 := bstep (se 2 (by rfl) ⟨650463, by rfl⟩ : syracuseStep 1734569 = 1300927) B1300927
theorem B1734983 : Blo 770335 1734983 := bstep (se 1 (by rfl) ⟨1301237, by rfl⟩ : syracuseStep 1734983 = 2602475) B2602475
theorem B3340777 : Blo 770335 3340777 := bstep (se 2 (by rfl) ⟨1252791, by rfl⟩ : syracuseStep 3340777 = 2505583) B2505583
theorem B14089247 : Blo 770335 14089247 := bstep (se 1 (by rfl) ⟨10566935, by rfl⟩ : syracuseStep 14089247 = 21133871) B21133871
theorem B1735919 : Blo 770335 1735919 := bstep (se 1 (by rfl) ⟨1301939, by rfl⟩ : syracuseStep 1735919 = 2603879) B2603879
theorem B2784991 : Blo 770335 2784991 := bstep (se 1 (by rfl) ⟨2088743, by rfl⟩ : syracuseStep 2784991 = 4177487) B4177487
theorem B1736801 : Blo 770335 1736801 := bstep (se 2 (by rfl) ⟨651300, by rfl⟩ : syracuseStep 1736801 = 1302601) B1302601
theorem B3900635 : Blo 770335 3900635 := bstep (se 1 (by rfl) ⟨2925476, by rfl⟩ : syracuseStep 3900635 = 5850953) B5850953
theorem B3704231 : Blo 770335 3704231 := bstep (se 1 (by rfl) ⟨2778173, by rfl⟩ : syracuseStep 3704231 = 5556347) B5556347
theorem B7407233 : Blo 770335 7407233 := bstep (se 2 (by rfl) ⟨2777712, by rfl⟩ : syracuseStep 7407233 = 5555425) B5555425
theorem B1739483 : Blo 770335 1739483 := bstep (se 1 (by rfl) ⟨1304612, by rfl⟩ : syracuseStep 1739483 = 2609225) B2609225
theorem B68553497 : Blo 770335 68553497 := bstep (se 2 (by rfl) ⟨25707561, by rfl⟩ : syracuseStep 68553497 = 51415123) B51415123
theorem B14257235 : Blo 770335 14257235 := bstep (se 1 (by rfl) ⟨10692926, by rfl⟩ : syracuseStep 14257235 = 21385853) B21385853
theorem B3706555 : Blo 770335 3706555 := bstep (se 1 (by rfl) ⟨2779916, by rfl⟩ : syracuseStep 3706555 = 5559833) B5559833
theorem B22254911 : Blo 770335 22254911 := bstep (se 1 (by rfl) ⟨16691183, by rfl⟩ : syracuseStep 22254911 = 33382367) B33382367
theorem B1742201 : Blo 770335 1742201 := bstep (se 2 (by rfl) ⟨653325, by rfl⟩ : syracuseStep 1742201 = 1306651) B1306651
theorem B3708287 : Blo 770335 3708287 := bstep (se 1 (by rfl) ⟨2781215, by rfl⟩ : syracuseStep 3708287 = 5562431) B5562431
theorem B14096105 : Blo 770335 14096105 := bstep (se 2 (by rfl) ⟨5286039, by rfl⟩ : syracuseStep 14096105 = 10572079) B10572079
theorem B4955195 : Blo 770335 4955195 := bstep (se 1 (by rfl) ⟨3716396, by rfl⟩ : syracuseStep 4955195 = 7432793) B7432793
theorem B29760695 : Blo 770335 29760695 := bstep (se 1 (by rfl) ⟨22320521, by rfl⟩ : syracuseStep 29760695 = 44641043) B44641043
theorem B5643935 : Blo 770335 5643935 := bstep (se 1 (by rfl) ⟨4232951, by rfl⟩ : syracuseStep 5643935 = 8465903) B8465903
theorem B9904193 : Blo 770335 9904193 := bstep (se 2 (by rfl) ⟨3714072, by rfl⟩ : syracuseStep 9904193 = 7428145) B7428145
theorem B15016033 : Blo 770335 15016033 := bstep (se 2 (by rfl) ⟨5631012, by rfl⟩ : syracuseStep 15016033 = 11262025) B11262025
theorem B5578955 : Blo 770335 5578955 := bstep (se 1 (by rfl) ⟨4184216, by rfl⟩ : syracuseStep 5578955 = 8368433) B8368433
theorem B16720505 : Blo 770335 16720505 := bstep (se 2 (by rfl) ⟨6270189, by rfl⟩ : syracuseStep 16720505 = 12540379) B12540379
theorem B19801097 : Blo 770335 19801097 := bstep (se 2 (by rfl) ⟨7425411, by rfl⟩ : syracuseStep 19801097 = 14850823) B14850823
theorem B1156379 : Blo 770335 1156379 := bstep (se 1 (by rfl) ⟨867284, by rfl⟩ : syracuseStep 1156379 = 1734569) B1734569
theorem B1156655 : Blo 770335 1156655 := bstep (se 1 (by rfl) ⟨867491, by rfl⟩ : syracuseStep 1156655 = 1734983) B1734983
theorem B1157279 : Blo 770335 1157279 := bstep (se 1 (by rfl) ⟨867959, by rfl⟩ : syracuseStep 1157279 = 1735919) B1735919
theorem B3713321 : Blo 770335 3713321 := bstep (se 2 (by rfl) ⟨1392495, by rfl⟩ : syracuseStep 3713321 = 2784991) B2784991
theorem B1649135 : Blo 770335 1649135 := bstep (se 1 (by rfl) ⟨1236851, by rfl⟩ : syracuseStep 1649135 = 2473703) B2473703
theorem B6597359 : Blo 770335 6597359 := bstep (se 1 (by rfl) ⟨4948019, by rfl⟩ : syracuseStep 6597359 = 9896039) B9896039
theorem B1157915 : Blo 770335 1157915 := bstep (se 1 (by rfl) ⟨868436, by rfl⟩ : syracuseStep 1157915 = 1736873) B1736873
theorem B1158137 : Blo 770335 1158137 := bstep (se 2 (by rfl) ⟨434301, by rfl⟩ : syracuseStep 1158137 = 868603) B868603
theorem B2599991 : Blo 770335 2599991 := bstep (se 1 (by rfl) ⟨1949993, by rfl⟩ : syracuseStep 2599991 = 3899987) B3899987
theorem B2927771 : Blo 770335 2927771 := bstep (se 1 (by rfl) ⟨2195828, by rfl⟩ : syracuseStep 2927771 = 4391657) B4391657
theorem B1158767 : Blo 770335 1158767 := bstep (se 1 (by rfl) ⟨869075, by rfl⟩ : syracuseStep 1158767 = 1738151) B1738151
theorem B1158815 : Blo 770335 1158815 := bstep (se 1 (by rfl) ⟨869111, by rfl⟩ : syracuseStep 1158815 = 1738223) B1738223
theorem B1159163 : Blo 770335 1159163 := bstep (se 1 (by rfl) ⟨869372, by rfl⟩ : syracuseStep 1159163 = 1738745) B1738745
theorem B3223579 : Blo 770335 3223579 := bstep (se 1 (by rfl) ⟨2417684, by rfl⟩ : syracuseStep 3223579 = 4835369) B4835369
theorem B1159259 : Blo 770335 1159259 := bstep (se 1 (by rfl) ⟨869444, by rfl⟩ : syracuseStep 1159259 = 1738889) B1738889
theorem B1159463 : Blo 770335 1159463 := bstep (se 1 (by rfl) ⟨869597, by rfl⟩ : syracuseStep 1159463 = 1739195) B1739195
theorem B1159547 : Blo 770335 1159547 := bstep (se 1 (by rfl) ⟨869660, by rfl⟩ : syracuseStep 1159547 = 1739321) B1739321
theorem B1159583 : Blo 770335 1159583 := bstep (se 1 (by rfl) ⟨869687, by rfl⟩ : syracuseStep 1159583 = 1739375) B1739375
theorem B8794655 : Blo 770335 8794655 := bstep (se 1 (by rfl) ⟨6595991, by rfl⟩ : syracuseStep 8794655 = 13191983) B13191983
theorem B1160159 : Blo 770335 1160159 := bstep (se 1 (by rfl) ⟨870119, by rfl⟩ : syracuseStep 1160159 = 1740239) B1740239
theorem B3716381 : Blo 770335 3716381 := bstep (se 3 (by rfl) ⟨696821, by rfl⟩ : syracuseStep 3716381 = 1393643) B1393643
theorem B1161263 : Blo 770335 1161263 := bstep (se 1 (by rfl) ⟨870947, by rfl⟩ : syracuseStep 1161263 = 1741895) B1741895
theorem B17873081 : Blo 770335 17873081 := bstep (se 2 (by rfl) ⟨6702405, by rfl⟩ : syracuseStep 17873081 = 13404811) B13404811
theorem B3291641 : Blo 770335 3291641 := bstep (se 2 (by rfl) ⟨1234365, by rfl⟩ : syracuseStep 3291641 = 2468731) B2468731
theorem B3914567 : Blo 770335 3914567 := bstep (se 1 (by rfl) ⟨2935925, by rfl⟩ : syracuseStep 3914567 = 5871851) B5871851
theorem B2932463 : Blo 770335 2932463 := bstep (se 1 (by rfl) ⟨2199347, by rfl⟩ : syracuseStep 2932463 = 4398695) B4398695
theorem B1851655 : Blo 770335 1851655 := bstep (se 1 (by rfl) ⟨1388741, by rfl⟩ : syracuseStep 1851655 = 2777483) B2777483
theorem B7127351 : Blo 770335 7127351 := bstep (se 1 (by rfl) ⟨5345513, by rfl⟩ : syracuseStep 7127351 = 10691027) B10691027
theorem B3916187 : Blo 770335 3916187 := bstep (se 1 (by rfl) ⟨2937140, by rfl⟩ : syracuseStep 3916187 = 5874281) B5874281
theorem B770559 : Blo 770335 770559 := bstep (se 1 (by rfl) ⟨577919, by rfl⟩ : syracuseStep 770559 = 1155839) B1155839
theorem B770791 : Blo 770335 770791 := bstep (se 1 (by rfl) ⟨578093, by rfl⟩ : syracuseStep 770791 = 1156187) B1156187
theorem B771231 : Blo 770335 771231 := bstep (se 1 (by rfl) ⟨578423, by rfl⟩ : syracuseStep 771231 = 1156847) B1156847
theorem B771323 : Blo 770335 771323 := bstep (se 1 (by rfl) ⟨578492, by rfl⟩ : syracuseStep 771323 = 1156985) B1156985
theorem B1951087 : Blo 770335 1951087 := bstep (se 1 (by rfl) ⟨1463315, by rfl⟩ : syracuseStep 1951087 = 2926631) B2926631
theorem B2475497 : Blo 770335 2475497 := bstep (se 2 (by rfl) ⟨928311, by rfl⟩ : syracuseStep 2475497 = 1856623) B1856623
theorem B3917321 : Blo 770335 3917321 := bstep (se 2 (by rfl) ⟨1468995, by rfl⟩ : syracuseStep 3917321 = 2937991) B2937991
theorem B869935 : Blo 770335 869935 := bstep (se 1 (by rfl) ⟨652451, by rfl⟩ : syracuseStep 869935 = 1304903) B1304903
theorem B771791 : Blo 770335 771791 := bstep (se 1 (by rfl) ⟨578843, by rfl⟩ : syracuseStep 771791 = 1157687) B1157687
theorem B771839 : Blo 770335 771839 := bstep (se 1 (by rfl) ⟨578879, by rfl⟩ : syracuseStep 771839 = 1157759) B1157759
theorem B771931 : Blo 770335 771931 := bstep (se 1 (by rfl) ⟨578948, by rfl⟩ : syracuseStep 771931 = 1157897) B1157897
theorem B1853855 : Blo 770335 1853855 := bstep (se 1 (by rfl) ⟨1390391, by rfl⟩ : syracuseStep 1853855 = 2780783) B2780783
theorem B772591 : Blo 770335 772591 := bstep (se 1 (by rfl) ⟨579443, by rfl⟩ : syracuseStep 772591 = 1158887) B1158887
theorem B772815 : Blo 770335 772815 := bstep (se 1 (by rfl) ⟨579611, by rfl⟩ : syracuseStep 772815 = 1159223) B1159223
theorem B772935 : Blo 770335 772935 := bstep (se 1 (by rfl) ⟨579701, by rfl⟩ : syracuseStep 772935 = 1159403) B1159403
theorem B773211 : Blo 770335 773211 := bstep (se 1 (by rfl) ⟨579908, by rfl⟩ : syracuseStep 773211 = 1159817) B1159817
theorem B773423 : Blo 770335 773423 := bstep (se 1 (by rfl) ⟨580067, by rfl⟩ : syracuseStep 773423 = 1160135) B1160135
theorem B773479 : Blo 770335 773479 := bstep (se 1 (by rfl) ⟨580109, by rfl⟩ : syracuseStep 773479 = 1160219) B1160219
theorem B2936321 : Blo 770335 2936321 := bstep (se 2 (by rfl) ⟨1101120, by rfl⟩ : syracuseStep 2936321 = 2202241) B2202241
theorem B773799 : Blo 770335 773799 := bstep (se 1 (by rfl) ⟨580349, by rfl⟩ : syracuseStep 773799 = 1160699) B1160699
theorem B5951231 : Blo 770335 5951231 := bstep (se 1 (by rfl) ⟨4463423, by rfl⟩ : syracuseStep 5951231 = 8926847) B8926847
theorem B773887 : Blo 770335 773887 := bstep (se 1 (by rfl) ⟨580415, by rfl⟩ : syracuseStep 773887 = 1160831) B1160831
theorem B1429331 : Blo 770335 1429331 := bstep (se 1 (by rfl) ⟨1071998, by rfl⟩ : syracuseStep 1429331 = 2143997) B2143997
theorem B773999 : Blo 770335 773999 := bstep (se 1 (by rfl) ⟨580499, by rfl⟩ : syracuseStep 773999 = 1160999) B1160999
theorem B774047 : Blo 770335 774047 := bstep (se 1 (by rfl) ⟨580535, by rfl⟩ : syracuseStep 774047 = 1161071) B1161071
theorem B3919913 : Blo 770335 3919913 := bstep (se 2 (by rfl) ⟨1469967, by rfl⟩ : syracuseStep 3919913 = 2939935) B2939935
theorem B2937323 : Blo 770335 2937323 := bstep (se 1 (by rfl) ⟨2202992, by rfl⟩ : syracuseStep 2937323 = 4405985) B4405985
theorem B9392831 : Blo 770335 9392831 := bstep (se 1 (by rfl) ⟨7044623, by rfl⟩ : syracuseStep 9392831 = 14089247) B14089247
theorem B2610089 : Blo 770335 2610089 := bstep (se 2 (by rfl) ⟨978783, by rfl⟩ : syracuseStep 2610089 = 1957567) B1957567
theorem B1954793 : Blo 770335 1954793 := bstep (se 2 (by rfl) ⟨733047, by rfl⟩ : syracuseStep 1954793 = 1466095) B1466095
theorem B1300907 : Blo 770335 1300907 := bstep (se 1 (by rfl) ⟨975680, by rfl⟩ : syracuseStep 1300907 = 1951361) B1951361
theorem B1301447 : Blo 770335 1301447 := bstep (se 1 (by rfl) ⟨976085, by rfl⟩ : syracuseStep 1301447 = 1952171) B1952171
theorem B1957031 : Blo 770335 1957031 := bstep (se 1 (by rfl) ⟨1467773, by rfl⟩ : syracuseStep 1957031 = 2935547) B2935547
theorem B3530141 : Blo 770335 3530141 := bstep (se 3 (by rfl) ⟨661901, by rfl⟩ : syracuseStep 3530141 = 1323803) B1323803
theorem B1564127 : Blo 770335 1564127 := bstep (se 1 (by rfl) ⟨1173095, by rfl⟩ : syracuseStep 1564127 = 2346191) B2346191
theorem B975007 : Blo 770335 975007 := bstep (se 1 (by rfl) ⟨731255, by rfl⟩ : syracuseStep 975007 = 1462511) B1462511
theorem B30466459 : Blo 770335 30466459 := bstep (se 1 (by rfl) ⟨22849844, by rfl⟩ : syracuseStep 30466459 = 45699689) B45699689
theorem B1303465 : Blo 770335 1303465 := bstep (se 2 (by rfl) ⟨488799, by rfl⟩ : syracuseStep 1303465 = 977599) B977599
theorem B2778071 : Blo 770335 2778071 := bstep (se 1 (by rfl) ⟨2083553, by rfl⟩ : syracuseStep 2778071 = 4167107) B4167107
theorem B343106675 : Blo 770335 343106675 := bstep (se 1 (by rfl) ⟨257330006, by rfl⟩ : syracuseStep 343106675 = 514660013) B514660013
theorem B1303735 : Blo 770335 1303735 := bstep (se 1 (by rfl) ⟨977801, by rfl⟩ : syracuseStep 1303735 = 1955603) B1955603
theorem B7431871 : Blo 770335 7431871 := bstep (se 1 (by rfl) ⟨5573903, by rfl⟩ : syracuseStep 7431871 = 11147807) B11147807
theorem B1566811 : Blo 770335 1566811 := bstep (se 1 (by rfl) ⟨1175108, by rfl⟩ : syracuseStep 1566811 = 2350217) B2350217
theorem B2091815 : Blo 770335 2091815 := bstep (se 1 (by rfl) ⟨1568861, by rfl⟩ : syracuseStep 2091815 = 3137723) B3137723
theorem B10546685 : Blo 770335 10546685 := bstep (se 3 (by rfl) ⟨1977503, by rfl⟩ : syracuseStep 10546685 = 3955007) B3955007
theorem B979391 : Blo 770335 979391 := bstep (se 1 (by rfl) ⟨734543, by rfl⟩ : syracuseStep 979391 = 1469087) B1469087
theorem B23753675 : Blo 770335 23753675 := bstep (se 1 (by rfl) ⟨17815256, by rfl⟩ : syracuseStep 23753675 = 35630513) B35630513
theorem B1733723 : Blo 770335 1733723 := bstep (se 1 (by rfl) ⟨1300292, by rfl⟩ : syracuseStep 1733723 = 2600585) B2600585
theorem B4454369 : Blo 770335 4454369 := bstep (se 2 (by rfl) ⟨1670388, by rfl⟩ : syracuseStep 4454369 = 3340777) B3340777
theorem B1734767 : Blo 770335 1734767 := bstep (se 1 (by rfl) ⟨1301075, by rfl⟩ : syracuseStep 1734767 = 2602151) B2602151
theorem B8813609 : Blo 770335 8813609 := bstep (se 2 (by rfl) ⟨3305103, by rfl⟩ : syracuseStep 8813609 = 6610207) B6610207
theorem B1736351 : Blo 770335 1736351 := bstep (se 1 (by rfl) ⟨1302263, by rfl⟩ : syracuseStep 1736351 = 2604527) B2604527
theorem B1736585 : Blo 770335 1736585 := bstep (se 2 (by rfl) ⟨651219, by rfl⟩ : syracuseStep 1736585 = 1302439) B1302439
theorem B20021377 : Blo 770335 20021377 := bstep (se 2 (by rfl) ⟨7508016, by rfl⟩ : syracuseStep 20021377 = 15016033) B15016033
theorem B4751567 : Blo 770335 4751567 := bstep (se 1 (by rfl) ⟨3563675, by rfl⟩ : syracuseStep 4751567 = 7127351) B7127351
theorem B1737953 : Blo 770335 1737953 := bstep (se 2 (by rfl) ⟨651732, by rfl⟩ : syracuseStep 1737953 = 1303465) B1303465
theorem B1738313 : Blo 770335 1738313 := bstep (se 2 (by rfl) ⟨651867, by rfl⟩ : syracuseStep 1738313 = 1303735) B1303735
theorem B9504823 : Blo 770335 9504823 := bstep (se 1 (by rfl) ⟨7128617, by rfl⟩ : syracuseStep 9504823 = 14257235) B14257235
theorem B3967487 : Blo 770335 3967487 := bstep (se 1 (by rfl) ⟨2975615, by rfl⟩ : syracuseStep 3967487 = 5951231) B5951231
theorem B7408189 : Blo 770335 7408189 := bstep (se 3 (by rfl) ⟨1389035, by rfl⟩ : syracuseStep 7408189 = 2778071) B2778071
theorem B6261887 : Blo 770335 6261887 := bstep (se 1 (by rfl) ⟨4696415, by rfl⟩ : syracuseStep 6261887 = 9392831) B9392831
theorem B1740059 : Blo 770335 1740059 := bstep (se 1 (by rfl) ⟨1305044, by rfl⟩ : syracuseStep 1740059 = 2610089) B2610089
theorem B4298105 : Blo 770335 4298105 := bstep (se 2 (by rfl) ⟨1611789, by rfl⟩ : syracuseStep 4298105 = 3223579) B3223579
theorem B11147003 : Blo 770335 11147003 := bstep (se 1 (by rfl) ⟨8360252, by rfl⟩ : syracuseStep 11147003 = 16720505) B16720505
theorem B9902189 : Blo 770335 9902189 := bstep (se 3 (by rfl) ⟨1856660, by rfl⟩ : syracuseStep 9902189 = 3713321) B3713321
theorem B4398239 : Blo 770335 4398239 := bstep (se 1 (by rfl) ⟨3298679, by rfl⟩ : syracuseStep 4398239 = 6597359) B6597359
theorem B13213853 : Blo 770335 13213853 := bstep (se 3 (by rfl) ⟨2477597, by rfl⟩ : syracuseStep 13213853 = 4955195) B4955195
theorem B15835783 : Blo 770335 15835783 := bstep (se 1 (by rfl) ⟨11876837, by rfl⟩ : syracuseStep 15835783 = 23753675) B23753675
theorem B1155815 : Blo 770335 1155815 := bstep (se 1 (by rfl) ⟨866861, by rfl⟩ : syracuseStep 1155815 = 1733723) B1733723
theorem B1156511 : Blo 770335 1156511 := bstep (se 1 (by rfl) ⟨867383, by rfl⟩ : syracuseStep 1156511 = 1734767) B1734767
theorem B5875739 : Blo 770335 5875739 := bstep (se 1 (by rfl) ⟨4406804, by rfl⟩ : syracuseStep 5875739 = 8813609) B8813609
theorem B3811549 : Blo 770335 3811549 := bstep (se 3 (by rfl) ⟨714665, by rfl⟩ : syracuseStep 3811549 = 1429331) B1429331
theorem B1157567 : Blo 770335 1157567 := bstep (se 1 (by rfl) ⟨868175, by rfl⟩ : syracuseStep 1157567 = 1736351) B1736351
theorem B1157723 : Blo 770335 1157723 := bstep (se 1 (by rfl) ⟨868292, by rfl⟩ : syracuseStep 1157723 = 1736585) B1736585
theorem B1157867 : Blo 770335 1157867 := bstep (se 1 (by rfl) ⟨868400, by rfl⟩ : syracuseStep 1157867 = 1736801) B1736801
theorem B2468873 : Blo 770335 2468873 := bstep (se 2 (by rfl) ⟨925827, by rfl⟩ : syracuseStep 2468873 = 1851655) B1851655
theorem B2600423 : Blo 770335 2600423 := bstep (se 1 (by rfl) ⟨1950317, by rfl⟩ : syracuseStep 2600423 = 3900635) B3900635
theorem B1650331 : Blo 770335 1650331 := bstep (se 1 (by rfl) ⟨1237748, by rfl⟩ : syracuseStep 1650331 = 2475497) B2475497
theorem B1159655 : Blo 770335 1159655 := bstep (se 1 (by rfl) ⟨869741, by rfl⟩ : syracuseStep 1159655 = 1739483) B1739483
theorem B2601449 : Blo 770335 2601449 := bstep (se 2 (by rfl) ⟨975543, by rfl⟩ : syracuseStep 2601449 = 1951087) B1951087
theorem B1159913 : Blo 770335 1159913 := bstep (se 2 (by rfl) ⟨434967, by rfl⟩ : syracuseStep 1159913 = 869935) B869935
theorem B9909161 : Blo 770335 9909161 := bstep (se 2 (by rfl) ⟨3715935, by rfl⟩ : syracuseStep 9909161 = 7431871) B7431871
theorem B1161467 : Blo 770335 1161467 := bstep (se 1 (by rfl) ⟨871100, by rfl⟩ : syracuseStep 1161467 = 1742201) B1742201
theorem B2472191 : Blo 770335 2472191 := bstep (se 1 (by rfl) ⟨1854143, by rfl⟩ : syracuseStep 2472191 = 3708287) B3708287
theorem B9877949 : Blo 770335 9877949 := bstep (se 3 (by rfl) ⟨1852115, by rfl⟩ : syracuseStep 9877949 = 3704231) B3704231
theorem B867271 : Blo 770335 867271 := bstep (se 1 (by rfl) ⟨650453, by rfl⟩ : syracuseStep 867271 = 1300907) B1300907
theorem B867631 : Blo 770335 867631 := bstep (se 1 (by rfl) ⟨650723, by rfl⟩ : syracuseStep 867631 = 1301447) B1301447
theorem B19840463 : Blo 770335 19840463 := bstep (se 1 (by rfl) ⟨14880347, by rfl⟩ : syracuseStep 19840463 = 29760695) B29760695
theorem B6602795 : Blo 770335 6602795 := bstep (se 1 (by rfl) ⟨4952096, by rfl⟩ : syracuseStep 6602795 = 9904193) B9904193
theorem B3719303 : Blo 770335 3719303 := bstep (se 1 (by rfl) ⟨2789477, by rfl⟩ : syracuseStep 3719303 = 5578955) B5578955
theorem B228737783 : Blo 770335 228737783 := bstep (se 1 (by rfl) ⟨171553337, by rfl⟩ : syracuseStep 228737783 = 343106675) B343106675
theorem B770919 : Blo 770335 770919 := bstep (se 1 (by rfl) ⟨578189, by rfl⟩ : syracuseStep 770919 = 1156379) B1156379
theorem B771103 : Blo 770335 771103 := bstep (se 1 (by rfl) ⟨578327, by rfl⟩ : syracuseStep 771103 = 1156655) B1156655
theorem B771519 : Blo 770335 771519 := bstep (se 1 (by rfl) ⟨578639, by rfl⟩ : syracuseStep 771519 = 1157279) B1157279
theorem B1099423 : Blo 770335 1099423 := bstep (se 1 (by rfl) ⟨824567, by rfl⟩ : syracuseStep 1099423 = 1649135) B1649135
theorem B771943 : Blo 770335 771943 := bstep (se 1 (by rfl) ⟨578957, by rfl⟩ : syracuseStep 771943 = 1157915) B1157915
theorem B1394543 : Blo 770335 1394543 := bstep (se 1 (by rfl) ⟨1045907, by rfl⟩ : syracuseStep 1394543 = 2091815) B2091815
theorem B772091 : Blo 770335 772091 := bstep (se 1 (by rfl) ⟨579068, by rfl⟩ : syracuseStep 772091 = 1158137) B1158137
theorem B1951847 : Blo 770335 1951847 := bstep (se 1 (by rfl) ⟨1463885, by rfl⟩ : syracuseStep 1951847 = 2927771) B2927771
theorem B7031123 : Blo 770335 7031123 := bstep (se 1 (by rfl) ⟨5273342, by rfl⟩ : syracuseStep 7031123 = 10546685) B10546685
theorem B772511 : Blo 770335 772511 := bstep (se 1 (by rfl) ⟨579383, by rfl⟩ : syracuseStep 772511 = 1158767) B1158767
theorem B772543 : Blo 770335 772543 := bstep (se 1 (by rfl) ⟨579407, by rfl⟩ : syracuseStep 772543 = 1158815) B1158815
theorem B772775 : Blo 770335 772775 := bstep (se 1 (by rfl) ⟨579581, by rfl⟩ : syracuseStep 772775 = 1159163) B1159163
theorem B772839 : Blo 770335 772839 := bstep (se 1 (by rfl) ⟨579629, by rfl⟩ : syracuseStep 772839 = 1159259) B1159259
theorem B772975 : Blo 770335 772975 := bstep (se 1 (by rfl) ⟨579731, by rfl⟩ : syracuseStep 772975 = 1159463) B1159463
theorem B773031 : Blo 770335 773031 := bstep (se 1 (by rfl) ⟨579773, by rfl⟩ : syracuseStep 773031 = 1159547) B1159547
theorem B773055 : Blo 770335 773055 := bstep (se 1 (by rfl) ⟨579791, by rfl⟩ : syracuseStep 773055 = 1159583) B1159583
theorem B773439 : Blo 770335 773439 := bstep (se 1 (by rfl) ⟨580079, by rfl⟩ : syracuseStep 773439 = 1160159) B1160159
theorem B2477587 : Blo 770335 2477587 := bstep (se 1 (by rfl) ⟨1858190, by rfl⟩ : syracuseStep 2477587 = 3716381) B3716381
theorem B2969579 : Blo 770335 2969579 := bstep (se 1 (by rfl) ⟨2227184, by rfl⟩ : syracuseStep 2969579 = 4454369) B4454369
theorem B774175 : Blo 770335 774175 := bstep (se 1 (by rfl) ⟨580631, by rfl⟩ : syracuseStep 774175 = 1161263) B1161263
theorem B11915387 : Blo 770335 11915387 := bstep (se 1 (by rfl) ⟨8936540, by rfl⟩ : syracuseStep 11915387 = 17873081) B17873081
theorem B2609711 : Blo 770335 2609711 := bstep (se 1 (by rfl) ⟨1957283, by rfl⟩ : syracuseStep 2609711 = 3914567) B3914567
theorem B1954975 : Blo 770335 1954975 := bstep (se 1 (by rfl) ⟨1466231, by rfl⟩ : syracuseStep 1954975 = 2932463) B2932463
theorem B1300009 : Blo 770335 1300009 := bstep (se 2 (by rfl) ⟨487503, by rfl⟩ : syracuseStep 1300009 = 975007) B975007
theorem B2610791 : Blo 770335 2610791 := bstep (se 1 (by rfl) ⟨1958093, by rfl⟩ : syracuseStep 2610791 = 3916187) B3916187
theorem B2611547 : Blo 770335 2611547 := bstep (se 1 (by rfl) ⟨1958660, by rfl⟩ : syracuseStep 2611547 = 3917321) B3917321
theorem B4938155 : Blo 770335 4938155 := bstep (se 1 (by rfl) ⟨3703616, by rfl⟩ : syracuseStep 4938155 = 7407233) B7407233
theorem B2611709 : Blo 770335 2611709 := bstep (se 3 (by rfl) ⟨489695, by rfl⟩ : syracuseStep 2611709 = 979391) B979391
theorem B1235903 : Blo 770335 1235903 := bstep (se 1 (by rfl) ⟨926927, by rfl⟩ : syracuseStep 1235903 = 1853855) B1853855
theorem B162487781 : Blo 770335 162487781 := bstep (se 4 (by rfl) ⟨15233229, by rfl⟩ : syracuseStep 162487781 = 30466459) B30466459
theorem B1957547 : Blo 770335 1957547 := bstep (se 1 (by rfl) ⟨1468160, by rfl⟩ : syracuseStep 1957547 = 2936321) B2936321
theorem B2613275 : Blo 770335 2613275 := bstep (se 1 (by rfl) ⟨1959956, by rfl⟩ : syracuseStep 2613275 = 3919913) B3919913
theorem B2089081 : Blo 770335 2089081 := bstep (se 2 (by rfl) ⟨783405, by rfl⟩ : syracuseStep 2089081 = 1566811) B1566811
theorem B1958215 : Blo 770335 1958215 := bstep (se 1 (by rfl) ⟨1468661, by rfl⟩ : syracuseStep 1958215 = 2937323) B2937323
theorem B1303195 : Blo 770335 1303195 := bstep (se 1 (by rfl) ⟨977396, by rfl⟩ : syracuseStep 1303195 = 1954793) B1954793
theorem B14836607 : Blo 770335 14836607 := bstep (se 1 (by rfl) ⟨11127455, by rfl⟩ : syracuseStep 14836607 = 22254911) B22254911
theorem B9397403 : Blo 770335 9397403 := bstep (se 1 (by rfl) ⟨7048052, by rfl⟩ : syracuseStep 9397403 = 14096105) B14096105
theorem B1304687 : Blo 770335 1304687 := bstep (se 1 (by rfl) ⟨978515, by rfl⟩ : syracuseStep 1304687 = 1957031) B1957031
theorem B4942073 : Blo 770335 4942073 := bstep (se 2 (by rfl) ⟨1853277, by rfl⟩ : syracuseStep 4942073 = 3706555) B3706555
theorem B2353427 : Blo 770335 2353427 := bstep (se 1 (by rfl) ⟨1765070, by rfl⟩ : syracuseStep 2353427 = 3530141) B3530141
theorem B1042751 : Blo 770335 1042751 := bstep (se 1 (by rfl) ⟨782063, by rfl⟩ : syracuseStep 1042751 = 1564127) B1564127
theorem B3762623 : Blo 770335 3762623 := bstep (se 1 (by rfl) ⟨2821967, by rfl⟩ : syracuseStep 3762623 = 5643935) B5643935
theorem B13200731 : Blo 770335 13200731 := bstep (se 1 (by rfl) ⟨9900548, by rfl⟩ : syracuseStep 13200731 = 19801097) B19801097
theorem B1733327 : Blo 770335 1733327 := bstep (se 1 (by rfl) ⟨1299995, by rfl⟩ : syracuseStep 1733327 = 2599991) B2599991
theorem B182809325 : Blo 770335 182809325 := bstep (se 3 (by rfl) ⟨34276748, by rfl⟩ : syracuseStep 182809325 = 68553497) B68553497
theorem B5863103 : Blo 770335 5863103 := bstep (se 1 (by rfl) ⟨4397327, by rfl⟩ : syracuseStep 5863103 = 8794655) B8794655
theorem B2194427 : Blo 770335 2194427 := bstep (se 1 (by rfl) ⟨1645820, by rfl⟩ : syracuseStep 2194427 = 3291641) B3291641
theorem B2785441 : Blo 770335 2785441 := bstep (se 2 (by rfl) ⟨1044540, by rfl⟩ : syracuseStep 2785441 = 2089081) B2089081
theorem B1737593 : Blo 770335 1737593 := bstep (se 2 (by rfl) ⟨651597, by rfl⟩ : syracuseStep 1737593 = 1303195) B1303195
theorem B4687415 : Blo 770335 4687415 := bstep (se 1 (by rfl) ⟨3515561, by rfl⟩ : syracuseStep 4687415 = 7031123) B7031123
theorem B5082065 : Blo 770335 5082065 := bstep (se 2 (by rfl) ⟨1905774, by rfl⟩ : syracuseStep 5082065 = 3811549) B3811549
theorem B1739807 : Blo 770335 1739807 := bstep (se 1 (by rfl) ⟨1304855, by rfl⟩ : syracuseStep 1739807 = 2609711) B2609711
theorem B1740527 : Blo 770335 1740527 := bstep (se 1 (by rfl) ⟨1305395, by rfl⟩ : syracuseStep 1740527 = 2610791) B2610791
theorem B1741031 : Blo 770335 1741031 := bstep (se 1 (by rfl) ⟨1305773, by rfl⟩ : syracuseStep 1741031 = 2611547) B2611547
theorem B1741139 : Blo 770335 1741139 := bstep (se 1 (by rfl) ⟨1305854, by rfl⟩ : syracuseStep 1741139 = 2611709) B2611709
theorem B2200441 : Blo 770335 2200441 := bstep (se 2 (by rfl) ⟨825165, by rfl⟩ : syracuseStep 2200441 = 1650331) B1650331
theorem B1742183 : Blo 770335 1742183 := bstep (se 1 (by rfl) ⟨1306637, by rfl⟩ : syracuseStep 1742183 = 2613275) B2613275
theorem B13178861 : Blo 770335 13178861 := bstep (se 3 (by rfl) ⟨2471036, by rfl⟩ : syracuseStep 13178861 = 4942073) B4942073
theorem B6264935 : Blo 770335 6264935 := bstep (se 1 (by rfl) ⟨4698701, by rfl⟩ : syracuseStep 6264935 = 9397403) B9397403
theorem B1645915 : Blo 770335 1645915 := bstep (se 1 (by rfl) ⟨1234436, by rfl⟩ : syracuseStep 1645915 = 2468873) B2468873
theorem B1155551 : Blo 770335 1155551 := bstep (se 1 (by rfl) ⟨866663, by rfl⟩ : syracuseStep 1155551 = 1733327) B1733327
theorem B121872883 : Blo 770335 121872883 := bstep (se 1 (by rfl) ⟨91404662, by rfl⟩ : syracuseStep 121872883 = 182809325) B182809325
theorem B3908735 : Blo 770335 3908735 := bstep (se 1 (by rfl) ⟨2931551, by rfl⟩ : syracuseStep 3908735 = 5863103) B5863103
theorem B1156361 : Blo 770335 1156361 := bstep (se 2 (by rfl) ⟨433635, by rfl⟩ : syracuseStep 1156361 = 867271) B867271
theorem B1648127 : Blo 770335 1648127 := bstep (se 1 (by rfl) ⟨1236095, by rfl⟩ : syracuseStep 1648127 = 2472191) B2472191
theorem B1156841 : Blo 770335 1156841 := bstep (se 2 (by rfl) ⟨433815, by rfl⟩ : syracuseStep 1156841 = 867631) B867631
theorem B4401863 : Blo 770335 4401863 := bstep (se 1 (by rfl) ⟨3301397, by rfl⟩ : syracuseStep 4401863 = 6602795) B6602795
theorem B1158635 : Blo 770335 1158635 := bstep (se 1 (by rfl) ⟨868976, by rfl⟩ : syracuseStep 1158635 = 1737953) B1737953
theorem B21114377 : Blo 770335 21114377 := bstep (se 2 (by rfl) ⟨7917891, by rfl⟩ : syracuseStep 21114377 = 15835783) B15835783
theorem B1158875 : Blo 770335 1158875 := bstep (se 1 (by rfl) ⟨869156, by rfl⟩ : syracuseStep 1158875 = 1738313) B1738313
theorem B4174591 : Blo 770335 4174591 := bstep (se 1 (by rfl) ⟨3130943, by rfl⟩ : syracuseStep 4174591 = 6261887) B6261887
theorem B1160039 : Blo 770335 1160039 := bstep (se 1 (by rfl) ⟨870029, by rfl⟩ : syracuseStep 1160039 = 1740059) B1740059
theorem B7943591 : Blo 770335 7943591 := bstep (se 1 (by rfl) ⟨5957693, by rfl⟩ : syracuseStep 7943591 = 11915387) B11915387
theorem B9877585 : Blo 770335 9877585 := bstep (se 2 (by rfl) ⟨3704094, by rfl⟩ : syracuseStep 9877585 = 7408189) B7408189
theorem B2865403 : Blo 770335 2865403 := bstep (se 1 (by rfl) ⟨2149052, by rfl⟩ : syracuseStep 2865403 = 4298105) B4298105
theorem B6601459 : Blo 770335 6601459 := bstep (se 1 (by rfl) ⟨4951094, by rfl⟩ : syracuseStep 6601459 = 9902189) B9902189
theorem B3292103 : Blo 770335 3292103 := bstep (se 1 (by rfl) ⟨2469077, by rfl⟩ : syracuseStep 3292103 = 4938155) B4938155
theorem B2932159 : Blo 770335 2932159 := bstep (se 1 (by rfl) ⟨2199119, by rfl⟩ : syracuseStep 2932159 = 4398239) B4398239
theorem B3718781 : Blo 770335 3718781 := bstep (se 3 (by rfl) ⟨697271, by rfl⟩ : syracuseStep 3718781 = 1394543) B1394543
theorem B770543 : Blo 770335 770543 := bstep (se 1 (by rfl) ⟨577907, by rfl⟩ : syracuseStep 770543 = 1155815) B1155815
theorem B771007 : Blo 770335 771007 := bstep (se 1 (by rfl) ⟨578255, by rfl⟩ : syracuseStep 771007 = 1156511) B1156511
theorem B3917159 : Blo 770335 3917159 := bstep (se 1 (by rfl) ⟨2937869, by rfl⟩ : syracuseStep 3917159 = 5875739) B5875739
theorem B869791 : Blo 770335 869791 := bstep (se 1 (by rfl) ⟨652343, by rfl⟩ : syracuseStep 869791 = 1304687) B1304687
theorem B2606633 : Blo 770335 2606633 := bstep (se 2 (by rfl) ⟨977487, by rfl⟩ : syracuseStep 2606633 = 1954975) B1954975
theorem B771711 : Blo 770335 771711 := bstep (se 1 (by rfl) ⟨578783, by rfl⟩ : syracuseStep 771711 = 1157567) B1157567
theorem B2508415 : Blo 770335 2508415 := bstep (se 1 (by rfl) ⟨1881311, by rfl⟩ : syracuseStep 2508415 = 3762623) B3762623
theorem B771815 : Blo 770335 771815 := bstep (se 1 (by rfl) ⟨578861, by rfl⟩ : syracuseStep 771815 = 1157723) B1157723
theorem B771911 : Blo 770335 771911 := bstep (se 1 (by rfl) ⟨578933, by rfl⟩ : syracuseStep 771911 = 1157867) B1157867
theorem B8800487 : Blo 770335 8800487 := bstep (se 1 (by rfl) ⟨6600365, by rfl⟩ : syracuseStep 8800487 = 13200731) B13200731
theorem B3295741 : Blo 770335 3295741 := bstep (se 3 (by rfl) ⟨617951, by rfl⟩ : syracuseStep 3295741 = 1235903) B1235903
theorem B773103 : Blo 770335 773103 := bstep (se 1 (by rfl) ⟨579827, by rfl⟩ : syracuseStep 773103 = 1159655) B1159655
theorem B773275 : Blo 770335 773275 := bstep (se 1 (by rfl) ⟨579956, by rfl⟩ : syracuseStep 773275 = 1159913) B1159913
theorem B6606107 : Blo 770335 6606107 := bstep (se 1 (by rfl) ⟨4954580, by rfl⟩ : syracuseStep 6606107 = 9909161) B9909161
theorem B774311 : Blo 770335 774311 := bstep (se 1 (by rfl) ⟨580733, by rfl⟩ : syracuseStep 774311 = 1161467) B1161467
theorem B1462951 : Blo 770335 1462951 := bstep (se 1 (by rfl) ⟨1097213, by rfl⟩ : syracuseStep 1462951 = 2194427) B2194427
theorem B13226975 : Blo 770335 13226975 := bstep (se 1 (by rfl) ⟨9920231, by rfl⟩ : syracuseStep 13226975 = 19840463) B19840463
theorem B7918877 : Blo 770335 7918877 := bstep (se 3 (by rfl) ⟨1484789, by rfl⟩ : syracuseStep 7918877 = 2969579) B2969579
theorem B2479535 : Blo 770335 2479535 := bstep (se 1 (by rfl) ⟨1859651, by rfl⟩ : syracuseStep 2479535 = 3719303) B3719303
theorem B3167711 : Blo 770335 3167711 := bstep (se 1 (by rfl) ⟨2375783, by rfl⟩ : syracuseStep 3167711 = 4751567) B4751567
theorem B26695169 : Blo 770335 26695169 := bstep (se 2 (by rfl) ⟨10010688, by rfl⟩ : syracuseStep 26695169 = 20021377) B20021377
theorem B2610953 : Blo 770335 2610953 := bstep (se 2 (by rfl) ⟨979107, by rfl⟩ : syracuseStep 2610953 = 1958215) B1958215
theorem B152491855 : Blo 770335 152491855 := bstep (se 1 (by rfl) ⟨114368891, by rfl⟩ : syracuseStep 152491855 = 228737783) B228737783
theorem B1301231 : Blo 770335 1301231 := bstep (se 1 (by rfl) ⟨975923, by rfl⟩ : syracuseStep 1301231 = 1951847) B1951847
theorem B2644991 : Blo 770335 2644991 := bstep (se 1 (by rfl) ⟨1983743, by rfl⟩ : syracuseStep 2644991 = 3967487) B3967487
theorem B12673097 : Blo 770335 12673097 := bstep (se 2 (by rfl) ⟨4752411, by rfl⟩ : syracuseStep 12673097 = 9504823) B9504823
theorem B7431335 : Blo 770335 7431335 := bstep (se 1 (by rfl) ⟨5573501, by rfl⟩ : syracuseStep 7431335 = 11147003) B11147003
theorem B3303449 : Blo 770335 3303449 := bstep (se 2 (by rfl) ⟨1238793, by rfl⟩ : syracuseStep 3303449 = 2477587) B2477587
theorem B108325187 : Blo 770335 108325187 := bstep (se 1 (by rfl) ⟨81243890, by rfl⟩ : syracuseStep 108325187 = 162487781) B162487781
theorem B1305031 : Blo 770335 1305031 := bstep (se 1 (by rfl) ⟨978773, by rfl⟩ : syracuseStep 1305031 = 1957547) B1957547
theorem B8809235 : Blo 770335 8809235 := bstep (se 1 (by rfl) ⟨6606926, by rfl⟩ : syracuseStep 8809235 = 13213853) B13213853
theorem B9891071 : Blo 770335 9891071 := bstep (se 1 (by rfl) ⟨7418303, by rfl⟩ : syracuseStep 9891071 = 14836607) B14836607
theorem B2780669 : Blo 770335 2780669 := bstep (se 3 (by rfl) ⟨521375, by rfl⟩ : syracuseStep 2780669 = 1042751) B1042751
theorem B1568951 : Blo 770335 1568951 := bstep (se 1 (by rfl) ⟨1176713, by rfl⟩ : syracuseStep 1568951 = 2353427) B2353427
theorem B1733345 : Blo 770335 1733345 := bstep (se 2 (by rfl) ⟨650004, by rfl⟩ : syracuseStep 1733345 = 1300009) B1300009
theorem B1733615 : Blo 770335 1733615 := bstep (se 1 (by rfl) ⟨1300211, by rfl⟩ : syracuseStep 1733615 = 2600423) B2600423
theorem B1734299 : Blo 770335 1734299 := bstep (se 1 (by rfl) ⟨1300724, by rfl⟩ : syracuseStep 1734299 = 2601449) B2601449
theorem B5863589 : Blo 770335 5863589 := bstep (se 4 (by rfl) ⟨549711, by rfl⟩ : syracuseStep 5863589 = 1099423) B1099423
theorem B6585299 : Blo 770335 6585299 := bstep (se 1 (by rfl) ⟨4938974, by rfl⟩ : syracuseStep 6585299 = 9877949) B9877949
theorem B162497177 : Blo 770335 162497177 := bstep (se 2 (by rfl) ⟨60936441, by rfl⟩ : syracuseStep 162497177 = 121872883) B121872883
theorem B1737755 : Blo 770335 1737755 := bstep (se 1 (by rfl) ⟨1303316, by rfl⟩ : syracuseStep 1737755 = 2606633) B2606633
theorem B5866991 : Blo 770335 5866991 := bstep (se 1 (by rfl) ⟨4400243, by rfl⟩ : syracuseStep 5866991 = 8800487) B8800487
theorem B1740041 : Blo 770335 1740041 := bstep (se 2 (by rfl) ⟨652515, by rfl⟩ : syracuseStep 1740041 = 1305031) B1305031
theorem B8817983 : Blo 770335 8817983 := bstep (se 1 (by rfl) ⟨6613487, by rfl⟩ : syracuseStep 8817983 = 13226975) B13226975
theorem B4394321 : Blo 770335 4394321 := bstep (se 2 (by rfl) ⟨1647870, by rfl⟩ : syracuseStep 4394321 = 3295741) B3295741
theorem B5279251 : Blo 770335 5279251 := bstep (se 1 (by rfl) ⟨3959438, by rfl⟩ : syracuseStep 5279251 = 7918877) B7918877
theorem B17796779 : Blo 770335 17796779 := bstep (se 1 (by rfl) ⟨13347584, by rfl⟩ : syracuseStep 17796779 = 26695169) B26695169
theorem B1740635 : Blo 770335 1740635 := bstep (se 1 (by rfl) ⟨1305476, by rfl⟩ : syracuseStep 1740635 = 2610953) B2610953
theorem B8785907 : Blo 770335 8785907 := bstep (se 1 (by rfl) ⟨6589430, by rfl⟩ : syracuseStep 8785907 = 13178861) B13178861
theorem B4395005 : Blo 770335 4395005 := bstep (se 3 (by rfl) ⟨824063, by rfl⟩ : syracuseStep 4395005 = 1648127) B1648127
theorem B4954223 : Blo 770335 4954223 := bstep (se 1 (by rfl) ⟨3715667, by rfl⟩ : syracuseStep 4954223 = 7431335) B7431335
theorem B2202299 : Blo 770335 2202299 := bstep (se 1 (by rfl) ⟨1651724, by rfl⟩ : syracuseStep 2202299 = 3303449) B3303449
theorem B5872823 : Blo 770335 5872823 := bstep (se 1 (by rfl) ⟨4404617, by rfl⟩ : syracuseStep 5872823 = 8809235) B8809235
theorem B6594047 : Blo 770335 6594047 := bstep (se 1 (by rfl) ⟨4945535, by rfl⟩ : syracuseStep 6594047 = 9891071) B9891071
theorem B1155563 : Blo 770335 1155563 := bstep (se 1 (by rfl) ⟨866672, by rfl⟩ : syracuseStep 1155563 = 1733345) B1733345
theorem B1155743 : Blo 770335 1155743 := bstep (se 1 (by rfl) ⟨866807, by rfl⟩ : syracuseStep 1155743 = 1733615) B1733615
theorem B13378213 : Blo 770335 13378213 := bstep (se 4 (by rfl) ⟨1254207, by rfl⟩ : syracuseStep 13378213 = 2508415) B2508415
theorem B1156199 : Blo 770335 1156199 := bstep (se 1 (by rfl) ⟨867149, by rfl⟩ : syracuseStep 1156199 = 1734299) B1734299
theorem B3909059 : Blo 770335 3909059 := bstep (se 1 (by rfl) ⟨2931794, by rfl⟩ : syracuseStep 3909059 = 5863589) B5863589
theorem B3909545 : Blo 770335 3909545 := bstep (se 2 (by rfl) ⟨1466079, by rfl⟩ : syracuseStep 3909545 = 2932159) B2932159
theorem B3713921 : Blo 770335 3713921 := bstep (se 2 (by rfl) ⟨1392720, by rfl⟩ : syracuseStep 3713921 = 2785441) B2785441
theorem B1158395 : Blo 770335 1158395 := bstep (se 1 (by rfl) ⟨868796, by rfl⟩ : syracuseStep 1158395 = 1737593) B1737593
theorem B3124943 : Blo 770335 3124943 := bstep (se 1 (by rfl) ⟨2343707, by rfl⟩ : syracuseStep 3124943 = 4687415) B4687415
theorem B1159721 : Blo 770335 1159721 := bstep (se 2 (by rfl) ⟨434895, by rfl⟩ : syracuseStep 1159721 = 869791) B869791
theorem B3388043 : Blo 770335 3388043 := bstep (se 1 (by rfl) ⟨2541032, by rfl⟩ : syracuseStep 3388043 = 5082065) B5082065
theorem B1159871 : Blo 770335 1159871 := bstep (se 1 (by rfl) ⟨869903, by rfl⟩ : syracuseStep 1159871 = 1739807) B1739807
theorem B4404071 : Blo 770335 4404071 := bstep (se 1 (by rfl) ⟨3303053, by rfl⟩ : syracuseStep 4404071 = 6606107) B6606107
theorem B1160351 : Blo 770335 1160351 := bstep (se 1 (by rfl) ⟨870263, by rfl⟩ : syracuseStep 1160351 = 1740527) B1740527
theorem B1160687 : Blo 770335 1160687 := bstep (se 1 (by rfl) ⟨870515, by rfl⟩ : syracuseStep 1160687 = 1741031) B1741031
theorem B1160759 : Blo 770335 1160759 := bstep (se 1 (by rfl) ⟨870569, by rfl⟩ : syracuseStep 1160759 = 1741139) B1741139
theorem B1161455 : Blo 770335 1161455 := bstep (se 1 (by rfl) ⟨871091, by rfl⟩ : syracuseStep 1161455 = 1742183) B1742183
theorem B1653023 : Blo 770335 1653023 := bstep (se 1 (by rfl) ⟨1239767, by rfl⟩ : syracuseStep 1653023 = 2479535) B2479535
theorem B2111807 : Blo 770335 2111807 := bstep (se 1 (by rfl) ⟨1583855, by rfl⟩ : syracuseStep 2111807 = 3167711) B3167711
theorem B4176623 : Blo 770335 4176623 := bstep (se 1 (by rfl) ⟨3132467, by rfl⟩ : syracuseStep 4176623 = 6264935) B6264935
theorem B867487 : Blo 770335 867487 := bstep (se 1 (by rfl) ⟨650615, by rfl⟩ : syracuseStep 867487 = 1301231) B1301231
theorem B770367 : Blo 770335 770367 := bstep (se 1 (by rfl) ⟨577775, by rfl⟩ : syracuseStep 770367 = 1155551) B1155551
theorem B2605823 : Blo 770335 2605823 := bstep (se 1 (by rfl) ⟨1954367, by rfl⟩ : syracuseStep 2605823 = 3908735) B3908735
theorem B770907 : Blo 770335 770907 := bstep (se 1 (by rfl) ⟨578180, by rfl⟩ : syracuseStep 770907 = 1156361) B1156361
theorem B1950601 : Blo 770335 1950601 := bstep (se 2 (by rfl) ⟨731475, by rfl⟩ : syracuseStep 1950601 = 1462951) B1462951
theorem B771227 : Blo 770335 771227 := bstep (se 1 (by rfl) ⟨578420, by rfl⟩ : syracuseStep 771227 = 1156841) B1156841
theorem B2933921 : Blo 770335 2933921 := bstep (se 2 (by rfl) ⟨1100220, by rfl⟩ : syracuseStep 2933921 = 2200441) B2200441
theorem B2934575 : Blo 770335 2934575 := bstep (se 1 (by rfl) ⟨2200931, by rfl⟩ : syracuseStep 2934575 = 4401863) B4401863
theorem B772423 : Blo 770335 772423 := bstep (se 1 (by rfl) ⟨579317, by rfl⟩ : syracuseStep 772423 = 1158635) B1158635
theorem B1853779 : Blo 770335 1853779 := bstep (se 1 (by rfl) ⟨1390334, by rfl⟩ : syracuseStep 1853779 = 2780669) B2780669
theorem B14076251 : Blo 770335 14076251 := bstep (se 1 (by rfl) ⟨10557188, by rfl⟩ : syracuseStep 14076251 = 21114377) B21114377
theorem B772583 : Blo 770335 772583 := bstep (se 1 (by rfl) ⟨579437, by rfl⟩ : syracuseStep 772583 = 1158875) B1158875
theorem B3820537 : Blo 770335 3820537 := bstep (se 2 (by rfl) ⟨1432701, by rfl⟩ : syracuseStep 3820537 = 2865403) B2865403
theorem B773359 : Blo 770335 773359 := bstep (se 1 (by rfl) ⟨580019, by rfl⟩ : syracuseStep 773359 = 1160039) B1160039
theorem B5295727 : Blo 770335 5295727 := bstep (se 1 (by rfl) ⟨3971795, by rfl⟩ : syracuseStep 5295727 = 7943591) B7943591
theorem B8801945 : Blo 770335 8801945 := bstep (se 2 (by rfl) ⟨3300729, by rfl⟩ : syracuseStep 8801945 = 6601459) B6601459
theorem B2479187 : Blo 770335 2479187 := bstep (se 1 (by rfl) ⟨1859390, by rfl⟩ : syracuseStep 2479187 = 3718781) B3718781
theorem B2611439 : Blo 770335 2611439 := bstep (se 1 (by rfl) ⟨1958579, by rfl⟩ : syracuseStep 2611439 = 3917159) B3917159
theorem B1763327 : Blo 770335 1763327 := bstep (se 1 (by rfl) ⟨1322495, by rfl⟩ : syracuseStep 1763327 = 2644991) B2644991
theorem B8448731 : Blo 770335 8448731 := bstep (se 1 (by rfl) ⟨6336548, by rfl⟩ : syracuseStep 8448731 = 12673097) B12673097
theorem B5566121 : Blo 770335 5566121 := bstep (se 2 (by rfl) ⟨2087295, by rfl⟩ : syracuseStep 5566121 = 4174591) B4174591
theorem B72216791 : Blo 770335 72216791 := bstep (se 1 (by rfl) ⟨54162593, by rfl⟩ : syracuseStep 72216791 = 108325187) B108325187
theorem B203322473 : Blo 770335 203322473 := bstep (se 2 (by rfl) ⟨76245927, by rfl⟩ : syracuseStep 203322473 = 152491855) B152491855
theorem B13170113 : Blo 770335 13170113 := bstep (se 2 (by rfl) ⟨4938792, by rfl⟩ : syracuseStep 13170113 = 9877585) B9877585
theorem B1045967 : Blo 770335 1045967 := bstep (se 1 (by rfl) ⟨784475, by rfl⟩ : syracuseStep 1045967 = 1568951) B1568951
theorem B2194553 : Blo 770335 2194553 := bstep (se 2 (by rfl) ⟨822957, by rfl⟩ : syracuseStep 2194553 = 1645915) B1645915
theorem B2194735 : Blo 770335 2194735 := bstep (se 1 (by rfl) ⟨1646051, by rfl⟩ : syracuseStep 2194735 = 3292103) B3292103
theorem B4390199 : Blo 770335 4390199 := bstep (se 1 (by rfl) ⟨3292649, by rfl⟩ : syracuseStep 4390199 = 6585299) B6585299
theorem B108331451 : Blo 770335 108331451 := bstep (se 1 (by rfl) ⟨81248588, by rfl⟩ : syracuseStep 108331451 = 162497177) B162497177
theorem B1737215 : Blo 770335 1737215 := bstep (se 1 (by rfl) ⟨1302911, by rfl⟩ : syracuseStep 1737215 = 2605823) B2605823
theorem B5867963 : Blo 770335 5867963 := bstep (se 1 (by rfl) ⟨4400972, by rfl⟩ : syracuseStep 5867963 = 8801945) B8801945
theorem B11864519 : Blo 770335 11864519 := bstep (se 1 (by rfl) ⟨8898389, by rfl⟩ : syracuseStep 11864519 = 17796779) B17796779
theorem B2789245 : Blo 770335 2789245 := bstep (se 3 (by rfl) ⟨522983, by rfl⟩ : syracuseStep 2789245 = 1045967) B1045967
theorem B1740959 : Blo 770335 1740959 := bstep (se 1 (by rfl) ⟨1305719, by rfl⟩ : syracuseStep 1740959 = 2611439) B2611439
theorem B4396031 : Blo 770335 4396031 := bstep (se 1 (by rfl) ⟨3297023, by rfl⟩ : syracuseStep 4396031 = 6594047) B6594047
theorem B3710747 : Blo 770335 3710747 := bstep (se 1 (by rfl) ⟨2783060, by rfl⟩ : syracuseStep 3710747 = 5566121) B5566121
theorem B48144527 : Blo 770335 48144527 := bstep (se 1 (by rfl) ⟨36108395, by rfl⟩ : syracuseStep 48144527 = 72216791) B72216791
theorem B1156649 : Blo 770335 1156649 := bstep (se 2 (by rfl) ⟨433743, by rfl⟩ : syracuseStep 1156649 = 867487) B867487
theorem B2926313 : Blo 770335 2926313 := bstep (se 2 (by rfl) ⟨1097367, by rfl⟩ : syracuseStep 2926313 = 2194735) B2194735
theorem B2926799 : Blo 770335 2926799 := bstep (se 1 (by rfl) ⟨2195099, by rfl⟩ : syracuseStep 2926799 = 4390199) B4390199
theorem B1158503 : Blo 770335 1158503 := bstep (se 1 (by rfl) ⟨868877, by rfl⟩ : syracuseStep 1158503 = 1737755) B1737755
theorem B17837617 : Blo 770335 17837617 := bstep (se 2 (by rfl) ⟨6689106, by rfl⟩ : syracuseStep 17837617 = 13378213) B13378213
theorem B3911327 : Blo 770335 3911327 := bstep (se 1 (by rfl) ⟨2933495, by rfl⟩ : syracuseStep 3911327 = 5866991) B5866991
theorem B2600801 : Blo 770335 2600801 := bstep (se 2 (by rfl) ⟨975300, by rfl⟩ : syracuseStep 2600801 = 1950601) B1950601
theorem B9384167 : Blo 770335 9384167 := bstep (se 1 (by rfl) ⟨7038125, by rfl⟩ : syracuseStep 9384167 = 14076251) B14076251
theorem B1160027 : Blo 770335 1160027 := bstep (se 1 (by rfl) ⟨870020, by rfl⟩ : syracuseStep 1160027 = 1740041) B1740041
theorem B5878655 : Blo 770335 5878655 := bstep (se 1 (by rfl) ⟨4408991, by rfl⟩ : syracuseStep 5878655 = 8817983) B8817983
theorem B2929547 : Blo 770335 2929547 := bstep (se 1 (by rfl) ⟨2197160, by rfl⟩ : syracuseStep 2929547 = 4394321) B4394321
theorem B1160423 : Blo 770335 1160423 := bstep (se 1 (by rfl) ⟨870317, by rfl⟩ : syracuseStep 1160423 = 1740635) B1740635
theorem B2930003 : Blo 770335 2930003 := bstep (se 1 (by rfl) ⟨2197502, by rfl⟩ : syracuseStep 2930003 = 4395005) B4395005
theorem B2471705 : Blo 770335 2471705 := bstep (se 2 (by rfl) ⟨926889, by rfl⟩ : syracuseStep 2471705 = 1853779) B1853779
theorem B3915215 : Blo 770335 3915215 := bstep (se 1 (by rfl) ⟨2936411, by rfl⟩ : syracuseStep 3915215 = 5872823) B5872823
theorem B7060969 : Blo 770335 7060969 := bstep (se 2 (by rfl) ⟨2647863, by rfl⟩ : syracuseStep 7060969 = 5295727) B5295727
theorem B4702205 : Blo 770335 4702205 := bstep (se 3 (by rfl) ⟨881663, by rfl⟩ : syracuseStep 4702205 = 1763327) B1763327
theorem B770375 : Blo 770335 770375 := bstep (se 1 (by rfl) ⟨577781, by rfl⟩ : syracuseStep 770375 = 1155563) B1155563
theorem B770495 : Blo 770335 770495 := bstep (se 1 (by rfl) ⟨577871, by rfl⟩ : syracuseStep 770495 = 1155743) B1155743
theorem B770799 : Blo 770335 770799 := bstep (se 1 (by rfl) ⟨578099, by rfl⟩ : syracuseStep 770799 = 1156199) B1156199
theorem B2606039 : Blo 770335 2606039 := bstep (se 1 (by rfl) ⟨1954529, by rfl⟩ : syracuseStep 2606039 = 3909059) B3909059
theorem B2606363 : Blo 770335 2606363 := bstep (se 1 (by rfl) ⟨1954772, by rfl⟩ : syracuseStep 2606363 = 3909545) B3909545
theorem B2475947 : Blo 770335 2475947 := bstep (se 1 (by rfl) ⟨1856960, by rfl⟩ : syracuseStep 2475947 = 3713921) B3713921
theorem B772263 : Blo 770335 772263 := bstep (se 1 (by rfl) ⟨579197, by rfl⟩ : syracuseStep 772263 = 1158395) B1158395
theorem B2083295 : Blo 770335 2083295 := bstep (se 1 (by rfl) ⟨1562471, by rfl⟩ : syracuseStep 2083295 = 3124943) B3124943
theorem B773147 : Blo 770335 773147 := bstep (se 1 (by rfl) ⟨579860, by rfl⟩ : syracuseStep 773147 = 1159721) B1159721
theorem B773247 : Blo 770335 773247 := bstep (se 1 (by rfl) ⟨579935, by rfl⟩ : syracuseStep 773247 = 1159871) B1159871
theorem B2936047 : Blo 770335 2936047 := bstep (se 1 (by rfl) ⟨2202035, by rfl⟩ : syracuseStep 2936047 = 4404071) B4404071
theorem B135548315 : Blo 770335 135548315 := bstep (se 1 (by rfl) ⟨101661236, by rfl⟩ : syracuseStep 135548315 = 203322473) B203322473
theorem B773567 : Blo 770335 773567 := bstep (se 1 (by rfl) ⟨580175, by rfl⟩ : syracuseStep 773567 = 1160351) B1160351
theorem B773791 : Blo 770335 773791 := bstep (se 1 (by rfl) ⟨580343, by rfl⟩ : syracuseStep 773791 = 1160687) B1160687
theorem B773839 : Blo 770335 773839 := bstep (se 1 (by rfl) ⟨580379, by rfl⟩ : syracuseStep 773839 = 1160759) B1160759
theorem B774303 : Blo 770335 774303 := bstep (se 1 (by rfl) ⟨580727, by rfl⟩ : syracuseStep 774303 = 1161455) B1161455
theorem B1102015 : Blo 770335 1102015 := bstep (se 1 (by rfl) ⟨826511, by rfl⟩ : syracuseStep 1102015 = 1653023) B1653023
theorem B1463035 : Blo 770335 1463035 := bstep (se 1 (by rfl) ⟨1097276, by rfl⟩ : syracuseStep 1463035 = 2194553) B2194553
theorem B1955947 : Blo 770335 1955947 := bstep (se 1 (by rfl) ⟨1466960, by rfl⟩ : syracuseStep 1955947 = 2933921) B2933921
theorem B1956383 : Blo 770335 1956383 := bstep (se 1 (by rfl) ⟨1467287, by rfl⟩ : syracuseStep 1956383 = 2934575) B2934575
theorem B5857271 : Blo 770335 5857271 := bstep (se 1 (by rfl) ⟨4392953, by rfl⟩ : syracuseStep 5857271 = 8785907) B8785907
theorem B6611165 : Blo 770335 6611165 := bstep (se 3 (by rfl) ⟨1239593, by rfl⟩ : syracuseStep 6611165 = 2479187) B2479187
theorem B3302815 : Blo 770335 3302815 := bstep (se 1 (by rfl) ⟨2477111, by rfl⟩ : syracuseStep 3302815 = 4954223) B4954223
theorem B1468199 : Blo 770335 1468199 := bstep (se 1 (by rfl) ⟨1101149, by rfl⟩ : syracuseStep 1468199 = 2202299) B2202299
theorem B7039001 : Blo 770335 7039001 := bstep (se 2 (by rfl) ⟨2639625, by rfl⟩ : syracuseStep 7039001 = 5279251) B5279251
theorem B20376197 : Blo 770335 20376197 := bstep (se 4 (by rfl) ⟨1910268, by rfl⟩ : syracuseStep 20376197 = 3820537) B3820537
theorem B5632487 : Blo 770335 5632487 := bstep (se 1 (by rfl) ⟨4224365, by rfl⟩ : syracuseStep 5632487 = 8448731) B8448731
theorem B11137661 : Blo 770335 11137661 := bstep (se 3 (by rfl) ⟨2088311, by rfl⟩ : syracuseStep 11137661 = 4176623) B4176623
theorem B2258695 : Blo 770335 2258695 := bstep (se 1 (by rfl) ⟨1694021, by rfl⟩ : syracuseStep 2258695 = 3388043) B3388043
theorem B8780075 : Blo 770335 8780075 := bstep (se 1 (by rfl) ⟨6585056, by rfl⟩ : syracuseStep 8780075 = 13170113) B13170113
theorem B1407871 : Blo 770335 1407871 := bstep (se 1 (by rfl) ⟨1055903, by rfl⟩ : syracuseStep 1407871 = 2111807) B2111807
theorem B72220967 : Blo 770335 72220967 := bstep (se 1 (by rfl) ⟨54165725, by rfl⟩ : syracuseStep 72220967 = 108331451) B108331451
theorem B1737359 : Blo 770335 1737359 := bstep (se 1 (by rfl) ⟨1303019, by rfl⟩ : syracuseStep 1737359 = 2606039) B2606039
theorem B1737575 : Blo 770335 1737575 := bstep (se 1 (by rfl) ⟨1303181, by rfl⟩ : syracuseStep 1737575 = 2606363) B2606363
theorem B7508645 : Blo 770335 7508645 := bstep (se 4 (by rfl) ⟨703935, by rfl⟩ : syracuseStep 7508645 = 1407871) B1407871
theorem B3904847 : Blo 770335 3904847 := bstep (se 1 (by rfl) ⟨2928635, by rfl⟩ : syracuseStep 3904847 = 5857271) B5857271
theorem B4692667 : Blo 770335 4692667 := bstep (se 1 (by rfl) ⟨3519500, by rfl⟩ : syracuseStep 4692667 = 7039001) B7039001
theorem B1647803 : Blo 770335 1647803 := bstep (se 1 (by rfl) ⟨1235852, by rfl⟩ : syracuseStep 1647803 = 2471705) B2471705
theorem B9414625 : Blo 770335 9414625 := bstep (se 2 (by rfl) ⟨3530484, by rfl⟩ : syracuseStep 9414625 = 7060969) B7060969
theorem B1158143 : Blo 770335 1158143 := bstep (se 1 (by rfl) ⟨868607, by rfl⟩ : syracuseStep 1158143 = 1737215) B1737215
theorem B1650631 : Blo 770335 1650631 := bstep (se 1 (by rfl) ⟨1237973, by rfl⟩ : syracuseStep 1650631 = 2475947) B2475947
theorem B3911975 : Blo 770335 3911975 := bstep (se 1 (by rfl) ⟨2933981, by rfl⟩ : syracuseStep 3911975 = 5867963) B5867963
theorem B7909679 : Blo 770335 7909679 := bstep (se 1 (by rfl) ⟨5932259, by rfl⟩ : syracuseStep 7909679 = 11864519) B11864519
theorem B1388863 : Blo 770335 1388863 := bstep (se 1 (by rfl) ⟨1041647, by rfl⟩ : syracuseStep 1388863 = 2083295) B2083295
theorem B4403753 : Blo 770335 4403753 := bstep (se 2 (by rfl) ⟨1651407, by rfl⟩ : syracuseStep 4403753 = 3302815) B3302815
theorem B1160639 : Blo 770335 1160639 := bstep (se 1 (by rfl) ⟨870479, by rfl⟩ : syracuseStep 1160639 = 1740959) B1740959
theorem B2930687 : Blo 770335 2930687 := bstep (se 1 (by rfl) ⟨2198015, by rfl⟩ : syracuseStep 2930687 = 4396031) B4396031
theorem B3914729 : Blo 770335 3914729 := bstep (se 2 (by rfl) ⟨1468023, by rfl⟩ : syracuseStep 3914729 = 2936047) B2936047
theorem B2473831 : Blo 770335 2473831 := bstep (se 1 (by rfl) ⟨1855373, by rfl⟩ : syracuseStep 2473831 = 3710747) B3710747
theorem B32096351 : Blo 770335 32096351 := bstep (se 1 (by rfl) ⟨24072263, by rfl⟩ : syracuseStep 32096351 = 48144527) B48144527
theorem B4407443 : Blo 770335 4407443 := bstep (se 1 (by rfl) ⟨3305582, by rfl⟩ : syracuseStep 4407443 = 6611165) B6611165
theorem B1950713 : Blo 770335 1950713 := bstep (se 2 (by rfl) ⟨731517, by rfl⟩ : syracuseStep 1950713 = 1463035) B1463035
theorem B771099 : Blo 770335 771099 := bstep (se 1 (by rfl) ⟨578324, by rfl⟩ : syracuseStep 771099 = 1156649) B1156649
theorem B1950875 : Blo 770335 1950875 := bstep (se 1 (by rfl) ⟨1463156, by rfl⟩ : syracuseStep 1950875 = 2926313) B2926313
theorem B1951199 : Blo 770335 1951199 := bstep (se 1 (by rfl) ⟨1463399, by rfl⟩ : syracuseStep 1951199 = 2926799) B2926799
theorem B13584131 : Blo 770335 13584131 := bstep (se 1 (by rfl) ⟨10188098, by rfl⟩ : syracuseStep 13584131 = 20376197) B20376197
theorem B772335 : Blo 770335 772335 := bstep (se 1 (by rfl) ⟨579251, by rfl⟩ : syracuseStep 772335 = 1158503) B1158503
theorem B2607551 : Blo 770335 2607551 := bstep (se 1 (by rfl) ⟨1955663, by rfl⟩ : syracuseStep 2607551 = 3911327) B3911327
theorem B2607929 : Blo 770335 2607929 := bstep (se 2 (by rfl) ⟨977973, by rfl⟩ : syracuseStep 2607929 = 1955947) B1955947
theorem B3754991 : Blo 770335 3754991 := bstep (se 1 (by rfl) ⟨2816243, by rfl⟩ : syracuseStep 3754991 = 5632487) B5632487
theorem B7425107 : Blo 770335 7425107 := bstep (se 1 (by rfl) ⟨5568830, by rfl⟩ : syracuseStep 7425107 = 11137661) B11137661
theorem B773351 : Blo 770335 773351 := bstep (se 1 (by rfl) ⟨580013, by rfl⟩ : syracuseStep 773351 = 1160027) B1160027
theorem B3919103 : Blo 770335 3919103 := bstep (se 1 (by rfl) ⟨2939327, by rfl⟩ : syracuseStep 3919103 = 5878655) B5878655
theorem B1953031 : Blo 770335 1953031 := bstep (se 1 (by rfl) ⟨1464773, by rfl⟩ : syracuseStep 1953031 = 2929547) B2929547
theorem B773615 : Blo 770335 773615 := bstep (se 1 (by rfl) ⟨580211, by rfl⟩ : syracuseStep 773615 = 1160423) B1160423
theorem B1953335 : Blo 770335 1953335 := bstep (se 1 (by rfl) ⟨1465001, by rfl⟩ : syracuseStep 1953335 = 2930003) B2930003
theorem B12046373 : Blo 770335 12046373 := bstep (se 4 (by rfl) ⟨1129347, by rfl⟩ : syracuseStep 12046373 = 2258695) B2258695
theorem B5853383 : Blo 770335 5853383 := bstep (se 1 (by rfl) ⟨4390037, by rfl⟩ : syracuseStep 5853383 = 8780075) B8780075
theorem B2610143 : Blo 770335 2610143 := bstep (se 1 (by rfl) ⟨1957607, by rfl⟩ : syracuseStep 2610143 = 3915215) B3915215
theorem B3134803 : Blo 770335 3134803 := bstep (se 1 (by rfl) ⟨2351102, by rfl⟩ : syracuseStep 3134803 = 4702205) B4702205
theorem B90365543 : Blo 770335 90365543 := bstep (se 1 (by rfl) ⟨67774157, by rfl⟩ : syracuseStep 90365543 = 135548315) B135548315
theorem B1304255 : Blo 770335 1304255 := bstep (se 1 (by rfl) ⟨978191, by rfl⟩ : syracuseStep 1304255 = 1956383) B1956383
theorem B23783489 : Blo 770335 23783489 := bstep (se 2 (by rfl) ⟨8918808, by rfl⟩ : syracuseStep 23783489 = 17837617) B17837617
theorem B1469353 : Blo 770335 1469353 := bstep (se 2 (by rfl) ⟨551007, by rfl⟩ : syracuseStep 1469353 = 1102015) B1102015
theorem B978799 : Blo 770335 978799 := bstep (se 1 (by rfl) ⟨734099, by rfl⟩ : syracuseStep 978799 = 1468199) B1468199
theorem B1733867 : Blo 770335 1733867 := bstep (se 1 (by rfl) ⟨1300400, by rfl⟩ : syracuseStep 1733867 = 2600801) B2600801
theorem B6256111 : Blo 770335 6256111 := bstep (se 1 (by rfl) ⟨4692083, by rfl⟩ : syracuseStep 6256111 = 9384167) B9384167
theorem B14875973 : Blo 770335 14875973 := bstep (se 4 (by rfl) ⟨1394622, by rfl⟩ : syracuseStep 14875973 = 2789245) B2789245
theorem B21397567 : Blo 770335 21397567 := bstep (se 1 (by rfl) ⟨16048175, by rfl⟩ : syracuseStep 21397567 = 32096351) B32096351
theorem B1738367 : Blo 770335 1738367 := bstep (se 1 (by rfl) ⟨1303775, by rfl⟩ : syracuseStep 1738367 = 2607551) B2607551
theorem B1738619 : Blo 770335 1738619 := bstep (se 1 (by rfl) ⟨1303964, by rfl⟩ : syracuseStep 1738619 = 2607929) B2607929
theorem B4950071 : Blo 770335 4950071 := bstep (se 1 (by rfl) ⟨3712553, by rfl⟩ : syracuseStep 4950071 = 7425107) B7425107
theorem B12552833 : Blo 770335 12552833 := bstep (se 2 (by rfl) ⟨4707312, by rfl⟩ : syracuseStep 12552833 = 9414625) B9414625
theorem B8030915 : Blo 770335 8030915 := bstep (se 1 (by rfl) ⟨6023186, by rfl⟩ : syracuseStep 8030915 = 12046373) B12046373
theorem B3902255 : Blo 770335 3902255 := bstep (se 1 (by rfl) ⟨2926691, by rfl⟩ : syracuseStep 3902255 = 5853383) B5853383
theorem B1740095 : Blo 770335 1740095 := bstep (se 1 (by rfl) ⟨1305071, by rfl⟩ : syracuseStep 1740095 = 2610143) B2610143
theorem B2200841 : Blo 770335 2200841 := bstep (se 2 (by rfl) ⟨825315, by rfl⟩ : syracuseStep 2200841 = 1650631) B1650631
theorem B1155911 : Blo 770335 1155911 := bstep (se 1 (by rfl) ⟨866933, by rfl⟩ : syracuseStep 1155911 = 1733867) B1733867
theorem B48147311 : Blo 770335 48147311 := bstep (se 1 (by rfl) ⟨36110483, by rfl⟩ : syracuseStep 48147311 = 72220967) B72220967
theorem B1158239 : Blo 770335 1158239 := bstep (se 1 (by rfl) ⟨868679, by rfl⟩ : syracuseStep 1158239 = 1737359) B1737359
theorem B1158383 : Blo 770335 1158383 := bstep (se 1 (by rfl) ⟨868787, by rfl⟩ : syracuseStep 1158383 = 1737575) B1737575
theorem B9056087 : Blo 770335 9056087 := bstep (se 1 (by rfl) ⟨6792065, by rfl⟩ : syracuseStep 9056087 = 13584131) B13584131
theorem B2503327 : Blo 770335 2503327 := bstep (se 1 (by rfl) ⟨1877495, by rfl⟩ : syracuseStep 2503327 = 3754991) B3754991
theorem B2603231 : Blo 770335 2603231 := bstep (se 1 (by rfl) ⟨1952423, by rfl⟩ : syracuseStep 2603231 = 3904847) B3904847
theorem B2604041 : Blo 770335 2604041 := bstep (se 2 (by rfl) ⟨976515, by rfl⟩ : syracuseStep 2604041 = 1953031) B1953031
theorem B60243695 : Blo 770335 60243695 := bstep (se 1 (by rfl) ⟨45182771, by rfl⟩ : syracuseStep 60243695 = 90365543) B90365543
theorem B1851817 : Blo 770335 1851817 := bstep (se 2 (by rfl) ⟨694431, by rfl⟩ : syracuseStep 1851817 = 1388863) B1388863
theorem B1098535 : Blo 770335 1098535 := bstep (se 1 (by rfl) ⟨823901, by rfl⟩ : syracuseStep 1098535 = 1647803) B1647803
theorem B869503 : Blo 770335 869503 := bstep (se 1 (by rfl) ⟨652127, by rfl⟩ : syracuseStep 869503 = 1304255) B1304255
theorem B4179737 : Blo 770335 4179737 := bstep (se 2 (by rfl) ⟨1567401, by rfl⟩ : syracuseStep 4179737 = 3134803) B3134803
theorem B8341481 : Blo 770335 8341481 := bstep (se 2 (by rfl) ⟨3128055, by rfl⟩ : syracuseStep 8341481 = 6256111) B6256111
theorem B772095 : Blo 770335 772095 := bstep (se 1 (by rfl) ⟨579071, by rfl⟩ : syracuseStep 772095 = 1158143) B1158143
theorem B2607983 : Blo 770335 2607983 := bstep (se 1 (by rfl) ⟨1955987, by rfl⟩ : syracuseStep 2607983 = 3911975) B3911975
theorem B2935835 : Blo 770335 2935835 := bstep (se 1 (by rfl) ⟨2201876, by rfl⟩ : syracuseStep 2935835 = 4403753) B4403753
theorem B773759 : Blo 770335 773759 := bstep (se 1 (by rfl) ⟨580319, by rfl⟩ : syracuseStep 773759 = 1160639) B1160639
theorem B1953791 : Blo 770335 1953791 := bstep (se 1 (by rfl) ⟨1465343, by rfl⟩ : syracuseStep 1953791 = 2930687) B2930687
theorem B2609819 : Blo 770335 2609819 := bstep (se 1 (by rfl) ⟨1957364, by rfl⟩ : syracuseStep 2609819 = 3914729) B3914729
theorem B9917315 : Blo 770335 9917315 := bstep (se 1 (by rfl) ⟨7437986, by rfl⟩ : syracuseStep 9917315 = 14875973) B14875973
theorem B3298441 : Blo 770335 3298441 := bstep (se 2 (by rfl) ⟨1236915, by rfl⟩ : syracuseStep 3298441 = 2473831) B2473831
theorem B2938295 : Blo 770335 2938295 := bstep (se 1 (by rfl) ⟨2203721, by rfl⟩ : syracuseStep 2938295 = 4407443) B4407443
theorem B1300475 : Blo 770335 1300475 := bstep (se 1 (by rfl) ⟨975356, by rfl⟩ : syracuseStep 1300475 = 1950713) B1950713
theorem B1300583 : Blo 770335 1300583 := bstep (se 1 (by rfl) ⟨975437, by rfl⟩ : syracuseStep 1300583 = 1950875) B1950875
theorem B1300799 : Blo 770335 1300799 := bstep (se 1 (by rfl) ⟨975599, by rfl⟩ : syracuseStep 1300799 = 1951199) B1951199
theorem B2612735 : Blo 770335 2612735 := bstep (se 1 (by rfl) ⟨1959551, by rfl⟩ : syracuseStep 2612735 = 3919103) B3919103
theorem B1302223 : Blo 770335 1302223 := bstep (se 1 (by rfl) ⟨976667, by rfl⟩ : syracuseStep 1302223 = 1953335) B1953335
theorem B5005763 : Blo 770335 5005763 := bstep (se 1 (by rfl) ⟨3754322, by rfl⟩ : syracuseStep 5005763 = 7508645) B7508645
theorem B1959137 : Blo 770335 1959137 := bstep (se 2 (by rfl) ⟨734676, by rfl⟩ : syracuseStep 1959137 = 1469353) B1469353
theorem B1305065 : Blo 770335 1305065 := bstep (se 2 (by rfl) ⟨489399, by rfl⟩ : syracuseStep 1305065 = 978799) B978799
theorem B15855659 : Blo 770335 15855659 := bstep (se 1 (by rfl) ⟨11891744, by rfl⟩ : syracuseStep 15855659 = 23783489) B23783489
theorem B5273119 : Blo 770335 5273119 := bstep (se 1 (by rfl) ⟨3954839, by rfl⟩ : syracuseStep 5273119 = 7909679) B7909679
theorem B6256889 : Blo 770335 6256889 := bstep (se 2 (by rfl) ⟨2346333, by rfl⟩ : syracuseStep 6256889 = 4692667) B4692667
theorem B2786491 : Blo 770335 2786491 := bstep (se 1 (by rfl) ⟨2089868, by rfl⟩ : syracuseStep 2786491 = 4179737) B4179737
theorem B1738655 : Blo 770335 1738655 := bstep (se 1 (by rfl) ⟨1303991, by rfl⟩ : syracuseStep 1738655 = 2607983) B2607983
theorem B1739879 : Blo 770335 1739879 := bstep (se 1 (by rfl) ⟨1304909, by rfl⟩ : syracuseStep 1739879 = 2609819) B2609819
theorem B1741823 : Blo 770335 1741823 := bstep (se 1 (by rfl) ⟨1306367, by rfl⟩ : syracuseStep 1741823 = 2612735) B2612735
theorem B4397921 : Blo 770335 4397921 := bstep (se 2 (by rfl) ⟨1649220, by rfl⟩ : syracuseStep 4397921 = 3298441) B3298441
theorem B6037391 : Blo 770335 6037391 := bstep (se 1 (by rfl) ⟨4528043, by rfl⟩ : syracuseStep 6037391 = 9056087) B9056087
theorem B28123301 : Blo 770335 28123301 := bstep (se 4 (by rfl) ⟨2636559, by rfl⟩ : syracuseStep 28123301 = 5273119) B5273119
theorem B4171259 : Blo 770335 4171259 := bstep (se 1 (by rfl) ⟨3128444, by rfl⟩ : syracuseStep 4171259 = 6256889) B6256889
theorem B2469089 : Blo 770335 2469089 := bstep (se 2 (by rfl) ⟨925908, by rfl⟩ : syracuseStep 2469089 = 1851817) B1851817
theorem B1158911 : Blo 770335 1158911 := bstep (se 1 (by rfl) ⟨869183, by rfl⟩ : syracuseStep 1158911 = 1738367) B1738367
theorem B1159079 : Blo 770335 1159079 := bstep (se 1 (by rfl) ⟨869309, by rfl⟩ : syracuseStep 1159079 = 1738619) B1738619
theorem B1159337 : Blo 770335 1159337 := bstep (se 2 (by rfl) ⟨434751, by rfl⟩ : syracuseStep 1159337 = 869503) B869503
theorem B5353943 : Blo 770335 5353943 := bstep (se 1 (by rfl) ⟨4015457, by rfl⟩ : syracuseStep 5353943 = 8030915) B8030915
theorem B2601503 : Blo 770335 2601503 := bstep (se 1 (by rfl) ⟨1951127, by rfl⟩ : syracuseStep 2601503 = 3902255) B3902255
theorem B1160063 : Blo 770335 1160063 := bstep (se 1 (by rfl) ⟨870047, by rfl⟩ : syracuseStep 1160063 = 1740095) B1740095
theorem B866983 : Blo 770335 866983 := bstep (se 1 (by rfl) ⟨650237, by rfl⟩ : syracuseStep 866983 = 1300475) B1300475
theorem B867055 : Blo 770335 867055 := bstep (se 1 (by rfl) ⟨650291, by rfl⟩ : syracuseStep 867055 = 1300583) B1300583
theorem B867199 : Blo 770335 867199 := bstep (se 1 (by rfl) ⟨650399, by rfl⟩ : syracuseStep 867199 = 1300799) B1300799
theorem B770607 : Blo 770335 770607 := bstep (se 1 (by rfl) ⟨577955, by rfl⟩ : syracuseStep 770607 = 1155911) B1155911
theorem B870043 : Blo 770335 870043 := bstep (se 1 (by rfl) ⟨652532, by rfl⟩ : syracuseStep 870043 = 1305065) B1305065
theorem B33474221 : Blo 770335 33474221 := bstep (se 3 (by rfl) ⟨6276416, by rfl⟩ : syracuseStep 33474221 = 12552833) B12552833
theorem B32098207 : Blo 770335 32098207 := bstep (se 1 (by rfl) ⟨24073655, by rfl⟩ : syracuseStep 32098207 = 48147311) B48147311
theorem B772159 : Blo 770335 772159 := bstep (se 1 (by rfl) ⟨579119, by rfl⟩ : syracuseStep 772159 = 1158239) B1158239
theorem B772255 : Blo 770335 772255 := bstep (se 1 (by rfl) ⟨579191, by rfl⟩ : syracuseStep 772255 = 1158383) B1158383
theorem B10570439 : Blo 770335 10570439 := bstep (se 1 (by rfl) ⟨7927829, by rfl⟩ : syracuseStep 10570439 = 15855659) B15855659
theorem B40162463 : Blo 770335 40162463 := bstep (se 1 (by rfl) ⟨30121847, by rfl⟩ : syracuseStep 40162463 = 60243695) B60243695
theorem B28530089 : Blo 770335 28530089 := bstep (se 2 (by rfl) ⟨10698783, by rfl⟩ : syracuseStep 28530089 = 21397567) B21397567
theorem B1464713 : Blo 770335 1464713 := bstep (se 2 (by rfl) ⟨549267, by rfl⟩ : syracuseStep 1464713 = 1098535) B1098535
theorem B5560987 : Blo 770335 5560987 := bstep (se 1 (by rfl) ⟨4170740, by rfl⟩ : syracuseStep 5560987 = 8341481) B8341481
theorem B3300047 : Blo 770335 3300047 := bstep (se 1 (by rfl) ⟨2475035, by rfl⟩ : syracuseStep 3300047 = 4950071) B4950071
theorem B1957223 : Blo 770335 1957223 := bstep (se 1 (by rfl) ⟨1467917, by rfl⟩ : syracuseStep 1957223 = 2935835) B2935835
theorem B1302527 : Blo 770335 1302527 := bstep (se 1 (by rfl) ⟨976895, by rfl⟩ : syracuseStep 1302527 = 1953791) B1953791
theorem B6611543 : Blo 770335 6611543 := bstep (se 1 (by rfl) ⟨4958657, by rfl⟩ : syracuseStep 6611543 = 9917315) B9917315
theorem B1467227 : Blo 770335 1467227 := bstep (se 1 (by rfl) ⟨1100420, by rfl⟩ : syracuseStep 1467227 = 2200841) B2200841
theorem B1958863 : Blo 770335 1958863 := bstep (se 1 (by rfl) ⟨1469147, by rfl⟩ : syracuseStep 1958863 = 2938295) B2938295
theorem B3337175 : Blo 770335 3337175 := bstep (se 1 (by rfl) ⟨2502881, by rfl⟩ : syracuseStep 3337175 = 5005763) B5005763
theorem B1306091 : Blo 770335 1306091 := bstep (se 1 (by rfl) ⟨979568, by rfl⟩ : syracuseStep 1306091 = 1959137) B1959137
theorem B3337769 : Blo 770335 3337769 := bstep (se 2 (by rfl) ⟨1251663, by rfl⟩ : syracuseStep 3337769 = 2503327) B2503327
theorem B1735487 : Blo 770335 1735487 := bstep (se 1 (by rfl) ⟨1301615, by rfl⟩ : syracuseStep 1735487 = 2603231) B2603231
theorem B1736027 : Blo 770335 1736027 := bstep (se 1 (by rfl) ⟨1302020, by rfl⟩ : syracuseStep 1736027 = 2604041) B2604041
theorem B1736297 : Blo 770335 1736297 := bstep (se 2 (by rfl) ⟨651111, by rfl⟩ : syracuseStep 1736297 = 1302223) B1302223
theorem B22316147 : Blo 770335 22316147 := bstep (se 1 (by rfl) ⟨16737110, by rfl⟩ : syracuseStep 22316147 = 33474221) B33474221
theorem B7046959 : Blo 770335 7046959 := bstep (se 1 (by rfl) ⟨5285219, by rfl⟩ : syracuseStep 7046959 = 10570439) B10570439
theorem B42797609 : Blo 770335 42797609 := bstep (se 2 (by rfl) ⟨16049103, by rfl⟩ : syracuseStep 42797609 = 32098207) B32098207
theorem B26774975 : Blo 770335 26774975 := bstep (se 1 (by rfl) ⟨20081231, by rfl⟩ : syracuseStep 26774975 = 40162463) B40162463
theorem B2200031 : Blo 770335 2200031 := bstep (se 1 (by rfl) ⟨1650023, by rfl⟩ : syracuseStep 2200031 = 3300047) B3300047
theorem B18748867 : Blo 770335 18748867 := bstep (se 1 (by rfl) ⟨14061650, by rfl⟩ : syracuseStep 18748867 = 28123301) B28123301
theorem B7414649 : Blo 770335 7414649 := bstep (se 2 (by rfl) ⟨2780493, by rfl⟩ : syracuseStep 7414649 = 5560987) B5560987
theorem B1155977 : Blo 770335 1155977 := bstep (se 2 (by rfl) ⟨433491, by rfl⟩ : syracuseStep 1155977 = 866983) B866983
theorem B1156073 : Blo 770335 1156073 := bstep (se 2 (by rfl) ⟨433527, by rfl⟩ : syracuseStep 1156073 = 867055) B867055
theorem B1156265 : Blo 770335 1156265 := bstep (se 2 (by rfl) ⟨433599, by rfl⟩ : syracuseStep 1156265 = 867199) B867199
theorem B1156991 : Blo 770335 1156991 := bstep (se 1 (by rfl) ⟨867743, by rfl⟩ : syracuseStep 1156991 = 1735487) B1735487
theorem B1157351 : Blo 770335 1157351 := bstep (se 1 (by rfl) ⟨868013, by rfl⟩ : syracuseStep 1157351 = 1736027) B1736027
theorem B1157531 : Blo 770335 1157531 := bstep (se 1 (by rfl) ⟨868148, by rfl⟩ : syracuseStep 1157531 = 1736297) B1736297
theorem B1159103 : Blo 770335 1159103 := bstep (se 1 (by rfl) ⟨869327, by rfl⟩ : syracuseStep 1159103 = 1738655) B1738655
theorem B3715321 : Blo 770335 3715321 := bstep (se 2 (by rfl) ⟨1393245, by rfl⟩ : syracuseStep 3715321 = 2786491) B2786491
theorem B1159919 : Blo 770335 1159919 := bstep (se 1 (by rfl) ⟨869939, by rfl⟩ : syracuseStep 1159919 = 1739879) B1739879
theorem B1160057 : Blo 770335 1160057 := bstep (se 2 (by rfl) ⟨435021, by rfl⟩ : syracuseStep 1160057 = 870043) B870043
theorem B1161215 : Blo 770335 1161215 := bstep (se 1 (by rfl) ⟨870911, by rfl⟩ : syracuseStep 1161215 = 1741823) B1741823
theorem B19020059 : Blo 770335 19020059 := bstep (se 1 (by rfl) ⟨14265044, by rfl⟩ : syracuseStep 19020059 = 28530089) B28530089
theorem B2931947 : Blo 770335 2931947 := bstep (se 1 (by rfl) ⟨2198960, by rfl⟩ : syracuseStep 2931947 = 4397921) B4397921
theorem B868351 : Blo 770335 868351 := bstep (se 1 (by rfl) ⟨651263, by rfl⟩ : syracuseStep 868351 = 1302527) B1302527
theorem B4407695 : Blo 770335 4407695 := bstep (se 1 (by rfl) ⟨3305771, by rfl⟩ : syracuseStep 4407695 = 6611543) B6611543
theorem B870727 : Blo 770335 870727 := bstep (se 1 (by rfl) ⟨653045, by rfl⟩ : syracuseStep 870727 = 1306091) B1306091
theorem B772607 : Blo 770335 772607 := bstep (se 1 (by rfl) ⟨579455, by rfl⟩ : syracuseStep 772607 = 1158911) B1158911
theorem B772719 : Blo 770335 772719 := bstep (se 1 (by rfl) ⟨579539, by rfl⟩ : syracuseStep 772719 = 1159079) B1159079
theorem B772891 : Blo 770335 772891 := bstep (se 1 (by rfl) ⟨579668, by rfl⟩ : syracuseStep 772891 = 1159337) B1159337
theorem B773375 : Blo 770335 773375 := bstep (se 1 (by rfl) ⟨580031, by rfl⟩ : syracuseStep 773375 = 1160063) B1160063
theorem B14277181 : Blo 770335 14277181 := bstep (se 3 (by rfl) ⟨2676971, by rfl⟩ : syracuseStep 14277181 = 5353943) B5353943
theorem B2611817 : Blo 770335 2611817 := bstep (se 2 (by rfl) ⟨979431, by rfl⟩ : syracuseStep 2611817 = 1958863) B1958863
theorem B976475 : Blo 770335 976475 := bstep (se 1 (by rfl) ⟨732356, by rfl⟩ : syracuseStep 976475 = 1464713) B1464713
theorem B1304815 : Blo 770335 1304815 := bstep (se 1 (by rfl) ⟨978611, by rfl⟩ : syracuseStep 1304815 = 1957223) B1957223
theorem B4024927 : Blo 770335 4024927 := bstep (se 1 (by rfl) ⟨3018695, by rfl⟩ : syracuseStep 4024927 = 6037391) B6037391
theorem B978151 : Blo 770335 978151 := bstep (se 1 (by rfl) ⟨733613, by rfl⟩ : syracuseStep 978151 = 1467227) B1467227
theorem B2780839 : Blo 770335 2780839 := bstep (se 1 (by rfl) ⟨2085629, by rfl⟩ : syracuseStep 2780839 = 4171259) B4171259
theorem B2224783 : Blo 770335 2224783 := bstep (se 1 (by rfl) ⟨1668587, by rfl⟩ : syracuseStep 2224783 = 3337175) B3337175
theorem B2225179 : Blo 770335 2225179 := bstep (se 1 (by rfl) ⟨1668884, by rfl⟩ : syracuseStep 2225179 = 3337769) B3337769
theorem B1734335 : Blo 770335 1734335 := bstep (se 1 (by rfl) ⟨1300751, by rfl⟩ : syracuseStep 1734335 = 2601503) B2601503
theorem B6584237 : Blo 770335 6584237 := bstep (se 3 (by rfl) ⟨1234544, by rfl⟩ : syracuseStep 6584237 = 2469089) B2469089
theorem B14877431 : Blo 770335 14877431 := bstep (se 1 (by rfl) ⟨11158073, by rfl⟩ : syracuseStep 14877431 = 22316147) B22316147
theorem B1739753 : Blo 770335 1739753 := bstep (se 2 (by rfl) ⟨652407, by rfl⟩ : syracuseStep 1739753 = 1304815) B1304815
theorem B1741211 : Blo 770335 1741211 := bstep (se 1 (by rfl) ⟨1305908, by rfl⟩ : syracuseStep 1741211 = 2611817) B2611817
theorem B3707785 : Blo 770335 3707785 := bstep (se 2 (by rfl) ⟨1390419, by rfl⟩ : syracuseStep 3707785 = 2780839) B2780839
theorem B4953761 : Blo 770335 4953761 := bstep (se 2 (by rfl) ⟨1857660, by rfl⟩ : syracuseStep 4953761 = 3715321) B3715321
theorem B1156223 : Blo 770335 1156223 := bstep (se 1 (by rfl) ⟨867167, by rfl⟩ : syracuseStep 1156223 = 1734335) B1734335
theorem B1157801 : Blo 770335 1157801 := bstep (se 2 (by rfl) ⟨434175, by rfl⟩ : syracuseStep 1157801 = 868351) B868351
theorem B1160969 : Blo 770335 1160969 := bstep (se 2 (by rfl) ⟨435363, by rfl⟩ : syracuseStep 1160969 = 870727) B870727
theorem B2603933 : Blo 770335 2603933 := bstep (se 3 (by rfl) ⟨488237, by rfl⟩ : syracuseStep 2603933 = 976475) B976475
theorem B770651 : Blo 770335 770651 := bstep (se 1 (by rfl) ⟨577988, by rfl⟩ : syracuseStep 770651 = 1155977) B1155977
theorem B770715 : Blo 770335 770715 := bstep (se 1 (by rfl) ⟨578036, by rfl⟩ : syracuseStep 770715 = 1156073) B1156073
theorem B770843 : Blo 770335 770843 := bstep (se 1 (by rfl) ⟨578132, by rfl⟩ : syracuseStep 770843 = 1156265) B1156265
theorem B2966377 : Blo 770335 2966377 := bstep (se 2 (by rfl) ⟨1112391, by rfl⟩ : syracuseStep 2966377 = 2224783) B2224783
theorem B771327 : Blo 770335 771327 := bstep (se 1 (by rfl) ⟨578495, by rfl⟩ : syracuseStep 771327 = 1156991) B1156991
theorem B2966905 : Blo 770335 2966905 := bstep (se 2 (by rfl) ⟨1112589, by rfl⟩ : syracuseStep 2966905 = 2225179) B2225179
theorem B771567 : Blo 770335 771567 := bstep (se 1 (by rfl) ⟨578675, by rfl⟩ : syracuseStep 771567 = 1157351) B1157351
theorem B771687 : Blo 770335 771687 := bstep (se 1 (by rfl) ⟨578765, by rfl⟩ : syracuseStep 771687 = 1157531) B1157531
theorem B772735 : Blo 770335 772735 := bstep (se 1 (by rfl) ⟨579551, by rfl⟩ : syracuseStep 772735 = 1159103) B1159103
theorem B773279 : Blo 770335 773279 := bstep (se 1 (by rfl) ⟨579959, by rfl⟩ : syracuseStep 773279 = 1159919) B1159919
theorem B773371 : Blo 770335 773371 := bstep (se 1 (by rfl) ⟨580028, by rfl⟩ : syracuseStep 773371 = 1160057) B1160057
theorem B774143 : Blo 770335 774143 := bstep (se 1 (by rfl) ⟨580607, by rfl⟩ : syracuseStep 774143 = 1161215) B1161215
theorem B1954631 : Blo 770335 1954631 := bstep (se 1 (by rfl) ⟨1465973, by rfl⟩ : syracuseStep 1954631 = 2931947) B2931947
theorem B2938463 : Blo 770335 2938463 := bstep (se 1 (by rfl) ⟨2203847, by rfl⟩ : syracuseStep 2938463 = 4407695) B4407695
theorem B28531739 : Blo 770335 28531739 := bstep (se 1 (by rfl) ⟨21398804, by rfl⟩ : syracuseStep 28531739 = 42797609) B42797609
theorem B17849983 : Blo 770335 17849983 := bstep (se 1 (by rfl) ⟨13387487, by rfl⟩ : syracuseStep 17849983 = 26774975) B26774975
theorem B9395945 : Blo 770335 9395945 := bstep (se 2 (by rfl) ⟨3523479, by rfl⟩ : syracuseStep 9395945 = 7046959) B7046959
theorem B1466687 : Blo 770335 1466687 := bstep (se 1 (by rfl) ⟨1100015, by rfl⟩ : syracuseStep 1466687 = 2200031) B2200031
theorem B5366569 : Blo 770335 5366569 := bstep (se 2 (by rfl) ⟨2012463, by rfl⟩ : syracuseStep 5366569 = 4024927) B4024927
theorem B1304201 : Blo 770335 1304201 := bstep (se 2 (by rfl) ⟨489075, by rfl⟩ : syracuseStep 1304201 = 978151) B978151
theorem B4943099 : Blo 770335 4943099 := bstep (se 1 (by rfl) ⟨3707324, by rfl⟩ : syracuseStep 4943099 = 7414649) B7414649
theorem B24998489 : Blo 770335 24998489 := bstep (se 2 (by rfl) ⟨9374433, by rfl⟩ : syracuseStep 24998489 = 18748867) B18748867
theorem B19036241 : Blo 770335 19036241 := bstep (se 2 (by rfl) ⟨7138590, by rfl⟩ : syracuseStep 19036241 = 14277181) B14277181
theorem B4389491 : Blo 770335 4389491 := bstep (se 1 (by rfl) ⟨3292118, by rfl⟩ : syracuseStep 4389491 = 6584237) B6584237
theorem B12680039 : Blo 770335 12680039 := bstep (se 1 (by rfl) ⟨9510029, by rfl⟩ : syracuseStep 12680039 = 19020059) B19020059
theorem B6263963 : Blo 770335 6263963 := bstep (se 1 (by rfl) ⟨4697972, by rfl⟩ : syracuseStep 6263963 = 9395945) B9395945
theorem B12690827 : Blo 770335 12690827 := bstep (se 1 (by rfl) ⟨9518120, by rfl⟩ : syracuseStep 12690827 = 19036241) B19036241
theorem B2926327 : Blo 770335 2926327 := bstep (se 1 (by rfl) ⟨2194745, by rfl⟩ : syracuseStep 2926327 = 4389491) B4389491
theorem B23799977 : Blo 770335 23799977 := bstep (se 2 (by rfl) ⟨8924991, by rfl⟩ : syracuseStep 23799977 = 17849983) B17849983
theorem B3911165 : Blo 770335 3911165 := bstep (se 3 (by rfl) ⟨733343, by rfl⟩ : syracuseStep 3911165 = 1466687) B1466687
theorem B7155425 : Blo 770335 7155425 := bstep (se 2 (by rfl) ⟨2683284, by rfl⟩ : syracuseStep 7155425 = 5366569) B5366569
theorem B1159835 : Blo 770335 1159835 := bstep (se 1 (by rfl) ⟨869876, by rfl⟩ : syracuseStep 1159835 = 1739753) B1739753
theorem B1160807 : Blo 770335 1160807 := bstep (se 1 (by rfl) ⟨870605, by rfl⟩ : syracuseStep 1160807 = 1741211) B1741211
theorem B19021159 : Blo 770335 19021159 := bstep (se 1 (by rfl) ⟨14265869, by rfl⟩ : syracuseStep 19021159 = 28531739) B28531739
theorem B19774853 : Blo 770335 19774853 := bstep (se 4 (by rfl) ⟨1853892, by rfl⟩ : syracuseStep 19774853 = 3707785) B3707785
theorem B770815 : Blo 770335 770815 := bstep (se 1 (by rfl) ⟨578111, by rfl⟩ : syracuseStep 770815 = 1156223) B1156223
theorem B869467 : Blo 770335 869467 := bstep (se 1 (by rfl) ⟨652100, by rfl⟩ : syracuseStep 869467 = 1304201) B1304201
theorem B771867 : Blo 770335 771867 := bstep (se 1 (by rfl) ⟨578900, by rfl⟩ : syracuseStep 771867 = 1157801) B1157801
theorem B3295399 : Blo 770335 3295399 := bstep (se 1 (by rfl) ⟨2471549, by rfl⟩ : syracuseStep 3295399 = 4943099) B4943099
theorem B16665659 : Blo 770335 16665659 := bstep (se 1 (by rfl) ⟨12499244, by rfl⟩ : syracuseStep 16665659 = 24998489) B24998489
theorem B773979 : Blo 770335 773979 := bstep (se 1 (by rfl) ⟨580484, by rfl⟩ : syracuseStep 773979 = 1160969) B1160969
theorem B9918287 : Blo 770335 9918287 := bstep (se 1 (by rfl) ⟨7438715, by rfl⟩ : syracuseStep 9918287 = 14877431) B14877431
theorem B3955169 : Blo 770335 3955169 := bstep (se 2 (by rfl) ⟨1483188, by rfl⟩ : syracuseStep 3955169 = 2966377) B2966377
theorem B3955873 : Blo 770335 3955873 := bstep (se 2 (by rfl) ⟨1483452, by rfl⟩ : syracuseStep 3955873 = 2966905) B2966905
theorem B1303087 : Blo 770335 1303087 := bstep (se 1 (by rfl) ⟨977315, by rfl⟩ : syracuseStep 1303087 = 1954631) B1954631
theorem B1958975 : Blo 770335 1958975 := bstep (se 1 (by rfl) ⟨1469231, by rfl⟩ : syracuseStep 1958975 = 2938463) B2938463
theorem B3302507 : Blo 770335 3302507 := bstep (se 1 (by rfl) ⟨2476880, by rfl⟩ : syracuseStep 3302507 = 4953761) B4953761
theorem B8453359 : Blo 770335 8453359 := bstep (se 1 (by rfl) ⟨6340019, by rfl⟩ : syracuseStep 8453359 = 12680039) B12680039
theorem B1735955 : Blo 770335 1735955 := bstep (se 1 (by rfl) ⟨1301966, by rfl⟩ : syracuseStep 1735955 = 2603933) B2603933
theorem B1737449 : Blo 770335 1737449 := bstep (se 2 (by rfl) ⟨651543, by rfl⟩ : syracuseStep 1737449 = 1303087) B1303087
theorem B11110439 : Blo 770335 11110439 := bstep (se 1 (by rfl) ⟨8332829, by rfl⟩ : syracuseStep 11110439 = 16665659) B16665659
theorem B3901769 : Blo 770335 3901769 := bstep (se 2 (by rfl) ⟨1463163, by rfl⟩ : syracuseStep 3901769 = 2926327) B2926327
theorem B4393865 : Blo 770335 4393865 := bstep (se 2 (by rfl) ⟨1647699, by rfl⟩ : syracuseStep 4393865 = 3295399) B3295399
theorem B2201671 : Blo 770335 2201671 := bstep (se 1 (by rfl) ⟨1651253, by rfl⟩ : syracuseStep 2201671 = 3302507) B3302507
theorem B8460551 : Blo 770335 8460551 := bstep (se 1 (by rfl) ⟨6345413, by rfl⟩ : syracuseStep 8460551 = 12690827) B12690827
theorem B15866651 : Blo 770335 15866651 := bstep (se 1 (by rfl) ⟨11899988, by rfl⟩ : syracuseStep 15866651 = 23799977) B23799977
theorem B1157303 : Blo 770335 1157303 := bstep (se 1 (by rfl) ⟨867977, by rfl⟩ : syracuseStep 1157303 = 1735955) B1735955
theorem B13183235 : Blo 770335 13183235 := bstep (se 1 (by rfl) ⟨9887426, by rfl⟩ : syracuseStep 13183235 = 19774853) B19774853
theorem B1159289 : Blo 770335 1159289 := bstep (se 2 (by rfl) ⟨434733, by rfl⟩ : syracuseStep 1159289 = 869467) B869467
theorem B4175975 : Blo 770335 4175975 := bstep (se 1 (by rfl) ⟨3131981, by rfl⟩ : syracuseStep 4175975 = 6263963) B6263963
theorem B2607443 : Blo 770335 2607443 := bstep (se 1 (by rfl) ⟨1955582, by rfl⟩ : syracuseStep 2607443 = 3911165) B3911165
theorem B4770283 : Blo 770335 4770283 := bstep (se 1 (by rfl) ⟨3577712, by rfl⟩ : syracuseStep 4770283 = 7155425) B7155425
theorem B773223 : Blo 770335 773223 := bstep (se 1 (by rfl) ⟨579917, by rfl⟩ : syracuseStep 773223 = 1159835) B1159835
theorem B773871 : Blo 770335 773871 := bstep (se 1 (by rfl) ⟨580403, by rfl⟩ : syracuseStep 773871 = 1160807) B1160807
theorem B6612191 : Blo 770335 6612191 := bstep (se 1 (by rfl) ⟨4959143, by rfl⟩ : syracuseStep 6612191 = 9918287) B9918287
theorem B1305983 : Blo 770335 1305983 := bstep (se 1 (by rfl) ⟨979487, by rfl⟩ : syracuseStep 1305983 = 1958975) B1958975
theorem B10547117 : Blo 770335 10547117 := bstep (se 3 (by rfl) ⟨1977584, by rfl⟩ : syracuseStep 10547117 = 3955169) B3955169
theorem B101446181 : Blo 770335 101446181 := bstep (se 4 (by rfl) ⟨9510579, by rfl⟩ : syracuseStep 101446181 = 19021159) B19021159
theorem B5274497 : Blo 770335 5274497 := bstep (se 2 (by rfl) ⟨1977936, by rfl⟩ : syracuseStep 5274497 = 3955873) B3955873
theorem B11271145 : Blo 770335 11271145 := bstep (se 2 (by rfl) ⟨4226679, by rfl⟩ : syracuseStep 11271145 = 8453359) B8453359
theorem B7406959 : Blo 770335 7406959 := bstep (se 1 (by rfl) ⟨5555219, by rfl⟩ : syracuseStep 7406959 = 11110439) B11110439
theorem B1738295 : Blo 770335 1738295 := bstep (se 1 (by rfl) ⟨1303721, by rfl⟩ : syracuseStep 1738295 = 2607443) B2607443
theorem B6360377 : Blo 770335 6360377 := bstep (se 2 (by rfl) ⟨2385141, by rfl⟩ : syracuseStep 6360377 = 4770283) B4770283
theorem B5640367 : Blo 770335 5640367 := bstep (se 1 (by rfl) ⟨4230275, by rfl⟩ : syracuseStep 5640367 = 8460551) B8460551
theorem B8788823 : Blo 770335 8788823 := bstep (se 1 (by rfl) ⟨6591617, by rfl⟩ : syracuseStep 8788823 = 13183235) B13183235
theorem B42311069 : Blo 770335 42311069 := bstep (se 3 (by rfl) ⟨7933325, by rfl⟩ : syracuseStep 42311069 = 15866651) B15866651
theorem B3516331 : Blo 770335 3516331 := bstep (se 1 (by rfl) ⟨2637248, by rfl⟩ : syracuseStep 3516331 = 5274497) B5274497
theorem B1158299 : Blo 770335 1158299 := bstep (se 1 (by rfl) ⟨868724, by rfl⟩ : syracuseStep 1158299 = 1737449) B1737449
theorem B2601179 : Blo 770335 2601179 := bstep (se 1 (by rfl) ⟨1950884, by rfl⟩ : syracuseStep 2601179 = 3901769) B3901769
theorem B2929243 : Blo 770335 2929243 := bstep (se 1 (by rfl) ⟨2196932, by rfl⟩ : syracuseStep 2929243 = 4393865) B4393865
theorem B4408127 : Blo 770335 4408127 := bstep (se 1 (by rfl) ⟨3306095, by rfl⟩ : syracuseStep 4408127 = 6612191) B6612191
theorem B771535 : Blo 770335 771535 := bstep (se 1 (by rfl) ⟨578651, by rfl⟩ : syracuseStep 771535 = 1157303) B1157303
theorem B870655 : Blo 770335 870655 := bstep (se 1 (by rfl) ⟨652991, by rfl⟩ : syracuseStep 870655 = 1305983) B1305983
theorem B7031411 : Blo 770335 7031411 := bstep (se 1 (by rfl) ⟨5273558, by rfl⟩ : syracuseStep 7031411 = 10547117) B10547117
theorem B772859 : Blo 770335 772859 := bstep (se 1 (by rfl) ⟨579644, by rfl⟩ : syracuseStep 772859 = 1159289) B1159289
theorem B2935561 : Blo 770335 2935561 := bstep (se 2 (by rfl) ⟨1100835, by rfl⟩ : syracuseStep 2935561 = 2201671) B2201671
theorem B15028193 : Blo 770335 15028193 := bstep (se 2 (by rfl) ⟨5635572, by rfl⟩ : syracuseStep 15028193 = 11271145) B11271145
theorem B67630787 : Blo 770335 67630787 := bstep (se 1 (by rfl) ⟨50723090, by rfl⟩ : syracuseStep 67630787 = 101446181) B101446181
theorem B2783983 : Blo 770335 2783983 := bstep (se 1 (by rfl) ⟨2087987, by rfl⟩ : syracuseStep 2783983 = 4175975) B4175975
theorem B4687607 : Blo 770335 4687607 := bstep (se 1 (by rfl) ⟨3515705, by rfl⟩ : syracuseStep 4687607 = 7031411) B7031411
theorem B4688441 : Blo 770335 4688441 := bstep (se 2 (by rfl) ⟨1758165, by rfl⟩ : syracuseStep 4688441 = 3516331) B3516331
theorem B3905657 : Blo 770335 3905657 := bstep (se 2 (by rfl) ⟨1464621, by rfl⟩ : syracuseStep 3905657 = 2929243) B2929243
theorem B3711977 : Blo 770335 3711977 := bstep (se 2 (by rfl) ⟨1391991, by rfl⟩ : syracuseStep 3711977 = 2783983) B2783983
theorem B1158863 : Blo 770335 1158863 := bstep (se 1 (by rfl) ⟨869147, by rfl⟩ : syracuseStep 1158863 = 1738295) B1738295
theorem B9875945 : Blo 770335 9875945 := bstep (se 2 (by rfl) ⟨3703479, by rfl⟩ : syracuseStep 9875945 = 7406959) B7406959
theorem B1160873 : Blo 770335 1160873 := bstep (se 2 (by rfl) ⟨435327, by rfl⟩ : syracuseStep 1160873 = 870655) B870655
theorem B3914081 : Blo 770335 3914081 := bstep (se 2 (by rfl) ⟨1467780, by rfl⟩ : syracuseStep 3914081 = 2935561) B2935561
theorem B7520489 : Blo 770335 7520489 := bstep (se 2 (by rfl) ⟨2820183, by rfl⟩ : syracuseStep 7520489 = 5640367) B5640367
theorem B772199 : Blo 770335 772199 := bstep (se 1 (by rfl) ⟨579149, by rfl⟩ : syracuseStep 772199 = 1158299) B1158299
theorem B16961005 : Blo 770335 16961005 := bstep (se 3 (by rfl) ⟨3180188, by rfl⟩ : syracuseStep 16961005 = 6360377) B6360377
theorem B2938751 : Blo 770335 2938751 := bstep (se 1 (by rfl) ⟨2204063, by rfl⟩ : syracuseStep 2938751 = 4408127) B4408127
theorem B5859215 : Blo 770335 5859215 := bstep (se 1 (by rfl) ⟨4394411, by rfl⟩ : syracuseStep 5859215 = 8788823) B8788823
theorem B28207379 : Blo 770335 28207379 := bstep (se 1 (by rfl) ⟨21155534, by rfl⟩ : syracuseStep 28207379 = 42311069) B42311069
theorem B1734119 : Blo 770335 1734119 := bstep (se 1 (by rfl) ⟨1300589, by rfl⟩ : syracuseStep 1734119 = 2601179) B2601179
theorem B45087191 : Blo 770335 45087191 := bstep (se 1 (by rfl) ⟨33815393, by rfl⟩ : syracuseStep 45087191 = 67630787) B67630787
theorem B40075181 : Blo 770335 40075181 := bstep (se 3 (by rfl) ⟨7514096, by rfl⟩ : syracuseStep 40075181 = 15028193) B15028193
theorem B5013659 : Blo 770335 5013659 := bstep (se 1 (by rfl) ⟨3760244, by rfl⟩ : syracuseStep 5013659 = 7520489) B7520489
theorem B3906143 : Blo 770335 3906143 := bstep (se 1 (by rfl) ⟨2929607, by rfl⟩ : syracuseStep 3906143 = 5859215) B5859215
theorem B1156079 : Blo 770335 1156079 := bstep (se 1 (by rfl) ⟨867059, by rfl⟩ : syracuseStep 1156079 = 1734119) B1734119
theorem B30058127 : Blo 770335 30058127 := bstep (se 1 (by rfl) ⟨22543595, by rfl⟩ : syracuseStep 30058127 = 45087191) B45087191
theorem B26716787 : Blo 770335 26716787 := bstep (se 1 (by rfl) ⟨20037590, by rfl⟩ : syracuseStep 26716787 = 40075181) B40075181
theorem B3125071 : Blo 770335 3125071 := bstep (se 1 (by rfl) ⟨2343803, by rfl⟩ : syracuseStep 3125071 = 4687607) B4687607
theorem B3125627 : Blo 770335 3125627 := bstep (se 1 (by rfl) ⟨2344220, by rfl⟩ : syracuseStep 3125627 = 4688441) B4688441
theorem B2603771 : Blo 770335 2603771 := bstep (se 1 (by rfl) ⟨1952828, by rfl⟩ : syracuseStep 2603771 = 3905657) B3905657
theorem B2474651 : Blo 770335 2474651 := bstep (se 1 (by rfl) ⟨1855988, by rfl⟩ : syracuseStep 2474651 = 3711977) B3711977
theorem B772575 : Blo 770335 772575 := bstep (se 1 (by rfl) ⟨579431, by rfl⟩ : syracuseStep 772575 = 1158863) B1158863
theorem B90458693 : Blo 770335 90458693 := bstep (se 4 (by rfl) ⟨8480502, by rfl⟩ : syracuseStep 90458693 = 16961005) B16961005
theorem B773915 : Blo 770335 773915 := bstep (se 1 (by rfl) ⟨580436, by rfl⟩ : syracuseStep 773915 = 1160873) B1160873
theorem B2609387 : Blo 770335 2609387 := bstep (se 1 (by rfl) ⟨1957040, by rfl⟩ : syracuseStep 2609387 = 3914081) B3914081
theorem B1959167 : Blo 770335 1959167 := bstep (se 1 (by rfl) ⟨1469375, by rfl⟩ : syracuseStep 1959167 = 2938751) B2938751
theorem B18804919 : Blo 770335 18804919 := bstep (se 1 (by rfl) ⟨14103689, by rfl⟩ : syracuseStep 18804919 = 28207379) B28207379
theorem B6583963 : Blo 770335 6583963 := bstep (se 1 (by rfl) ⟨4937972, by rfl⟩ : syracuseStep 6583963 = 9875945) B9875945
theorem B3342439 : Blo 770335 3342439 := bstep (se 1 (by rfl) ⟨2506829, by rfl⟩ : syracuseStep 3342439 = 5013659) B5013659
theorem B1739591 : Blo 770335 1739591 := bstep (se 1 (by rfl) ⟨1304693, by rfl⟩ : syracuseStep 1739591 = 2609387) B2609387
theorem B25073225 : Blo 770335 25073225 := bstep (se 2 (by rfl) ⟨9402459, by rfl⟩ : syracuseStep 25073225 = 18804919) B18804919
theorem B60305795 : Blo 770335 60305795 := bstep (se 1 (by rfl) ⟨45229346, by rfl⟩ : syracuseStep 60305795 = 90458693) B90458693
theorem B6599069 : Blo 770335 6599069 := bstep (se 3 (by rfl) ⟨1237325, by rfl⟩ : syracuseStep 6599069 = 2474651) B2474651
theorem B2604095 : Blo 770335 2604095 := bstep (se 1 (by rfl) ⟨1953071, by rfl⟩ : syracuseStep 2604095 = 3906143) B3906143
theorem B770719 : Blo 770335 770719 := bstep (se 1 (by rfl) ⟨578039, by rfl⟩ : syracuseStep 770719 = 1156079) B1156079
theorem B20038751 : Blo 770335 20038751 := bstep (se 1 (by rfl) ⟨15029063, by rfl⟩ : syracuseStep 20038751 = 30058127) B30058127
theorem B17811191 : Blo 770335 17811191 := bstep (se 1 (by rfl) ⟨13358393, by rfl⟩ : syracuseStep 17811191 = 26716787) B26716787
theorem B2083751 : Blo 770335 2083751 := bstep (se 1 (by rfl) ⟨1562813, by rfl⟩ : syracuseStep 2083751 = 3125627) B3125627
theorem B16667045 : Blo 770335 16667045 := bstep (se 4 (by rfl) ⟨1562535, by rfl⟩ : syracuseStep 16667045 = 3125071) B3125071
theorem B1306111 : Blo 770335 1306111 := bstep (se 1 (by rfl) ⟨979583, by rfl⟩ : syracuseStep 1306111 = 1959167) B1959167
theorem B8778617 : Blo 770335 8778617 := bstep (se 2 (by rfl) ⟨3291981, by rfl⟩ : syracuseStep 8778617 = 6583963) B6583963
theorem B1735847 : Blo 770335 1735847 := bstep (se 1 (by rfl) ⟨1301885, by rfl⟩ : syracuseStep 1735847 = 2603771) B2603771
theorem B4456585 : Blo 770335 4456585 := bstep (se 2 (by rfl) ⟨1671219, by rfl⟩ : syracuseStep 4456585 = 3342439) B3342439
theorem B11111363 : Blo 770335 11111363 := bstep (se 1 (by rfl) ⟨8333522, by rfl⟩ : syracuseStep 11111363 = 16667045) B16667045
theorem B16715483 : Blo 770335 16715483 := bstep (se 1 (by rfl) ⟨12536612, by rfl⟩ : syracuseStep 16715483 = 25073225) B25073225
theorem B1741481 : Blo 770335 1741481 := bstep (se 2 (by rfl) ⟨653055, by rfl⟩ : syracuseStep 1741481 = 1306111) B1306111
theorem B4399379 : Blo 770335 4399379 := bstep (se 1 (by rfl) ⟨3299534, by rfl⟩ : syracuseStep 4399379 = 6599069) B6599069
theorem B1157231 : Blo 770335 1157231 := bstep (se 1 (by rfl) ⟨867923, by rfl⟩ : syracuseStep 1157231 = 1735847) B1735847
theorem B11874127 : Blo 770335 11874127 := bstep (se 1 (by rfl) ⟨8905595, by rfl⟩ : syracuseStep 11874127 = 17811191) B17811191
theorem B1159727 : Blo 770335 1159727 := bstep (se 1 (by rfl) ⟨869795, by rfl⟩ : syracuseStep 1159727 = 1739591) B1739591
theorem B1389167 : Blo 770335 1389167 := bstep (se 1 (by rfl) ⟨1041875, by rfl⟩ : syracuseStep 1389167 = 2083751) B2083751
theorem B5852411 : Blo 770335 5852411 := bstep (se 1 (by rfl) ⟨4389308, by rfl⟩ : syracuseStep 5852411 = 8778617) B8778617
theorem B13359167 : Blo 770335 13359167 := bstep (se 1 (by rfl) ⟨10019375, by rfl⟩ : syracuseStep 13359167 = 20038751) B20038751
theorem B40203863 : Blo 770335 40203863 := bstep (se 1 (by rfl) ⟨30152897, by rfl⟩ : syracuseStep 40203863 = 60305795) B60305795
theorem B1736063 : Blo 770335 1736063 := bstep (se 1 (by rfl) ⟨1302047, by rfl⟩ : syracuseStep 1736063 = 2604095) B2604095
theorem B7407575 : Blo 770335 7407575 := bstep (se 1 (by rfl) ⟨5555681, by rfl⟩ : syracuseStep 7407575 = 11111363) B11111363
theorem B3901607 : Blo 770335 3901607 := bstep (se 1 (by rfl) ⟨2926205, by rfl⟩ : syracuseStep 3901607 = 5852411) B5852411
theorem B11143655 : Blo 770335 11143655 := bstep (se 1 (by rfl) ⟨8357741, by rfl⟩ : syracuseStep 11143655 = 16715483) B16715483
theorem B15832169 : Blo 770335 15832169 := bstep (se 2 (by rfl) ⟨5937063, by rfl⟩ : syracuseStep 15832169 = 11874127) B11874127
theorem B926111 : Blo 770335 926111 := bstep (se 1 (by rfl) ⟨694583, by rfl⟩ : syracuseStep 926111 = 1389167) B1389167
theorem B1157375 : Blo 770335 1157375 := bstep (se 1 (by rfl) ⟨868031, by rfl⟩ : syracuseStep 1157375 = 1736063) B1736063
theorem B23768453 : Blo 770335 23768453 := bstep (se 4 (by rfl) ⟨2228292, by rfl⟩ : syracuseStep 23768453 = 4456585) B4456585
theorem B1160987 : Blo 770335 1160987 := bstep (se 1 (by rfl) ⟨870740, by rfl⟩ : syracuseStep 1160987 = 1741481) B1741481
theorem B2932919 : Blo 770335 2932919 := bstep (se 1 (by rfl) ⟨2199689, by rfl⟩ : syracuseStep 2932919 = 4399379) B4399379
theorem B771487 : Blo 770335 771487 := bstep (se 1 (by rfl) ⟨578615, by rfl⟩ : syracuseStep 771487 = 1157231) B1157231
theorem B773151 : Blo 770335 773151 := bstep (se 1 (by rfl) ⟨579863, by rfl⟩ : syracuseStep 773151 = 1159727) B1159727
theorem B8906111 : Blo 770335 8906111 := bstep (se 1 (by rfl) ⟨6679583, by rfl⟩ : syracuseStep 8906111 = 13359167) B13359167
theorem B26802575 : Blo 770335 26802575 := bstep (se 1 (by rfl) ⟨20101931, by rfl⟩ : syracuseStep 26802575 = 40203863) B40203863
theorem B10554779 : Blo 770335 10554779 := bstep (se 1 (by rfl) ⟨7916084, by rfl⟩ : syracuseStep 10554779 = 15832169) B15832169
theorem B5937407 : Blo 770335 5937407 := bstep (se 1 (by rfl) ⟨4453055, by rfl⟩ : syracuseStep 5937407 = 8906111) B8906111
theorem B17868383 : Blo 770335 17868383 := bstep (se 1 (by rfl) ⟨13401287, by rfl⟩ : syracuseStep 17868383 = 26802575) B26802575
theorem B2469629 : Blo 770335 2469629 := bstep (se 3 (by rfl) ⟨463055, by rfl⟩ : syracuseStep 2469629 = 926111) B926111
theorem B2601071 : Blo 770335 2601071 := bstep (se 1 (by rfl) ⟨1950803, by rfl⟩ : syracuseStep 2601071 = 3901607) B3901607
theorem B771583 : Blo 770335 771583 := bstep (se 1 (by rfl) ⟨578687, by rfl⟩ : syracuseStep 771583 = 1157375) B1157375
theorem B15845635 : Blo 770335 15845635 := bstep (se 1 (by rfl) ⟨11884226, by rfl⟩ : syracuseStep 15845635 = 23768453) B23768453
theorem B773991 : Blo 770335 773991 := bstep (se 1 (by rfl) ⟨580493, by rfl⟩ : syracuseStep 773991 = 1160987) B1160987
theorem B1955279 : Blo 770335 1955279 := bstep (se 1 (by rfl) ⟨1466459, by rfl⟩ : syracuseStep 1955279 = 2932919) B2932919
theorem B4938383 : Blo 770335 4938383 := bstep (se 1 (by rfl) ⟨3703787, by rfl⟩ : syracuseStep 4938383 = 7407575) B7407575
theorem B7429103 : Blo 770335 7429103 := bstep (se 1 (by rfl) ⟨5571827, by rfl⟩ : syracuseStep 7429103 = 11143655) B11143655
theorem B4952735 : Blo 770335 4952735 := bstep (se 1 (by rfl) ⟨3714551, by rfl⟩ : syracuseStep 4952735 = 7429103) B7429103
theorem B1646419 : Blo 770335 1646419 := bstep (se 1 (by rfl) ⟨1234814, by rfl⟩ : syracuseStep 1646419 = 2469629) B2469629
theorem B3292255 : Blo 770335 3292255 := bstep (se 1 (by rfl) ⟨2469191, by rfl⟩ : syracuseStep 3292255 = 4938383) B4938383
theorem B11912255 : Blo 770335 11912255 := bstep (se 1 (by rfl) ⟨8934191, by rfl⟩ : syracuseStep 11912255 = 17868383) B17868383
theorem B7036519 : Blo 770335 7036519 := bstep (se 1 (by rfl) ⟨5277389, by rfl⟩ : syracuseStep 7036519 = 10554779) B10554779
theorem B21127513 : Blo 770335 21127513 := bstep (se 2 (by rfl) ⟨7922817, by rfl⟩ : syracuseStep 21127513 = 15845635) B15845635
theorem B1303519 : Blo 770335 1303519 := bstep (se 1 (by rfl) ⟨977639, by rfl⟩ : syracuseStep 1303519 = 1955279) B1955279
theorem B3958271 : Blo 770335 3958271 := bstep (se 1 (by rfl) ⟨2968703, by rfl⟩ : syracuseStep 3958271 = 5937407) B5937407
theorem B1734047 : Blo 770335 1734047 := bstep (se 1 (by rfl) ⟨1300535, by rfl⟩ : syracuseStep 1734047 = 2601071) B2601071
theorem B1738025 : Blo 770335 1738025 := bstep (se 2 (by rfl) ⟨651759, by rfl⟩ : syracuseStep 1738025 = 1303519) B1303519
theorem B1156031 : Blo 770335 1156031 := bstep (se 1 (by rfl) ⟨867023, by rfl⟩ : syracuseStep 1156031 = 1734047) B1734047
theorem B9382025 : Blo 770335 9382025 := bstep (se 2 (by rfl) ⟨3518259, by rfl⟩ : syracuseStep 9382025 = 7036519) B7036519
theorem B7941503 : Blo 770335 7941503 := bstep (se 1 (by rfl) ⟨5956127, by rfl⟩ : syracuseStep 7941503 = 11912255) B11912255
theorem B2638847 : Blo 770335 2638847 := bstep (se 1 (by rfl) ⟨1979135, by rfl⟩ : syracuseStep 2638847 = 3958271) B3958271
theorem B28170017 : Blo 770335 28170017 := bstep (se 2 (by rfl) ⟨10563756, by rfl⟩ : syracuseStep 28170017 = 21127513) B21127513
theorem B3301823 : Blo 770335 3301823 := bstep (se 1 (by rfl) ⟨2476367, by rfl⟩ : syracuseStep 3301823 = 4952735) B4952735
theorem B4389673 : Blo 770335 4389673 := bstep (se 2 (by rfl) ⟨1646127, by rfl⟩ : syracuseStep 4389673 = 3292255) B3292255
theorem B2195225 : Blo 770335 2195225 := bstep (se 2 (by rfl) ⟨823209, by rfl⟩ : syracuseStep 2195225 = 1646419) B1646419
theorem B18780011 : Blo 770335 18780011 := bstep (se 1 (by rfl) ⟨14085008, by rfl⟩ : syracuseStep 18780011 = 28170017) B28170017
theorem B1158683 : Blo 770335 1158683 := bstep (se 1 (by rfl) ⟨869012, by rfl⟩ : syracuseStep 1158683 = 1738025) B1738025
theorem B25018733 : Blo 770335 25018733 := bstep (se 3 (by rfl) ⟨4691012, by rfl⟩ : syracuseStep 25018733 = 9382025) B9382025
theorem B770687 : Blo 770335 770687 := bstep (se 1 (by rfl) ⟨578015, by rfl⟩ : syracuseStep 770687 = 1156031) B1156031
theorem B5294335 : Blo 770335 5294335 := bstep (se 1 (by rfl) ⟨3970751, by rfl⟩ : syracuseStep 5294335 = 7941503) B7941503
theorem B5852897 : Blo 770335 5852897 := bstep (se 2 (by rfl) ⟨2194836, by rfl⟩ : syracuseStep 5852897 = 4389673) B4389673
theorem B1463483 : Blo 770335 1463483 := bstep (se 1 (by rfl) ⟨1097612, by rfl⟩ : syracuseStep 1463483 = 2195225) B2195225
theorem B1759231 : Blo 770335 1759231 := bstep (se 1 (by rfl) ⟨1319423, by rfl⟩ : syracuseStep 1759231 = 2638847) B2638847
theorem B8804861 : Blo 770335 8804861 := bstep (se 3 (by rfl) ⟨1650911, by rfl⟩ : syracuseStep 8804861 = 3301823) B3301823
theorem B16679155 : Blo 770335 16679155 := bstep (se 1 (by rfl) ⟨12509366, by rfl⟩ : syracuseStep 16679155 = 25018733) B25018733
theorem B3901931 : Blo 770335 3901931 := bstep (se 1 (by rfl) ⟨2926448, by rfl⟩ : syracuseStep 3901931 = 5852897) B5852897
theorem B12520007 : Blo 770335 12520007 := bstep (se 1 (by rfl) ⟨9390005, by rfl⟩ : syracuseStep 12520007 = 18780011) B18780011
theorem B5869907 : Blo 770335 5869907 := bstep (se 1 (by rfl) ⟨4402430, by rfl⟩ : syracuseStep 5869907 = 8804861) B8804861
theorem B7059113 : Blo 770335 7059113 := bstep (se 2 (by rfl) ⟨2647167, by rfl⟩ : syracuseStep 7059113 = 5294335) B5294335
theorem B772455 : Blo 770335 772455 := bstep (se 1 (by rfl) ⟨579341, by rfl⟩ : syracuseStep 772455 = 1158683) B1158683
theorem B2345641 : Blo 770335 2345641 := bstep (se 2 (by rfl) ⟨879615, by rfl⟩ : syracuseStep 2345641 = 1759231) B1759231
theorem B975655 : Blo 770335 975655 := bstep (se 1 (by rfl) ⟨731741, by rfl⟩ : syracuseStep 975655 = 1463483) B1463483
theorem B2601287 : Blo 770335 2601287 := bstep (se 1 (by rfl) ⟨1950965, by rfl⟩ : syracuseStep 2601287 = 3901931) B3901931
theorem B3913271 : Blo 770335 3913271 := bstep (se 1 (by rfl) ⟨2934953, by rfl⟩ : syracuseStep 3913271 = 5869907) B5869907
theorem B4706075 : Blo 770335 4706075 := bstep (se 1 (by rfl) ⟨3529556, by rfl⟩ : syracuseStep 4706075 = 7059113) B7059113
theorem B22238873 : Blo 770335 22238873 := bstep (se 2 (by rfl) ⟨8339577, by rfl⟩ : syracuseStep 22238873 = 16679155) B16679155
theorem B1300873 : Blo 770335 1300873 := bstep (se 2 (by rfl) ⟨487827, by rfl⟩ : syracuseStep 1300873 = 975655) B975655
theorem B8346671 : Blo 770335 8346671 := bstep (se 1 (by rfl) ⟨6260003, by rfl⟩ : syracuseStep 8346671 = 12520007) B12520007
theorem B12510085 : Blo 770335 12510085 := bstep (se 4 (by rfl) ⟨1172820, by rfl⟩ : syracuseStep 12510085 = 2345641) B2345641
theorem B16680113 : Blo 770335 16680113 := bstep (se 2 (by rfl) ⟨6255042, by rfl⟩ : syracuseStep 16680113 = 12510085) B12510085
theorem B14825915 : Blo 770335 14825915 := bstep (se 1 (by rfl) ⟨11119436, by rfl⟩ : syracuseStep 14825915 = 22238873) B22238873
theorem B2608847 : Blo 770335 2608847 := bstep (se 1 (by rfl) ⟨1956635, by rfl⟩ : syracuseStep 2608847 = 3913271) B3913271
theorem B3137383 : Blo 770335 3137383 := bstep (se 1 (by rfl) ⟨2353037, by rfl⟩ : syracuseStep 3137383 = 4706075) B4706075
theorem B5564447 : Blo 770335 5564447 := bstep (se 1 (by rfl) ⟨4173335, by rfl⟩ : syracuseStep 5564447 = 8346671) B8346671
theorem B1734191 : Blo 770335 1734191 := bstep (se 1 (by rfl) ⟨1300643, by rfl⟩ : syracuseStep 1734191 = 2601287) B2601287
theorem B1734497 : Blo 770335 1734497 := bstep (se 2 (by rfl) ⟨650436, by rfl⟩ : syracuseStep 1734497 = 1300873) B1300873
theorem B1739231 : Blo 770335 1739231 := bstep (se 1 (by rfl) ⟨1304423, by rfl⟩ : syracuseStep 1739231 = 2608847) B2608847
theorem B3709631 : Blo 770335 3709631 := bstep (se 1 (by rfl) ⟨2782223, by rfl⟩ : syracuseStep 3709631 = 5564447) B5564447
theorem B1156127 : Blo 770335 1156127 := bstep (se 1 (by rfl) ⟨867095, by rfl⟩ : syracuseStep 1156127 = 1734191) B1734191
theorem B1156331 : Blo 770335 1156331 := bstep (se 1 (by rfl) ⟨867248, by rfl⟩ : syracuseStep 1156331 = 1734497) B1734497
theorem B11120075 : Blo 770335 11120075 := bstep (se 1 (by rfl) ⟨8340056, by rfl⟩ : syracuseStep 11120075 = 16680113) B16680113
theorem B9883943 : Blo 770335 9883943 := bstep (se 1 (by rfl) ⟨7412957, by rfl⟩ : syracuseStep 9883943 = 14825915) B14825915
theorem B4183177 : Blo 770335 4183177 := bstep (se 2 (by rfl) ⟨1568691, by rfl⟩ : syracuseStep 4183177 = 3137383) B3137383
theorem B6589295 : Blo 770335 6589295 := bstep (se 1 (by rfl) ⟨4941971, by rfl⟩ : syracuseStep 6589295 = 9883943) B9883943
theorem B5577569 : Blo 770335 5577569 := bstep (se 2 (by rfl) ⟨2091588, by rfl⟩ : syracuseStep 5577569 = 4183177) B4183177
theorem B7413383 : Blo 770335 7413383 := bstep (se 1 (by rfl) ⟨5560037, by rfl⟩ : syracuseStep 7413383 = 11120075) B11120075
theorem B1159487 : Blo 770335 1159487 := bstep (se 1 (by rfl) ⟨869615, by rfl⟩ : syracuseStep 1159487 = 1739231) B1739231
theorem B2473087 : Blo 770335 2473087 := bstep (se 1 (by rfl) ⟨1854815, by rfl⟩ : syracuseStep 2473087 = 3709631) B3709631
theorem B770751 : Blo 770335 770751 := bstep (se 1 (by rfl) ⟨578063, by rfl⟩ : syracuseStep 770751 = 1156127) B1156127
theorem B770887 : Blo 770335 770887 := bstep (se 1 (by rfl) ⟨578165, by rfl⟩ : syracuseStep 770887 = 1156331) B1156331
theorem B4392863 : Blo 770335 4392863 := bstep (se 1 (by rfl) ⟨3294647, by rfl⟩ : syracuseStep 4392863 = 6589295) B6589295
theorem B3718379 : Blo 770335 3718379 := bstep (se 1 (by rfl) ⟨2788784, by rfl⟩ : syracuseStep 3718379 = 5577569) B5577569
theorem B772991 : Blo 770335 772991 := bstep (se 1 (by rfl) ⟨579743, by rfl⟩ : syracuseStep 772991 = 1159487) B1159487
theorem B3297449 : Blo 770335 3297449 := bstep (se 2 (by rfl) ⟨1236543, by rfl⟩ : syracuseStep 3297449 = 2473087) B2473087
theorem B4942255 : Blo 770335 4942255 := bstep (se 1 (by rfl) ⟨3706691, by rfl⟩ : syracuseStep 4942255 = 7413383) B7413383
theorem B6589673 : Blo 770335 6589673 := bstep (se 2 (by rfl) ⟨2471127, by rfl⟩ : syracuseStep 6589673 = 4942255) B4942255
theorem B8793197 : Blo 770335 8793197 := bstep (se 3 (by rfl) ⟨1648724, by rfl⟩ : syracuseStep 8793197 = 3297449) B3297449
theorem B2928575 : Blo 770335 2928575 := bstep (se 1 (by rfl) ⟨2196431, by rfl⟩ : syracuseStep 2928575 = 4392863) B4392863
theorem B2478919 : Blo 770335 2478919 := bstep (se 1 (by rfl) ⟨1859189, by rfl⟩ : syracuseStep 2478919 = 3718379) B3718379
theorem B4393115 : Blo 770335 4393115 := bstep (se 1 (by rfl) ⟨3294836, by rfl⟩ : syracuseStep 4393115 = 6589673) B6589673
theorem B1952383 : Blo 770335 1952383 := bstep (se 1 (by rfl) ⟨1464287, by rfl⟩ : syracuseStep 1952383 = 2928575) B2928575
theorem B3305225 : Blo 770335 3305225 := bstep (se 2 (by rfl) ⟨1239459, by rfl⟩ : syracuseStep 3305225 = 2478919) B2478919
theorem B5862131 : Blo 770335 5862131 := bstep (se 1 (by rfl) ⟨4396598, by rfl⟩ : syracuseStep 5862131 = 8793197) B8793197
theorem B2203483 : Blo 770335 2203483 := bstep (se 1 (by rfl) ⟨1652612, by rfl⟩ : syracuseStep 2203483 = 3305225) B3305225
theorem B3908087 : Blo 770335 3908087 := bstep (se 1 (by rfl) ⟨2931065, by rfl⟩ : syracuseStep 3908087 = 5862131) B5862131
theorem B2928743 : Blo 770335 2928743 := bstep (se 1 (by rfl) ⟨2196557, by rfl⟩ : syracuseStep 2928743 = 4393115) B4393115
theorem B2603177 : Blo 770335 2603177 := bstep (se 2 (by rfl) ⟨976191, by rfl⟩ : syracuseStep 2603177 = 1952383) B1952383
theorem B2605391 : Blo 770335 2605391 := bstep (se 1 (by rfl) ⟨1954043, by rfl⟩ : syracuseStep 2605391 = 3908087) B3908087
theorem B1952495 : Blo 770335 1952495 := bstep (se 1 (by rfl) ⟨1464371, by rfl⟩ : syracuseStep 1952495 = 2928743) B2928743
theorem B2937977 : Blo 770335 2937977 := bstep (se 2 (by rfl) ⟨1101741, by rfl⟩ : syracuseStep 2937977 = 2203483) B2203483
theorem B1735451 : Blo 770335 1735451 := bstep (se 1 (by rfl) ⟨1301588, by rfl⟩ : syracuseStep 1735451 = 2603177) B2603177
theorem B1736927 : Blo 770335 1736927 := bstep (se 1 (by rfl) ⟨1302695, by rfl⟩ : syracuseStep 1736927 = 2605391) B2605391
theorem B1156967 : Blo 770335 1156967 := bstep (se 1 (by rfl) ⟨867725, by rfl⟩ : syracuseStep 1156967 = 1735451) B1735451
theorem B1301663 : Blo 770335 1301663 := bstep (se 1 (by rfl) ⟨976247, by rfl⟩ : syracuseStep 1301663 = 1952495) B1952495
theorem B1958651 : Blo 770335 1958651 := bstep (se 1 (by rfl) ⟨1468988, by rfl⟩ : syracuseStep 1958651 = 2937977) B2937977
theorem B1157951 : Blo 770335 1157951 := bstep (se 1 (by rfl) ⟨868463, by rfl⟩ : syracuseStep 1157951 = 1736927) B1736927
theorem B867775 : Blo 770335 867775 := bstep (se 1 (by rfl) ⟨650831, by rfl⟩ : syracuseStep 867775 = 1301663) B1301663
theorem B771311 : Blo 770335 771311 := bstep (se 1 (by rfl) ⟨578483, by rfl⟩ : syracuseStep 771311 = 1156967) B1156967
theorem B1305767 : Blo 770335 1305767 := bstep (se 1 (by rfl) ⟨979325, by rfl⟩ : syracuseStep 1305767 = 1958651) B1958651
theorem B1157033 : Blo 770335 1157033 := bstep (se 2 (by rfl) ⟨433887, by rfl⟩ : syracuseStep 1157033 = 867775) B867775
theorem B771967 : Blo 770335 771967 := bstep (se 1 (by rfl) ⟨578975, by rfl⟩ : syracuseStep 771967 = 1157951) B1157951
theorem B870511 : Blo 770335 870511 := bstep (se 1 (by rfl) ⟨652883, by rfl⟩ : syracuseStep 870511 = 1305767) B1305767
theorem B1160681 : Blo 770335 1160681 := bstep (se 2 (by rfl) ⟨435255, by rfl⟩ : syracuseStep 1160681 = 870511) B870511
theorem B771355 : Blo 770335 771355 := bstep (se 1 (by rfl) ⟨578516, by rfl⟩ : syracuseStep 771355 = 1157033) B1157033
theorem B773787 : Blo 770335 773787 := bstep (se 1 (by rfl) ⟨580340, by rfl⟩ : syracuseStep 773787 = 1160681) B1160681

theorem C0 (j : ℕ) (h1 : 192583 ≤ j) (h2 : j ≤ 193282) : Blo 770335 (4 * j + 3) := by
  interval_cases j
  · exact B770335
  · exact B770339
  · exact B770343
  · exact B770347
  · exact B770351
  · exact B770355
  · exact B770359
  · exact B770363
  · exact B770367
  · exact B770371
  · exact B770375
  · exact B770379
  · exact B770383
  · exact B770387
  · exact B770391
  · exact B770395
  · exact B770399
  · exact B770403
  · exact B770407
  · exact B770411
  · exact B770415
  · exact B770419
  · exact B770423
  · exact B770427
  · exact B770431
  · exact B770435
  · exact B770439
  · exact B770443
  · exact B770447
  · exact B770451
  · exact B770455
  · exact B770459
  · exact B770463
  · exact B770467
  · exact B770471
  · exact B770475
  · exact B770479
  · exact B770483
  · exact B770487
  · exact B770491
  · exact B770495
  · exact B770499
  · exact B770503
  · exact B770507
  · exact B770511
  · exact B770515
  · exact B770519
  · exact B770523
  · exact B770527
  · exact B770531
  · exact B770535
  · exact B770539
  · exact B770543
  · exact B770547
  · exact B770551
  · exact B770555
  · exact B770559
  · exact B770563
  · exact B770567
  · exact B770571
  · exact B770575
  · exact B770579
  · exact B770583
  · exact B770587
  · exact B770591
  · exact B770595
  · exact B770599
  · exact B770603
  · exact B770607
  · exact B770611
  · exact B770615
  · exact B770619
  · exact B770623
  · exact B770627
  · exact B770631
  · exact B770635
  · exact B770639
  · exact B770643
  · exact B770647
  · exact B770651
  · exact B770655
  · exact B770659
  · exact B770663
  · exact B770667
  · exact B770671
  · exact B770675
  · exact B770679
  · exact B770683
  · exact B770687
  · exact B770691
  · exact B770695
  · exact B770699
  · exact B770703
  · exact B770707
  · exact B770711
  · exact B770715
  · exact B770719
  · exact B770723
  · exact B770727
  · exact B770731
  · exact B770735
  · exact B770739
  · exact B770743
  · exact B770747
  · exact B770751
  · exact B770755
  · exact B770759
  · exact B770763
  · exact B770767
  · exact B770771
  · exact B770775
  · exact B770779
  · exact B770783
  · exact B770787
  · exact B770791
  · exact B770795
  · exact B770799
  · exact B770803
  · exact B770807
  · exact B770811
  · exact B770815
  · exact B770819
  · exact B770823
  · exact B770827
  · exact B770831
  · exact B770835
  · exact B770839
  · exact B770843
  · exact B770847
  · exact B770851
  · exact B770855
  · exact B770859
  · exact B770863
  · exact B770867
  · exact B770871
  · exact B770875
  · exact B770879
  · exact B770883
  · exact B770887
  · exact B770891
  · exact B770895
  · exact B770899
  · exact B770903
  · exact B770907
  · exact B770911
  · exact B770915
  · exact B770919
  · exact B770923
  · exact B770927
  · exact B770931
  · exact B770935
  · exact B770939
  · exact B770943
  · exact B770947
  · exact B770951
  · exact B770955
  · exact B770959
  · exact B770963
  · exact B770967
  · exact B770971
  · exact B770975
  · exact B770979
  · exact B770983
  · exact B770987
  · exact B770991
  · exact B770995
  · exact B770999
  · exact B771003
  · exact B771007
  · exact B771011
  · exact B771015
  · exact B771019
  · exact B771023
  · exact B771027
  · exact B771031
  · exact B771035
  · exact B771039
  · exact B771043
  · exact B771047
  · exact B771051
  · exact B771055
  · exact B771059
  · exact B771063
  · exact B771067
  · exact B771071
  · exact B771075
  · exact B771079
  · exact B771083
  · exact B771087
  · exact B771091
  · exact B771095
  · exact B771099
  · exact B771103
  · exact B771107
  · exact B771111
  · exact B771115
  · exact B771119
  · exact B771123
  · exact B771127
  · exact B771131
  · exact B771135
  · exact B771139
  · exact B771143
  · exact B771147
  · exact B771151
  · exact B771155
  · exact B771159
  · exact B771163
  · exact B771167
  · exact B771171
  · exact B771175
  · exact B771179
  · exact B771183
  · exact B771187
  · exact B771191
  · exact B771195
  · exact B771199
  · exact B771203
  · exact B771207
  · exact B771211
  · exact B771215
  · exact B771219
  · exact B771223
  · exact B771227
  · exact B771231
  · exact B771235
  · exact B771239
  · exact B771243
  · exact B771247
  · exact B771251
  · exact B771255
  · exact B771259
  · exact B771263
  · exact B771267
  · exact B771271
  · exact B771275
  · exact B771279
  · exact B771283
  · exact B771287
  · exact B771291
  · exact B771295
  · exact B771299
  · exact B771303
  · exact B771307
  · exact B771311
  · exact B771315
  · exact B771319
  · exact B771323
  · exact B771327
  · exact B771331
  · exact B771335
  · exact B771339
  · exact B771343
  · exact B771347
  · exact B771351
  · exact B771355
  · exact B771359
  · exact B771363
  · exact B771367
  · exact B771371
  · exact B771375
  · exact B771379
  · exact B771383
  · exact B771387
  · exact B771391
  · exact B771395
  · exact B771399
  · exact B771403
  · exact B771407
  · exact B771411
  · exact B771415
  · exact B771419
  · exact B771423
  · exact B771427
  · exact B771431
  · exact B771435
  · exact B771439
  · exact B771443
  · exact B771447
  · exact B771451
  · exact B771455
  · exact B771459
  · exact B771463
  · exact B771467
  · exact B771471
  · exact B771475
  · exact B771479
  · exact B771483
  · exact B771487
  · exact B771491
  · exact B771495
  · exact B771499
  · exact B771503
  · exact B771507
  · exact B771511
  · exact B771515
  · exact B771519
  · exact B771523
  · exact B771527
  · exact B771531
  · exact B771535
  · exact B771539
  · exact B771543
  · exact B771547
  · exact B771551
  · exact B771555
  · exact B771559
  · exact B771563
  · exact B771567
  · exact B771571
  · exact B771575
  · exact B771579
  · exact B771583
  · exact B771587
  · exact B771591
  · exact B771595
  · exact B771599
  · exact B771603
  · exact B771607
  · exact B771611
  · exact B771615
  · exact B771619
  · exact B771623
  · exact B771627
  · exact B771631
  · exact B771635
  · exact B771639
  · exact B771643
  · exact B771647
  · exact B771651
  · exact B771655
  · exact B771659
  · exact B771663
  · exact B771667
  · exact B771671
  · exact B771675
  · exact B771679
  · exact B771683
  · exact B771687
  · exact B771691
  · exact B771695
  · exact B771699
  · exact B771703
  · exact B771707
  · exact B771711
  · exact B771715
  · exact B771719
  · exact B771723
  · exact B771727
  · exact B771731
  · exact B771735
  · exact B771739
  · exact B771743
  · exact B771747
  · exact B771751
  · exact B771755
  · exact B771759
  · exact B771763
  · exact B771767
  · exact B771771
  · exact B771775
  · exact B771779
  · exact B771783
  · exact B771787
  · exact B771791
  · exact B771795
  · exact B771799
  · exact B771803
  · exact B771807
  · exact B771811
  · exact B771815
  · exact B771819
  · exact B771823
  · exact B771827
  · exact B771831
  · exact B771835
  · exact B771839
  · exact B771843
  · exact B771847
  · exact B771851
  · exact B771855
  · exact B771859
  · exact B771863
  · exact B771867
  · exact B771871
  · exact B771875
  · exact B771879
  · exact B771883
  · exact B771887
  · exact B771891
  · exact B771895
  · exact B771899
  · exact B771903
  · exact B771907
  · exact B771911
  · exact B771915
  · exact B771919
  · exact B771923
  · exact B771927
  · exact B771931
  · exact B771935
  · exact B771939
  · exact B771943
  · exact B771947
  · exact B771951
  · exact B771955
  · exact B771959
  · exact B771963
  · exact B771967
  · exact B771971
  · exact B771975
  · exact B771979
  · exact B771983
  · exact B771987
  · exact B771991
  · exact B771995
  · exact B771999
  · exact B772003
  · exact B772007
  · exact B772011
  · exact B772015
  · exact B772019
  · exact B772023
  · exact B772027
  · exact B772031
  · exact B772035
  · exact B772039
  · exact B772043
  · exact B772047
  · exact B772051
  · exact B772055
  · exact B772059
  · exact B772063
  · exact B772067
  · exact B772071
  · exact B772075
  · exact B772079
  · exact B772083
  · exact B772087
  · exact B772091
  · exact B772095
  · exact B772099
  · exact B772103
  · exact B772107
  · exact B772111
  · exact B772115
  · exact B772119
  · exact B772123
  · exact B772127
  · exact B772131
  · exact B772135
  · exact B772139
  · exact B772143
  · exact B772147
  · exact B772151
  · exact B772155
  · exact B772159
  · exact B772163
  · exact B772167
  · exact B772171
  · exact B772175
  · exact B772179
  · exact B772183
  · exact B772187
  · exact B772191
  · exact B772195
  · exact B772199
  · exact B772203
  · exact B772207
  · exact B772211
  · exact B772215
  · exact B772219
  · exact B772223
  · exact B772227
  · exact B772231
  · exact B772235
  · exact B772239
  · exact B772243
  · exact B772247
  · exact B772251
  · exact B772255
  · exact B772259
  · exact B772263
  · exact B772267
  · exact B772271
  · exact B772275
  · exact B772279
  · exact B772283
  · exact B772287
  · exact B772291
  · exact B772295
  · exact B772299
  · exact B772303
  · exact B772307
  · exact B772311
  · exact B772315
  · exact B772319
  · exact B772323
  · exact B772327
  · exact B772331
  · exact B772335
  · exact B772339
  · exact B772343
  · exact B772347
  · exact B772351
  · exact B772355
  · exact B772359
  · exact B772363
  · exact B772367
  · exact B772371
  · exact B772375
  · exact B772379
  · exact B772383
  · exact B772387
  · exact B772391
  · exact B772395
  · exact B772399
  · exact B772403
  · exact B772407
  · exact B772411
  · exact B772415
  · exact B772419
  · exact B772423
  · exact B772427
  · exact B772431
  · exact B772435
  · exact B772439
  · exact B772443
  · exact B772447
  · exact B772451
  · exact B772455
  · exact B772459
  · exact B772463
  · exact B772467
  · exact B772471
  · exact B772475
  · exact B772479
  · exact B772483
  · exact B772487
  · exact B772491
  · exact B772495
  · exact B772499
  · exact B772503
  · exact B772507
  · exact B772511
  · exact B772515
  · exact B772519
  · exact B772523
  · exact B772527
  · exact B772531
  · exact B772535
  · exact B772539
  · exact B772543
  · exact B772547
  · exact B772551
  · exact B772555
  · exact B772559
  · exact B772563
  · exact B772567
  · exact B772571
  · exact B772575
  · exact B772579
  · exact B772583
  · exact B772587
  · exact B772591
  · exact B772595
  · exact B772599
  · exact B772603
  · exact B772607
  · exact B772611
  · exact B772615
  · exact B772619
  · exact B772623
  · exact B772627
  · exact B772631
  · exact B772635
  · exact B772639
  · exact B772643
  · exact B772647
  · exact B772651
  · exact B772655
  · exact B772659
  · exact B772663
  · exact B772667
  · exact B772671
  · exact B772675
  · exact B772679
  · exact B772683
  · exact B772687
  · exact B772691
  · exact B772695
  · exact B772699
  · exact B772703
  · exact B772707
  · exact B772711
  · exact B772715
  · exact B772719
  · exact B772723
  · exact B772727
  · exact B772731
  · exact B772735
  · exact B772739
  · exact B772743
  · exact B772747
  · exact B772751
  · exact B772755
  · exact B772759
  · exact B772763
  · exact B772767
  · exact B772771
  · exact B772775
  · exact B772779
  · exact B772783
  · exact B772787
  · exact B772791
  · exact B772795
  · exact B772799
  · exact B772803
  · exact B772807
  · exact B772811
  · exact B772815
  · exact B772819
  · exact B772823
  · exact B772827
  · exact B772831
  · exact B772835
  · exact B772839
  · exact B772843
  · exact B772847
  · exact B772851
  · exact B772855
  · exact B772859
  · exact B772863
  · exact B772867
  · exact B772871
  · exact B772875
  · exact B772879
  · exact B772883
  · exact B772887
  · exact B772891
  · exact B772895
  · exact B772899
  · exact B772903
  · exact B772907
  · exact B772911
  · exact B772915
  · exact B772919
  · exact B772923
  · exact B772927
  · exact B772931
  · exact B772935
  · exact B772939
  · exact B772943
  · exact B772947
  · exact B772951
  · exact B772955
  · exact B772959
  · exact B772963
  · exact B772967
  · exact B772971
  · exact B772975
  · exact B772979
  · exact B772983
  · exact B772987
  · exact B772991
  · exact B772995
  · exact B772999
  · exact B773003
  · exact B773007
  · exact B773011
  · exact B773015
  · exact B773019
  · exact B773023
  · exact B773027
  · exact B773031
  · exact B773035
  · exact B773039
  · exact B773043
  · exact B773047
  · exact B773051
  · exact B773055
  · exact B773059
  · exact B773063
  · exact B773067
  · exact B773071
  · exact B773075
  · exact B773079
  · exact B773083
  · exact B773087
  · exact B773091
  · exact B773095
  · exact B773099
  · exact B773103
  · exact B773107
  · exact B773111
  · exact B773115
  · exact B773119
  · exact B773123
  · exact B773127
  · exact B773131

theorem C1 (j : ℕ) (h1 : 193283 ≤ j) (h2 : j ≤ 193583) : Blo 770335 (4 * j + 3) := by
  interval_cases j
  · exact B773135
  · exact B773139
  · exact B773143
  · exact B773147
  · exact B773151
  · exact B773155
  · exact B773159
  · exact B773163
  · exact B773167
  · exact B773171
  · exact B773175
  · exact B773179
  · exact B773183
  · exact B773187
  · exact B773191
  · exact B773195
  · exact B773199
  · exact B773203
  · exact B773207
  · exact B773211
  · exact B773215
  · exact B773219
  · exact B773223
  · exact B773227
  · exact B773231
  · exact B773235
  · exact B773239
  · exact B773243
  · exact B773247
  · exact B773251
  · exact B773255
  · exact B773259
  · exact B773263
  · exact B773267
  · exact B773271
  · exact B773275
  · exact B773279
  · exact B773283
  · exact B773287
  · exact B773291
  · exact B773295
  · exact B773299
  · exact B773303
  · exact B773307
  · exact B773311
  · exact B773315
  · exact B773319
  · exact B773323
  · exact B773327
  · exact B773331
  · exact B773335
  · exact B773339
  · exact B773343
  · exact B773347
  · exact B773351
  · exact B773355
  · exact B773359
  · exact B773363
  · exact B773367
  · exact B773371
  · exact B773375
  · exact B773379
  · exact B773383
  · exact B773387
  · exact B773391
  · exact B773395
  · exact B773399
  · exact B773403
  · exact B773407
  · exact B773411
  · exact B773415
  · exact B773419
  · exact B773423
  · exact B773427
  · exact B773431
  · exact B773435
  · exact B773439
  · exact B773443
  · exact B773447
  · exact B773451
  · exact B773455
  · exact B773459
  · exact B773463
  · exact B773467
  · exact B773471
  · exact B773475
  · exact B773479
  · exact B773483
  · exact B773487
  · exact B773491
  · exact B773495
  · exact B773499
  · exact B773503
  · exact B773507
  · exact B773511
  · exact B773515
  · exact B773519
  · exact B773523
  · exact B773527
  · exact B773531
  · exact B773535
  · exact B773539
  · exact B773543
  · exact B773547
  · exact B773551
  · exact B773555
  · exact B773559
  · exact B773563
  · exact B773567
  · exact B773571
  · exact B773575
  · exact B773579
  · exact B773583
  · exact B773587
  · exact B773591
  · exact B773595
  · exact B773599
  · exact B773603
  · exact B773607
  · exact B773611
  · exact B773615
  · exact B773619
  · exact B773623
  · exact B773627
  · exact B773631
  · exact B773635
  · exact B773639
  · exact B773643
  · exact B773647
  · exact B773651
  · exact B773655
  · exact B773659
  · exact B773663
  · exact B773667
  · exact B773671
  · exact B773675
  · exact B773679
  · exact B773683
  · exact B773687
  · exact B773691
  · exact B773695
  · exact B773699
  · exact B773703
  · exact B773707
  · exact B773711
  · exact B773715
  · exact B773719
  · exact B773723
  · exact B773727
  · exact B773731
  · exact B773735
  · exact B773739
  · exact B773743
  · exact B773747
  · exact B773751
  · exact B773755
  · exact B773759
  · exact B773763
  · exact B773767
  · exact B773771
  · exact B773775
  · exact B773779
  · exact B773783
  · exact B773787
  · exact B773791
  · exact B773795
  · exact B773799
  · exact B773803
  · exact B773807
  · exact B773811
  · exact B773815
  · exact B773819
  · exact B773823
  · exact B773827
  · exact B773831
  · exact B773835
  · exact B773839
  · exact B773843
  · exact B773847
  · exact B773851
  · exact B773855
  · exact B773859
  · exact B773863
  · exact B773867
  · exact B773871
  · exact B773875
  · exact B773879
  · exact B773883
  · exact B773887
  · exact B773891
  · exact B773895
  · exact B773899
  · exact B773903
  · exact B773907
  · exact B773911
  · exact B773915
  · exact B773919
  · exact B773923
  · exact B773927
  · exact B773931
  · exact B773935
  · exact B773939
  · exact B773943
  · exact B773947
  · exact B773951
  · exact B773955
  · exact B773959
  · exact B773963
  · exact B773967
  · exact B773971
  · exact B773975
  · exact B773979
  · exact B773983
  · exact B773987
  · exact B773991
  · exact B773995
  · exact B773999
  · exact B774003
  · exact B774007
  · exact B774011
  · exact B774015
  · exact B774019
  · exact B774023
  · exact B774027
  · exact B774031
  · exact B774035
  · exact B774039
  · exact B774043
  · exact B774047
  · exact B774051
  · exact B774055
  · exact B774059
  · exact B774063
  · exact B774067
  · exact B774071
  · exact B774075
  · exact B774079
  · exact B774083
  · exact B774087
  · exact B774091
  · exact B774095
  · exact B774099
  · exact B774103
  · exact B774107
  · exact B774111
  · exact B774115
  · exact B774119
  · exact B774123
  · exact B774127
  · exact B774131
  · exact B774135
  · exact B774139
  · exact B774143
  · exact B774147
  · exact B774151
  · exact B774155
  · exact B774159
  · exact B774163
  · exact B774167
  · exact B774171
  · exact B774175
  · exact B774179
  · exact B774183
  · exact B774187
  · exact B774191
  · exact B774195
  · exact B774199
  · exact B774203
  · exact B774207
  · exact B774211
  · exact B774215
  · exact B774219
  · exact B774223
  · exact B774227
  · exact B774231
  · exact B774235
  · exact B774239
  · exact B774243
  · exact B774247
  · exact B774251
  · exact B774255
  · exact B774259
  · exact B774263
  · exact B774267
  · exact B774271
  · exact B774275
  · exact B774279
  · exact B774283
  · exact B774287
  · exact B774291
  · exact B774295
  · exact B774299
  · exact B774303
  · exact B774307
  · exact B774311
  · exact B774315
  · exact B774319
  · exact B774323
  · exact B774327
  · exact B774331
  · exact B774335

theorem solution (m : ℕ) (hlo : 770335 ≤ m) (hhi : m ≤ 774335) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 192583 ≤ j := by omega
    have hj2 : j ≤ 193583 := by omega
    have hb : Blo 770335 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 193283 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
