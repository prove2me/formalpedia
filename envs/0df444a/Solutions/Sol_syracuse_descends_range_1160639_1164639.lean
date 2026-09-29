-- Prove2me | solution 1 for syracuse_descends_range_1160639_1164639
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:49.967979+00:00
-- url     : https://prove2.me/submissions/a1a6ff46-826c-47d5-8133-0ed4fb35b315

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


theorem B10616885 : Blo 1160639 10616885 := bbase (se 5 (by rfl) ⟨497666, by rfl⟩ : syracuseStep 10616885 = 995333) (by norm_num)
theorem B2654333 : Blo 1160639 2654333 := bbase (se 3 (by rfl) ⟨497687, by rfl⟩ : syracuseStep 2654333 = 995375) (by norm_num)
theorem B3309797 : Blo 1160639 3309797 := bbase (se 4 (by rfl) ⟨310293, by rfl⟩ : syracuseStep 3309797 = 620587) (by norm_num)
theorem B1769725 : Blo 1160639 1769725 := bbase (se 3 (by rfl) ⟨331823, by rfl⟩ : syracuseStep 1769725 = 663647) (by norm_num)
theorem B1769773 : Blo 1160639 1769773 := bbase (se 3 (by rfl) ⟨331832, by rfl⟩ : syracuseStep 1769773 = 663665) (by norm_num)
theorem B2097581 : Blo 1160639 2097581 := bbase (se 3 (by rfl) ⟨393296, by rfl⟩ : syracuseStep 2097581 = 786593) (by norm_num)
theorem B6291989 : Blo 1160639 6291989 := bbase (se 6 (by rfl) ⟨147468, by rfl⟩ : syracuseStep 6291989 = 294937) (by norm_num)
theorem B2982469 : Blo 1160639 2982469 := bbase (se 4 (by rfl) ⟨279606, by rfl⟩ : syracuseStep 2982469 = 559213) (by norm_num)
theorem B2655173 : Blo 1160639 2655173 := bbase (se 4 (by rfl) ⟨248922, by rfl⟩ : syracuseStep 2655173 = 497845) (by norm_num)
theorem B2655389 : Blo 1160639 2655389 := bbase (se 3 (by rfl) ⟨497885, by rfl⟩ : syracuseStep 2655389 = 995771) (by norm_num)
theorem B2098541 : Blo 1160639 2098541 := bbase (se 3 (by rfl) ⟨393476, by rfl⟩ : syracuseStep 2098541 = 786953) (by norm_num)
theorem B2655629 : Blo 1160639 2655629 := bbase (se 3 (by rfl) ⟨497930, by rfl⟩ : syracuseStep 2655629 = 995861) (by norm_num)
theorem B2655973 : Blo 1160639 2655973 := bbase (se 4 (by rfl) ⟨248997, by rfl⟩ : syracuseStep 2655973 = 497995) (by norm_num)
theorem B5310197 : Blo 1160639 5310197 := bbase (se 5 (by rfl) ⟨248915, by rfl⟩ : syracuseStep 5310197 = 497831) (by norm_num)
theorem B3311381 : Blo 1160639 3311381 := bbase (se 6 (by rfl) ⟨77610, by rfl⟩ : syracuseStep 3311381 = 155221) (by norm_num)
theorem B1345621 : Blo 1160639 1345621 := bbase (se 8 (by rfl) ⟨7884, by rfl⟩ : syracuseStep 1345621 = 15769) (by norm_num)
theorem B10619221 : Blo 1160639 10619221 := bbase (se 10 (by rfl) ⟨15555, by rfl⟩ : syracuseStep 10619221 = 31111) (by norm_num)
theorem B6293909 : Blo 1160639 6293909 := bbase (se 6 (by rfl) ⟨147513, by rfl⟩ : syracuseStep 6293909 = 295027) (by norm_num)
theorem B3312053 : Blo 1160639 3312053 := bbase (se 5 (by rfl) ⟨155252, by rfl⟩ : syracuseStep 3312053 = 310505) (by norm_num)
theorem B2296613 : Blo 1160639 2296613 := bbase (se 4 (by rfl) ⟨215307, by rfl⟩ : syracuseStep 2296613 = 430615) (by norm_num)
theorem B3312485 : Blo 1160639 3312485 := bbase (se 4 (by rfl) ⟨310545, by rfl⟩ : syracuseStep 3312485 = 621091) (by norm_num)
theorem B2722709 : Blo 1160639 2722709 := bbase (se 6 (by rfl) ⟨63813, by rfl⟩ : syracuseStep 2722709 = 127627) (by norm_num)
theorem B3313237 : Blo 1160639 3313237 := bbase (se 8 (by rfl) ⟨19413, by rfl⟩ : syracuseStep 3313237 = 38827) (by norm_num)
theorem B1740965 : Blo 1160639 1740965 := bbase (se 4 (by rfl) ⟨163215, by rfl⟩ : syracuseStep 1740965 = 326431) (by norm_num)
theorem B1740989 : Blo 1160639 1740989 := bbase (se 3 (by rfl) ⟨326435, by rfl⟩ : syracuseStep 1740989 = 652871) (by norm_num)
theorem B1741013 : Blo 1160639 1741013 := bbase (se 7 (by rfl) ⟨20402, by rfl⟩ : syracuseStep 1741013 = 40805) (by norm_num)
theorem B1741037 : Blo 1160639 1741037 := bbase (se 3 (by rfl) ⟨326444, by rfl⟩ : syracuseStep 1741037 = 652889) (by norm_num)
theorem B1741061 : Blo 1160639 1741061 := bbase (se 4 (by rfl) ⟨163224, by rfl⟩ : syracuseStep 1741061 = 326449) (by norm_num)
theorem B1741085 : Blo 1160639 1741085 := bbase (se 3 (by rfl) ⟨326453, by rfl⟩ : syracuseStep 1741085 = 652907) (by norm_num)
theorem B1741109 : Blo 1160639 1741109 := bbase (se 5 (by rfl) ⟨81614, by rfl⟩ : syracuseStep 1741109 = 163229) (by norm_num)
theorem B1741133 : Blo 1160639 1741133 := bbase (se 3 (by rfl) ⟨326462, by rfl⟩ : syracuseStep 1741133 = 652925) (by norm_num)
theorem B1741157 : Blo 1160639 1741157 := bbase (se 4 (by rfl) ⟨163233, by rfl⟩ : syracuseStep 1741157 = 326467) (by norm_num)
theorem B1741181 : Blo 1160639 1741181 := bbase (se 3 (by rfl) ⟨326471, by rfl⟩ : syracuseStep 1741181 = 652943) (by norm_num)
theorem B1741205 : Blo 1160639 1741205 := bbase (se 6 (by rfl) ⟨40809, by rfl⟩ : syracuseStep 1741205 = 81619) (by norm_num)
theorem B1741229 : Blo 1160639 1741229 := bbase (se 3 (by rfl) ⟨326480, by rfl⟩ : syracuseStep 1741229 = 652961) (by norm_num)
theorem B1741253 : Blo 1160639 1741253 := bbase (se 4 (by rfl) ⟨163242, by rfl⟩ : syracuseStep 1741253 = 326485) (by norm_num)
theorem B1741277 : Blo 1160639 1741277 := bbase (se 3 (by rfl) ⟨326489, by rfl⟩ : syracuseStep 1741277 = 652979) (by norm_num)
theorem B1741301 : Blo 1160639 1741301 := bbase (se 5 (by rfl) ⟨81623, by rfl⟩ : syracuseStep 1741301 = 163247) (by norm_num)
theorem B1741325 : Blo 1160639 1741325 := bbase (se 3 (by rfl) ⟨326498, by rfl⟩ : syracuseStep 1741325 = 652997) (by norm_num)
theorem B11932181 : Blo 1160639 11932181 := bbase (se 6 (by rfl) ⟨279660, by rfl⟩ : syracuseStep 11932181 = 559321) (by norm_num)
theorem B1741349 : Blo 1160639 1741349 := bbase (se 4 (by rfl) ⟨163251, by rfl⟩ : syracuseStep 1741349 = 326503) (by norm_num)
theorem B1741373 : Blo 1160639 1741373 := bbase (se 3 (by rfl) ⟨326507, by rfl⟩ : syracuseStep 1741373 = 653015) (by norm_num)
theorem B1741397 : Blo 1160639 1741397 := bbase (se 8 (by rfl) ⟨10203, by rfl⟩ : syracuseStep 1741397 = 20407) (by norm_num)
theorem B1741421 : Blo 1160639 1741421 := bbase (se 3 (by rfl) ⟨326516, by rfl⟩ : syracuseStep 1741421 = 653033) (by norm_num)
theorem B1741445 : Blo 1160639 1741445 := bbase (se 4 (by rfl) ⟨163260, by rfl⟩ : syracuseStep 1741445 = 326521) (by norm_num)
theorem B1741469 : Blo 1160639 1741469 := bbase (se 3 (by rfl) ⟨326525, by rfl⟩ : syracuseStep 1741469 = 653051) (by norm_num)
theorem B1741493 : Blo 1160639 1741493 := bbase (se 5 (by rfl) ⟨81632, by rfl⟩ : syracuseStep 1741493 = 163265) (by norm_num)
theorem B1741517 : Blo 1160639 1741517 := bbase (se 3 (by rfl) ⟨326534, by rfl⟩ : syracuseStep 1741517 = 653069) (by norm_num)
theorem B1741541 : Blo 1160639 1741541 := bbase (se 4 (by rfl) ⟨163269, by rfl⟩ : syracuseStep 1741541 = 326539) (by norm_num)
theorem B1741565 : Blo 1160639 1741565 := bbase (se 3 (by rfl) ⟨326543, by rfl⟩ : syracuseStep 1741565 = 653087) (by norm_num)
theorem B1741589 : Blo 1160639 1741589 := bbase (se 6 (by rfl) ⟨40818, by rfl⟩ : syracuseStep 1741589 = 81637) (by norm_num)
theorem B1741613 : Blo 1160639 1741613 := bbase (se 3 (by rfl) ⟨326552, by rfl⟩ : syracuseStep 1741613 = 653105) (by norm_num)
theorem B1741637 : Blo 1160639 1741637 := bbase (se 4 (by rfl) ⟨163278, by rfl⟩ : syracuseStep 1741637 = 326557) (by norm_num)
theorem B1741661 : Blo 1160639 1741661 := bbase (se 3 (by rfl) ⟨326561, by rfl⟩ : syracuseStep 1741661 = 653123) (by norm_num)
theorem B1741685 : Blo 1160639 1741685 := bbase (se 5 (by rfl) ⟨81641, by rfl⟩ : syracuseStep 1741685 = 163283) (by norm_num)
theorem B1741709 : Blo 1160639 1741709 := bbase (se 3 (by rfl) ⟨326570, by rfl⟩ : syracuseStep 1741709 = 653141) (by norm_num)
theorem B1741733 : Blo 1160639 1741733 := bbase (se 4 (by rfl) ⟨163287, by rfl⟩ : syracuseStep 1741733 = 326575) (by norm_num)
theorem B1741757 : Blo 1160639 1741757 := bbase (se 3 (by rfl) ⟨326579, by rfl⟩ : syracuseStep 1741757 = 653159) (by norm_num)
theorem B1741781 : Blo 1160639 1741781 := bbase (se 7 (by rfl) ⟨20411, by rfl⟩ : syracuseStep 1741781 = 40823) (by norm_num)
theorem B2790373 : Blo 1160639 2790373 := bbase (se 4 (by rfl) ⟨261597, by rfl⟩ : syracuseStep 2790373 = 523195) (by norm_num)
theorem B1741805 : Blo 1160639 1741805 := bbase (se 3 (by rfl) ⟨326588, by rfl⟩ : syracuseStep 1741805 = 653177) (by norm_num)
theorem B1741829 : Blo 1160639 1741829 := bbase (se 4 (by rfl) ⟨163296, by rfl⟩ : syracuseStep 1741829 = 326593) (by norm_num)
theorem B1741853 : Blo 1160639 1741853 := bbase (se 3 (by rfl) ⟨326597, by rfl⟩ : syracuseStep 1741853 = 653195) (by norm_num)
theorem B1741877 : Blo 1160639 1741877 := bbase (se 5 (by rfl) ⟨81650, by rfl⟩ : syracuseStep 1741877 = 163301) (by norm_num)
theorem B1741901 : Blo 1160639 1741901 := bbase (se 3 (by rfl) ⟨326606, by rfl⟩ : syracuseStep 1741901 = 653213) (by norm_num)
theorem B1741925 : Blo 1160639 1741925 := bbase (se 4 (by rfl) ⟨163305, by rfl⟩ : syracuseStep 1741925 = 326611) (by norm_num)
theorem B1741949 : Blo 1160639 1741949 := bbase (se 3 (by rfl) ⟨326615, by rfl⟩ : syracuseStep 1741949 = 653231) (by norm_num)
theorem B1741973 : Blo 1160639 1741973 := bbase (se 6 (by rfl) ⟨40827, by rfl⟩ : syracuseStep 1741973 = 81655) (by norm_num)
theorem B5969045 : Blo 1160639 5969045 := bbase (se 6 (by rfl) ⟨139899, by rfl⟩ : syracuseStep 5969045 = 279799) (by norm_num)
theorem B1741997 : Blo 1160639 1741997 := bbase (se 3 (by rfl) ⟨326624, by rfl⟩ : syracuseStep 1741997 = 653249) (by norm_num)
theorem B1742021 : Blo 1160639 1742021 := bbase (se 4 (by rfl) ⟨163314, by rfl⟩ : syracuseStep 1742021 = 326629) (by norm_num)
theorem B2790605 : Blo 1160639 2790605 := bbase (se 3 (by rfl) ⟨523238, by rfl⟩ : syracuseStep 2790605 = 1046477) (by norm_num)
theorem B1742045 : Blo 1160639 1742045 := bbase (se 3 (by rfl) ⟨326633, by rfl⟩ : syracuseStep 1742045 = 653267) (by norm_num)
theorem B1742069 : Blo 1160639 1742069 := bbase (se 5 (by rfl) ⟨81659, by rfl⟩ : syracuseStep 1742069 = 163319) (by norm_num)
theorem B1742093 : Blo 1160639 1742093 := bbase (se 3 (by rfl) ⟨326642, by rfl⟩ : syracuseStep 1742093 = 653285) (by norm_num)
theorem B1742117 : Blo 1160639 1742117 := bbase (se 4 (by rfl) ⟨163323, by rfl⟩ : syracuseStep 1742117 = 326647) (by norm_num)
theorem B1742141 : Blo 1160639 1742141 := bbase (se 3 (by rfl) ⟨326651, by rfl⟩ : syracuseStep 1742141 = 653303) (by norm_num)
theorem B1742165 : Blo 1160639 1742165 := bbase (se 14 (by rfl) ⟨159, by rfl⟩ : syracuseStep 1742165 = 319) (by norm_num)
theorem B2790749 : Blo 1160639 2790749 := bbase (se 3 (by rfl) ⟨523265, by rfl⟩ : syracuseStep 2790749 = 1046531) (by norm_num)
theorem B1742189 : Blo 1160639 1742189 := bbase (se 3 (by rfl) ⟨326660, by rfl⟩ : syracuseStep 1742189 = 653321) (by norm_num)
theorem B1742213 : Blo 1160639 1742213 := bbase (se 4 (by rfl) ⟨163332, by rfl⟩ : syracuseStep 1742213 = 326665) (by norm_num)
theorem B1742237 : Blo 1160639 1742237 := bbase (se 3 (by rfl) ⟨326669, by rfl⟩ : syracuseStep 1742237 = 653339) (by norm_num)
theorem B1742261 : Blo 1160639 1742261 := bbase (se 5 (by rfl) ⟨81668, by rfl⟩ : syracuseStep 1742261 = 163337) (by norm_num)
theorem B1742285 : Blo 1160639 1742285 := bbase (se 3 (by rfl) ⟨326678, by rfl⟩ : syracuseStep 1742285 = 653357) (by norm_num)
theorem B1742309 : Blo 1160639 1742309 := bbase (se 4 (by rfl) ⟨163341, by rfl⟩ : syracuseStep 1742309 = 326683) (by norm_num)
theorem B1742333 : Blo 1160639 1742333 := bbase (se 3 (by rfl) ⟨326687, by rfl⟩ : syracuseStep 1742333 = 653375) (by norm_num)
theorem B1742357 : Blo 1160639 1742357 := bbase (se 6 (by rfl) ⟨40836, by rfl⟩ : syracuseStep 1742357 = 81673) (by norm_num)
theorem B1742381 : Blo 1160639 1742381 := bbase (se 3 (by rfl) ⟨326696, by rfl⟩ : syracuseStep 1742381 = 653393) (by norm_num)
theorem B1742405 : Blo 1160639 1742405 := bbase (se 4 (by rfl) ⟨163350, by rfl⟩ : syracuseStep 1742405 = 326701) (by norm_num)
theorem B1513033 : Blo 1160639 1513033 := bbase (se 2 (by rfl) ⟨567387, by rfl⟩ : syracuseStep 1513033 = 1134775) (by norm_num)
theorem B2790989 : Blo 1160639 2790989 := bbase (se 3 (by rfl) ⟨523310, by rfl⟩ : syracuseStep 2790989 = 1046621) (by norm_num)
theorem B1742429 : Blo 1160639 1742429 := bbase (se 3 (by rfl) ⟨326705, by rfl⟩ : syracuseStep 1742429 = 653411) (by norm_num)
theorem B1742453 : Blo 1160639 1742453 := bbase (se 5 (by rfl) ⟨81677, by rfl⟩ : syracuseStep 1742453 = 163355) (by norm_num)
theorem B1742477 : Blo 1160639 1742477 := bbase (se 3 (by rfl) ⟨326714, by rfl⟩ : syracuseStep 1742477 = 653429) (by norm_num)
theorem B1742501 : Blo 1160639 1742501 := bbase (se 4 (by rfl) ⟨163359, by rfl⟩ : syracuseStep 1742501 = 326719) (by norm_num)
theorem B1742525 : Blo 1160639 1742525 := bbase (se 3 (by rfl) ⟨326723, by rfl⟩ : syracuseStep 1742525 = 653447) (by norm_num)
theorem B2987725 : Blo 1160639 2987725 := bbase (se 3 (by rfl) ⟨560198, by rfl⟩ : syracuseStep 2987725 = 1120397) (by norm_num)
theorem B1742549 : Blo 1160639 1742549 := bbase (se 7 (by rfl) ⟨20420, by rfl⟩ : syracuseStep 1742549 = 40841) (by norm_num)
theorem B1742573 : Blo 1160639 1742573 := bbase (se 3 (by rfl) ⟨326732, by rfl⟩ : syracuseStep 1742573 = 653465) (by norm_num)
theorem B1742597 : Blo 1160639 1742597 := bbase (se 4 (by rfl) ⟨163368, by rfl⟩ : syracuseStep 1742597 = 326737) (by norm_num)
theorem B1742621 : Blo 1160639 1742621 := bbase (se 3 (by rfl) ⟨326741, by rfl⟩ : syracuseStep 1742621 = 653483) (by norm_num)
theorem B1742645 : Blo 1160639 1742645 := bbase (se 5 (by rfl) ⟨81686, by rfl⟩ : syracuseStep 1742645 = 163373) (by norm_num)
theorem B1742669 : Blo 1160639 1742669 := bbase (se 3 (by rfl) ⟨326750, by rfl⟩ : syracuseStep 1742669 = 653501) (by norm_num)
theorem B1677133 : Blo 1160639 1677133 := bbase (se 3 (by rfl) ⟨314462, by rfl⟩ : syracuseStep 1677133 = 628925) (by norm_num)
theorem B1742693 : Blo 1160639 1742693 := bbase (se 4 (by rfl) ⟨163377, by rfl⟩ : syracuseStep 1742693 = 326755) (by norm_num)
theorem B1742717 : Blo 1160639 1742717 := bbase (se 3 (by rfl) ⟨326759, by rfl⟩ : syracuseStep 1742717 = 653519) (by norm_num)
theorem B1742741 : Blo 1160639 1742741 := bbase (se 6 (by rfl) ⟨40845, by rfl⟩ : syracuseStep 1742741 = 81691) (by norm_num)
theorem B1742765 : Blo 1160639 1742765 := bbase (se 3 (by rfl) ⟨326768, by rfl⟩ : syracuseStep 1742765 = 653537) (by norm_num)
theorem B1742789 : Blo 1160639 1742789 := bbase (se 4 (by rfl) ⟨163386, by rfl⟩ : syracuseStep 1742789 = 326773) (by norm_num)
theorem B1742813 : Blo 1160639 1742813 := bbase (se 3 (by rfl) ⟨326777, by rfl⟩ : syracuseStep 1742813 = 653555) (by norm_num)
theorem B1742837 : Blo 1160639 1742837 := bbase (se 5 (by rfl) ⟨81695, by rfl⟩ : syracuseStep 1742837 = 163391) (by norm_num)
theorem B1742861 : Blo 1160639 1742861 := bbase (se 3 (by rfl) ⟨326786, by rfl⟩ : syracuseStep 1742861 = 653573) (by norm_num)
theorem B1742885 : Blo 1160639 1742885 := bbase (se 4 (by rfl) ⟨163395, by rfl⟩ : syracuseStep 1742885 = 326791) (by norm_num)
theorem B1742909 : Blo 1160639 1742909 := bbase (se 3 (by rfl) ⟨326795, by rfl⟩ : syracuseStep 1742909 = 653591) (by norm_num)
theorem B1742933 : Blo 1160639 1742933 := bbase (se 8 (by rfl) ⟨10212, by rfl⟩ : syracuseStep 1742933 = 20425) (by norm_num)
theorem B1742957 : Blo 1160639 1742957 := bbase (se 3 (by rfl) ⟨326804, by rfl⟩ : syracuseStep 1742957 = 653609) (by norm_num)
theorem B1742981 : Blo 1160639 1742981 := bbase (se 4 (by rfl) ⟨163404, by rfl⟩ : syracuseStep 1742981 = 326809) (by norm_num)
theorem B1743005 : Blo 1160639 1743005 := bbase (se 3 (by rfl) ⟨326813, by rfl⟩ : syracuseStep 1743005 = 653627) (by norm_num)
theorem B1743029 : Blo 1160639 1743029 := bbase (se 5 (by rfl) ⟨81704, by rfl⟩ : syracuseStep 1743029 = 163409) (by norm_num)
theorem B1743053 : Blo 1160639 1743053 := bbase (se 3 (by rfl) ⟨326822, by rfl⟩ : syracuseStep 1743053 = 653645) (by norm_num)
theorem B1743077 : Blo 1160639 1743077 := bbase (se 4 (by rfl) ⟨163413, by rfl⟩ : syracuseStep 1743077 = 326827) (by norm_num)
theorem B1743101 : Blo 1160639 1743101 := bbase (se 3 (by rfl) ⟨326831, by rfl⟩ : syracuseStep 1743101 = 653663) (by norm_num)
theorem B1743125 : Blo 1160639 1743125 := bbase (se 6 (by rfl) ⟨40854, by rfl⟩ : syracuseStep 1743125 = 81709) (by norm_num)
theorem B1743149 : Blo 1160639 1743149 := bbase (se 3 (by rfl) ⟨326840, by rfl⟩ : syracuseStep 1743149 = 653681) (by norm_num)
theorem B1743173 : Blo 1160639 1743173 := bbase (se 4 (by rfl) ⟨163422, by rfl⟩ : syracuseStep 1743173 = 326845) (by norm_num)
theorem B2791757 : Blo 1160639 2791757 := bbase (se 3 (by rfl) ⟨523454, by rfl⟩ : syracuseStep 2791757 = 1046909) (by norm_num)
theorem B1743197 : Blo 1160639 1743197 := bbase (se 3 (by rfl) ⟨326849, by rfl⟩ : syracuseStep 1743197 = 653699) (by norm_num)
theorem B1743221 : Blo 1160639 1743221 := bbase (se 5 (by rfl) ⟨81713, by rfl⟩ : syracuseStep 1743221 = 163427) (by norm_num)
theorem B3316085 : Blo 1160639 3316085 := bbase (se 5 (by rfl) ⟨155441, by rfl⟩ : syracuseStep 3316085 = 310883) (by norm_num)
theorem B1743245 : Blo 1160639 1743245 := bbase (se 3 (by rfl) ⟨326858, by rfl⟩ : syracuseStep 1743245 = 653717) (by norm_num)
theorem B1743269 : Blo 1160639 1743269 := bbase (se 4 (by rfl) ⟨163431, by rfl⟩ : syracuseStep 1743269 = 326863) (by norm_num)
theorem B1743293 : Blo 1160639 1743293 := bbase (se 3 (by rfl) ⟨326867, by rfl⟩ : syracuseStep 1743293 = 653735) (by norm_num)
theorem B1743317 : Blo 1160639 1743317 := bbase (se 7 (by rfl) ⟨20429, by rfl⟩ : syracuseStep 1743317 = 40859) (by norm_num)
theorem B1743341 : Blo 1160639 1743341 := bbase (se 3 (by rfl) ⟨326876, by rfl⟩ : syracuseStep 1743341 = 653753) (by norm_num)
theorem B1743365 : Blo 1160639 1743365 := bbase (se 4 (by rfl) ⟨163440, by rfl⟩ : syracuseStep 1743365 = 326881) (by norm_num)
theorem B1743389 : Blo 1160639 1743389 := bbase (se 3 (by rfl) ⟨326885, by rfl⟩ : syracuseStep 1743389 = 653771) (by norm_num)
theorem B1743413 : Blo 1160639 1743413 := bbase (se 5 (by rfl) ⟨81722, by rfl⟩ : syracuseStep 1743413 = 163445) (by norm_num)
theorem B1743437 : Blo 1160639 1743437 := bbase (se 3 (by rfl) ⟨326894, by rfl⟩ : syracuseStep 1743437 = 653789) (by norm_num)
theorem B1743461 : Blo 1160639 1743461 := bbase (se 4 (by rfl) ⟨163449, by rfl⟩ : syracuseStep 1743461 = 326899) (by norm_num)
theorem B1743485 : Blo 1160639 1743485 := bbase (se 3 (by rfl) ⟨326903, by rfl⟩ : syracuseStep 1743485 = 653807) (by norm_num)
theorem B1743509 : Blo 1160639 1743509 := bbase (se 6 (by rfl) ⟨40863, by rfl⟩ : syracuseStep 1743509 = 81727) (by norm_num)
theorem B1743533 : Blo 1160639 1743533 := bbase (se 3 (by rfl) ⟨326912, by rfl⟩ : syracuseStep 1743533 = 653825) (by norm_num)
theorem B1743557 : Blo 1160639 1743557 := bbase (se 4 (by rfl) ⟨163458, by rfl⟩ : syracuseStep 1743557 = 326917) (by norm_num)
theorem B1743581 : Blo 1160639 1743581 := bbase (se 3 (by rfl) ⟨326921, by rfl⟩ : syracuseStep 1743581 = 653843) (by norm_num)
theorem B1743605 : Blo 1160639 1743605 := bbase (se 5 (by rfl) ⟨81731, by rfl⟩ : syracuseStep 1743605 = 163463) (by norm_num)
theorem B1743629 : Blo 1160639 1743629 := bbase (se 3 (by rfl) ⟨326930, by rfl⟩ : syracuseStep 1743629 = 653861) (by norm_num)
theorem B1743653 : Blo 1160639 1743653 := bbase (se 4 (by rfl) ⟨163467, by rfl⟩ : syracuseStep 1743653 = 326935) (by norm_num)
theorem B1743677 : Blo 1160639 1743677 := bbase (se 3 (by rfl) ⟨326939, by rfl⟩ : syracuseStep 1743677 = 653879) (by norm_num)
theorem B1743701 : Blo 1160639 1743701 := bbase (se 9 (by rfl) ⟨5108, by rfl⟩ : syracuseStep 1743701 = 10217) (by norm_num)
theorem B1743725 : Blo 1160639 1743725 := bbase (se 3 (by rfl) ⟨326948, by rfl⟩ : syracuseStep 1743725 = 653897) (by norm_num)
theorem B2235269 : Blo 1160639 2235269 := bbase (se 4 (by rfl) ⟨209556, by rfl⟩ : syracuseStep 2235269 = 419113) (by norm_num)
theorem B1743749 : Blo 1160639 1743749 := bbase (se 4 (by rfl) ⟨163476, by rfl⟩ : syracuseStep 1743749 = 326953) (by norm_num)
theorem B1743773 : Blo 1160639 1743773 := bbase (se 3 (by rfl) ⟨326957, by rfl⟩ : syracuseStep 1743773 = 653915) (by norm_num)
theorem B1743797 : Blo 1160639 1743797 := bbase (se 5 (by rfl) ⟨81740, by rfl⟩ : syracuseStep 1743797 = 163481) (by norm_num)
theorem B1743821 : Blo 1160639 1743821 := bbase (se 3 (by rfl) ⟨326966, by rfl⟩ : syracuseStep 1743821 = 653933) (by norm_num)
theorem B20126677 : Blo 1160639 20126677 := bbase (se 7 (by rfl) ⟨235859, by rfl⟩ : syracuseStep 20126677 = 471719) (by norm_num)
theorem B1743845 : Blo 1160639 1743845 := bbase (se 4 (by rfl) ⟨163485, by rfl⟩ : syracuseStep 1743845 = 326971) (by norm_num)
theorem B1743869 : Blo 1160639 1743869 := bbase (se 3 (by rfl) ⟨326975, by rfl⟩ : syracuseStep 1743869 = 653951) (by norm_num)
theorem B1743893 : Blo 1160639 1743893 := bbase (se 6 (by rfl) ⟨40872, by rfl⟩ : syracuseStep 1743893 = 81745) (by norm_num)
theorem B1743917 : Blo 1160639 1743917 := bbase (se 3 (by rfl) ⟨326984, by rfl⟩ : syracuseStep 1743917 = 653969) (by norm_num)
theorem B1743941 : Blo 1160639 1743941 := bbase (se 4 (by rfl) ⟨163494, by rfl⟩ : syracuseStep 1743941 = 326989) (by norm_num)
theorem B1743965 : Blo 1160639 1743965 := bbase (se 3 (by rfl) ⟨326993, by rfl⟩ : syracuseStep 1743965 = 653987) (by norm_num)
theorem B1743989 : Blo 1160639 1743989 := bbase (se 5 (by rfl) ⟨81749, by rfl⟩ : syracuseStep 1743989 = 163499) (by norm_num)
theorem B1744013 : Blo 1160639 1744013 := bbase (se 3 (by rfl) ⟨327002, by rfl⟩ : syracuseStep 1744013 = 654005) (by norm_num)
theorem B1744037 : Blo 1160639 1744037 := bbase (se 4 (by rfl) ⟨163503, by rfl⟩ : syracuseStep 1744037 = 327007) (by norm_num)
theorem B1744061 : Blo 1160639 1744061 := bbase (se 3 (by rfl) ⟨327011, by rfl⟩ : syracuseStep 1744061 = 654023) (by norm_num)
theorem B1744085 : Blo 1160639 1744085 := bbase (se 7 (by rfl) ⟨20438, by rfl⟩ : syracuseStep 1744085 = 40877) (by norm_num)
theorem B1744109 : Blo 1160639 1744109 := bbase (se 3 (by rfl) ⟨327020, by rfl⟩ : syracuseStep 1744109 = 654041) (by norm_num)
theorem B1744133 : Blo 1160639 1744133 := bbase (se 4 (by rfl) ⟨163512, by rfl⟩ : syracuseStep 1744133 = 327025) (by norm_num)
theorem B1744157 : Blo 1160639 1744157 := bbase (se 3 (by rfl) ⟨327029, by rfl⟩ : syracuseStep 1744157 = 654059) (by norm_num)
theorem B1744181 : Blo 1160639 1744181 := bbase (se 5 (by rfl) ⟨81758, by rfl⟩ : syracuseStep 1744181 = 163517) (by norm_num)
theorem B1744205 : Blo 1160639 1744205 := bbase (se 3 (by rfl) ⟨327038, by rfl⟩ : syracuseStep 1744205 = 654077) (by norm_num)
theorem B1744229 : Blo 1160639 1744229 := bbase (se 4 (by rfl) ⟨163521, by rfl⟩ : syracuseStep 1744229 = 327043) (by norm_num)
theorem B1744253 : Blo 1160639 1744253 := bbase (se 3 (by rfl) ⟨327047, by rfl⟩ : syracuseStep 1744253 = 654095) (by norm_num)
theorem B1744277 : Blo 1160639 1744277 := bbase (se 6 (by rfl) ⟨40881, by rfl⟩ : syracuseStep 1744277 = 81763) (by norm_num)
theorem B1744301 : Blo 1160639 1744301 := bbase (se 3 (by rfl) ⟨327056, by rfl⟩ : syracuseStep 1744301 = 654113) (by norm_num)
theorem B1744325 : Blo 1160639 1744325 := bbase (se 4 (by rfl) ⟨163530, by rfl⟩ : syracuseStep 1744325 = 327061) (by norm_num)
theorem B1744349 : Blo 1160639 1744349 := bbase (se 3 (by rfl) ⟨327065, by rfl⟩ : syracuseStep 1744349 = 654131) (by norm_num)
theorem B1744373 : Blo 1160639 1744373 := bbase (se 5 (by rfl) ⟨81767, by rfl⟩ : syracuseStep 1744373 = 163535) (by norm_num)
theorem B1744397 : Blo 1160639 1744397 := bbase (se 3 (by rfl) ⟨327074, by rfl⟩ : syracuseStep 1744397 = 654149) (by norm_num)
theorem B1744421 : Blo 1160639 1744421 := bbase (se 4 (by rfl) ⟨163539, by rfl⟩ : syracuseStep 1744421 = 327079) (by norm_num)
theorem B1744445 : Blo 1160639 1744445 := bbase (se 3 (by rfl) ⟨327083, by rfl⟩ : syracuseStep 1744445 = 654167) (by norm_num)
theorem B8822357 : Blo 1160639 8822357 := bbase (se 8 (by rfl) ⟨51693, by rfl⟩ : syracuseStep 8822357 = 103387) (by norm_num)
theorem B1744469 : Blo 1160639 1744469 := bbase (se 8 (by rfl) ⟨10221, by rfl⟩ : syracuseStep 1744469 = 20443) (by norm_num)
theorem B1744493 : Blo 1160639 1744493 := bbase (se 3 (by rfl) ⟨327092, by rfl⟩ : syracuseStep 1744493 = 654185) (by norm_num)
theorem B1744517 : Blo 1160639 1744517 := bbase (se 4 (by rfl) ⟨163548, by rfl⟩ : syracuseStep 1744517 = 327097) (by norm_num)
theorem B1744541 : Blo 1160639 1744541 := bbase (se 3 (by rfl) ⟨327101, by rfl⟩ : syracuseStep 1744541 = 654203) (by norm_num)
theorem B2793133 : Blo 1160639 2793133 := bbase (se 3 (by rfl) ⟨523712, by rfl⟩ : syracuseStep 2793133 = 1047425) (by norm_num)
theorem B1744565 : Blo 1160639 1744565 := bbase (se 5 (by rfl) ⟨81776, by rfl⟩ : syracuseStep 1744565 = 163553) (by norm_num)
theorem B1744589 : Blo 1160639 1744589 := bbase (se 3 (by rfl) ⟨327110, by rfl⟩ : syracuseStep 1744589 = 654221) (by norm_num)
theorem B1744613 : Blo 1160639 1744613 := bbase (se 4 (by rfl) ⟨163557, by rfl⟩ : syracuseStep 1744613 = 327115) (by norm_num)
theorem B1744637 : Blo 1160639 1744637 := bbase (se 3 (by rfl) ⟨327119, by rfl⟩ : syracuseStep 1744637 = 654239) (by norm_num)
theorem B1744661 : Blo 1160639 1744661 := bbase (se 6 (by rfl) ⟨40890, by rfl⟩ : syracuseStep 1744661 = 81781) (by norm_num)
theorem B1744685 : Blo 1160639 1744685 := bbase (se 3 (by rfl) ⟨327128, by rfl⟩ : syracuseStep 1744685 = 654257) (by norm_num)
theorem B7446325 : Blo 1160639 7446325 := bbase (se 5 (by rfl) ⟨349046, by rfl⟩ : syracuseStep 7446325 = 698093) (by norm_num)
theorem B1744709 : Blo 1160639 1744709 := bbase (se 4 (by rfl) ⟨163566, by rfl⟩ : syracuseStep 1744709 = 327133) (by norm_num)
theorem B2236253 : Blo 1160639 2236253 := bbase (se 3 (by rfl) ⟨419297, by rfl⟩ : syracuseStep 2236253 = 838595) (by norm_num)
theorem B1744733 : Blo 1160639 1744733 := bbase (se 3 (by rfl) ⟨327137, by rfl⟩ : syracuseStep 1744733 = 654275) (by norm_num)
theorem B1744757 : Blo 1160639 1744757 := bbase (se 5 (by rfl) ⟨81785, by rfl⟩ : syracuseStep 1744757 = 163571) (by norm_num)
theorem B2203517 : Blo 1160639 2203517 := bbase (se 3 (by rfl) ⟨413159, by rfl⟩ : syracuseStep 2203517 = 826319) (by norm_num)
theorem B1744781 : Blo 1160639 1744781 := bbase (se 3 (by rfl) ⟨327146, by rfl⟩ : syracuseStep 1744781 = 654293) (by norm_num)
theorem B1744805 : Blo 1160639 1744805 := bbase (se 4 (by rfl) ⟨163575, by rfl⟩ : syracuseStep 1744805 = 327151) (by norm_num)
theorem B1744829 : Blo 1160639 1744829 := bbase (se 3 (by rfl) ⟨327155, by rfl⟩ : syracuseStep 1744829 = 654311) (by norm_num)
theorem B1744853 : Blo 1160639 1744853 := bbase (se 7 (by rfl) ⟨20447, by rfl⟩ : syracuseStep 1744853 = 40895) (by norm_num)
theorem B1744877 : Blo 1160639 1744877 := bbase (se 3 (by rfl) ⟨327164, by rfl⟩ : syracuseStep 1744877 = 654329) (by norm_num)
theorem B1744901 : Blo 1160639 1744901 := bbase (se 4 (by rfl) ⟨163584, by rfl⟩ : syracuseStep 1744901 = 327169) (by norm_num)
theorem B2203661 : Blo 1160639 2203661 := bbase (se 3 (by rfl) ⟨413186, by rfl⟩ : syracuseStep 2203661 = 826373) (by norm_num)
theorem B1744925 : Blo 1160639 1744925 := bbase (se 3 (by rfl) ⟨327173, by rfl⟩ : syracuseStep 1744925 = 654347) (by norm_num)
theorem B1744949 : Blo 1160639 1744949 := bbase (se 5 (by rfl) ⟨81794, by rfl⟩ : syracuseStep 1744949 = 163589) (by norm_num)
theorem B1744973 : Blo 1160639 1744973 := bbase (se 3 (by rfl) ⟨327182, by rfl⟩ : syracuseStep 1744973 = 654365) (by norm_num)
theorem B1744997 : Blo 1160639 1744997 := bbase (se 4 (by rfl) ⟨163593, by rfl⟩ : syracuseStep 1744997 = 327187) (by norm_num)
theorem B1745021 : Blo 1160639 1745021 := bbase (se 3 (by rfl) ⟨327191, by rfl⟩ : syracuseStep 1745021 = 654383) (by norm_num)
theorem B1745045 : Blo 1160639 1745045 := bbase (se 6 (by rfl) ⟨40899, by rfl⟩ : syracuseStep 1745045 = 81799) (by norm_num)
theorem B1745069 : Blo 1160639 1745069 := bbase (se 3 (by rfl) ⟨327200, by rfl⟩ : syracuseStep 1745069 = 654401) (by norm_num)
theorem B1745093 : Blo 1160639 1745093 := bbase (se 4 (by rfl) ⟨163602, by rfl⟩ : syracuseStep 1745093 = 327205) (by norm_num)
theorem B1745117 : Blo 1160639 1745117 := bbase (se 3 (by rfl) ⟨327209, by rfl⟩ : syracuseStep 1745117 = 654419) (by norm_num)
theorem B1745141 : Blo 1160639 1745141 := bbase (se 5 (by rfl) ⟨81803, by rfl⟩ : syracuseStep 1745141 = 163607) (by norm_num)
theorem B1745165 : Blo 1160639 1745165 := bbase (se 3 (by rfl) ⟨327218, by rfl⟩ : syracuseStep 1745165 = 654437) (by norm_num)
theorem B1745189 : Blo 1160639 1745189 := bbase (se 4 (by rfl) ⟨163611, by rfl⟩ : syracuseStep 1745189 = 327223) (by norm_num)
theorem B2203949 : Blo 1160639 2203949 := bbase (se 3 (by rfl) ⟨413240, by rfl⟩ : syracuseStep 2203949 = 826481) (by norm_num)
theorem B1745213 : Blo 1160639 1745213 := bbase (se 3 (by rfl) ⟨327227, by rfl⟩ : syracuseStep 1745213 = 654455) (by norm_num)
theorem B1745237 : Blo 1160639 1745237 := bbase (se 10 (by rfl) ⟨2556, by rfl⟩ : syracuseStep 1745237 = 5113) (by norm_num)
theorem B1745261 : Blo 1160639 1745261 := bbase (se 3 (by rfl) ⟨327236, by rfl⟩ : syracuseStep 1745261 = 654473) (by norm_num)
theorem B1417585 : Blo 1160639 1417585 := bbase (se 2 (by rfl) ⟨531594, by rfl⟩ : syracuseStep 1417585 = 1063189) (by norm_num)
theorem B1745285 : Blo 1160639 1745285 := bbase (se 4 (by rfl) ⟨163620, by rfl⟩ : syracuseStep 1745285 = 327241) (by norm_num)
theorem B1745309 : Blo 1160639 1745309 := bbase (se 3 (by rfl) ⟨327245, by rfl⟩ : syracuseStep 1745309 = 654491) (by norm_num)
theorem B1745333 : Blo 1160639 1745333 := bbase (se 5 (by rfl) ⟨81812, by rfl⟩ : syracuseStep 1745333 = 163625) (by norm_num)
theorem B2204101 : Blo 1160639 2204101 := bbase (se 4 (by rfl) ⟨206634, by rfl⟩ : syracuseStep 2204101 = 413269) (by norm_num)
theorem B1745357 : Blo 1160639 1745357 := bbase (se 3 (by rfl) ⟨327254, by rfl⟩ : syracuseStep 1745357 = 654509) (by norm_num)
theorem B1745381 : Blo 1160639 1745381 := bbase (se 4 (by rfl) ⟨163629, by rfl⟩ : syracuseStep 1745381 = 327259) (by norm_num)
theorem B1745405 : Blo 1160639 1745405 := bbase (se 3 (by rfl) ⟨327263, by rfl⟩ : syracuseStep 1745405 = 654527) (by norm_num)
theorem B1745429 : Blo 1160639 1745429 := bbase (se 6 (by rfl) ⟨40908, by rfl⟩ : syracuseStep 1745429 = 81817) (by norm_num)
theorem B1745453 : Blo 1160639 1745453 := bbase (se 3 (by rfl) ⟨327272, by rfl⟩ : syracuseStep 1745453 = 654545) (by norm_num)
theorem B1745477 : Blo 1160639 1745477 := bbase (se 4 (by rfl) ⟨163638, by rfl⟩ : syracuseStep 1745477 = 327277) (by norm_num)
theorem B1745501 : Blo 1160639 1745501 := bbase (se 3 (by rfl) ⟨327281, by rfl⟩ : syracuseStep 1745501 = 654563) (by norm_num)
theorem B1745525 : Blo 1160639 1745525 := bbase (se 5 (by rfl) ⟨81821, by rfl⟩ : syracuseStep 1745525 = 163643) (by norm_num)
theorem B1745549 : Blo 1160639 1745549 := bbase (se 3 (by rfl) ⟨327290, by rfl⟩ : syracuseStep 1745549 = 654581) (by norm_num)
theorem B11936405 : Blo 1160639 11936405 := bbase (se 6 (by rfl) ⟨279759, by rfl⟩ : syracuseStep 11936405 = 559519) (by norm_num)
theorem B1745573 : Blo 1160639 1745573 := bbase (se 4 (by rfl) ⟨163647, by rfl⟩ : syracuseStep 1745573 = 327295) (by norm_num)
theorem B1745597 : Blo 1160639 1745597 := bbase (se 3 (by rfl) ⟨327299, by rfl⟩ : syracuseStep 1745597 = 654599) (by norm_num)
theorem B1745621 : Blo 1160639 1745621 := bbase (se 7 (by rfl) ⟨20456, by rfl⟩ : syracuseStep 1745621 = 40913) (by norm_num)
theorem B3023581 : Blo 1160639 3023581 := bbase (se 3 (by rfl) ⟨566921, by rfl⟩ : syracuseStep 3023581 = 1133843) (by norm_num)
theorem B1745645 : Blo 1160639 1745645 := bbase (se 3 (by rfl) ⟨327308, by rfl⟩ : syracuseStep 1745645 = 654617) (by norm_num)
theorem B2204405 : Blo 1160639 2204405 := bbase (se 5 (by rfl) ⟨103331, by rfl⟩ : syracuseStep 2204405 = 206663) (by norm_num)
theorem B1745669 : Blo 1160639 1745669 := bbase (se 4 (by rfl) ⟨163656, by rfl⟩ : syracuseStep 1745669 = 327313) (by norm_num)
theorem B1745693 : Blo 1160639 1745693 := bbase (se 3 (by rfl) ⟨327317, by rfl⟩ : syracuseStep 1745693 = 654635) (by norm_num)
theorem B1745717 : Blo 1160639 1745717 := bbase (se 5 (by rfl) ⟨81830, by rfl⟩ : syracuseStep 1745717 = 163661) (by norm_num)
theorem B1745741 : Blo 1160639 1745741 := bbase (se 3 (by rfl) ⟨327326, by rfl⟩ : syracuseStep 1745741 = 654653) (by norm_num)
theorem B2794333 : Blo 1160639 2794333 := bbase (se 3 (by rfl) ⟨523937, by rfl⟩ : syracuseStep 2794333 = 1047875) (by norm_num)
theorem B1745765 : Blo 1160639 1745765 := bbase (se 4 (by rfl) ⟨163665, by rfl⟩ : syracuseStep 1745765 = 327331) (by norm_num)
theorem B1745789 : Blo 1160639 1745789 := bbase (se 3 (by rfl) ⟨327335, by rfl⟩ : syracuseStep 1745789 = 654671) (by norm_num)
theorem B1745813 : Blo 1160639 1745813 := bbase (se 6 (by rfl) ⟨40917, by rfl⟩ : syracuseStep 1745813 = 81835) (by norm_num)
theorem B1745837 : Blo 1160639 1745837 := bbase (se 3 (by rfl) ⟨327344, by rfl⟩ : syracuseStep 1745837 = 654689) (by norm_num)
theorem B1745861 : Blo 1160639 1745861 := bbase (se 4 (by rfl) ⟨163674, by rfl⟩ : syracuseStep 1745861 = 327349) (by norm_num)
theorem B1745885 : Blo 1160639 1745885 := bbase (se 3 (by rfl) ⟨327353, by rfl⟩ : syracuseStep 1745885 = 654707) (by norm_num)
theorem B1745909 : Blo 1160639 1745909 := bbase (se 5 (by rfl) ⟨81839, by rfl⟩ : syracuseStep 1745909 = 163679) (by norm_num)
theorem B1745933 : Blo 1160639 1745933 := bbase (se 3 (by rfl) ⟨327362, by rfl⟩ : syracuseStep 1745933 = 654725) (by norm_num)
theorem B1745957 : Blo 1160639 1745957 := bbase (se 4 (by rfl) ⟨163683, by rfl⟩ : syracuseStep 1745957 = 327367) (by norm_num)
theorem B1745981 : Blo 1160639 1745981 := bbase (se 3 (by rfl) ⟨327371, by rfl⟩ : syracuseStep 1745981 = 654743) (by norm_num)
theorem B1746005 : Blo 1160639 1746005 := bbase (se 8 (by rfl) ⟨10230, by rfl⟩ : syracuseStep 1746005 = 20461) (by norm_num)
theorem B1746029 : Blo 1160639 1746029 := bbase (se 3 (by rfl) ⟨327380, by rfl⟩ : syracuseStep 1746029 = 654761) (by norm_num)
theorem B1746053 : Blo 1160639 1746053 := bbase (se 4 (by rfl) ⟨163692, by rfl⟩ : syracuseStep 1746053 = 327385) (by norm_num)
theorem B1746077 : Blo 1160639 1746077 := bbase (se 3 (by rfl) ⟨327389, by rfl⟩ : syracuseStep 1746077 = 654779) (by norm_num)
theorem B1746101 : Blo 1160639 1746101 := bbase (se 5 (by rfl) ⟨81848, by rfl⟩ : syracuseStep 1746101 = 163697) (by norm_num)
theorem B1746125 : Blo 1160639 1746125 := bbase (se 3 (by rfl) ⟨327398, by rfl⟩ : syracuseStep 1746125 = 654797) (by norm_num)
theorem B1746149 : Blo 1160639 1746149 := bbase (se 4 (by rfl) ⟨163701, by rfl⟩ : syracuseStep 1746149 = 327403) (by norm_num)
theorem B1746173 : Blo 1160639 1746173 := bbase (se 3 (by rfl) ⟨327407, by rfl⟩ : syracuseStep 1746173 = 654815) (by norm_num)
theorem B1746197 : Blo 1160639 1746197 := bbase (se 6 (by rfl) ⟨40926, by rfl⟩ : syracuseStep 1746197 = 81853) (by norm_num)
theorem B1746221 : Blo 1160639 1746221 := bbase (se 3 (by rfl) ⟨327416, by rfl⟩ : syracuseStep 1746221 = 654833) (by norm_num)
theorem B6628661 : Blo 1160639 6628661 := bbase (se 5 (by rfl) ⟨310718, by rfl⟩ : syracuseStep 6628661 = 621437) (by norm_num)
theorem B1746245 : Blo 1160639 1746245 := bbase (se 4 (by rfl) ⟨163710, by rfl⟩ : syracuseStep 1746245 = 327421) (by norm_num)
theorem B1746269 : Blo 1160639 1746269 := bbase (se 3 (by rfl) ⟨327425, by rfl⟩ : syracuseStep 1746269 = 654851) (by norm_num)
theorem B1746293 : Blo 1160639 1746293 := bbase (se 5 (by rfl) ⟨81857, by rfl⟩ : syracuseStep 1746293 = 163715) (by norm_num)
theorem B1746317 : Blo 1160639 1746317 := bbase (se 3 (by rfl) ⟨327434, by rfl⟩ : syracuseStep 1746317 = 654869) (by norm_num)
theorem B1746341 : Blo 1160639 1746341 := bbase (se 4 (by rfl) ⟨163719, by rfl⟩ : syracuseStep 1746341 = 327439) (by norm_num)
theorem B1746365 : Blo 1160639 1746365 := bbase (se 3 (by rfl) ⟨327443, by rfl⟩ : syracuseStep 1746365 = 654887) (by norm_num)
theorem B6038981 : Blo 1160639 6038981 := bbase (se 4 (by rfl) ⟨566154, by rfl⟩ : syracuseStep 6038981 = 1132309) (by norm_num)
theorem B2794949 : Blo 1160639 2794949 := bbase (se 4 (by rfl) ⟨262026, by rfl⟩ : syracuseStep 2794949 = 524053) (by norm_num)
theorem B1746389 : Blo 1160639 1746389 := bbase (se 7 (by rfl) ⟨20465, by rfl⟩ : syracuseStep 1746389 = 40931) (by norm_num)
theorem B2205157 : Blo 1160639 2205157 := bbase (se 4 (by rfl) ⟨206733, by rfl⟩ : syracuseStep 2205157 = 413467) (by norm_num)
theorem B1746413 : Blo 1160639 1746413 := bbase (se 3 (by rfl) ⟨327452, by rfl⟩ : syracuseStep 1746413 = 654905) (by norm_num)
theorem B1746437 : Blo 1160639 1746437 := bbase (se 4 (by rfl) ⟨163728, by rfl⟩ : syracuseStep 1746437 = 327457) (by norm_num)
theorem B1746461 : Blo 1160639 1746461 := bbase (se 3 (by rfl) ⟨327461, by rfl⟩ : syracuseStep 1746461 = 654923) (by norm_num)
theorem B1746485 : Blo 1160639 1746485 := bbase (se 5 (by rfl) ⟨81866, by rfl⟩ : syracuseStep 1746485 = 163733) (by norm_num)
theorem B1746509 : Blo 1160639 1746509 := bbase (se 3 (by rfl) ⟨327470, by rfl⟩ : syracuseStep 1746509 = 654941) (by norm_num)
theorem B1746533 : Blo 1160639 1746533 := bbase (se 4 (by rfl) ⟨163737, by rfl⟩ : syracuseStep 1746533 = 327475) (by norm_num)
theorem B2205301 : Blo 1160639 2205301 := bbase (se 5 (by rfl) ⟨103373, by rfl⟩ : syracuseStep 2205301 = 206747) (by norm_num)
theorem B1746557 : Blo 1160639 1746557 := bbase (se 3 (by rfl) ⟨327479, by rfl⟩ : syracuseStep 1746557 = 654959) (by norm_num)
theorem B2795141 : Blo 1160639 2795141 := bbase (se 4 (by rfl) ⟨262044, by rfl⟩ : syracuseStep 2795141 = 524089) (by norm_num)
theorem B1746581 : Blo 1160639 1746581 := bbase (se 6 (by rfl) ⟨40935, by rfl⟩ : syracuseStep 1746581 = 81871) (by norm_num)
theorem B4957861 : Blo 1160639 4957861 := bbase (se 4 (by rfl) ⟨464799, by rfl⟩ : syracuseStep 4957861 = 929599) (by norm_num)
theorem B1746605 : Blo 1160639 1746605 := bbase (se 3 (by rfl) ⟨327488, by rfl⟩ : syracuseStep 1746605 = 654977) (by norm_num)
theorem B1746629 : Blo 1160639 1746629 := bbase (se 4 (by rfl) ⟨163746, by rfl⟩ : syracuseStep 1746629 = 327493) (by norm_num)
theorem B1746653 : Blo 1160639 1746653 := bbase (se 3 (by rfl) ⟨327497, by rfl⟩ : syracuseStep 1746653 = 654995) (by norm_num)
theorem B2795237 : Blo 1160639 2795237 := bbase (se 4 (by rfl) ⟨262053, by rfl⟩ : syracuseStep 2795237 = 524107) (by norm_num)
theorem B1746677 : Blo 1160639 1746677 := bbase (se 5 (by rfl) ⟨81875, by rfl⟩ : syracuseStep 1746677 = 163751) (by norm_num)
theorem B1746701 : Blo 1160639 1746701 := bbase (se 3 (by rfl) ⟨327506, by rfl⟩ : syracuseStep 1746701 = 655013) (by norm_num)
theorem B2205461 : Blo 1160639 2205461 := bbase (se 6 (by rfl) ⟨51690, by rfl⟩ : syracuseStep 2205461 = 103381) (by norm_num)
theorem B1746725 : Blo 1160639 1746725 := bbase (se 4 (by rfl) ⟨163755, by rfl⟩ : syracuseStep 1746725 = 327511) (by norm_num)
theorem B1746749 : Blo 1160639 1746749 := bbase (se 3 (by rfl) ⟨327515, by rfl⟩ : syracuseStep 1746749 = 655031) (by norm_num)
theorem B1746773 : Blo 1160639 1746773 := bbase (se 9 (by rfl) ⟨5117, by rfl⟩ : syracuseStep 1746773 = 10235) (by norm_num)
theorem B1746797 : Blo 1160639 1746797 := bbase (se 3 (by rfl) ⟨327524, by rfl⟩ : syracuseStep 1746797 = 655049) (by norm_num)
theorem B1746821 : Blo 1160639 1746821 := bbase (se 4 (by rfl) ⟨163764, by rfl⟩ : syracuseStep 1746821 = 327529) (by norm_num)
theorem B4532117 : Blo 1160639 4532117 := bbase (se 6 (by rfl) ⟨106221, by rfl⟩ : syracuseStep 4532117 = 212443) (by norm_num)
theorem B1746845 : Blo 1160639 1746845 := bbase (se 3 (by rfl) ⟨327533, by rfl⟩ : syracuseStep 1746845 = 655067) (by norm_num)
theorem B2205605 : Blo 1160639 2205605 := bbase (se 4 (by rfl) ⟨206775, by rfl⟩ : syracuseStep 2205605 = 413551) (by norm_num)
theorem B1746869 : Blo 1160639 1746869 := bbase (se 5 (by rfl) ⟨81884, by rfl⟩ : syracuseStep 1746869 = 163769) (by norm_num)
theorem B1746893 : Blo 1160639 1746893 := bbase (se 3 (by rfl) ⟨327542, by rfl⟩ : syracuseStep 1746893 = 655085) (by norm_num)
theorem B1746917 : Blo 1160639 1746917 := bbase (se 4 (by rfl) ⟨163773, by rfl⟩ : syracuseStep 1746917 = 327547) (by norm_num)
theorem B1746941 : Blo 1160639 1746941 := bbase (se 3 (by rfl) ⟨327551, by rfl⟩ : syracuseStep 1746941 = 655103) (by norm_num)
theorem B8366165 : Blo 1160639 8366165 := bbase (se 8 (by rfl) ⟨49020, by rfl⟩ : syracuseStep 8366165 = 98041) (by norm_num)
theorem B2205893 : Blo 1160639 2205893 := bbase (se 4 (by rfl) ⟨206802, by rfl⟩ : syracuseStep 2205893 = 413605) (by norm_num)
theorem B4466933 : Blo 1160639 4466933 := bbase (se 5 (by rfl) ⟨209387, by rfl⟩ : syracuseStep 4466933 = 418775) (by norm_num)
theorem B2206045 : Blo 1160639 2206045 := bbase (se 3 (by rfl) ⟨413633, by rfl⟩ : syracuseStep 2206045 = 827267) (by norm_num)
theorem B4958597 : Blo 1160639 4958597 := bbase (se 4 (by rfl) ⟨464868, by rfl⟩ : syracuseStep 4958597 = 929737) (by norm_num)
theorem B2206349 : Blo 1160639 2206349 := bbase (se 3 (by rfl) ⟨413690, by rfl⟩ : syracuseStep 2206349 = 827381) (by norm_num)
theorem B5876549 : Blo 1160639 5876549 := bbase (se 4 (by rfl) ⟨550926, by rfl⟩ : syracuseStep 5876549 = 1101853) (by norm_num)
theorem B5581669 : Blo 1160639 5581669 := bbase (se 4 (by rfl) ⟨523281, by rfl⟩ : syracuseStep 5581669 = 1046563) (by norm_num)
theorem B3976069 : Blo 1160639 3976069 := bbase (se 4 (by rfl) ⟨372756, by rfl⟩ : syracuseStep 3976069 = 745513) (by norm_num)
theorem B2207101 : Blo 1160639 2207101 := bbase (se 3 (by rfl) ⟨413831, by rfl⟩ : syracuseStep 2207101 = 827663) (by norm_num)
theorem B2207245 : Blo 1160639 2207245 := bbase (se 3 (by rfl) ⟨413858, by rfl⟩ : syracuseStep 2207245 = 827717) (by norm_num)
theorem B1257121 : Blo 1160639 1257121 := bbase (se 2 (by rfl) ⟨471420, by rfl⟩ : syracuseStep 1257121 = 942841) (by norm_num)
theorem B2207405 : Blo 1160639 2207405 := bbase (se 3 (by rfl) ⟨413888, by rfl⟩ : syracuseStep 2207405 = 827777) (by norm_num)
theorem B3976901 : Blo 1160639 3976901 := bbase (se 4 (by rfl) ⟨372834, by rfl⟩ : syracuseStep 3976901 = 745669) (by norm_num)
theorem B7450325 : Blo 1160639 7450325 := bbase (se 7 (by rfl) ⟨87308, by rfl⟩ : syracuseStep 7450325 = 174617) (by norm_num)
theorem B3780325 : Blo 1160639 3780325 := bbase (se 4 (by rfl) ⟨354405, by rfl⟩ : syracuseStep 3780325 = 708811) (by norm_num)
theorem B2207549 : Blo 1160639 2207549 := bbase (se 3 (by rfl) ⟨413915, by rfl⟩ : syracuseStep 2207549 = 827831) (by norm_num)
theorem B5976085 : Blo 1160639 5976085 := bbase (se 6 (by rfl) ⟨140064, by rfl⟩ : syracuseStep 5976085 = 280129) (by norm_num)
theorem B8368181 : Blo 1160639 8368181 := bbase (se 5 (by rfl) ⟨392258, by rfl⟩ : syracuseStep 8368181 = 784517) (by norm_num)
theorem B5877845 : Blo 1160639 5877845 := bbase (se 8 (by rfl) ⟨34440, by rfl⟩ : syracuseStep 5877845 = 68881) (by norm_num)
theorem B2207837 : Blo 1160639 2207837 := bbase (se 3 (by rfl) ⟨413969, by rfl⟩ : syracuseStep 2207837 = 827939) (by norm_num)
theorem B2797669 : Blo 1160639 2797669 := bbase (se 4 (by rfl) ⟨262281, by rfl⟩ : syracuseStep 2797669 = 524563) (by norm_num)
theorem B2207989 : Blo 1160639 2207989 := bbase (se 5 (by rfl) ⟨103499, by rfl⟩ : syracuseStep 2207989 = 206999) (by norm_num)
theorem B2798005 : Blo 1160639 2798005 := bbase (se 5 (by rfl) ⟨131156, by rfl⟩ : syracuseStep 2798005 = 262313) (by norm_num)
theorem B3355141 : Blo 1160639 3355141 := bbase (se 4 (by rfl) ⟨314544, by rfl⟩ : syracuseStep 3355141 = 629089) (by norm_num)
theorem B2208293 : Blo 1160639 2208293 := bbase (se 4 (by rfl) ⟨207027, by rfl⟩ : syracuseStep 2208293 = 414055) (by norm_num)
theorem B1324225 : Blo 1160639 1324225 := bbase (se 2 (by rfl) ⟨496584, by rfl⟩ : syracuseStep 1324225 = 993169) (by norm_num)
theorem B2209045 : Blo 1160639 2209045 := bbase (se 6 (by rfl) ⟨51774, by rfl⟩ : syracuseStep 2209045 = 103549) (by norm_num)
theorem B5879141 : Blo 1160639 5879141 := bbase (se 4 (by rfl) ⟨551169, by rfl⟩ : syracuseStep 5879141 = 1102339) (by norm_num)
theorem B2209189 : Blo 1160639 2209189 := bbase (se 4 (by rfl) ⟨207111, by rfl⟩ : syracuseStep 2209189 = 414223) (by norm_num)
theorem B2209349 : Blo 1160639 2209349 := bbase (se 4 (by rfl) ⟨207126, by rfl⟩ : syracuseStep 2209349 = 414253) (by norm_num)
theorem B4961893 : Blo 1160639 4961893 := bbase (se 4 (by rfl) ⟨465177, by rfl⟩ : syracuseStep 4961893 = 930355) (by norm_num)
theorem B3061373 : Blo 1160639 3061373 := bbase (se 3 (by rfl) ⟨574007, by rfl⟩ : syracuseStep 3061373 = 1148015) (by norm_num)
theorem B3356293 : Blo 1160639 3356293 := bbase (se 4 (by rfl) ⟨314652, by rfl⟩ : syracuseStep 3356293 = 629305) (by norm_num)
theorem B2209493 : Blo 1160639 2209493 := bbase (se 7 (by rfl) ⟨25892, by rfl⟩ : syracuseStep 2209493 = 51785) (by norm_num)
theorem B2013125 : Blo 1160639 2013125 := bbase (se 4 (by rfl) ⟨188730, by rfl⟩ : syracuseStep 2013125 = 377461) (by norm_num)
theorem B1259473 : Blo 1160639 1259473 := bbase (se 2 (by rfl) ⟨472302, by rfl⟩ : syracuseStep 1259473 = 944605) (by norm_num)
theorem B2209781 : Blo 1160639 2209781 := bbase (se 5 (by rfl) ⟨103583, by rfl⟩ : syracuseStep 2209781 = 207167) (by norm_num)
theorem B7944277 : Blo 1160639 7944277 := bbase (se 8 (by rfl) ⟨46548, by rfl⟩ : syracuseStep 7944277 = 93097) (by norm_num)
theorem B2209933 : Blo 1160639 2209933 := bbase (se 3 (by rfl) ⟨414362, by rfl⟩ : syracuseStep 2209933 = 828725) (by norm_num)
theorem B1653053 : Blo 1160639 1653053 := bbase (se 3 (by rfl) ⟨309947, by rfl⟩ : syracuseStep 1653053 = 619895) (by norm_num)
theorem B188627285 : Blo 1160639 188627285 := bbase (se 10 (by rfl) ⟨276309, by rfl⟩ : syracuseStep 188627285 = 552619) (by norm_num)
theorem B2210237 : Blo 1160639 2210237 := bbase (se 3 (by rfl) ⟨414419, by rfl⟩ : syracuseStep 2210237 = 828839) (by norm_num)
theorem B5880437 : Blo 1160639 5880437 := bbase (se 5 (by rfl) ⟨275645, by rfl⟩ : syracuseStep 5880437 = 551291) (by norm_num)
theorem B12270197 : Blo 1160639 12270197 := bbase (se 5 (by rfl) ⟨575165, by rfl⟩ : syracuseStep 12270197 = 1150331) (by norm_num)
theorem B10074773 : Blo 1160639 10074773 := bbase (se 6 (by rfl) ⟨236127, by rfl⟩ : syracuseStep 10074773 = 472255) (by norm_num)
theorem B1260257 : Blo 1160639 1260257 := bbase (se 2 (by rfl) ⟨472596, by rfl⟩ : syracuseStep 1260257 = 945193) (by norm_num)
theorem B7060213 : Blo 1160639 7060213 := bbase (se 5 (by rfl) ⟨330947, by rfl⟩ : syracuseStep 7060213 = 661895) (by norm_num)
theorem B1260353 : Blo 1160639 1260353 := bbase (se 2 (by rfl) ⟨472632, by rfl⟩ : syracuseStep 1260353 = 945265) (by norm_num)
theorem B22362965 : Blo 1160639 22362965 := bbase (se 9 (by rfl) ⟨65516, by rfl⟩ : syracuseStep 22362965 = 131033) (by norm_num)
theorem B5585861 : Blo 1160639 5585861 := bbase (se 4 (by rfl) ⟨523674, by rfl⟩ : syracuseStep 5585861 = 1047349) (by norm_num)
theorem B1194961 : Blo 1160639 1194961 := bbase (se 2 (by rfl) ⟨448110, by rfl⟩ : syracuseStep 1194961 = 896221) (by norm_num)
theorem B1260533 : Blo 1160639 1260533 := bbase (se 5 (by rfl) ⟨59087, by rfl⟩ : syracuseStep 1260533 = 118175) (by norm_num)
theorem B1653805 : Blo 1160639 1653805 := bbase (se 3 (by rfl) ⟨310088, by rfl⟩ : syracuseStep 1653805 = 620177) (by norm_num)
theorem B1326181 : Blo 1160639 1326181 := bbase (se 4 (by rfl) ⟨124329, by rfl⟩ : syracuseStep 1326181 = 248659) (by norm_num)
theorem B2210989 : Blo 1160639 2210989 := bbase (se 3 (by rfl) ⟨414560, by rfl⟩ : syracuseStep 2210989 = 829121) (by norm_num)
theorem B8830133 : Blo 1160639 8830133 := bbase (se 5 (by rfl) ⟨413912, by rfl⟩ : syracuseStep 8830133 = 827825) (by norm_num)
theorem B3980677 : Blo 1160639 3980677 := bbase (se 4 (by rfl) ⟨373188, by rfl⟩ : syracuseStep 3980677 = 746377) (by norm_num)
theorem B7945781 : Blo 1160639 7945781 := bbase (se 5 (by rfl) ⟨372458, by rfl⟩ : syracuseStep 7945781 = 744917) (by norm_num)
theorem B6274709 : Blo 1160639 6274709 := bbase (se 6 (by rfl) ⟨147063, by rfl⟩ : syracuseStep 6274709 = 294127) (by norm_num)
theorem B1195733 : Blo 1160639 1195733 := bbase (se 7 (by rfl) ⟨14012, by rfl⟩ : syracuseStep 1195733 = 28025) (by norm_num)
theorem B1490681 : Blo 1160639 1490681 := bbase (se 2 (by rfl) ⟨559005, by rfl⟩ : syracuseStep 1490681 = 1118011) (by norm_num)
theorem B1654597 : Blo 1160639 1654597 := bbase (se 4 (by rfl) ⟨155118, by rfl⟩ : syracuseStep 1654597 = 310237) (by norm_num)
theorem B2178893 : Blo 1160639 2178893 := bbase (se 3 (by rfl) ⟨408542, by rfl⟩ : syracuseStep 2178893 = 817085) (by norm_num)
theorem B174407509 : Blo 1160639 174407509 := bbase (se 9 (by rfl) ⟨510959, by rfl⟩ : syracuseStep 174407509 = 1021919) (by norm_num)
theorem B5881733 : Blo 1160639 5881733 := bbase (se 4 (by rfl) ⟨551412, by rfl⟩ : syracuseStep 5881733 = 1102825) (by norm_num)
theorem B13254677 : Blo 1160639 13254677 := bbase (se 6 (by rfl) ⟨310656, by rfl⟩ : syracuseStep 13254677 = 621313) (by norm_num)
theorem B1654933 : Blo 1160639 1654933 := bbase (se 6 (by rfl) ⟨38787, by rfl⟩ : syracuseStep 1654933 = 77575) (by norm_num)
theorem B4538549 : Blo 1160639 4538549 := bbase (se 5 (by rfl) ⟨212744, by rfl⟩ : syracuseStep 4538549 = 425489) (by norm_num)
theorem B1327385 : Blo 1160639 1327385 := bbase (se 2 (by rfl) ⟨497769, by rfl⟩ : syracuseStep 1327385 = 995539) (by norm_num)
theorem B1655149 : Blo 1160639 1655149 := bbase (se 3 (by rfl) ⟨310340, by rfl⟩ : syracuseStep 1655149 = 620681) (by norm_num)
theorem B8733109 : Blo 1160639 8733109 := bbase (se 5 (by rfl) ⟨409364, by rfl⟩ : syracuseStep 8733109 = 818729) (by norm_num)
theorem B4964885 : Blo 1160639 4964885 := bbase (se 6 (by rfl) ⟨116364, by rfl⟩ : syracuseStep 4964885 = 232729) (by norm_num)
theorem B1655525 : Blo 1160639 1655525 := bbase (se 4 (by rfl) ⟨155205, by rfl⟩ : syracuseStep 1655525 = 310411) (by norm_num)
theorem B3720293 : Blo 1160639 3720293 := bbase (se 4 (by rfl) ⟨348777, by rfl⟩ : syracuseStep 3720293 = 697555) (by norm_num)
theorem B5031013 : Blo 1160639 5031013 := bbase (se 4 (by rfl) ⟨471657, by rfl⟩ : syracuseStep 5031013 = 943315) (by norm_num)
theorem B5883029 : Blo 1160639 5883029 := bbase (se 6 (by rfl) ⟨137883, by rfl⟩ : syracuseStep 5883029 = 275767) (by norm_num)
theorem B3720421 : Blo 1160639 3720421 := bbase (se 4 (by rfl) ⟨348789, by rfl⟩ : syracuseStep 3720421 = 697579) (by norm_num)
theorem B2835685 : Blo 1160639 2835685 := bbase (se 4 (by rfl) ⟨265845, by rfl⟩ : syracuseStep 2835685 = 531691) (by norm_num)
theorem B1885421 : Blo 1160639 1885421 := bbase (se 3 (by rfl) ⟨353516, by rfl⟩ : syracuseStep 1885421 = 707033) (by norm_num)
theorem B4408613 : Blo 1160639 4408613 := bbase (se 4 (by rfl) ⟨413307, by rfl⟩ : syracuseStep 4408613 = 826615) (by norm_num)
theorem B1361305 : Blo 1160639 1361305 := bbase (se 2 (by rfl) ⟨510489, by rfl⟩ : syracuseStep 1361305 = 1020979) (by norm_num)
theorem B4965893 : Blo 1160639 4965893 := bbase (se 4 (by rfl) ⟨465552, by rfl⟩ : syracuseStep 4965893 = 931105) (by norm_num)
theorem B4408901 : Blo 1160639 4408901 := bbase (se 4 (by rfl) ⟨413334, by rfl⟩ : syracuseStep 4408901 = 826669) (by norm_num)
theorem B3917429 : Blo 1160639 3917429 := bbase (se 5 (by rfl) ⟨183629, by rfl⟩ : syracuseStep 3917429 = 367259) (by norm_num)
theorem B7456373 : Blo 1160639 7456373 := bbase (se 5 (by rfl) ⟨349517, by rfl⟩ : syracuseStep 7456373 = 699035) (by norm_num)
theorem B3917861 : Blo 1160639 3917861 := bbase (se 4 (by rfl) ⟨367299, by rfl⟩ : syracuseStep 3917861 = 734599) (by norm_num)
theorem B1656949 : Blo 1160639 1656949 := bbase (se 5 (by rfl) ⟨77669, by rfl⟩ : syracuseStep 1656949 = 155339) (by norm_num)
theorem B1493201 : Blo 1160639 1493201 := bbase (se 2 (by rfl) ⟨559950, by rfl⟩ : syracuseStep 1493201 = 1119901) (by norm_num)
theorem B1395029 : Blo 1160639 1395029 := bbase (se 10 (by rfl) ⟨2043, by rfl⟩ : syracuseStep 1395029 = 4087) (by norm_num)
theorem B1493365 : Blo 1160639 1493365 := bbase (se 5 (by rfl) ⟨70001, by rfl⟩ : syracuseStep 1493365 = 140003) (by norm_num)
theorem B5884325 : Blo 1160639 5884325 := bbase (se 4 (by rfl) ⟨551655, by rfl⟩ : syracuseStep 5884325 = 1103311) (by norm_num)
theorem B3918293 : Blo 1160639 3918293 := bbase (se 7 (by rfl) ⟨45917, by rfl⟩ : syracuseStep 3918293 = 91835) (by norm_num)
theorem B1657541 : Blo 1160639 1657541 := bbase (se 4 (by rfl) ⟨155394, by rfl⟩ : syracuseStep 1657541 = 310789) (by norm_num)
theorem B4410085 : Blo 1160639 4410085 := bbase (se 4 (by rfl) ⟨413445, by rfl⟩ : syracuseStep 4410085 = 826891) (by norm_num)
theorem B1657621 : Blo 1160639 1657621 := bbase (se 6 (by rfl) ⟨38850, by rfl⟩ : syracuseStep 1657621 = 77701) (by norm_num)
theorem B1887085 : Blo 1160639 1887085 := bbase (se 3 (by rfl) ⟨353828, by rfl⟩ : syracuseStep 1887085 = 707657) (by norm_num)
theorem B3918725 : Blo 1160639 3918725 := bbase (se 4 (by rfl) ⟨367380, by rfl⟩ : syracuseStep 3918725 = 734761) (by norm_num)
theorem B1657741 : Blo 1160639 1657741 := bbase (se 3 (by rfl) ⟨310826, by rfl⟩ : syracuseStep 1657741 = 621653) (by norm_num)
theorem B1657837 : Blo 1160639 1657837 := bbase (se 3 (by rfl) ⟨310844, by rfl⟩ : syracuseStep 1657837 = 621689) (by norm_num)
theorem B4410389 : Blo 1160639 4410389 := bbase (se 6 (by rfl) ⟨103368, by rfl⟩ : syracuseStep 4410389 = 206737) (by norm_num)
theorem B4967669 : Blo 1160639 4967669 := bbase (se 5 (by rfl) ⟨232859, by rfl⟩ : syracuseStep 4967669 = 465719) (by norm_num)
theorem B3919157 : Blo 1160639 3919157 := bbase (se 5 (by rfl) ⟨183710, by rfl⟩ : syracuseStep 3919157 = 367421) (by norm_num)
theorem B1396225 : Blo 1160639 1396225 := bbase (se 2 (by rfl) ⟨523584, by rfl⟩ : syracuseStep 1396225 = 1047169) (by norm_num)
theorem B1396297 : Blo 1160639 1396297 := bbase (se 2 (by rfl) ⟨523611, by rfl⟩ : syracuseStep 1396297 = 1047223) (by norm_num)
theorem B5885621 : Blo 1160639 5885621 := bbase (se 5 (by rfl) ⟨275888, by rfl⟩ : syracuseStep 5885621 = 551777) (by norm_num)
theorem B3919589 : Blo 1160639 3919589 := bbase (se 4 (by rfl) ⟨367461, by rfl⟩ : syracuseStep 3919589 = 734923) (by norm_num)
theorem B3723317 : Blo 1160639 3723317 := bbase (se 5 (by rfl) ⟨174530, by rfl⟩ : syracuseStep 3723317 = 349061) (by norm_num)
theorem B3920021 : Blo 1160639 3920021 := bbase (se 6 (by rfl) ⟨91875, by rfl⟩ : syracuseStep 3920021 = 183751) (by norm_num)
theorem B1397297 : Blo 1160639 1397297 := bbase (se 2 (by rfl) ⟨523986, by rfl⟩ : syracuseStep 1397297 = 1047973) (by norm_num)
theorem B3920453 : Blo 1160639 3920453 := bbase (se 4 (by rfl) ⟨367542, by rfl⟩ : syracuseStep 3920453 = 735085) (by norm_num)
theorem B9425621 : Blo 1160639 9425621 := bbase (se 7 (by rfl) ⟨110456, by rfl⟩ : syracuseStep 9425621 = 220913) (by norm_num)
theorem B5886917 : Blo 1160639 5886917 := bbase (se 4 (by rfl) ⟨551898, by rfl⟩ : syracuseStep 5886917 = 1103797) (by norm_num)
theorem B3920885 : Blo 1160639 3920885 := bbase (se 5 (by rfl) ⟨183791, by rfl⟩ : syracuseStep 3920885 = 367583) (by norm_num)
theorem B3822661 : Blo 1160639 3822661 := bbase (se 4 (by rfl) ⟨358374, by rfl⟩ : syracuseStep 3822661 = 716749) (by norm_num)
theorem B2937941 : Blo 1160639 2937941 := bbase (se 8 (by rfl) ⟨17214, by rfl⟩ : syracuseStep 2937941 = 34429) (by norm_num)
theorem B4412501 : Blo 1160639 4412501 := bbase (se 8 (by rfl) ⟨25854, by rfl⟩ : syracuseStep 4412501 = 51709) (by norm_num)
theorem B10605653 : Blo 1160639 10605653 := bbase (se 8 (by rfl) ⟨62142, by rfl⟩ : syracuseStep 10605653 = 124285) (by norm_num)
theorem B4183253 : Blo 1160639 4183253 := bbase (se 7 (by rfl) ⟨49022, by rfl⟩ : syracuseStep 4183253 = 98045) (by norm_num)
theorem B1397989 : Blo 1160639 1397989 := bbase (se 4 (by rfl) ⟨131061, by rfl⟩ : syracuseStep 1397989 = 262123) (by norm_num)
theorem B1397993 : Blo 1160639 1397993 := bbase (se 2 (by rfl) ⟨524247, by rfl⟩ : syracuseStep 1397993 = 1048495) (by norm_num)
theorem B2938133 : Blo 1160639 2938133 := bbase (se 6 (by rfl) ⟨68862, by rfl⟩ : syracuseStep 2938133 = 137725) (by norm_num)
theorem B4412789 : Blo 1160639 4412789 := bbase (se 5 (by rfl) ⟨206849, by rfl⟩ : syracuseStep 4412789 = 413699) (by norm_num)
theorem B3921317 : Blo 1160639 3921317 := bbase (se 4 (by rfl) ⟨367623, by rfl⟩ : syracuseStep 3921317 = 735247) (by norm_num)
theorem B9917909 : Blo 1160639 9917909 := bbase (se 7 (by rfl) ⟨116225, by rfl⟩ : syracuseStep 9917909 = 232451) (by norm_num)
theorem B2479709 : Blo 1160639 2479709 := bbase (se 3 (by rfl) ⟨464945, by rfl⟩ : syracuseStep 2479709 = 929891) (by norm_num)
theorem B2938477 : Blo 1160639 2938477 := bbase (se 3 (by rfl) ⟨550964, by rfl⟩ : syracuseStep 2938477 = 1101929) (by norm_num)
theorem B5297861 : Blo 1160639 5297861 := bbase (se 4 (by rfl) ⟨496674, by rfl⟩ : syracuseStep 5297861 = 993349) (by norm_num)
theorem B2938589 : Blo 1160639 2938589 := bbase (se 3 (by rfl) ⟨550985, by rfl⟩ : syracuseStep 2938589 = 1101971) (by norm_num)
theorem B1398493 : Blo 1160639 1398493 := bbase (se 3 (by rfl) ⟨262217, by rfl⟩ : syracuseStep 1398493 = 524435) (by norm_num)
theorem B2479853 : Blo 1160639 2479853 := bbase (se 3 (by rfl) ⟨464972, by rfl⟩ : syracuseStep 2479853 = 929945) (by norm_num)
theorem B3921749 : Blo 1160639 3921749 := bbase (se 9 (by rfl) ⟨11489, by rfl⟩ : syracuseStep 3921749 = 22979) (by norm_num)
theorem B1988477 : Blo 1160639 1988477 := bbase (se 3 (by rfl) ⟨372839, by rfl⟩ : syracuseStep 1988477 = 745679) (by norm_num)
theorem B19879829 : Blo 1160639 19879829 := bbase (se 6 (by rfl) ⟨465933, by rfl⟩ : syracuseStep 19879829 = 931867) (by norm_num)
theorem B2938781 : Blo 1160639 2938781 := bbase (se 3 (by rfl) ⟨551021, by rfl⟩ : syracuseStep 2938781 = 1102043) (by norm_num)
theorem B2480213 : Blo 1160639 2480213 := bbase (se 8 (by rfl) ⟨14532, by rfl⟩ : syracuseStep 2480213 = 29065) (by norm_num)
theorem B6707285 : Blo 1160639 6707285 := bbase (se 8 (by rfl) ⟨39300, by rfl⟩ : syracuseStep 6707285 = 78601) (by norm_num)
theorem B1398877 : Blo 1160639 1398877 := bbase (se 3 (by rfl) ⟨262289, by rfl⟩ : syracuseStep 1398877 = 524579) (by norm_num)
theorem B3725509 : Blo 1160639 3725509 := bbase (se 4 (by rfl) ⟨349266, by rfl⟩ : syracuseStep 3725509 = 698533) (by norm_num)
theorem B5888213 : Blo 1160639 5888213 := bbase (se 7 (by rfl) ⟨69002, by rfl⟩ : syracuseStep 5888213 = 138005) (by norm_num)
theorem B2939125 : Blo 1160639 2939125 := bbase (se 5 (by rfl) ⟨137771, by rfl⟩ : syracuseStep 2939125 = 275543) (by norm_num)
theorem B3922181 : Blo 1160639 3922181 := bbase (se 4 (by rfl) ⟨367704, by rfl⟩ : syracuseStep 3922181 = 735409) (by norm_num)
theorem B2611493 : Blo 1160639 2611493 := bbase (se 4 (by rfl) ⟨244827, by rfl⟩ : syracuseStep 2611493 = 489655) (by norm_num)
theorem B2939237 : Blo 1160639 2939237 := bbase (se 4 (by rfl) ⟨275553, by rfl⟩ : syracuseStep 2939237 = 551107) (by norm_num)
theorem B2611565 : Blo 1160639 2611565 := bbase (se 3 (by rfl) ⟨489668, by rfl⟩ : syracuseStep 2611565 = 979337) (by norm_num)
theorem B2611637 : Blo 1160639 2611637 := bbase (se 5 (by rfl) ⟨122420, by rfl⟩ : syracuseStep 2611637 = 244841) (by norm_num)
theorem B2611709 : Blo 1160639 2611709 := bbase (se 3 (by rfl) ⟨489695, by rfl⟩ : syracuseStep 2611709 = 979391) (by norm_num)
theorem B4184581 : Blo 1160639 4184581 := bbase (se 4 (by rfl) ⟨392304, by rfl⟩ : syracuseStep 4184581 = 784609) (by norm_num)
theorem B4413973 : Blo 1160639 4413973 := bbase (se 6 (by rfl) ⟨103452, by rfl⟩ : syracuseStep 4413973 = 206905) (by norm_num)
theorem B2939429 : Blo 1160639 2939429 := bbase (se 4 (by rfl) ⟨275571, by rfl⟩ : syracuseStep 2939429 = 551143) (by norm_num)
theorem B2611781 : Blo 1160639 2611781 := bbase (se 4 (by rfl) ⟨244854, by rfl⟩ : syracuseStep 2611781 = 489709) (by norm_num)
theorem B2611853 : Blo 1160639 2611853 := bbase (se 3 (by rfl) ⟨489722, by rfl⟩ : syracuseStep 2611853 = 979445) (by norm_num)
theorem B2120357 : Blo 1160639 2120357 := bbase (se 4 (by rfl) ⟨198783, by rfl⟩ : syracuseStep 2120357 = 397567) (by norm_num)
theorem B3922613 : Blo 1160639 3922613 := bbase (se 5 (by rfl) ⟨183872, by rfl⟩ : syracuseStep 3922613 = 367745) (by norm_num)
theorem B2611925 : Blo 1160639 2611925 := bbase (se 7 (by rfl) ⟨30608, by rfl⟩ : syracuseStep 2611925 = 61217) (by norm_num)
theorem B8837909 : Blo 1160639 8837909 := bbase (se 6 (by rfl) ⟨207138, by rfl⟩ : syracuseStep 8837909 = 414277) (by norm_num)
theorem B2611997 : Blo 1160639 2611997 := bbase (se 3 (by rfl) ⟨489749, by rfl⟩ : syracuseStep 2611997 = 979499) (by norm_num)
theorem B4414277 : Blo 1160639 4414277 := bbase (se 4 (by rfl) ⟨413838, by rfl⟩ : syracuseStep 4414277 = 827677) (by norm_num)
theorem B2612069 : Blo 1160639 2612069 := bbase (se 4 (by rfl) ⟨244881, by rfl⟩ : syracuseStep 2612069 = 489763) (by norm_num)
theorem B2939773 : Blo 1160639 2939773 := bbase (se 3 (by rfl) ⟨551207, by rfl⟩ : syracuseStep 2939773 = 1102415) (by norm_num)
theorem B2612141 : Blo 1160639 2612141 := bbase (se 3 (by rfl) ⟨489776, by rfl⟩ : syracuseStep 2612141 = 979553) (by norm_num)
theorem B2481101 : Blo 1160639 2481101 := bbase (se 3 (by rfl) ⟨465206, by rfl⟩ : syracuseStep 2481101 = 930413) (by norm_num)
theorem B2939885 : Blo 1160639 2939885 := bbase (se 3 (by rfl) ⟨551228, by rfl⟩ : syracuseStep 2939885 = 1102457) (by norm_num)
theorem B2612213 : Blo 1160639 2612213 := bbase (se 5 (by rfl) ⟨122447, by rfl⟩ : syracuseStep 2612213 = 244895) (by norm_num)
theorem B3726341 : Blo 1160639 3726341 := bbase (se 4 (by rfl) ⟨349344, by rfl⟩ : syracuseStep 3726341 = 698689) (by norm_num)
theorem B2612285 : Blo 1160639 2612285 := bbase (se 3 (by rfl) ⟨489803, by rfl⟩ : syracuseStep 2612285 = 979607) (by norm_num)
theorem B3923045 : Blo 1160639 3923045 := bbase (se 4 (by rfl) ⟨367785, by rfl⟩ : syracuseStep 3923045 = 735571) (by norm_num)
theorem B2612357 : Blo 1160639 2612357 := bbase (se 4 (by rfl) ⟨244908, by rfl⟩ : syracuseStep 2612357 = 489817) (by norm_num)
theorem B2940077 : Blo 1160639 2940077 := bbase (se 3 (by rfl) ⟨551264, by rfl⟩ : syracuseStep 2940077 = 1102529) (by norm_num)
theorem B2481349 : Blo 1160639 2481349 := bbase (se 4 (by rfl) ⟨232626, by rfl⟩ : syracuseStep 2481349 = 465253) (by norm_num)
theorem B2612429 : Blo 1160639 2612429 := bbase (se 3 (by rfl) ⟨489830, by rfl⟩ : syracuseStep 2612429 = 979661) (by norm_num)
theorem B2612501 : Blo 1160639 2612501 := bbase (se 6 (by rfl) ⟨61230, by rfl⟩ : syracuseStep 2612501 = 122461) (by norm_num)
theorem B14736725 : Blo 1160639 14736725 := bbase (se 11 (by rfl) ⟨10793, by rfl⟩ : syracuseStep 14736725 = 21587) (by norm_num)
theorem B2612573 : Blo 1160639 2612573 := bbase (se 3 (by rfl) ⟨489857, by rfl⟩ : syracuseStep 2612573 = 979715) (by norm_num)
theorem B2612645 : Blo 1160639 2612645 := bbase (se 4 (by rfl) ⟨244935, by rfl⟩ : syracuseStep 2612645 = 489871) (by norm_num)
theorem B4971941 : Blo 1160639 4971941 := bbase (se 4 (by rfl) ⟨466119, by rfl⟩ : syracuseStep 4971941 = 932239) (by norm_num)
theorem B5889509 : Blo 1160639 5889509 := bbase (se 4 (by rfl) ⟨552141, by rfl⟩ : syracuseStep 5889509 = 1104283) (by norm_num)
theorem B2612717 : Blo 1160639 2612717 := bbase (se 3 (by rfl) ⟨489884, by rfl⟩ : syracuseStep 2612717 = 979769) (by norm_num)
theorem B2940421 : Blo 1160639 2940421 := bbase (se 4 (by rfl) ⟨275664, by rfl⟩ : syracuseStep 2940421 = 551329) (by norm_num)
theorem B3923477 : Blo 1160639 3923477 := bbase (se 6 (by rfl) ⟨91956, by rfl⟩ : syracuseStep 3923477 = 183913) (by norm_num)
theorem B2612789 : Blo 1160639 2612789 := bbase (se 5 (by rfl) ⟨122474, by rfl⟩ : syracuseStep 2612789 = 244949) (by norm_num)
theorem B2940533 : Blo 1160639 2940533 := bbase (se 5 (by rfl) ⟨137837, by rfl⟩ : syracuseStep 2940533 = 275675) (by norm_num)
theorem B5594741 : Blo 1160639 5594741 := bbase (se 5 (by rfl) ⟨262253, by rfl⟩ : syracuseStep 5594741 = 524507) (by norm_num)
theorem B2612861 : Blo 1160639 2612861 := bbase (se 3 (by rfl) ⟨489911, by rfl⟩ : syracuseStep 2612861 = 979823) (by norm_num)
theorem B2481853 : Blo 1160639 2481853 := bbase (se 3 (by rfl) ⟨465347, by rfl⟩ : syracuseStep 2481853 = 930695) (by norm_num)
theorem B1859269 : Blo 1160639 1859269 := bbase (se 4 (by rfl) ⟨174306, by rfl⟩ : syracuseStep 1859269 = 348613) (by norm_num)
theorem B2612933 : Blo 1160639 2612933 := bbase (se 4 (by rfl) ⟨244962, by rfl⟩ : syracuseStep 2612933 = 489925) (by norm_num)
theorem B2613005 : Blo 1160639 2613005 := bbase (se 3 (by rfl) ⟨489938, by rfl⟩ : syracuseStep 2613005 = 979877) (by norm_num)
theorem B2940725 : Blo 1160639 2940725 := bbase (se 5 (by rfl) ⟨137846, by rfl⟩ : syracuseStep 2940725 = 275693) (by norm_num)
theorem B2613077 : Blo 1160639 2613077 := bbase (se 9 (by rfl) ⟨7655, by rfl⟩ : syracuseStep 2613077 = 15311) (by norm_num)
theorem B2613149 : Blo 1160639 2613149 := bbase (se 3 (by rfl) ⟨489965, by rfl⟩ : syracuseStep 2613149 = 979931) (by norm_num)
theorem B4186021 : Blo 1160639 4186021 := bbase (se 4 (by rfl) ⟨392439, by rfl⟩ : syracuseStep 4186021 = 784879) (by norm_num)
theorem B3923909 : Blo 1160639 3923909 := bbase (se 4 (by rfl) ⟨367866, by rfl⟩ : syracuseStep 3923909 = 735733) (by norm_num)
theorem B2613221 : Blo 1160639 2613221 := bbase (se 4 (by rfl) ⟨244989, by rfl⟩ : syracuseStep 2613221 = 489979) (by norm_num)
theorem B2613293 : Blo 1160639 2613293 := bbase (se 3 (by rfl) ⟨489992, by rfl⟩ : syracuseStep 2613293 = 979985) (by norm_num)
theorem B4481093 : Blo 1160639 4481093 := bbase (se 4 (by rfl) ⟨420102, by rfl⟩ : syracuseStep 4481093 = 840205) (by norm_num)
theorem B2613365 : Blo 1160639 2613365 := bbase (se 5 (by rfl) ⟨122501, by rfl⟩ : syracuseStep 2613365 = 245003) (by norm_num)
theorem B2941069 : Blo 1160639 2941069 := bbase (se 3 (by rfl) ⟨551450, by rfl⟩ : syracuseStep 2941069 = 1102901) (by norm_num)
theorem B2613437 : Blo 1160639 2613437 := bbase (se 3 (by rfl) ⟨490019, by rfl⟩ : syracuseStep 2613437 = 980039) (by norm_num)
theorem B1990885 : Blo 1160639 1990885 := bbase (se 4 (by rfl) ⟨186645, by rfl⟩ : syracuseStep 1990885 = 373291) (by norm_num)
theorem B2941181 : Blo 1160639 2941181 := bbase (se 3 (by rfl) ⟨551471, by rfl⟩ : syracuseStep 2941181 = 1102943) (by norm_num)
theorem B2613509 : Blo 1160639 2613509 := bbase (se 4 (by rfl) ⟨245016, by rfl⟩ : syracuseStep 2613509 = 490033) (by norm_num)
theorem B2613581 : Blo 1160639 2613581 := bbase (se 3 (by rfl) ⟨490046, by rfl⟩ : syracuseStep 2613581 = 980093) (by norm_num)
theorem B1859941 : Blo 1160639 1859941 := bbase (se 4 (by rfl) ⟨174369, by rfl⟩ : syracuseStep 1859941 = 348739) (by norm_num)
theorem B3924341 : Blo 1160639 3924341 := bbase (se 5 (by rfl) ⟨183953, by rfl⟩ : syracuseStep 3924341 = 367907) (by norm_num)
theorem B2613653 : Blo 1160639 2613653 := bbase (se 6 (by rfl) ⟨61257, by rfl⟩ : syracuseStep 2613653 = 122515) (by norm_num)
theorem B2941373 : Blo 1160639 2941373 := bbase (se 3 (by rfl) ⟨551507, by rfl⟩ : syracuseStep 2941373 = 1103015) (by norm_num)
theorem B2613725 : Blo 1160639 2613725 := bbase (se 3 (by rfl) ⟨490073, by rfl⟩ : syracuseStep 2613725 = 980147) (by norm_num)
theorem B2613797 : Blo 1160639 2613797 := bbase (se 4 (by rfl) ⟨245043, by rfl⟩ : syracuseStep 2613797 = 490087) (by norm_num)
theorem B4481573 : Blo 1160639 4481573 := bbase (se 4 (by rfl) ⟨420147, by rfl⟩ : syracuseStep 4481573 = 840295) (by norm_num)
theorem B2482741 : Blo 1160639 2482741 := bbase (se 5 (by rfl) ⟨116378, by rfl⟩ : syracuseStep 2482741 = 232757) (by norm_num)
theorem B2613869 : Blo 1160639 2613869 := bbase (se 3 (by rfl) ⟨490100, by rfl⟩ : syracuseStep 2613869 = 980201) (by norm_num)
theorem B2613941 : Blo 1160639 2613941 := bbase (se 5 (by rfl) ⟨122528, by rfl⟩ : syracuseStep 2613941 = 245057) (by norm_num)
theorem B5890805 : Blo 1160639 5890805 := bbase (se 5 (by rfl) ⟨276131, by rfl⟩ : syracuseStep 5890805 = 552263) (by norm_num)
theorem B2614013 : Blo 1160639 2614013 := bbase (se 3 (by rfl) ⟨490127, by rfl⟩ : syracuseStep 2614013 = 980255) (by norm_num)
theorem B2941717 : Blo 1160639 2941717 := bbase (se 6 (by rfl) ⟨68946, by rfl⟩ : syracuseStep 2941717 = 137893) (by norm_num)
theorem B3924773 : Blo 1160639 3924773 := bbase (se 4 (by rfl) ⟨367947, by rfl⟩ : syracuseStep 3924773 = 735895) (by norm_num)
theorem B1958701 : Blo 1160639 1958701 := bbase (se 3 (by rfl) ⟨367256, by rfl⟩ : syracuseStep 1958701 = 734513) (by norm_num)
theorem B2614085 : Blo 1160639 2614085 := bbase (se 4 (by rfl) ⟨245070, by rfl⟩ : syracuseStep 2614085 = 490141) (by norm_num)
theorem B3728213 : Blo 1160639 3728213 := bbase (se 9 (by rfl) ⟨10922, by rfl⟩ : syracuseStep 3728213 = 21845) (by norm_num)
theorem B1958789 : Blo 1160639 1958789 := bbase (se 4 (by rfl) ⟨183636, by rfl⟩ : syracuseStep 1958789 = 367273) (by norm_num)
theorem B2941829 : Blo 1160639 2941829 := bbase (se 4 (by rfl) ⟨275796, by rfl⟩ : syracuseStep 2941829 = 551593) (by norm_num)
theorem B4416389 : Blo 1160639 4416389 := bbase (se 4 (by rfl) ⟨414036, by rfl⟩ : syracuseStep 4416389 = 828073) (by norm_num)
theorem B2614157 : Blo 1160639 2614157 := bbase (se 3 (by rfl) ⟨490154, by rfl⟩ : syracuseStep 2614157 = 980309) (by norm_num)
theorem B2614229 : Blo 1160639 2614229 := bbase (se 7 (by rfl) ⟨30635, by rfl⟩ : syracuseStep 2614229 = 61271) (by norm_num)
theorem B1958917 : Blo 1160639 1958917 := bbase (se 4 (by rfl) ⟨183648, by rfl⟩ : syracuseStep 1958917 = 367297) (by norm_num)
theorem B2614301 : Blo 1160639 2614301 := bbase (se 3 (by rfl) ⟨490181, by rfl⟩ : syracuseStep 2614301 = 980363) (by norm_num)
theorem B2483237 : Blo 1160639 2483237 := bbase (se 4 (by rfl) ⟨232803, by rfl⟩ : syracuseStep 2483237 = 465607) (by norm_num)
theorem B7070773 : Blo 1160639 7070773 := bbase (se 5 (by rfl) ⟨331442, by rfl⟩ : syracuseStep 7070773 = 662885) (by norm_num)
theorem B2942021 : Blo 1160639 2942021 := bbase (se 4 (by rfl) ⟨275814, by rfl⟩ : syracuseStep 2942021 = 551629) (by norm_num)
theorem B5104709 : Blo 1160639 5104709 := bbase (se 4 (by rfl) ⟨478566, by rfl⟩ : syracuseStep 5104709 = 957133) (by norm_num)
theorem B1959005 : Blo 1160639 1959005 := bbase (se 3 (by rfl) ⟨367313, by rfl⟩ : syracuseStep 1959005 = 734627) (by norm_num)
theorem B2614373 : Blo 1160639 2614373 := bbase (se 4 (by rfl) ⟨245097, by rfl⟩ : syracuseStep 2614373 = 490195) (by norm_num)
theorem B4973717 : Blo 1160639 4973717 := bbase (se 6 (by rfl) ⟨116571, by rfl⟩ : syracuseStep 4973717 = 233143) (by norm_num)
theorem B4416677 : Blo 1160639 4416677 := bbase (se 4 (by rfl) ⟨414063, by rfl⟩ : syracuseStep 4416677 = 828127) (by norm_num)
theorem B2614445 : Blo 1160639 2614445 := bbase (se 3 (by rfl) ⟨490208, by rfl⟩ : syracuseStep 2614445 = 980417) (by norm_num)
theorem B3925205 : Blo 1160639 3925205 := bbase (se 7 (by rfl) ⟨45998, by rfl⟩ : syracuseStep 3925205 = 91997) (by norm_num)
theorem B1959133 : Blo 1160639 1959133 := bbase (se 3 (by rfl) ⟨367337, by rfl⟩ : syracuseStep 1959133 = 734675) (by norm_num)
theorem B2614517 : Blo 1160639 2614517 := bbase (se 5 (by rfl) ⟨122555, by rfl⟩ : syracuseStep 2614517 = 245111) (by norm_num)
theorem B2123029 : Blo 1160639 2123029 := bbase (se 6 (by rfl) ⟨49758, by rfl⟩ : syracuseStep 2123029 = 99517) (by norm_num)
theorem B1959221 : Blo 1160639 1959221 := bbase (se 5 (by rfl) ⟨91838, by rfl⟩ : syracuseStep 1959221 = 183677) (by norm_num)
theorem B2614589 : Blo 1160639 2614589 := bbase (se 3 (by rfl) ⟨490235, by rfl⟩ : syracuseStep 2614589 = 980471) (by norm_num)
theorem B1860941 : Blo 1160639 1860941 := bbase (se 3 (by rfl) ⟨348926, by rfl⟩ : syracuseStep 1860941 = 697853) (by norm_num)
theorem B12739925 : Blo 1160639 12739925 := bbase (se 12 (by rfl) ⟨4665, by rfl⟩ : syracuseStep 12739925 = 9331) (by norm_num)
theorem B2614661 : Blo 1160639 2614661 := bbase (se 4 (by rfl) ⟨245124, by rfl⟩ : syracuseStep 2614661 = 490249) (by norm_num)
theorem B4973957 : Blo 1160639 4973957 := bbase (se 4 (by rfl) ⟨466308, by rfl⟩ : syracuseStep 4973957 = 932617) (by norm_num)
theorem B2942365 : Blo 1160639 2942365 := bbase (se 3 (by rfl) ⟨551693, by rfl⟩ : syracuseStep 2942365 = 1103387) (by norm_num)
theorem B1959349 : Blo 1160639 1959349 := bbase (se 5 (by rfl) ⟨91844, by rfl⟩ : syracuseStep 1959349 = 183689) (by norm_num)
theorem B2614733 : Blo 1160639 2614733 := bbase (se 3 (by rfl) ⟨490262, by rfl⟩ : syracuseStep 2614733 = 980525) (by norm_num)
theorem B5301733 : Blo 1160639 5301733 := bbase (se 4 (by rfl) ⟨497037, by rfl⟩ : syracuseStep 5301733 = 994075) (by norm_num)
theorem B1959437 : Blo 1160639 1959437 := bbase (se 3 (by rfl) ⟨367394, by rfl⟩ : syracuseStep 1959437 = 734789) (by norm_num)
theorem B2942477 : Blo 1160639 2942477 := bbase (se 3 (by rfl) ⟨551714, by rfl⟩ : syracuseStep 2942477 = 1103429) (by norm_num)
theorem B2614805 : Blo 1160639 2614805 := bbase (se 6 (by rfl) ⟨61284, by rfl⟩ : syracuseStep 2614805 = 122569) (by norm_num)
theorem B2614877 : Blo 1160639 2614877 := bbase (se 3 (by rfl) ⟨490289, by rfl⟩ : syracuseStep 2614877 = 980579) (by norm_num)
theorem B3925637 : Blo 1160639 3925637 := bbase (se 4 (by rfl) ⟨368028, by rfl⟩ : syracuseStep 3925637 = 736057) (by norm_num)
theorem B1959565 : Blo 1160639 1959565 := bbase (se 3 (by rfl) ⟨367418, by rfl⟩ : syracuseStep 1959565 = 734837) (by norm_num)
theorem B2614949 : Blo 1160639 2614949 := bbase (se 4 (by rfl) ⟨245151, by rfl⟩ : syracuseStep 2614949 = 490303) (by norm_num)
theorem B2942669 : Blo 1160639 2942669 := bbase (se 3 (by rfl) ⟨551750, by rfl⟩ : syracuseStep 2942669 = 1103501) (by norm_num)
theorem B1959653 : Blo 1160639 1959653 := bbase (se 4 (by rfl) ⟨183717, by rfl⟩ : syracuseStep 1959653 = 367435) (by norm_num)
theorem B2615021 : Blo 1160639 2615021 := bbase (se 3 (by rfl) ⟨490316, by rfl⟩ : syracuseStep 2615021 = 980633) (by norm_num)
theorem B2615093 : Blo 1160639 2615093 := bbase (se 5 (by rfl) ⟨122582, by rfl⟩ : syracuseStep 2615093 = 245165) (by norm_num)
theorem B1959781 : Blo 1160639 1959781 := bbase (se 4 (by rfl) ⟨183729, by rfl⟩ : syracuseStep 1959781 = 367459) (by norm_num)
theorem B2615165 : Blo 1160639 2615165 := bbase (se 3 (by rfl) ⟨490343, by rfl⟩ : syracuseStep 2615165 = 980687) (by norm_num)
theorem B2484125 : Blo 1160639 2484125 := bbase (se 3 (by rfl) ⟨465773, by rfl⟩ : syracuseStep 2484125 = 931547) (by norm_num)
theorem B1959869 : Blo 1160639 1959869 := bbase (se 3 (by rfl) ⟨367475, by rfl⟩ : syracuseStep 1959869 = 734951) (by norm_num)
theorem B2615237 : Blo 1160639 2615237 := bbase (se 4 (by rfl) ⟨245178, by rfl⟩ : syracuseStep 2615237 = 490357) (by norm_num)
theorem B5892101 : Blo 1160639 5892101 := bbase (se 4 (by rfl) ⟨552384, by rfl⟩ : syracuseStep 5892101 = 1104769) (by norm_num)
theorem B2615309 : Blo 1160639 2615309 := bbase (se 3 (by rfl) ⟨490370, by rfl⟩ : syracuseStep 2615309 = 980741) (by norm_num)
theorem B2517013 : Blo 1160639 2517013 := bbase (se 6 (by rfl) ⟨58992, by rfl⟩ : syracuseStep 2517013 = 117985) (by norm_num)
theorem B2484245 : Blo 1160639 2484245 := bbase (se 6 (by rfl) ⟨58224, by rfl⟩ : syracuseStep 2484245 = 116449) (by norm_num)
theorem B2943013 : Blo 1160639 2943013 := bbase (se 4 (by rfl) ⟨275907, by rfl⟩ : syracuseStep 2943013 = 551815) (by norm_num)
theorem B7956533 : Blo 1160639 7956533 := bbase (se 5 (by rfl) ⟨372962, by rfl⟩ : syracuseStep 7956533 = 745925) (by norm_num)
theorem B3926069 : Blo 1160639 3926069 := bbase (se 5 (by rfl) ⟨184034, by rfl⟩ : syracuseStep 3926069 = 368069) (by norm_num)
theorem B1959997 : Blo 1160639 1959997 := bbase (se 3 (by rfl) ⟨367499, by rfl⟩ : syracuseStep 1959997 = 734999) (by norm_num)
theorem B2615381 : Blo 1160639 2615381 := bbase (se 8 (by rfl) ⟨15324, by rfl⟩ : syracuseStep 2615381 = 30649) (by norm_num)
theorem B1960085 : Blo 1160639 1960085 := bbase (se 6 (by rfl) ⟨45939, by rfl⟩ : syracuseStep 1960085 = 91879) (by norm_num)
theorem B2943125 : Blo 1160639 2943125 := bbase (se 6 (by rfl) ⟨68979, by rfl⟩ : syracuseStep 2943125 = 137959) (by norm_num)
theorem B7071893 : Blo 1160639 7071893 := bbase (se 6 (by rfl) ⟨165747, by rfl⟩ : syracuseStep 7071893 = 331495) (by norm_num)
theorem B2615453 : Blo 1160639 2615453 := bbase (se 3 (by rfl) ⟨490397, by rfl⟩ : syracuseStep 2615453 = 980795) (by norm_num)
theorem B2615525 : Blo 1160639 2615525 := bbase (se 4 (by rfl) ⟨245205, by rfl⟩ : syracuseStep 2615525 = 490411) (by norm_num)
theorem B1960213 : Blo 1160639 1960213 := bbase (se 6 (by rfl) ⟨45942, by rfl⟩ : syracuseStep 1960213 = 91885) (by norm_num)
theorem B2615597 : Blo 1160639 2615597 := bbase (se 3 (by rfl) ⟨490424, by rfl⟩ : syracuseStep 2615597 = 980849) (by norm_num)
theorem B4417861 : Blo 1160639 4417861 := bbase (se 4 (by rfl) ⟨414174, by rfl⟩ : syracuseStep 4417861 = 828349) (by norm_num)
theorem B2943317 : Blo 1160639 2943317 := bbase (se 10 (by rfl) ⟨4311, by rfl⟩ : syracuseStep 2943317 = 8623) (by norm_num)
theorem B1960301 : Blo 1160639 1960301 := bbase (se 3 (by rfl) ⟨367556, by rfl⟩ : syracuseStep 1960301 = 735113) (by norm_num)
theorem B2615669 : Blo 1160639 2615669 := bbase (se 5 (by rfl) ⟨122609, by rfl⟩ : syracuseStep 2615669 = 245219) (by norm_num)
theorem B6613397 : Blo 1160639 6613397 := bbase (se 6 (by rfl) ⟨155001, by rfl⟩ : syracuseStep 6613397 = 310003) (by norm_num)
theorem B1239457 : Blo 1160639 1239457 := bbase (se 2 (by rfl) ⟨464796, by rfl⟩ : syracuseStep 1239457 = 929593) (by norm_num)
theorem B2615741 : Blo 1160639 2615741 := bbase (se 3 (by rfl) ⟨490451, by rfl⟩ : syracuseStep 2615741 = 980903) (by norm_num)
theorem B3926501 : Blo 1160639 3926501 := bbase (se 4 (by rfl) ⟨368109, by rfl⟩ : syracuseStep 3926501 = 736219) (by norm_num)
theorem B1960429 : Blo 1160639 1960429 := bbase (se 3 (by rfl) ⟨367580, by rfl⟩ : syracuseStep 1960429 = 735161) (by norm_num)
theorem B2615813 : Blo 1160639 2615813 := bbase (se 4 (by rfl) ⟨245232, by rfl⟩ : syracuseStep 2615813 = 490465) (by norm_num)
theorem B1468945 : Blo 1160639 1468945 := bbase (se 2 (by rfl) ⟨550854, by rfl⟩ : syracuseStep 1468945 = 1101709) (by norm_num)
theorem B1239581 : Blo 1160639 1239581 := bbase (se 3 (by rfl) ⟨232421, by rfl⟩ : syracuseStep 1239581 = 464843) (by norm_num)
theorem B3140165 : Blo 1160639 3140165 := bbase (se 4 (by rfl) ⟨294390, by rfl⟩ : syracuseStep 3140165 = 588781) (by norm_num)
theorem B1960517 : Blo 1160639 1960517 := bbase (se 4 (by rfl) ⟨183798, by rfl⟩ : syracuseStep 1960517 = 367597) (by norm_num)
theorem B2615885 : Blo 1160639 2615885 := bbase (se 3 (by rfl) ⟨490478, by rfl⟩ : syracuseStep 2615885 = 980957) (by norm_num)
theorem B4418165 : Blo 1160639 4418165 := bbase (se 5 (by rfl) ⟨207101, by rfl⟩ : syracuseStep 4418165 = 414203) (by norm_num)
theorem B2517637 : Blo 1160639 2517637 := bbase (se 4 (by rfl) ⟨236028, by rfl⟩ : syracuseStep 2517637 = 472057) (by norm_num)
theorem B2484877 : Blo 1160639 2484877 := bbase (se 3 (by rfl) ⟨465914, by rfl⟩ : syracuseStep 2484877 = 931829) (by norm_num)
theorem B2615957 : Blo 1160639 2615957 := bbase (se 6 (by rfl) ⟨61311, by rfl⟩ : syracuseStep 2615957 = 122623) (by norm_num)
theorem B2091685 : Blo 1160639 2091685 := bbase (se 4 (by rfl) ⟨196095, by rfl⟩ : syracuseStep 2091685 = 392191) (by norm_num)
theorem B2943661 : Blo 1160639 2943661 := bbase (se 3 (by rfl) ⟨551936, by rfl⟩ : syracuseStep 2943661 = 1103873) (by norm_num)
theorem B1469117 : Blo 1160639 1469117 := bbase (se 3 (by rfl) ⟨275459, by rfl⟩ : syracuseStep 1469117 = 550919) (by norm_num)
theorem B1960645 : Blo 1160639 1960645 := bbase (se 4 (by rfl) ⟨183810, by rfl⟩ : syracuseStep 1960645 = 367621) (by norm_num)
theorem B2616029 : Blo 1160639 2616029 := bbase (se 3 (by rfl) ⟨490505, by rfl⟩ : syracuseStep 2616029 = 981011) (by norm_num)
theorem B1469173 : Blo 1160639 1469173 := bbase (se 5 (by rfl) ⟨68867, by rfl⟩ : syracuseStep 1469173 = 137735) (by norm_num)
theorem B1239833 : Blo 1160639 1239833 := bbase (se 2 (by rfl) ⟨464937, by rfl⟩ : syracuseStep 1239833 = 929875) (by norm_num)
theorem B1960733 : Blo 1160639 1960733 := bbase (se 3 (by rfl) ⟨367637, by rfl⟩ : syracuseStep 1960733 = 735275) (by norm_num)
theorem B2943773 : Blo 1160639 2943773 := bbase (se 3 (by rfl) ⟨551957, by rfl⟩ : syracuseStep 2943773 = 1103915) (by norm_num)
theorem B2616101 : Blo 1160639 2616101 := bbase (se 4 (by rfl) ⟨245259, by rfl⟩ : syracuseStep 2616101 = 490519) (by norm_num)
theorem B1862453 : Blo 1160639 1862453 := bbase (se 5 (by rfl) ⟨87302, by rfl⟩ : syracuseStep 1862453 = 174605) (by norm_num)
theorem B1469269 : Blo 1160639 1469269 := bbase (se 9 (by rfl) ⟨4304, by rfl⟩ : syracuseStep 1469269 = 8609) (by norm_num)
theorem B2616173 : Blo 1160639 2616173 := bbase (se 3 (by rfl) ⟨490532, by rfl⟩ : syracuseStep 2616173 = 981065) (by norm_num)
theorem B3926933 : Blo 1160639 3926933 := bbase (se 6 (by rfl) ⟨92037, by rfl⟩ : syracuseStep 3926933 = 184075) (by norm_num)
theorem B1960861 : Blo 1160639 1960861 := bbase (se 3 (by rfl) ⟨367661, by rfl⟩ : syracuseStep 1960861 = 735323) (by norm_num)
theorem B2616245 : Blo 1160639 2616245 := bbase (se 5 (by rfl) ⟨122636, by rfl⟩ : syracuseStep 2616245 = 245273) (by norm_num)
theorem B2091973 : Blo 1160639 2091973 := bbase (se 4 (by rfl) ⟨196122, by rfl⟩ : syracuseStep 2091973 = 392245) (by norm_num)
theorem B2943965 : Blo 1160639 2943965 := bbase (se 3 (by rfl) ⟨551993, by rfl⟩ : syracuseStep 2943965 = 1103987) (by norm_num)
theorem B1960949 : Blo 1160639 1960949 := bbase (se 5 (by rfl) ⟨91919, by rfl⟩ : syracuseStep 1960949 = 183839) (by norm_num)
theorem B2616317 : Blo 1160639 2616317 := bbase (se 3 (by rfl) ⟨490559, by rfl⟩ : syracuseStep 2616317 = 981119) (by norm_num)
theorem B1469441 : Blo 1160639 1469441 := bbase (se 2 (by rfl) ⟨551040, by rfl⟩ : syracuseStep 1469441 = 1102081) (by norm_num)
theorem B1469497 : Blo 1160639 1469497 := bbase (se 2 (by rfl) ⟨551061, by rfl⟩ : syracuseStep 1469497 = 1102123) (by norm_num)
theorem B2616389 : Blo 1160639 2616389 := bbase (se 4 (by rfl) ⟨245286, by rfl⟩ : syracuseStep 2616389 = 490573) (by norm_num)
theorem B1961077 : Blo 1160639 1961077 := bbase (se 5 (by rfl) ⟨91925, by rfl⟩ : syracuseStep 1961077 = 183851) (by norm_num)
theorem B1305733 : Blo 1160639 1305733 := bbase (se 4 (by rfl) ⟨122412, by rfl⟩ : syracuseStep 1305733 = 244825) (by norm_num)
theorem B2616461 : Blo 1160639 2616461 := bbase (se 3 (by rfl) ⟨490586, by rfl⟩ : syracuseStep 2616461 = 981173) (by norm_num)
theorem B1469593 : Blo 1160639 1469593 := bbase (se 2 (by rfl) ⟨551097, by rfl⟩ : syracuseStep 1469593 = 1102195) (by norm_num)
theorem B1305769 : Blo 1160639 1305769 := bbase (se 2 (by rfl) ⟨489663, by rfl⟩ : syracuseStep 1305769 = 979327) (by norm_num)
theorem B6286517 : Blo 1160639 6286517 := bbase (se 5 (by rfl) ⟨294680, by rfl⟩ : syracuseStep 6286517 = 589361) (by norm_num)
theorem B1305805 : Blo 1160639 1305805 := bbase (se 3 (by rfl) ⟨244838, by rfl⟩ : syracuseStep 1305805 = 489677) (by norm_num)
theorem B1961165 : Blo 1160639 1961165 := bbase (se 3 (by rfl) ⟨367718, by rfl⟩ : syracuseStep 1961165 = 735437) (by norm_num)
theorem B1240277 : Blo 1160639 1240277 := bbase (se 7 (by rfl) ⟨14534, by rfl⟩ : syracuseStep 1240277 = 29069) (by norm_num)
theorem B2616533 : Blo 1160639 2616533 := bbase (se 7 (by rfl) ⟨30662, by rfl⟩ : syracuseStep 2616533 = 61325) (by norm_num)
theorem B1305841 : Blo 1160639 1305841 := bbase (se 2 (by rfl) ⟨489690, by rfl⟩ : syracuseStep 1305841 = 979381) (by norm_num)
theorem B1862909 : Blo 1160639 1862909 := bbase (se 3 (by rfl) ⟨349295, by rfl⟩ : syracuseStep 1862909 = 698591) (by norm_num)
theorem B1305877 : Blo 1160639 1305877 := bbase (se 6 (by rfl) ⟨30606, by rfl⟩ : syracuseStep 1305877 = 61213) (by norm_num)
theorem B5893397 : Blo 1160639 5893397 := bbase (se 6 (by rfl) ⟨138126, by rfl⟩ : syracuseStep 5893397 = 276253) (by norm_num)
theorem B2616605 : Blo 1160639 2616605 := bbase (se 3 (by rfl) ⟨490613, by rfl⟩ : syracuseStep 2616605 = 981227) (by norm_num)
theorem B2944309 : Blo 1160639 2944309 := bbase (se 5 (by rfl) ⟨138014, by rfl⟩ : syracuseStep 2944309 = 276029) (by norm_num)
theorem B1305913 : Blo 1160639 1305913 := bbase (se 2 (by rfl) ⟨489717, by rfl⟩ : syracuseStep 1305913 = 979435) (by norm_num)
theorem B1469765 : Blo 1160639 1469765 := bbase (se 4 (by rfl) ⟨137790, by rfl⟩ : syracuseStep 1469765 = 275581) (by norm_num)
theorem B3927365 : Blo 1160639 3927365 := bbase (se 4 (by rfl) ⟨368190, by rfl⟩ : syracuseStep 3927365 = 736381) (by norm_num)
theorem B1961293 : Blo 1160639 1961293 := bbase (se 3 (by rfl) ⟨367742, by rfl⟩ : syracuseStep 1961293 = 735485) (by norm_num)
theorem B1305949 : Blo 1160639 1305949 := bbase (se 3 (by rfl) ⟨244865, by rfl⟩ : syracuseStep 1305949 = 489731) (by norm_num)
theorem B2616677 : Blo 1160639 2616677 := bbase (se 4 (by rfl) ⟨245313, by rfl⟩ : syracuseStep 2616677 = 490627) (by norm_num)
theorem B1469821 : Blo 1160639 1469821 := bbase (se 3 (by rfl) ⟨275591, by rfl⟩ : syracuseStep 1469821 = 551183) (by norm_num)
theorem B1305985 : Blo 1160639 1305985 := bbase (se 2 (by rfl) ⟨489744, by rfl⟩ : syracuseStep 1305985 = 979489) (by norm_num)
theorem B1306021 : Blo 1160639 1306021 := bbase (se 4 (by rfl) ⟨122439, by rfl⟩ : syracuseStep 1306021 = 244879) (by norm_num)
theorem B1961381 : Blo 1160639 1961381 := bbase (se 4 (by rfl) ⟨183879, by rfl⟩ : syracuseStep 1961381 = 367759) (by norm_num)
theorem B2944421 : Blo 1160639 2944421 := bbase (se 4 (by rfl) ⟨276039, by rfl⟩ : syracuseStep 2944421 = 552079) (by norm_num)
theorem B2616749 : Blo 1160639 2616749 := bbase (se 3 (by rfl) ⟨490640, by rfl⟩ : syracuseStep 2616749 = 981281) (by norm_num)
theorem B1306057 : Blo 1160639 1306057 := bbase (se 2 (by rfl) ⟨489771, by rfl⟩ : syracuseStep 1306057 = 979543) (by norm_num)
theorem B2092493 : Blo 1160639 2092493 := bbase (se 3 (by rfl) ⟨392342, by rfl⟩ : syracuseStep 2092493 = 784685) (by norm_num)
theorem B1240525 : Blo 1160639 1240525 := bbase (se 3 (by rfl) ⟨232598, by rfl⟩ : syracuseStep 1240525 = 465197) (by norm_num)
theorem B1469917 : Blo 1160639 1469917 := bbase (se 3 (by rfl) ⟨275609, by rfl⟩ : syracuseStep 1469917 = 551219) (by norm_num)
theorem B1306093 : Blo 1160639 1306093 := bbase (se 3 (by rfl) ⟨244892, by rfl⟩ : syracuseStep 1306093 = 489785) (by norm_num)
theorem B2616821 : Blo 1160639 2616821 := bbase (se 5 (by rfl) ⟨122663, by rfl⟩ : syracuseStep 2616821 = 245327) (by norm_num)
theorem B2485765 : Blo 1160639 2485765 := bbase (se 4 (by rfl) ⟨233040, by rfl⟩ : syracuseStep 2485765 = 466081) (by norm_num)
theorem B1306129 : Blo 1160639 1306129 := bbase (se 2 (by rfl) ⟨489798, by rfl⟩ : syracuseStep 1306129 = 979597) (by norm_num)
theorem B1961509 : Blo 1160639 1961509 := bbase (se 4 (by rfl) ⟨183891, by rfl⟩ : syracuseStep 1961509 = 367783) (by norm_num)
theorem B3730981 : Blo 1160639 3730981 := bbase (se 4 (by rfl) ⟨349779, by rfl⟩ : syracuseStep 3730981 = 699559) (by norm_num)
theorem B1306165 : Blo 1160639 1306165 := bbase (se 5 (by rfl) ⟨61226, by rfl⟩ : syracuseStep 1306165 = 122453) (by norm_num)
theorem B6614581 : Blo 1160639 6614581 := bbase (se 5 (by rfl) ⟨310058, by rfl⟩ : syracuseStep 6614581 = 620117) (by norm_num)
theorem B2616893 : Blo 1160639 2616893 := bbase (se 3 (by rfl) ⟨490667, by rfl⟩ : syracuseStep 2616893 = 981335) (by norm_num)
theorem B1306201 : Blo 1160639 1306201 := bbase (se 2 (by rfl) ⟨489825, by rfl⟩ : syracuseStep 1306201 = 979651) (by norm_num)
theorem B2092637 : Blo 1160639 2092637 := bbase (se 3 (by rfl) ⟨392369, by rfl⟩ : syracuseStep 2092637 = 784739) (by norm_num)
theorem B2944613 : Blo 1160639 2944613 := bbase (se 4 (by rfl) ⟨276057, by rfl⟩ : syracuseStep 2944613 = 552115) (by norm_num)
theorem B1306237 : Blo 1160639 1306237 := bbase (se 3 (by rfl) ⟨244919, by rfl⟩ : syracuseStep 1306237 = 489839) (by norm_num)
theorem B1961597 : Blo 1160639 1961597 := bbase (se 3 (by rfl) ⟨367799, by rfl⟩ : syracuseStep 1961597 = 735599) (by norm_num)
theorem B2485885 : Blo 1160639 2485885 := bbase (se 3 (by rfl) ⟨466103, by rfl⟩ : syracuseStep 2485885 = 932207) (by norm_num)
theorem B2616965 : Blo 1160639 2616965 := bbase (se 4 (by rfl) ⟨245340, by rfl⟩ : syracuseStep 2616965 = 490681) (by norm_num)
theorem B1470089 : Blo 1160639 1470089 := bbase (se 2 (by rfl) ⟨551283, by rfl⟩ : syracuseStep 1470089 = 1102567) (by norm_num)
theorem B1306273 : Blo 1160639 1306273 := bbase (se 2 (by rfl) ⟨489852, by rfl⟩ : syracuseStep 1306273 = 979705) (by norm_num)
theorem B1470145 : Blo 1160639 1470145 := bbase (se 2 (by rfl) ⟨551304, by rfl⟩ : syracuseStep 1470145 = 1102609) (by norm_num)
theorem B1306309 : Blo 1160639 1306309 := bbase (se 4 (by rfl) ⟨122466, by rfl⟩ : syracuseStep 1306309 = 244933) (by norm_num)
theorem B2617037 : Blo 1160639 2617037 := bbase (se 3 (by rfl) ⟨490694, by rfl⟩ : syracuseStep 2617037 = 981389) (by norm_num)
theorem B1306345 : Blo 1160639 1306345 := bbase (se 2 (by rfl) ⟨489879, by rfl⟩ : syracuseStep 1306345 = 979759) (by norm_num)
theorem B3927797 : Blo 1160639 3927797 := bbase (se 5 (by rfl) ⟨184115, by rfl⟩ : syracuseStep 3927797 = 368231) (by norm_num)
theorem B1961725 : Blo 1160639 1961725 := bbase (se 3 (by rfl) ⟨367823, by rfl⟩ : syracuseStep 1961725 = 735647) (by norm_num)
theorem B1306381 : Blo 1160639 1306381 := bbase (se 3 (by rfl) ⟨244946, by rfl⟩ : syracuseStep 1306381 = 489893) (by norm_num)
theorem B2617109 : Blo 1160639 2617109 := bbase (se 6 (by rfl) ⟨61338, by rfl⟩ : syracuseStep 2617109 = 122677) (by norm_num)
theorem B1470241 : Blo 1160639 1470241 := bbase (se 2 (by rfl) ⟨551340, by rfl⟩ : syracuseStep 1470241 = 1102681) (by norm_num)
theorem B1306417 : Blo 1160639 1306417 := bbase (se 2 (by rfl) ⟨489906, by rfl⟩ : syracuseStep 1306417 = 979813) (by norm_num)
theorem B2092853 : Blo 1160639 2092853 := bbase (se 5 (by rfl) ⟨98102, by rfl⟩ : syracuseStep 2092853 = 196205) (by norm_num)
theorem B1306453 : Blo 1160639 1306453 := bbase (se 9 (by rfl) ⟨3827, by rfl⟩ : syracuseStep 1306453 = 7655) (by norm_num)
theorem B1961813 : Blo 1160639 1961813 := bbase (se 9 (by rfl) ⟨5747, by rfl⟩ : syracuseStep 1961813 = 11495) (by norm_num)
theorem B2617181 : Blo 1160639 2617181 := bbase (se 3 (by rfl) ⟨490721, by rfl⟩ : syracuseStep 2617181 = 981443) (by norm_num)
theorem B1306489 : Blo 1160639 1306489 := bbase (se 2 (by rfl) ⟨489933, by rfl⟩ : syracuseStep 1306489 = 979867) (by norm_num)
theorem B2092925 : Blo 1160639 2092925 := bbase (se 3 (by rfl) ⟨392423, by rfl⟩ : syracuseStep 2092925 = 784847) (by norm_num)
theorem B2486141 : Blo 1160639 2486141 := bbase (se 3 (by rfl) ⟨466151, by rfl⟩ : syracuseStep 2486141 = 932303) (by norm_num)
theorem B1240969 : Blo 1160639 1240969 := bbase (se 2 (by rfl) ⟨465363, by rfl⟩ : syracuseStep 1240969 = 930727) (by norm_num)
theorem B1306525 : Blo 1160639 1306525 := bbase (se 3 (by rfl) ⟨244973, by rfl⟩ : syracuseStep 1306525 = 489947) (by norm_num)
theorem B2617253 : Blo 1160639 2617253 := bbase (se 4 (by rfl) ⟨245367, by rfl⟩ : syracuseStep 2617253 = 490735) (by norm_num)
theorem B2944957 : Blo 1160639 2944957 := bbase (se 3 (by rfl) ⟨552179, by rfl⟩ : syracuseStep 2944957 = 1104359) (by norm_num)
theorem B1306561 : Blo 1160639 1306561 := bbase (se 2 (by rfl) ⟨489960, by rfl⟩ : syracuseStep 1306561 = 979921) (by norm_num)
theorem B1241029 : Blo 1160639 1241029 := bbase (se 4 (by rfl) ⟨116346, by rfl⟩ : syracuseStep 1241029 = 232693) (by norm_num)
theorem B1470413 : Blo 1160639 1470413 := bbase (se 3 (by rfl) ⟨275702, by rfl⟩ : syracuseStep 1470413 = 551405) (by norm_num)
theorem B1961941 : Blo 1160639 1961941 := bbase (se 7 (by rfl) ⟨22991, by rfl⟩ : syracuseStep 1961941 = 45983) (by norm_num)
theorem B1306597 : Blo 1160639 1306597 := bbase (se 4 (by rfl) ⟨122493, by rfl⟩ : syracuseStep 1306597 = 244987) (by norm_num)
theorem B2617325 : Blo 1160639 2617325 := bbase (se 3 (by rfl) ⟨490748, by rfl⟩ : syracuseStep 2617325 = 981497) (by norm_num)
theorem B1470469 : Blo 1160639 1470469 := bbase (se 4 (by rfl) ⟨137856, by rfl⟩ : syracuseStep 1470469 = 275713) (by norm_num)
theorem B1306633 : Blo 1160639 1306633 := bbase (se 2 (by rfl) ⟨489987, by rfl⟩ : syracuseStep 1306633 = 979975) (by norm_num)
theorem B1306669 : Blo 1160639 1306669 := bbase (se 3 (by rfl) ⟨245000, by rfl⟩ : syracuseStep 1306669 = 490001) (by norm_num)
theorem B1962029 : Blo 1160639 1962029 := bbase (se 3 (by rfl) ⟨367880, by rfl⟩ : syracuseStep 1962029 = 735761) (by norm_num)
theorem B2945069 : Blo 1160639 2945069 := bbase (se 3 (by rfl) ⟨552200, by rfl⟩ : syracuseStep 2945069 = 1104401) (by norm_num)
theorem B2617397 : Blo 1160639 2617397 := bbase (se 5 (by rfl) ⟨122690, by rfl⟩ : syracuseStep 2617397 = 245381) (by norm_num)
theorem B1306705 : Blo 1160639 1306705 := bbase (se 2 (by rfl) ⟨490014, by rfl⟩ : syracuseStep 1306705 = 980029) (by norm_num)
theorem B1470565 : Blo 1160639 1470565 := bbase (se 4 (by rfl) ⟨137865, by rfl⟩ : syracuseStep 1470565 = 275731) (by norm_num)
theorem B1306741 : Blo 1160639 1306741 := bbase (se 5 (by rfl) ⟨61253, by rfl⟩ : syracuseStep 1306741 = 122507) (by norm_num)
theorem B1568893 : Blo 1160639 1568893 := bbase (se 3 (by rfl) ⟨294167, by rfl⟩ : syracuseStep 1568893 = 588335) (by norm_num)
theorem B2617469 : Blo 1160639 2617469 := bbase (se 3 (by rfl) ⟨490775, by rfl⟩ : syracuseStep 2617469 = 981551) (by norm_num)
theorem B3305605 : Blo 1160639 3305605 := bbase (se 4 (by rfl) ⟨309900, by rfl⟩ : syracuseStep 3305605 = 619801) (by norm_num)
theorem B1306777 : Blo 1160639 1306777 := bbase (se 2 (by rfl) ⟨490041, by rfl⟩ : syracuseStep 1306777 = 980083) (by norm_num)
theorem B3928229 : Blo 1160639 3928229 := bbase (se 4 (by rfl) ⟨368271, by rfl⟩ : syracuseStep 3928229 = 736543) (by norm_num)
theorem B1962157 : Blo 1160639 1962157 := bbase (se 3 (by rfl) ⟨367904, by rfl⟩ : syracuseStep 1962157 = 735809) (by norm_num)
theorem B1306813 : Blo 1160639 1306813 := bbase (se 3 (by rfl) ⟨245027, by rfl⟩ : syracuseStep 1306813 = 490055) (by norm_num)
theorem B2617541 : Blo 1160639 2617541 := bbase (se 4 (by rfl) ⟨245394, by rfl⟩ : syracuseStep 2617541 = 490789) (by norm_num)
theorem B1863901 : Blo 1160639 1863901 := bbase (se 3 (by rfl) ⟨349481, by rfl⟩ : syracuseStep 1863901 = 698963) (by norm_num)
theorem B1306849 : Blo 1160639 1306849 := bbase (se 2 (by rfl) ⟨490068, by rfl⟩ : syracuseStep 1306849 = 980137) (by norm_num)
theorem B2093293 : Blo 1160639 2093293 := bbase (se 3 (by rfl) ⟨392492, by rfl⟩ : syracuseStep 2093293 = 784985) (by norm_num)
theorem B2945261 : Blo 1160639 2945261 := bbase (se 3 (by rfl) ⟨552236, by rfl⟩ : syracuseStep 2945261 = 1104473) (by norm_num)
theorem B1241345 : Blo 1160639 1241345 := bbase (se 2 (by rfl) ⟨465504, by rfl⟩ : syracuseStep 1241345 = 931009) (by norm_num)
theorem B1306885 : Blo 1160639 1306885 := bbase (se 4 (by rfl) ⟨122520, by rfl⟩ : syracuseStep 1306885 = 245041) (by norm_num)
theorem B1962245 : Blo 1160639 1962245 := bbase (se 4 (by rfl) ⟨183960, by rfl⟩ : syracuseStep 1962245 = 367921) (by norm_num)
theorem B2617613 : Blo 1160639 2617613 := bbase (se 3 (by rfl) ⟨490802, by rfl⟩ : syracuseStep 2617613 = 981605) (by norm_num)
theorem B1470737 : Blo 1160639 1470737 := bbase (se 2 (by rfl) ⟨551526, by rfl⟩ : syracuseStep 1470737 = 1103053) (by norm_num)
theorem B3305765 : Blo 1160639 3305765 := bbase (se 4 (by rfl) ⟨309915, by rfl⟩ : syracuseStep 3305765 = 619831) (by norm_num)
theorem B1306921 : Blo 1160639 1306921 := bbase (se 2 (by rfl) ⟨490095, by rfl⟩ : syracuseStep 1306921 = 980191) (by norm_num)
theorem B3535157 : Blo 1160639 3535157 := bbase (se 5 (by rfl) ⟨165710, by rfl⟩ : syracuseStep 3535157 = 331421) (by norm_num)
theorem B1470793 : Blo 1160639 1470793 := bbase (se 2 (by rfl) ⟨551547, by rfl⟩ : syracuseStep 1470793 = 1103095) (by norm_num)
theorem B1306957 : Blo 1160639 1306957 := bbase (se 3 (by rfl) ⟨245054, by rfl⟩ : syracuseStep 1306957 = 490109) (by norm_num)
theorem B2617685 : Blo 1160639 2617685 := bbase (se 10 (by rfl) ⟨3834, by rfl⟩ : syracuseStep 2617685 = 7669) (by norm_num)
theorem B1306993 : Blo 1160639 1306993 := bbase (se 2 (by rfl) ⟨490122, by rfl⟩ : syracuseStep 1306993 = 980245) (by norm_num)
theorem B1962373 : Blo 1160639 1962373 := bbase (se 4 (by rfl) ⟨183972, by rfl⟩ : syracuseStep 1962373 = 367945) (by norm_num)
theorem B1307029 : Blo 1160639 1307029 := bbase (se 6 (by rfl) ⟨30633, by rfl⟩ : syracuseStep 1307029 = 61267) (by norm_num)
theorem B2617757 : Blo 1160639 2617757 := bbase (se 3 (by rfl) ⟨490829, by rfl⟩ : syracuseStep 2617757 = 981659) (by norm_num)
theorem B1470889 : Blo 1160639 1470889 := bbase (se 2 (by rfl) ⟨551583, by rfl⟩ : syracuseStep 1470889 = 1103167) (by norm_num)
theorem B1307065 : Blo 1160639 1307065 := bbase (se 2 (by rfl) ⟨490149, by rfl⟩ : syracuseStep 1307065 = 980299) (by norm_num)
theorem B1307101 : Blo 1160639 1307101 := bbase (se 3 (by rfl) ⟨245081, by rfl⟩ : syracuseStep 1307101 = 490163) (by norm_num)
theorem B1962461 : Blo 1160639 1962461 := bbase (se 3 (by rfl) ⟨367961, by rfl⟩ : syracuseStep 1962461 = 735923) (by norm_num)
theorem B2617829 : Blo 1160639 2617829 := bbase (se 4 (by rfl) ⟨245421, by rfl⟩ : syracuseStep 2617829 = 490843) (by norm_num)
theorem B1307137 : Blo 1160639 1307137 := bbase (se 2 (by rfl) ⟨490176, by rfl⟩ : syracuseStep 1307137 = 980353) (by norm_num)
theorem B3306005 : Blo 1160639 3306005 := bbase (se 6 (by rfl) ⟨77484, by rfl⟩ : syracuseStep 3306005 = 154969) (by norm_num)
theorem B1307173 : Blo 1160639 1307173 := bbase (se 4 (by rfl) ⟨122547, by rfl⟩ : syracuseStep 1307173 = 245095) (by norm_num)
theorem B5894693 : Blo 1160639 5894693 := bbase (se 4 (by rfl) ⟨552627, by rfl⟩ : syracuseStep 5894693 = 1105255) (by norm_num)
theorem B2617901 : Blo 1160639 2617901 := bbase (se 3 (by rfl) ⟨490856, by rfl⟩ : syracuseStep 2617901 = 981713) (by norm_num)
theorem B2945605 : Blo 1160639 2945605 := bbase (se 4 (by rfl) ⟨276150, by rfl⟩ : syracuseStep 2945605 = 552301) (by norm_num)
theorem B1307209 : Blo 1160639 1307209 := bbase (se 2 (by rfl) ⟨490203, by rfl⟩ : syracuseStep 1307209 = 980407) (by norm_num)
theorem B1765973 : Blo 1160639 1765973 := bbase (se 8 (by rfl) ⟨10347, by rfl⟩ : syracuseStep 1765973 = 20695) (by norm_num)
theorem B1471061 : Blo 1160639 1471061 := bbase (se 8 (by rfl) ⟨8619, by rfl⟩ : syracuseStep 1471061 = 17239) (by norm_num)
theorem B3928661 : Blo 1160639 3928661 := bbase (se 8 (by rfl) ⟨23019, by rfl⟩ : syracuseStep 3928661 = 46039) (by norm_num)
theorem B1962589 : Blo 1160639 1962589 := bbase (se 3 (by rfl) ⟨367985, by rfl⟩ : syracuseStep 1962589 = 735971) (by norm_num)
theorem B1307245 : Blo 1160639 1307245 := bbase (se 3 (by rfl) ⟨245108, by rfl⟩ : syracuseStep 1307245 = 490217) (by norm_num)
theorem B2617973 : Blo 1160639 2617973 := bbase (se 5 (by rfl) ⟨122717, by rfl⟩ : syracuseStep 2617973 = 245435) (by norm_num)
theorem B1471117 : Blo 1160639 1471117 := bbase (se 3 (by rfl) ⟨275834, by rfl⟩ : syracuseStep 1471117 = 551669) (by norm_num)
theorem B1307281 : Blo 1160639 1307281 := bbase (se 2 (by rfl) ⟨490230, by rfl⟩ : syracuseStep 1307281 = 980461) (by norm_num)
theorem B1307317 : Blo 1160639 1307317 := bbase (se 5 (by rfl) ⟨61280, by rfl⟩ : syracuseStep 1307317 = 122561) (by norm_num)
theorem B1962677 : Blo 1160639 1962677 := bbase (se 5 (by rfl) ⟨92000, by rfl⟩ : syracuseStep 1962677 = 184001) (by norm_num)
theorem B2945717 : Blo 1160639 2945717 := bbase (se 5 (by rfl) ⟨138080, by rfl⟩ : syracuseStep 2945717 = 276161) (by norm_num)
theorem B4420277 : Blo 1160639 4420277 := bbase (se 5 (by rfl) ⟨207200, by rfl⟩ : syracuseStep 4420277 = 414401) (by norm_num)
theorem B1241789 : Blo 1160639 1241789 := bbase (se 3 (by rfl) ⟨232835, by rfl⟩ : syracuseStep 1241789 = 465671) (by norm_num)
theorem B2618045 : Blo 1160639 2618045 := bbase (se 3 (by rfl) ⟨490883, by rfl⟩ : syracuseStep 2618045 = 981767) (by norm_num)
theorem B3306197 : Blo 1160639 3306197 := bbase (se 7 (by rfl) ⟨38744, by rfl⟩ : syracuseStep 3306197 = 77489) (by norm_num)
theorem B1307353 : Blo 1160639 1307353 := bbase (se 2 (by rfl) ⟨490257, by rfl⟩ : syracuseStep 1307353 = 980515) (by norm_num)
theorem B1471213 : Blo 1160639 1471213 := bbase (se 3 (by rfl) ⟨275852, by rfl⟩ : syracuseStep 1471213 = 551705) (by norm_num)
theorem B2487029 : Blo 1160639 2487029 := bbase (se 5 (by rfl) ⟨116579, by rfl⟩ : syracuseStep 2487029 = 233159) (by norm_num)
theorem B1241849 : Blo 1160639 1241849 := bbase (se 2 (by rfl) ⟨465693, by rfl⟩ : syracuseStep 1241849 = 931387) (by norm_num)
theorem B1307389 : Blo 1160639 1307389 := bbase (se 3 (by rfl) ⟨245135, by rfl⟩ : syracuseStep 1307389 = 490271) (by norm_num)
theorem B2618117 : Blo 1160639 2618117 := bbase (se 4 (by rfl) ⟨245448, by rfl⟩ : syracuseStep 2618117 = 490897) (by norm_num)
theorem B1307425 : Blo 1160639 1307425 := bbase (se 2 (by rfl) ⟨490284, by rfl⟩ : syracuseStep 1307425 = 980569) (by norm_num)
theorem B1962805 : Blo 1160639 1962805 := bbase (se 5 (by rfl) ⟨92006, by rfl⟩ : syracuseStep 1962805 = 184013) (by norm_num)
theorem B1307461 : Blo 1160639 1307461 := bbase (se 4 (by rfl) ⟨122574, by rfl⟩ : syracuseStep 1307461 = 245149) (by norm_num)
theorem B2618189 : Blo 1160639 2618189 := bbase (se 3 (by rfl) ⟨490910, by rfl⟩ : syracuseStep 2618189 = 981821) (by norm_num)
theorem B5665621 : Blo 1160639 5665621 := bbase (se 9 (by rfl) ⟨16598, by rfl⟩ : syracuseStep 5665621 = 33197) (by norm_num)
theorem B1864549 : Blo 1160639 1864549 := bbase (se 4 (by rfl) ⟨174801, by rfl⟩ : syracuseStep 1864549 = 349603) (by norm_num)
theorem B1307497 : Blo 1160639 1307497 := bbase (se 2 (by rfl) ⟨490311, by rfl⟩ : syracuseStep 1307497 = 980623) (by norm_num)
theorem B2093933 : Blo 1160639 2093933 := bbase (se 3 (by rfl) ⟨392612, by rfl⟩ : syracuseStep 2093933 = 785225) (by norm_num)
theorem B2945909 : Blo 1160639 2945909 := bbase (se 5 (by rfl) ⟨138089, by rfl⟩ : syracuseStep 2945909 = 276179) (by norm_num)
theorem B1241977 : Blo 1160639 1241977 := bbase (se 2 (by rfl) ⟨465741, by rfl⟩ : syracuseStep 1241977 = 931483) (by norm_num)
theorem B1307533 : Blo 1160639 1307533 := bbase (se 3 (by rfl) ⟨245162, by rfl⟩ : syracuseStep 1307533 = 490325) (by norm_num)
theorem B1962893 : Blo 1160639 1962893 := bbase (se 3 (by rfl) ⟨368042, by rfl⟩ : syracuseStep 1962893 = 736085) (by norm_num)
theorem B2618261 : Blo 1160639 2618261 := bbase (se 6 (by rfl) ⟨61365, by rfl⟩ : syracuseStep 2618261 = 122731) (by norm_num)
theorem B1471385 : Blo 1160639 1471385 := bbase (se 2 (by rfl) ⟨551769, by rfl⟩ : syracuseStep 1471385 = 1103539) (by norm_num)
theorem B1307569 : Blo 1160639 1307569 := bbase (se 2 (by rfl) ⟨490338, by rfl⟩ : syracuseStep 1307569 = 980677) (by norm_num)
theorem B1471441 : Blo 1160639 1471441 := bbase (se 2 (by rfl) ⟨551790, by rfl⟩ : syracuseStep 1471441 = 1103581) (by norm_num)
theorem B1307605 : Blo 1160639 1307605 := bbase (se 7 (by rfl) ⟨15323, by rfl⟩ : syracuseStep 1307605 = 30647) (by norm_num)
theorem B4420565 : Blo 1160639 4420565 := bbase (se 7 (by rfl) ⟨51803, by rfl⟩ : syracuseStep 4420565 = 103607) (by norm_num)
theorem B2618333 : Blo 1160639 2618333 := bbase (se 3 (by rfl) ⟨490937, by rfl⟩ : syracuseStep 2618333 = 981875) (by norm_num)
theorem B2487269 : Blo 1160639 2487269 := bbase (se 4 (by rfl) ⟨233181, by rfl⟩ : syracuseStep 2487269 = 466363) (by norm_num)
theorem B1307641 : Blo 1160639 1307641 := bbase (se 2 (by rfl) ⟨490365, by rfl⟩ : syracuseStep 1307641 = 980731) (by norm_num)
theorem B3929093 : Blo 1160639 3929093 := bbase (se 4 (by rfl) ⟨368352, by rfl⟩ : syracuseStep 3929093 = 736705) (by norm_num)
theorem B1176589 : Blo 1160639 1176589 := bbase (se 3 (by rfl) ⟨220610, by rfl⟩ : syracuseStep 1176589 = 441221) (by norm_num)
theorem B1963021 : Blo 1160639 1963021 := bbase (se 3 (by rfl) ⟨368066, by rfl⟩ : syracuseStep 1963021 = 736133) (by norm_num)
theorem B1307677 : Blo 1160639 1307677 := bbase (se 3 (by rfl) ⟨245189, by rfl⟩ : syracuseStep 1307677 = 490379) (by norm_num)
theorem B2618405 : Blo 1160639 2618405 := bbase (se 4 (by rfl) ⟨245475, by rfl⟩ : syracuseStep 2618405 = 490951) (by norm_num)
theorem B1471537 : Blo 1160639 1471537 := bbase (se 2 (by rfl) ⟨551826, by rfl⟩ : syracuseStep 1471537 = 1103653) (by norm_num)
theorem B3142709 : Blo 1160639 3142709 := bbase (se 5 (by rfl) ⟨147314, by rfl⟩ : syracuseStep 3142709 = 294629) (by norm_num)
theorem B1307713 : Blo 1160639 1307713 := bbase (se 2 (by rfl) ⟨490392, by rfl⟩ : syracuseStep 1307713 = 980785) (by norm_num)
theorem B1307749 : Blo 1160639 1307749 := bbase (se 4 (by rfl) ⟨122601, by rfl⟩ : syracuseStep 1307749 = 245203) (by norm_num)
theorem B1963109 : Blo 1160639 1963109 := bbase (se 4 (by rfl) ⟨184041, by rfl⟩ : syracuseStep 1963109 = 368083) (by norm_num)
theorem B2618477 : Blo 1160639 2618477 := bbase (se 3 (by rfl) ⟨490964, by rfl⟩ : syracuseStep 2618477 = 981929) (by norm_num)
theorem B1307785 : Blo 1160639 1307785 := bbase (se 2 (by rfl) ⟨490419, by rfl⟩ : syracuseStep 1307785 = 980839) (by norm_num)
theorem B1307821 : Blo 1160639 1307821 := bbase (se 3 (by rfl) ⟨245216, by rfl⟩ : syracuseStep 1307821 = 490433) (by norm_num)
theorem B2618549 : Blo 1160639 2618549 := bbase (se 5 (by rfl) ⟨122744, by rfl⟩ : syracuseStep 2618549 = 245489) (by norm_num)
theorem B2946253 : Blo 1160639 2946253 := bbase (se 3 (by rfl) ⟨552422, by rfl⟩ : syracuseStep 2946253 = 1104845) (by norm_num)
theorem B1307857 : Blo 1160639 1307857 := bbase (se 2 (by rfl) ⟨490446, by rfl⟩ : syracuseStep 1307857 = 980893) (by norm_num)
theorem B1471709 : Blo 1160639 1471709 := bbase (se 3 (by rfl) ⟨275945, by rfl⟩ : syracuseStep 1471709 = 551891) (by norm_num)
theorem B1963237 : Blo 1160639 1963237 := bbase (se 4 (by rfl) ⟨184053, by rfl⟩ : syracuseStep 1963237 = 368107) (by norm_num)
theorem B1307893 : Blo 1160639 1307893 := bbase (se 5 (by rfl) ⟨61307, by rfl⟩ : syracuseStep 1307893 = 122615) (by norm_num)
theorem B4715765 : Blo 1160639 4715765 := bbase (se 5 (by rfl) ⟨221051, by rfl⟩ : syracuseStep 4715765 = 442103) (by norm_num)
theorem B2618621 : Blo 1160639 2618621 := bbase (se 3 (by rfl) ⟨490991, by rfl⟩ : syracuseStep 2618621 = 981983) (by norm_num)
theorem B1570061 : Blo 1160639 1570061 := bbase (se 3 (by rfl) ⟨294386, by rfl⟩ : syracuseStep 1570061 = 588773) (by norm_num)
theorem B1471765 : Blo 1160639 1471765 := bbase (se 6 (by rfl) ⟨34494, by rfl⟩ : syracuseStep 1471765 = 68989) (by norm_num)
theorem B1307929 : Blo 1160639 1307929 := bbase (se 2 (by rfl) ⟨490473, by rfl⟩ : syracuseStep 1307929 = 980947) (by norm_num)
theorem B1242421 : Blo 1160639 1242421 := bbase (se 5 (by rfl) ⟨58238, by rfl⟩ : syracuseStep 1242421 = 116477) (by norm_num)
theorem B1307965 : Blo 1160639 1307965 := bbase (se 3 (by rfl) ⟨245243, by rfl⟩ : syracuseStep 1307965 = 490487) (by norm_num)
theorem B1963325 : Blo 1160639 1963325 := bbase (se 3 (by rfl) ⟨368123, by rfl⟩ : syracuseStep 1963325 = 736247) (by norm_num)
theorem B2946365 : Blo 1160639 2946365 := bbase (se 3 (by rfl) ⟨552443, by rfl⟩ : syracuseStep 2946365 = 1104887) (by norm_num)
theorem B2618693 : Blo 1160639 2618693 := bbase (se 4 (by rfl) ⟨245502, by rfl⟩ : syracuseStep 2618693 = 491005) (by norm_num)
theorem B9925973 : Blo 1160639 9925973 := bbase (se 13 (by rfl) ⟨1817, by rfl⟩ : syracuseStep 9925973 = 3635) (by norm_num)
theorem B1308001 : Blo 1160639 1308001 := bbase (se 2 (by rfl) ⟨490500, by rfl⟩ : syracuseStep 1308001 = 981001) (by norm_num)
theorem B1471861 : Blo 1160639 1471861 := bbase (se 5 (by rfl) ⟨68993, by rfl⟩ : syracuseStep 1471861 = 137987) (by norm_num)
theorem B1308037 : Blo 1160639 1308037 := bbase (se 4 (by rfl) ⟨122628, by rfl⟩ : syracuseStep 1308037 = 245257) (by norm_num)
theorem B2618765 : Blo 1160639 2618765 := bbase (se 3 (by rfl) ⟨491018, by rfl⟩ : syracuseStep 2618765 = 982037) (by norm_num)
theorem B1308073 : Blo 1160639 1308073 := bbase (se 2 (by rfl) ⟨490527, by rfl⟩ : syracuseStep 1308073 = 981055) (by norm_num)
theorem B1242541 : Blo 1160639 1242541 := bbase (se 3 (by rfl) ⟨232976, by rfl⟩ : syracuseStep 1242541 = 465953) (by norm_num)
theorem B3929525 : Blo 1160639 3929525 := bbase (se 5 (by rfl) ⟨184196, by rfl⟩ : syracuseStep 3929525 = 368393) (by norm_num)
theorem B1963453 : Blo 1160639 1963453 := bbase (se 3 (by rfl) ⟨368147, by rfl⟩ : syracuseStep 1963453 = 736295) (by norm_num)
theorem B1308109 : Blo 1160639 1308109 := bbase (se 3 (by rfl) ⟨245270, by rfl⟩ : syracuseStep 1308109 = 490541) (by norm_num)
theorem B2618837 : Blo 1160639 2618837 := bbase (se 7 (by rfl) ⟨30689, by rfl⟩ : syracuseStep 2618837 = 61379) (by norm_num)
theorem B1570277 : Blo 1160639 1570277 := bbase (se 4 (by rfl) ⟨147213, by rfl⟩ : syracuseStep 1570277 = 294427) (by norm_num)
theorem B1308145 : Blo 1160639 1308145 := bbase (se 2 (by rfl) ⟨490554, by rfl⟩ : syracuseStep 1308145 = 981109) (by norm_num)
theorem B6616565 : Blo 1160639 6616565 := bbase (se 5 (by rfl) ⟨310151, by rfl⟩ : syracuseStep 6616565 = 620303) (by norm_num)
theorem B2946557 : Blo 1160639 2946557 := bbase (se 3 (by rfl) ⟨552479, by rfl⟩ : syracuseStep 2946557 = 1104959) (by norm_num)
theorem B1308181 : Blo 1160639 1308181 := bbase (se 6 (by rfl) ⟨30660, by rfl⟩ : syracuseStep 1308181 = 61321) (by norm_num)
theorem B1963541 : Blo 1160639 1963541 := bbase (se 6 (by rfl) ⟨46020, by rfl⟩ : syracuseStep 1963541 = 92041) (by norm_num)
theorem B2618909 : Blo 1160639 2618909 := bbase (se 3 (by rfl) ⟨491045, by rfl⟩ : syracuseStep 2618909 = 982091) (by norm_num)
theorem B1472033 : Blo 1160639 1472033 := bbase (se 2 (by rfl) ⟨552012, by rfl⟩ : syracuseStep 1472033 = 1104025) (by norm_num)
theorem B1308217 : Blo 1160639 1308217 := bbase (se 2 (by rfl) ⟨490581, by rfl⟩ : syracuseStep 1308217 = 981163) (by norm_num)
theorem B2094677 : Blo 1160639 2094677 := bbase (se 8 (by rfl) ⟨12273, by rfl⟩ : syracuseStep 2094677 = 24547) (by norm_num)
theorem B1472089 : Blo 1160639 1472089 := bbase (se 2 (by rfl) ⟨552033, by rfl⟩ : syracuseStep 1472089 = 1104067) (by norm_num)
theorem B2651741 : Blo 1160639 2651741 := bbase (se 3 (by rfl) ⟨497201, by rfl⟩ : syracuseStep 2651741 = 994403) (by norm_num)
theorem B1308253 : Blo 1160639 1308253 := bbase (se 3 (by rfl) ⟨245297, by rfl⟩ : syracuseStep 1308253 = 490595) (by norm_num)
theorem B2618981 : Blo 1160639 2618981 := bbase (se 4 (by rfl) ⟨245529, by rfl⟩ : syracuseStep 2618981 = 491059) (by norm_num)
theorem B1308289 : Blo 1160639 1308289 := bbase (se 2 (by rfl) ⟨490608, by rfl⟩ : syracuseStep 1308289 = 981217) (by norm_num)
theorem B1963669 : Blo 1160639 1963669 := bbase (se 6 (by rfl) ⟨46023, by rfl⟩ : syracuseStep 1963669 = 92047) (by norm_num)
theorem B1308325 : Blo 1160639 1308325 := bbase (se 4 (by rfl) ⟨122655, by rfl⟩ : syracuseStep 1308325 = 245311) (by norm_num)
theorem B1242793 : Blo 1160639 1242793 := bbase (se 2 (by rfl) ⟨466047, by rfl⟩ : syracuseStep 1242793 = 932095) (by norm_num)
theorem B1242797 : Blo 1160639 1242797 := bbase (se 3 (by rfl) ⟨233024, by rfl⟩ : syracuseStep 1242797 = 466049) (by norm_num)
theorem B2619053 : Blo 1160639 2619053 := bbase (se 3 (by rfl) ⟨491072, by rfl⟩ : syracuseStep 2619053 = 982145) (by norm_num)
theorem B3307189 : Blo 1160639 3307189 := bbase (se 5 (by rfl) ⟨155024, by rfl⟩ : syracuseStep 3307189 = 310049) (by norm_num)
theorem B1472185 : Blo 1160639 1472185 := bbase (se 2 (by rfl) ⟨552069, by rfl⟩ : syracuseStep 1472185 = 1104139) (by norm_num)
theorem B1308361 : Blo 1160639 1308361 := bbase (se 2 (by rfl) ⟨490635, by rfl⟩ : syracuseStep 1308361 = 981271) (by norm_num)
theorem B1963757 : Blo 1160639 1963757 := bbase (se 3 (by rfl) ⟨368204, by rfl⟩ : syracuseStep 1963757 = 736409) (by norm_num)
theorem B1308397 : Blo 1160639 1308397 := bbase (se 3 (by rfl) ⟨245324, by rfl⟩ : syracuseStep 1308397 = 490649) (by norm_num)
theorem B2619125 : Blo 1160639 2619125 := bbase (se 5 (by rfl) ⟨122771, by rfl⟩ : syracuseStep 2619125 = 245543) (by norm_num)
theorem B1865477 : Blo 1160639 1865477 := bbase (se 4 (by rfl) ⟨174888, by rfl⟩ : syracuseStep 1865477 = 349777) (by norm_num)
theorem B1308433 : Blo 1160639 1308433 := bbase (se 2 (by rfl) ⟨490662, by rfl⟩ : syracuseStep 1308433 = 981325) (by norm_num)
theorem B1308469 : Blo 1160639 1308469 := bbase (se 5 (by rfl) ⟨61334, by rfl⟩ : syracuseStep 1308469 = 122669) (by norm_num)
theorem B5895989 : Blo 1160639 5895989 := bbase (se 5 (by rfl) ⟨276374, by rfl⟩ : syracuseStep 5895989 = 552749) (by norm_num)
theorem B2619197 : Blo 1160639 2619197 := bbase (se 3 (by rfl) ⟨491099, by rfl⟩ : syracuseStep 2619197 = 982199) (by norm_num)
theorem B2946901 : Blo 1160639 2946901 := bbase (se 9 (by rfl) ⟨8633, by rfl⟩ : syracuseStep 2946901 = 17267) (by norm_num)
theorem B1308505 : Blo 1160639 1308505 := bbase (se 2 (by rfl) ⟨490689, by rfl⟩ : syracuseStep 1308505 = 981379) (by norm_num)
theorem B1472357 : Blo 1160639 1472357 := bbase (se 4 (by rfl) ⟨138033, by rfl⟩ : syracuseStep 1472357 = 276067) (by norm_num)
theorem B3929957 : Blo 1160639 3929957 := bbase (se 4 (by rfl) ⟨368433, by rfl⟩ : syracuseStep 3929957 = 736867) (by norm_num)
theorem B1963885 : Blo 1160639 1963885 := bbase (se 3 (by rfl) ⟨368228, by rfl⟩ : syracuseStep 1963885 = 736457) (by norm_num)
theorem B1308541 : Blo 1160639 1308541 := bbase (se 3 (by rfl) ⟨245351, by rfl⟩ : syracuseStep 1308541 = 490703) (by norm_num)
theorem B2619269 : Blo 1160639 2619269 := bbase (se 4 (by rfl) ⟨245556, by rfl⟩ : syracuseStep 2619269 = 491113) (by norm_num)
theorem B1472413 : Blo 1160639 1472413 := bbase (se 3 (by rfl) ⟨276077, by rfl⟩ : syracuseStep 1472413 = 552155) (by norm_num)
theorem B1308577 : Blo 1160639 1308577 := bbase (se 2 (by rfl) ⟨490716, by rfl⟩ : syracuseStep 1308577 = 981433) (by norm_num)
theorem B1177513 : Blo 1160639 1177513 := bbase (se 2 (by rfl) ⟨441567, by rfl⟩ : syracuseStep 1177513 = 883135) (by norm_num)
theorem B1767341 : Blo 1160639 1767341 := bbase (se 3 (by rfl) ⟨331376, by rfl⟩ : syracuseStep 1767341 = 662753) (by norm_num)
theorem B1963973 : Blo 1160639 1963973 := bbase (se 4 (by rfl) ⟨184122, by rfl⟩ : syracuseStep 1963973 = 368245) (by norm_num)
theorem B1308613 : Blo 1160639 1308613 := bbase (se 4 (by rfl) ⟨122682, by rfl⟩ : syracuseStep 1308613 = 245365) (by norm_num)
theorem B2947013 : Blo 1160639 2947013 := bbase (se 4 (by rfl) ⟨276282, by rfl⟩ : syracuseStep 2947013 = 552565) (by norm_num)
theorem B2619341 : Blo 1160639 2619341 := bbase (se 3 (by rfl) ⟨491126, by rfl⟩ : syracuseStep 2619341 = 982253) (by norm_num)
theorem B1308649 : Blo 1160639 1308649 := bbase (se 2 (by rfl) ⟨490743, by rfl⟩ : syracuseStep 1308649 = 981487) (by norm_num)
theorem B1472509 : Blo 1160639 1472509 := bbase (se 3 (by rfl) ⟨276095, by rfl⟩ : syracuseStep 1472509 = 552191) (by norm_num)
theorem B1308685 : Blo 1160639 1308685 := bbase (se 3 (by rfl) ⟨245378, by rfl⟩ : syracuseStep 1308685 = 490757) (by norm_num)
theorem B2619413 : Blo 1160639 2619413 := bbase (se 6 (by rfl) ⟨61392, by rfl⟩ : syracuseStep 2619413 = 122785) (by norm_num)
theorem B1308721 : Blo 1160639 1308721 := bbase (se 2 (by rfl) ⟨490770, by rfl⟩ : syracuseStep 1308721 = 981541) (by norm_num)
theorem B1964101 : Blo 1160639 1964101 := bbase (se 4 (by rfl) ⟨184134, by rfl⟩ : syracuseStep 1964101 = 368269) (by norm_num)
theorem B1308757 : Blo 1160639 1308757 := bbase (se 8 (by rfl) ⟨7668, by rfl⟩ : syracuseStep 1308757 = 15337) (by norm_num)
theorem B2619485 : Blo 1160639 2619485 := bbase (se 3 (by rfl) ⟨491153, by rfl⟩ : syracuseStep 2619485 = 982307) (by norm_num)
theorem B4421749 : Blo 1160639 4421749 := bbase (se 5 (by rfl) ⟨207269, by rfl⟩ : syracuseStep 4421749 = 414539) (by norm_num)
theorem B1308793 : Blo 1160639 1308793 := bbase (se 2 (by rfl) ⟨490797, by rfl⟩ : syracuseStep 1308793 = 981595) (by norm_num)
theorem B2947205 : Blo 1160639 2947205 := bbase (se 4 (by rfl) ⟨276300, by rfl⟩ : syracuseStep 2947205 = 552601) (by norm_num)
theorem B1308829 : Blo 1160639 1308829 := bbase (se 3 (by rfl) ⟨245405, by rfl⟩ : syracuseStep 1308829 = 490811) (by norm_num)
theorem B1964189 : Blo 1160639 1964189 := bbase (se 3 (by rfl) ⟨368285, by rfl⟩ : syracuseStep 1964189 = 736571) (by norm_num)
theorem B2619557 : Blo 1160639 2619557 := bbase (se 4 (by rfl) ⟨245583, by rfl⟩ : syracuseStep 2619557 = 491167) (by norm_num)
theorem B1472681 : Blo 1160639 1472681 := bbase (se 2 (by rfl) ⟨552255, by rfl⟩ : syracuseStep 1472681 = 1104511) (by norm_num)
theorem B1308865 : Blo 1160639 1308865 := bbase (se 2 (by rfl) ⟨490824, by rfl⟩ : syracuseStep 1308865 = 981649) (by norm_num)
theorem B4192469 : Blo 1160639 4192469 := bbase (se 7 (by rfl) ⟨49130, by rfl⟩ : syracuseStep 4192469 = 98261) (by norm_num)
theorem B1472737 : Blo 1160639 1472737 := bbase (se 2 (by rfl) ⟨552276, by rfl⟩ : syracuseStep 1472737 = 1104553) (by norm_num)
theorem B1243361 : Blo 1160639 1243361 := bbase (se 2 (by rfl) ⟨466260, by rfl⟩ : syracuseStep 1243361 = 932521) (by norm_num)
theorem B1308901 : Blo 1160639 1308901 := bbase (se 4 (by rfl) ⟨122709, by rfl⟩ : syracuseStep 1308901 = 245419) (by norm_num)
theorem B2619629 : Blo 1160639 2619629 := bbase (se 3 (by rfl) ⟨491180, by rfl⟩ : syracuseStep 2619629 = 982361) (by norm_num)
theorem B1308937 : Blo 1160639 1308937 := bbase (se 2 (by rfl) ⟨490851, by rfl⟩ : syracuseStep 1308937 = 981703) (by norm_num)
theorem B3930389 : Blo 1160639 3930389 := bbase (se 6 (by rfl) ⟨92118, by rfl⟩ : syracuseStep 3930389 = 184237) (by norm_num)
theorem B1964317 : Blo 1160639 1964317 := bbase (se 3 (by rfl) ⟨368309, by rfl⟩ : syracuseStep 1964317 = 736619) (by norm_num)
theorem B1308973 : Blo 1160639 1308973 := bbase (se 3 (by rfl) ⟨245432, by rfl⟩ : syracuseStep 1308973 = 490865) (by norm_num)
theorem B2619701 : Blo 1160639 2619701 := bbase (se 5 (by rfl) ⟨122798, by rfl⟩ : syracuseStep 2619701 = 245597) (by norm_num)
theorem B1472833 : Blo 1160639 1472833 := bbase (se 2 (by rfl) ⟨552312, by rfl⟩ : syracuseStep 1472833 = 1104625) (by norm_num)
theorem B1309009 : Blo 1160639 1309009 := bbase (se 2 (by rfl) ⟨490878, by rfl⟩ : syracuseStep 1309009 = 981757) (by norm_num)
theorem B1309045 : Blo 1160639 1309045 := bbase (se 5 (by rfl) ⟨61361, by rfl⟩ : syracuseStep 1309045 = 122723) (by norm_num)
theorem B1964405 : Blo 1160639 1964405 := bbase (se 5 (by rfl) ⟨92081, by rfl⟩ : syracuseStep 1964405 = 184163) (by norm_num)
theorem B2619773 : Blo 1160639 2619773 := bbase (se 3 (by rfl) ⟨491207, by rfl⟩ : syracuseStep 2619773 = 982415) (by norm_num)
theorem B1309081 : Blo 1160639 1309081 := bbase (se 2 (by rfl) ⟨490905, by rfl⟩ : syracuseStep 1309081 = 981811) (by norm_num)
theorem B1243549 : Blo 1160639 1243549 := bbase (se 3 (by rfl) ⟨233165, by rfl⟩ : syracuseStep 1243549 = 466331) (by norm_num)
theorem B1309117 : Blo 1160639 1309117 := bbase (se 3 (by rfl) ⟨245459, by rfl⟩ : syracuseStep 1309117 = 490919) (by norm_num)
theorem B2619845 : Blo 1160639 2619845 := bbase (se 4 (by rfl) ⟨245610, by rfl⟩ : syracuseStep 2619845 = 491221) (by norm_num)
theorem B1767901 : Blo 1160639 1767901 := bbase (se 3 (by rfl) ⟨331481, by rfl⟩ : syracuseStep 1767901 = 662963) (by norm_num)
theorem B2947549 : Blo 1160639 2947549 := bbase (se 3 (by rfl) ⟨552665, by rfl⟩ : syracuseStep 2947549 = 1105331) (by norm_num)
theorem B1309153 : Blo 1160639 1309153 := bbase (se 2 (by rfl) ⟨490932, by rfl⟩ : syracuseStep 1309153 = 981865) (by norm_num)
theorem B1473005 : Blo 1160639 1473005 := bbase (se 3 (by rfl) ⟨276188, by rfl⟩ : syracuseStep 1473005 = 552377) (by norm_num)
theorem B1964533 : Blo 1160639 1964533 := bbase (se 5 (by rfl) ⟨92087, by rfl⟩ : syracuseStep 1964533 = 184175) (by norm_num)
theorem B4717061 : Blo 1160639 4717061 := bbase (se 4 (by rfl) ⟨442224, by rfl⟩ : syracuseStep 4717061 = 884449) (by norm_num)
theorem B1309189 : Blo 1160639 1309189 := bbase (se 4 (by rfl) ⟨122736, by rfl⟩ : syracuseStep 1309189 = 245473) (by norm_num)
theorem B2619917 : Blo 1160639 2619917 := bbase (se 3 (by rfl) ⟨491234, by rfl⟩ : syracuseStep 2619917 = 982469) (by norm_num)
theorem B1473061 : Blo 1160639 1473061 := bbase (se 4 (by rfl) ⟨138099, by rfl⟩ : syracuseStep 1473061 = 276199) (by norm_num)
theorem B1309225 : Blo 1160639 1309225 := bbase (se 2 (by rfl) ⟨490959, by rfl⟩ : syracuseStep 1309225 = 981919) (by norm_num)
theorem B1309261 : Blo 1160639 1309261 := bbase (se 3 (by rfl) ⟨245486, by rfl⟩ : syracuseStep 1309261 = 490973) (by norm_num)
theorem B1964621 : Blo 1160639 1964621 := bbase (se 3 (by rfl) ⟨368366, by rfl⟩ : syracuseStep 1964621 = 736733) (by norm_num)
theorem B2947661 : Blo 1160639 2947661 := bbase (se 3 (by rfl) ⟨552686, by rfl⟩ : syracuseStep 2947661 = 1105373) (by norm_num)
theorem B2619989 : Blo 1160639 2619989 := bbase (se 8 (by rfl) ⟨15351, by rfl⟩ : syracuseStep 2619989 = 30703) (by norm_num)
theorem B1309297 : Blo 1160639 1309297 := bbase (se 2 (by rfl) ⟨490986, by rfl⟩ : syracuseStep 1309297 = 981973) (by norm_num)
theorem B1473157 : Blo 1160639 1473157 := bbase (se 4 (by rfl) ⟨138108, by rfl⟩ : syracuseStep 1473157 = 276217) (by norm_num)
theorem B1309333 : Blo 1160639 1309333 := bbase (se 6 (by rfl) ⟨30687, by rfl⟩ : syracuseStep 1309333 = 61375) (by norm_num)
theorem B2620061 : Blo 1160639 2620061 := bbase (se 3 (by rfl) ⟨491261, by rfl⟩ : syracuseStep 2620061 = 982523) (by norm_num)
theorem B1309369 : Blo 1160639 1309369 := bbase (se 2 (by rfl) ⟨491013, by rfl⟩ : syracuseStep 1309369 = 982027) (by norm_num)
theorem B1342157 : Blo 1160639 1342157 := bbase (se 3 (by rfl) ⟨251654, by rfl⟩ : syracuseStep 1342157 = 503309) (by norm_num)
theorem B1964749 : Blo 1160639 1964749 := bbase (se 3 (by rfl) ⟨368390, by rfl⟩ : syracuseStep 1964749 = 736781) (by norm_num)
theorem B1309405 : Blo 1160639 1309405 := bbase (se 3 (by rfl) ⟨245513, by rfl⟩ : syracuseStep 1309405 = 491027) (by norm_num)
theorem B2620133 : Blo 1160639 2620133 := bbase (se 4 (by rfl) ⟨245637, by rfl⟩ : syracuseStep 2620133 = 491275) (by norm_num)
theorem B3144437 : Blo 1160639 3144437 := bbase (se 5 (by rfl) ⟨147395, by rfl⟩ : syracuseStep 3144437 = 294791) (by norm_num)
theorem B1309441 : Blo 1160639 1309441 := bbase (se 2 (by rfl) ⟨491040, by rfl⟩ : syracuseStep 1309441 = 982081) (by norm_num)
theorem B3308293 : Blo 1160639 3308293 := bbase (se 4 (by rfl) ⟨310152, by rfl⟩ : syracuseStep 3308293 = 620305) (by norm_num)
theorem B2947853 : Blo 1160639 2947853 := bbase (se 3 (by rfl) ⟨552722, by rfl⟩ : syracuseStep 2947853 = 1105445) (by norm_num)
theorem B4193045 : Blo 1160639 4193045 := bbase (se 6 (by rfl) ⟨98274, by rfl⟩ : syracuseStep 4193045 = 196549) (by norm_num)
theorem B1309477 : Blo 1160639 1309477 := bbase (se 4 (by rfl) ⟨122763, by rfl⟩ : syracuseStep 1309477 = 245527) (by norm_num)
theorem B1964837 : Blo 1160639 1964837 := bbase (se 4 (by rfl) ⟨184203, by rfl⟩ : syracuseStep 1964837 = 368407) (by norm_num)
theorem B2620205 : Blo 1160639 2620205 := bbase (se 3 (by rfl) ⟨491288, by rfl⟩ : syracuseStep 2620205 = 982577) (by norm_num)
theorem B1473329 : Blo 1160639 1473329 := bbase (se 2 (by rfl) ⟨552498, by rfl⟩ : syracuseStep 1473329 = 1104997) (by norm_num)
theorem B1309513 : Blo 1160639 1309513 := bbase (se 2 (by rfl) ⟨491067, by rfl⟩ : syracuseStep 1309513 = 982135) (by norm_num)
theorem B1473385 : Blo 1160639 1473385 := bbase (se 2 (by rfl) ⟨552519, by rfl⟩ : syracuseStep 1473385 = 1105039) (by norm_num)
theorem B1309549 : Blo 1160639 1309549 := bbase (se 3 (by rfl) ⟨245540, by rfl⟩ : syracuseStep 1309549 = 491081) (by norm_num)
theorem B2620277 : Blo 1160639 2620277 := bbase (se 5 (by rfl) ⟨122825, by rfl⟩ : syracuseStep 2620277 = 245651) (by norm_num)
theorem B1309585 : Blo 1160639 1309585 := bbase (se 2 (by rfl) ⟨491094, by rfl⟩ : syracuseStep 1309585 = 982189) (by norm_num)
theorem B1964965 : Blo 1160639 1964965 := bbase (se 4 (by rfl) ⟨184215, by rfl⟩ : syracuseStep 1964965 = 368431) (by norm_num)
theorem B1309621 : Blo 1160639 1309621 := bbase (se 5 (by rfl) ⟨61388, by rfl⟩ : syracuseStep 1309621 = 122777) (by norm_num)
theorem B2620349 : Blo 1160639 2620349 := bbase (se 3 (by rfl) ⟨491315, by rfl⟩ : syracuseStep 2620349 = 982631) (by norm_num)
theorem B1473481 : Blo 1160639 1473481 := bbase (se 2 (by rfl) ⟨552555, by rfl⟩ : syracuseStep 1473481 = 1105111) (by norm_num)
theorem B1309657 : Blo 1160639 1309657 := bbase (se 2 (by rfl) ⟨491121, by rfl⟩ : syracuseStep 1309657 = 982243) (by norm_num)
theorem B2653165 : Blo 1160639 2653165 := bbase (se 3 (by rfl) ⟨497468, by rfl⟩ : syracuseStep 2653165 = 994937) (by norm_num)
theorem B1309693 : Blo 1160639 1309693 := bbase (se 3 (by rfl) ⟨245567, by rfl⟩ : syracuseStep 1309693 = 491135) (by norm_num)
theorem B1965053 : Blo 1160639 1965053 := bbase (se 3 (by rfl) ⟨368447, by rfl⟩ : syracuseStep 1965053 = 736895) (by norm_num)
theorem B2620421 : Blo 1160639 2620421 := bbase (se 4 (by rfl) ⟨245664, by rfl⟩ : syracuseStep 2620421 = 491329) (by norm_num)
theorem B1178645 : Blo 1160639 1178645 := bbase (se 6 (by rfl) ⟨27624, by rfl⟩ : syracuseStep 1178645 = 55249) (by norm_num)
theorem B1309729 : Blo 1160639 1309729 := bbase (se 2 (by rfl) ⟨491148, by rfl⟩ : syracuseStep 1309729 = 982297) (by norm_num)
theorem B1309765 : Blo 1160639 1309765 := bbase (se 4 (by rfl) ⟨122790, by rfl⟩ : syracuseStep 1309765 = 245581) (by norm_num)
theorem B1309801 : Blo 1160639 1309801 := bbase (se 2 (by rfl) ⟨491175, by rfl⟩ : syracuseStep 1309801 = 982351) (by norm_num)
theorem B1473653 : Blo 1160639 1473653 := bbase (se 5 (by rfl) ⟨69077, by rfl⟩ : syracuseStep 1473653 = 138155) (by norm_num)
theorem B1965181 : Blo 1160639 1965181 := bbase (se 3 (by rfl) ⟨368471, by rfl⟩ : syracuseStep 1965181 = 736943) (by norm_num)
theorem B1309837 : Blo 1160639 1309837 := bbase (se 3 (by rfl) ⟨245594, by rfl⟩ : syracuseStep 1309837 = 491189) (by norm_num)
theorem B1473709 : Blo 1160639 1473709 := bbase (se 3 (by rfl) ⟨276320, by rfl⟩ : syracuseStep 1473709 = 552641) (by norm_num)
theorem B1309873 : Blo 1160639 1309873 := bbase (se 2 (by rfl) ⟨491202, by rfl⟩ : syracuseStep 1309873 = 982405) (by norm_num)
theorem B5962949 : Blo 1160639 5962949 := bbase (se 4 (by rfl) ⟨559026, by rfl⟩ : syracuseStep 5962949 = 1118053) (by norm_num)
theorem B1309909 : Blo 1160639 1309909 := bbase (se 7 (by rfl) ⟨15350, by rfl⟩ : syracuseStep 1309909 = 30701) (by norm_num)
theorem B1965269 : Blo 1160639 1965269 := bbase (se 7 (by rfl) ⟨23030, by rfl⟩ : syracuseStep 1965269 = 46061) (by norm_num)
theorem B1309945 : Blo 1160639 1309945 := bbase (se 2 (by rfl) ⟨491229, by rfl⟩ : syracuseStep 1309945 = 982459) (by norm_num)
theorem B1473805 : Blo 1160639 1473805 := bbase (se 3 (by rfl) ⟨276338, by rfl⟩ : syracuseStep 1473805 = 552677) (by norm_num)
theorem B1309981 : Blo 1160639 1309981 := bbase (se 3 (by rfl) ⟨245621, by rfl⟩ : syracuseStep 1309981 = 491243) (by norm_num)
theorem B1310017 : Blo 1160639 1310017 := bbase (se 2 (by rfl) ⟨491256, by rfl⟩ : syracuseStep 1310017 = 982513) (by norm_num)
theorem B2686285 : Blo 1160639 2686285 := bbase (se 3 (by rfl) ⟨503678, by rfl⟩ : syracuseStep 2686285 = 1007357) (by norm_num)
theorem B1310053 : Blo 1160639 1310053 := bbase (se 4 (by rfl) ⟨122817, by rfl⟩ : syracuseStep 1310053 = 245635) (by norm_num)
theorem B1310089 : Blo 1160639 1310089 := bbase (se 2 (by rfl) ⟨491283, by rfl⟩ : syracuseStep 1310089 = 982567) (by norm_num)
theorem B1310125 : Blo 1160639 1310125 := bbase (se 3 (by rfl) ⟨245648, by rfl⟩ : syracuseStep 1310125 = 491297) (by norm_num)
theorem B1473977 : Blo 1160639 1473977 := bbase (se 2 (by rfl) ⟨552741, by rfl⟩ : syracuseStep 1473977 = 1105483) (by norm_num)
theorem B2358725 : Blo 1160639 2358725 := bbase (se 4 (by rfl) ⟨221130, by rfl⟩ : syracuseStep 2358725 = 442261) (by norm_num)
theorem B1310161 : Blo 1160639 1310161 := bbase (se 2 (by rfl) ⟨491310, by rfl⟩ : syracuseStep 1310161 = 982621) (by norm_num)
theorem B2358757 : Blo 1160639 2358757 := bbase (se 4 (by rfl) ⟨221133, by rfl⟩ : syracuseStep 2358757 = 442267) (by norm_num)
theorem B1310197 : Blo 1160639 1310197 := bbase (se 5 (by rfl) ⟨61415, by rfl⟩ : syracuseStep 1310197 = 122831) (by norm_num)
theorem B1343045 : Blo 1160639 1343045 := bbase (se 4 (by rfl) ⟨125910, by rfl⟩ : syracuseStep 1343045 = 251821) (by norm_num)
theorem B1179209 : Blo 1160639 1179209 := bbase (se 2 (by rfl) ⟨442203, by rfl⟩ : syracuseStep 1179209 = 884407) (by norm_num)
theorem B1179229 : Blo 1160639 1179229 := bbase (se 3 (by rfl) ⟨221105, by rfl⟩ : syracuseStep 1179229 = 442211) (by norm_num)
theorem B2981485 : Blo 1160639 2981485 := bbase (se 3 (by rfl) ⟨559028, by rfl⟩ : syracuseStep 2981485 = 1118057) (by norm_num)
theorem B6618773 : Blo 1160639 6618773 := bbase (se 6 (by rfl) ⟨155127, by rfl⟩ : syracuseStep 6618773 = 310255) (by norm_num)
theorem B4718357 : Blo 1160639 4718357 := bbase (se 6 (by rfl) ⟨110586, by rfl⟩ : syracuseStep 4718357 = 221173) (by norm_num)
theorem B7438229 : Blo 1160639 7438229 := bbase (se 6 (by rfl) ⟨174333, by rfl⟩ : syracuseStep 7438229 = 348667) (by norm_num)
theorem B8814581 : Blo 1160639 8814581 := bbase (se 5 (by rfl) ⟨413183, by rfl⟩ : syracuseStep 8814581 = 826367) (by norm_num)
theorem B7077923 : Blo 1160639 7077923 := bstep (se 1 (by rfl) ⟨5308442, by rfl⟩ : syracuseStep 7077923 = 10616885) B10616885
theorem B1769555 : Blo 1160639 1769555 := bstep (se 1 (by rfl) ⟨1327166, by rfl⟩ : syracuseStep 1769555 = 2654333) B2654333
theorem B2654513 : Blo 1160639 2654513 := bstep (se 2 (by rfl) ⟨995442, by rfl⟩ : syracuseStep 2654513 = 1990885) B1990885
theorem B2359633 : Blo 1160639 2359633 := bstep (se 2 (by rfl) ⟨884862, by rfl⟩ : syracuseStep 2359633 = 1769725) B1769725
theorem B3309923 : Blo 1160639 3309923 := bstep (se 1 (by rfl) ⟨2482442, by rfl⟩ : syracuseStep 3309923 = 4964885) B4964885
theorem B4194659 : Blo 1160639 4194659 := bstep (se 1 (by rfl) ⟨3145994, by rfl⟩ : syracuseStep 4194659 = 6291989) B6291989
theorem B2359697 : Blo 1160639 2359697 := bstep (se 2 (by rfl) ⟨884886, by rfl⟩ : syracuseStep 2359697 = 1769773) B1769773
theorem B1770115 : Blo 1160639 1770115 := bstep (se 1 (by rfl) ⟨1327586, by rfl⟩ : syracuseStep 1770115 = 2655173) B2655173
theorem B3310253 : Blo 1160639 3310253 := bstep (se 3 (by rfl) ⟨620672, by rfl⟩ : syracuseStep 3310253 = 1241345) B1241345
theorem B3539693 : Blo 1160639 3539693 := bstep (se 3 (by rfl) ⟨663692, by rfl⟩ : syracuseStep 3539693 = 1327385) B1327385
theorem B3310321 : Blo 1160639 3310321 := bstep (se 2 (by rfl) ⟨1241370, by rfl⟩ : syracuseStep 3310321 = 2482741) B2482741
theorem B1770419 : Blo 1160639 1770419 := bstep (se 1 (by rfl) ⟨1327814, by rfl⟩ : syracuseStep 1770419 = 2655629) B2655629
theorem B4031441 : Blo 1160639 4031441 := bstep (se 2 (by rfl) ⟨1511790, by rfl⟩ : syracuseStep 4031441 = 3023581) B3023581
theorem B3310595 : Blo 1160639 3310595 := bstep (se 1 (by rfl) ⟨2482946, by rfl⟩ : syracuseStep 3310595 = 4965893) B4965893
theorem B3540131 : Blo 1160639 3540131 := bstep (se 1 (by rfl) ⟨2655098, by rfl⟩ : syracuseStep 3540131 = 5310197) B5310197
theorem B3311437 : Blo 1160639 3311437 := bstep (se 3 (by rfl) ⟨620894, by rfl⟩ : syracuseStep 3311437 = 1241789) B1241789
theorem B8816525 : Blo 1160639 8816525 := bstep (se 3 (by rfl) ⟨1653098, by rfl⟩ : syracuseStep 8816525 = 3306197) B3306197
theorem B3311597 : Blo 1160639 3311597 := bstep (se 3 (by rfl) ⟨620924, by rfl⟩ : syracuseStep 3311597 = 1241849) B1241849
theorem B3311779 : Blo 1160639 3311779 := bstep (se 1 (by rfl) ⟨2483834, by rfl⟩ : syracuseStep 3311779 = 4967669) B4967669
theorem B7081037 : Blo 1160639 7081037 := bstep (se 3 (by rfl) ⟨1327694, by rfl⟩ : syracuseStep 7081037 = 2655389) B2655389
theorem B14158961 : Blo 1160639 14158961 := bstep (se 2 (by rfl) ⟨5309610, by rfl⟩ : syracuseStep 14158961 = 10619221) B10619221
theorem B2788835 : Blo 1160639 2788835 := bstep (se 1 (by rfl) ⟨2091626, by rfl⟩ : syracuseStep 2788835 = 4183253) B4183253
theorem B3313169 : Blo 1160639 3313169 := bstep (se 2 (by rfl) ⟨1242438, by rfl⟩ : syracuseStep 3313169 = 2484877) B2484877
theorem B2788913 : Blo 1160639 2788913 := bstep (se 2 (by rfl) ⟨1045842, by rfl⟩ : syracuseStep 2788913 = 2091685) B2091685
theorem B7442225 : Blo 1160639 7442225 := bstep (se 2 (by rfl) ⟨2790834, by rfl⟩ : syracuseStep 7442225 = 5581669) B5581669
theorem B2789297 : Blo 1160639 2789297 := bstep (se 2 (by rfl) ⟨1045986, by rfl⟩ : syracuseStep 2789297 = 2091973) B2091973
theorem B37654469 : Blo 1160639 37654469 := bstep (se 4 (by rfl) ⟨3530106, by rfl⟩ : syracuseStep 37654469 = 7060213) B7060213
theorem B1740977 : Blo 1160639 1740977 := bstep (se 2 (by rfl) ⟨652866, by rfl⟩ : syracuseStep 1740977 = 1305733) B1305733
theorem B1740995 : Blo 1160639 1740995 := bstep (se 1 (by rfl) ⟨1305746, by rfl⟩ : syracuseStep 1740995 = 2611493) B2611493
theorem B1741025 : Blo 1160639 1741025 := bstep (se 2 (by rfl) ⟨652884, by rfl⟩ : syracuseStep 1741025 = 1305769) B1305769
theorem B1741043 : Blo 1160639 1741043 := bstep (se 1 (by rfl) ⟨1305782, by rfl⟩ : syracuseStep 1741043 = 2611565) B2611565
theorem B1741073 : Blo 1160639 1741073 := bstep (se 2 (by rfl) ⟨652902, by rfl⟩ : syracuseStep 1741073 = 1305805) B1305805
theorem B1741091 : Blo 1160639 1741091 := bstep (se 1 (by rfl) ⟨1305818, by rfl⟩ : syracuseStep 1741091 = 2611637) B2611637
theorem B1741121 : Blo 1160639 1741121 := bstep (se 2 (by rfl) ⟨652920, by rfl⟩ : syracuseStep 1741121 = 1305841) B1305841
theorem B8163661 : Blo 1160639 8163661 := bstep (se 3 (by rfl) ⟨1530686, by rfl⟩ : syracuseStep 8163661 = 3061373) B3061373
theorem B1741139 : Blo 1160639 1741139 := bstep (se 1 (by rfl) ⟨1305854, by rfl⟩ : syracuseStep 1741139 = 2611709) B2611709
theorem B1741169 : Blo 1160639 1741169 := bstep (se 2 (by rfl) ⟨652938, by rfl⟩ : syracuseStep 1741169 = 1305877) B1305877
theorem B1741187 : Blo 1160639 1741187 := bstep (se 1 (by rfl) ⟨1305890, by rfl⟩ : syracuseStep 1741187 = 2611781) B2611781
theorem B1741217 : Blo 1160639 1741217 := bstep (se 2 (by rfl) ⟨652956, by rfl⟩ : syracuseStep 1741217 = 1305913) B1305913
theorem B1741235 : Blo 1160639 1741235 := bstep (se 1 (by rfl) ⟨1305926, by rfl⟩ : syracuseStep 1741235 = 2611853) B2611853
theorem B3314125 : Blo 1160639 3314125 := bstep (se 3 (by rfl) ⟨621398, by rfl⟩ : syracuseStep 3314125 = 1242797) B1242797
theorem B1741265 : Blo 1160639 1741265 := bstep (se 2 (by rfl) ⟨652974, by rfl⟩ : syracuseStep 1741265 = 1305949) B1305949
theorem B1741283 : Blo 1160639 1741283 := bstep (se 1 (by rfl) ⟨1305962, by rfl⟩ : syracuseStep 1741283 = 2611925) B2611925
theorem B1741313 : Blo 1160639 1741313 := bstep (se 2 (by rfl) ⟨652992, by rfl⟩ : syracuseStep 1741313 = 1305985) B1305985
theorem B1741331 : Blo 1160639 1741331 := bstep (se 1 (by rfl) ⟨1305998, by rfl⟩ : syracuseStep 1741331 = 2611997) B2611997
theorem B1741361 : Blo 1160639 1741361 := bstep (se 2 (by rfl) ⟨653010, by rfl⟩ : syracuseStep 1741361 = 1306021) B1306021
theorem B1741379 : Blo 1160639 1741379 := bstep (se 1 (by rfl) ⟨1306034, by rfl⟩ : syracuseStep 1741379 = 2612069) B2612069
theorem B1741409 : Blo 1160639 1741409 := bstep (se 2 (by rfl) ⟨653028, by rfl⟩ : syracuseStep 1741409 = 1306057) B1306057
theorem B1741427 : Blo 1160639 1741427 := bstep (se 1 (by rfl) ⟨1306070, by rfl⟩ : syracuseStep 1741427 = 2612141) B2612141
theorem B1741457 : Blo 1160639 1741457 := bstep (se 2 (by rfl) ⟨653046, by rfl⟩ : syracuseStep 1741457 = 1306093) B1306093
theorem B1741475 : Blo 1160639 1741475 := bstep (se 1 (by rfl) ⟨1306106, by rfl⟩ : syracuseStep 1741475 = 2612213) B2612213
theorem B3314353 : Blo 1160639 3314353 := bstep (se 2 (by rfl) ⟨1242882, by rfl⟩ : syracuseStep 3314353 = 2485765) B2485765
theorem B1741505 : Blo 1160639 1741505 := bstep (se 2 (by rfl) ⟨653064, by rfl⟩ : syracuseStep 1741505 = 1306129) B1306129
theorem B1741523 : Blo 1160639 1741523 := bstep (se 1 (by rfl) ⟨1306142, by rfl⟩ : syracuseStep 1741523 = 2612285) B2612285
theorem B1741553 : Blo 1160639 1741553 := bstep (se 2 (by rfl) ⟨653082, by rfl⟩ : syracuseStep 1741553 = 1306165) B1306165
theorem B8819441 : Blo 1160639 8819441 := bstep (se 2 (by rfl) ⟨3307290, by rfl⟩ : syracuseStep 8819441 = 6614581) B6614581
theorem B1741571 : Blo 1160639 1741571 := bstep (se 1 (by rfl) ⟨1306178, by rfl⟩ : syracuseStep 1741571 = 2612357) B2612357
theorem B1741601 : Blo 1160639 1741601 := bstep (se 2 (by rfl) ⟨653100, by rfl⟩ : syracuseStep 1741601 = 1306201) B1306201
theorem B1741619 : Blo 1160639 1741619 := bstep (se 1 (by rfl) ⟨1306214, by rfl⟩ : syracuseStep 1741619 = 2612429) B2612429
theorem B1741649 : Blo 1160639 1741649 := bstep (se 2 (by rfl) ⟨653118, by rfl⟩ : syracuseStep 1741649 = 1306237) B1306237
theorem B3314513 : Blo 1160639 3314513 := bstep (se 2 (by rfl) ⟨1242942, by rfl⟩ : syracuseStep 3314513 = 2485885) B2485885
theorem B1741667 : Blo 1160639 1741667 := bstep (se 1 (by rfl) ⟨1306250, by rfl⟩ : syracuseStep 1741667 = 2612501) B2612501
theorem B1741697 : Blo 1160639 1741697 := bstep (se 2 (by rfl) ⟨653136, by rfl⟩ : syracuseStep 1741697 = 1306273) B1306273
theorem B1676161 : Blo 1160639 1676161 := bstep (se 2 (by rfl) ⟨628560, by rfl⟩ : syracuseStep 1676161 = 1257121) B1257121
theorem B1741715 : Blo 1160639 1741715 := bstep (se 1 (by rfl) ⟨1306286, by rfl⟩ : syracuseStep 1741715 = 2612573) B2612573
theorem B1741745 : Blo 1160639 1741745 := bstep (se 2 (by rfl) ⟨653154, by rfl⟩ : syracuseStep 1741745 = 1306309) B1306309
theorem B1741763 : Blo 1160639 1741763 := bstep (se 1 (by rfl) ⟨1306322, by rfl⟩ : syracuseStep 1741763 = 2612645) B2612645
theorem B3314627 : Blo 1160639 3314627 := bstep (se 1 (by rfl) ⟨2485970, by rfl⟩ : syracuseStep 3314627 = 4971941) B4971941
theorem B1741793 : Blo 1160639 1741793 := bstep (se 2 (by rfl) ⟨653172, by rfl⟩ : syracuseStep 1741793 = 1306345) B1306345
theorem B1741811 : Blo 1160639 1741811 := bstep (se 1 (by rfl) ⟨1306358, by rfl⟩ : syracuseStep 1741811 = 2612717) B2612717
theorem B1741841 : Blo 1160639 1741841 := bstep (se 2 (by rfl) ⟨653190, by rfl⟩ : syracuseStep 1741841 = 1306381) B1306381
theorem B1741859 : Blo 1160639 1741859 := bstep (se 1 (by rfl) ⟨1306394, by rfl⟩ : syracuseStep 1741859 = 2612789) B2612789
theorem B1741889 : Blo 1160639 1741889 := bstep (se 2 (by rfl) ⟨653208, by rfl⟩ : syracuseStep 1741889 = 1306417) B1306417
theorem B1741907 : Blo 1160639 1741907 := bstep (se 1 (by rfl) ⟨1306430, by rfl⟩ : syracuseStep 1741907 = 2612861) B2612861
theorem B1741937 : Blo 1160639 1741937 := bstep (se 2 (by rfl) ⟨653226, by rfl⟩ : syracuseStep 1741937 = 1306453) B1306453
theorem B1741955 : Blo 1160639 1741955 := bstep (se 1 (by rfl) ⟨1306466, by rfl⟩ : syracuseStep 1741955 = 2612933) B2612933
theorem B1741985 : Blo 1160639 1741985 := bstep (se 2 (by rfl) ⟨653244, by rfl⟩ : syracuseStep 1741985 = 1306489) B1306489
theorem B1742003 : Blo 1160639 1742003 := bstep (se 1 (by rfl) ⟨1306502, by rfl⟩ : syracuseStep 1742003 = 2613005) B2613005
theorem B1742033 : Blo 1160639 1742033 := bstep (se 2 (by rfl) ⟨653262, by rfl⟩ : syracuseStep 1742033 = 1306525) B1306525
theorem B1742051 : Blo 1160639 1742051 := bstep (se 1 (by rfl) ⟨1306538, by rfl⟩ : syracuseStep 1742051 = 2613077) B2613077
theorem B1742081 : Blo 1160639 1742081 := bstep (se 2 (by rfl) ⟨653280, by rfl⟩ : syracuseStep 1742081 = 1306561) B1306561
theorem B1742099 : Blo 1160639 1742099 := bstep (se 1 (by rfl) ⟨1306574, by rfl⟩ : syracuseStep 1742099 = 2613149) B2613149
theorem B1742129 : Blo 1160639 1742129 := bstep (se 2 (by rfl) ⟨653298, by rfl⟩ : syracuseStep 1742129 = 1306597) B1306597
theorem B1742147 : Blo 1160639 1742147 := bstep (se 1 (by rfl) ⟨1306610, by rfl⟩ : syracuseStep 1742147 = 2613221) B2613221
theorem B1742177 : Blo 1160639 1742177 := bstep (se 2 (by rfl) ⟨653316, by rfl⟩ : syracuseStep 1742177 = 1306633) B1306633
theorem B7968113 : Blo 1160639 7968113 := bstep (se 2 (by rfl) ⟨2988042, by rfl⟩ : syracuseStep 7968113 = 5976085) B5976085
theorem B1742195 : Blo 1160639 1742195 := bstep (se 1 (by rfl) ⟨1306646, by rfl⟩ : syracuseStep 1742195 = 2613293) B2613293
theorem B1742225 : Blo 1160639 1742225 := bstep (se 2 (by rfl) ⟨653334, by rfl⟩ : syracuseStep 1742225 = 1306669) B1306669
theorem B1742243 : Blo 1160639 1742243 := bstep (se 1 (by rfl) ⟨1306682, by rfl⟩ : syracuseStep 1742243 = 2613365) B2613365
theorem B1742273 : Blo 1160639 1742273 := bstep (se 2 (by rfl) ⟨653352, by rfl⟩ : syracuseStep 1742273 = 1306705) B1306705
theorem B1742291 : Blo 1160639 1742291 := bstep (se 1 (by rfl) ⟨1306718, by rfl⟩ : syracuseStep 1742291 = 2613437) B2613437
theorem B1742321 : Blo 1160639 1742321 := bstep (se 2 (by rfl) ⟨653370, by rfl⟩ : syracuseStep 1742321 = 1306741) B1306741
theorem B1742339 : Blo 1160639 1742339 := bstep (se 1 (by rfl) ⟨1306754, by rfl⟩ : syracuseStep 1742339 = 2613509) B2613509
theorem B1742369 : Blo 1160639 1742369 := bstep (se 2 (by rfl) ⟨653388, by rfl⟩ : syracuseStep 1742369 = 1306777) B1306777
theorem B1742387 : Blo 1160639 1742387 := bstep (se 1 (by rfl) ⟨1306790, by rfl⟩ : syracuseStep 1742387 = 2613581) B2613581
theorem B1742417 : Blo 1160639 1742417 := bstep (se 2 (by rfl) ⟨653406, by rfl⟩ : syracuseStep 1742417 = 1306813) B1306813
theorem B1742435 : Blo 1160639 1742435 := bstep (se 1 (by rfl) ⟨1306826, by rfl⟩ : syracuseStep 1742435 = 2613653) B2613653
theorem B1742465 : Blo 1160639 1742465 := bstep (se 2 (by rfl) ⟨653424, by rfl⟩ : syracuseStep 1742465 = 1306849) B1306849
theorem B2791057 : Blo 1160639 2791057 := bstep (se 2 (by rfl) ⟨1046646, by rfl⟩ : syracuseStep 2791057 = 2093293) B2093293
theorem B1742483 : Blo 1160639 1742483 := bstep (se 1 (by rfl) ⟨1306862, by rfl⟩ : syracuseStep 1742483 = 2613725) B2613725
theorem B1742513 : Blo 1160639 1742513 := bstep (se 2 (by rfl) ⟨653442, by rfl⟩ : syracuseStep 1742513 = 1306885) B1306885
theorem B1742531 : Blo 1160639 1742531 := bstep (se 1 (by rfl) ⟨1306898, by rfl⟩ : syracuseStep 1742531 = 2613797) B2613797
theorem B1742561 : Blo 1160639 1742561 := bstep (se 2 (by rfl) ⟨653460, by rfl⟩ : syracuseStep 1742561 = 1306921) B1306921
theorem B1742579 : Blo 1160639 1742579 := bstep (se 1 (by rfl) ⟨1306934, by rfl⟩ : syracuseStep 1742579 = 2613869) B2613869
theorem B1742609 : Blo 1160639 1742609 := bstep (se 2 (by rfl) ⟨653478, by rfl⟩ : syracuseStep 1742609 = 1306957) B1306957
theorem B1742627 : Blo 1160639 1742627 := bstep (se 1 (by rfl) ⟨1306970, by rfl⟩ : syracuseStep 1742627 = 2613941) B2613941
theorem B1742657 : Blo 1160639 1742657 := bstep (se 2 (by rfl) ⟨653496, by rfl⟩ : syracuseStep 1742657 = 1306993) B1306993
theorem B1742675 : Blo 1160639 1742675 := bstep (se 1 (by rfl) ⟨1307006, by rfl⟩ : syracuseStep 1742675 = 2614013) B2614013
theorem B1742705 : Blo 1160639 1742705 := bstep (se 2 (by rfl) ⟨653514, by rfl⟩ : syracuseStep 1742705 = 1307029) B1307029
theorem B1742723 : Blo 1160639 1742723 := bstep (se 1 (by rfl) ⟨1307042, by rfl⟩ : syracuseStep 1742723 = 2614085) B2614085
theorem B1742753 : Blo 1160639 1742753 := bstep (se 2 (by rfl) ⟨653532, by rfl⟩ : syracuseStep 1742753 = 1307065) B1307065
theorem B3315629 : Blo 1160639 3315629 := bstep (se 3 (by rfl) ⟨621680, by rfl⟩ : syracuseStep 3315629 = 1243361) B1243361
theorem B1742771 : Blo 1160639 1742771 := bstep (se 1 (by rfl) ⟨1307078, by rfl⟩ : syracuseStep 1742771 = 2614157) B2614157
theorem B1742801 : Blo 1160639 1742801 := bstep (se 2 (by rfl) ⟨653550, by rfl⟩ : syracuseStep 1742801 = 1307101) B1307101
theorem B1742819 : Blo 1160639 1742819 := bstep (se 1 (by rfl) ⟨1307114, by rfl⟩ : syracuseStep 1742819 = 2614229) B2614229
theorem B1742849 : Blo 1160639 1742849 := bstep (se 2 (by rfl) ⟨653568, by rfl⟩ : syracuseStep 1742849 = 1307137) B1307137
theorem B1742867 : Blo 1160639 1742867 := bstep (se 1 (by rfl) ⟨1307150, by rfl⟩ : syracuseStep 1742867 = 2614301) B2614301
theorem B1742897 : Blo 1160639 1742897 := bstep (se 2 (by rfl) ⟨653586, by rfl⟩ : syracuseStep 1742897 = 1307173) B1307173
theorem B1742915 : Blo 1160639 1742915 := bstep (se 1 (by rfl) ⟨1307186, by rfl⟩ : syracuseStep 1742915 = 2614373) B2614373
theorem B1742945 : Blo 1160639 1742945 := bstep (se 2 (by rfl) ⟨653604, by rfl⟩ : syracuseStep 1742945 = 1307209) B1307209
theorem B3315811 : Blo 1160639 3315811 := bstep (se 1 (by rfl) ⟨2486858, by rfl⟩ : syracuseStep 3315811 = 4973717) B4973717
theorem B1742963 : Blo 1160639 1742963 := bstep (se 1 (by rfl) ⟨1307222, by rfl⟩ : syracuseStep 1742963 = 2614445) B2614445
theorem B1742993 : Blo 1160639 1742993 := bstep (se 2 (by rfl) ⟨653622, by rfl⟩ : syracuseStep 1742993 = 1307245) B1307245
theorem B1743011 : Blo 1160639 1743011 := bstep (se 1 (by rfl) ⟨1307258, by rfl⟩ : syracuseStep 1743011 = 2614517) B2614517
theorem B1743041 : Blo 1160639 1743041 := bstep (se 2 (by rfl) ⟨653640, by rfl⟩ : syracuseStep 1743041 = 1307281) B1307281
theorem B7444685 : Blo 1160639 7444685 := bstep (se 3 (by rfl) ⟨1395878, by rfl⟩ : syracuseStep 7444685 = 2791757) B2791757
theorem B1743059 : Blo 1160639 1743059 := bstep (se 1 (by rfl) ⟨1307294, by rfl⟩ : syracuseStep 1743059 = 2614589) B2614589
theorem B8493283 : Blo 1160639 8493283 := bstep (se 1 (by rfl) ⟨6369962, by rfl⟩ : syracuseStep 8493283 = 12739925) B12739925
theorem B1743089 : Blo 1160639 1743089 := bstep (se 2 (by rfl) ⟨653658, by rfl⟩ : syracuseStep 1743089 = 1307317) B1307317
theorem B1743107 : Blo 1160639 1743107 := bstep (se 1 (by rfl) ⟨1307330, by rfl⟩ : syracuseStep 1743107 = 2614661) B2614661
theorem B3315971 : Blo 1160639 3315971 := bstep (se 1 (by rfl) ⟨2486978, by rfl⟩ : syracuseStep 3315971 = 4973957) B4973957
theorem B1743137 : Blo 1160639 1743137 := bstep (se 2 (by rfl) ⟨653676, by rfl⟩ : syracuseStep 1743137 = 1307353) B1307353
theorem B1743155 : Blo 1160639 1743155 := bstep (se 1 (by rfl) ⟨1307366, by rfl⟩ : syracuseStep 1743155 = 2614733) B2614733
theorem B1743185 : Blo 1160639 1743185 := bstep (se 2 (by rfl) ⟨653694, by rfl⟩ : syracuseStep 1743185 = 1307389) B1307389
theorem B1743203 : Blo 1160639 1743203 := bstep (se 1 (by rfl) ⟨1307402, by rfl⟩ : syracuseStep 1743203 = 2614805) B2614805
theorem B1743233 : Blo 1160639 1743233 := bstep (se 2 (by rfl) ⟨653712, by rfl⟩ : syracuseStep 1743233 = 1307425) B1307425
theorem B16783757 : Blo 1160639 16783757 := bstep (se 3 (by rfl) ⟨3146954, by rfl⟩ : syracuseStep 16783757 = 6293909) B6293909
theorem B1743251 : Blo 1160639 1743251 := bstep (se 1 (by rfl) ⟨1307438, by rfl⟩ : syracuseStep 1743251 = 2614877) B2614877
theorem B1743281 : Blo 1160639 1743281 := bstep (se 2 (by rfl) ⟨653730, by rfl⟩ : syracuseStep 1743281 = 1307461) B1307461
theorem B1743299 : Blo 1160639 1743299 := bstep (se 1 (by rfl) ⟨1307474, by rfl⟩ : syracuseStep 1743299 = 2614949) B2614949
theorem B1743329 : Blo 1160639 1743329 := bstep (se 2 (by rfl) ⟨653748, by rfl⟩ : syracuseStep 1743329 = 1307497) B1307497
theorem B1743347 : Blo 1160639 1743347 := bstep (se 1 (by rfl) ⟨1307510, by rfl⟩ : syracuseStep 1743347 = 2615021) B2615021
theorem B1743377 : Blo 1160639 1743377 := bstep (se 2 (by rfl) ⟨653766, by rfl⟩ : syracuseStep 1743377 = 1307533) B1307533
theorem B1743395 : Blo 1160639 1743395 := bstep (se 1 (by rfl) ⟨1307546, by rfl⟩ : syracuseStep 1743395 = 2615093) B2615093
theorem B1743425 : Blo 1160639 1743425 := bstep (se 2 (by rfl) ⟨653784, by rfl⟩ : syracuseStep 1743425 = 1307569) B1307569
theorem B1743443 : Blo 1160639 1743443 := bstep (se 1 (by rfl) ⟨1307582, by rfl⟩ : syracuseStep 1743443 = 2615165) B2615165
theorem B1743473 : Blo 1160639 1743473 := bstep (se 2 (by rfl) ⟨653802, by rfl⟩ : syracuseStep 1743473 = 1307605) B1307605
theorem B1743491 : Blo 1160639 1743491 := bstep (se 1 (by rfl) ⟨1307618, by rfl⟩ : syracuseStep 1743491 = 2615237) B2615237
theorem B1743521 : Blo 1160639 1743521 := bstep (se 2 (by rfl) ⟨653820, by rfl⟩ : syracuseStep 1743521 = 1307641) B1307641
theorem B1743539 : Blo 1160639 1743539 := bstep (se 1 (by rfl) ⟨1307654, by rfl⟩ : syracuseStep 1743539 = 2615309) B2615309
theorem B1743569 : Blo 1160639 1743569 := bstep (se 2 (by rfl) ⟨653838, by rfl⟩ : syracuseStep 1743569 = 1307677) B1307677
theorem B5577443 : Blo 1160639 5577443 := bstep (se 1 (by rfl) ⟨4183082, by rfl⟩ : syracuseStep 5577443 = 8366165) B8366165
theorem B1743587 : Blo 1160639 1743587 := bstep (se 1 (by rfl) ⟨1307690, by rfl⟩ : syracuseStep 1743587 = 2615381) B2615381
theorem B1743617 : Blo 1160639 1743617 := bstep (se 2 (by rfl) ⟨653856, by rfl⟩ : syracuseStep 1743617 = 1307713) B1307713
theorem B1743635 : Blo 1160639 1743635 := bstep (se 1 (by rfl) ⟨1307726, by rfl⟩ : syracuseStep 1743635 = 2615453) B2615453
theorem B1743665 : Blo 1160639 1743665 := bstep (se 2 (by rfl) ⟨653874, by rfl⟩ : syracuseStep 1743665 = 1307749) B1307749
theorem B1743683 : Blo 1160639 1743683 := bstep (se 1 (by rfl) ⟨1307762, by rfl⟩ : syracuseStep 1743683 = 2615525) B2615525
theorem B1743713 : Blo 1160639 1743713 := bstep (se 2 (by rfl) ⟨653892, by rfl⟩ : syracuseStep 1743713 = 1307785) B1307785
theorem B1743731 : Blo 1160639 1743731 := bstep (se 1 (by rfl) ⟨1307798, by rfl⟩ : syracuseStep 1743731 = 2615597) B2615597
theorem B1743761 : Blo 1160639 1743761 := bstep (se 2 (by rfl) ⟨653910, by rfl⟩ : syracuseStep 1743761 = 1307821) B1307821
theorem B1743779 : Blo 1160639 1743779 := bstep (se 1 (by rfl) ⟨1307834, by rfl⟩ : syracuseStep 1743779 = 2615669) B2615669
theorem B1743809 : Blo 1160639 1743809 := bstep (se 2 (by rfl) ⟨653928, by rfl⟩ : syracuseStep 1743809 = 1307857) B1307857
theorem B6626245 : Blo 1160639 6626245 := bstep (se 4 (by rfl) ⟨621210, by rfl⟩ : syracuseStep 6626245 = 1242421) B1242421
theorem B1743827 : Blo 1160639 1743827 := bstep (se 1 (by rfl) ⟨1307870, by rfl⟩ : syracuseStep 1743827 = 2615741) B2615741
theorem B1743857 : Blo 1160639 1743857 := bstep (se 2 (by rfl) ⟨653946, by rfl⟩ : syracuseStep 1743857 = 1307893) B1307893
theorem B1743875 : Blo 1160639 1743875 := bstep (se 1 (by rfl) ⟨1307906, by rfl⟩ : syracuseStep 1743875 = 2615813) B2615813
theorem B1743905 : Blo 1160639 1743905 := bstep (se 2 (by rfl) ⟨653964, by rfl⟩ : syracuseStep 1743905 = 1307929) B1307929
theorem B1743923 : Blo 1160639 1743923 := bstep (se 1 (by rfl) ⟨1307942, by rfl⟩ : syracuseStep 1743923 = 2615885) B2615885
theorem B1743953 : Blo 1160639 1743953 := bstep (se 2 (by rfl) ⟨653982, by rfl⟩ : syracuseStep 1743953 = 1307965) B1307965
theorem B1743971 : Blo 1160639 1743971 := bstep (se 1 (by rfl) ⟨1307978, by rfl⟩ : syracuseStep 1743971 = 2615957) B2615957
theorem B1744001 : Blo 1160639 1744001 := bstep (se 2 (by rfl) ⟨654000, by rfl⟩ : syracuseStep 1744001 = 1308001) B1308001
theorem B1744019 : Blo 1160639 1744019 := bstep (se 1 (by rfl) ⟨1308014, by rfl⟩ : syracuseStep 1744019 = 2616029) B2616029
theorem B1744049 : Blo 1160639 1744049 := bstep (se 2 (by rfl) ⟨654018, by rfl⟩ : syracuseStep 1744049 = 1308037) B1308037
theorem B1744067 : Blo 1160639 1744067 := bstep (se 1 (by rfl) ⟨1308050, by rfl⟩ : syracuseStep 1744067 = 2616101) B2616101
theorem B3579085 : Blo 1160639 3579085 := bstep (se 3 (by rfl) ⟨671078, by rfl⟩ : syracuseStep 3579085 = 1342157) B1342157
theorem B1744097 : Blo 1160639 1744097 := bstep (se 2 (by rfl) ⟨654036, by rfl⟩ : syracuseStep 1744097 = 1308073) B1308073
theorem B1744115 : Blo 1160639 1744115 := bstep (se 1 (by rfl) ⟨1308086, by rfl⟩ : syracuseStep 1744115 = 2616173) B2616173
theorem B1744145 : Blo 1160639 1744145 := bstep (se 2 (by rfl) ⟨654054, by rfl⟩ : syracuseStep 1744145 = 1308109) B1308109
theorem B1744163 : Blo 1160639 1744163 := bstep (se 1 (by rfl) ⟨1308122, by rfl⟩ : syracuseStep 1744163 = 2616245) B2616245
theorem B1744193 : Blo 1160639 1744193 := bstep (se 2 (by rfl) ⟨654072, by rfl⟩ : syracuseStep 1744193 = 1308145) B1308145
theorem B1744211 : Blo 1160639 1744211 := bstep (se 1 (by rfl) ⟨1308158, by rfl⟩ : syracuseStep 1744211 = 2616317) B2616317
theorem B1744241 : Blo 1160639 1744241 := bstep (se 2 (by rfl) ⟨654090, by rfl⟩ : syracuseStep 1744241 = 1308181) B1308181
theorem B1744259 : Blo 1160639 1744259 := bstep (se 1 (by rfl) ⟨1308194, by rfl⟩ : syracuseStep 1744259 = 2616389) B2616389
theorem B1744289 : Blo 1160639 1744289 := bstep (se 2 (by rfl) ⟨654108, by rfl⟩ : syracuseStep 1744289 = 1308217) B1308217
theorem B1744307 : Blo 1160639 1744307 := bstep (se 1 (by rfl) ⟨1308230, by rfl⟩ : syracuseStep 1744307 = 2616461) B2616461
theorem B1744337 : Blo 1160639 1744337 := bstep (se 2 (by rfl) ⟨654126, by rfl⟩ : syracuseStep 1744337 = 1308253) B1308253
theorem B1744355 : Blo 1160639 1744355 := bstep (se 1 (by rfl) ⟨1308266, by rfl⟩ : syracuseStep 1744355 = 2616533) B2616533
theorem B1744385 : Blo 1160639 1744385 := bstep (se 2 (by rfl) ⟨654144, by rfl⟩ : syracuseStep 1744385 = 1308289) B1308289
theorem B1744403 : Blo 1160639 1744403 := bstep (se 1 (by rfl) ⟨1308302, by rfl⟩ : syracuseStep 1744403 = 2616605) B2616605
theorem B1744433 : Blo 1160639 1744433 := bstep (se 2 (by rfl) ⟨654162, by rfl⟩ : syracuseStep 1744433 = 1308325) B1308325
theorem B1744451 : Blo 1160639 1744451 := bstep (se 1 (by rfl) ⟨1308338, by rfl⟩ : syracuseStep 1744451 = 2616677) B2616677
theorem B1744481 : Blo 1160639 1744481 := bstep (se 2 (by rfl) ⟨654180, by rfl⟩ : syracuseStep 1744481 = 1308361) B1308361
theorem B1744499 : Blo 1160639 1744499 := bstep (se 1 (by rfl) ⟨1308374, by rfl⟩ : syracuseStep 1744499 = 2616749) B2616749
theorem B1744529 : Blo 1160639 1744529 := bstep (se 2 (by rfl) ⟨654198, by rfl⟩ : syracuseStep 1744529 = 1308397) B1308397
theorem B1744547 : Blo 1160639 1744547 := bstep (se 1 (by rfl) ⟨1308410, by rfl⟩ : syracuseStep 1744547 = 2616821) B2616821
theorem B1744577 : Blo 1160639 1744577 := bstep (se 2 (by rfl) ⟨654216, by rfl⟩ : syracuseStep 1744577 = 1308433) B1308433
theorem B1744595 : Blo 1160639 1744595 := bstep (se 1 (by rfl) ⟨1308446, by rfl⟩ : syracuseStep 1744595 = 2616893) B2616893
theorem B1744625 : Blo 1160639 1744625 := bstep (se 2 (by rfl) ⟨654234, by rfl⟩ : syracuseStep 1744625 = 1308469) B1308469
theorem B1744643 : Blo 1160639 1744643 := bstep (se 1 (by rfl) ⟨1308482, by rfl⟩ : syracuseStep 1744643 = 2616965) B2616965
theorem B2236177 : Blo 1160639 2236177 := bstep (se 2 (by rfl) ⟨838566, by rfl⟩ : syracuseStep 2236177 = 1677133) B1677133
theorem B1744673 : Blo 1160639 1744673 := bstep (se 2 (by rfl) ⟨654252, by rfl⟩ : syracuseStep 1744673 = 1308505) B1308505
theorem B1744691 : Blo 1160639 1744691 := bstep (se 1 (by rfl) ⟨1308518, by rfl⟩ : syracuseStep 1744691 = 2617037) B2617037
theorem B1744721 : Blo 1160639 1744721 := bstep (se 2 (by rfl) ⟨654270, by rfl⟩ : syracuseStep 1744721 = 1308541) B1308541
theorem B1744739 : Blo 1160639 1744739 := bstep (se 1 (by rfl) ⟨1308554, by rfl⟩ : syracuseStep 1744739 = 2617109) B2617109
theorem B1744769 : Blo 1160639 1744769 := bstep (se 2 (by rfl) ⟨654288, by rfl⟩ : syracuseStep 1744769 = 1308577) B1308577
theorem B1744787 : Blo 1160639 1744787 := bstep (se 1 (by rfl) ⟨1308590, by rfl⟩ : syracuseStep 1744787 = 2617181) B2617181
theorem B1744817 : Blo 1160639 1744817 := bstep (se 2 (by rfl) ⟨654306, by rfl⟩ : syracuseStep 1744817 = 1308613) B1308613
theorem B1679297 : Blo 1160639 1679297 := bstep (se 2 (by rfl) ⟨629736, by rfl⟩ : syracuseStep 1679297 = 1259473) B1259473
theorem B1744835 : Blo 1160639 1744835 := bstep (se 1 (by rfl) ⟨1308626, by rfl⟩ : syracuseStep 1744835 = 2617253) B2617253
theorem B1744865 : Blo 1160639 1744865 := bstep (se 2 (by rfl) ⟨654324, by rfl⟩ : syracuseStep 1744865 = 1308649) B1308649
theorem B1744883 : Blo 1160639 1744883 := bstep (se 1 (by rfl) ⟨1308662, by rfl⟩ : syracuseStep 1744883 = 2617325) B2617325
theorem B1744913 : Blo 1160639 1744913 := bstep (se 2 (by rfl) ⟨654342, by rfl⟩ : syracuseStep 1744913 = 1308685) B1308685
theorem B5578787 : Blo 1160639 5578787 := bstep (se 1 (by rfl) ⟨4184090, by rfl⟩ : syracuseStep 5578787 = 8368181) B8368181
theorem B1744931 : Blo 1160639 1744931 := bstep (se 1 (by rfl) ⟨1308698, by rfl⟩ : syracuseStep 1744931 = 2617397) B2617397
theorem B1744961 : Blo 1160639 1744961 := bstep (se 2 (by rfl) ⟨654360, by rfl⟩ : syracuseStep 1744961 = 1308721) B1308721
theorem B1744979 : Blo 1160639 1744979 := bstep (se 1 (by rfl) ⟨1308734, by rfl⟩ : syracuseStep 1744979 = 2617469) B2617469
theorem B10592369 : Blo 1160639 10592369 := bstep (se 2 (by rfl) ⟨3972138, by rfl⟩ : syracuseStep 10592369 = 7944277) B7944277
theorem B1745009 : Blo 1160639 1745009 := bstep (se 2 (by rfl) ⟨654378, by rfl⟩ : syracuseStep 1745009 = 1308757) B1308757
theorem B1745027 : Blo 1160639 1745027 := bstep (se 1 (by rfl) ⟨1308770, by rfl⟩ : syracuseStep 1745027 = 2617541) B2617541
theorem B1745057 : Blo 1160639 1745057 := bstep (se 2 (by rfl) ⟨654396, by rfl⟩ : syracuseStep 1745057 = 1308793) B1308793
theorem B1745075 : Blo 1160639 1745075 := bstep (se 1 (by rfl) ⟨1308806, by rfl⟩ : syracuseStep 1745075 = 2617613) B2617613
theorem B2203843 : Blo 1160639 2203843 := bstep (se 1 (by rfl) ⟨1652882, by rfl⟩ : syracuseStep 2203843 = 3305765) B3305765
theorem B1745105 : Blo 1160639 1745105 := bstep (se 2 (by rfl) ⟨654414, by rfl⟩ : syracuseStep 1745105 = 1308829) B1308829
theorem B1745123 : Blo 1160639 1745123 := bstep (se 1 (by rfl) ⟨1308842, by rfl⟩ : syracuseStep 1745123 = 2617685) B2617685
theorem B1745153 : Blo 1160639 1745153 := bstep (se 2 (by rfl) ⟨654432, by rfl⟩ : syracuseStep 1745153 = 1308865) B1308865
theorem B1745171 : Blo 1160639 1745171 := bstep (se 1 (by rfl) ⟨1308878, by rfl⟩ : syracuseStep 1745171 = 2617757) B2617757
theorem B1745201 : Blo 1160639 1745201 := bstep (se 2 (by rfl) ⟨654450, by rfl⟩ : syracuseStep 1745201 = 1308901) B1308901
theorem B1745219 : Blo 1160639 1745219 := bstep (se 1 (by rfl) ⟨1308914, by rfl⟩ : syracuseStep 1745219 = 2617829) B2617829
theorem B1745249 : Blo 1160639 1745249 := bstep (se 2 (by rfl) ⟨654468, by rfl⟩ : syracuseStep 1745249 = 1308937) B1308937
theorem B2204003 : Blo 1160639 2204003 := bstep (se 1 (by rfl) ⟨1653002, by rfl⟩ : syracuseStep 2204003 = 3306005) B3306005
theorem B1745267 : Blo 1160639 1745267 := bstep (se 1 (by rfl) ⟨1308950, by rfl⟩ : syracuseStep 1745267 = 2617901) B2617901
theorem B7446917 : Blo 1160639 7446917 := bstep (se 4 (by rfl) ⟨698148, by rfl⟩ : syracuseStep 7446917 = 1396297) B1396297
theorem B8069509 : Blo 1160639 8069509 := bstep (se 4 (by rfl) ⟨756516, by rfl⟩ : syracuseStep 8069509 = 1513033) B1513033
theorem B1745297 : Blo 1160639 1745297 := bstep (se 2 (by rfl) ⟨654486, by rfl⟩ : syracuseStep 1745297 = 1308973) B1308973
theorem B1745315 : Blo 1160639 1745315 := bstep (se 1 (by rfl) ⟨1308986, by rfl⟩ : syracuseStep 1745315 = 2617973) B2617973
theorem B1745345 : Blo 1160639 1745345 := bstep (se 2 (by rfl) ⟨654504, by rfl⟩ : syracuseStep 1745345 = 1309009) B1309009
theorem B1745363 : Blo 1160639 1745363 := bstep (se 1 (by rfl) ⟨1309022, by rfl⟩ : syracuseStep 1745363 = 2618045) B2618045
theorem B1745393 : Blo 1160639 1745393 := bstep (se 2 (by rfl) ⟨654522, by rfl⟩ : syracuseStep 1745393 = 1309045) B1309045
theorem B1745411 : Blo 1160639 1745411 := bstep (se 1 (by rfl) ⟨1309058, by rfl⟩ : syracuseStep 1745411 = 2618117) B2618117
theorem B1745441 : Blo 1160639 1745441 := bstep (se 2 (by rfl) ⟨654540, by rfl⟩ : syracuseStep 1745441 = 1309081) B1309081
theorem B1745459 : Blo 1160639 1745459 := bstep (se 1 (by rfl) ⟨1309094, by rfl⟩ : syracuseStep 1745459 = 2618189) B2618189
theorem B1745489 : Blo 1160639 1745489 := bstep (se 2 (by rfl) ⟨654558, by rfl⟩ : syracuseStep 1745489 = 1309117) B1309117
theorem B1745507 : Blo 1160639 1745507 := bstep (se 1 (by rfl) ⟨1309130, by rfl⟩ : syracuseStep 1745507 = 2618261) B2618261
theorem B1745537 : Blo 1160639 1745537 := bstep (se 2 (by rfl) ⟨654576, by rfl⟩ : syracuseStep 1745537 = 1309153) B1309153
theorem B1745555 : Blo 1160639 1745555 := bstep (se 1 (by rfl) ⟨1309166, by rfl⟩ : syracuseStep 1745555 = 2618333) B2618333
theorem B5579441 : Blo 1160639 5579441 := bstep (se 2 (by rfl) ⟨2092290, by rfl⟩ : syracuseStep 5579441 = 4184581) B4184581
theorem B1745585 : Blo 1160639 1745585 := bstep (se 2 (by rfl) ⟨654594, by rfl⟩ : syracuseStep 1745585 = 1309189) B1309189
theorem B1745603 : Blo 1160639 1745603 := bstep (se 1 (by rfl) ⟨1309202, by rfl⟩ : syracuseStep 1745603 = 2618405) B2618405
theorem B1745633 : Blo 1160639 1745633 := bstep (se 2 (by rfl) ⟨654612, by rfl⟩ : syracuseStep 1745633 = 1309225) B1309225
theorem B1745651 : Blo 1160639 1745651 := bstep (se 1 (by rfl) ⟨1309238, by rfl⟩ : syracuseStep 1745651 = 2618477) B2618477
theorem B1745681 : Blo 1160639 1745681 := bstep (se 2 (by rfl) ⟨654630, by rfl⟩ : syracuseStep 1745681 = 1309261) B1309261
theorem B1745699 : Blo 1160639 1745699 := bstep (se 1 (by rfl) ⟨1309274, by rfl⟩ : syracuseStep 1745699 = 2618549) B2618549
theorem B1745729 : Blo 1160639 1745729 := bstep (se 2 (by rfl) ⟨654648, by rfl⟩ : syracuseStep 1745729 = 1309297) B1309297
theorem B1745747 : Blo 1160639 1745747 := bstep (se 1 (by rfl) ⟨1309310, by rfl⟩ : syracuseStep 1745747 = 2618621) B2618621
theorem B1745777 : Blo 1160639 1745777 := bstep (se 2 (by rfl) ⟨654666, by rfl⟩ : syracuseStep 1745777 = 1309333) B1309333
theorem B1745795 : Blo 1160639 1745795 := bstep (se 1 (by rfl) ⟨1309346, by rfl⟩ : syracuseStep 1745795 = 2618693) B2618693
theorem B6628229 : Blo 1160639 6628229 := bstep (se 4 (by rfl) ⟨621396, by rfl⟩ : syracuseStep 6628229 = 1242793) B1242793
theorem B1745825 : Blo 1160639 1745825 := bstep (se 2 (by rfl) ⟨654684, by rfl⟩ : syracuseStep 1745825 = 1309369) B1309369
theorem B1745843 : Blo 1160639 1745843 := bstep (se 1 (by rfl) ⟨1309382, by rfl⟩ : syracuseStep 1745843 = 2618765) B2618765
theorem B1745873 : Blo 1160639 1745873 := bstep (se 2 (by rfl) ⟨654702, by rfl⟩ : syracuseStep 1745873 = 1309405) B1309405
theorem B1745891 : Blo 1160639 1745891 := bstep (se 1 (by rfl) ⟨1309418, by rfl⟩ : syracuseStep 1745891 = 2618837) B2618837
theorem B1745921 : Blo 1160639 1745921 := bstep (se 2 (by rfl) ⟨654720, by rfl⟩ : syracuseStep 1745921 = 1309441) B1309441
theorem B1745939 : Blo 1160639 1745939 := bstep (se 1 (by rfl) ⟨1309454, by rfl⟩ : syracuseStep 1745939 = 2618909) B2618909
theorem B1745969 : Blo 1160639 1745969 := bstep (se 2 (by rfl) ⟨654738, by rfl⟩ : syracuseStep 1745969 = 1309477) B1309477
theorem B1745987 : Blo 1160639 1745987 := bstep (se 1 (by rfl) ⟨1309490, by rfl⟩ : syracuseStep 1745987 = 2618981) B2618981
theorem B1746017 : Blo 1160639 1746017 := bstep (se 2 (by rfl) ⟨654756, by rfl⟩ : syracuseStep 1746017 = 1309513) B1309513
theorem B1746035 : Blo 1160639 1746035 := bstep (se 1 (by rfl) ⟨1309526, by rfl⟩ : syracuseStep 1746035 = 2619053) B2619053
theorem B1746065 : Blo 1160639 1746065 := bstep (se 2 (by rfl) ⟨654774, by rfl⟩ : syracuseStep 1746065 = 1309549) B1309549
theorem B1746083 : Blo 1160639 1746083 := bstep (se 1 (by rfl) ⟨1309562, by rfl⟩ : syracuseStep 1746083 = 2619125) B2619125
theorem B1746113 : Blo 1160639 1746113 := bstep (se 2 (by rfl) ⟨654792, by rfl⟩ : syracuseStep 1746113 = 1309585) B1309585
theorem B14165189 : Blo 1160639 14165189 := bstep (se 4 (by rfl) ⟨1327986, by rfl⟩ : syracuseStep 14165189 = 2655973) B2655973
theorem B1746131 : Blo 1160639 1746131 := bstep (se 1 (by rfl) ⟨1309598, by rfl⟩ : syracuseStep 1746131 = 2619197) B2619197
theorem B1746161 : Blo 1160639 1746161 := bstep (se 2 (by rfl) ⟨654810, by rfl⟩ : syracuseStep 1746161 = 1309621) B1309621
theorem B1746179 : Blo 1160639 1746179 := bstep (se 1 (by rfl) ⟨1309634, by rfl⟩ : syracuseStep 1746179 = 2619269) B2619269
theorem B1746209 : Blo 1160639 1746209 := bstep (se 2 (by rfl) ⟨654828, by rfl⟩ : syracuseStep 1746209 = 1309657) B1309657
theorem B1746227 : Blo 1160639 1746227 := bstep (se 1 (by rfl) ⟨1309670, by rfl⟩ : syracuseStep 1746227 = 2619341) B2619341
theorem B1746257 : Blo 1160639 1746257 := bstep (se 2 (by rfl) ⟨654846, by rfl⟩ : syracuseStep 1746257 = 1309693) B1309693
theorem B1746275 : Blo 1160639 1746275 := bstep (se 1 (by rfl) ⟨1309706, by rfl⟩ : syracuseStep 1746275 = 2619413) B2619413
theorem B1746305 : Blo 1160639 1746305 := bstep (se 2 (by rfl) ⟨654864, by rfl⟩ : syracuseStep 1746305 = 1309729) B1309729
theorem B2205073 : Blo 1160639 2205073 := bstep (se 2 (by rfl) ⟨826902, by rfl⟩ : syracuseStep 2205073 = 1653805) B1653805
theorem B1746323 : Blo 1160639 1746323 := bstep (se 1 (by rfl) ⟨1309742, by rfl⟩ : syracuseStep 1746323 = 2619485) B2619485
theorem B1746353 : Blo 1160639 1746353 := bstep (se 2 (by rfl) ⟨654882, by rfl⟩ : syracuseStep 1746353 = 1309765) B1309765
theorem B1746371 : Blo 1160639 1746371 := bstep (se 1 (by rfl) ⟨1309778, by rfl⟩ : syracuseStep 1746371 = 2619557) B2619557
theorem B1746401 : Blo 1160639 1746401 := bstep (se 2 (by rfl) ⟨654900, by rfl⟩ : syracuseStep 1746401 = 1309801) B1309801
theorem B2794979 : Blo 1160639 2794979 := bstep (se 1 (by rfl) ⟨2096234, by rfl⟩ : syracuseStep 2794979 = 4192469) B4192469
theorem B1746419 : Blo 1160639 1746419 := bstep (se 1 (by rfl) ⟨1309814, by rfl⟩ : syracuseStep 1746419 = 2619629) B2619629
theorem B3581453 : Blo 1160639 3581453 := bstep (se 3 (by rfl) ⟨671522, by rfl⟩ : syracuseStep 3581453 = 1343045) B1343045
theorem B1746449 : Blo 1160639 1746449 := bstep (se 2 (by rfl) ⟨654918, by rfl⟩ : syracuseStep 1746449 = 1309837) B1309837
theorem B1746467 : Blo 1160639 1746467 := bstep (se 1 (by rfl) ⟨1309850, by rfl⟩ : syracuseStep 1746467 = 2619701) B2619701
theorem B48342581 : Blo 1160639 48342581 := bstep (se 5 (by rfl) ⟨2266058, by rfl⟩ : syracuseStep 48342581 = 4532117) B4532117
theorem B1746497 : Blo 1160639 1746497 := bstep (se 2 (by rfl) ⟨654936, by rfl⟩ : syracuseStep 1746497 = 1309873) B1309873
theorem B1746515 : Blo 1160639 1746515 := bstep (se 1 (by rfl) ⟨1309886, by rfl⟩ : syracuseStep 1746515 = 2619773) B2619773
theorem B1746545 : Blo 1160639 1746545 := bstep (se 2 (by rfl) ⟨654954, by rfl⟩ : syracuseStep 1746545 = 1309909) B1309909
theorem B1746563 : Blo 1160639 1746563 := bstep (se 1 (by rfl) ⟨1309922, by rfl⟩ : syracuseStep 1746563 = 2619845) B2619845
theorem B1746593 : Blo 1160639 1746593 := bstep (se 2 (by rfl) ⟨654972, by rfl⟩ : syracuseStep 1746593 = 1309945) B1309945
theorem B1746611 : Blo 1160639 1746611 := bstep (se 1 (by rfl) ⟨1309958, by rfl⟩ : syracuseStep 1746611 = 2619917) B2619917
theorem B1746641 : Blo 1160639 1746641 := bstep (se 2 (by rfl) ⟨654990, by rfl⟩ : syracuseStep 1746641 = 1309981) B1309981
theorem B1746659 : Blo 1160639 1746659 := bstep (se 1 (by rfl) ⟨1309994, by rfl⟩ : syracuseStep 1746659 = 2619989) B2619989
theorem B1746689 : Blo 1160639 1746689 := bstep (se 2 (by rfl) ⟨655008, by rfl⟩ : syracuseStep 1746689 = 1310017) B1310017
theorem B3581713 : Blo 1160639 3581713 := bstep (se 2 (by rfl) ⟨1343142, by rfl⟩ : syracuseStep 3581713 = 2686285) B2686285
theorem B1746707 : Blo 1160639 1746707 := bstep (se 1 (by rfl) ⟨1310030, by rfl⟩ : syracuseStep 1746707 = 2620061) B2620061
theorem B1746737 : Blo 1160639 1746737 := bstep (se 2 (by rfl) ⟨655026, by rfl⟩ : syracuseStep 1746737 = 1310053) B1310053
theorem B1746755 : Blo 1160639 1746755 := bstep (se 1 (by rfl) ⟨1310066, by rfl⟩ : syracuseStep 1746755 = 2620133) B2620133
theorem B1746785 : Blo 1160639 1746785 := bstep (se 2 (by rfl) ⟨655044, by rfl⟩ : syracuseStep 1746785 = 1310089) B1310089
theorem B2795363 : Blo 1160639 2795363 := bstep (se 1 (by rfl) ⟨2096522, by rfl⟩ : syracuseStep 2795363 = 4193045) B4193045
theorem B1746803 : Blo 1160639 1746803 := bstep (se 1 (by rfl) ⟨1310102, by rfl⟩ : syracuseStep 1746803 = 2620205) B2620205
theorem B3188621 : Blo 1160639 3188621 := bstep (se 3 (by rfl) ⟨597866, by rfl⟩ : syracuseStep 3188621 = 1195733) B1195733
theorem B1746833 : Blo 1160639 1746833 := bstep (se 2 (by rfl) ⟨655062, by rfl⟩ : syracuseStep 1746833 = 1310125) B1310125
theorem B1746851 : Blo 1160639 1746851 := bstep (se 1 (by rfl) ⟨1310138, by rfl⟩ : syracuseStep 1746851 = 2620277) B2620277
theorem B1746881 : Blo 1160639 1746881 := bstep (se 2 (by rfl) ⟨655080, by rfl⟩ : syracuseStep 1746881 = 1310161) B1310161
theorem B1746899 : Blo 1160639 1746899 := bstep (se 1 (by rfl) ⟨1310174, by rfl⟩ : syracuseStep 1746899 = 2620349) B2620349
theorem B3975149 : Blo 1160639 3975149 := bstep (se 3 (by rfl) ⟨745340, by rfl⟩ : syracuseStep 3975149 = 1490681) B1490681
theorem B1746929 : Blo 1160639 1746929 := bstep (se 2 (by rfl) ⟨655098, by rfl⟩ : syracuseStep 1746929 = 1310197) B1310197
theorem B1746947 : Blo 1160639 1746947 := bstep (se 1 (by rfl) ⟨1310210, by rfl⟩ : syracuseStep 1746947 = 2620421) B2620421
theorem B21473333 : Blo 1160639 21473333 := bstep (se 5 (by rfl) ⟨1006562, by rfl⟩ : syracuseStep 21473333 = 2013125) B2013125
theorem B3975299 : Blo 1160639 3975299 := bstep (se 1 (by rfl) ⟨2981474, by rfl⟩ : syracuseStep 3975299 = 5962949) B5962949
theorem B3975313 : Blo 1160639 3975313 := bstep (se 2 (by rfl) ⟨1490742, by rfl⟩ : syracuseStep 3975313 = 2981485) B2981485
theorem B5810381 : Blo 1160639 5810381 := bstep (se 3 (by rfl) ⟨1089446, by rfl⟩ : syracuseStep 5810381 = 2178893) B2178893
theorem B5581133 : Blo 1160639 5581133 := bstep (se 3 (by rfl) ⟨1046462, by rfl⟩ : syracuseStep 5581133 = 2092925) B2092925
theorem B2206129 : Blo 1160639 2206129 := bstep (se 2 (by rfl) ⟨827298, by rfl⟩ : syracuseStep 2206129 = 1654597) B1654597
theorem B5581361 : Blo 1160639 5581361 := bstep (se 2 (by rfl) ⟨2093010, by rfl⟩ : syracuseStep 5581361 = 4186021) B4186021
theorem B4958819 : Blo 1160639 4958819 := bstep (se 1 (by rfl) ⟨3719114, by rfl⟩ : syracuseStep 4958819 = 7438229) B7438229
theorem B5876387 : Blo 1160639 5876387 := bstep (se 1 (by rfl) ⟨4407290, by rfl⟩ : syracuseStep 5876387 = 8814581) B8814581
theorem B2206531 : Blo 1160639 2206531 := bstep (se 1 (by rfl) ⟨1654898, by rfl⟩ : syracuseStep 2206531 = 3309797) B3309797
theorem B2206577 : Blo 1160639 2206577 := bstep (se 2 (by rfl) ⟨827466, by rfl⟩ : syracuseStep 2206577 = 1654933) B1654933
theorem B12102797 : Blo 1160639 12102797 := bstep (se 3 (by rfl) ⟨2269274, by rfl⟩ : syracuseStep 12102797 = 4538549) B4538549
theorem B2206865 : Blo 1160639 2206865 := bstep (se 2 (by rfl) ⟨827574, by rfl⟩ : syracuseStep 2206865 = 1655149) B1655149
theorem B11644145 : Blo 1160639 11644145 := bstep (se 2 (by rfl) ⟨4366554, by rfl⟩ : syracuseStep 11644145 = 8733109) B8733109
theorem B3976625 : Blo 1160639 3976625 := bstep (se 2 (by rfl) ⟨1491234, by rfl⟩ : syracuseStep 3976625 = 2982469) B2982469
theorem B5877197 : Blo 1160639 5877197 := bstep (se 3 (by rfl) ⟨1101974, by rfl⟩ : syracuseStep 5877197 = 2203949) B2203949
theorem B9940805 : Blo 1160639 9940805 := bstep (se 4 (by rfl) ⟨931950, by rfl⟩ : syracuseStep 9940805 = 1863901) B1863901
theorem B2207587 : Blo 1160639 2207587 := bstep (se 1 (by rfl) ⟨1655690, by rfl⟩ : syracuseStep 2207587 = 3311381) B3311381
theorem B2208035 : Blo 1160639 2208035 := bstep (se 1 (by rfl) ⟨1656026, by rfl⟩ : syracuseStep 2208035 = 3312053) B3312053
theorem B4960561 : Blo 1160639 4960561 := bstep (se 2 (by rfl) ⟨1860210, by rfl⟩ : syracuseStep 4960561 = 3720421) B3720421
theorem B3780913 : Blo 1160639 3780913 := bstep (se 2 (by rfl) ⟨1417842, by rfl⟩ : syracuseStep 3780913 = 2835685) B2835685
theorem B2208323 : Blo 1160639 2208323 := bstep (se 1 (by rfl) ⟨1656242, by rfl⟩ : syracuseStep 2208323 = 3312485) B3312485
theorem B1815139 : Blo 1160639 1815139 := bstep (se 1 (by rfl) ⟨1361354, by rfl⟩ : syracuseStep 1815139 = 2722709) B2722709
theorem B6632077 : Blo 1160639 6632077 := bstep (se 3 (by rfl) ⟨1243514, by rfl⟩ : syracuseStep 6632077 = 2487029) B2487029
theorem B5583821 : Blo 1160639 5583821 := bstep (se 3 (by rfl) ⟨1046966, by rfl⟩ : syracuseStep 5583821 = 2093933) B2093933
theorem B1160643 : Blo 1160639 1160643 := bstep (se 1 (by rfl) ⟨870482, by rfl⟩ : syracuseStep 1160643 = 1740965) B1740965
theorem B1160659 : Blo 1160639 1160659 := bstep (se 1 (by rfl) ⟨870494, by rfl⟩ : syracuseStep 1160659 = 1740989) B1740989
theorem B1160675 : Blo 1160639 1160675 := bstep (se 1 (by rfl) ⟨870506, by rfl⟩ : syracuseStep 1160675 = 1741013) B1741013
theorem B2209265 : Blo 1160639 2209265 := bstep (se 2 (by rfl) ⟨828474, by rfl⟩ : syracuseStep 2209265 = 1656949) B1656949
theorem B1160691 : Blo 1160639 1160691 := bstep (se 1 (by rfl) ⟨870518, by rfl⟩ : syracuseStep 1160691 = 1741037) B1741037
theorem B1160707 : Blo 1160639 1160707 := bstep (se 1 (by rfl) ⟨870530, by rfl⟩ : syracuseStep 1160707 = 1741061) B1741061
theorem B1160723 : Blo 1160639 1160723 := bstep (se 1 (by rfl) ⟨870542, by rfl⟩ : syracuseStep 1160723 = 1741085) B1741085
theorem B1160739 : Blo 1160639 1160739 := bstep (se 1 (by rfl) ⟨870554, by rfl⟩ : syracuseStep 1160739 = 1741109) B1741109
theorem B1160755 : Blo 1160639 1160755 := bstep (se 1 (by rfl) ⟨870566, by rfl⟩ : syracuseStep 1160755 = 1741133) B1741133
theorem B1160771 : Blo 1160639 1160771 := bstep (se 1 (by rfl) ⟨870578, by rfl⟩ : syracuseStep 1160771 = 1741157) B1741157
theorem B1160787 : Blo 1160639 1160787 := bstep (se 1 (by rfl) ⟨870590, by rfl⟩ : syracuseStep 1160787 = 1741181) B1741181
theorem B1160803 : Blo 1160639 1160803 := bstep (se 1 (by rfl) ⟨870602, by rfl⟩ : syracuseStep 1160803 = 1741205) B1741205
theorem B1160819 : Blo 1160639 1160819 := bstep (se 1 (by rfl) ⟨870614, by rfl⟩ : syracuseStep 1160819 = 1741229) B1741229
theorem B1160835 : Blo 1160639 1160835 := bstep (se 1 (by rfl) ⟨870626, by rfl⟩ : syracuseStep 1160835 = 1741253) B1741253
theorem B1160851 : Blo 1160639 1160851 := bstep (se 1 (by rfl) ⟨870638, by rfl⟩ : syracuseStep 1160851 = 1741277) B1741277
theorem B1160867 : Blo 1160639 1160867 := bstep (se 1 (by rfl) ⟨870650, by rfl⟩ : syracuseStep 1160867 = 1741301) B1741301
theorem B1160883 : Blo 1160639 1160883 := bstep (se 1 (by rfl) ⟨870662, by rfl⟩ : syracuseStep 1160883 = 1741325) B1741325
theorem B1160899 : Blo 1160639 1160899 := bstep (se 1 (by rfl) ⟨870674, by rfl⟩ : syracuseStep 1160899 = 1741349) B1741349
theorem B1160915 : Blo 1160639 1160915 := bstep (se 1 (by rfl) ⟨870686, by rfl⟩ : syracuseStep 1160915 = 1741373) B1741373
theorem B1160931 : Blo 1160639 1160931 := bstep (se 1 (by rfl) ⟨870698, by rfl⟩ : syracuseStep 1160931 = 1741397) B1741397
theorem B1160947 : Blo 1160639 1160947 := bstep (se 1 (by rfl) ⟨870710, by rfl⟩ : syracuseStep 1160947 = 1741421) B1741421
theorem B1160963 : Blo 1160639 1160963 := bstep (se 1 (by rfl) ⟨870722, by rfl⟩ : syracuseStep 1160963 = 1741445) B1741445
theorem B1160979 : Blo 1160639 1160979 := bstep (se 1 (by rfl) ⟨870734, by rfl⟩ : syracuseStep 1160979 = 1741469) B1741469
theorem B1160995 : Blo 1160639 1160995 := bstep (se 1 (by rfl) ⟨870746, by rfl⟩ : syracuseStep 1160995 = 1741493) B1741493
theorem B1161011 : Blo 1160639 1161011 := bstep (se 1 (by rfl) ⟨870758, by rfl⟩ : syracuseStep 1161011 = 1741517) B1741517
theorem B1161027 : Blo 1160639 1161027 := bstep (se 1 (by rfl) ⟨870770, by rfl⟩ : syracuseStep 1161027 = 1741541) B1741541
theorem B1161043 : Blo 1160639 1161043 := bstep (se 1 (by rfl) ⟨870782, by rfl⟩ : syracuseStep 1161043 = 1741565) B1741565
theorem B1161059 : Blo 1160639 1161059 := bstep (se 1 (by rfl) ⟨870794, by rfl⟩ : syracuseStep 1161059 = 1741589) B1741589
theorem B1161075 : Blo 1160639 1161075 := bstep (se 1 (by rfl) ⟨870806, by rfl⟩ : syracuseStep 1161075 = 1741613) B1741613
theorem B1652609 : Blo 1160639 1652609 := bstep (se 2 (by rfl) ⟨619728, by rfl⟩ : syracuseStep 1652609 = 1239457) B1239457
theorem B1161091 : Blo 1160639 1161091 := bstep (se 1 (by rfl) ⟨870818, by rfl⟩ : syracuseStep 1161091 = 1741637) B1741637
theorem B1161107 : Blo 1160639 1161107 := bstep (se 1 (by rfl) ⟨870830, by rfl⟩ : syracuseStep 1161107 = 1741661) B1741661
theorem B1161123 : Blo 1160639 1161123 := bstep (se 1 (by rfl) ⟨870842, by rfl⟩ : syracuseStep 1161123 = 1741685) B1741685
theorem B1161139 : Blo 1160639 1161139 := bstep (se 1 (by rfl) ⟨870854, by rfl⟩ : syracuseStep 1161139 = 1741709) B1741709
theorem B1161155 : Blo 1160639 1161155 := bstep (se 1 (by rfl) ⟨870866, by rfl⟩ : syracuseStep 1161155 = 1741733) B1741733
theorem B5027789 : Blo 1160639 5027789 := bstep (se 3 (by rfl) ⟨942710, by rfl⟩ : syracuseStep 5027789 = 1885421) B1885421
theorem B1161171 : Blo 1160639 1161171 := bstep (se 1 (by rfl) ⟨870878, by rfl⟩ : syracuseStep 1161171 = 1741757) B1741757
theorem B1161187 : Blo 1160639 1161187 := bstep (se 1 (by rfl) ⟨870890, by rfl⟩ : syracuseStep 1161187 = 1741781) B1741781
theorem B1161203 : Blo 1160639 1161203 := bstep (se 1 (by rfl) ⟨870902, by rfl⟩ : syracuseStep 1161203 = 1741805) B1741805
theorem B1161219 : Blo 1160639 1161219 := bstep (se 1 (by rfl) ⟨870914, by rfl⟩ : syracuseStep 1161219 = 1741829) B1741829
theorem B1161235 : Blo 1160639 1161235 := bstep (se 1 (by rfl) ⟨870926, by rfl⟩ : syracuseStep 1161235 = 1741853) B1741853
theorem B1161251 : Blo 1160639 1161251 := bstep (se 1 (by rfl) ⟨870938, by rfl⟩ : syracuseStep 1161251 = 1741877) B1741877
theorem B1161267 : Blo 1160639 1161267 := bstep (se 1 (by rfl) ⟨870950, by rfl⟩ : syracuseStep 1161267 = 1741901) B1741901
theorem B1161283 : Blo 1160639 1161283 := bstep (se 1 (by rfl) ⟨870962, by rfl⟩ : syracuseStep 1161283 = 1741925) B1741925
theorem B1161299 : Blo 1160639 1161299 := bstep (se 1 (by rfl) ⟨870974, by rfl⟩ : syracuseStep 1161299 = 1741949) B1741949
theorem B1161315 : Blo 1160639 1161315 := bstep (se 1 (by rfl) ⟨870986, by rfl⟩ : syracuseStep 1161315 = 1741973) B1741973
theorem B3979363 : Blo 1160639 3979363 := bstep (se 1 (by rfl) ⟨2984522, by rfl⟩ : syracuseStep 3979363 = 5969045) B5969045
theorem B1161331 : Blo 1160639 1161331 := bstep (se 1 (by rfl) ⟨870998, by rfl⟩ : syracuseStep 1161331 = 1741997) B1741997
theorem B1161347 : Blo 1160639 1161347 := bstep (se 1 (by rfl) ⟨871010, by rfl⟩ : syracuseStep 1161347 = 1742021) B1742021
theorem B1161363 : Blo 1160639 1161363 := bstep (se 1 (by rfl) ⟨871022, by rfl⟩ : syracuseStep 1161363 = 1742045) B1742045
theorem B1161379 : Blo 1160639 1161379 := bstep (se 1 (by rfl) ⟨871034, by rfl⟩ : syracuseStep 1161379 = 1742069) B1742069
theorem B3356849 : Blo 1160639 3356849 := bstep (se 2 (by rfl) ⟨1258818, by rfl⟩ : syracuseStep 3356849 = 2517637) B2517637
theorem B1161395 : Blo 1160639 1161395 := bstep (se 1 (by rfl) ⟨871046, by rfl⟩ : syracuseStep 1161395 = 1742093) B1742093
theorem B1161411 : Blo 1160639 1161411 := bstep (se 1 (by rfl) ⟨871058, by rfl⟩ : syracuseStep 1161411 = 1742117) B1742117
theorem B4962509 : Blo 1160639 4962509 := bstep (se 3 (by rfl) ⟨930470, by rfl⟩ : syracuseStep 4962509 = 1860941) B1860941
theorem B1161427 : Blo 1160639 1161427 := bstep (se 1 (by rfl) ⟨871070, by rfl⟩ : syracuseStep 1161427 = 1742141) B1742141
theorem B1161443 : Blo 1160639 1161443 := bstep (se 1 (by rfl) ⟨871082, by rfl⟩ : syracuseStep 1161443 = 1742165) B1742165
theorem B1161459 : Blo 1160639 1161459 := bstep (se 1 (by rfl) ⟨871094, by rfl⟩ : syracuseStep 1161459 = 1742189) B1742189
theorem B1161475 : Blo 1160639 1161475 := bstep (se 1 (by rfl) ⟨871106, by rfl⟩ : syracuseStep 1161475 = 1742213) B1742213
theorem B1161491 : Blo 1160639 1161491 := bstep (se 1 (by rfl) ⟨871118, by rfl⟩ : syracuseStep 1161491 = 1742237) B1742237
theorem B1161507 : Blo 1160639 1161507 := bstep (se 1 (by rfl) ⟨871130, by rfl⟩ : syracuseStep 1161507 = 1742261) B1742261
theorem B5880113 : Blo 1160639 5880113 := bstep (se 2 (by rfl) ⟨2205042, by rfl⟩ : syracuseStep 5880113 = 4410085) B4410085
theorem B1161523 : Blo 1160639 1161523 := bstep (se 1 (by rfl) ⟨871142, by rfl⟩ : syracuseStep 1161523 = 1742285) B1742285
theorem B1161539 : Blo 1160639 1161539 := bstep (se 1 (by rfl) ⟨871154, by rfl⟩ : syracuseStep 1161539 = 1742309) B1742309
theorem B1161555 : Blo 1160639 1161555 := bstep (se 1 (by rfl) ⟨871166, by rfl⟩ : syracuseStep 1161555 = 1742333) B1742333
theorem B1161571 : Blo 1160639 1161571 := bstep (se 1 (by rfl) ⟨871178, by rfl⟩ : syracuseStep 1161571 = 1742357) B1742357
theorem B2210161 : Blo 1160639 2210161 := bstep (se 2 (by rfl) ⟨828810, by rfl⟩ : syracuseStep 2210161 = 1657621) B1657621
theorem B1161587 : Blo 1160639 1161587 := bstep (se 1 (by rfl) ⟨871190, by rfl⟩ : syracuseStep 1161587 = 1742381) B1742381
theorem B1161603 : Blo 1160639 1161603 := bstep (se 1 (by rfl) ⟨871202, by rfl⟩ : syracuseStep 1161603 = 1742405) B1742405
theorem B1653139 : Blo 1160639 1653139 := bstep (se 1 (by rfl) ⟨1239854, by rfl⟩ : syracuseStep 1653139 = 2479709) B2479709
theorem B1161619 : Blo 1160639 1161619 := bstep (se 1 (by rfl) ⟨871214, by rfl⟩ : syracuseStep 1161619 = 1742429) B1742429
theorem B1161635 : Blo 1160639 1161635 := bstep (se 1 (by rfl) ⟨871226, by rfl⟩ : syracuseStep 1161635 = 1742453) B1742453
theorem B1161651 : Blo 1160639 1161651 := bstep (se 1 (by rfl) ⟨871238, by rfl⟩ : syracuseStep 1161651 = 1742477) B1742477
theorem B1161667 : Blo 1160639 1161667 := bstep (se 1 (by rfl) ⟨871250, by rfl⟩ : syracuseStep 1161667 = 1742501) B1742501
theorem B1161683 : Blo 1160639 1161683 := bstep (se 1 (by rfl) ⟨871262, by rfl⟩ : syracuseStep 1161683 = 1742525) B1742525
theorem B1161699 : Blo 1160639 1161699 := bstep (se 1 (by rfl) ⟨871274, by rfl⟩ : syracuseStep 1161699 = 1742549) B1742549
theorem B1161715 : Blo 1160639 1161715 := bstep (se 1 (by rfl) ⟨871286, by rfl⟩ : syracuseStep 1161715 = 1742573) B1742573
theorem B1161731 : Blo 1160639 1161731 := bstep (se 1 (by rfl) ⟨871298, by rfl⟩ : syracuseStep 1161731 = 1742597) B1742597
theorem B2210321 : Blo 1160639 2210321 := bstep (se 2 (by rfl) ⟨828870, by rfl⟩ : syracuseStep 2210321 = 1657741) B1657741
theorem B1161747 : Blo 1160639 1161747 := bstep (se 1 (by rfl) ⟨871310, by rfl⟩ : syracuseStep 1161747 = 1742621) B1742621
theorem B1161763 : Blo 1160639 1161763 := bstep (se 1 (by rfl) ⟨871322, by rfl⟩ : syracuseStep 1161763 = 1742645) B1742645
theorem B1161779 : Blo 1160639 1161779 := bstep (se 1 (by rfl) ⟨871334, by rfl⟩ : syracuseStep 1161779 = 1742669) B1742669
theorem B1161795 : Blo 1160639 1161795 := bstep (se 1 (by rfl) ⟨871346, by rfl⟩ : syracuseStep 1161795 = 1742693) B1742693
theorem B1161811 : Blo 1160639 1161811 := bstep (se 1 (by rfl) ⟨871358, by rfl⟩ : syracuseStep 1161811 = 1742717) B1742717
theorem B1325651 : Blo 1160639 1325651 := bstep (se 1 (by rfl) ⟨994238, by rfl⟩ : syracuseStep 1325651 = 1988477) B1988477
theorem B1161827 : Blo 1160639 1161827 := bstep (se 1 (by rfl) ⟨871370, by rfl⟩ : syracuseStep 1161827 = 1742741) B1742741
theorem B13253219 : Blo 1160639 13253219 := bstep (se 1 (by rfl) ⟨9939914, by rfl⟩ : syracuseStep 13253219 = 19879829) B19879829
theorem B1161843 : Blo 1160639 1161843 := bstep (se 1 (by rfl) ⟨871382, by rfl⟩ : syracuseStep 1161843 = 1742765) B1742765
theorem B1161859 : Blo 1160639 1161859 := bstep (se 1 (by rfl) ⟨871394, by rfl⟩ : syracuseStep 1161859 = 1742789) B1742789
theorem B1161875 : Blo 1160639 1161875 := bstep (se 1 (by rfl) ⟨871406, by rfl⟩ : syracuseStep 1161875 = 1742813) B1742813
theorem B1161891 : Blo 1160639 1161891 := bstep (se 1 (by rfl) ⟨871418, by rfl⟩ : syracuseStep 1161891 = 1742837) B1742837
theorem B1161907 : Blo 1160639 1161907 := bstep (se 1 (by rfl) ⟨871430, by rfl⟩ : syracuseStep 1161907 = 1742861) B1742861
theorem B1161923 : Blo 1160639 1161923 := bstep (se 1 (by rfl) ⟨871442, by rfl⟩ : syracuseStep 1161923 = 1742885) B1742885
theorem B1161939 : Blo 1160639 1161939 := bstep (se 1 (by rfl) ⟨871454, by rfl⟩ : syracuseStep 1161939 = 1742909) B1742909
theorem B1653475 : Blo 1160639 1653475 := bstep (se 1 (by rfl) ⟨1240106, by rfl⟩ : syracuseStep 1653475 = 2480213) B2480213
theorem B4471523 : Blo 1160639 4471523 := bstep (se 1 (by rfl) ⟨3353642, by rfl⟩ : syracuseStep 4471523 = 6707285) B6707285
theorem B1161955 : Blo 1160639 1161955 := bstep (se 1 (by rfl) ⟨871466, by rfl⟩ : syracuseStep 1161955 = 1742933) B1742933
theorem B1161971 : Blo 1160639 1161971 := bstep (se 1 (by rfl) ⟨871478, by rfl⟩ : syracuseStep 1161971 = 1742957) B1742957
theorem B1161987 : Blo 1160639 1161987 := bstep (se 1 (by rfl) ⟨871490, by rfl⟩ : syracuseStep 1161987 = 1742981) B1742981
theorem B1162003 : Blo 1160639 1162003 := bstep (se 1 (by rfl) ⟨871502, by rfl⟩ : syracuseStep 1162003 = 1743005) B1743005
theorem B1162019 : Blo 1160639 1162019 := bstep (se 1 (by rfl) ⟨871514, by rfl⟩ : syracuseStep 1162019 = 1743029) B1743029
theorem B1162035 : Blo 1160639 1162035 := bstep (se 1 (by rfl) ⟨871526, by rfl⟩ : syracuseStep 1162035 = 1743053) B1743053
theorem B1162051 : Blo 1160639 1162051 := bstep (se 1 (by rfl) ⟨871538, by rfl⟩ : syracuseStep 1162051 = 1743077) B1743077
theorem B1162067 : Blo 1160639 1162067 := bstep (se 1 (by rfl) ⟨871550, by rfl⟩ : syracuseStep 1162067 = 1743101) B1743101
theorem B1162083 : Blo 1160639 1162083 := bstep (se 1 (by rfl) ⟨871562, by rfl⟩ : syracuseStep 1162083 = 1743125) B1743125
theorem B1162099 : Blo 1160639 1162099 := bstep (se 1 (by rfl) ⟨871574, by rfl⟩ : syracuseStep 1162099 = 1743149) B1743149
theorem B1162115 : Blo 1160639 1162115 := bstep (se 1 (by rfl) ⟨871586, by rfl⟩ : syracuseStep 1162115 = 1743173) B1743173
theorem B1162131 : Blo 1160639 1162131 := bstep (se 1 (by rfl) ⟨871598, by rfl⟩ : syracuseStep 1162131 = 1743197) B1743197
theorem B1162147 : Blo 1160639 1162147 := bstep (se 1 (by rfl) ⟨871610, by rfl⟩ : syracuseStep 1162147 = 1743221) B1743221
theorem B2210723 : Blo 1160639 2210723 := bstep (se 1 (by rfl) ⟨1658042, by rfl⟩ : syracuseStep 2210723 = 3316085) B3316085
theorem B1162163 : Blo 1160639 1162163 := bstep (se 1 (by rfl) ⟨871622, by rfl⟩ : syracuseStep 1162163 = 1743245) B1743245
theorem B1162179 : Blo 1160639 1162179 := bstep (se 1 (by rfl) ⟨871634, by rfl⟩ : syracuseStep 1162179 = 1743269) B1743269
theorem B1162195 : Blo 1160639 1162195 := bstep (se 1 (by rfl) ⟨871646, by rfl⟩ : syracuseStep 1162195 = 1743293) B1743293
theorem B1162211 : Blo 1160639 1162211 := bstep (se 1 (by rfl) ⟨871658, by rfl⟩ : syracuseStep 1162211 = 1743317) B1743317
theorem B1162227 : Blo 1160639 1162227 := bstep (se 1 (by rfl) ⟨871670, by rfl⟩ : syracuseStep 1162227 = 1743341) B1743341
theorem B1162243 : Blo 1160639 1162243 := bstep (se 1 (by rfl) ⟨871682, by rfl⟩ : syracuseStep 1162243 = 1743365) B1743365
theorem B1162259 : Blo 1160639 1162259 := bstep (se 1 (by rfl) ⟨871694, by rfl⟩ : syracuseStep 1162259 = 1743389) B1743389
theorem B1162275 : Blo 1160639 1162275 := bstep (se 1 (by rfl) ⟨871706, by rfl⟩ : syracuseStep 1162275 = 1743413) B1743413
theorem B1162291 : Blo 1160639 1162291 := bstep (se 1 (by rfl) ⟨871718, by rfl⟩ : syracuseStep 1162291 = 1743437) B1743437
theorem B1162307 : Blo 1160639 1162307 := bstep (se 1 (by rfl) ⟨871730, by rfl⟩ : syracuseStep 1162307 = 1743461) B1743461
theorem B1162323 : Blo 1160639 1162323 := bstep (se 1 (by rfl) ⟨871742, by rfl⟩ : syracuseStep 1162323 = 1743485) B1743485
theorem B1162339 : Blo 1160639 1162339 := bstep (se 1 (by rfl) ⟨871754, by rfl⟩ : syracuseStep 1162339 = 1743509) B1743509
theorem B1162355 : Blo 1160639 1162355 := bstep (se 1 (by rfl) ⟨871766, by rfl⟩ : syracuseStep 1162355 = 1743533) B1743533
theorem B1162371 : Blo 1160639 1162371 := bstep (se 1 (by rfl) ⟨871778, by rfl⟩ : syracuseStep 1162371 = 1743557) B1743557
theorem B1162387 : Blo 1160639 1162387 := bstep (se 1 (by rfl) ⟨871790, by rfl⟩ : syracuseStep 1162387 = 1743581) B1743581
theorem B1162403 : Blo 1160639 1162403 := bstep (se 1 (by rfl) ⟨871802, by rfl⟩ : syracuseStep 1162403 = 1743605) B1743605
theorem B1162419 : Blo 1160639 1162419 := bstep (se 1 (by rfl) ⟨871814, by rfl⟩ : syracuseStep 1162419 = 1743629) B1743629
theorem B1162435 : Blo 1160639 1162435 := bstep (se 1 (by rfl) ⟨871826, by rfl⟩ : syracuseStep 1162435 = 1743653) B1743653
theorem B1162451 : Blo 1160639 1162451 := bstep (se 1 (by rfl) ⟨871838, by rfl⟩ : syracuseStep 1162451 = 1743677) B1743677
theorem B1162467 : Blo 1160639 1162467 := bstep (se 1 (by rfl) ⟨871850, by rfl⟩ : syracuseStep 1162467 = 1743701) B1743701
theorem B1162483 : Blo 1160639 1162483 := bstep (se 1 (by rfl) ⟨871862, by rfl⟩ : syracuseStep 1162483 = 1743725) B1743725
theorem B1490179 : Blo 1160639 1490179 := bstep (se 1 (by rfl) ⟨1117634, by rfl⟩ : syracuseStep 1490179 = 2235269) B2235269
theorem B1162499 : Blo 1160639 1162499 := bstep (se 1 (by rfl) ⟨871874, by rfl⟩ : syracuseStep 1162499 = 1743749) B1743749
theorem B1654033 : Blo 1160639 1654033 := bstep (se 2 (by rfl) ⟨620262, by rfl⟩ : syracuseStep 1654033 = 1240525) B1240525
theorem B1162515 : Blo 1160639 1162515 := bstep (se 1 (by rfl) ⟨871886, by rfl⟩ : syracuseStep 1162515 = 1743773) B1743773
theorem B1162531 : Blo 1160639 1162531 := bstep (se 1 (by rfl) ⟨871898, by rfl⟩ : syracuseStep 1162531 = 1743797) B1743797
theorem B1654067 : Blo 1160639 1654067 := bstep (se 1 (by rfl) ⟨1240550, by rfl⟩ : syracuseStep 1654067 = 2481101) B2481101
theorem B1162547 : Blo 1160639 1162547 := bstep (se 1 (by rfl) ⟨871910, by rfl⟩ : syracuseStep 1162547 = 1743821) B1743821
theorem B1162563 : Blo 1160639 1162563 := bstep (se 1 (by rfl) ⟨871922, by rfl⟩ : syracuseStep 1162563 = 1743845) B1743845
theorem B1162579 : Blo 1160639 1162579 := bstep (se 1 (by rfl) ⟨871934, by rfl⟩ : syracuseStep 1162579 = 1743869) B1743869
theorem B1162595 : Blo 1160639 1162595 := bstep (se 1 (by rfl) ⟨871946, by rfl⟩ : syracuseStep 1162595 = 1743893) B1743893
theorem B1162611 : Blo 1160639 1162611 := bstep (se 1 (by rfl) ⟨871958, by rfl⟩ : syracuseStep 1162611 = 1743917) B1743917
theorem B1162627 : Blo 1160639 1162627 := bstep (se 1 (by rfl) ⟨871970, by rfl⟩ : syracuseStep 1162627 = 1743941) B1743941
theorem B1162643 : Blo 1160639 1162643 := bstep (se 1 (by rfl) ⟨871982, by rfl⟩ : syracuseStep 1162643 = 1743965) B1743965
theorem B1162659 : Blo 1160639 1162659 := bstep (se 1 (by rfl) ⟨871994, by rfl⟩ : syracuseStep 1162659 = 1743989) B1743989
theorem B1162675 : Blo 1160639 1162675 := bstep (se 1 (by rfl) ⟨872006, by rfl⟩ : syracuseStep 1162675 = 1744013) B1744013
theorem B1162691 : Blo 1160639 1162691 := bstep (se 1 (by rfl) ⟨872018, by rfl⟩ : syracuseStep 1162691 = 1744037) B1744037
theorem B1162707 : Blo 1160639 1162707 := bstep (se 1 (by rfl) ⟨872030, by rfl⟩ : syracuseStep 1162707 = 1744061) B1744061
theorem B1162723 : Blo 1160639 1162723 := bstep (se 1 (by rfl) ⟨872042, by rfl⟩ : syracuseStep 1162723 = 1744085) B1744085
theorem B1162739 : Blo 1160639 1162739 := bstep (se 1 (by rfl) ⟨872054, by rfl⟩ : syracuseStep 1162739 = 1744109) B1744109
theorem B1162755 : Blo 1160639 1162755 := bstep (se 1 (by rfl) ⟨872066, by rfl⟩ : syracuseStep 1162755 = 1744133) B1744133
theorem B1162771 : Blo 1160639 1162771 := bstep (se 1 (by rfl) ⟨872078, by rfl⟩ : syracuseStep 1162771 = 1744157) B1744157
theorem B1162787 : Blo 1160639 1162787 := bstep (se 1 (by rfl) ⟨872090, by rfl⟩ : syracuseStep 1162787 = 1744181) B1744181
theorem B1162803 : Blo 1160639 1162803 := bstep (se 1 (by rfl) ⟨872102, by rfl⟩ : syracuseStep 1162803 = 1744205) B1744205
theorem B1162819 : Blo 1160639 1162819 := bstep (se 1 (by rfl) ⟨872114, by rfl⟩ : syracuseStep 1162819 = 1744229) B1744229
theorem B1162835 : Blo 1160639 1162835 := bstep (se 1 (by rfl) ⟨872126, by rfl⟩ : syracuseStep 1162835 = 1744253) B1744253
theorem B1162851 : Blo 1160639 1162851 := bstep (se 1 (by rfl) ⟨872138, by rfl⟩ : syracuseStep 1162851 = 1744277) B1744277
theorem B1162867 : Blo 1160639 1162867 := bstep (se 1 (by rfl) ⟨872150, by rfl⟩ : syracuseStep 1162867 = 1744301) B1744301
theorem B1162883 : Blo 1160639 1162883 := bstep (se 1 (by rfl) ⟨872162, by rfl⟩ : syracuseStep 1162883 = 1744325) B1744325
theorem B1162899 : Blo 1160639 1162899 := bstep (se 1 (by rfl) ⟨872174, by rfl⟩ : syracuseStep 1162899 = 1744349) B1744349
theorem B1162915 : Blo 1160639 1162915 := bstep (se 1 (by rfl) ⟨872186, by rfl⟩ : syracuseStep 1162915 = 1744373) B1744373
theorem B1162931 : Blo 1160639 1162931 := bstep (se 1 (by rfl) ⟨872198, by rfl⟩ : syracuseStep 1162931 = 1744397) B1744397
theorem B1162947 : Blo 1160639 1162947 := bstep (se 1 (by rfl) ⟨872210, by rfl⟩ : syracuseStep 1162947 = 1744421) B1744421
theorem B1162963 : Blo 1160639 1162963 := bstep (se 1 (by rfl) ⟨872222, by rfl⟩ : syracuseStep 1162963 = 1744445) B1744445
theorem B5881571 : Blo 1160639 5881571 := bstep (se 1 (by rfl) ⟨4411178, by rfl⟩ : syracuseStep 5881571 = 8822357) B8822357
theorem B1162979 : Blo 1160639 1162979 := bstep (se 1 (by rfl) ⟨872234, by rfl⟩ : syracuseStep 1162979 = 1744469) B1744469
theorem B1162995 : Blo 1160639 1162995 := bstep (se 1 (by rfl) ⟨872246, by rfl⟩ : syracuseStep 1162995 = 1744493) B1744493
theorem B1163011 : Blo 1160639 1163011 := bstep (se 1 (by rfl) ⟨872258, by rfl⟩ : syracuseStep 1163011 = 1744517) B1744517
theorem B1163027 : Blo 1160639 1163027 := bstep (se 1 (by rfl) ⟨872270, by rfl⟩ : syracuseStep 1163027 = 1744541) B1744541
theorem B1163043 : Blo 1160639 1163043 := bstep (se 1 (by rfl) ⟨872282, by rfl⟩ : syracuseStep 1163043 = 1744565) B1744565
theorem B1163059 : Blo 1160639 1163059 := bstep (se 1 (by rfl) ⟨872294, by rfl⟩ : syracuseStep 1163059 = 1744589) B1744589
theorem B1163075 : Blo 1160639 1163075 := bstep (se 1 (by rfl) ⟨872306, by rfl⟩ : syracuseStep 1163075 = 1744613) B1744613
theorem B1163091 : Blo 1160639 1163091 := bstep (se 1 (by rfl) ⟨872318, by rfl⟩ : syracuseStep 1163091 = 1744637) B1744637
theorem B1654625 : Blo 1160639 1654625 := bstep (se 2 (by rfl) ⟨620484, by rfl⟩ : syracuseStep 1654625 = 1240969) B1240969
theorem B1163107 : Blo 1160639 1163107 := bstep (se 1 (by rfl) ⟨872330, by rfl⟩ : syracuseStep 1163107 = 1744661) B1744661
theorem B1163123 : Blo 1160639 1163123 := bstep (se 1 (by rfl) ⟨872342, by rfl⟩ : syracuseStep 1163123 = 1744685) B1744685
theorem B1163139 : Blo 1160639 1163139 := bstep (se 1 (by rfl) ⟨872354, by rfl⟩ : syracuseStep 1163139 = 1744709) B1744709
theorem B1163155 : Blo 1160639 1163155 := bstep (se 1 (by rfl) ⟨872366, by rfl⟩ : syracuseStep 1163155 = 1744733) B1744733
theorem B1163171 : Blo 1160639 1163171 := bstep (se 1 (by rfl) ⟨872378, by rfl⟩ : syracuseStep 1163171 = 1744757) B1744757
theorem B1654705 : Blo 1160639 1654705 := bstep (se 2 (by rfl) ⟨620514, by rfl⟩ : syracuseStep 1654705 = 1241029) B1241029
theorem B1163187 : Blo 1160639 1163187 := bstep (se 1 (by rfl) ⟨872390, by rfl⟩ : syracuseStep 1163187 = 1744781) B1744781
theorem B1163203 : Blo 1160639 1163203 := bstep (se 1 (by rfl) ⟨872402, by rfl⟩ : syracuseStep 1163203 = 1744805) B1744805
theorem B1163219 : Blo 1160639 1163219 := bstep (se 1 (by rfl) ⟨872414, by rfl⟩ : syracuseStep 1163219 = 1744829) B1744829
theorem B1163235 : Blo 1160639 1163235 := bstep (se 1 (by rfl) ⟨872426, by rfl⟩ : syracuseStep 1163235 = 1744853) B1744853
theorem B1163251 : Blo 1160639 1163251 := bstep (se 1 (by rfl) ⟨872438, by rfl⟩ : syracuseStep 1163251 = 1744877) B1744877
theorem B1163267 : Blo 1160639 1163267 := bstep (se 1 (by rfl) ⟨872450, by rfl⟩ : syracuseStep 1163267 = 1744901) B1744901
theorem B1163283 : Blo 1160639 1163283 := bstep (se 1 (by rfl) ⟨872462, by rfl⟩ : syracuseStep 1163283 = 1744925) B1744925
theorem B1163299 : Blo 1160639 1163299 := bstep (se 1 (by rfl) ⟨872474, by rfl⟩ : syracuseStep 1163299 = 1744949) B1744949
theorem B1163315 : Blo 1160639 1163315 := bstep (se 1 (by rfl) ⟨872486, by rfl⟩ : syracuseStep 1163315 = 1744973) B1744973
theorem B1163331 : Blo 1160639 1163331 := bstep (se 1 (by rfl) ⟨872498, by rfl⟩ : syracuseStep 1163331 = 1744997) B1744997
theorem B6275141 : Blo 1160639 6275141 := bstep (se 4 (by rfl) ⟨588294, by rfl⟩ : syracuseStep 6275141 = 1176589) B1176589
theorem B1163347 : Blo 1160639 1163347 := bstep (se 1 (by rfl) ⟨872510, by rfl⟩ : syracuseStep 1163347 = 1745021) B1745021
theorem B1163363 : Blo 1160639 1163363 := bstep (se 1 (by rfl) ⟨872522, by rfl⟩ : syracuseStep 1163363 = 1745045) B1745045
theorem B1163379 : Blo 1160639 1163379 := bstep (se 1 (by rfl) ⟨872534, by rfl⟩ : syracuseStep 1163379 = 1745069) B1745069
theorem B1163395 : Blo 1160639 1163395 := bstep (se 1 (by rfl) ⟨872546, by rfl⟩ : syracuseStep 1163395 = 1745093) B1745093
theorem B1163411 : Blo 1160639 1163411 := bstep (se 1 (by rfl) ⟨872558, by rfl⟩ : syracuseStep 1163411 = 1745117) B1745117
theorem B1163427 : Blo 1160639 1163427 := bstep (se 1 (by rfl) ⟨872570, by rfl⟩ : syracuseStep 1163427 = 1745141) B1745141
theorem B4407473 : Blo 1160639 4407473 := bstep (se 2 (by rfl) ⟨1652802, by rfl⟩ : syracuseStep 4407473 = 3305605) B3305605
theorem B1163443 : Blo 1160639 1163443 := bstep (se 1 (by rfl) ⟨872582, by rfl⟩ : syracuseStep 1163443 = 1745165) B1745165
theorem B1163459 : Blo 1160639 1163459 := bstep (se 1 (by rfl) ⟨872594, by rfl⟩ : syracuseStep 1163459 = 1745189) B1745189
theorem B1163475 : Blo 1160639 1163475 := bstep (se 1 (by rfl) ⟨872606, by rfl⟩ : syracuseStep 1163475 = 1745213) B1745213
theorem B1163491 : Blo 1160639 1163491 := bstep (se 1 (by rfl) ⟨872618, by rfl⟩ : syracuseStep 1163491 = 1745237) B1745237
theorem B1163507 : Blo 1160639 1163507 := bstep (se 1 (by rfl) ⟨872630, by rfl⟩ : syracuseStep 1163507 = 1745261) B1745261
theorem B1163523 : Blo 1160639 1163523 := bstep (se 1 (by rfl) ⟨872642, by rfl⟩ : syracuseStep 1163523 = 1745285) B1745285
theorem B1163539 : Blo 1160639 1163539 := bstep (se 1 (by rfl) ⟨872654, by rfl⟩ : syracuseStep 1163539 = 1745309) B1745309
theorem B1163555 : Blo 1160639 1163555 := bstep (se 1 (by rfl) ⟨872666, by rfl⟩ : syracuseStep 1163555 = 1745333) B1745333
theorem B1163571 : Blo 1160639 1163571 := bstep (se 1 (by rfl) ⟨872678, by rfl⟩ : syracuseStep 1163571 = 1745357) B1745357
theorem B1163587 : Blo 1160639 1163587 := bstep (se 1 (by rfl) ⟨872690, by rfl⟩ : syracuseStep 1163587 = 1745381) B1745381
theorem B1163603 : Blo 1160639 1163603 := bstep (se 1 (by rfl) ⟨872702, by rfl⟩ : syracuseStep 1163603 = 1745405) B1745405
theorem B1163619 : Blo 1160639 1163619 := bstep (se 1 (by rfl) ⟨872714, by rfl⟩ : syracuseStep 1163619 = 1745429) B1745429
theorem B1163635 : Blo 1160639 1163635 := bstep (se 1 (by rfl) ⟨872726, by rfl⟩ : syracuseStep 1163635 = 1745453) B1745453
theorem B1163651 : Blo 1160639 1163651 := bstep (se 1 (by rfl) ⟨872738, by rfl⟩ : syracuseStep 1163651 = 1745477) B1745477
theorem B1163667 : Blo 1160639 1163667 := bstep (se 1 (by rfl) ⟨872750, by rfl⟩ : syracuseStep 1163667 = 1745501) B1745501
theorem B1163683 : Blo 1160639 1163683 := bstep (se 1 (by rfl) ⟨872762, by rfl⟩ : syracuseStep 1163683 = 1745525) B1745525
theorem B1163699 : Blo 1160639 1163699 := bstep (se 1 (by rfl) ⟨872774, by rfl⟩ : syracuseStep 1163699 = 1745549) B1745549
theorem B1163715 : Blo 1160639 1163715 := bstep (se 1 (by rfl) ⟨872786, by rfl⟩ : syracuseStep 1163715 = 1745573) B1745573
theorem B1163731 : Blo 1160639 1163731 := bstep (se 1 (by rfl) ⟨872798, by rfl⟩ : syracuseStep 1163731 = 1745597) B1745597
theorem B1163747 : Blo 1160639 1163747 := bstep (se 1 (by rfl) ⟨872810, by rfl⟩ : syracuseStep 1163747 = 1745621) B1745621
theorem B1163763 : Blo 1160639 1163763 := bstep (se 1 (by rfl) ⟨872822, by rfl⟩ : syracuseStep 1163763 = 1745645) B1745645
theorem B1163779 : Blo 1160639 1163779 := bstep (se 1 (by rfl) ⟨872834, by rfl⟩ : syracuseStep 1163779 = 1745669) B1745669
theorem B5882381 : Blo 1160639 5882381 := bstep (se 3 (by rfl) ⟨1102946, by rfl⟩ : syracuseStep 5882381 = 2205893) B2205893
theorem B1163795 : Blo 1160639 1163795 := bstep (se 1 (by rfl) ⟨872846, by rfl⟩ : syracuseStep 1163795 = 1745693) B1745693
theorem B1163811 : Blo 1160639 1163811 := bstep (se 1 (by rfl) ⟨872858, by rfl⟩ : syracuseStep 1163811 = 1745717) B1745717
theorem B3981869 : Blo 1160639 3981869 := bstep (se 3 (by rfl) ⟨746600, by rfl⟩ : syracuseStep 3981869 = 1493201) B1493201
theorem B1163827 : Blo 1160639 1163827 := bstep (se 1 (by rfl) ⟨872870, by rfl⟩ : syracuseStep 1163827 = 1745741) B1745741
theorem B84754997 : Blo 1160639 84754997 := bstep (se 5 (by rfl) ⟨3972890, by rfl⟩ : syracuseStep 84754997 = 7945781) B7945781
theorem B1163843 : Blo 1160639 1163843 := bstep (se 1 (by rfl) ⟨872882, by rfl⟩ : syracuseStep 1163843 = 1745765) B1745765
theorem B1163859 : Blo 1160639 1163859 := bstep (se 1 (by rfl) ⟨872894, by rfl⟩ : syracuseStep 1163859 = 1745789) B1745789
theorem B1163875 : Blo 1160639 1163875 := bstep (se 1 (by rfl) ⟨872906, by rfl⟩ : syracuseStep 1163875 = 1745813) B1745813
theorem B1163891 : Blo 1160639 1163891 := bstep (se 1 (by rfl) ⟨872918, by rfl⟩ : syracuseStep 1163891 = 1745837) B1745837
theorem B1163907 : Blo 1160639 1163907 := bstep (se 1 (by rfl) ⟨872930, by rfl⟩ : syracuseStep 1163907 = 1745861) B1745861
theorem B1163923 : Blo 1160639 1163923 := bstep (se 1 (by rfl) ⟨872942, by rfl⟩ : syracuseStep 1163923 = 1745885) B1745885
theorem B1163939 : Blo 1160639 1163939 := bstep (se 1 (by rfl) ⟨872954, by rfl⟩ : syracuseStep 1163939 = 1745909) B1745909
theorem B4473521 : Blo 1160639 4473521 := bstep (se 2 (by rfl) ⟨1677570, by rfl⟩ : syracuseStep 4473521 = 3355141) B3355141
theorem B1163955 : Blo 1160639 1163955 := bstep (se 1 (by rfl) ⟨872966, by rfl⟩ : syracuseStep 1163955 = 1745933) B1745933
theorem B1655491 : Blo 1160639 1655491 := bstep (se 1 (by rfl) ⟨1241618, by rfl⟩ : syracuseStep 1655491 = 2483237) B2483237
theorem B1163971 : Blo 1160639 1163971 := bstep (se 1 (by rfl) ⟨872978, by rfl⟩ : syracuseStep 1163971 = 1745957) B1745957
theorem B1163987 : Blo 1160639 1163987 := bstep (se 1 (by rfl) ⟨872990, by rfl⟩ : syracuseStep 1163987 = 1745981) B1745981
theorem B1164003 : Blo 1160639 1164003 := bstep (se 1 (by rfl) ⟨873002, by rfl⟩ : syracuseStep 1164003 = 1746005) B1746005
theorem B1164019 : Blo 1160639 1164019 := bstep (se 1 (by rfl) ⟨873014, by rfl⟩ : syracuseStep 1164019 = 1746029) B1746029
theorem B1164035 : Blo 1160639 1164035 := bstep (se 1 (by rfl) ⟨873026, by rfl⟩ : syracuseStep 1164035 = 1746053) B1746053
theorem B1164051 : Blo 1160639 1164051 := bstep (se 1 (by rfl) ⟨873038, by rfl⟩ : syracuseStep 1164051 = 1746077) B1746077
theorem B1164067 : Blo 1160639 1164067 := bstep (se 1 (by rfl) ⟨873050, by rfl⟩ : syracuseStep 1164067 = 1746101) B1746101
theorem B1164083 : Blo 1160639 1164083 := bstep (se 1 (by rfl) ⟨873062, by rfl⟩ : syracuseStep 1164083 = 1746125) B1746125
theorem B1164099 : Blo 1160639 1164099 := bstep (se 1 (by rfl) ⟨873074, by rfl⟩ : syracuseStep 1164099 = 1746149) B1746149
theorem B4408141 : Blo 1160639 4408141 := bstep (se 3 (by rfl) ⟨826526, by rfl⟩ : syracuseStep 4408141 = 1653053) B1653053
theorem B1164115 : Blo 1160639 1164115 := bstep (se 1 (by rfl) ⟨873086, by rfl⟩ : syracuseStep 1164115 = 1746173) B1746173
theorem B1164131 : Blo 1160639 1164131 := bstep (se 1 (by rfl) ⟨873098, by rfl⟩ : syracuseStep 1164131 = 1746197) B1746197
theorem B1164147 : Blo 1160639 1164147 := bstep (se 1 (by rfl) ⟨873110, by rfl⟩ : syracuseStep 1164147 = 1746221) B1746221
theorem B1164163 : Blo 1160639 1164163 := bstep (se 1 (by rfl) ⟨873122, by rfl⟩ : syracuseStep 1164163 = 1746245) B1746245
theorem B3720077 : Blo 1160639 3720077 := bstep (se 3 (by rfl) ⟨697514, by rfl⟩ : syracuseStep 3720077 = 1395029) B1395029
theorem B1164179 : Blo 1160639 1164179 := bstep (se 1 (by rfl) ⟨873134, by rfl⟩ : syracuseStep 1164179 = 1746269) B1746269
theorem B1164195 : Blo 1160639 1164195 := bstep (se 1 (by rfl) ⟨873146, by rfl⟩ : syracuseStep 1164195 = 1746293) B1746293
theorem B1164211 : Blo 1160639 1164211 := bstep (se 1 (by rfl) ⟨873158, by rfl⟩ : syracuseStep 1164211 = 1746317) B1746317
theorem B1164227 : Blo 1160639 1164227 := bstep (se 1 (by rfl) ⟨873170, by rfl⟩ : syracuseStep 1164227 = 1746341) B1746341
theorem B1164243 : Blo 1160639 1164243 := bstep (se 1 (by rfl) ⟨873182, by rfl⟩ : syracuseStep 1164243 = 1746365) B1746365
theorem B1164259 : Blo 1160639 1164259 := bstep (se 1 (by rfl) ⟨873194, by rfl⟩ : syracuseStep 1164259 = 1746389) B1746389
theorem B1164275 : Blo 1160639 1164275 := bstep (se 1 (by rfl) ⟨873206, by rfl⟩ : syracuseStep 1164275 = 1746413) B1746413
theorem B1164291 : Blo 1160639 1164291 := bstep (se 1 (by rfl) ⟨873218, by rfl⟩ : syracuseStep 1164291 = 1746437) B1746437
theorem B1164307 : Blo 1160639 1164307 := bstep (se 1 (by rfl) ⟨873230, by rfl⟩ : syracuseStep 1164307 = 1746461) B1746461
theorem B1164323 : Blo 1160639 1164323 := bstep (se 1 (by rfl) ⟨873242, by rfl⟩ : syracuseStep 1164323 = 1746485) B1746485
theorem B1164339 : Blo 1160639 1164339 := bstep (se 1 (by rfl) ⟨873254, by rfl⟩ : syracuseStep 1164339 = 1746509) B1746509
theorem B1164355 : Blo 1160639 1164355 := bstep (se 1 (by rfl) ⟨873266, by rfl⟩ : syracuseStep 1164355 = 1746533) B1746533
theorem B1164371 : Blo 1160639 1164371 := bstep (se 1 (by rfl) ⟨873278, by rfl⟩ : syracuseStep 1164371 = 1746557) B1746557
theorem B1164387 : Blo 1160639 1164387 := bstep (se 1 (by rfl) ⟨873290, by rfl⟩ : syracuseStep 1164387 = 1746581) B1746581
theorem B7554161 : Blo 1160639 7554161 := bstep (se 2 (by rfl) ⟨2832810, by rfl⟩ : syracuseStep 7554161 = 5665621) B5665621
theorem B1164403 : Blo 1160639 1164403 := bstep (se 1 (by rfl) ⟨873302, by rfl⟩ : syracuseStep 1164403 = 1746605) B1746605
theorem B1164419 : Blo 1160639 1164419 := bstep (se 1 (by rfl) ⟨873314, by rfl⟩ : syracuseStep 1164419 = 1746629) B1746629
theorem B1164435 : Blo 1160639 1164435 := bstep (se 1 (by rfl) ⟨873326, by rfl⟩ : syracuseStep 1164435 = 1746653) B1746653
theorem B1655969 : Blo 1160639 1655969 := bstep (se 2 (by rfl) ⟨620988, by rfl⟩ : syracuseStep 1655969 = 1241977) B1241977
theorem B1164451 : Blo 1160639 1164451 := bstep (se 1 (by rfl) ⟨873338, by rfl⟩ : syracuseStep 1164451 = 1746677) B1746677
theorem B1164467 : Blo 1160639 1164467 := bstep (se 1 (by rfl) ⟨873350, by rfl⟩ : syracuseStep 1164467 = 1746701) B1746701
theorem B1164483 : Blo 1160639 1164483 := bstep (se 1 (by rfl) ⟨873362, by rfl⟩ : syracuseStep 1164483 = 1746725) B1746725
theorem B1164499 : Blo 1160639 1164499 := bstep (se 1 (by rfl) ⟨873374, by rfl⟩ : syracuseStep 1164499 = 1746749) B1746749
theorem B1164515 : Blo 1160639 1164515 := bstep (se 1 (by rfl) ⟨873386, by rfl⟩ : syracuseStep 1164515 = 1746773) B1746773
theorem B1164531 : Blo 1160639 1164531 := bstep (se 1 (by rfl) ⟨873398, by rfl⟩ : syracuseStep 1164531 = 1746797) B1746797
theorem B1164547 : Blo 1160639 1164547 := bstep (se 1 (by rfl) ⟨873410, by rfl⟩ : syracuseStep 1164547 = 1746821) B1746821
theorem B1656083 : Blo 1160639 1656083 := bstep (se 1 (by rfl) ⟨1242062, by rfl⟩ : syracuseStep 1656083 = 2484125) B2484125
theorem B1164563 : Blo 1160639 1164563 := bstep (se 1 (by rfl) ⟨873422, by rfl⟩ : syracuseStep 1164563 = 1746845) B1746845
theorem B1164579 : Blo 1160639 1164579 := bstep (se 1 (by rfl) ⟨873434, by rfl⟩ : syracuseStep 1164579 = 1746869) B1746869
theorem B3720497 : Blo 1160639 3720497 := bstep (se 2 (by rfl) ⟨1395186, by rfl⟩ : syracuseStep 3720497 = 2790373) B2790373
theorem B1164595 : Blo 1160639 1164595 := bstep (se 1 (by rfl) ⟨873446, by rfl⟩ : syracuseStep 1164595 = 1746893) B1746893
theorem B1164611 : Blo 1160639 1164611 := bstep (se 1 (by rfl) ⟨873458, by rfl⟩ : syracuseStep 1164611 = 1746917) B1746917
theorem B1164627 : Blo 1160639 1164627 := bstep (se 1 (by rfl) ⟨873470, by rfl⟩ : syracuseStep 1164627 = 1746941) B1746941
theorem B1656163 : Blo 1160639 1656163 := bstep (se 1 (by rfl) ⟨1242122, by rfl⟩ : syracuseStep 1656163 = 2484245) B2484245
theorem B5096881 : Blo 1160639 5096881 := bstep (se 2 (by rfl) ⟨1911330, by rfl⟩ : syracuseStep 5096881 = 3822661) B3822661
theorem B11322821 : Blo 1160639 11322821 := bstep (se 4 (by rfl) ⟨1061514, by rfl⟩ : syracuseStep 11322821 = 2123029) B2123029
theorem B8373773 : Blo 1160639 8373773 := bstep (se 3 (by rfl) ⟨1570082, by rfl⟩ : syracuseStep 8373773 = 3140165) B3140165
theorem B4408931 : Blo 1160639 4408931 := bstep (se 1 (by rfl) ⟨3306698, by rfl⟩ : syracuseStep 4408931 = 6613397) B6613397
theorem B32720525 : Blo 1160639 32720525 := bstep (se 3 (by rfl) ⟨6135098, by rfl⟩ : syracuseStep 32720525 = 12270197) B12270197
theorem B5654285 : Blo 1160639 5654285 := bstep (se 3 (by rfl) ⟨1060178, by rfl⟩ : syracuseStep 5654285 = 2120357) B2120357
theorem B3917645 : Blo 1160639 3917645 := bstep (se 3 (by rfl) ⟨734558, by rfl⟩ : syracuseStep 3917645 = 1469117) B1469117
theorem B3917699 : Blo 1160639 3917699 := bstep (se 1 (by rfl) ⟨2938274, by rfl⟩ : syracuseStep 3917699 = 5876549) B5876549
theorem B1656721 : Blo 1160639 1656721 := bstep (se 2 (by rfl) ⟨621270, by rfl⟩ : syracuseStep 1656721 = 1242541) B1242541
theorem B3360685 : Blo 1160639 3360685 := bstep (se 3 (by rfl) ⟨630128, by rfl⟩ : syracuseStep 3360685 = 1260257) B1260257
theorem B7260293 : Blo 1160639 7260293 := bstep (se 4 (by rfl) ⟨680652, by rfl⟩ : syracuseStep 7260293 = 1361305) B1361305
theorem B4966541 : Blo 1160639 4966541 := bstep (se 3 (by rfl) ⟨931226, by rfl⟩ : syracuseStep 4966541 = 1862453) B1862453
theorem B3917969 : Blo 1160639 3917969 := bstep (se 2 (by rfl) ⟨1469238, by rfl⟩ : syracuseStep 3917969 = 2938477) B2938477
theorem B3360941 : Blo 1160639 3360941 := bstep (se 3 (by rfl) ⟨630176, by rfl⟩ : syracuseStep 3360941 = 1260353) B1260353
theorem B4475057 : Blo 1160639 4475057 := bstep (se 2 (by rfl) ⟨1678146, by rfl⟩ : syracuseStep 4475057 = 3356293) B3356293
theorem B4409585 : Blo 1160639 4409585 := bstep (se 2 (by rfl) ⟨1653594, by rfl⟩ : syracuseStep 4409585 = 3307189) B3307189
theorem B3983633 : Blo 1160639 3983633 := bstep (se 2 (by rfl) ⟨1493862, by rfl⟩ : syracuseStep 3983633 = 2987725) B2987725
theorem B1394995 : Blo 1160639 1394995 := bstep (se 1 (by rfl) ⟨1046246, by rfl⟩ : syracuseStep 1394995 = 2092493) B2092493
theorem B1395091 : Blo 1160639 1395091 := bstep (se 1 (by rfl) ⟨1046318, by rfl⟩ : syracuseStep 1395091 = 2092637) B2092637
theorem B4966883 : Blo 1160639 4966883 := bstep (se 1 (by rfl) ⟨3725162, by rfl⟩ : syracuseStep 4966883 = 7450325) B7450325
theorem B1395235 : Blo 1160639 1395235 := bstep (se 1 (by rfl) ⟨1046426, by rfl⟩ : syracuseStep 1395235 = 2092853) B2092853
theorem B1657427 : Blo 1160639 1657427 := bstep (se 1 (by rfl) ⟨1243070, by rfl⟩ : syracuseStep 1657427 = 2486141) B2486141
theorem B3361421 : Blo 1160639 3361421 := bstep (se 3 (by rfl) ⟨630266, by rfl⟩ : syracuseStep 3361421 = 1260533) B1260533
theorem B3918509 : Blo 1160639 3918509 := bstep (se 3 (by rfl) ⟨734720, by rfl⟩ : syracuseStep 3918509 = 1469441) B1469441
theorem B3918563 : Blo 1160639 3918563 := bstep (se 1 (by rfl) ⟨2938922, by rfl⟩ : syracuseStep 3918563 = 5877845) B5877845
theorem B4967345 : Blo 1160639 4967345 := bstep (se 2 (by rfl) ⟨1862754, by rfl⟩ : syracuseStep 4967345 = 3725509) B3725509
theorem B3918833 : Blo 1160639 3918833 := bstep (se 2 (by rfl) ⟨1469562, by rfl⟩ : syracuseStep 3918833 = 2939125) B2939125
theorem B1658065 : Blo 1160639 1658065 := bstep (se 2 (by rfl) ⟨621774, by rfl⟩ : syracuseStep 1658065 = 1243549) B1243549
theorem B1658179 : Blo 1160639 1658179 := bstep (se 1 (by rfl) ⟨1243634, by rfl⟩ : syracuseStep 1658179 = 2487269) B2487269
theorem B5885297 : Blo 1160639 5885297 := bstep (se 2 (by rfl) ⟨2206986, by rfl⟩ : syracuseStep 5885297 = 4413973) B4413973
theorem B3919373 : Blo 1160639 3919373 := bstep (se 3 (by rfl) ⟨734882, by rfl⟩ : syracuseStep 3919373 = 1469765) B1469765
theorem B25120277 : Blo 1160639 25120277 := bstep (se 6 (by rfl) ⟨588756, by rfl⟩ : syracuseStep 25120277 = 1177513) B1177513
theorem B3919427 : Blo 1160639 3919427 := bstep (se 1 (by rfl) ⟨2939570, by rfl⟩ : syracuseStep 3919427 = 5879141) B5879141
theorem B4411043 : Blo 1160639 4411043 := bstep (se 1 (by rfl) ⟨3308282, by rfl⟩ : syracuseStep 4411043 = 6616565) B6616565
theorem B4411057 : Blo 1160639 4411057 := bstep (se 2 (by rfl) ⟨1654146, by rfl⟩ : syracuseStep 4411057 = 3308293) B3308293
theorem B1396451 : Blo 1160639 1396451 := bstep (se 1 (by rfl) ⟨1047338, by rfl⟩ : syracuseStep 1396451 = 2094677) B2094677
theorem B3919697 : Blo 1160639 3919697 := bstep (se 2 (by rfl) ⟨1469886, by rfl⟩ : syracuseStep 3919697 = 2939773) B2939773
theorem B1593281 : Blo 1160639 1593281 := bstep (se 2 (by rfl) ⟨597480, by rfl⟩ : syracuseStep 1593281 = 1194961) B1194961
theorem B125751523 : Blo 1160639 125751523 := bstep (se 1 (by rfl) ⟨94313642, by rfl⟩ : syracuseStep 125751523 = 188627285) B188627285
theorem B3920237 : Blo 1160639 3920237 := bstep (se 3 (by rfl) ⟨735044, by rfl⟩ : syracuseStep 3920237 = 1470089) B1470089
theorem B3920291 : Blo 1160639 3920291 := bstep (se 1 (by rfl) ⟨2940218, by rfl⟩ : syracuseStep 3920291 = 5880437) B5880437
theorem B3723907 : Blo 1160639 3723907 := bstep (se 1 (by rfl) ⟨2792930, by rfl⟩ : syracuseStep 3723907 = 5585861) B5585861
theorem B3920561 : Blo 1160639 3920561 := bstep (se 2 (by rfl) ⟨1470210, by rfl⟩ : syracuseStep 3920561 = 2940421) B2940421
theorem B5886755 : Blo 1160639 5886755 := bstep (se 1 (by rfl) ⟨4415066, by rfl⟩ : syracuseStep 5886755 = 8830133) B8830133
theorem B3724177 : Blo 1160639 3724177 := bstep (se 2 (by rfl) ⟨1396566, by rfl⟩ : syracuseStep 3724177 = 2793133) B2793133
theorem B2479025 : Blo 1160639 2479025 := bstep (se 2 (by rfl) ⟨929634, by rfl⟩ : syracuseStep 2479025 = 1859269) B1859269
theorem B4183139 : Blo 1160639 4183139 := bstep (se 1 (by rfl) ⟨3137354, by rfl⟩ : syracuseStep 4183139 = 6274709) B6274709
theorem B4412515 : Blo 1160639 4412515 := bstep (se 1 (by rfl) ⟨3309386, by rfl⟩ : syracuseStep 4412515 = 6618773) B6618773
theorem B232543345 : Blo 1160639 232543345 := bstep (se 2 (by rfl) ⟨87203754, by rfl⟩ : syracuseStep 232543345 = 174407509) B174407509
theorem B3921101 : Blo 1160639 3921101 := bstep (se 3 (by rfl) ⟨735206, by rfl⟩ : syracuseStep 3921101 = 1470413) B1470413
theorem B3921155 : Blo 1160639 3921155 := bstep (se 1 (by rfl) ⟨2940866, by rfl⟩ : syracuseStep 3921155 = 5881733) B5881733
theorem B8836451 : Blo 1160639 8836451 := bstep (se 1 (by rfl) ⟨6627338, by rfl⟩ : syracuseStep 8836451 = 13254677) B13254677
theorem B13424069 : Blo 1160639 13424069 := bstep (se 4 (by rfl) ⟨1258506, by rfl⟩ : syracuseStep 13424069 = 2517013) B2517013
theorem B11949581 : Blo 1160639 11949581 := bstep (se 3 (by rfl) ⟨2240546, by rfl⟩ : syracuseStep 11949581 = 4481093) B4481093
theorem B3921425 : Blo 1160639 3921425 := bstep (se 2 (by rfl) ⟨1470534, by rfl⟩ : syracuseStep 3921425 = 2941069) B2941069
theorem B5887565 : Blo 1160639 5887565 := bstep (se 3 (by rfl) ⟨1103918, by rfl⟩ : syracuseStep 5887565 = 2207837) B2207837
theorem B1890113 : Blo 1160639 1890113 := bstep (se 2 (by rfl) ⟨708792, by rfl⟩ : syracuseStep 1890113 = 1417585) B1417585
theorem B7460677 : Blo 1160639 7460677 := bstep (se 4 (by rfl) ⟨699438, by rfl⟩ : syracuseStep 7460677 = 1398877) B1398877
theorem B2938801 : Blo 1160639 2938801 := bstep (se 2 (by rfl) ⟨1102050, by rfl⟩ : syracuseStep 2938801 = 2204101) B2204101
theorem B3921965 : Blo 1160639 3921965 := bstep (se 3 (by rfl) ⟨735368, by rfl⟩ : syracuseStep 3921965 = 1470737) B1470737
theorem B2480195 : Blo 1160639 2480195 := bstep (se 1 (by rfl) ⟨1860146, by rfl⟩ : syracuseStep 2480195 = 3720293) B3720293
theorem B3922019 : Blo 1160639 3922019 := bstep (se 1 (by rfl) ⟨2941514, by rfl⟩ : syracuseStep 3922019 = 5883029) B5883029
theorem B2939075 : Blo 1160639 2939075 := bstep (se 1 (by rfl) ⟨2204306, by rfl⟩ : syracuseStep 2939075 = 4408613) B4408613
theorem B1399027 : Blo 1160639 1399027 := bstep (se 1 (by rfl) ⟨1049270, by rfl⟩ : syracuseStep 1399027 = 2098541) B2098541
theorem B3922289 : Blo 1160639 3922289 := bstep (se 2 (by rfl) ⟨1470858, by rfl⟩ : syracuseStep 3922289 = 2941717) B2941717
theorem B2939267 : Blo 1160639 2939267 := bstep (se 1 (by rfl) ⟨2204450, by rfl⟩ : syracuseStep 2939267 = 4408901) B4408901
theorem B2611601 : Blo 1160639 2611601 := bstep (se 2 (by rfl) ⟨979350, by rfl⟩ : syracuseStep 2611601 = 1958701) B1958701
theorem B2611619 : Blo 1160639 2611619 := bstep (se 1 (by rfl) ⟨1958714, by rfl⟩ : syracuseStep 2611619 = 3917429) B3917429
theorem B4970915 : Blo 1160639 4970915 := bstep (se 1 (by rfl) ⟨3728186, by rfl⟩ : syracuseStep 4970915 = 7456373) B7456373
theorem B5593549 : Blo 1160639 5593549 := bstep (se 3 (by rfl) ⟨1048790, by rfl⟩ : syracuseStep 5593549 = 2097581) B2097581
theorem B3725777 : Blo 1160639 3725777 := bstep (se 2 (by rfl) ⟨1397166, by rfl⟩ : syracuseStep 3725777 = 2794333) B2794333
theorem B2611889 : Blo 1160639 2611889 := bstep (se 2 (by rfl) ⟨979458, by rfl⟩ : syracuseStep 2611889 = 1958917) B1958917
theorem B2611907 : Blo 1160639 2611907 := bstep (se 1 (by rfl) ⟨1958930, by rfl⟩ : syracuseStep 2611907 = 3917861) B3917861
theorem B9427697 : Blo 1160639 9427697 := bstep (se 2 (by rfl) ⟨3535386, by rfl⟩ : syracuseStep 9427697 = 7070773) B7070773
theorem B3726125 : Blo 1160639 3726125 := bstep (se 3 (by rfl) ⟨698648, by rfl⟩ : syracuseStep 3726125 = 1397297) B1397297
theorem B6708017 : Blo 1160639 6708017 := bstep (se 2 (by rfl) ⟨2515506, by rfl⟩ : syracuseStep 6708017 = 5031013) B5031013
theorem B4709261 : Blo 1160639 4709261 := bstep (se 3 (by rfl) ⟨882986, by rfl⟩ : syracuseStep 4709261 = 1765973) B1765973
theorem B3922829 : Blo 1160639 3922829 := bstep (se 3 (by rfl) ⟨735530, by rfl⟩ : syracuseStep 3922829 = 1471061) B1471061
theorem B3922883 : Blo 1160639 3922883 := bstep (se 1 (by rfl) ⟨2942162, by rfl⟩ : syracuseStep 3922883 = 5884325) B5884325
theorem B2612177 : Blo 1160639 2612177 := bstep (se 2 (by rfl) ⟨979566, by rfl⟩ : syracuseStep 2612177 = 1959133) B1959133
theorem B2612195 : Blo 1160639 2612195 := bstep (se 1 (by rfl) ⟨1959146, by rfl⟩ : syracuseStep 2612195 = 3918293) B3918293
theorem B9919685 : Blo 1160639 9919685 := bstep (se 4 (by rfl) ⟨929970, by rfl⟩ : syracuseStep 9919685 = 1859941) B1859941
theorem B3923153 : Blo 1160639 3923153 := bstep (se 2 (by rfl) ⟨1471182, by rfl⟩ : syracuseStep 3923153 = 2942365) B2942365
theorem B2612465 : Blo 1160639 2612465 := bstep (se 2 (by rfl) ⟨979674, by rfl⟩ : syracuseStep 2612465 = 1959349) B1959349
theorem B2612483 : Blo 1160639 2612483 := bstep (se 1 (by rfl) ⟨1959362, by rfl⟩ : syracuseStep 2612483 = 3918725) B3918725
theorem B4414733 : Blo 1160639 4414733 := bstep (se 3 (by rfl) ⟨827762, by rfl⟩ : syracuseStep 4414733 = 1655525) B1655525
theorem B2940209 : Blo 1160639 2940209 := bstep (se 2 (by rfl) ⟨1102578, by rfl⟩ : syracuseStep 2940209 = 2205157) B2205157
theorem B7068977 : Blo 1160639 7068977 := bstep (se 2 (by rfl) ⟨2650866, by rfl⟩ : syracuseStep 7068977 = 5301733) B5301733
theorem B2940259 : Blo 1160639 2940259 := bstep (se 1 (by rfl) ⟨2205194, by rfl⟩ : syracuseStep 2940259 = 4410389) B4410389
theorem B2940401 : Blo 1160639 2940401 := bstep (se 2 (by rfl) ⟨1102650, by rfl⟩ : syracuseStep 2940401 = 2205301) B2205301
theorem B2612753 : Blo 1160639 2612753 := bstep (se 2 (by rfl) ⟨979782, by rfl⟩ : syracuseStep 2612753 = 1959565) B1959565
theorem B2612771 : Blo 1160639 2612771 := bstep (se 1 (by rfl) ⟨1959578, by rfl⟩ : syracuseStep 2612771 = 3919157) B3919157
theorem B6610481 : Blo 1160639 6610481 := bstep (se 2 (by rfl) ⟨2478930, by rfl⟩ : syracuseStep 6610481 = 4957861) B4957861
theorem B3923693 : Blo 1160639 3923693 := bstep (se 3 (by rfl) ⟨735692, by rfl⟩ : syracuseStep 3923693 = 1471385) B1471385
theorem B3923747 : Blo 1160639 3923747 := bstep (se 1 (by rfl) ⟨2942810, by rfl⟩ : syracuseStep 3923747 = 5885621) B5885621
theorem B2613041 : Blo 1160639 2613041 := bstep (se 2 (by rfl) ⟨979890, by rfl⟩ : syracuseStep 2613041 = 1959781) B1959781
theorem B2613059 : Blo 1160639 2613059 := bstep (se 1 (by rfl) ⟨1959794, by rfl⟩ : syracuseStep 2613059 = 3919589) B3919589
theorem B2482211 : Blo 1160639 2482211 := bstep (se 1 (by rfl) ⟨1861658, by rfl⟩ : syracuseStep 2482211 = 3723317) B3723317
theorem B3924017 : Blo 1160639 3924017 := bstep (se 2 (by rfl) ⟨1471506, by rfl⟩ : syracuseStep 3924017 = 2943013) B2943013
theorem B2613329 : Blo 1160639 2613329 := bstep (se 2 (by rfl) ⟨979998, by rfl⟩ : syracuseStep 2613329 = 1959997) B1959997
theorem B2613347 : Blo 1160639 2613347 := bstep (se 1 (by rfl) ⟨1960010, by rfl⟩ : syracuseStep 2613347 = 3920021) B3920021
theorem B1794161 : Blo 1160639 1794161 := bstep (se 2 (by rfl) ⟨672810, by rfl⟩ : syracuseStep 1794161 = 1345621) B1345621
theorem B7954787 : Blo 1160639 7954787 := bstep (se 1 (by rfl) ⟨5966090, by rfl⟩ : syracuseStep 7954787 = 11932181) B11932181
theorem B2613617 : Blo 1160639 2613617 := bstep (se 2 (by rfl) ⟨980106, by rfl⟩ : syracuseStep 2613617 = 1960213) B1960213
theorem B2613635 : Blo 1160639 2613635 := bstep (se 1 (by rfl) ⟨1960226, by rfl⟩ : syracuseStep 2613635 = 3920453) B3920453
theorem B5890481 : Blo 1160639 5890481 := bstep (se 2 (by rfl) ⟨2208930, by rfl⟩ : syracuseStep 5890481 = 4417861) B4417861
theorem B2941393 : Blo 1160639 2941393 := bstep (se 2 (by rfl) ⟨1103022, by rfl⟩ : syracuseStep 2941393 = 2206045) B2206045
theorem B6283747 : Blo 1160639 6283747 := bstep (se 1 (by rfl) ⟨4712810, by rfl⟩ : syracuseStep 6283747 = 9425621) B9425621
theorem B1991153 : Blo 1160639 1991153 := bstep (se 2 (by rfl) ⟨746682, by rfl⟩ : syracuseStep 1991153 = 1493365) B1493365
theorem B3924557 : Blo 1160639 3924557 := bstep (se 3 (by rfl) ⟨735854, by rfl⟩ : syracuseStep 3924557 = 1471709) B1471709
theorem B3727981 : Blo 1160639 3727981 := bstep (se 3 (by rfl) ⟨698996, by rfl⟩ : syracuseStep 3727981 = 1397993) B1397993
theorem B3924611 : Blo 1160639 3924611 := bstep (se 1 (by rfl) ⟨2943458, by rfl⟩ : syracuseStep 3924611 = 5886917) B5886917
theorem B2613905 : Blo 1160639 2613905 := bstep (se 2 (by rfl) ⟨980214, by rfl⟩ : syracuseStep 2613905 = 1960429) B1960429
theorem B2613923 : Blo 1160639 2613923 := bstep (se 1 (by rfl) ⟨1960442, by rfl⟩ : syracuseStep 2613923 = 3920885) B3920885
theorem B1958593 : Blo 1160639 1958593 := bstep (se 2 (by rfl) ⟨734472, by rfl⟩ : syracuseStep 1958593 = 1468945) B1468945
theorem B4186829 : Blo 1160639 4186829 := bstep (se 3 (by rfl) ⟨785030, by rfl⟩ : syracuseStep 4186829 = 1570061) B1570061
theorem B1958627 : Blo 1160639 1958627 := bstep (se 1 (by rfl) ⟨1468970, by rfl⟩ : syracuseStep 1958627 = 2937941) B2937941
theorem B2941667 : Blo 1160639 2941667 := bstep (se 1 (by rfl) ⟨2206250, by rfl⟩ : syracuseStep 2941667 = 4412501) B4412501
theorem B7070435 : Blo 1160639 7070435 := bstep (se 1 (by rfl) ⟨5302826, by rfl⟩ : syracuseStep 7070435 = 10605653) B10605653
theorem B1860403 : Blo 1160639 1860403 := bstep (se 1 (by rfl) ⟨1395302, by rfl⟩ : syracuseStep 1860403 = 2790605) B2790605
theorem B1958755 : Blo 1160639 1958755 := bstep (se 1 (by rfl) ⟨1469066, by rfl⟩ : syracuseStep 1958755 = 2938133) B2938133
theorem B3924881 : Blo 1160639 3924881 := bstep (se 2 (by rfl) ⟨1471830, by rfl⟩ : syracuseStep 3924881 = 2943661) B2943661
theorem B1860499 : Blo 1160639 1860499 := bstep (se 1 (by rfl) ⟨1395374, by rfl⟩ : syracuseStep 1860499 = 2790749) B2790749
theorem B2941859 : Blo 1160639 2941859 := bstep (se 1 (by rfl) ⟨2206394, by rfl⟩ : syracuseStep 2941859 = 4412789) B4412789
theorem B2614193 : Blo 1160639 2614193 := bstep (se 2 (by rfl) ⟨980322, by rfl⟩ : syracuseStep 2614193 = 1960645) B1960645
theorem B2614211 : Blo 1160639 2614211 := bstep (se 1 (by rfl) ⟨1960658, by rfl⟩ : syracuseStep 2614211 = 3921317) B3921317
theorem B6611939 : Blo 1160639 6611939 := bstep (se 1 (by rfl) ⟨4958954, by rfl⟩ : syracuseStep 6611939 = 9917909) B9917909
theorem B1958897 : Blo 1160639 1958897 := bstep (se 2 (by rfl) ⟨734586, by rfl⟩ : syracuseStep 1958897 = 1469173) B1469173
theorem B1860659 : Blo 1160639 1860659 := bstep (se 1 (by rfl) ⟨1395494, by rfl⟩ : syracuseStep 1860659 = 2790989) B2790989
theorem B1959025 : Blo 1160639 1959025 := bstep (se 2 (by rfl) ⟨734634, by rfl⟩ : syracuseStep 1959025 = 1469269) B1469269
theorem B3531907 : Blo 1160639 3531907 := bstep (se 1 (by rfl) ⟨2648930, by rfl⟩ : syracuseStep 3531907 = 5297861) B5297861
theorem B2516113 : Blo 1160639 2516113 := bstep (se 2 (by rfl) ⟨943542, by rfl⟩ : syracuseStep 2516113 = 1887085) B1887085
theorem B1959059 : Blo 1160639 1959059 := bstep (se 1 (by rfl) ⟨1469294, by rfl⟩ : syracuseStep 1959059 = 2938589) B2938589
theorem B5301425 : Blo 1160639 5301425 := bstep (se 2 (by rfl) ⟨1988034, by rfl⟩ : syracuseStep 5301425 = 3976069) B3976069
theorem B2614481 : Blo 1160639 2614481 := bstep (se 2 (by rfl) ⟨980430, by rfl⟩ : syracuseStep 2614481 = 1960861) B1960861
theorem B2614499 : Blo 1160639 2614499 := bstep (se 1 (by rfl) ⟨1960874, by rfl⟩ : syracuseStep 2614499 = 3921749) B3921749
theorem B4187405 : Blo 1160639 4187405 := bstep (se 3 (by rfl) ⟨785138, by rfl⟩ : syracuseStep 4187405 = 1570277) B1570277
theorem B1959187 : Blo 1160639 1959187 := bstep (se 1 (by rfl) ⟨1469390, by rfl⟩ : syracuseStep 1959187 = 2938781) B2938781
theorem B1959329 : Blo 1160639 1959329 := bstep (se 2 (by rfl) ⟨734748, by rfl⟩ : syracuseStep 1959329 = 1469497) B1469497
theorem B3925421 : Blo 1160639 3925421 := bstep (se 3 (by rfl) ⟨736016, by rfl⟩ : syracuseStep 3925421 = 1472033) B1472033
theorem B3925475 : Blo 1160639 3925475 := bstep (se 1 (by rfl) ⟨2944106, by rfl⟩ : syracuseStep 3925475 = 5888213) B5888213
theorem B2614769 : Blo 1160639 2614769 := bstep (se 2 (by rfl) ⟨980538, by rfl⟩ : syracuseStep 2614769 = 1961077) B1961077
theorem B2614787 : Blo 1160639 2614787 := bstep (se 1 (by rfl) ⟨1961090, by rfl⟩ : syracuseStep 2614787 = 3922181) B3922181
theorem B1959457 : Blo 1160639 1959457 := bstep (se 2 (by rfl) ⟨734796, by rfl⟩ : syracuseStep 1959457 = 1469593) B1469593
theorem B1959491 : Blo 1160639 1959491 := bstep (se 1 (by rfl) ⟨1469618, by rfl⟩ : syracuseStep 1959491 = 2939237) B2939237
theorem B1959619 : Blo 1160639 1959619 := bstep (se 1 (by rfl) ⟨1469714, by rfl⟩ : syracuseStep 1959619 = 2939429) B2939429
theorem B3925745 : Blo 1160639 3925745 := bstep (se 2 (by rfl) ⟨1472154, by rfl⟩ : syracuseStep 3925745 = 2944309) B2944309
theorem B2615057 : Blo 1160639 2615057 := bstep (se 2 (by rfl) ⟨980646, by rfl⟩ : syracuseStep 2615057 = 1961293) B1961293
theorem B2615075 : Blo 1160639 2615075 := bstep (se 1 (by rfl) ⟨1961306, by rfl⟩ : syracuseStep 2615075 = 3922613) B3922613
theorem B1959761 : Blo 1160639 1959761 := bstep (se 2 (by rfl) ⟨734910, by rfl⟩ : syracuseStep 1959761 = 1469821) B1469821
theorem B2942801 : Blo 1160639 2942801 := bstep (se 2 (by rfl) ⟨1103550, by rfl⟩ : syracuseStep 2942801 = 2207101) B2207101
theorem B5891939 : Blo 1160639 5891939 := bstep (se 1 (by rfl) ⟨4418954, by rfl⟩ : syracuseStep 5891939 = 8837909) B8837909
theorem B2942851 : Blo 1160639 2942851 := bstep (se 1 (by rfl) ⟨2207138, by rfl⟩ : syracuseStep 2942851 = 4414277) B4414277
theorem B6612941 : Blo 1160639 6612941 := bstep (se 3 (by rfl) ⟨1239926, by rfl⟩ : syracuseStep 6612941 = 2479853) B2479853
theorem B1959889 : Blo 1160639 1959889 := bstep (se 2 (by rfl) ⟨734958, by rfl⟩ : syracuseStep 1959889 = 1469917) B1469917
theorem B1959923 : Blo 1160639 1959923 := bstep (se 1 (by rfl) ⟨1469942, by rfl⟩ : syracuseStep 1959923 = 2939885) B2939885
theorem B1861633 : Blo 1160639 1861633 := bstep (se 2 (by rfl) ⟨698112, by rfl⟩ : syracuseStep 1861633 = 1396225) B1396225
theorem B2484227 : Blo 1160639 2484227 := bstep (se 1 (by rfl) ⟨1863170, by rfl⟩ : syracuseStep 2484227 = 3726341) B3726341
theorem B4974605 : Blo 1160639 4974605 := bstep (se 3 (by rfl) ⟨932738, by rfl⟩ : syracuseStep 4974605 = 1865477) B1865477
theorem B2942993 : Blo 1160639 2942993 := bstep (se 2 (by rfl) ⟨1103622, by rfl⟩ : syracuseStep 2942993 = 2207245) B2207245
theorem B2615345 : Blo 1160639 2615345 := bstep (se 2 (by rfl) ⟨980754, by rfl⟩ : syracuseStep 2615345 = 1961509) B1961509
theorem B4974641 : Blo 1160639 4974641 := bstep (se 2 (by rfl) ⟨1865490, by rfl⟩ : syracuseStep 4974641 = 3730981) B3730981
theorem B2615363 : Blo 1160639 2615363 := bstep (se 1 (by rfl) ⟨1961522, by rfl⟩ : syracuseStep 2615363 = 3923045) B3923045
theorem B4417649 : Blo 1160639 4417649 := bstep (se 2 (by rfl) ⟨1656618, by rfl⟩ : syracuseStep 4417649 = 3313237) B3313237
theorem B1960051 : Blo 1160639 1960051 := bstep (se 1 (by rfl) ⟨1470038, by rfl⟩ : syracuseStep 1960051 = 2940077) B2940077
theorem B9824483 : Blo 1160639 9824483 := bstep (se 1 (by rfl) ⟨7368362, by rfl⟩ : syracuseStep 9824483 = 14736725) B14736725
theorem B1960193 : Blo 1160639 1960193 := bstep (se 2 (by rfl) ⟨735072, by rfl⟩ : syracuseStep 1960193 = 1470145) B1470145
theorem B3926285 : Blo 1160639 3926285 := bstep (se 3 (by rfl) ⟨736178, by rfl⟩ : syracuseStep 3926285 = 1472357) B1472357
theorem B5040433 : Blo 1160639 5040433 := bstep (se 2 (by rfl) ⟨1890162, by rfl⟩ : syracuseStep 5040433 = 3780325) B3780325
theorem B3926339 : Blo 1160639 3926339 := bstep (se 1 (by rfl) ⟨2944754, by rfl⟩ : syracuseStep 3926339 = 5889509) B5889509
theorem B2615633 : Blo 1160639 2615633 := bstep (se 2 (by rfl) ⟨980862, by rfl⟩ : syracuseStep 2615633 = 1961725) B1961725
theorem B2615651 : Blo 1160639 2615651 := bstep (se 1 (by rfl) ⟨1961738, by rfl⟩ : syracuseStep 2615651 = 3923477) B3923477
theorem B1960321 : Blo 1160639 1960321 := bstep (se 2 (by rfl) ⟨735120, by rfl⟩ : syracuseStep 1960321 = 1470241) B1470241
theorem B1960355 : Blo 1160639 1960355 := bstep (se 1 (by rfl) ⟨1470266, by rfl⟩ : syracuseStep 1960355 = 2940533) B2940533
theorem B3729827 : Blo 1160639 3729827 := bstep (se 1 (by rfl) ⟨2797370, by rfl⟩ : syracuseStep 3729827 = 5594741) B5594741
theorem B1960483 : Blo 1160639 1960483 := bstep (se 1 (by rfl) ⟨1470362, by rfl⟩ : syracuseStep 1960483 = 2940725) B2940725
theorem B8841797 : Blo 1160639 8841797 := bstep (se 4 (by rfl) ⟨828918, by rfl⟩ : syracuseStep 8841797 = 1657837) B1657837
theorem B3926609 : Blo 1160639 3926609 := bstep (se 2 (by rfl) ⟨1472478, by rfl⟩ : syracuseStep 3926609 = 2944957) B2944957
theorem B1469011 : Blo 1160639 1469011 := bstep (se 1 (by rfl) ⟨1101758, by rfl⟩ : syracuseStep 1469011 = 2203517) B2203517
theorem B2615921 : Blo 1160639 2615921 := bstep (se 2 (by rfl) ⟨980970, by rfl⟩ : syracuseStep 2615921 = 1961941) B1961941
theorem B2615939 : Blo 1160639 2615939 := bstep (se 1 (by rfl) ⟨1961954, by rfl⟩ : syracuseStep 2615939 = 3923909) B3923909
theorem B5892749 : Blo 1160639 5892749 := bstep (se 3 (by rfl) ⟨1104890, by rfl⟩ : syracuseStep 5892749 = 2209781) B2209781
theorem B1960625 : Blo 1160639 1960625 := bstep (se 2 (by rfl) ⟨735234, by rfl⟩ : syracuseStep 1960625 = 1470469) B1470469
theorem B1469107 : Blo 1160639 1469107 := bstep (se 1 (by rfl) ⟨1101830, by rfl⟩ : syracuseStep 1469107 = 2203661) B2203661
theorem B1960753 : Blo 1160639 1960753 := bstep (se 2 (by rfl) ⟨735282, by rfl⟩ : syracuseStep 1960753 = 1470565) B1470565
theorem B3730225 : Blo 1160639 3730225 := bstep (se 2 (by rfl) ⟨1398834, by rfl⟩ : syracuseStep 3730225 = 2797669) B2797669
theorem B2091857 : Blo 1160639 2091857 := bstep (se 2 (by rfl) ⟨784446, by rfl⟩ : syracuseStep 2091857 = 1568893) B1568893
theorem B1960787 : Blo 1160639 1960787 := bstep (se 1 (by rfl) ⟨1470590, by rfl⟩ : syracuseStep 1960787 = 2941181) B2941181
theorem B2616209 : Blo 1160639 2616209 := bstep (se 2 (by rfl) ⟨981078, by rfl⟩ : syracuseStep 2616209 = 1962157) B1962157
theorem B2616227 : Blo 1160639 2616227 := bstep (se 1 (by rfl) ⟨1962170, by rfl⟩ : syracuseStep 2616227 = 3924341) B3924341
theorem B1960915 : Blo 1160639 1960915 := bstep (se 1 (by rfl) ⟨1470686, by rfl⟩ : syracuseStep 1960915 = 2941373) B2941373
theorem B2943985 : Blo 1160639 2943985 := bstep (se 2 (by rfl) ⟨1103994, by rfl⟩ : syracuseStep 2943985 = 2207989) B2207989
theorem B47803445 : Blo 1160639 47803445 := bstep (se 5 (by rfl) ⟨2240786, by rfl⟩ : syracuseStep 47803445 = 4481573) B4481573
theorem B1961057 : Blo 1160639 1961057 := bstep (se 2 (by rfl) ⟨735396, by rfl⟩ : syracuseStep 1961057 = 1470793) B1470793
theorem B7957603 : Blo 1160639 7957603 := bstep (se 1 (by rfl) ⟨5968202, by rfl⟩ : syracuseStep 7957603 = 11936405) B11936405
theorem B3927149 : Blo 1160639 3927149 := bstep (se 3 (by rfl) ⟨736340, by rfl⟩ : syracuseStep 3927149 = 1472681) B1472681
theorem B1469603 : Blo 1160639 1469603 := bstep (se 1 (by rfl) ⟨1102202, by rfl⟩ : syracuseStep 1469603 = 2204405) B2204405
theorem B3927203 : Blo 1160639 3927203 := bstep (se 1 (by rfl) ⟨2945402, by rfl⟩ : syracuseStep 3927203 = 5890805) B5890805
theorem B2616497 : Blo 1160639 2616497 := bstep (se 2 (by rfl) ⟨981186, by rfl⟩ : syracuseStep 2616497 = 1962373) B1962373
theorem B2616515 : Blo 1160639 2616515 := bstep (se 1 (by rfl) ⟨1962386, by rfl⟩ : syracuseStep 2616515 = 3924773) B3924773
theorem B1961185 : Blo 1160639 1961185 := bstep (se 2 (by rfl) ⟨735444, by rfl⟩ : syracuseStep 1961185 = 1470889) B1470889
theorem B2485475 : Blo 1160639 2485475 := bstep (se 1 (by rfl) ⟨1864106, by rfl⟩ : syracuseStep 2485475 = 3728213) B3728213
theorem B3730673 : Blo 1160639 3730673 := bstep (se 2 (by rfl) ⟨1399002, by rfl⟩ : syracuseStep 3730673 = 2798005) B2798005
theorem B1305859 : Blo 1160639 1305859 := bstep (se 1 (by rfl) ⟨979394, by rfl⟩ : syracuseStep 1305859 = 1958789) B1958789
theorem B1961219 : Blo 1160639 1961219 := bstep (se 1 (by rfl) ⟨1470914, by rfl⟩ : syracuseStep 1961219 = 2941829) B2941829
theorem B2944259 : Blo 1160639 2944259 := bstep (se 1 (by rfl) ⟨2208194, by rfl⟩ : syracuseStep 2944259 = 4416389) B4416389
theorem B1961347 : Blo 1160639 1961347 := bstep (se 1 (by rfl) ⟨1471010, by rfl⟩ : syracuseStep 1961347 = 2942021) B2942021
theorem B3403139 : Blo 1160639 3403139 := bstep (se 1 (by rfl) ⟨2552354, by rfl⟩ : syracuseStep 3403139 = 5104709) B5104709
theorem B1306003 : Blo 1160639 1306003 := bstep (se 1 (by rfl) ⟨979502, by rfl⟩ : syracuseStep 1306003 = 1959005) B1959005
theorem B3927473 : Blo 1160639 3927473 := bstep (se 2 (by rfl) ⟨1472802, by rfl⟩ : syracuseStep 3927473 = 2945605) B2945605
theorem B2944451 : Blo 1160639 2944451 := bstep (se 1 (by rfl) ⟨2208338, by rfl⟩ : syracuseStep 2944451 = 4416677) B4416677
theorem B2616785 : Blo 1160639 2616785 := bstep (se 2 (by rfl) ⟨981294, by rfl⟩ : syracuseStep 2616785 = 1962589) B1962589
theorem B2616803 : Blo 1160639 2616803 := bstep (se 1 (by rfl) ⟨1962602, by rfl⟩ : syracuseStep 2616803 = 3925205) B3925205
theorem B1961489 : Blo 1160639 1961489 := bstep (se 2 (by rfl) ⟨735558, by rfl⟩ : syracuseStep 1961489 = 1471117) B1471117
theorem B1306147 : Blo 1160639 1306147 := bstep (se 1 (by rfl) ⟨979610, by rfl⟩ : syracuseStep 1306147 = 1959221) B1959221
theorem B4419107 : Blo 1160639 4419107 := bstep (se 1 (by rfl) ⟨3314330, by rfl⟩ : syracuseStep 4419107 = 6628661) B6628661
theorem B4025987 : Blo 1160639 4025987 := bstep (se 1 (by rfl) ⟨3019490, by rfl⟩ : syracuseStep 4025987 = 6038981) B6038981
theorem B1863299 : Blo 1160639 1863299 := bstep (se 1 (by rfl) ⟨1397474, by rfl⟩ : syracuseStep 1863299 = 2794949) B2794949
theorem B1961617 : Blo 1160639 1961617 := bstep (se 2 (by rfl) ⟨735606, by rfl⟩ : syracuseStep 1961617 = 1471213) B1471213
theorem B1306291 : Blo 1160639 1306291 := bstep (se 1 (by rfl) ⟨979718, by rfl⟩ : syracuseStep 1306291 = 1959437) B1959437
theorem B1961651 : Blo 1160639 1961651 := bstep (se 1 (by rfl) ⟨1471238, by rfl⟩ : syracuseStep 1961651 = 2942477) B2942477
theorem B2617073 : Blo 1160639 2617073 := bstep (se 2 (by rfl) ⟨981402, by rfl⟩ : syracuseStep 2617073 = 1962805) B1962805
theorem B2617091 : Blo 1160639 2617091 := bstep (se 1 (by rfl) ⟨1962818, by rfl⟩ : syracuseStep 2617091 = 3925637) B3925637
theorem B1863427 : Blo 1160639 1863427 := bstep (se 1 (by rfl) ⟨1397570, by rfl⟩ : syracuseStep 1863427 = 2795141) B2795141
theorem B2486065 : Blo 1160639 2486065 := bstep (se 2 (by rfl) ⟨932274, by rfl⟩ : syracuseStep 2486065 = 1864549) B1864549
theorem B1961779 : Blo 1160639 1961779 := bstep (se 1 (by rfl) ⟨1471334, by rfl⟩ : syracuseStep 1961779 = 2942669) B2942669
theorem B1306435 : Blo 1160639 1306435 := bstep (se 1 (by rfl) ⟨979826, by rfl⟩ : syracuseStep 1306435 = 1959653) B1959653
theorem B1863491 : Blo 1160639 1863491 := bstep (se 1 (by rfl) ⟨1397618, by rfl⟩ : syracuseStep 1863491 = 2795237) B2795237
theorem B1470307 : Blo 1160639 1470307 := bstep (se 1 (by rfl) ⟨1102730, by rfl⟩ : syracuseStep 1470307 = 2205461) B2205461
theorem B1961921 : Blo 1160639 1961921 := bstep (se 2 (by rfl) ⟨735720, by rfl⟩ : syracuseStep 1961921 = 1471441) B1471441
theorem B1470403 : Blo 1160639 1470403 := bstep (se 1 (by rfl) ⟨1102802, by rfl⟩ : syracuseStep 1470403 = 2205605) B2205605
theorem B3928013 : Blo 1160639 3928013 := bstep (se 3 (by rfl) ⟨736502, by rfl⟩ : syracuseStep 3928013 = 1473005) B1473005
theorem B1306579 : Blo 1160639 1306579 := bstep (se 1 (by rfl) ⟨979934, by rfl⟩ : syracuseStep 1306579 = 1959869) B1959869
theorem B3928067 : Blo 1160639 3928067 := bstep (se 1 (by rfl) ⟨2946050, by rfl⟩ : syracuseStep 3928067 = 5892101) B5892101
theorem B2617361 : Blo 1160639 2617361 := bstep (se 2 (by rfl) ⟨981510, by rfl⟩ : syracuseStep 2617361 = 1963021) B1963021
theorem B5304355 : Blo 1160639 5304355 := bstep (se 1 (by rfl) ⟨3978266, by rfl⟩ : syracuseStep 5304355 = 7956533) B7956533
theorem B2617379 : Blo 1160639 2617379 := bstep (se 1 (by rfl) ⟨1963034, by rfl⟩ : syracuseStep 2617379 = 3926069) B3926069
theorem B1962049 : Blo 1160639 1962049 := bstep (se 2 (by rfl) ⟨735768, by rfl⟩ : syracuseStep 1962049 = 1471537) B1471537
theorem B3305549 : Blo 1160639 3305549 := bstep (se 3 (by rfl) ⟨619790, by rfl⟩ : syracuseStep 3305549 = 1239581) B1239581
theorem B1306723 : Blo 1160639 1306723 := bstep (se 1 (by rfl) ⟨980042, by rfl⟩ : syracuseStep 1306723 = 1960085) B1960085
theorem B1962083 : Blo 1160639 1962083 := bstep (se 1 (by rfl) ⟨1471562, by rfl⟩ : syracuseStep 1962083 = 2943125) B2943125
theorem B4714595 : Blo 1160639 4714595 := bstep (se 1 (by rfl) ⟨3535946, by rfl⟩ : syracuseStep 4714595 = 7071893) B7071893
theorem B2977955 : Blo 1160639 2977955 := bstep (se 1 (by rfl) ⟨2233466, by rfl⟩ : syracuseStep 2977955 = 4466933) B4466933
theorem B1962211 : Blo 1160639 1962211 := bstep (se 1 (by rfl) ⟨1471658, by rfl⟩ : syracuseStep 1962211 = 2943317) B2943317
theorem B1306867 : Blo 1160639 1306867 := bstep (se 1 (by rfl) ⟨980150, by rfl⟩ : syracuseStep 1306867 = 1960301) B1960301
theorem B1765633 : Blo 1160639 1765633 := bstep (se 2 (by rfl) ⟨662112, by rfl⟩ : syracuseStep 1765633 = 1324225) B1324225
theorem B3305731 : Blo 1160639 3305731 := bstep (se 1 (by rfl) ⟨2479298, by rfl⟩ : syracuseStep 3305731 = 4958597) B4958597
theorem B3928337 : Blo 1160639 3928337 := bstep (se 2 (by rfl) ⟨1473126, by rfl⟩ : syracuseStep 3928337 = 2946253) B2946253
theorem B2617649 : Blo 1160639 2617649 := bstep (se 2 (by rfl) ⟨981618, by rfl⟩ : syracuseStep 2617649 = 1963237) B1963237
theorem B1863985 : Blo 1160639 1863985 := bstep (se 2 (by rfl) ⟨698994, by rfl⟩ : syracuseStep 1863985 = 1397989) B1397989
theorem B2617667 : Blo 1160639 2617667 := bstep (se 1 (by rfl) ⟨1963250, by rfl⟩ : syracuseStep 2617667 = 3926501) B3926501
theorem B1962353 : Blo 1160639 1962353 := bstep (se 2 (by rfl) ⟨735882, by rfl⟩ : syracuseStep 1962353 = 1471765) B1471765
theorem B2945393 : Blo 1160639 2945393 := bstep (se 2 (by rfl) ⟨1104522, by rfl⟩ : syracuseStep 2945393 = 2209045) B2209045
theorem B1307011 : Blo 1160639 1307011 := bstep (se 1 (by rfl) ⟨980258, by rfl⟩ : syracuseStep 1307011 = 1960517) B1960517
theorem B2945443 : Blo 1160639 2945443 := bstep (se 1 (by rfl) ⟨2209082, by rfl⟩ : syracuseStep 2945443 = 4418165) B4418165
theorem B1470899 : Blo 1160639 1470899 := bstep (se 1 (by rfl) ⟨1103174, by rfl⟩ : syracuseStep 1470899 = 2206349) B2206349
theorem B1962481 : Blo 1160639 1962481 := bstep (se 2 (by rfl) ⟨735930, by rfl⟩ : syracuseStep 1962481 = 1471861) B1471861
theorem B4420109 : Blo 1160639 4420109 := bstep (se 3 (by rfl) ⟨828770, by rfl⟩ : syracuseStep 4420109 = 1657541) B1657541
theorem B1307155 : Blo 1160639 1307155 := bstep (se 1 (by rfl) ⟨980366, by rfl⟩ : syracuseStep 1307155 = 1960733) B1960733
theorem B1962515 : Blo 1160639 1962515 := bstep (se 1 (by rfl) ⟨1471886, by rfl⟩ : syracuseStep 1962515 = 2943773) B2943773
theorem B2945585 : Blo 1160639 2945585 := bstep (se 2 (by rfl) ⟨1104594, by rfl⟩ : syracuseStep 2945585 = 2209189) B2209189
theorem B2617937 : Blo 1160639 2617937 := bstep (se 2 (by rfl) ⟨981726, by rfl⟩ : syracuseStep 2617937 = 1963453) B1963453
theorem B2617955 : Blo 1160639 2617955 := bstep (se 1 (by rfl) ⟨1963466, by rfl⟩ : syracuseStep 2617955 = 3926933) B3926933
theorem B1962643 : Blo 1160639 1962643 := bstep (se 1 (by rfl) ⟨1471982, by rfl⟩ : syracuseStep 1962643 = 2943965) B2943965
theorem B1307299 : Blo 1160639 1307299 := bstep (se 1 (by rfl) ⟨980474, by rfl⟩ : syracuseStep 1307299 = 1960949) B1960949
theorem B3306221 : Blo 1160639 3306221 := bstep (se 3 (by rfl) ⟨619916, by rfl⟩ : syracuseStep 3306221 = 1239833) B1239833
theorem B6124301 : Blo 1160639 6124301 := bstep (se 3 (by rfl) ⟨1148306, by rfl⟩ : syracuseStep 6124301 = 2296613) B2296613
theorem B1962785 : Blo 1160639 1962785 := bstep (se 2 (by rfl) ⟨736044, by rfl⟩ : syracuseStep 1962785 = 1472089) B1472089
theorem B4191011 : Blo 1160639 4191011 := bstep (se 1 (by rfl) ⟨3143258, by rfl⟩ : syracuseStep 4191011 = 6286517) B6286517
theorem B3928877 : Blo 1160639 3928877 := bstep (se 3 (by rfl) ⟨736664, by rfl⟩ : syracuseStep 3928877 = 1473329) B1473329
theorem B6615857 : Blo 1160639 6615857 := bstep (se 2 (by rfl) ⟨2480946, by rfl⟩ : syracuseStep 6615857 = 4961893) B4961893
theorem B1307443 : Blo 1160639 1307443 := bstep (se 1 (by rfl) ⟨980582, by rfl⟩ : syracuseStep 1307443 = 1961165) B1961165
theorem B1241939 : Blo 1160639 1241939 := bstep (se 1 (by rfl) ⟨931454, by rfl⟩ : syracuseStep 1241939 = 1862909) B1862909
theorem B3928931 : Blo 1160639 3928931 := bstep (se 1 (by rfl) ⟨2946698, by rfl⟩ : syracuseStep 3928931 = 5893397) B5893397
theorem B2618225 : Blo 1160639 2618225 := bstep (se 2 (by rfl) ⟨981834, by rfl⟩ : syracuseStep 2618225 = 1963669) B1963669
theorem B2618243 : Blo 1160639 2618243 := bstep (se 1 (by rfl) ⟨1963682, by rfl⟩ : syracuseStep 2618243 = 3927365) B3927365
theorem B1962913 : Blo 1160639 1962913 := bstep (se 2 (by rfl) ⟨736092, by rfl⟩ : syracuseStep 1962913 = 1472185) B1472185
theorem B1307587 : Blo 1160639 1307587 := bstep (se 1 (by rfl) ⟨980690, by rfl⟩ : syracuseStep 1307587 = 1961381) B1961381
theorem B1962947 : Blo 1160639 1962947 := bstep (se 1 (by rfl) ⟨1472210, by rfl⟩ : syracuseStep 1962947 = 2944421) B2944421
theorem B1864657 : Blo 1160639 1864657 := bstep (se 2 (by rfl) ⟨699246, by rfl⟩ : syracuseStep 1864657 = 1398493) B1398493
theorem B1963075 : Blo 1160639 1963075 := bstep (se 1 (by rfl) ⟨1472306, by rfl⟩ : syracuseStep 1963075 = 2944613) B2944613
theorem B1307731 : Blo 1160639 1307731 := bstep (se 1 (by rfl) ⟨980798, by rfl⟩ : syracuseStep 1307731 = 1961597) B1961597
theorem B3929201 : Blo 1160639 3929201 := bstep (se 2 (by rfl) ⟨1473450, by rfl⟩ : syracuseStep 3929201 = 2946901) B2946901
theorem B1471603 : Blo 1160639 1471603 := bstep (se 1 (by rfl) ⟨1103702, by rfl⟩ : syracuseStep 1471603 = 2207405) B2207405
theorem B2651267 : Blo 1160639 2651267 := bstep (se 1 (by rfl) ⟨1988450, by rfl⟩ : syracuseStep 2651267 = 3976901) B3976901
theorem B2618513 : Blo 1160639 2618513 := bstep (se 2 (by rfl) ⟨981942, by rfl⟩ : syracuseStep 2618513 = 1963885) B1963885
theorem B2618531 : Blo 1160639 2618531 := bstep (se 1 (by rfl) ⟨1963898, by rfl⟩ : syracuseStep 2618531 = 3927797) B3927797
theorem B1963217 : Blo 1160639 1963217 := bstep (se 2 (by rfl) ⟨736206, by rfl⟩ : syracuseStep 1963217 = 1472413) B1472413
theorem B1471699 : Blo 1160639 1471699 := bstep (se 1 (by rfl) ⟨1103774, by rfl⟩ : syracuseStep 1471699 = 2207549) B2207549
theorem B1307875 : Blo 1160639 1307875 := bstep (se 1 (by rfl) ⟨980906, by rfl⟩ : syracuseStep 1307875 = 1961813) B1961813
theorem B1963345 : Blo 1160639 1963345 := bstep (se 2 (by rfl) ⟨736254, by rfl⟩ : syracuseStep 1963345 = 1472509) B1472509
theorem B1308019 : Blo 1160639 1308019 := bstep (se 1 (by rfl) ⟨981014, by rfl⟩ : syracuseStep 1308019 = 1962029) B1962029
theorem B1963379 : Blo 1160639 1963379 := bstep (se 1 (by rfl) ⟨1472534, by rfl⟩ : syracuseStep 1963379 = 2945069) B2945069
theorem B3143053 : Blo 1160639 3143053 := bstep (se 3 (by rfl) ⟨589322, by rfl⟩ : syracuseStep 3143053 = 1178645) B1178645
theorem B2618801 : Blo 1160639 2618801 := bstep (se 2 (by rfl) ⟨982050, by rfl⟩ : syracuseStep 2618801 = 1964101) B1964101
theorem B2618819 : Blo 1160639 2618819 := bstep (se 1 (by rfl) ⟨1964114, by rfl⟩ : syracuseStep 2618819 = 3928229) B3928229
theorem B5895665 : Blo 1160639 5895665 := bstep (se 2 (by rfl) ⟨2210874, by rfl⟩ : syracuseStep 5895665 = 4421749) B4421749
theorem B1963507 : Blo 1160639 1963507 := bstep (se 1 (by rfl) ⟨1472630, by rfl⟩ : syracuseStep 1963507 = 2945261) B2945261
theorem B1308163 : Blo 1160639 1308163 := bstep (se 1 (by rfl) ⟨981122, by rfl⟩ : syracuseStep 1308163 = 1962245) B1962245
theorem B2946577 : Blo 1160639 2946577 := bstep (se 2 (by rfl) ⟨1104966, by rfl⟩ : syracuseStep 2946577 = 2209933) B2209933
theorem B2356771 : Blo 1160639 2356771 := bstep (se 1 (by rfl) ⟨1767578, by rfl⟩ : syracuseStep 2356771 = 3535157) B3535157
theorem B1963649 : Blo 1160639 1963649 := bstep (se 2 (by rfl) ⟨736368, by rfl⟩ : syracuseStep 1963649 = 1472737) B1472737
theorem B3929741 : Blo 1160639 3929741 := bstep (se 3 (by rfl) ⟨736826, by rfl⟩ : syracuseStep 3929741 = 1473653) B1473653
theorem B1308307 : Blo 1160639 1308307 := bstep (se 1 (by rfl) ⟨981230, by rfl⟩ : syracuseStep 1308307 = 1962461) B1962461
theorem B1472195 : Blo 1160639 1472195 := bstep (se 1 (by rfl) ⟨1104146, by rfl⟩ : syracuseStep 1472195 = 2208293) B2208293
theorem B3929795 : Blo 1160639 3929795 := bstep (se 1 (by rfl) ⟨2947346, by rfl⟩ : syracuseStep 3929795 = 5894693) B5894693
theorem B2619089 : Blo 1160639 2619089 := bstep (se 2 (by rfl) ⟨982158, by rfl⟩ : syracuseStep 2619089 = 1964317) B1964317
theorem B2619107 : Blo 1160639 2619107 := bstep (se 1 (by rfl) ⟨1964330, by rfl⟩ : syracuseStep 2619107 = 3928661) B3928661
theorem B1963777 : Blo 1160639 1963777 := bstep (se 2 (by rfl) ⟨736416, by rfl⟩ : syracuseStep 1963777 = 1472833) B1472833
theorem B1308451 : Blo 1160639 1308451 := bstep (se 1 (by rfl) ⟨981338, by rfl⟩ : syracuseStep 1308451 = 1962677) B1962677
theorem B1963811 : Blo 1160639 1963811 := bstep (se 1 (by rfl) ⟨1472858, by rfl⟩ : syracuseStep 1963811 = 2945717) B2945717
theorem B2946851 : Blo 1160639 2946851 := bstep (se 1 (by rfl) ⟨2210138, by rfl⟩ : syracuseStep 2946851 = 4420277) B4420277
theorem B3307405 : Blo 1160639 3307405 := bstep (se 3 (by rfl) ⟨620138, by rfl⟩ : syracuseStep 3307405 = 1240277) B1240277
theorem B1963939 : Blo 1160639 1963939 := bstep (se 1 (by rfl) ⟨1472954, by rfl⟩ : syracuseStep 1963939 = 2945909) B2945909
theorem B1308595 : Blo 1160639 1308595 := bstep (se 1 (by rfl) ⟨981446, by rfl⟩ : syracuseStep 1308595 = 1962893) B1962893
theorem B2357201 : Blo 1160639 2357201 := bstep (se 2 (by rfl) ⟨883950, by rfl⟩ : syracuseStep 2357201 = 1767901) B1767901
theorem B3930065 : Blo 1160639 3930065 := bstep (se 2 (by rfl) ⟨1473774, by rfl⟩ : syracuseStep 3930065 = 2947549) B2947549
theorem B2947043 : Blo 1160639 2947043 := bstep (se 1 (by rfl) ⟨2210282, by rfl⟩ : syracuseStep 2947043 = 4420565) B4420565
theorem B2619377 : Blo 1160639 2619377 := bstep (se 2 (by rfl) ⟨982266, by rfl⟩ : syracuseStep 2619377 = 1964533) B1964533
theorem B2619395 : Blo 1160639 2619395 := bstep (se 1 (by rfl) ⟨1964546, by rfl⟩ : syracuseStep 2619395 = 3929093) B3929093
theorem B2095139 : Blo 1160639 2095139 := bstep (se 1 (by rfl) ⟨1571354, by rfl⟩ : syracuseStep 2095139 = 3142709) B3142709
theorem B1964081 : Blo 1160639 1964081 := bstep (se 2 (by rfl) ⟨736530, by rfl⟩ : syracuseStep 1964081 = 1473061) B1473061
theorem B1308739 : Blo 1160639 1308739 := bstep (se 1 (by rfl) ⟨981554, by rfl⟩ : syracuseStep 1308739 = 1963109) B1963109
theorem B3143843 : Blo 1160639 3143843 := bstep (se 1 (by rfl) ⟨2357882, by rfl⟩ : syracuseStep 3143843 = 4715765) B4715765
theorem B1964209 : Blo 1160639 1964209 := bstep (se 2 (by rfl) ⟨736578, by rfl⟩ : syracuseStep 1964209 = 1473157) B1473157
theorem B1308883 : Blo 1160639 1308883 := bstep (se 1 (by rfl) ⟨981662, by rfl⟩ : syracuseStep 1308883 = 1963325) B1963325
theorem B1964243 : Blo 1160639 1964243 := bstep (se 1 (by rfl) ⟨1473182, by rfl⟩ : syracuseStep 1964243 = 2946365) B2946365
theorem B6617315 : Blo 1160639 6617315 := bstep (se 1 (by rfl) ⟨4962986, by rfl⟩ : syracuseStep 6617315 = 9925973) B9925973
theorem B2619665 : Blo 1160639 2619665 := bstep (se 2 (by rfl) ⟨982374, by rfl⟩ : syracuseStep 2619665 = 1964749) B1964749
theorem B2619683 : Blo 1160639 2619683 := bstep (se 1 (by rfl) ⟨1964762, by rfl⟩ : syracuseStep 2619683 = 3929525) B3929525
theorem B1964371 : Blo 1160639 1964371 := bstep (se 1 (by rfl) ⟨1473278, by rfl⟩ : syracuseStep 1964371 = 2946557) B2946557
theorem B1309027 : Blo 1160639 1309027 := bstep (se 1 (by rfl) ⟨981770, by rfl⟩ : syracuseStep 1309027 = 1963541) B1963541
theorem B1472899 : Blo 1160639 1472899 := bstep (se 1 (by rfl) ⟨1104674, by rfl⟩ : syracuseStep 1472899 = 2209349) B2209349
theorem B1767827 : Blo 1160639 1767827 := bstep (se 1 (by rfl) ⟨1325870, by rfl⟩ : syracuseStep 1767827 = 2651741) B2651741
theorem B1964513 : Blo 1160639 1964513 := bstep (se 2 (by rfl) ⟨736692, by rfl⟩ : syracuseStep 1964513 = 1473385) B1473385
theorem B1472995 : Blo 1160639 1472995 := bstep (se 1 (by rfl) ⟨1104746, by rfl⟩ : syracuseStep 1472995 = 2209493) B2209493
theorem B3930605 : Blo 1160639 3930605 := bstep (se 3 (by rfl) ⟨736988, by rfl⟩ : syracuseStep 3930605 = 1473977) B1473977
theorem B1309171 : Blo 1160639 1309171 := bstep (se 1 (by rfl) ⟨981878, by rfl⟩ : syracuseStep 1309171 = 1963757) B1963757
theorem B6289933 : Blo 1160639 6289933 := bstep (se 3 (by rfl) ⟨1179362, by rfl⟩ : syracuseStep 6289933 = 2358725) B2358725
theorem B3930659 : Blo 1160639 3930659 := bstep (se 1 (by rfl) ⟨2947994, by rfl⟩ : syracuseStep 3930659 = 5895989) B5895989
theorem B2619953 : Blo 1160639 2619953 := bstep (se 2 (by rfl) ⟨982482, by rfl⟩ : syracuseStep 2619953 = 1964965) B1964965
theorem B2619971 : Blo 1160639 2619971 := bstep (se 1 (by rfl) ⟨1964978, by rfl⟩ : syracuseStep 2619971 = 3929957) B3929957
theorem B1964641 : Blo 1160639 1964641 := bstep (se 2 (by rfl) ⟨736740, by rfl⟩ : syracuseStep 1964641 = 1473481) B1473481
theorem B26835569 : Blo 1160639 26835569 := bstep (se 2 (by rfl) ⟨10063338, by rfl⟩ : syracuseStep 26835569 = 20126677) B20126677
theorem B1178227 : Blo 1160639 1178227 := bstep (se 1 (by rfl) ⟨883670, by rfl⟩ : syracuseStep 1178227 = 1767341) B1767341
theorem B1309315 : Blo 1160639 1309315 := bstep (se 1 (by rfl) ⟨981986, by rfl⟩ : syracuseStep 1309315 = 1963973) B1963973
theorem B1964675 : Blo 1160639 1964675 := bstep (se 1 (by rfl) ⟨1473506, by rfl⟩ : syracuseStep 1964675 = 2947013) B2947013
theorem B3537553 : Blo 1160639 3537553 := bstep (se 2 (by rfl) ⟨1326582, by rfl⟩ : syracuseStep 3537553 = 2653165) B2653165
theorem B1964803 : Blo 1160639 1964803 := bstep (se 1 (by rfl) ⟨1473602, by rfl⟩ : syracuseStep 1964803 = 2947205) B2947205
theorem B1309459 : Blo 1160639 1309459 := bstep (se 1 (by rfl) ⟨982094, by rfl⟩ : syracuseStep 1309459 = 1964189) B1964189
theorem B1768241 : Blo 1160639 1768241 := bstep (se 2 (by rfl) ⟨663090, by rfl⟩ : syracuseStep 1768241 = 1326181) B1326181
theorem B2620241 : Blo 1160639 2620241 := bstep (se 2 (by rfl) ⟨982590, by rfl⟩ : syracuseStep 2620241 = 1965181) B1965181
theorem B2620259 : Blo 1160639 2620259 := bstep (se 1 (by rfl) ⟨1965194, by rfl⟩ : syracuseStep 2620259 = 3930389) B3930389
theorem B3144557 : Blo 1160639 3144557 := bstep (se 3 (by rfl) ⟨589604, by rfl⟩ : syracuseStep 3144557 = 1179209) B1179209
theorem B1964945 : Blo 1160639 1964945 := bstep (se 2 (by rfl) ⟨736854, by rfl⟩ : syracuseStep 1964945 = 1473709) B1473709
theorem B2947985 : Blo 1160639 2947985 := bstep (se 2 (by rfl) ⟨1105494, by rfl⟩ : syracuseStep 2947985 = 2210989) B2210989
theorem B1309603 : Blo 1160639 1309603 := bstep (se 1 (by rfl) ⟨982202, by rfl⟩ : syracuseStep 1309603 = 1964405) B1964405
theorem B3308465 : Blo 1160639 3308465 := bstep (se 2 (by rfl) ⟨1240674, by rfl⟩ : syracuseStep 3308465 = 2481349) B2481349
theorem B1473491 : Blo 1160639 1473491 := bstep (se 1 (by rfl) ⟨1105118, by rfl⟩ : syracuseStep 1473491 = 2210237) B2210237
theorem B3144707 : Blo 1160639 3144707 := bstep (se 1 (by rfl) ⟨2358530, by rfl⟩ : syracuseStep 3144707 = 4717061) B4717061
theorem B1965073 : Blo 1160639 1965073 := bstep (se 2 (by rfl) ⟨736902, by rfl⟩ : syracuseStep 1965073 = 1473805) B1473805
theorem B1309747 : Blo 1160639 1309747 := bstep (se 1 (by rfl) ⟨982310, by rfl⟩ : syracuseStep 1309747 = 1964621) B1964621
theorem B1965107 : Blo 1160639 1965107 := bstep (se 1 (by rfl) ⟨1473830, by rfl⟩ : syracuseStep 1965107 = 2947661) B2947661
theorem B6716515 : Blo 1160639 6716515 := bstep (se 1 (by rfl) ⟨5037386, by rfl⟩ : syracuseStep 6716515 = 10074773) B10074773
theorem B2096291 : Blo 1160639 2096291 := bstep (se 1 (by rfl) ⟨1572218, by rfl⟩ : syracuseStep 2096291 = 3144437) B3144437
theorem B5307569 : Blo 1160639 5307569 := bstep (se 2 (by rfl) ⟨1990338, by rfl⟩ : syracuseStep 5307569 = 3980677) B3980677
theorem B1965235 : Blo 1160639 1965235 := bstep (se 1 (by rfl) ⟨1473926, by rfl⟩ : syracuseStep 1965235 = 2947853) B2947853
theorem B1309891 : Blo 1160639 1309891 := bstep (se 1 (by rfl) ⟨982418, by rfl⟩ : syracuseStep 1309891 = 1964837) B1964837
theorem B14908643 : Blo 1160639 14908643 := bstep (se 1 (by rfl) ⟨11181482, by rfl⟩ : syracuseStep 14908643 = 22362965) B22362965
theorem B3145009 : Blo 1160639 3145009 := bstep (se 2 (by rfl) ⟨1179378, by rfl⟩ : syracuseStep 3145009 = 2358757) B2358757
theorem B1310035 : Blo 1160639 1310035 := bstep (se 1 (by rfl) ⟨982526, by rfl⟩ : syracuseStep 1310035 = 1965053) B1965053
theorem B1572305 : Blo 1160639 1572305 := bstep (se 2 (by rfl) ⟨589614, by rfl⟩ : syracuseStep 1572305 = 1179229) B1179229
theorem B1310179 : Blo 1160639 1310179 := bstep (se 1 (by rfl) ⟨982634, by rfl⟩ : syracuseStep 1310179 = 1965269) B1965269
theorem B5963341 : Blo 1160639 5963341 := bstep (se 3 (by rfl) ⟨1118126, by rfl⟩ : syracuseStep 5963341 = 2236253) B2236253
theorem B3309137 : Blo 1160639 3309137 := bstep (se 2 (by rfl) ⟨1240926, by rfl⟩ : syracuseStep 3309137 = 2481853) B2481853
theorem B9928433 : Blo 1160639 9928433 := bstep (se 2 (by rfl) ⟨3723162, by rfl⟩ : syracuseStep 9928433 = 7446325) B7446325
theorem B3145571 : Blo 1160639 3145571 := bstep (se 1 (by rfl) ⟨2359178, by rfl⟩ : syracuseStep 3145571 = 4718357) B4718357
theorem B4718615 : Blo 1160639 4718615 := bstep (se 1 (by rfl) ⟨3538961, by rfl⟩ : syracuseStep 4718615 = 7077923) B7077923
theorem B1179703 : Blo 1160639 1179703 := bstep (se 1 (by rfl) ⟨884777, by rfl⟩ : syracuseStep 1179703 = 1769555) B1769555
theorem B6619229 : Blo 1160639 6619229 := bstep (se 3 (by rfl) ⟨1241105, by rfl⟩ : syracuseStep 6619229 = 2482211) B2482211
theorem B4784429 : Blo 1160639 4784429 := bstep (se 3 (by rfl) ⟨897080, by rfl⟩ : syracuseStep 4784429 = 1794161) B1794161
theorem B2654579 : Blo 1160639 2654579 := bstep (se 1 (by rfl) ⟨1990934, by rfl⟩ : syracuseStep 2654579 = 3981869) B3981869
theorem B3146177 : Blo 1160639 3146177 := bstep (se 2 (by rfl) ⟨1179816, by rfl⟩ : syracuseStep 3146177 = 2359633) B2359633
theorem B2982347 : Blo 1160639 2982347 := bstep (se 1 (by rfl) ⟨2236760, by rfl⟩ : syracuseStep 2982347 = 4473521) B4473521
theorem B2359795 : Blo 1160639 2359795 := bstep (se 1 (by rfl) ⟨1769846, by rfl⟩ : syracuseStep 2359795 = 3539693) B3539693
theorem B1180279 : Blo 1160639 1180279 := bstep (se 1 (by rfl) ⟨885209, by rfl⟩ : syracuseStep 1180279 = 1770419) B1770419
theorem B2687627 : Blo 1160639 2687627 := bstep (se 1 (by rfl) ⟨2015720, by rfl⟩ : syracuseStep 2687627 = 4031441) B4031441
theorem B2360087 : Blo 1160639 2360087 := bstep (se 1 (by rfl) ⟨1770065, by rfl⟩ : syracuseStep 2360087 = 3540131) B3540131
theorem B2360153 : Blo 1160639 2360153 := bstep (se 2 (by rfl) ⟨885057, by rfl⟩ : syracuseStep 2360153 = 1770115) B1770115
theorem B3769523 : Blo 1160639 3769523 := bstep (se 1 (by rfl) ⟨2827142, by rfl⟩ : syracuseStep 3769523 = 5654285) B5654285
theorem B3311027 : Blo 1160639 3311027 := bstep (se 1 (by rfl) ⟨2483270, by rfl⟩ : syracuseStep 3311027 = 4966541) B4966541
theorem B2655755 : Blo 1160639 2655755 := bstep (se 1 (by rfl) ⟨1991816, by rfl⟩ : syracuseStep 2655755 = 3983633) B3983633
theorem B3311255 : Blo 1160639 3311255 := bstep (se 1 (by rfl) ⟨2483441, by rfl⟩ : syracuseStep 3311255 = 4966883) B4966883
theorem B3311563 : Blo 1160639 3311563 := bstep (se 1 (by rfl) ⟨2483672, by rfl⟩ : syracuseStep 3311563 = 4967345) B4967345
theorem B4720691 : Blo 1160639 4720691 := bstep (se 1 (by rfl) ⟨3540518, by rfl⟩ : syracuseStep 4720691 = 7081037) B7081037
theorem B9439307 : Blo 1160639 9439307 := bstep (se 1 (by rfl) ⟨7079480, by rfl⟩ : syracuseStep 9439307 = 14158961) B14158961
theorem B3311837 : Blo 1160639 3311837 := bstep (se 3 (by rfl) ⟨620969, by rfl⟩ : syracuseStep 3311837 = 1241939) B1241939
theorem B16746851 : Blo 1160639 16746851 := bstep (se 1 (by rfl) ⟨12560138, by rfl⟩ : syracuseStep 16746851 = 25120277) B25120277
theorem B25102979 : Blo 1160639 25102979 := bstep (se 1 (by rfl) ⟨18827234, by rfl⟩ : syracuseStep 25102979 = 37654469) B37654469
theorem B7441253 : Blo 1160639 7441253 := bstep (se 4 (by rfl) ⟨697617, by rfl⟩ : syracuseStep 7441253 = 1395235) B1395235
theorem B6720577 : Blo 1160639 6720577 := bstep (se 2 (by rfl) ⟨2520216, by rfl⟩ : syracuseStep 6720577 = 5040433) B5040433
theorem B28314805 : Blo 1160639 28314805 := bstep (se 5 (by rfl) ⟨1327256, by rfl⟩ : syracuseStep 28314805 = 2654513) B2654513
theorem B2788759 : Blo 1160639 2788759 := bstep (se 1 (by rfl) ⟨2091569, by rfl⟩ : syracuseStep 2788759 = 4183139) B4183139
theorem B5312075 : Blo 1160639 5312075 := bstep (se 1 (by rfl) ⟨3984056, by rfl⟩ : syracuseStep 5312075 = 7968113) B7968113
theorem B8949379 : Blo 1160639 8949379 := bstep (se 1 (by rfl) ⟨6712034, by rfl⟩ : syracuseStep 8949379 = 13424069) B13424069
theorem B7966387 : Blo 1160639 7966387 := bstep (se 1 (by rfl) ⟨5974790, by rfl⟩ : syracuseStep 7966387 = 11949581) B11949581
theorem B25170101 : Blo 1160639 25170101 := bstep (se 5 (by rfl) ⟨1179848, by rfl⟩ : syracuseStep 25170101 = 2359697) B2359697
theorem B1741067 : Blo 1160639 1741067 := bstep (se 1 (by rfl) ⟨1305800, by rfl⟩ : syracuseStep 1741067 = 2611601) B2611601
theorem B1741079 : Blo 1160639 1741079 := bstep (se 1 (by rfl) ⟨1305809, by rfl⟩ : syracuseStep 1741079 = 2611619) B2611619
theorem B3313943 : Blo 1160639 3313943 := bstep (se 1 (by rfl) ⟨2485457, by rfl⟩ : syracuseStep 3313943 = 4970915) B4970915
theorem B1741145 : Blo 1160639 1741145 := bstep (se 2 (by rfl) ⟨652929, by rfl⟩ : syracuseStep 1741145 = 1305859) B1305859
theorem B1741259 : Blo 1160639 1741259 := bstep (se 1 (by rfl) ⟨1305944, by rfl⟩ : syracuseStep 1741259 = 2611889) B2611889
theorem B1741271 : Blo 1160639 1741271 := bstep (se 1 (by rfl) ⟨1305953, by rfl⟩ : syracuseStep 1741271 = 2611907) B2611907
theorem B1741337 : Blo 1160639 1741337 := bstep (se 2 (by rfl) ⟨653001, by rfl⟩ : syracuseStep 1741337 = 1306003) B1306003
theorem B1741451 : Blo 1160639 1741451 := bstep (se 1 (by rfl) ⟨1306088, by rfl⟩ : syracuseStep 1741451 = 2612177) B2612177
theorem B1741463 : Blo 1160639 1741463 := bstep (se 1 (by rfl) ⟨1306097, by rfl⟩ : syracuseStep 1741463 = 2612195) B2612195
theorem B1741529 : Blo 1160639 1741529 := bstep (se 2 (by rfl) ⟨653073, by rfl⟩ : syracuseStep 1741529 = 1306147) B1306147
theorem B1741643 : Blo 1160639 1741643 := bstep (se 1 (by rfl) ⟨1306232, by rfl⟩ : syracuseStep 1741643 = 2612465) B2612465
theorem B1741655 : Blo 1160639 1741655 := bstep (se 1 (by rfl) ⟨1306241, by rfl⟩ : syracuseStep 1741655 = 2612483) B2612483
theorem B1741721 : Blo 1160639 1741721 := bstep (se 2 (by rfl) ⟨653145, by rfl⟩ : syracuseStep 1741721 = 1306291) B1306291
theorem B1741835 : Blo 1160639 1741835 := bstep (se 1 (by rfl) ⟨1306376, by rfl⟩ : syracuseStep 1741835 = 2612753) B2612753
theorem B1741847 : Blo 1160639 1741847 := bstep (se 1 (by rfl) ⟨1306385, by rfl⟩ : syracuseStep 1741847 = 2612771) B2612771
theorem B3314753 : Blo 1160639 3314753 := bstep (se 2 (by rfl) ⟨1243032, by rfl⟩ : syracuseStep 3314753 = 2486065) B2486065
theorem B1741913 : Blo 1160639 1741913 := bstep (se 2 (by rfl) ⟨653217, by rfl⟩ : syracuseStep 1741913 = 1306435) B1306435
theorem B1742027 : Blo 1160639 1742027 := bstep (se 1 (by rfl) ⟨1306520, by rfl⟩ : syracuseStep 1742027 = 2613041) B2613041
theorem B13407437 : Blo 1160639 13407437 := bstep (se 3 (by rfl) ⟨2513894, by rfl⟩ : syracuseStep 13407437 = 5027789) B5027789
theorem B1742039 : Blo 1160639 1742039 := bstep (se 1 (by rfl) ⟨1306529, by rfl⟩ : syracuseStep 1742039 = 2613059) B2613059
theorem B1742105 : Blo 1160639 1742105 := bstep (se 2 (by rfl) ⟨653289, by rfl⟩ : syracuseStep 1742105 = 1306579) B1306579
theorem B6624605 : Blo 1160639 6624605 := bstep (se 3 (by rfl) ⟨1242113, by rfl⟩ : syracuseStep 6624605 = 2484227) B2484227
theorem B1742219 : Blo 1160639 1742219 := bstep (se 1 (by rfl) ⟨1306664, by rfl⟩ : syracuseStep 1742219 = 2613329) B2613329
theorem B1742231 : Blo 1160639 1742231 := bstep (se 1 (by rfl) ⟨1306673, by rfl⟩ : syracuseStep 1742231 = 2613347) B2613347
theorem B1742297 : Blo 1160639 1742297 := bstep (se 2 (by rfl) ⟨653361, by rfl⟩ : syracuseStep 1742297 = 1306723) B1306723
theorem B1742411 : Blo 1160639 1742411 := bstep (se 1 (by rfl) ⟨1306808, by rfl⟩ : syracuseStep 1742411 = 2613617) B2613617
theorem B1742423 : Blo 1160639 1742423 := bstep (se 1 (by rfl) ⟨1306817, by rfl⟩ : syracuseStep 1742423 = 2613635) B2613635
theorem B1742489 : Blo 1160639 1742489 := bstep (se 2 (by rfl) ⟨653433, by rfl⟩ : syracuseStep 1742489 = 1306867) B1306867
theorem B1742603 : Blo 1160639 1742603 := bstep (se 1 (by rfl) ⟨1306952, by rfl⟩ : syracuseStep 1742603 = 2613905) B2613905
theorem B10884881 : Blo 1160639 10884881 := bstep (se 2 (by rfl) ⟨4081830, by rfl⟩ : syracuseStep 10884881 = 8163661) B8163661
theorem B1742615 : Blo 1160639 1742615 := bstep (se 1 (by rfl) ⟨1306961, by rfl⟩ : syracuseStep 1742615 = 2613923) B2613923
theorem B8951597 : Blo 1160639 8951597 := bstep (se 3 (by rfl) ⟨1678424, by rfl⟩ : syracuseStep 8951597 = 3356849) B3356849
theorem B1742681 : Blo 1160639 1742681 := bstep (se 2 (by rfl) ⟨653505, by rfl⟩ : syracuseStep 1742681 = 1307011) B1307011
theorem B1742795 : Blo 1160639 1742795 := bstep (se 1 (by rfl) ⟨1307096, by rfl⟩ : syracuseStep 1742795 = 2614193) B2614193
theorem B1742807 : Blo 1160639 1742807 := bstep (se 1 (by rfl) ⟨1307105, by rfl⟩ : syracuseStep 1742807 = 2614211) B2614211
theorem B1742873 : Blo 1160639 1742873 := bstep (se 2 (by rfl) ⟨653577, by rfl⟩ : syracuseStep 1742873 = 1307155) B1307155
theorem B9443459 : Blo 1160639 9443459 := bstep (se 1 (by rfl) ⟨7082594, by rfl⟩ : syracuseStep 9443459 = 14165189) B14165189
theorem B1742987 : Blo 1160639 1742987 := bstep (se 1 (by rfl) ⟨1307240, by rfl⟩ : syracuseStep 1742987 = 2614481) B2614481
theorem B1742999 : Blo 1160639 1742999 := bstep (se 1 (by rfl) ⟨1307249, by rfl⟩ : syracuseStep 1742999 = 2614499) B2614499
theorem B2791603 : Blo 1160639 2791603 := bstep (se 1 (by rfl) ⟨2093702, by rfl⟩ : syracuseStep 2791603 = 4187405) B4187405
theorem B1743065 : Blo 1160639 1743065 := bstep (se 2 (by rfl) ⟨653649, by rfl⟩ : syracuseStep 1743065 = 1307299) B1307299
theorem B1743179 : Blo 1160639 1743179 := bstep (se 1 (by rfl) ⟨1307384, by rfl⟩ : syracuseStep 1743179 = 2614769) B2614769
theorem B1743191 : Blo 1160639 1743191 := bstep (se 1 (by rfl) ⟨1307393, by rfl⟩ : syracuseStep 1743191 = 2614787) B2614787
theorem B1743257 : Blo 1160639 1743257 := bstep (se 2 (by rfl) ⟨653721, by rfl⟩ : syracuseStep 1743257 = 1307443) B1307443
theorem B2234881 : Blo 1160639 2234881 := bstep (se 2 (by rfl) ⟨838080, by rfl⟩ : syracuseStep 2234881 = 1676161) B1676161
theorem B1743371 : Blo 1160639 1743371 := bstep (se 1 (by rfl) ⟨1307528, by rfl⟩ : syracuseStep 1743371 = 2615057) B2615057
theorem B1743383 : Blo 1160639 1743383 := bstep (se 1 (by rfl) ⟨1307537, by rfl⟩ : syracuseStep 1743383 = 2615075) B2615075
theorem B9935405 : Blo 1160639 9935405 := bstep (se 3 (by rfl) ⟨1862888, by rfl⟩ : syracuseStep 9935405 = 3725777) B3725777
theorem B1743449 : Blo 1160639 1743449 := bstep (se 2 (by rfl) ⟨653793, by rfl⟩ : syracuseStep 1743449 = 1307587) B1307587
theorem B3316403 : Blo 1160639 3316403 := bstep (se 1 (by rfl) ⟨2487302, by rfl⟩ : syracuseStep 3316403 = 4974605) B4974605
theorem B1743563 : Blo 1160639 1743563 := bstep (se 1 (by rfl) ⟨1307672, by rfl⟩ : syracuseStep 1743563 = 2615345) B2615345
theorem B3316427 : Blo 1160639 3316427 := bstep (se 1 (by rfl) ⟨2487320, by rfl⟩ : syracuseStep 3316427 = 4974641) B4974641
theorem B1743575 : Blo 1160639 1743575 := bstep (se 1 (by rfl) ⟨1307681, by rfl⟩ : syracuseStep 1743575 = 2615363) B2615363
theorem B1743641 : Blo 1160639 1743641 := bstep (se 2 (by rfl) ⟨653865, by rfl⟩ : syracuseStep 1743641 = 1307731) B1307731
theorem B3873587 : Blo 1160639 3873587 := bstep (se 1 (by rfl) ⟨2905190, by rfl⟩ : syracuseStep 3873587 = 5810381) B5810381
theorem B310057793 : Blo 1160639 310057793 := bstep (se 2 (by rfl) ⟨116271672, by rfl⟩ : syracuseStep 310057793 = 232543345) B232543345
theorem B1743755 : Blo 1160639 1743755 := bstep (se 1 (by rfl) ⟨1307816, by rfl⟩ : syracuseStep 1743755 = 2615633) B2615633
theorem B1743767 : Blo 1160639 1743767 := bstep (se 1 (by rfl) ⟨1307825, by rfl⟩ : syracuseStep 1743767 = 2615651) B2615651
theorem B1743833 : Blo 1160639 1743833 := bstep (se 2 (by rfl) ⟨653937, by rfl⟩ : syracuseStep 1743833 = 1307875) B1307875
theorem B1743947 : Blo 1160639 1743947 := bstep (se 1 (by rfl) ⟨1307960, by rfl⟩ : syracuseStep 1743947 = 2615921) B2615921
theorem B1743959 : Blo 1160639 1743959 := bstep (se 1 (by rfl) ⟨1307969, by rfl⟩ : syracuseStep 1743959 = 2615939) B2615939
theorem B1744025 : Blo 1160639 1744025 := bstep (se 2 (by rfl) ⟨654009, by rfl⟩ : syracuseStep 1744025 = 1308019) B1308019
theorem B1744139 : Blo 1160639 1744139 := bstep (se 1 (by rfl) ⟨1308104, by rfl⟩ : syracuseStep 1744139 = 2616209) B2616209
theorem B1744151 : Blo 1160639 1744151 := bstep (se 1 (by rfl) ⟨1308113, by rfl⟩ : syracuseStep 1744151 = 2616227) B2616227
theorem B1744217 : Blo 1160639 1744217 := bstep (se 2 (by rfl) ⟨654081, by rfl⟩ : syracuseStep 1744217 = 1308163) B1308163
theorem B8068531 : Blo 1160639 8068531 := bstep (se 1 (by rfl) ⟨6051398, by rfl⟩ : syracuseStep 8068531 = 12102797) B12102797
theorem B1744331 : Blo 1160639 1744331 := bstep (se 1 (by rfl) ⟨1308248, by rfl⟩ : syracuseStep 1744331 = 2616497) B2616497
theorem B1744343 : Blo 1160639 1744343 := bstep (se 1 (by rfl) ⟨1308257, by rfl⟩ : syracuseStep 1744343 = 2616515) B2616515
theorem B1744409 : Blo 1160639 1744409 := bstep (se 2 (by rfl) ⟨654153, by rfl⟩ : syracuseStep 1744409 = 1308307) B1308307
theorem B1744523 : Blo 1160639 1744523 := bstep (se 1 (by rfl) ⟨1308392, by rfl⟩ : syracuseStep 1744523 = 2616785) B2616785
theorem B1744535 : Blo 1160639 1744535 := bstep (se 1 (by rfl) ⟨1308401, by rfl⟩ : syracuseStep 1744535 = 2616803) B2616803
theorem B1744601 : Blo 1160639 1744601 := bstep (se 2 (by rfl) ⟨654225, by rfl⟩ : syracuseStep 1744601 = 1308451) B1308451
theorem B1744715 : Blo 1160639 1744715 := bstep (se 1 (by rfl) ⟨1308536, by rfl⟩ : syracuseStep 1744715 = 2617073) B2617073
theorem B1744727 : Blo 1160639 1744727 := bstep (se 1 (by rfl) ⟨1308545, by rfl⟩ : syracuseStep 1744727 = 2617091) B2617091
theorem B6627203 : Blo 1160639 6627203 := bstep (se 1 (by rfl) ⟨4970402, by rfl⟩ : syracuseStep 6627203 = 9940805) B9940805
theorem B1744793 : Blo 1160639 1744793 := bstep (se 2 (by rfl) ⟨654297, by rfl⟩ : syracuseStep 1744793 = 1308595) B1308595
theorem B1744907 : Blo 1160639 1744907 := bstep (se 1 (by rfl) ⟨1308680, by rfl⟩ : syracuseStep 1744907 = 2617361) B2617361
theorem B1744919 : Blo 1160639 1744919 := bstep (se 1 (by rfl) ⟨1308689, by rfl⟩ : syracuseStep 1744919 = 2617379) B2617379
theorem B2203699 : Blo 1160639 2203699 := bstep (se 1 (by rfl) ⟨1652774, by rfl⟩ : syracuseStep 2203699 = 3305549) B3305549
theorem B1744985 : Blo 1160639 1744985 := bstep (se 2 (by rfl) ⟨654369, by rfl⟩ : syracuseStep 1744985 = 1308739) B1308739
theorem B1745099 : Blo 1160639 1745099 := bstep (se 1 (by rfl) ⟨1308824, by rfl⟩ : syracuseStep 1745099 = 2617649) B2617649
theorem B1745111 : Blo 1160639 1745111 := bstep (se 1 (by rfl) ⟨1308833, by rfl⟩ : syracuseStep 1745111 = 2617667) B2617667
theorem B1745177 : Blo 1160639 1745177 := bstep (se 2 (by rfl) ⟨654441, by rfl⟩ : syracuseStep 1745177 = 1308883) B1308883
theorem B1745291 : Blo 1160639 1745291 := bstep (se 1 (by rfl) ⟨1308968, by rfl⟩ : syracuseStep 1745291 = 2617937) B2617937
theorem B1745303 : Blo 1160639 1745303 := bstep (se 1 (by rfl) ⟨1308977, by rfl⟩ : syracuseStep 1745303 = 2617955) B2617955
theorem B1745369 : Blo 1160639 1745369 := bstep (se 2 (by rfl) ⟨654513, by rfl⟩ : syracuseStep 1745369 = 1309027) B1309027
theorem B2204147 : Blo 1160639 2204147 := bstep (se 1 (by rfl) ⟨1653110, by rfl⟩ : syracuseStep 2204147 = 3306221) B3306221
theorem B2794007 : Blo 1160639 2794007 := bstep (se 1 (by rfl) ⟨2095505, by rfl⟩ : syracuseStep 2794007 = 4191011) B4191011
theorem B2204185 : Blo 1160639 2204185 := bstep (se 2 (by rfl) ⟨826569, by rfl⟩ : syracuseStep 2204185 = 1653139) B1653139
theorem B1745483 : Blo 1160639 1745483 := bstep (se 1 (by rfl) ⟨1309112, by rfl⟩ : syracuseStep 1745483 = 2618225) B2618225
theorem B1745495 : Blo 1160639 1745495 := bstep (se 1 (by rfl) ⟨1309121, by rfl⟩ : syracuseStep 1745495 = 2618243) B2618243
theorem B1745561 : Blo 1160639 1745561 := bstep (se 2 (by rfl) ⟨654585, by rfl⟩ : syracuseStep 1745561 = 1309171) B1309171
theorem B1745675 : Blo 1160639 1745675 := bstep (se 1 (by rfl) ⟨1309256, by rfl⟩ : syracuseStep 1745675 = 2618513) B2618513
theorem B1745687 : Blo 1160639 1745687 := bstep (se 1 (by rfl) ⟨1309265, by rfl⟩ : syracuseStep 1745687 = 2618531) B2618531
theorem B1745753 : Blo 1160639 1745753 := bstep (se 2 (by rfl) ⟨654657, by rfl⟩ : syracuseStep 1745753 = 1309315) B1309315
theorem B1745867 : Blo 1160639 1745867 := bstep (se 1 (by rfl) ⟨1309400, by rfl⟩ : syracuseStep 1745867 = 2618801) B2618801
theorem B1745879 : Blo 1160639 1745879 := bstep (se 1 (by rfl) ⟨1309409, by rfl⟩ : syracuseStep 1745879 = 2618819) B2618819
theorem B2204633 : Blo 1160639 2204633 := bstep (se 2 (by rfl) ⟨826737, by rfl⟩ : syracuseStep 2204633 = 1653475) B1653475
theorem B1745945 : Blo 1160639 1745945 := bstep (se 2 (by rfl) ⟨654729, by rfl⟩ : syracuseStep 1745945 = 1309459) B1309459
theorem B1746059 : Blo 1160639 1746059 := bstep (se 1 (by rfl) ⟨1309544, by rfl⟩ : syracuseStep 1746059 = 2619089) B2619089
theorem B1746071 : Blo 1160639 1746071 := bstep (se 1 (by rfl) ⟨1309553, by rfl⟩ : syracuseStep 1746071 = 2619107) B2619107
theorem B1746137 : Blo 1160639 1746137 := bstep (se 2 (by rfl) ⟨654801, by rfl⟩ : syracuseStep 1746137 = 1309603) B1309603
theorem B1746251 : Blo 1160639 1746251 := bstep (se 1 (by rfl) ⟨1309688, by rfl⟩ : syracuseStep 1746251 = 2619377) B2619377
theorem B1746263 : Blo 1160639 1746263 := bstep (se 1 (by rfl) ⟨1309697, by rfl⟩ : syracuseStep 1746263 = 2619395) B2619395
theorem B1746329 : Blo 1160639 1746329 := bstep (se 2 (by rfl) ⟨654873, by rfl⟩ : syracuseStep 1746329 = 1309747) B1309747
theorem B8955353 : Blo 1160639 8955353 := bstep (se 2 (by rfl) ⟨3358257, by rfl⟩ : syracuseStep 8955353 = 6716515) B6716515
theorem B1746443 : Blo 1160639 1746443 := bstep (se 1 (by rfl) ⟨1309832, by rfl⟩ : syracuseStep 1746443 = 2619665) B2619665
theorem B1746455 : Blo 1160639 1746455 := bstep (se 1 (by rfl) ⟨1309841, by rfl⟩ : syracuseStep 1746455 = 2619683) B2619683
theorem B1746521 : Blo 1160639 1746521 := bstep (se 2 (by rfl) ⟨654945, by rfl⟩ : syracuseStep 1746521 = 1309891) B1309891
theorem B2205377 : Blo 1160639 2205377 := bstep (se 2 (by rfl) ⟨827016, by rfl⟩ : syracuseStep 2205377 = 1654033) B1654033
theorem B1746635 : Blo 1160639 1746635 := bstep (se 1 (by rfl) ⟨1309976, by rfl⟩ : syracuseStep 1746635 = 2619953) B2619953
theorem B1746647 : Blo 1160639 1746647 := bstep (se 1 (by rfl) ⟨1309985, by rfl⟩ : syracuseStep 1746647 = 2619971) B2619971
theorem B1746713 : Blo 1160639 1746713 := bstep (se 2 (by rfl) ⟨655017, by rfl⟩ : syracuseStep 1746713 = 1310035) B1310035
theorem B1746827 : Blo 1160639 1746827 := bstep (se 1 (by rfl) ⟨1310120, by rfl⟩ : syracuseStep 1746827 = 2620241) B2620241
theorem B1746839 : Blo 1160639 1746839 := bstep (se 1 (by rfl) ⟨1310129, by rfl⟩ : syracuseStep 1746839 = 2620259) B2620259
theorem B2205643 : Blo 1160639 2205643 := bstep (se 1 (by rfl) ⟨1654232, by rfl⟩ : syracuseStep 2205643 = 3308465) B3308465
theorem B1746905 : Blo 1160639 1746905 := bstep (se 2 (by rfl) ⟨655089, by rfl⟩ : syracuseStep 1746905 = 1310179) B1310179
theorem B9939095 : Blo 1160639 9939095 := bstep (se 1 (by rfl) ⟨7454321, by rfl⟩ : syracuseStep 9939095 = 14908643) B14908643
theorem B2206091 : Blo 1160639 2206091 := bstep (se 1 (by rfl) ⟨1654568, by rfl⟩ : syracuseStep 2206091 = 3309137) B3309137
theorem B2206273 : Blo 1160639 2206273 := bstep (se 2 (by rfl) ⟨827352, by rfl⟩ : syracuseStep 2206273 = 1654705) B1654705
theorem B28289893 : Blo 1160639 28289893 := bstep (se 4 (by rfl) ⟨2652177, by rfl⟩ : syracuseStep 28289893 = 5304355) B5304355
theorem B2206615 : Blo 1160639 2206615 := bstep (se 1 (by rfl) ⟨1654961, by rfl⟩ : syracuseStep 2206615 = 3309923) B3309923
theorem B2796439 : Blo 1160639 2796439 := bstep (se 1 (by rfl) ⟨2097329, by rfl⟩ : syracuseStep 2796439 = 4194659) B4194659
theorem B56503331 : Blo 1160639 56503331 := bstep (se 1 (by rfl) ⟨42377498, by rfl⟩ : syracuseStep 56503331 = 84754997) B84754997
theorem B2206835 : Blo 1160639 2206835 := bstep (se 1 (by rfl) ⟨1655126, by rfl⟩ : syracuseStep 2206835 = 3310253) B3310253
theorem B2207063 : Blo 1160639 2207063 := bstep (se 1 (by rfl) ⟨1655297, by rfl⟩ : syracuseStep 2207063 = 3310595) B3310595
theorem B2207321 : Blo 1160639 2207321 := bstep (se 2 (by rfl) ⟨827745, by rfl⟩ : syracuseStep 2207321 = 1655491) B1655491
theorem B7548547 : Blo 1160639 7548547 := bstep (se 1 (by rfl) ⟨5661410, by rfl⟩ : syracuseStep 7548547 = 11322821) B11322821
theorem B5582515 : Blo 1160639 5582515 := bstep (se 1 (by rfl) ⟨4186886, by rfl⟩ : syracuseStep 5582515 = 8373773) B8373773
theorem B5877521 : Blo 1160639 5877521 := bstep (se 2 (by rfl) ⟨2204070, by rfl⟩ : syracuseStep 5877521 = 4408141) B4408141
theorem B5877683 : Blo 1160639 5877683 := bstep (se 1 (by rfl) ⟨4408262, by rfl⟩ : syracuseStep 5877683 = 8816525) B8816525
theorem B2207731 : Blo 1160639 2207731 := bstep (se 1 (by rfl) ⟨1655798, by rfl⟩ : syracuseStep 2207731 = 3311597) B3311597
theorem B2240627 : Blo 1160639 2240627 := bstep (se 1 (by rfl) ⟨1680470, by rfl⟩ : syracuseStep 2240627 = 3360941) B3360941
theorem B3354817 : Blo 1160639 3354817 := bstep (se 2 (by rfl) ⟨1258056, by rfl⟩ : syracuseStep 3354817 = 2516113) B2516113
theorem B2240947 : Blo 1160639 2240947 := bstep (se 1 (by rfl) ⟨1680710, by rfl⟩ : syracuseStep 2240947 = 3361421) B3361421
theorem B2208217 : Blo 1160639 2208217 := bstep (se 2 (by rfl) ⟨828081, by rfl⟩ : syracuseStep 2208217 = 1656163) B1656163
theorem B6795841 : Blo 1160639 6795841 := bstep (se 2 (by rfl) ⟨2548440, by rfl⟩ : syracuseStep 6795841 = 5096881) B5096881
theorem B43037381 : Blo 1160639 43037381 := bstep (se 4 (by rfl) ⟨4034754, by rfl⟩ : syracuseStep 43037381 = 8069509) B8069509
theorem B2208779 : Blo 1160639 2208779 := bstep (se 1 (by rfl) ⟨1656584, by rfl⟩ : syracuseStep 2208779 = 3313169) B3313169
theorem B2208961 : Blo 1160639 2208961 := bstep (se 2 (by rfl) ⟨828360, by rfl⟩ : syracuseStep 2208961 = 1656721) B1656721
theorem B4961483 : Blo 1160639 4961483 := bstep (se 1 (by rfl) ⟨3721112, by rfl⟩ : syracuseStep 4961483 = 7442225) B7442225
theorem B14890189 : Blo 1160639 14890189 := bstep (se 3 (by rfl) ⟨2791910, by rfl⟩ : syracuseStep 14890189 = 5583821) B5583821
theorem B1160651 : Blo 1160639 1160651 := bstep (se 1 (by rfl) ⟨870488, by rfl⟩ : syracuseStep 1160651 = 1740977) B1740977
theorem B1160663 : Blo 1160639 1160663 := bstep (se 1 (by rfl) ⟨870497, by rfl⟩ : syracuseStep 1160663 = 1740995) B1740995
theorem B1160683 : Blo 1160639 1160683 := bstep (se 1 (by rfl) ⟨870512, by rfl⟩ : syracuseStep 1160683 = 1741025) B1741025
theorem B1160695 : Blo 1160639 1160695 := bstep (se 1 (by rfl) ⟨870521, by rfl⟩ : syracuseStep 1160695 = 1741043) B1741043
theorem B1160715 : Blo 1160639 1160715 := bstep (se 1 (by rfl) ⟨870536, by rfl⟩ : syracuseStep 1160715 = 1741073) B1741073
theorem B1160727 : Blo 1160639 1160727 := bstep (se 1 (by rfl) ⟨870545, by rfl⟩ : syracuseStep 1160727 = 1741091) B1741091
theorem B1160747 : Blo 1160639 1160747 := bstep (se 1 (by rfl) ⟨870560, by rfl⟩ : syracuseStep 1160747 = 1741121) B1741121
theorem B1160759 : Blo 1160639 1160759 := bstep (se 1 (by rfl) ⟨870569, by rfl⟩ : syracuseStep 1160759 = 1741139) B1741139
theorem B1160779 : Blo 1160639 1160779 := bstep (se 1 (by rfl) ⟨870584, by rfl⟩ : syracuseStep 1160779 = 1741169) B1741169
theorem B1160791 : Blo 1160639 1160791 := bstep (se 1 (by rfl) ⟨870593, by rfl⟩ : syracuseStep 1160791 = 1741187) B1741187
theorem B1160811 : Blo 1160639 1160811 := bstep (se 1 (by rfl) ⟨870608, by rfl⟩ : syracuseStep 1160811 = 1741217) B1741217
theorem B1160823 : Blo 1160639 1160823 := bstep (se 1 (by rfl) ⟨870617, by rfl⟩ : syracuseStep 1160823 = 1741235) B1741235
theorem B1160843 : Blo 1160639 1160843 := bstep (se 1 (by rfl) ⟨870632, by rfl⟩ : syracuseStep 1160843 = 1741265) B1741265
theorem B1160855 : Blo 1160639 1160855 := bstep (se 1 (by rfl) ⟨870641, by rfl⟩ : syracuseStep 1160855 = 1741283) B1741283
theorem B1160875 : Blo 1160639 1160875 := bstep (se 1 (by rfl) ⟨870656, by rfl⟩ : syracuseStep 1160875 = 1741313) B1741313
theorem B1160887 : Blo 1160639 1160887 := bstep (se 1 (by rfl) ⟨870665, by rfl⟩ : syracuseStep 1160887 = 1741331) B1741331
theorem B1160907 : Blo 1160639 1160907 := bstep (se 1 (by rfl) ⟨870680, by rfl⟩ : syracuseStep 1160907 = 1741361) B1741361
theorem B1160919 : Blo 1160639 1160919 := bstep (se 1 (by rfl) ⟨870689, by rfl⟩ : syracuseStep 1160919 = 1741379) B1741379
theorem B1160939 : Blo 1160639 1160939 := bstep (se 1 (by rfl) ⟨870704, by rfl⟩ : syracuseStep 1160939 = 1741409) B1741409
theorem B1160951 : Blo 1160639 1160951 := bstep (se 1 (by rfl) ⟨870713, by rfl⟩ : syracuseStep 1160951 = 1741427) B1741427
theorem B1160971 : Blo 1160639 1160971 := bstep (se 1 (by rfl) ⟨870728, by rfl⟩ : syracuseStep 1160971 = 1741457) B1741457
theorem B1160983 : Blo 1160639 1160983 := bstep (se 1 (by rfl) ⟨870737, by rfl⟩ : syracuseStep 1160983 = 1741475) B1741475
theorem B1161003 : Blo 1160639 1161003 := bstep (se 1 (by rfl) ⟨870752, by rfl⟩ : syracuseStep 1161003 = 1741505) B1741505
theorem B1161015 : Blo 1160639 1161015 := bstep (se 1 (by rfl) ⟨870761, by rfl⟩ : syracuseStep 1161015 = 1741523) B1741523
theorem B1161035 : Blo 1160639 1161035 := bstep (se 1 (by rfl) ⟨870776, by rfl⟩ : syracuseStep 1161035 = 1741553) B1741553
theorem B5879627 : Blo 1160639 5879627 := bstep (se 1 (by rfl) ⟨4409720, by rfl⟩ : syracuseStep 5879627 = 8819441) B8819441
theorem B1161047 : Blo 1160639 1161047 := bstep (se 1 (by rfl) ⟨870785, by rfl⟩ : syracuseStep 1161047 = 1741571) B1741571
theorem B1161067 : Blo 1160639 1161067 := bstep (se 1 (by rfl) ⟨870800, by rfl⟩ : syracuseStep 1161067 = 1741601) B1741601
theorem B1161079 : Blo 1160639 1161079 := bstep (se 1 (by rfl) ⟨870809, by rfl⟩ : syracuseStep 1161079 = 1741619) B1741619
theorem B1161099 : Blo 1160639 1161099 := bstep (se 1 (by rfl) ⟨870824, by rfl⟩ : syracuseStep 1161099 = 1741649) B1741649
theorem B2209675 : Blo 1160639 2209675 := bstep (se 1 (by rfl) ⟨1657256, by rfl⟩ : syracuseStep 2209675 = 3314513) B3314513
theorem B1161111 : Blo 1160639 1161111 := bstep (se 1 (by rfl) ⟨870833, by rfl⟩ : syracuseStep 1161111 = 1741667) B1741667
theorem B1161131 : Blo 1160639 1161131 := bstep (se 1 (by rfl) ⟨870848, by rfl⟩ : syracuseStep 1161131 = 1741697) B1741697
theorem B1161143 : Blo 1160639 1161143 := bstep (se 1 (by rfl) ⟨870857, by rfl⟩ : syracuseStep 1161143 = 1741715) B1741715
theorem B1161163 : Blo 1160639 1161163 := bstep (se 1 (by rfl) ⟨870872, by rfl⟩ : syracuseStep 1161163 = 1741745) B1741745
theorem B1161175 : Blo 1160639 1161175 := bstep (se 1 (by rfl) ⟨870881, by rfl⟩ : syracuseStep 1161175 = 1741763) B1741763
theorem B2209751 : Blo 1160639 2209751 := bstep (se 1 (by rfl) ⟨1657313, by rfl⟩ : syracuseStep 2209751 = 3314627) B3314627
theorem B1161195 : Blo 1160639 1161195 := bstep (se 1 (by rfl) ⟨870896, by rfl⟩ : syracuseStep 1161195 = 1741793) B1741793
theorem B1161207 : Blo 1160639 1161207 := bstep (se 1 (by rfl) ⟨870905, by rfl⟩ : syracuseStep 1161207 = 1741811) B1741811
theorem B1161227 : Blo 1160639 1161227 := bstep (se 1 (by rfl) ⟨870920, by rfl⟩ : syracuseStep 1161227 = 1741841) B1741841
theorem B1161239 : Blo 1160639 1161239 := bstep (se 1 (by rfl) ⟨870929, by rfl⟩ : syracuseStep 1161239 = 1741859) B1741859
theorem B1161259 : Blo 1160639 1161259 := bstep (se 1 (by rfl) ⟨870944, by rfl⟩ : syracuseStep 1161259 = 1741889) B1741889
theorem B1161271 : Blo 1160639 1161271 := bstep (se 1 (by rfl) ⟨870953, by rfl⟩ : syracuseStep 1161271 = 1741907) B1741907
theorem B1161291 : Blo 1160639 1161291 := bstep (se 1 (by rfl) ⟨870968, by rfl⟩ : syracuseStep 1161291 = 1741937) B1741937
theorem B1161303 : Blo 1160639 1161303 := bstep (se 1 (by rfl) ⟨870977, by rfl⟩ : syracuseStep 1161303 = 1741955) B1741955
theorem B1161323 : Blo 1160639 1161323 := bstep (se 1 (by rfl) ⟨870992, by rfl⟩ : syracuseStep 1161323 = 1741985) B1741985
theorem B1161335 : Blo 1160639 1161335 := bstep (se 1 (by rfl) ⟨871001, by rfl⟩ : syracuseStep 1161335 = 1742003) B1742003
theorem B1161355 : Blo 1160639 1161355 := bstep (se 1 (by rfl) ⟨871016, by rfl⟩ : syracuseStep 1161355 = 1742033) B1742033
theorem B1161367 : Blo 1160639 1161367 := bstep (se 1 (by rfl) ⟨871025, by rfl⟩ : syracuseStep 1161367 = 1742051) B1742051
theorem B1161387 : Blo 1160639 1161387 := bstep (se 1 (by rfl) ⟨871040, by rfl⟩ : syracuseStep 1161387 = 1742081) B1742081
theorem B1161399 : Blo 1160639 1161399 := bstep (se 1 (by rfl) ⟨871049, by rfl⟩ : syracuseStep 1161399 = 1742099) B1742099
theorem B1161419 : Blo 1160639 1161419 := bstep (se 1 (by rfl) ⟨871064, by rfl⟩ : syracuseStep 1161419 = 1742129) B1742129
theorem B1161431 : Blo 1160639 1161431 := bstep (se 1 (by rfl) ⟨871073, by rfl⟩ : syracuseStep 1161431 = 1742147) B1742147
theorem B1161451 : Blo 1160639 1161451 := bstep (se 1 (by rfl) ⟨871088, by rfl⟩ : syracuseStep 1161451 = 1742177) B1742177
theorem B1161463 : Blo 1160639 1161463 := bstep (se 1 (by rfl) ⟨871097, by rfl⟩ : syracuseStep 1161463 = 1742195) B1742195
theorem B1161483 : Blo 1160639 1161483 := bstep (se 1 (by rfl) ⟨871112, by rfl⟩ : syracuseStep 1161483 = 1742225) B1742225
theorem B1161495 : Blo 1160639 1161495 := bstep (se 1 (by rfl) ⟨871121, by rfl⟩ : syracuseStep 1161495 = 1742243) B1742243
theorem B1161515 : Blo 1160639 1161515 := bstep (se 1 (by rfl) ⟨871136, by rfl⟩ : syracuseStep 1161515 = 1742273) B1742273
theorem B1161527 : Blo 1160639 1161527 := bstep (se 1 (by rfl) ⟨871145, by rfl⟩ : syracuseStep 1161527 = 1742291) B1742291
theorem B1161547 : Blo 1160639 1161547 := bstep (se 1 (by rfl) ⟨871160, by rfl⟩ : syracuseStep 1161547 = 1742321) B1742321
theorem B1161559 : Blo 1160639 1161559 := bstep (se 1 (by rfl) ⟨871169, by rfl⟩ : syracuseStep 1161559 = 1742339) B1742339
theorem B1161579 : Blo 1160639 1161579 := bstep (se 1 (by rfl) ⟨871184, by rfl⟩ : syracuseStep 1161579 = 1742369) B1742369
theorem B1161591 : Blo 1160639 1161591 := bstep (se 1 (by rfl) ⟨871193, by rfl⟩ : syracuseStep 1161591 = 1742387) B1742387
theorem B1161611 : Blo 1160639 1161611 := bstep (se 1 (by rfl) ⟨871208, by rfl⟩ : syracuseStep 1161611 = 1742417) B1742417
theorem B1161623 : Blo 1160639 1161623 := bstep (se 1 (by rfl) ⟨871217, by rfl⟩ : syracuseStep 1161623 = 1742435) B1742435
theorem B1161643 : Blo 1160639 1161643 := bstep (se 1 (by rfl) ⟨871232, by rfl⟩ : syracuseStep 1161643 = 1742465) B1742465
theorem B1161655 : Blo 1160639 1161655 := bstep (se 1 (by rfl) ⟨871241, by rfl⟩ : syracuseStep 1161655 = 1742483) B1742483
theorem B1161675 : Blo 1160639 1161675 := bstep (se 1 (by rfl) ⟨871256, by rfl⟩ : syracuseStep 1161675 = 1742513) B1742513
theorem B1161687 : Blo 1160639 1161687 := bstep (se 1 (by rfl) ⟨871265, by rfl⟩ : syracuseStep 1161687 = 1742531) B1742531
theorem B1161707 : Blo 1160639 1161707 := bstep (se 1 (by rfl) ⟨871280, by rfl⟩ : syracuseStep 1161707 = 1742561) B1742561
theorem B1161719 : Blo 1160639 1161719 := bstep (se 1 (by rfl) ⟨871289, by rfl⟩ : syracuseStep 1161719 = 1742579) B1742579
theorem B1161739 : Blo 1160639 1161739 := bstep (se 1 (by rfl) ⟨871304, by rfl⟩ : syracuseStep 1161739 = 1742609) B1742609
theorem B1161751 : Blo 1160639 1161751 := bstep (se 1 (by rfl) ⟨871313, by rfl⟩ : syracuseStep 1161751 = 1742627) B1742627
theorem B1161771 : Blo 1160639 1161771 := bstep (se 1 (by rfl) ⟨871328, by rfl⟩ : syracuseStep 1161771 = 1742657) B1742657
theorem B1161783 : Blo 1160639 1161783 := bstep (se 1 (by rfl) ⟨871337, by rfl⟩ : syracuseStep 1161783 = 1742675) B1742675
theorem B1161803 : Blo 1160639 1161803 := bstep (se 1 (by rfl) ⟨871352, by rfl⟩ : syracuseStep 1161803 = 1742705) B1742705
theorem B1161815 : Blo 1160639 1161815 := bstep (se 1 (by rfl) ⟨871361, by rfl⟩ : syracuseStep 1161815 = 1742723) B1742723
theorem B1161835 : Blo 1160639 1161835 := bstep (se 1 (by rfl) ⟨871376, by rfl⟩ : syracuseStep 1161835 = 1742753) B1742753
theorem B2210419 : Blo 1160639 2210419 := bstep (se 1 (by rfl) ⟨1657814, by rfl⟩ : syracuseStep 2210419 = 3315629) B3315629
theorem B1161847 : Blo 1160639 1161847 := bstep (se 1 (by rfl) ⟨871385, by rfl⟩ : syracuseStep 1161847 = 1742771) B1742771
theorem B1161867 : Blo 1160639 1161867 := bstep (se 1 (by rfl) ⟨871400, by rfl⟩ : syracuseStep 1161867 = 1742801) B1742801
theorem B1161879 : Blo 1160639 1161879 := bstep (se 1 (by rfl) ⟨871409, by rfl⟩ : syracuseStep 1161879 = 1742819) B1742819
theorem B1161899 : Blo 1160639 1161899 := bstep (se 1 (by rfl) ⟨871424, by rfl⟩ : syracuseStep 1161899 = 1742849) B1742849
theorem B1161911 : Blo 1160639 1161911 := bstep (se 1 (by rfl) ⟨871433, by rfl⟩ : syracuseStep 1161911 = 1742867) B1742867
theorem B1161931 : Blo 1160639 1161931 := bstep (se 1 (by rfl) ⟨871448, by rfl⟩ : syracuseStep 1161931 = 1742897) B1742897
theorem B9550541 : Blo 1160639 9550541 := bstep (se 3 (by rfl) ⟨1790726, by rfl⟩ : syracuseStep 9550541 = 3581453) B3581453
theorem B1653463 : Blo 1160639 1653463 := bstep (se 1 (by rfl) ⟨1240097, by rfl⟩ : syracuseStep 1653463 = 2480195) B2480195
theorem B1161943 : Blo 1160639 1161943 := bstep (se 1 (by rfl) ⟨871457, by rfl⟩ : syracuseStep 1161943 = 1742915) B1742915
theorem B1161963 : Blo 1160639 1161963 := bstep (se 1 (by rfl) ⟨871472, by rfl⟩ : syracuseStep 1161963 = 1742945) B1742945
theorem B1161975 : Blo 1160639 1161975 := bstep (se 1 (by rfl) ⟨871481, by rfl⟩ : syracuseStep 1161975 = 1742963) B1742963
theorem B1161995 : Blo 1160639 1161995 := bstep (se 1 (by rfl) ⟨871496, by rfl⟩ : syracuseStep 1161995 = 1742993) B1742993
theorem B1162007 : Blo 1160639 1162007 := bstep (se 1 (by rfl) ⟨871505, by rfl⟩ : syracuseStep 1162007 = 1743011) B1743011
theorem B1162027 : Blo 1160639 1162027 := bstep (se 1 (by rfl) ⟨871520, by rfl⟩ : syracuseStep 1162027 = 1743041) B1743041
theorem B4963123 : Blo 1160639 4963123 := bstep (se 1 (by rfl) ⟨3722342, by rfl⟩ : syracuseStep 4963123 = 7444685) B7444685
theorem B1162039 : Blo 1160639 1162039 := bstep (se 1 (by rfl) ⟨871529, by rfl⟩ : syracuseStep 1162039 = 1743059) B1743059
theorem B1162059 : Blo 1160639 1162059 := bstep (se 1 (by rfl) ⟨871544, by rfl⟩ : syracuseStep 1162059 = 1743089) B1743089
theorem B1162071 : Blo 1160639 1162071 := bstep (se 1 (by rfl) ⟨871553, by rfl⟩ : syracuseStep 1162071 = 1743107) B1743107
theorem B2210647 : Blo 1160639 2210647 := bstep (se 1 (by rfl) ⟨1657985, by rfl⟩ : syracuseStep 2210647 = 3315971) B3315971
theorem B1162091 : Blo 1160639 1162091 := bstep (se 1 (by rfl) ⟨871568, by rfl⟩ : syracuseStep 1162091 = 1743137) B1743137
theorem B1162103 : Blo 1160639 1162103 := bstep (se 1 (by rfl) ⟨871577, by rfl⟩ : syracuseStep 1162103 = 1743155) B1743155
theorem B1162123 : Blo 1160639 1162123 := bstep (se 1 (by rfl) ⟨871592, by rfl⟩ : syracuseStep 1162123 = 1743185) B1743185
theorem B1162135 : Blo 1160639 1162135 := bstep (se 1 (by rfl) ⟨871601, by rfl⟩ : syracuseStep 1162135 = 1743203) B1743203
theorem B1162155 : Blo 1160639 1162155 := bstep (se 1 (by rfl) ⟨871616, by rfl⟩ : syracuseStep 1162155 = 1743233) B1743233
theorem B11189171 : Blo 1160639 11189171 := bstep (se 1 (by rfl) ⟨8391878, by rfl⟩ : syracuseStep 11189171 = 16783757) B16783757
theorem B1162167 : Blo 1160639 1162167 := bstep (se 1 (by rfl) ⟨871625, by rfl⟩ : syracuseStep 1162167 = 1743251) B1743251
theorem B2210753 : Blo 1160639 2210753 := bstep (se 2 (by rfl) ⟨829032, by rfl⟩ : syracuseStep 2210753 = 1658065) B1658065
theorem B1162187 : Blo 1160639 1162187 := bstep (se 1 (by rfl) ⟨871640, by rfl⟩ : syracuseStep 1162187 = 1743281) B1743281
theorem B1162199 : Blo 1160639 1162199 := bstep (se 1 (by rfl) ⟨871649, by rfl⟩ : syracuseStep 1162199 = 1743299) B1743299
theorem B1162219 : Blo 1160639 1162219 := bstep (se 1 (by rfl) ⟨871664, by rfl⟩ : syracuseStep 1162219 = 1743329) B1743329
theorem B1162231 : Blo 1160639 1162231 := bstep (se 1 (by rfl) ⟨871673, by rfl⟩ : syracuseStep 1162231 = 1743347) B1743347
theorem B1162251 : Blo 1160639 1162251 := bstep (se 1 (by rfl) ⟨871688, by rfl⟩ : syracuseStep 1162251 = 1743377) B1743377
theorem B1162263 : Blo 1160639 1162263 := bstep (se 1 (by rfl) ⟨871697, by rfl⟩ : syracuseStep 1162263 = 1743395) B1743395
theorem B1162283 : Blo 1160639 1162283 := bstep (se 1 (by rfl) ⟨871712, by rfl⟩ : syracuseStep 1162283 = 1743425) B1743425
theorem B1162295 : Blo 1160639 1162295 := bstep (se 1 (by rfl) ⟨871721, by rfl⟩ : syracuseStep 1162295 = 1743443) B1743443
theorem B1162315 : Blo 1160639 1162315 := bstep (se 1 (by rfl) ⟨871736, by rfl⟩ : syracuseStep 1162315 = 1743473) B1743473
theorem B1162327 : Blo 1160639 1162327 := bstep (se 1 (by rfl) ⟨871745, by rfl⟩ : syracuseStep 1162327 = 1743491) B1743491
theorem B2210905 : Blo 1160639 2210905 := bstep (se 2 (by rfl) ⟨829089, by rfl⟩ : syracuseStep 2210905 = 1658179) B1658179
theorem B1162347 : Blo 1160639 1162347 := bstep (se 1 (by rfl) ⟨871760, by rfl⟩ : syracuseStep 1162347 = 1743521) B1743521
theorem B1162359 : Blo 1160639 1162359 := bstep (se 1 (by rfl) ⟨871769, by rfl⟩ : syracuseStep 1162359 = 1743539) B1743539
theorem B1162379 : Blo 1160639 1162379 := bstep (se 1 (by rfl) ⟨871784, by rfl⟩ : syracuseStep 1162379 = 1743569) B1743569
theorem B3718295 : Blo 1160639 3718295 := bstep (se 1 (by rfl) ⟨2788721, by rfl⟩ : syracuseStep 3718295 = 5577443) B5577443
theorem B1162391 : Blo 1160639 1162391 := bstep (se 1 (by rfl) ⟨871793, by rfl⟩ : syracuseStep 1162391 = 1743587) B1743587
theorem B1162411 : Blo 1160639 1162411 := bstep (se 1 (by rfl) ⟨871808, by rfl⟩ : syracuseStep 1162411 = 1743617) B1743617
theorem B1162423 : Blo 1160639 1162423 := bstep (se 1 (by rfl) ⟨871817, by rfl⟩ : syracuseStep 1162423 = 1743635) B1743635
theorem B4472011 : Blo 1160639 4472011 := bstep (se 1 (by rfl) ⟨3354008, by rfl⟩ : syracuseStep 4472011 = 6708017) B6708017
theorem B1162443 : Blo 1160639 1162443 := bstep (se 1 (by rfl) ⟨871832, by rfl⟩ : syracuseStep 1162443 = 1743665) B1743665
theorem B1162455 : Blo 1160639 1162455 := bstep (se 1 (by rfl) ⟨871841, by rfl⟩ : syracuseStep 1162455 = 1743683) B1743683
theorem B1162475 : Blo 1160639 1162475 := bstep (se 1 (by rfl) ⟨871856, by rfl⟩ : syracuseStep 1162475 = 1743713) B1743713
theorem B1162487 : Blo 1160639 1162487 := bstep (se 1 (by rfl) ⟨871865, by rfl⟩ : syracuseStep 1162487 = 1743731) B1743731
theorem B1162507 : Blo 1160639 1162507 := bstep (se 1 (by rfl) ⟨871880, by rfl⟩ : syracuseStep 1162507 = 1743761) B1743761
theorem B1162519 : Blo 1160639 1162519 := bstep (se 1 (by rfl) ⟨871889, by rfl⟩ : syracuseStep 1162519 = 1743779) B1743779
theorem B1162539 : Blo 1160639 1162539 := bstep (se 1 (by rfl) ⟨871904, by rfl⟩ : syracuseStep 1162539 = 1743809) B1743809
theorem B1162551 : Blo 1160639 1162551 := bstep (se 1 (by rfl) ⟨871913, by rfl⟩ : syracuseStep 1162551 = 1743827) B1743827
theorem B1162571 : Blo 1160639 1162571 := bstep (se 1 (by rfl) ⟨871928, by rfl⟩ : syracuseStep 1162571 = 1743857) B1743857
theorem B1162583 : Blo 1160639 1162583 := bstep (se 1 (by rfl) ⟨871937, by rfl⟩ : syracuseStep 1162583 = 1743875) B1743875
theorem B1162603 : Blo 1160639 1162603 := bstep (se 1 (by rfl) ⟨871952, by rfl⟩ : syracuseStep 1162603 = 1743905) B1743905
theorem B1162615 : Blo 1160639 1162615 := bstep (se 1 (by rfl) ⟨871961, by rfl⟩ : syracuseStep 1162615 = 1743923) B1743923
theorem B1162635 : Blo 1160639 1162635 := bstep (se 1 (by rfl) ⟨871976, by rfl⟩ : syracuseStep 1162635 = 1743953) B1743953
theorem B1162647 : Blo 1160639 1162647 := bstep (se 1 (by rfl) ⟨871985, by rfl⟩ : syracuseStep 1162647 = 1743971) B1743971
theorem B1162667 : Blo 1160639 1162667 := bstep (se 1 (by rfl) ⟨872000, by rfl⟩ : syracuseStep 1162667 = 1744001) B1744001
theorem B1162679 : Blo 1160639 1162679 := bstep (se 1 (by rfl) ⟨872009, by rfl⟩ : syracuseStep 1162679 = 1744019) B1744019
theorem B1162699 : Blo 1160639 1162699 := bstep (se 1 (by rfl) ⟨872024, by rfl⟩ : syracuseStep 1162699 = 1744049) B1744049
theorem B1162711 : Blo 1160639 1162711 := bstep (se 1 (by rfl) ⟨872033, by rfl⟩ : syracuseStep 1162711 = 1744067) B1744067
theorem B1162731 : Blo 1160639 1162731 := bstep (se 1 (by rfl) ⟨872048, by rfl⟩ : syracuseStep 1162731 = 1744097) B1744097
theorem B1162743 : Blo 1160639 1162743 := bstep (se 1 (by rfl) ⟨872057, by rfl⟩ : syracuseStep 1162743 = 1744115) B1744115
theorem B1162763 : Blo 1160639 1162763 := bstep (se 1 (by rfl) ⟨872072, by rfl⟩ : syracuseStep 1162763 = 1744145) B1744145
theorem B1162775 : Blo 1160639 1162775 := bstep (se 1 (by rfl) ⟨872081, by rfl⟩ : syracuseStep 1162775 = 1744163) B1744163
theorem B1162795 : Blo 1160639 1162795 := bstep (se 1 (by rfl) ⟨872096, by rfl⟩ : syracuseStep 1162795 = 1744193) B1744193
theorem B1162807 : Blo 1160639 1162807 := bstep (se 1 (by rfl) ⟨872105, by rfl⟩ : syracuseStep 1162807 = 1744211) B1744211
theorem B5881409 : Blo 1160639 5881409 := bstep (se 2 (by rfl) ⟨2205528, by rfl⟩ : syracuseStep 5881409 = 4411057) B4411057
theorem B1162827 : Blo 1160639 1162827 := bstep (se 1 (by rfl) ⟨872120, by rfl⟩ : syracuseStep 1162827 = 1744241) B1744241
theorem B1162839 : Blo 1160639 1162839 := bstep (se 1 (by rfl) ⟨872129, by rfl⟩ : syracuseStep 1162839 = 1744259) B1744259
theorem B1162859 : Blo 1160639 1162859 := bstep (se 1 (by rfl) ⟨872144, by rfl⟩ : syracuseStep 1162859 = 1744289) B1744289
theorem B1162871 : Blo 1160639 1162871 := bstep (se 1 (by rfl) ⟨872153, by rfl⟩ : syracuseStep 1162871 = 1744307) B1744307
theorem B1162891 : Blo 1160639 1162891 := bstep (se 1 (by rfl) ⟨872168, by rfl⟩ : syracuseStep 1162891 = 1744337) B1744337
theorem B1162903 : Blo 1160639 1162903 := bstep (se 1 (by rfl) ⟨872177, by rfl⟩ : syracuseStep 1162903 = 1744355) B1744355
theorem B1162923 : Blo 1160639 1162923 := bstep (se 1 (by rfl) ⟨872192, by rfl⟩ : syracuseStep 1162923 = 1744385) B1744385
theorem B4406957 : Blo 1160639 4406957 := bstep (se 3 (by rfl) ⟨826304, by rfl⟩ : syracuseStep 4406957 = 1652609) B1652609
theorem B1162935 : Blo 1160639 1162935 := bstep (se 1 (by rfl) ⟨872201, by rfl⟩ : syracuseStep 1162935 = 1744403) B1744403
theorem B4406987 : Blo 1160639 4406987 := bstep (se 1 (by rfl) ⟨3305240, by rfl⟩ : syracuseStep 4406987 = 6610481) B6610481
theorem B1162955 : Blo 1160639 1162955 := bstep (se 1 (by rfl) ⟨872216, by rfl⟩ : syracuseStep 1162955 = 1744433) B1744433
theorem B1162967 : Blo 1160639 1162967 := bstep (se 1 (by rfl) ⟨872225, by rfl⟩ : syracuseStep 1162967 = 1744451) B1744451
theorem B1162987 : Blo 1160639 1162987 := bstep (se 1 (by rfl) ⟨872240, by rfl⟩ : syracuseStep 1162987 = 1744481) B1744481
theorem B1162999 : Blo 1160639 1162999 := bstep (se 1 (by rfl) ⟨872249, by rfl⟩ : syracuseStep 1162999 = 1744499) B1744499
theorem B1163019 : Blo 1160639 1163019 := bstep (se 1 (by rfl) ⟨872264, by rfl⟩ : syracuseStep 1163019 = 1744529) B1744529
theorem B1163031 : Blo 1160639 1163031 := bstep (se 1 (by rfl) ⟨872273, by rfl⟩ : syracuseStep 1163031 = 1744547) B1744547
theorem B1163051 : Blo 1160639 1163051 := bstep (se 1 (by rfl) ⟨872288, by rfl⟩ : syracuseStep 1163051 = 1744577) B1744577
theorem B1163063 : Blo 1160639 1163063 := bstep (se 1 (by rfl) ⟨872297, by rfl⟩ : syracuseStep 1163063 = 1744595) B1744595
theorem B1163083 : Blo 1160639 1163083 := bstep (se 1 (by rfl) ⟨872312, by rfl⟩ : syracuseStep 1163083 = 1744625) B1744625
theorem B1163095 : Blo 1160639 1163095 := bstep (se 1 (by rfl) ⟨872321, by rfl⟩ : syracuseStep 1163095 = 1744643) B1744643
theorem B1163115 : Blo 1160639 1163115 := bstep (se 1 (by rfl) ⟨872336, by rfl⟩ : syracuseStep 1163115 = 1744673) B1744673
theorem B1163127 : Blo 1160639 1163127 := bstep (se 1 (by rfl) ⟨872345, by rfl⟩ : syracuseStep 1163127 = 1744691) B1744691
theorem B1163147 : Blo 1160639 1163147 := bstep (se 1 (by rfl) ⟨872360, by rfl⟩ : syracuseStep 1163147 = 1744721) B1744721
theorem B1163159 : Blo 1160639 1163159 := bstep (se 1 (by rfl) ⟨872369, by rfl⟩ : syracuseStep 1163159 = 1744739) B1744739
theorem B1163179 : Blo 1160639 1163179 := bstep (se 1 (by rfl) ⟨872384, by rfl⟩ : syracuseStep 1163179 = 1744769) B1744769
theorem B1163191 : Blo 1160639 1163191 := bstep (se 1 (by rfl) ⟨872393, by rfl⟩ : syracuseStep 1163191 = 1744787) B1744787
theorem B1163211 : Blo 1160639 1163211 := bstep (se 1 (by rfl) ⟨872408, by rfl⟩ : syracuseStep 1163211 = 1744817) B1744817
theorem B1163223 : Blo 1160639 1163223 := bstep (se 1 (by rfl) ⟨872417, by rfl⟩ : syracuseStep 1163223 = 1744835) B1744835
theorem B1163243 : Blo 1160639 1163243 := bstep (se 1 (by rfl) ⟨872432, by rfl⟩ : syracuseStep 1163243 = 1744865) B1744865
theorem B1163255 : Blo 1160639 1163255 := bstep (se 1 (by rfl) ⟨872441, by rfl⟩ : syracuseStep 1163255 = 1744883) B1744883
theorem B1163275 : Blo 1160639 1163275 := bstep (se 1 (by rfl) ⟨872456, by rfl⟩ : syracuseStep 1163275 = 1744913) B1744913
theorem B3719191 : Blo 1160639 3719191 := bstep (se 1 (by rfl) ⟨2789393, by rfl⟩ : syracuseStep 3719191 = 5578787) B5578787
theorem B1163287 : Blo 1160639 1163287 := bstep (se 1 (by rfl) ⟨872465, by rfl⟩ : syracuseStep 1163287 = 1744931) B1744931
theorem B1163307 : Blo 1160639 1163307 := bstep (se 1 (by rfl) ⟨872480, by rfl⟩ : syracuseStep 1163307 = 1744961) B1744961
theorem B1163319 : Blo 1160639 1163319 := bstep (se 1 (by rfl) ⟨872489, by rfl⟩ : syracuseStep 1163319 = 1744979) B1744979
theorem B7061579 : Blo 1160639 7061579 := bstep (se 1 (by rfl) ⟨5296184, by rfl⟩ : syracuseStep 7061579 = 10592369) B10592369
theorem B1163339 : Blo 1160639 1163339 := bstep (se 1 (by rfl) ⟨872504, by rfl⟩ : syracuseStep 1163339 = 1745009) B1745009
theorem B1163351 : Blo 1160639 1163351 := bstep (se 1 (by rfl) ⟨872513, by rfl⟩ : syracuseStep 1163351 = 1745027) B1745027
theorem B1163371 : Blo 1160639 1163371 := bstep (se 1 (by rfl) ⟨872528, by rfl⟩ : syracuseStep 1163371 = 1745057) B1745057
theorem B1163383 : Blo 1160639 1163383 := bstep (se 1 (by rfl) ⟨872537, by rfl⟩ : syracuseStep 1163383 = 1745075) B1745075
theorem B1163403 : Blo 1160639 1163403 := bstep (se 1 (by rfl) ⟨872552, by rfl⟩ : syracuseStep 1163403 = 1745105) B1745105
theorem B1163415 : Blo 1160639 1163415 := bstep (se 1 (by rfl) ⟨872561, by rfl⟩ : syracuseStep 1163415 = 1745123) B1745123
theorem B1163435 : Blo 1160639 1163435 := bstep (se 1 (by rfl) ⟨872576, by rfl⟩ : syracuseStep 1163435 = 1745153) B1745153
theorem B1163447 : Blo 1160639 1163447 := bstep (se 1 (by rfl) ⟨872585, by rfl⟩ : syracuseStep 1163447 = 1745171) B1745171
theorem B1163467 : Blo 1160639 1163467 := bstep (se 1 (by rfl) ⟨872600, by rfl⟩ : syracuseStep 1163467 = 1745201) B1745201
theorem B1163479 : Blo 1160639 1163479 := bstep (se 1 (by rfl) ⟨872609, by rfl⟩ : syracuseStep 1163479 = 1745219) B1745219
theorem B1163499 : Blo 1160639 1163499 := bstep (se 1 (by rfl) ⟨872624, by rfl⟩ : syracuseStep 1163499 = 1745249) B1745249
theorem B1163511 : Blo 1160639 1163511 := bstep (se 1 (by rfl) ⟨872633, by rfl⟩ : syracuseStep 1163511 = 1745267) B1745267
theorem B4964611 : Blo 1160639 4964611 := bstep (se 1 (by rfl) ⟨3723458, by rfl⟩ : syracuseStep 4964611 = 7446917) B7446917
theorem B1163531 : Blo 1160639 1163531 := bstep (se 1 (by rfl) ⟨872648, by rfl⟩ : syracuseStep 1163531 = 1745297) B1745297
theorem B1163543 : Blo 1160639 1163543 := bstep (se 1 (by rfl) ⟨872657, by rfl⟩ : syracuseStep 1163543 = 1745315) B1745315
theorem B1163563 : Blo 1160639 1163563 := bstep (se 1 (by rfl) ⟨872672, by rfl⟩ : syracuseStep 1163563 = 1745345) B1745345
theorem B1163575 : Blo 1160639 1163575 := bstep (se 1 (by rfl) ⟨872681, by rfl⟩ : syracuseStep 1163575 = 1745363) B1745363
theorem B1163595 : Blo 1160639 1163595 := bstep (se 1 (by rfl) ⟨872696, by rfl⟩ : syracuseStep 1163595 = 1745393) B1745393
theorem B1327435 : Blo 1160639 1327435 := bstep (se 1 (by rfl) ⟨995576, by rfl⟩ : syracuseStep 1327435 = 1991153) B1991153
theorem B1163607 : Blo 1160639 1163607 := bstep (se 1 (by rfl) ⟨872705, by rfl⟩ : syracuseStep 1163607 = 1745411) B1745411
theorem B4407641 : Blo 1160639 4407641 := bstep (se 2 (by rfl) ⟨1652865, by rfl⟩ : syracuseStep 4407641 = 3305731) B3305731
theorem B1163627 : Blo 1160639 1163627 := bstep (se 1 (by rfl) ⟨872720, by rfl⟩ : syracuseStep 1163627 = 1745441) B1745441
theorem B1163639 : Blo 1160639 1163639 := bstep (se 1 (by rfl) ⟨872729, by rfl⟩ : syracuseStep 1163639 = 1745459) B1745459
theorem B1163659 : Blo 1160639 1163659 := bstep (se 1 (by rfl) ⟨872744, by rfl⟩ : syracuseStep 1163659 = 1745489) B1745489
theorem B1163671 : Blo 1160639 1163671 := bstep (se 1 (by rfl) ⟨872753, by rfl⟩ : syracuseStep 1163671 = 1745507) B1745507
theorem B1163691 : Blo 1160639 1163691 := bstep (se 1 (by rfl) ⟨872768, by rfl⟩ : syracuseStep 1163691 = 1745537) B1745537
theorem B1163703 : Blo 1160639 1163703 := bstep (se 1 (by rfl) ⟨872777, by rfl⟩ : syracuseStep 1163703 = 1745555) B1745555
theorem B3719627 : Blo 1160639 3719627 := bstep (se 1 (by rfl) ⟨2789720, by rfl⟩ : syracuseStep 3719627 = 5579441) B5579441
theorem B1163723 : Blo 1160639 1163723 := bstep (se 1 (by rfl) ⟨872792, by rfl⟩ : syracuseStep 1163723 = 1745585) B1745585
theorem B1163735 : Blo 1160639 1163735 := bstep (se 1 (by rfl) ⟨872801, by rfl⟩ : syracuseStep 1163735 = 1745603) B1745603
theorem B1163755 : Blo 1160639 1163755 := bstep (se 1 (by rfl) ⟨872816, by rfl⟩ : syracuseStep 1163755 = 1745633) B1745633
theorem B1163767 : Blo 1160639 1163767 := bstep (se 1 (by rfl) ⟨872825, by rfl⟩ : syracuseStep 1163767 = 1745651) B1745651
theorem B1163787 : Blo 1160639 1163787 := bstep (se 1 (by rfl) ⟨872840, by rfl⟩ : syracuseStep 1163787 = 1745681) B1745681
theorem B1163799 : Blo 1160639 1163799 := bstep (se 1 (by rfl) ⟨872849, by rfl⟩ : syracuseStep 1163799 = 1745699) B1745699
theorem B1163819 : Blo 1160639 1163819 := bstep (se 1 (by rfl) ⟨872864, by rfl⟩ : syracuseStep 1163819 = 1745729) B1745729
theorem B1163831 : Blo 1160639 1163831 := bstep (se 1 (by rfl) ⟨872873, by rfl⟩ : syracuseStep 1163831 = 1745747) B1745747
theorem B1163851 : Blo 1160639 1163851 := bstep (se 1 (by rfl) ⟨872888, by rfl⟩ : syracuseStep 1163851 = 1745777) B1745777
theorem B1163863 : Blo 1160639 1163863 := bstep (se 1 (by rfl) ⟨872897, by rfl⟩ : syracuseStep 1163863 = 1745795) B1745795
theorem B1163883 : Blo 1160639 1163883 := bstep (se 1 (by rfl) ⟨872912, by rfl⟩ : syracuseStep 1163883 = 1745825) B1745825
theorem B1163895 : Blo 1160639 1163895 := bstep (se 1 (by rfl) ⟨872921, by rfl⟩ : syracuseStep 1163895 = 1745843) B1745843
theorem B1163915 : Blo 1160639 1163915 := bstep (se 1 (by rfl) ⟨872936, by rfl⟩ : syracuseStep 1163915 = 1745873) B1745873
theorem B4407959 : Blo 1160639 4407959 := bstep (se 1 (by rfl) ⟨3305969, by rfl⟩ : syracuseStep 4407959 = 6611939) B6611939
theorem B1163927 : Blo 1160639 1163927 := bstep (se 1 (by rfl) ⟨872945, by rfl⟩ : syracuseStep 1163927 = 1745891) B1745891
theorem B1163947 : Blo 1160639 1163947 := bstep (se 1 (by rfl) ⟨872960, by rfl⟩ : syracuseStep 1163947 = 1745921) B1745921
theorem B1163959 : Blo 1160639 1163959 := bstep (se 1 (by rfl) ⟨872969, by rfl⟩ : syracuseStep 1163959 = 1745939) B1745939
theorem B1163979 : Blo 1160639 1163979 := bstep (se 1 (by rfl) ⟨872984, by rfl⟩ : syracuseStep 1163979 = 1745969) B1745969
theorem B1163991 : Blo 1160639 1163991 := bstep (se 1 (by rfl) ⟨872993, by rfl⟩ : syracuseStep 1163991 = 1745987) B1745987
theorem B1164011 : Blo 1160639 1164011 := bstep (se 1 (by rfl) ⟨873008, by rfl⟩ : syracuseStep 1164011 = 1746017) B1746017
theorem B1164023 : Blo 1160639 1164023 := bstep (se 1 (by rfl) ⟨873017, by rfl⟩ : syracuseStep 1164023 = 1746035) B1746035
theorem B1164043 : Blo 1160639 1164043 := bstep (se 1 (by rfl) ⟨873032, by rfl⟩ : syracuseStep 1164043 = 1746065) B1746065
theorem B1164055 : Blo 1160639 1164055 := bstep (se 1 (by rfl) ⟨873041, by rfl⟩ : syracuseStep 1164055 = 1746083) B1746083
theorem B1164075 : Blo 1160639 1164075 := bstep (se 1 (by rfl) ⟨873056, by rfl⟩ : syracuseStep 1164075 = 1746113) B1746113
theorem B1164087 : Blo 1160639 1164087 := bstep (se 1 (by rfl) ⟨873065, by rfl⟩ : syracuseStep 1164087 = 1746131) B1746131
theorem B1164107 : Blo 1160639 1164107 := bstep (se 1 (by rfl) ⟨873080, by rfl⟩ : syracuseStep 1164107 = 1746161) B1746161
theorem B1164119 : Blo 1160639 1164119 := bstep (se 1 (by rfl) ⟨873089, by rfl⟩ : syracuseStep 1164119 = 1746179) B1746179
theorem B4965209 : Blo 1160639 4965209 := bstep (se 2 (by rfl) ⟨1861953, by rfl⟩ : syracuseStep 4965209 = 3723907) B3723907
theorem B1164139 : Blo 1160639 1164139 := bstep (se 1 (by rfl) ⟨873104, by rfl⟩ : syracuseStep 1164139 = 1746209) B1746209
theorem B14140277 : Blo 1160639 14140277 := bstep (se 5 (by rfl) ⟨662825, by rfl⟩ : syracuseStep 14140277 = 1325651) B1325651
theorem B1164151 : Blo 1160639 1164151 := bstep (se 1 (by rfl) ⟨873113, by rfl⟩ : syracuseStep 1164151 = 1746227) B1746227
theorem B1164171 : Blo 1160639 1164171 := bstep (se 1 (by rfl) ⟨873128, by rfl⟩ : syracuseStep 1164171 = 1746257) B1746257
theorem B1164183 : Blo 1160639 1164183 := bstep (se 1 (by rfl) ⟨873137, by rfl⟩ : syracuseStep 1164183 = 1746275) B1746275
theorem B1164203 : Blo 1160639 1164203 := bstep (se 1 (by rfl) ⟨873152, by rfl⟩ : syracuseStep 1164203 = 1746305) B1746305
theorem B1164215 : Blo 1160639 1164215 := bstep (se 1 (by rfl) ⟨873161, by rfl⟩ : syracuseStep 1164215 = 1746323) B1746323
theorem B1164235 : Blo 1160639 1164235 := bstep (se 1 (by rfl) ⟨873176, by rfl⟩ : syracuseStep 1164235 = 1746353) B1746353
theorem B1164247 : Blo 1160639 1164247 := bstep (se 1 (by rfl) ⟨873185, by rfl⟩ : syracuseStep 1164247 = 1746371) B1746371
theorem B1164267 : Blo 1160639 1164267 := bstep (se 1 (by rfl) ⟨873200, by rfl⟩ : syracuseStep 1164267 = 1746401) B1746401
theorem B1164279 : Blo 1160639 1164279 := bstep (se 1 (by rfl) ⟨873209, by rfl⟩ : syracuseStep 1164279 = 1746419) B1746419
theorem B1164299 : Blo 1160639 1164299 := bstep (se 1 (by rfl) ⟨873224, by rfl⟩ : syracuseStep 1164299 = 1746449) B1746449
theorem B1164311 : Blo 1160639 1164311 := bstep (se 1 (by rfl) ⟨873233, by rfl⟩ : syracuseStep 1164311 = 1746467) B1746467
theorem B32228387 : Blo 1160639 32228387 := bstep (se 1 (by rfl) ⟨24171290, by rfl⟩ : syracuseStep 32228387 = 48342581) B48342581
theorem B1164331 : Blo 1160639 1164331 := bstep (se 1 (by rfl) ⟨873248, by rfl⟩ : syracuseStep 1164331 = 1746497) B1746497
theorem B1164343 : Blo 1160639 1164343 := bstep (se 1 (by rfl) ⟨873257, by rfl⟩ : syracuseStep 1164343 = 1746515) B1746515
theorem B19088453 : Blo 1160639 19088453 := bstep (se 4 (by rfl) ⟨1789542, by rfl⟩ : syracuseStep 19088453 = 3579085) B3579085
theorem B1164363 : Blo 1160639 1164363 := bstep (se 1 (by rfl) ⟨873272, by rfl⟩ : syracuseStep 1164363 = 1746545) B1746545
theorem B1164375 : Blo 1160639 1164375 := bstep (se 1 (by rfl) ⟨873281, by rfl⟩ : syracuseStep 1164375 = 1746563) B1746563
theorem B1164395 : Blo 1160639 1164395 := bstep (se 1 (by rfl) ⟨873296, by rfl⟩ : syracuseStep 1164395 = 1746593) B1746593
theorem B1164407 : Blo 1160639 1164407 := bstep (se 1 (by rfl) ⟨873305, by rfl⟩ : syracuseStep 1164407 = 1746611) B1746611
theorem B1164427 : Blo 1160639 1164427 := bstep (se 1 (by rfl) ⟨873320, by rfl⟩ : syracuseStep 1164427 = 1746641) B1746641
theorem B1164439 : Blo 1160639 1164439 := bstep (se 1 (by rfl) ⟨873329, by rfl⟩ : syracuseStep 1164439 = 1746659) B1746659
theorem B1164459 : Blo 1160639 1164459 := bstep (se 1 (by rfl) ⟨873344, by rfl⟩ : syracuseStep 1164459 = 1746689) B1746689
theorem B1164471 : Blo 1160639 1164471 := bstep (se 1 (by rfl) ⟨873353, by rfl⟩ : syracuseStep 1164471 = 1746707) B1746707
theorem B4965569 : Blo 1160639 4965569 := bstep (se 2 (by rfl) ⟨1862088, by rfl⟩ : syracuseStep 4965569 = 3724177) B3724177
theorem B1164491 : Blo 1160639 1164491 := bstep (se 1 (by rfl) ⟨873368, by rfl⟩ : syracuseStep 1164491 = 1746737) B1746737
theorem B1164503 : Blo 1160639 1164503 := bstep (se 1 (by rfl) ⟨873377, by rfl⟩ : syracuseStep 1164503 = 1746755) B1746755
theorem B1164523 : Blo 1160639 1164523 := bstep (se 1 (by rfl) ⟨873392, by rfl⟩ : syracuseStep 1164523 = 1746785) B1746785
theorem B1164535 : Blo 1160639 1164535 := bstep (se 1 (by rfl) ⟨873401, by rfl⟩ : syracuseStep 1164535 = 1746803) B1746803
theorem B1164555 : Blo 1160639 1164555 := bstep (se 1 (by rfl) ⟨873416, by rfl⟩ : syracuseStep 1164555 = 1746833) B1746833
theorem B1164567 : Blo 1160639 1164567 := bstep (se 1 (by rfl) ⟨873425, by rfl⟩ : syracuseStep 1164567 = 1746851) B1746851
theorem B1164587 : Blo 1160639 1164587 := bstep (se 1 (by rfl) ⟨873440, by rfl⟩ : syracuseStep 1164587 = 1746881) B1746881
theorem B4408627 : Blo 1160639 4408627 := bstep (se 1 (by rfl) ⟨3306470, by rfl⟩ : syracuseStep 4408627 = 6612941) B6612941
theorem B1164599 : Blo 1160639 1164599 := bstep (se 1 (by rfl) ⟨873449, by rfl⟩ : syracuseStep 1164599 = 1746899) B1746899
theorem B1164619 : Blo 1160639 1164619 := bstep (se 1 (by rfl) ⟨873464, by rfl⟩ : syracuseStep 1164619 = 1746929) B1746929
theorem B1164631 : Blo 1160639 1164631 := bstep (se 1 (by rfl) ⟨873473, by rfl⟩ : syracuseStep 1164631 = 1746947) B1746947
theorem B5883353 : Blo 1160639 5883353 := bstep (se 2 (by rfl) ⟨2206257, by rfl⟩ : syracuseStep 5883353 = 4412515) B4412515
theorem B3720755 : Blo 1160639 3720755 := bstep (se 1 (by rfl) ⟨2790566, by rfl⟩ : syracuseStep 3720755 = 5581133) B5581133
theorem B3720907 : Blo 1160639 3720907 := bstep (se 1 (by rfl) ⟨2790680, by rfl⟩ : syracuseStep 3720907 = 5581361) B5581361
theorem B3917591 : Blo 1160639 3917591 := bstep (se 1 (by rfl) ⟨2938193, by rfl⟩ : syracuseStep 3917591 = 5876387) B5876387
theorem B31868963 : Blo 1160639 31868963 := bstep (se 1 (by rfl) ⟨23901722, by rfl⟩ : syracuseStep 31868963 = 47803445) B47803445
theorem B1656983 : Blo 1160639 1656983 := bstep (se 1 (by rfl) ⟨1242737, by rfl⟩ : syracuseStep 1656983 = 2485475) B2485475
theorem B3721409 : Blo 1160639 3721409 := bstep (se 2 (by rfl) ⟨1395528, by rfl⟩ : syracuseStep 3721409 = 2791057) B2791057
theorem B3918131 : Blo 1160639 3918131 := bstep (se 1 (by rfl) ⟨2938598, by rfl⟩ : syracuseStep 3918131 = 5877197) B5877197
theorem B9947569 : Blo 1160639 9947569 := bstep (se 2 (by rfl) ⟨3730338, by rfl⟩ : syracuseStep 9947569 = 7460677) B7460677
theorem B4409873 : Blo 1160639 4409873 := bstep (se 2 (by rfl) ⟨1653702, by rfl⟩ : syracuseStep 4409873 = 3307405) B3307405
theorem B3918401 : Blo 1160639 3918401 := bstep (se 2 (by rfl) ⟨1469400, by rfl⟩ : syracuseStep 3918401 = 2938801) B2938801
theorem B1985303 : Blo 1160639 1985303 := bstep (se 1 (by rfl) ⟨1488977, by rfl⟩ : syracuseStep 1985303 = 2977955) B2977955
theorem B11324377 : Blo 1160639 11324377 := bstep (se 2 (by rfl) ⟨4246641, by rfl⟩ : syracuseStep 11324377 = 8493283) B8493283
theorem B5884973 : Blo 1160639 5884973 := bstep (se 3 (by rfl) ⟨1103432, by rfl⟩ : syracuseStep 5884973 = 2206865) B2206865
theorem B3918941 : Blo 1160639 3918941 := bstep (se 3 (by rfl) ⟨734801, by rfl⟩ : syracuseStep 3918941 = 1469603) B1469603
theorem B5590109 : Blo 1160639 5590109 := bstep (se 3 (by rfl) ⟨1048145, by rfl⟩ : syracuseStep 5590109 = 2096291) B2096291
theorem B4082867 : Blo 1160639 4082867 := bstep (se 1 (by rfl) ⟨3062150, by rfl⟩ : syracuseStep 4082867 = 6124301) B6124301
theorem B4410571 : Blo 1160639 4410571 := bstep (se 1 (by rfl) ⟨3307928, by rfl⟩ : syracuseStep 4410571 = 6615857) B6615857
theorem B7458065 : Blo 1160639 7458065 := bstep (se 2 (by rfl) ⟨2796774, by rfl⟩ : syracuseStep 7458065 = 5593549) B5593549
theorem B4410845 : Blo 1160639 4410845 := bstep (se 3 (by rfl) ⟨827033, by rfl⟩ : syracuseStep 4410845 = 1654067) B1654067
theorem B10604333 : Blo 1160639 10604333 := bstep (se 3 (by rfl) ⟨1988312, by rfl⟩ : syracuseStep 10604333 = 3976625) B3976625
theorem B8834993 : Blo 1160639 8834993 := bstep (se 2 (by rfl) ⟨3313122, by rfl⟩ : syracuseStep 8834993 = 6626245) B6626245
theorem B1396759 : Blo 1160639 1396759 := bstep (se 1 (by rfl) ⟨1047569, by rfl⟩ : syracuseStep 1396759 = 2095139) B2095139
theorem B4411543 : Blo 1160639 4411543 := bstep (se 1 (by rfl) ⟨3308657, by rfl⟩ : syracuseStep 4411543 = 6617315) B6617315
theorem B3920075 : Blo 1160639 3920075 := bstep (se 1 (by rfl) ⟨2940056, by rfl⟩ : syracuseStep 3920075 = 5880113) B5880113
theorem B1986905 : Blo 1160639 1986905 := bstep (se 2 (by rfl) ⟨745089, by rfl⟩ : syracuseStep 1986905 = 1490179) B1490179
theorem B8835479 : Blo 1160639 8835479 := bstep (se 1 (by rfl) ⟨6626609, by rfl⟩ : syracuseStep 8835479 = 13253219) B13253219
theorem B3920345 : Blo 1160639 3920345 := bstep (se 2 (by rfl) ⟨1470129, by rfl⟩ : syracuseStep 3920345 = 2940259) B2940259
theorem B3723869 : Blo 1160639 3723869 := bstep (se 3 (by rfl) ⟨698225, by rfl⟩ : syracuseStep 3723869 = 1396451) B1396451
theorem B7951121 : Blo 1160639 7951121 := bstep (se 2 (by rfl) ⟨2981670, by rfl⟩ : syracuseStep 7951121 = 5963341) B5963341
theorem B4969309 : Blo 1160639 4969309 := bstep (se 3 (by rfl) ⟨931745, by rfl⟩ : syracuseStep 4969309 = 1863491) B1863491
theorem B4412333 : Blo 1160639 4412333 := bstep (se 3 (by rfl) ⟨827312, by rfl⟩ : syracuseStep 4412333 = 1654625) B1654625
theorem B3921047 : Blo 1160639 3921047 := bstep (se 1 (by rfl) ⟨2940785, by rfl⟩ : syracuseStep 3921047 = 5881571) B5881571
theorem B4248749 : Blo 1160639 4248749 := bstep (se 3 (by rfl) ⟨796640, by rfl⟩ : syracuseStep 4248749 = 1593281) B1593281
theorem B4478125 : Blo 1160639 4478125 := bstep (se 3 (by rfl) ⟨839648, by rfl⟩ : syracuseStep 4478125 = 1679297) B1679297
theorem B4183427 : Blo 1160639 4183427 := bstep (se 1 (by rfl) ⟨3137570, by rfl⟩ : syracuseStep 4183427 = 6275141) B6275141
theorem B2938315 : Blo 1160639 2938315 := bstep (se 1 (by rfl) ⟨2203736, by rfl⟩ : syracuseStep 2938315 = 4407473) B4407473
theorem B2938457 : Blo 1160639 2938457 := bstep (se 2 (by rfl) ⟨1101921, by rfl⟩ : syracuseStep 2938457 = 2203843) B2203843
theorem B3921587 : Blo 1160639 3921587 := bstep (se 1 (by rfl) ⟨2941190, by rfl⟩ : syracuseStep 3921587 = 5882381) B5882381
theorem B2480051 : Blo 1160639 2480051 := bstep (se 1 (by rfl) ⟨1860038, by rfl⟩ : syracuseStep 2480051 = 3720077) B3720077
theorem B3921857 : Blo 1160639 3921857 := bstep (se 2 (by rfl) ⟨1470696, by rfl⟩ : syracuseStep 3921857 = 2941393) B2941393
theorem B8378329 : Blo 1160639 8378329 := bstep (se 2 (by rfl) ⟨3141873, by rfl⟩ : syracuseStep 8378329 = 6283747) B6283747
theorem B5036107 : Blo 1160639 5036107 := bstep (se 1 (by rfl) ⟨3777080, by rfl⟩ : syracuseStep 5036107 = 7554161) B7554161
theorem B4970641 : Blo 1160639 4970641 := bstep (se 2 (by rfl) ⟨1863990, by rfl⟩ : syracuseStep 4970641 = 3727981) B3727981
theorem B2611457 : Blo 1160639 2611457 := bstep (se 2 (by rfl) ⟨979296, by rfl⟩ : syracuseStep 2611457 = 1958593) B1958593
theorem B4413761 : Blo 1160639 4413761 := bstep (se 2 (by rfl) ⟨1655160, by rfl⟩ : syracuseStep 4413761 = 3310321) B3310321
theorem B2939287 : Blo 1160639 2939287 := bstep (se 1 (by rfl) ⟨2204465, by rfl⟩ : syracuseStep 2939287 = 4408931) B4408931
theorem B2480537 : Blo 1160639 2480537 := bstep (se 2 (by rfl) ⟨930201, by rfl⟩ : syracuseStep 2480537 = 1860403) B1860403
theorem B21813683 : Blo 1160639 21813683 := bstep (se 1 (by rfl) ⟨16360262, by rfl⟩ : syracuseStep 21813683 = 32720525) B32720525
theorem B2611673 : Blo 1160639 2611673 := bstep (se 2 (by rfl) ⟨979377, by rfl⟩ : syracuseStep 2611673 = 1958755) B1958755
theorem B3922397 : Blo 1160639 3922397 := bstep (se 3 (by rfl) ⟨735449, by rfl⟩ : syracuseStep 3922397 = 1470899) B1470899
theorem B2611763 : Blo 1160639 2611763 := bstep (se 1 (by rfl) ⟨1958822, by rfl⟩ : syracuseStep 2611763 = 3917645) B3917645
theorem B2611799 : Blo 1160639 2611799 := bstep (se 1 (by rfl) ⟨1958849, by rfl⟩ : syracuseStep 2611799 = 3917699) B3917699
theorem B4840195 : Blo 1160639 4840195 := bstep (se 1 (by rfl) ⟨3630146, by rfl⟩ : syracuseStep 4840195 = 7260293) B7260293
theorem B2611979 : Blo 1160639 2611979 := bstep (se 1 (by rfl) ⟨1958984, by rfl⟩ : syracuseStep 2611979 = 3917969) B3917969
theorem B2612033 : Blo 1160639 2612033 := bstep (se 2 (by rfl) ⟨979512, by rfl⟩ : syracuseStep 2612033 = 1959025) B1959025
theorem B2939723 : Blo 1160639 2939723 := bstep (se 1 (by rfl) ⟨2204792, by rfl⟩ : syracuseStep 2939723 = 4409585) B4409585
theorem B5888861 : Blo 1160639 5888861 := bstep (se 3 (by rfl) ⟨1104161, by rfl⟩ : syracuseStep 5888861 = 2208323) B2208323
theorem B2612249 : Blo 1160639 2612249 := bstep (se 2 (by rfl) ⟨979593, by rfl⟩ : syracuseStep 2612249 = 1959187) B1959187
theorem B2612339 : Blo 1160639 2612339 := bstep (se 1 (by rfl) ⟨1959254, by rfl⟩ : syracuseStep 2612339 = 3918509) B3918509
theorem B2612375 : Blo 1160639 2612375 := bstep (se 1 (by rfl) ⟨1959281, by rfl⟩ : syracuseStep 2612375 = 3918563) B3918563
theorem B47733941 : Blo 1160639 47733941 := bstep (se 5 (by rfl) ⟨2237528, by rfl⟩ : syracuseStep 47733941 = 4475057) B4475057
theorem B2940097 : Blo 1160639 2940097 := bstep (se 2 (by rfl) ⟨1102536, by rfl⟩ : syracuseStep 2940097 = 2205073) B2205073
theorem B11164877 : Blo 1160639 11164877 := bstep (se 3 (by rfl) ⟨2093414, by rfl⟩ : syracuseStep 11164877 = 4186829) B4186829
theorem B2612555 : Blo 1160639 2612555 := bstep (se 1 (by rfl) ⟨1959416, by rfl⟩ : syracuseStep 2612555 = 3918833) B3918833
theorem B2612609 : Blo 1160639 2612609 := bstep (se 2 (by rfl) ⟨979728, by rfl⟩ : syracuseStep 2612609 = 1959457) B1959457
theorem B3923531 : Blo 1160639 3923531 := bstep (se 1 (by rfl) ⟨2942648, by rfl⟩ : syracuseStep 3923531 = 5885297) B5885297
theorem B2612825 : Blo 1160639 2612825 := bstep (se 2 (by rfl) ⟨979809, by rfl⟩ : syracuseStep 2612825 = 1959619) B1959619
theorem B2612915 : Blo 1160639 2612915 := bstep (se 1 (by rfl) ⟨1959686, by rfl⟩ : syracuseStep 2612915 = 3919373) B3919373
theorem B4775617 : Blo 1160639 4775617 := bstep (se 2 (by rfl) ⟨1790856, by rfl⟩ : syracuseStep 4775617 = 3581713) B3581713
theorem B1859275 : Blo 1160639 1859275 := bstep (se 1 (by rfl) ⟨1394456, by rfl⟩ : syracuseStep 1859275 = 2788913) B2788913
theorem B2612951 : Blo 1160639 2612951 := bstep (se 1 (by rfl) ⟨1959713, by rfl⟩ : syracuseStep 2612951 = 3919427) B3919427
theorem B4415249 : Blo 1160639 4415249 := bstep (se 2 (by rfl) ⟨1655718, by rfl⟩ : syracuseStep 4415249 = 3311437) B3311437
theorem B2940695 : Blo 1160639 2940695 := bstep (se 1 (by rfl) ⟨2205521, by rfl⟩ : syracuseStep 2940695 = 4411043) B4411043
theorem B6610733 : Blo 1160639 6610733 := bstep (se 3 (by rfl) ⟨1239512, by rfl⟩ : syracuseStep 6610733 = 2479025) B2479025
theorem B3923801 : Blo 1160639 3923801 := bstep (se 2 (by rfl) ⟨1471425, by rfl⟩ : syracuseStep 3923801 = 2942851) B2942851
theorem B2613131 : Blo 1160639 2613131 := bstep (se 1 (by rfl) ⟨1959848, by rfl⟩ : syracuseStep 2613131 = 3919697) B3919697
theorem B4480913 : Blo 1160639 4480913 := bstep (se 2 (by rfl) ⟨1680342, by rfl⟩ : syracuseStep 4480913 = 3360685) B3360685
theorem B2613185 : Blo 1160639 2613185 := bstep (se 2 (by rfl) ⟨979944, by rfl⟩ : syracuseStep 2613185 = 1959889) B1959889
theorem B1859531 : Blo 1160639 1859531 := bstep (se 1 (by rfl) ⟨1394648, by rfl⟩ : syracuseStep 1859531 = 2789297) B2789297
theorem B2482177 : Blo 1160639 2482177 := bstep (se 2 (by rfl) ⟨930816, by rfl⟩ : syracuseStep 2482177 = 1861633) B1861633
theorem B2613401 : Blo 1160639 2613401 := bstep (se 2 (by rfl) ⟨980025, by rfl⟩ : syracuseStep 2613401 = 1960051) B1960051
theorem B5300417 : Blo 1160639 5300417 := bstep (se 2 (by rfl) ⟨1987656, by rfl⟩ : syracuseStep 5300417 = 3975313) B3975313
theorem B4415705 : Blo 1160639 4415705 := bstep (se 2 (by rfl) ⟨1655889, by rfl⟩ : syracuseStep 4415705 = 3311779) B3311779
theorem B2613491 : Blo 1160639 2613491 := bstep (se 1 (by rfl) ⟨1960118, by rfl⟩ : syracuseStep 2613491 = 3920237) B3920237
theorem B2613527 : Blo 1160639 2613527 := bstep (se 1 (by rfl) ⟨1960145, by rfl⟩ : syracuseStep 2613527 = 3920291) B3920291
theorem B1859993 : Blo 1160639 1859993 := bstep (se 2 (by rfl) ⟨697497, by rfl⟩ : syracuseStep 1859993 = 1394995) B1394995
theorem B4415917 : Blo 1160639 4415917 := bstep (se 3 (by rfl) ⟨827984, by rfl⟩ : syracuseStep 4415917 = 1655969) B1655969
theorem B2613707 : Blo 1160639 2613707 := bstep (se 1 (by rfl) ⟨1960280, by rfl⟩ : syracuseStep 2613707 = 3920561) B3920561
theorem B2613761 : Blo 1160639 2613761 := bstep (se 2 (by rfl) ⟨980160, by rfl⟩ : syracuseStep 2613761 = 1960321) B1960321
theorem B3924503 : Blo 1160639 3924503 := bstep (se 1 (by rfl) ⟨2943377, by rfl⟩ : syracuseStep 3924503 = 5886755) B5886755
theorem B1860121 : Blo 1160639 1860121 := bstep (se 2 (by rfl) ⟨697545, by rfl⟩ : syracuseStep 1860121 = 1395091) B1395091
theorem B2941505 : Blo 1160639 2941505 := bstep (se 2 (by rfl) ⟨1103064, by rfl⟩ : syracuseStep 2941505 = 2206129) B2206129
theorem B2613977 : Blo 1160639 2613977 := bstep (se 2 (by rfl) ⟨980241, by rfl⟩ : syracuseStep 2613977 = 1960483) B1960483
theorem B4416221 : Blo 1160639 4416221 := bstep (se 3 (by rfl) ⟨828041, by rfl⟩ : syracuseStep 4416221 = 1656083) B1656083
theorem B1958681 : Blo 1160639 1958681 := bstep (se 2 (by rfl) ⟨734505, by rfl⟩ : syracuseStep 1958681 = 1469011) B1469011
theorem B9921325 : Blo 1160639 9921325 := bstep (se 3 (by rfl) ⟨1860248, by rfl⟩ : syracuseStep 9921325 = 3720497) B3720497
theorem B2614067 : Blo 1160639 2614067 := bstep (se 1 (by rfl) ⟨1960550, by rfl⟩ : syracuseStep 2614067 = 3921101) B3921101
theorem B2614103 : Blo 1160639 2614103 := bstep (se 1 (by rfl) ⟨1960577, by rfl⟩ : syracuseStep 2614103 = 3921155) B3921155
theorem B5890967 : Blo 1160639 5890967 := bstep (se 1 (by rfl) ⟨4418225, by rfl⟩ : syracuseStep 5890967 = 8836451) B8836451
theorem B1958809 : Blo 1160639 1958809 := bstep (se 2 (by rfl) ⟨734553, by rfl⟩ : syracuseStep 1958809 = 1469107) B1469107
theorem B2614283 : Blo 1160639 2614283 := bstep (se 1 (by rfl) ⟨1960712, by rfl⟩ : syracuseStep 2614283 = 3921425) B3921425
theorem B3925043 : Blo 1160639 3925043 := bstep (se 1 (by rfl) ⟨2943782, by rfl⟩ : syracuseStep 3925043 = 5887565) B5887565
theorem B2614337 : Blo 1160639 2614337 := bstep (se 2 (by rfl) ⟨980376, by rfl⟩ : syracuseStep 2614337 = 1960753) B1960753
theorem B4973633 : Blo 1160639 4973633 := bstep (se 2 (by rfl) ⟨1865112, by rfl⟩ : syracuseStep 4973633 = 3730225) B3730225
theorem B2942041 : Blo 1160639 2942041 := bstep (se 2 (by rfl) ⟨1103265, by rfl⟩ : syracuseStep 2942041 = 2206531) B2206531
theorem B2614553 : Blo 1160639 2614553 := bstep (se 2 (by rfl) ⟨980457, by rfl⟩ : syracuseStep 2614553 = 1960915) B1960915
theorem B3925313 : Blo 1160639 3925313 := bstep (se 2 (by rfl) ⟨1471992, by rfl⟩ : syracuseStep 3925313 = 2943985) B2943985
theorem B2614643 : Blo 1160639 2614643 := bstep (se 1 (by rfl) ⟨1960982, by rfl⟩ : syracuseStep 2614643 = 3921965) B3921965
theorem B2614679 : Blo 1160639 2614679 := bstep (se 1 (by rfl) ⟨1961009, by rfl⟩ : syracuseStep 2614679 = 3922019) B3922019
theorem B1959383 : Blo 1160639 1959383 := bstep (se 1 (by rfl) ⟨1469537, by rfl⟩ : syracuseStep 1959383 = 2939075) B2939075
theorem B10610137 : Blo 1160639 10610137 := bstep (se 2 (by rfl) ⟨3978801, by rfl⟩ : syracuseStep 10610137 = 7957603) B7957603
theorem B2614859 : Blo 1160639 2614859 := bstep (se 1 (by rfl) ⟨1961144, by rfl⟩ : syracuseStep 2614859 = 3922289) B3922289
theorem B1959511 : Blo 1160639 1959511 := bstep (se 1 (by rfl) ⟨1469633, by rfl⟩ : syracuseStep 1959511 = 2939267) B2939267
theorem B2614913 : Blo 1160639 2614913 := bstep (se 2 (by rfl) ⟨980592, by rfl⟩ : syracuseStep 2614913 = 1961185) B1961185
theorem B6285131 : Blo 1160639 6285131 := bstep (se 1 (by rfl) ⟨4713848, by rfl⟩ : syracuseStep 6285131 = 9427697) B9427697
theorem B2615129 : Blo 1160639 2615129 := bstep (se 2 (by rfl) ⟨980673, by rfl⟩ : syracuseStep 2615129 = 1961347) B1961347
theorem B3925853 : Blo 1160639 3925853 := bstep (se 3 (by rfl) ⟨736097, by rfl⟩ : syracuseStep 3925853 = 1472195) B1472195
theorem B2484083 : Blo 1160639 2484083 := bstep (se 1 (by rfl) ⟨1863062, by rfl⟩ : syracuseStep 2484083 = 3726125) B3726125
theorem B3139507 : Blo 1160639 3139507 := bstep (se 1 (by rfl) ⟨2354630, by rfl⟩ : syracuseStep 3139507 = 4709261) B4709261
theorem B2615219 : Blo 1160639 2615219 := bstep (se 1 (by rfl) ⟨1961414, by rfl⟩ : syracuseStep 2615219 = 3922829) B3922829
theorem B2615255 : Blo 1160639 2615255 := bstep (se 1 (by rfl) ⟨1961441, by rfl⟩ : syracuseStep 2615255 = 3922883) B3922883
theorem B9922661 : Blo 1160639 9922661 := bstep (se 4 (by rfl) ⟨930249, by rfl⟩ : syracuseStep 9922661 = 1860499) B1860499
theorem B6613123 : Blo 1160639 6613123 := bstep (se 1 (by rfl) ⟨4959842, by rfl⟩ : syracuseStep 6613123 = 9919685) B9919685
theorem B2615435 : Blo 1160639 2615435 := bstep (se 1 (by rfl) ⟨1961576, by rfl⟩ : syracuseStep 2615435 = 3923153) B3923153
theorem B5040301 : Blo 1160639 5040301 := bstep (se 3 (by rfl) ⟨945056, by rfl⟩ : syracuseStep 5040301 = 1890113) B1890113
theorem B2943155 : Blo 1160639 2943155 := bstep (se 1 (by rfl) ⟨2207366, by rfl⟩ : syracuseStep 2943155 = 4414733) B4414733
theorem B2615489 : Blo 1160639 2615489 := bstep (se 2 (by rfl) ⟨980808, by rfl⟩ : syracuseStep 2615489 = 1961617) B1961617
theorem B1960139 : Blo 1160639 1960139 := bstep (se 1 (by rfl) ⟨1470104, by rfl⟩ : syracuseStep 1960139 = 2940209) B2940209
theorem B4712651 : Blo 1160639 4712651 := bstep (se 1 (by rfl) ⟨3534488, by rfl⟩ : syracuseStep 4712651 = 7068977) B7068977
theorem B1960267 : Blo 1160639 1960267 := bstep (se 1 (by rfl) ⟨1470200, by rfl⟩ : syracuseStep 1960267 = 2940401) B2940401
theorem B2484569 : Blo 1160639 2484569 := bstep (se 2 (by rfl) ⟨931713, by rfl⟩ : syracuseStep 2484569 = 1863427) B1863427
theorem B29747573 : Blo 1160639 29747573 := bstep (se 5 (by rfl) ⟨1394417, by rfl⟩ : syracuseStep 29747573 = 2788835) B2788835
theorem B2615705 : Blo 1160639 2615705 := bstep (se 2 (by rfl) ⟨980889, by rfl⟩ : syracuseStep 2615705 = 1961779) B1961779
theorem B1960409 : Blo 1160639 1960409 := bstep (se 2 (by rfl) ⟨735153, by rfl⟩ : syracuseStep 1960409 = 1470307) B1470307
theorem B2943449 : Blo 1160639 2943449 := bstep (se 2 (by rfl) ⟨1103793, by rfl⟩ : syracuseStep 2943449 = 2207587) B2207587
theorem B2615795 : Blo 1160639 2615795 := bstep (se 1 (by rfl) ⟨1961846, by rfl⟩ : syracuseStep 2615795 = 3923693) B3923693
theorem B2615831 : Blo 1160639 2615831 := bstep (se 1 (by rfl) ⟨1961873, by rfl⟩ : syracuseStep 2615831 = 3923747) B3923747
theorem B1960537 : Blo 1160639 1960537 := bstep (se 2 (by rfl) ⟨735201, by rfl⟩ : syracuseStep 1960537 = 1470403) B1470403
theorem B2616011 : Blo 1160639 2616011 := bstep (se 1 (by rfl) ⟨1962008, by rfl⟩ : syracuseStep 2616011 = 3924017) B3924017
theorem B2616065 : Blo 1160639 2616065 := bstep (se 2 (by rfl) ⟨981024, by rfl⟩ : syracuseStep 2616065 = 1962049) B1962049
theorem B1469335 : Blo 1160639 1469335 := bstep (se 1 (by rfl) ⟨1102001, by rfl⟩ : syracuseStep 1469335 = 2204003) B2204003
theorem B5303191 : Blo 1160639 5303191 := bstep (se 1 (by rfl) ⟨3977393, by rfl⟩ : syracuseStep 5303191 = 7954787) B7954787
theorem B3926987 : Blo 1160639 3926987 := bstep (se 1 (by rfl) ⟨2945240, by rfl⟩ : syracuseStep 3926987 = 5890481) B5890481
theorem B167668697 : Blo 1160639 167668697 := bstep (se 2 (by rfl) ⟨62875761, by rfl⟩ : syracuseStep 167668697 = 125751523) B125751523
theorem B2616281 : Blo 1160639 2616281 := bstep (se 2 (by rfl) ⟨981105, by rfl⟩ : syracuseStep 2616281 = 1962211) B1962211
theorem B2354177 : Blo 1160639 2354177 := bstep (se 2 (by rfl) ⟨882816, by rfl⟩ : syracuseStep 2354177 = 1765633) B1765633
theorem B2616371 : Blo 1160639 2616371 := bstep (se 1 (by rfl) ⟨1962278, by rfl⟩ : syracuseStep 2616371 = 3924557) B3924557
theorem B6614081 : Blo 1160639 6614081 := bstep (se 2 (by rfl) ⟨2480280, by rfl⟩ : syracuseStep 6614081 = 4960561) B4960561
theorem B2485313 : Blo 1160639 2485313 := bstep (se 2 (by rfl) ⟨931992, by rfl⟩ : syracuseStep 2485313 = 1863985) B1863985
theorem B5041217 : Blo 1160639 5041217 := bstep (se 2 (by rfl) ⟨1890456, by rfl⟩ : syracuseStep 5041217 = 3780913) B3780913
theorem B2616407 : Blo 1160639 2616407 := bstep (se 1 (by rfl) ⟨1962305, by rfl⟩ : syracuseStep 2616407 = 3924611) B3924611
theorem B1305751 : Blo 1160639 1305751 := bstep (se 1 (by rfl) ⟨979313, by rfl⟩ : syracuseStep 1305751 = 1958627) B1958627
theorem B1961111 : Blo 1160639 1961111 := bstep (se 1 (by rfl) ⟨1470833, by rfl⟩ : syracuseStep 1961111 = 2941667) B2941667
theorem B4713623 : Blo 1160639 4713623 := bstep (se 1 (by rfl) ⟨3535217, by rfl⟩ : syracuseStep 4713623 = 7070435) B7070435
theorem B3927257 : Blo 1160639 3927257 := bstep (se 2 (by rfl) ⟨1472721, by rfl⟩ : syracuseStep 3927257 = 2945443) B2945443
theorem B4418819 : Blo 1160639 4418819 := bstep (se 1 (by rfl) ⟨3314114, by rfl⟩ : syracuseStep 4418819 = 6628229) B6628229
theorem B2616587 : Blo 1160639 2616587 := bstep (se 1 (by rfl) ⟨1962440, by rfl⟩ : syracuseStep 2616587 = 3924881) B3924881
theorem B4418833 : Blo 1160639 4418833 := bstep (se 2 (by rfl) ⟨1657062, by rfl⟩ : syracuseStep 4418833 = 3314125) B3314125
theorem B1961239 : Blo 1160639 1961239 := bstep (se 1 (by rfl) ⟨1470929, by rfl⟩ : syracuseStep 1961239 = 2941859) B2941859
theorem B2616641 : Blo 1160639 2616641 := bstep (se 2 (by rfl) ⟨981240, by rfl⟩ : syracuseStep 2616641 = 1962481) B1962481
theorem B1305931 : Blo 1160639 1305931 := bstep (se 1 (by rfl) ⟨979448, by rfl⟩ : syracuseStep 1305931 = 1958897) B1958897
theorem B18836837 : Blo 1160639 18836837 := bstep (se 4 (by rfl) ⟨1765953, by rfl⟩ : syracuseStep 18836837 = 3531907) B3531907
theorem B1240439 : Blo 1160639 1240439 := bstep (se 1 (by rfl) ⟨930329, by rfl⟩ : syracuseStep 1240439 = 1860659) B1860659
theorem B1306039 : Blo 1160639 1306039 := bstep (se 1 (by rfl) ⟨979529, by rfl⟩ : syracuseStep 1306039 = 1959059) B1959059
theorem B3534283 : Blo 1160639 3534283 := bstep (se 1 (by rfl) ⟨2650712, by rfl⟩ : syracuseStep 3534283 = 5301425) B5301425
theorem B2420185 : Blo 1160639 2420185 := bstep (se 2 (by rfl) ⟨907569, by rfl⟩ : syracuseStep 2420185 = 1815139) B1815139
theorem B8842769 : Blo 1160639 8842769 := bstep (se 2 (by rfl) ⟨3316038, by rfl⟩ : syracuseStep 8842769 = 6632077) B6632077
theorem B2616857 : Blo 1160639 2616857 := bstep (se 2 (by rfl) ⟨981321, by rfl⟩ : syracuseStep 2616857 = 1962643) B1962643
theorem B4419137 : Blo 1160639 4419137 := bstep (se 2 (by rfl) ⟨1657176, by rfl⟩ : syracuseStep 4419137 = 3314353) B3314353
theorem B1306219 : Blo 1160639 1306219 := bstep (se 1 (by rfl) ⟨979664, by rfl⟩ : syracuseStep 1306219 = 1959329) B1959329
theorem B2616947 : Blo 1160639 2616947 := bstep (se 1 (by rfl) ⟨1962710, by rfl⟩ : syracuseStep 2616947 = 3925421) B3925421
theorem B2616983 : Blo 1160639 2616983 := bstep (se 1 (by rfl) ⟨1962737, by rfl⟩ : syracuseStep 2616983 = 3925475) B3925475
theorem B1863319 : Blo 1160639 1863319 := bstep (se 1 (by rfl) ⟨1397489, by rfl⟩ : syracuseStep 1863319 = 2794979) B2794979
theorem B1306327 : Blo 1160639 1306327 := bstep (se 1 (by rfl) ⟨979745, by rfl⟩ : syracuseStep 1306327 = 1959491) B1959491
theorem B2617163 : Blo 1160639 2617163 := bstep (se 1 (by rfl) ⟨1962872, by rfl⟩ : syracuseStep 2617163 = 3925745) B3925745
theorem B2617217 : Blo 1160639 2617217 := bstep (se 2 (by rfl) ⟨981456, by rfl⟩ : syracuseStep 2617217 = 1962913) B1962913
theorem B1306507 : Blo 1160639 1306507 := bstep (se 1 (by rfl) ⟨979880, by rfl⟩ : syracuseStep 1306507 = 1959761) B1959761
theorem B1961867 : Blo 1160639 1961867 := bstep (se 1 (by rfl) ⟨1471400, by rfl⟩ : syracuseStep 1961867 = 2942801) B2942801
theorem B1863575 : Blo 1160639 1863575 := bstep (se 1 (by rfl) ⟨1397681, by rfl⟩ : syracuseStep 1863575 = 2795363) B2795363
theorem B3927959 : Blo 1160639 3927959 := bstep (se 1 (by rfl) ⟨2945969, by rfl⟩ : syracuseStep 3927959 = 5891939) B5891939
theorem B2125747 : Blo 1160639 2125747 := bstep (se 1 (by rfl) ⟨1594310, by rfl⟩ : syracuseStep 2125747 = 3188621) B3188621
theorem B2486209 : Blo 1160639 2486209 := bstep (se 2 (by rfl) ⟨932328, by rfl⟩ : syracuseStep 2486209 = 1864657) B1864657
theorem B2650099 : Blo 1160639 2650099 := bstep (se 1 (by rfl) ⟨1987574, by rfl⟩ : syracuseStep 2650099 = 3975149) B3975149
theorem B1306615 : Blo 1160639 1306615 := bstep (se 1 (by rfl) ⟨979961, by rfl⟩ : syracuseStep 1306615 = 1959923) B1959923
theorem B1961995 : Blo 1160639 1961995 := bstep (se 1 (by rfl) ⟨1471496, by rfl⟩ : syracuseStep 1961995 = 2942993) B2942993
theorem B14315555 : Blo 1160639 14315555 := bstep (se 1 (by rfl) ⟨10736666, by rfl⟩ : syracuseStep 14315555 = 21473333) B21473333
theorem B2945099 : Blo 1160639 2945099 := bstep (se 1 (by rfl) ⟨2208824, by rfl⟩ : syracuseStep 2945099 = 4417649) B4417649
theorem B2650199 : Blo 1160639 2650199 := bstep (se 1 (by rfl) ⟨1987649, by rfl⟩ : syracuseStep 2650199 = 3975299) B3975299
theorem B2617433 : Blo 1160639 2617433 := bstep (se 2 (by rfl) ⟨981537, by rfl⟩ : syracuseStep 2617433 = 1963075) B1963075
theorem B6549655 : Blo 1160639 6549655 := bstep (se 1 (by rfl) ⟨4912241, by rfl⟩ : syracuseStep 6549655 = 9824483) B9824483
theorem B1962137 : Blo 1160639 1962137 := bstep (se 2 (by rfl) ⟨735801, by rfl⟩ : syracuseStep 1962137 = 1471603) B1471603
theorem B1306795 : Blo 1160639 1306795 := bstep (se 1 (by rfl) ⟨980096, by rfl⟩ : syracuseStep 1306795 = 1960193) B1960193
theorem B2617523 : Blo 1160639 2617523 := bstep (se 1 (by rfl) ⟨1963142, by rfl⟩ : syracuseStep 2617523 = 3926285) B3926285
theorem B2617559 : Blo 1160639 2617559 := bstep (se 1 (by rfl) ⟨1963169, by rfl⟩ : syracuseStep 2617559 = 3926339) B3926339
theorem B4419805 : Blo 1160639 4419805 := bstep (se 3 (by rfl) ⟨828713, by rfl⟩ : syracuseStep 4419805 = 1657427) B1657427
theorem B1306903 : Blo 1160639 1306903 := bstep (se 1 (by rfl) ⟨980177, by rfl⟩ : syracuseStep 1306903 = 1960355) B1960355
theorem B2486551 : Blo 1160639 2486551 := bstep (se 1 (by rfl) ⟨1864913, by rfl⟩ : syracuseStep 2486551 = 3729827) B3729827
theorem B1962265 : Blo 1160639 1962265 := bstep (se 2 (by rfl) ⟨735849, by rfl⟩ : syracuseStep 1962265 = 1471699) B1471699
theorem B5894531 : Blo 1160639 5894531 := bstep (se 1 (by rfl) ⟨4420898, by rfl⟩ : syracuseStep 5894531 = 8841797) B8841797
theorem B2617739 : Blo 1160639 2617739 := bstep (se 1 (by rfl) ⟨1963304, by rfl⟩ : syracuseStep 2617739 = 3926609) B3926609
theorem B3305879 : Blo 1160639 3305879 := bstep (se 1 (by rfl) ⟨2479409, by rfl⟩ : syracuseStep 3305879 = 4958819) B4958819
theorem B3928499 : Blo 1160639 3928499 := bstep (se 1 (by rfl) ⟨2946374, by rfl⟩ : syracuseStep 3928499 = 5892749) B5892749
theorem B2617793 : Blo 1160639 2617793 := bstep (se 2 (by rfl) ⟨981672, by rfl⟩ : syracuseStep 2617793 = 1963345) B1963345
theorem B1307083 : Blo 1160639 1307083 := bstep (se 1 (by rfl) ⟨980312, by rfl⟩ : syracuseStep 1307083 = 1960625) B1960625
theorem B4190737 : Blo 1160639 4190737 := bstep (se 2 (by rfl) ⟨1571526, by rfl⟩ : syracuseStep 4190737 = 3143053) B3143053
theorem B1307191 : Blo 1160639 1307191 := bstep (se 1 (by rfl) ⟨980393, by rfl⟩ : syracuseStep 1307191 = 1960787) B1960787
theorem B1471051 : Blo 1160639 1471051 := bstep (se 1 (by rfl) ⟨1103288, by rfl⟩ : syracuseStep 1471051 = 2206577) B2206577
theorem B2618009 : Blo 1160639 2618009 := bstep (se 2 (by rfl) ⟨981753, by rfl⟩ : syracuseStep 2618009 = 1963507) B1963507
theorem B3928769 : Blo 1160639 3928769 := bstep (se 2 (by rfl) ⟨1473288, by rfl⟩ : syracuseStep 3928769 = 2946577) B2946577
theorem B3142361 : Blo 1160639 3142361 := bstep (se 2 (by rfl) ⟨1178385, by rfl⟩ : syracuseStep 3142361 = 2356771) B2356771
theorem B1307371 : Blo 1160639 1307371 := bstep (se 1 (by rfl) ⟨980528, by rfl⟩ : syracuseStep 1307371 = 1961057) B1961057
theorem B2618099 : Blo 1160639 2618099 := bstep (se 1 (by rfl) ⟨1963574, by rfl⟩ : syracuseStep 2618099 = 3927149) B3927149
theorem B2618135 : Blo 1160639 2618135 := bstep (se 1 (by rfl) ⟨1963601, by rfl⟩ : syracuseStep 2618135 = 3927203) B3927203
theorem B4715309 : Blo 1160639 4715309 := bstep (se 3 (by rfl) ⟨884120, by rfl⟩ : syracuseStep 4715309 = 1768241) B1768241
theorem B7762763 : Blo 1160639 7762763 := bstep (se 1 (by rfl) ⟨5822072, by rfl⟩ : syracuseStep 7762763 = 11644145) B11644145
theorem B2487115 : Blo 1160639 2487115 := bstep (se 1 (by rfl) ⟨1865336, by rfl⟩ : syracuseStep 2487115 = 3730673) B3730673
theorem B1307479 : Blo 1160639 1307479 := bstep (se 1 (by rfl) ⟨980609, by rfl⟩ : syracuseStep 1307479 = 1961219) B1961219
theorem B1962839 : Blo 1160639 1962839 := bstep (se 1 (by rfl) ⟨1472129, by rfl⟩ : syracuseStep 1962839 = 2944259) B2944259
theorem B2618315 : Blo 1160639 2618315 := bstep (se 1 (by rfl) ⟨1963736, by rfl⟩ : syracuseStep 2618315 = 3927473) B3927473
theorem B1962967 : Blo 1160639 1962967 := bstep (se 1 (by rfl) ⟨1472225, by rfl⟩ : syracuseStep 1962967 = 2944451) B2944451
theorem B2618369 : Blo 1160639 2618369 := bstep (se 2 (by rfl) ⟨981888, by rfl⟩ : syracuseStep 2618369 = 1963777) B1963777
theorem B1307659 : Blo 1160639 1307659 := bstep (se 1 (by rfl) ⟨980744, by rfl⟩ : syracuseStep 1307659 = 1961489) B1961489
theorem B2946071 : Blo 1160639 2946071 := bstep (se 1 (by rfl) ⟨2209553, by rfl⟩ : syracuseStep 2946071 = 4419107) B4419107
theorem B2683991 : Blo 1160639 2683991 := bstep (se 1 (by rfl) ⟨2012993, by rfl⟩ : syracuseStep 2683991 = 4025987) B4025987
theorem B1242199 : Blo 1160639 1242199 := bstep (se 1 (by rfl) ⟨931649, by rfl⟩ : syracuseStep 1242199 = 1863299) B1863299
theorem B1307767 : Blo 1160639 1307767 := bstep (se 1 (by rfl) ⟨980825, by rfl⟩ : syracuseStep 1307767 = 1961651) B1961651
theorem B2618585 : Blo 1160639 2618585 := bstep (se 2 (by rfl) ⟨981969, by rfl⟩ : syracuseStep 2618585 = 1963939) B1963939
theorem B3929309 : Blo 1160639 3929309 := bstep (se 3 (by rfl) ⟨736745, by rfl⟩ : syracuseStep 3929309 = 1473491) B1473491
theorem B1307947 : Blo 1160639 1307947 := bstep (se 1 (by rfl) ⟨980960, by rfl⟩ : syracuseStep 1307947 = 1961921) B1961921
theorem B2618675 : Blo 1160639 2618675 := bstep (se 1 (by rfl) ⟨1964006, by rfl⟩ : syracuseStep 2618675 = 3928013) B3928013
theorem B2618711 : Blo 1160639 2618711 := bstep (se 1 (by rfl) ⟨1964033, by rfl⟩ : syracuseStep 2618711 = 3928067) B3928067
theorem B1308055 : Blo 1160639 1308055 := bstep (se 1 (by rfl) ⟨981041, by rfl⟩ : syracuseStep 1308055 = 1962083) B1962083
theorem B3143063 : Blo 1160639 3143063 := bstep (se 1 (by rfl) ⟨2357297, by rfl⟩ : syracuseStep 3143063 = 4714595) B4714595
theorem B5305817 : Blo 1160639 5305817 := bstep (se 2 (by rfl) ⟨1989681, by rfl⟩ : syracuseStep 5305817 = 3979363) B3979363
theorem B4421081 : Blo 1160639 4421081 := bstep (se 2 (by rfl) ⟨1657905, by rfl⟩ : syracuseStep 4421081 = 3315811) B3315811
theorem B2618891 : Blo 1160639 2618891 := bstep (se 1 (by rfl) ⟨1964168, by rfl⟩ : syracuseStep 2618891 = 3928337) B3928337
theorem B1472023 : Blo 1160639 1472023 := bstep (se 1 (by rfl) ⟨1104017, by rfl⟩ : syracuseStep 1472023 = 2208035) B2208035
theorem B2618945 : Blo 1160639 2618945 := bstep (se 2 (by rfl) ⟨982104, by rfl⟩ : syracuseStep 2618945 = 1964209) B1964209
theorem B1308235 : Blo 1160639 1308235 := bstep (se 1 (by rfl) ⟨981176, by rfl⟩ : syracuseStep 1308235 = 1962353) B1962353
theorem B1963595 : Blo 1160639 1963595 := bstep (se 1 (by rfl) ⟨1472696, by rfl⟩ : syracuseStep 1963595 = 2945393) B2945393
theorem B1865369 : Blo 1160639 1865369 := bstep (se 2 (by rfl) ⟨699513, by rfl⟩ : syracuseStep 1865369 = 1399027) B1399027
theorem B2946739 : Blo 1160639 2946739 := bstep (se 1 (by rfl) ⟨2210054, by rfl⟩ : syracuseStep 2946739 = 4420109) B4420109
theorem B1308343 : Blo 1160639 1308343 := bstep (se 1 (by rfl) ⟨981257, by rfl⟩ : syracuseStep 1308343 = 1962515) B1962515
theorem B1963723 : Blo 1160639 1963723 := bstep (se 1 (by rfl) ⟨1472792, by rfl⟩ : syracuseStep 1963723 = 2945585) B2945585
theorem B2619161 : Blo 1160639 2619161 := bstep (se 2 (by rfl) ⟨982185, by rfl⟩ : syracuseStep 2619161 = 1964371) B1964371
theorem B2946881 : Blo 1160639 2946881 := bstep (se 2 (by rfl) ⟨1105080, by rfl⟩ : syracuseStep 2946881 = 2210161) B2210161
theorem B1963865 : Blo 1160639 1963865 := bstep (se 2 (by rfl) ⟨736449, by rfl⟩ : syracuseStep 1963865 = 1472899) B1472899
theorem B1308523 : Blo 1160639 1308523 := bstep (se 1 (by rfl) ⟨981392, by rfl⟩ : syracuseStep 1308523 = 1962785) B1962785
theorem B2619251 : Blo 1160639 2619251 := bstep (se 1 (by rfl) ⟨1964438, by rfl⟩ : syracuseStep 2619251 = 3928877) B3928877
theorem B2619287 : Blo 1160639 2619287 := bstep (se 1 (by rfl) ⟨1964465, by rfl⟩ : syracuseStep 2619287 = 3928931) B3928931
theorem B1308631 : Blo 1160639 1308631 := bstep (se 1 (by rfl) ⟨981473, by rfl⟩ : syracuseStep 1308631 = 1962947) B1962947
theorem B1963993 : Blo 1160639 1963993 := bstep (se 2 (by rfl) ⟨736497, by rfl⟩ : syracuseStep 1963993 = 1472995) B1472995
theorem B8386577 : Blo 1160639 8386577 := bstep (se 2 (by rfl) ⟨3144966, by rfl⟩ : syracuseStep 8386577 = 6289933) B6289933
theorem B2619467 : Blo 1160639 2619467 := bstep (se 1 (by rfl) ⟨1964600, by rfl⟩ : syracuseStep 2619467 = 3929201) B3929201
theorem B1767511 : Blo 1160639 1767511 := bstep (se 1 (by rfl) ⟨1325633, by rfl⟩ : syracuseStep 1767511 = 2651267) B2651267
theorem B2619521 : Blo 1160639 2619521 := bstep (se 2 (by rfl) ⟨982320, by rfl⟩ : syracuseStep 2619521 = 1964641) B1964641
theorem B1308811 : Blo 1160639 1308811 := bstep (se 1 (by rfl) ⟨981608, by rfl⟩ : syracuseStep 1308811 = 1963217) B1963217
theorem B1570969 : Blo 1160639 1570969 := bstep (se 2 (by rfl) ⟨589113, by rfl⟩ : syracuseStep 1570969 = 1178227) B1178227
theorem B22313141 : Blo 1160639 22313141 := bstep (se 5 (by rfl) ⟨1045928, by rfl⟩ : syracuseStep 22313141 = 2091857) B2091857
theorem B4716737 : Blo 1160639 4716737 := bstep (se 2 (by rfl) ⟨1768776, by rfl⟩ : syracuseStep 4716737 = 3537553) B3537553
theorem B1308919 : Blo 1160639 1308919 := bstep (se 1 (by rfl) ⟨981689, by rfl⟩ : syracuseStep 1308919 = 1963379) B1963379
theorem B1472843 : Blo 1160639 1472843 := bstep (se 1 (by rfl) ⟨1104632, by rfl⟩ : syracuseStep 1472843 = 2209265) B2209265
theorem B3930443 : Blo 1160639 3930443 := bstep (se 1 (by rfl) ⟨2947832, by rfl⟩ : syracuseStep 3930443 = 5895665) B5895665
theorem B2619737 : Blo 1160639 2619737 := bstep (se 2 (by rfl) ⟨982401, by rfl⟩ : syracuseStep 2619737 = 1964803) B1964803
theorem B9075037 : Blo 1160639 9075037 := bstep (se 3 (by rfl) ⟨1701569, by rfl⟩ : syracuseStep 9075037 = 3403139) B3403139
theorem B1309099 : Blo 1160639 1309099 := bstep (se 1 (by rfl) ⟨981824, by rfl⟩ : syracuseStep 1309099 = 1963649) B1963649
theorem B2619827 : Blo 1160639 2619827 := bstep (se 1 (by rfl) ⟨1964870, by rfl⟩ : syracuseStep 2619827 = 3929741) B3929741
theorem B2619863 : Blo 1160639 2619863 := bstep (se 1 (by rfl) ⟨1964897, by rfl⟩ : syracuseStep 2619863 = 3929795) B3929795
theorem B1309207 : Blo 1160639 1309207 := bstep (se 1 (by rfl) ⟨981905, by rfl⟩ : syracuseStep 1309207 = 1963811) B1963811
theorem B1964567 : Blo 1160639 1964567 := bstep (se 1 (by rfl) ⟨1473425, by rfl⟩ : syracuseStep 1964567 = 2946851) B2946851
theorem B4192813 : Blo 1160639 4192813 := bstep (se 3 (by rfl) ⟨786152, by rfl⟩ : syracuseStep 4192813 = 1572305) B1572305
theorem B1571467 : Blo 1160639 1571467 := bstep (se 1 (by rfl) ⟨1178600, by rfl⟩ : syracuseStep 1571467 = 2357201) B2357201
theorem B2620043 : Blo 1160639 2620043 := bstep (se 1 (by rfl) ⟨1965032, by rfl⟩ : syracuseStep 2620043 = 3930065) B3930065
theorem B1964695 : Blo 1160639 1964695 := bstep (se 1 (by rfl) ⟨1473521, by rfl⟩ : syracuseStep 1964695 = 2947043) B2947043
theorem B2620097 : Blo 1160639 2620097 := bstep (se 2 (by rfl) ⟨982536, by rfl⟩ : syracuseStep 2620097 = 1965073) B1965073
theorem B1309387 : Blo 1160639 1309387 := bstep (se 1 (by rfl) ⟨982040, by rfl⟩ : syracuseStep 1309387 = 1964081) B1964081
theorem B2095895 : Blo 1160639 2095895 := bstep (se 1 (by rfl) ⟨1571921, by rfl⟩ : syracuseStep 2095895 = 3143843) B3143843
theorem B3308339 : Blo 1160639 3308339 := bstep (se 1 (by rfl) ⟨2481254, by rfl⟩ : syracuseStep 3308339 = 4962509) B4962509
theorem B1309495 : Blo 1160639 1309495 := bstep (se 1 (by rfl) ⟨982121, by rfl⟩ : syracuseStep 1309495 = 1964243) B1964243
theorem B2620313 : Blo 1160639 2620313 := bstep (se 2 (by rfl) ⟨982617, by rfl⟩ : syracuseStep 2620313 = 1965235) B1965235
theorem B1178551 : Blo 1160639 1178551 := bstep (se 1 (by rfl) ⟨883913, by rfl⟩ : syracuseStep 1178551 = 1767827) B1767827
theorem B1309675 : Blo 1160639 1309675 := bstep (se 1 (by rfl) ⟨982256, by rfl⟩ : syracuseStep 1309675 = 1964513) B1964513
theorem B2620403 : Blo 1160639 2620403 := bstep (se 1 (by rfl) ⟨1965302, by rfl⟩ : syracuseStep 2620403 = 3930605) B3930605
theorem B1473547 : Blo 1160639 1473547 := bstep (se 1 (by rfl) ⟨1105160, by rfl⟩ : syracuseStep 1473547 = 2210321) B2210321
theorem B2620439 : Blo 1160639 2620439 := bstep (se 1 (by rfl) ⟨1965329, by rfl⟩ : syracuseStep 2620439 = 3930659) B3930659
theorem B4193345 : Blo 1160639 4193345 := bstep (se 2 (by rfl) ⟨1572504, by rfl⟩ : syracuseStep 4193345 = 3145009) B3145009
theorem B17890379 : Blo 1160639 17890379 := bstep (se 1 (by rfl) ⟨13417784, by rfl⟩ : syracuseStep 17890379 = 26835569) B26835569
theorem B1309783 : Blo 1160639 1309783 := bstep (se 1 (by rfl) ⟨982337, by rfl⟩ : syracuseStep 1309783 = 1964675) B1964675
theorem B2981015 : Blo 1160639 2981015 := bstep (se 1 (by rfl) ⟨2235761, by rfl⟩ : syracuseStep 2981015 = 4471523) B4471523
theorem B2096371 : Blo 1160639 2096371 := bstep (se 1 (by rfl) ⟨1572278, by rfl⟩ : syracuseStep 2096371 = 3144557) B3144557
theorem B1309963 : Blo 1160639 1309963 := bstep (se 1 (by rfl) ⟨982472, by rfl⟩ : syracuseStep 1309963 = 1964945) B1964945
theorem B1965323 : Blo 1160639 1965323 := bstep (se 1 (by rfl) ⟨1473992, by rfl⟩ : syracuseStep 1965323 = 2947985) B2947985
theorem B1473815 : Blo 1160639 1473815 := bstep (se 1 (by rfl) ⟨1105361, by rfl⟩ : syracuseStep 1473815 = 2210723) B2210723
theorem B2096471 : Blo 1160639 2096471 := bstep (se 1 (by rfl) ⟨1572353, by rfl⟩ : syracuseStep 2096471 = 3144707) B3144707
theorem B1310071 : Blo 1160639 1310071 := bstep (se 1 (by rfl) ⟨982553, by rfl⟩ : syracuseStep 1310071 = 1965107) B1965107
theorem B3538379 : Blo 1160639 3538379 := bstep (se 1 (by rfl) ⟨2653784, by rfl⟩ : syracuseStep 3538379 = 5307569) B5307569
theorem B2981569 : Blo 1160639 2981569 := bstep (se 2 (by rfl) ⟨1118088, by rfl⟩ : syracuseStep 2981569 = 2236177) B2236177
theorem B6618955 : Blo 1160639 6618955 := bstep (se 1 (by rfl) ⟨4964216, by rfl⟩ : syracuseStep 6618955 = 9928433) B9928433
theorem B2097047 : Blo 1160639 2097047 := bstep (se 1 (by rfl) ⟨1572785, by rfl⟩ : syracuseStep 2097047 = 3145571) B3145571
theorem B3309569 : Blo 1160639 3309569 := bstep (se 2 (by rfl) ⟨1241088, by rfl⟩ : syracuseStep 3309569 = 2482177) B2482177
theorem B12582973 : Blo 1160639 12582973 := bstep (se 3 (by rfl) ⟨2359307, by rfl⟩ : syracuseStep 12582973 = 4718615) B4718615
theorem B1769719 : Blo 1160639 1769719 := bstep (se 1 (by rfl) ⟨1327289, by rfl⟩ : syracuseStep 1769719 = 2654579) B2654579
theorem B6291749 : Blo 1160639 6291749 := bstep (se 4 (by rfl) ⟨589851, by rfl⟩ : syracuseStep 6291749 = 1179703) B1179703
theorem B2097451 : Blo 1160639 2097451 := bstep (se 1 (by rfl) ⟨1573088, by rfl⟩ : syracuseStep 2097451 = 3146177) B3146177
theorem B6619481 : Blo 1160639 6619481 := bstep (se 2 (by rfl) ⟨2482305, by rfl⟩ : syracuseStep 6619481 = 4964611) B4964611
theorem B1573391 : Blo 1160639 1573391 := bstep (se 1 (by rfl) ⟨1180043, by rfl⟩ : syracuseStep 1573391 = 2360087) B2360087
theorem B3310139 : Blo 1160639 3310139 := bstep (se 1 (by rfl) ⟨2482604, by rfl⟩ : syracuseStep 3310139 = 4965209) B4965209
theorem B1573435 : Blo 1160639 1573435 := bstep (se 1 (by rfl) ⟨1180076, by rfl⟩ : syracuseStep 1573435 = 2360153) B2360153
theorem B3146393 : Blo 1160639 3146393 := bstep (se 2 (by rfl) ⟨1179897, by rfl⟩ : syracuseStep 3146393 = 2359795) B2359795
theorem B3310379 : Blo 1160639 3310379 := bstep (se 1 (by rfl) ⟨2482784, by rfl⟩ : syracuseStep 3310379 = 4965569) B4965569
theorem B1573705 : Blo 1160639 1573705 := bstep (se 2 (by rfl) ⟨590139, by rfl⟩ : syracuseStep 1573705 = 1180279) B1180279
theorem B1770503 : Blo 1160639 1770503 := bstep (se 1 (by rfl) ⟨1327877, by rfl⟩ : syracuseStep 1770503 = 2655755) B2655755
theorem B6292871 : Blo 1160639 6292871 := bstep (se 1 (by rfl) ⟨4719653, by rfl⟩ : syracuseStep 6292871 = 9439307) B9439307
theorem B7079653 : Blo 1160639 7079653 := bstep (se 4 (by rfl) ⟨663717, by rfl⟩ : syracuseStep 7079653 = 1327435) B1327435
theorem B2721911 : Blo 1160639 2721911 := bstep (se 1 (by rfl) ⟨2041433, by rfl⟩ : syracuseStep 2721911 = 4082867) B4082867
theorem B16780067 : Blo 1160639 16780067 := bstep (se 1 (by rfl) ⟨12585050, by rfl⟩ : syracuseStep 16780067 = 25170101) B25170101
theorem B8817497 : Blo 1160639 8817497 := bstep (se 2 (by rfl) ⟨3306561, by rfl⟩ : syracuseStep 8817497 = 6613123) B6613123
theorem B6720401 : Blo 1160639 6720401 := bstep (se 2 (by rfl) ⟨2520150, by rfl⟩ : syracuseStep 6720401 = 5040301) B5040301
theorem B8818469 : Blo 1160639 8818469 := bstep (se 4 (by rfl) ⟨826731, by rfl⟩ : syracuseStep 8818469 = 1653463) B1653463
theorem B37719857 : Blo 1160639 37719857 := bstep (se 2 (by rfl) ⟨14144946, by rfl⟩ : syracuseStep 37719857 = 28289893) B28289893
theorem B5967731 : Blo 1160639 5967731 := bstep (se 1 (by rfl) ⟨4475798, by rfl⟩ : syracuseStep 5967731 = 8951597) B8951597
theorem B6295639 : Blo 1160639 6295639 := bstep (se 1 (by rfl) ⟨4721729, by rfl⟩ : syracuseStep 6295639 = 9443459) B9443459
theorem B1740971 : Blo 1160639 1740971 := bstep (se 1 (by rfl) ⟨1305728, by rfl⟩ : syracuseStep 1740971 = 2611457) B2611457
theorem B1741001 : Blo 1160639 1741001 := bstep (se 2 (by rfl) ⟨652875, by rfl⟩ : syracuseStep 1741001 = 1305751) B1305751
theorem B37753073 : Blo 1160639 37753073 := bstep (se 2 (by rfl) ⟨14157402, by rfl⟩ : syracuseStep 37753073 = 28314805) B28314805
theorem B1741115 : Blo 1160639 1741115 := bstep (se 1 (by rfl) ⟨1305836, by rfl⟩ : syracuseStep 1741115 = 2611673) B2611673
theorem B6623603 : Blo 1160639 6623603 := bstep (se 1 (by rfl) ⟨4967702, by rfl⟩ : syracuseStep 6623603 = 9935405) B9935405
theorem B1741175 : Blo 1160639 1741175 := bstep (se 1 (by rfl) ⟨1305881, by rfl⟩ : syracuseStep 1741175 = 2611763) B2611763
theorem B1741199 : Blo 1160639 1741199 := bstep (se 1 (by rfl) ⟨1305899, by rfl⟩ : syracuseStep 1741199 = 2611799) B2611799
theorem B1741241 : Blo 1160639 1741241 := bstep (se 2 (by rfl) ⟨652965, by rfl⟩ : syracuseStep 1741241 = 1305931) B1305931
theorem B1741319 : Blo 1160639 1741319 := bstep (se 1 (by rfl) ⟨1305989, by rfl⟩ : syracuseStep 1741319 = 2611979) B2611979
theorem B1741355 : Blo 1160639 1741355 := bstep (se 1 (by rfl) ⟨1306016, by rfl⟩ : syracuseStep 1741355 = 2612033) B2612033
theorem B206705195 : Blo 1160639 206705195 := bstep (se 1 (by rfl) ⟨155028896, by rfl⟩ : syracuseStep 206705195 = 310057793) B310057793
theorem B1741385 : Blo 1160639 1741385 := bstep (se 2 (by rfl) ⟨653019, by rfl⟩ : syracuseStep 1741385 = 1306039) B1306039
theorem B1741499 : Blo 1160639 1741499 := bstep (se 1 (by rfl) ⟨1306124, by rfl⟩ : syracuseStep 1741499 = 2612249) B2612249
theorem B1741559 : Blo 1160639 1741559 := bstep (se 1 (by rfl) ⟨1306169, by rfl⟩ : syracuseStep 1741559 = 2612339) B2612339
theorem B1741583 : Blo 1160639 1741583 := bstep (se 1 (by rfl) ⟨1306187, by rfl⟩ : syracuseStep 1741583 = 2612375) B2612375
theorem B31822627 : Blo 1160639 31822627 := bstep (se 1 (by rfl) ⟨23866970, by rfl⟩ : syracuseStep 31822627 = 47733941) B47733941
theorem B7443251 : Blo 1160639 7443251 := bstep (se 1 (by rfl) ⟨5582438, by rfl⟩ : syracuseStep 7443251 = 11164877) B11164877
theorem B1741625 : Blo 1160639 1741625 := bstep (se 2 (by rfl) ⟨653109, by rfl⟩ : syracuseStep 1741625 = 1306219) B1306219
theorem B10064729 : Blo 1160639 10064729 := bstep (se 2 (by rfl) ⟨3774273, by rfl⟩ : syracuseStep 10064729 = 7548547) B7548547
theorem B11932505 : Blo 1160639 11932505 := bstep (se 2 (by rfl) ⟨4474689, by rfl⟩ : syracuseStep 11932505 = 8949379) B8949379
theorem B1741703 : Blo 1160639 1741703 := bstep (se 1 (by rfl) ⟨1306277, by rfl⟩ : syracuseStep 1741703 = 2612555) B2612555
theorem B7443353 : Blo 1160639 7443353 := bstep (se 2 (by rfl) ⟨2791257, by rfl⟩ : syracuseStep 7443353 = 5582515) B5582515
theorem B10621849 : Blo 1160639 10621849 := bstep (se 2 (by rfl) ⟨3983193, by rfl⟩ : syracuseStep 10621849 = 7966387) B7966387
theorem B1741739 : Blo 1160639 1741739 := bstep (se 1 (by rfl) ⟨1306304, by rfl⟩ : syracuseStep 1741739 = 2612609) B2612609
theorem B1741769 : Blo 1160639 1741769 := bstep (se 2 (by rfl) ⟨653163, by rfl⟩ : syracuseStep 1741769 = 1306327) B1306327
theorem B1741883 : Blo 1160639 1741883 := bstep (se 1 (by rfl) ⟨1306412, by rfl⟩ : syracuseStep 1741883 = 2612825) B2612825
theorem B1741943 : Blo 1160639 1741943 := bstep (se 1 (by rfl) ⟨1306457, by rfl⟩ : syracuseStep 1741943 = 2612915) B2612915
theorem B1741967 : Blo 1160639 1741967 := bstep (se 1 (by rfl) ⟨1306475, by rfl⟩ : syracuseStep 1741967 = 2612951) B2612951
theorem B1742009 : Blo 1160639 1742009 := bstep (se 2 (by rfl) ⟨653253, by rfl⟩ : syracuseStep 1742009 = 1306507) B1306507
theorem B3314945 : Blo 1160639 3314945 := bstep (se 2 (by rfl) ⟨1243104, by rfl⟩ : syracuseStep 3314945 = 2486209) B2486209
theorem B1742087 : Blo 1160639 1742087 := bstep (se 1 (by rfl) ⟨1306565, by rfl⟩ : syracuseStep 1742087 = 2613131) B2613131
theorem B2987275 : Blo 1160639 2987275 := bstep (se 1 (by rfl) ⟨2240456, by rfl⟩ : syracuseStep 2987275 = 4480913) B4480913
theorem B1742123 : Blo 1160639 1742123 := bstep (se 1 (by rfl) ⟨1306592, by rfl⟩ : syracuseStep 1742123 = 2613185) B2613185
theorem B1742153 : Blo 1160639 1742153 := bstep (se 2 (by rfl) ⟨653307, by rfl⟩ : syracuseStep 1742153 = 1306615) B1306615
theorem B1742267 : Blo 1160639 1742267 := bstep (se 1 (by rfl) ⟨1306700, by rfl⟩ : syracuseStep 1742267 = 2613401) B2613401
theorem B12588509 : Blo 1160639 12588509 := bstep (se 3 (by rfl) ⟨2360345, by rfl⟩ : syracuseStep 12588509 = 4720691) B4720691
theorem B1742327 : Blo 1160639 1742327 := bstep (se 1 (by rfl) ⟨1306745, by rfl⟩ : syracuseStep 1742327 = 2613491) B2613491
theorem B1742351 : Blo 1160639 1742351 := bstep (se 1 (by rfl) ⟨1306763, by rfl⟩ : syracuseStep 1742351 = 2613527) B2613527
theorem B1742393 : Blo 1160639 1742393 := bstep (se 2 (by rfl) ⟨653397, by rfl⟩ : syracuseStep 1742393 = 1306795) B1306795
theorem B1742471 : Blo 1160639 1742471 := bstep (se 1 (by rfl) ⟨1306853, by rfl⟩ : syracuseStep 1742471 = 2613707) B2613707
theorem B1742507 : Blo 1160639 1742507 := bstep (se 1 (by rfl) ⟨1306880, by rfl⟩ : syracuseStep 1742507 = 2613761) B2613761
theorem B1742537 : Blo 1160639 1742537 := bstep (se 2 (by rfl) ⟨653451, by rfl⟩ : syracuseStep 1742537 = 1306903) B1306903
theorem B3315401 : Blo 1160639 3315401 := bstep (se 2 (by rfl) ⟨1243275, by rfl⟩ : syracuseStep 3315401 = 2486551) B2486551
theorem B6625061 : Blo 1160639 6625061 := bstep (se 4 (by rfl) ⟨621099, by rfl⟩ : syracuseStep 6625061 = 1242199) B1242199
theorem B1742651 : Blo 1160639 1742651 := bstep (se 1 (by rfl) ⟨1306988, by rfl⟩ : syracuseStep 1742651 = 2613977) B2613977
theorem B1742711 : Blo 1160639 1742711 := bstep (se 1 (by rfl) ⟨1307033, by rfl⟩ : syracuseStep 1742711 = 2614067) B2614067
theorem B1742735 : Blo 1160639 1742735 := bstep (se 1 (by rfl) ⟨1307051, by rfl⟩ : syracuseStep 1742735 = 2614103) B2614103
theorem B2987929 : Blo 1160639 2987929 := bstep (se 2 (by rfl) ⟨1120473, by rfl⟩ : syracuseStep 2987929 = 2240947) B2240947
theorem B1742777 : Blo 1160639 1742777 := bstep (se 2 (by rfl) ⟨653541, by rfl⟩ : syracuseStep 1742777 = 1307083) B1307083
theorem B1742855 : Blo 1160639 1742855 := bstep (se 1 (by rfl) ⟨1307141, by rfl⟩ : syracuseStep 1742855 = 2614283) B2614283
theorem B1742891 : Blo 1160639 1742891 := bstep (se 1 (by rfl) ⟨1307168, by rfl⟩ : syracuseStep 1742891 = 2614337) B2614337
theorem B3315755 : Blo 1160639 3315755 := bstep (se 1 (by rfl) ⟨2486816, by rfl⟩ : syracuseStep 3315755 = 4973633) B4973633
theorem B1742921 : Blo 1160639 1742921 := bstep (se 2 (by rfl) ⟨653595, by rfl⟩ : syracuseStep 1742921 = 1307191) B1307191
theorem B1743035 : Blo 1160639 1743035 := bstep (se 1 (by rfl) ⟨1307276, by rfl⟩ : syracuseStep 1743035 = 2614553) B2614553
theorem B1743095 : Blo 1160639 1743095 := bstep (se 1 (by rfl) ⟨1307321, by rfl⟩ : syracuseStep 1743095 = 2614643) B2614643
theorem B1743119 : Blo 1160639 1743119 := bstep (se 1 (by rfl) ⟨1307339, by rfl⟩ : syracuseStep 1743119 = 2614679) B2614679
theorem B1743161 : Blo 1160639 1743161 := bstep (se 2 (by rfl) ⟨653685, by rfl⟩ : syracuseStep 1743161 = 1307371) B1307371
theorem B5970235 : Blo 1160639 5970235 := bstep (se 1 (by rfl) ⟨4477676, by rfl⟩ : syracuseStep 5970235 = 8955353) B8955353
theorem B1743239 : Blo 1160639 1743239 := bstep (se 1 (by rfl) ⟨1307429, by rfl⟩ : syracuseStep 1743239 = 2614859) B2614859
theorem B1743275 : Blo 1160639 1743275 := bstep (se 1 (by rfl) ⟨1307456, by rfl⟩ : syracuseStep 1743275 = 2614913) B2614913
theorem B3316153 : Blo 1160639 3316153 := bstep (se 2 (by rfl) ⟨1243557, by rfl⟩ : syracuseStep 3316153 = 2487115) B2487115
theorem B1743305 : Blo 1160639 1743305 := bstep (se 2 (by rfl) ⟨653739, by rfl⟩ : syracuseStep 1743305 = 1307479) B1307479
theorem B6625745 : Blo 1160639 6625745 := bstep (se 2 (by rfl) ⟨2484654, by rfl⟩ : syracuseStep 6625745 = 4969309) B4969309
theorem B58169821 : Blo 1160639 58169821 := bstep (se 3 (by rfl) ⟨10906841, by rfl⟩ : syracuseStep 58169821 = 21813683) B21813683
theorem B1743419 : Blo 1160639 1743419 := bstep (se 1 (by rfl) ⟨1307564, by rfl⟩ : syracuseStep 1743419 = 2615129) B2615129
theorem B1743479 : Blo 1160639 1743479 := bstep (se 1 (by rfl) ⟨1307609, by rfl⟩ : syracuseStep 1743479 = 2615219) B2615219
theorem B1743503 : Blo 1160639 1743503 := bstep (se 1 (by rfl) ⟨1307627, by rfl⟩ : syracuseStep 1743503 = 2615255) B2615255
theorem B1743545 : Blo 1160639 1743545 := bstep (se 2 (by rfl) ⟨653829, by rfl⟩ : syracuseStep 1743545 = 1307659) B1307659
theorem B1743623 : Blo 1160639 1743623 := bstep (se 1 (by rfl) ⟨1307717, by rfl⟩ : syracuseStep 1743623 = 2615435) B2615435
theorem B6626063 : Blo 1160639 6626063 := bstep (se 1 (by rfl) ⟨4969547, by rfl⟩ : syracuseStep 6626063 = 9939095) B9939095
theorem B1743659 : Blo 1160639 1743659 := bstep (se 1 (by rfl) ⟨1307744, by rfl⟩ : syracuseStep 1743659 = 2615489) B2615489
theorem B1743689 : Blo 1160639 1743689 := bstep (se 2 (by rfl) ⟨653883, by rfl⟩ : syracuseStep 1743689 = 1307767) B1307767
theorem B5970833 : Blo 1160639 5970833 := bstep (se 2 (by rfl) ⟨2239062, by rfl⟩ : syracuseStep 5970833 = 4478125) B4478125
theorem B19831715 : Blo 1160639 19831715 := bstep (se 1 (by rfl) ⟨14873786, by rfl⟩ : syracuseStep 19831715 = 29747573) B29747573
theorem B1743803 : Blo 1160639 1743803 := bstep (se 1 (by rfl) ⟨1307852, by rfl⟩ : syracuseStep 1743803 = 2615705) B2615705
theorem B1743863 : Blo 1160639 1743863 := bstep (se 1 (by rfl) ⟨1307897, by rfl⟩ : syracuseStep 1743863 = 2615795) B2615795
theorem B1743887 : Blo 1160639 1743887 := bstep (se 1 (by rfl) ⟨1307915, by rfl⟩ : syracuseStep 1743887 = 2615831) B2615831
theorem B1743929 : Blo 1160639 1743929 := bstep (se 2 (by rfl) ⟨653973, by rfl⟩ : syracuseStep 1743929 = 1307947) B1307947
theorem B1744007 : Blo 1160639 1744007 := bstep (se 1 (by rfl) ⟨1308005, by rfl⟩ : syracuseStep 1744007 = 2616011) B2616011
theorem B1744043 : Blo 1160639 1744043 := bstep (se 1 (by rfl) ⟨1308032, by rfl⟩ : syracuseStep 1744043 = 2616065) B2616065
theorem B1744073 : Blo 1160639 1744073 := bstep (se 2 (by rfl) ⟨654027, by rfl⟩ : syracuseStep 1744073 = 1308055) B1308055
theorem B111779131 : Blo 1160639 111779131 := bstep (se 1 (by rfl) ⟨83834348, by rfl⟩ : syracuseStep 111779131 = 167668697) B167668697
theorem B1744187 : Blo 1160639 1744187 := bstep (se 1 (by rfl) ⟨1308140, by rfl⟩ : syracuseStep 1744187 = 2616281) B2616281
theorem B1744247 : Blo 1160639 1744247 := bstep (se 1 (by rfl) ⟨1308185, by rfl⟩ : syracuseStep 1744247 = 2616371) B2616371
theorem B1744271 : Blo 1160639 1744271 := bstep (se 1 (by rfl) ⟨1308203, by rfl⟩ : syracuseStep 1744271 = 2616407) B2616407
theorem B1744313 : Blo 1160639 1744313 := bstep (se 2 (by rfl) ⟨654117, by rfl⟩ : syracuseStep 1744313 = 1308235) B1308235
theorem B1744391 : Blo 1160639 1744391 := bstep (se 1 (by rfl) ⟨1308293, by rfl⟩ : syracuseStep 1744391 = 2616587) B2616587
theorem B1744427 : Blo 1160639 1744427 := bstep (se 1 (by rfl) ⟨1308320, by rfl⟩ : syracuseStep 1744427 = 2616641) B2616641
theorem B12557891 : Blo 1160639 12557891 := bstep (se 1 (by rfl) ⟨9418418, by rfl⟩ : syracuseStep 12557891 = 18836837) B18836837
theorem B1744457 : Blo 1160639 1744457 := bstep (se 2 (by rfl) ⟨654171, by rfl⟩ : syracuseStep 1744457 = 1308343) B1308343
theorem B1744571 : Blo 1160639 1744571 := bstep (se 1 (by rfl) ⟨1308428, by rfl⟩ : syracuseStep 1744571 = 2616857) B2616857
theorem B1744631 : Blo 1160639 1744631 := bstep (se 1 (by rfl) ⟨1308473, by rfl⟩ : syracuseStep 1744631 = 2616947) B2616947
theorem B1744655 : Blo 1160639 1744655 := bstep (se 1 (by rfl) ⟨1308491, by rfl⟩ : syracuseStep 1744655 = 2616983) B2616983
theorem B1744697 : Blo 1160639 1744697 := bstep (se 2 (by rfl) ⟨654261, by rfl⟩ : syracuseStep 1744697 = 1308523) B1308523
theorem B1744775 : Blo 1160639 1744775 := bstep (se 1 (by rfl) ⟨1308581, by rfl⟩ : syracuseStep 1744775 = 2617163) B2617163
theorem B1744811 : Blo 1160639 1744811 := bstep (se 1 (by rfl) ⟨1308608, by rfl⟩ : syracuseStep 1744811 = 2617217) B2617217
theorem B1744841 : Blo 1160639 1744841 := bstep (se 2 (by rfl) ⟨654315, by rfl⟩ : syracuseStep 1744841 = 1308631) B1308631
theorem B9543703 : Blo 1160639 9543703 := bstep (se 1 (by rfl) ⟨7157777, by rfl⟩ : syracuseStep 9543703 = 14315555) B14315555
theorem B1744955 : Blo 1160639 1744955 := bstep (se 1 (by rfl) ⟨1308716, by rfl⟩ : syracuseStep 1744955 = 2617433) B2617433
theorem B1745015 : Blo 1160639 1745015 := bstep (se 1 (by rfl) ⟨1308761, by rfl⟩ : syracuseStep 1745015 = 2617523) B2617523
theorem B1745039 : Blo 1160639 1745039 := bstep (se 1 (by rfl) ⟨1308779, by rfl⟩ : syracuseStep 1745039 = 2617559) B2617559
theorem B1745081 : Blo 1160639 1745081 := bstep (se 2 (by rfl) ⟨654405, by rfl⟩ : syracuseStep 1745081 = 1308811) B1308811
theorem B6627521 : Blo 1160639 6627521 := bstep (se 2 (by rfl) ⟨2485320, by rfl⟩ : syracuseStep 6627521 = 4970641) B4970641
theorem B1745159 : Blo 1160639 1745159 := bstep (se 1 (by rfl) ⟨1308869, by rfl⟩ : syracuseStep 1745159 = 2617739) B2617739
theorem B2203919 : Blo 1160639 2203919 := bstep (se 1 (by rfl) ⟨1652939, by rfl⟩ : syracuseStep 2203919 = 3305879) B3305879
theorem B1745195 : Blo 1160639 1745195 := bstep (se 1 (by rfl) ⟨1308896, by rfl⟩ : syracuseStep 1745195 = 2617793) B2617793
theorem B1745225 : Blo 1160639 1745225 := bstep (se 2 (by rfl) ⟨654459, by rfl⟩ : syracuseStep 1745225 = 1308919) B1308919
theorem B1745339 : Blo 1160639 1745339 := bstep (se 1 (by rfl) ⟨1309004, by rfl⟩ : syracuseStep 1745339 = 2618009) B2618009
theorem B12100049 : Blo 1160639 12100049 := bstep (se 2 (by rfl) ⟨4537518, by rfl⟩ : syracuseStep 12100049 = 9075037) B9075037
theorem B1745399 : Blo 1160639 1745399 := bstep (se 1 (by rfl) ⟨1309049, by rfl⟩ : syracuseStep 1745399 = 2618099) B2618099
theorem B1745423 : Blo 1160639 1745423 := bstep (se 1 (by rfl) ⟨1309067, by rfl⟩ : syracuseStep 1745423 = 2618135) B2618135
theorem B1745465 : Blo 1160639 1745465 := bstep (se 2 (by rfl) ⟨654549, by rfl⟩ : syracuseStep 1745465 = 1309099) B1309099
theorem B1745543 : Blo 1160639 1745543 := bstep (se 1 (by rfl) ⟨1309157, by rfl⟩ : syracuseStep 1745543 = 2618315) B2618315
theorem B1745579 : Blo 1160639 1745579 := bstep (se 1 (by rfl) ⟨1309184, by rfl⟩ : syracuseStep 1745579 = 2618369) B2618369
theorem B1745609 : Blo 1160639 1745609 := bstep (se 2 (by rfl) ⟨654603, by rfl⟩ : syracuseStep 1745609 = 1309207) B1309207
theorem B1745723 : Blo 1160639 1745723 := bstep (se 1 (by rfl) ⟨1309292, by rfl⟩ : syracuseStep 1745723 = 2618585) B2618585
theorem B1745783 : Blo 1160639 1745783 := bstep (se 1 (by rfl) ⟨1309337, by rfl⟩ : syracuseStep 1745783 = 2618675) B2618675
theorem B1745807 : Blo 1160639 1745807 := bstep (se 1 (by rfl) ⟨1309355, by rfl⟩ : syracuseStep 1745807 = 2618711) B2618711
theorem B1745849 : Blo 1160639 1745849 := bstep (se 2 (by rfl) ⟨654693, by rfl⟩ : syracuseStep 1745849 = 1309387) B1309387
theorem B25469957 : Blo 1160639 25469957 := bstep (se 4 (by rfl) ⟨2387808, by rfl⟩ : syracuseStep 25469957 = 4775617) B4775617
theorem B1745927 : Blo 1160639 1745927 := bstep (se 1 (by rfl) ⟨1309445, by rfl⟩ : syracuseStep 1745927 = 2618891) B2618891
theorem B1745963 : Blo 1160639 1745963 := bstep (se 1 (by rfl) ⟨1309472, by rfl⟩ : syracuseStep 1745963 = 2618945) B2618945
theorem B1745993 : Blo 1160639 1745993 := bstep (se 2 (by rfl) ⟨654747, by rfl⟩ : syracuseStep 1745993 = 1309495) B1309495
theorem B1746107 : Blo 1160639 1746107 := bstep (se 1 (by rfl) ⟨1309580, by rfl⟩ : syracuseStep 1746107 = 2619161) B2619161
theorem B1746167 : Blo 1160639 1746167 := bstep (se 1 (by rfl) ⟨1309625, by rfl⟩ : syracuseStep 1746167 = 2619251) B2619251
theorem B1746191 : Blo 1160639 1746191 := bstep (se 1 (by rfl) ⟨1309643, by rfl⟩ : syracuseStep 1746191 = 2619287) B2619287
theorem B1746233 : Blo 1160639 1746233 := bstep (se 2 (by rfl) ⟨654837, by rfl⟩ : syracuseStep 1746233 = 1309675) B1309675
theorem B1746311 : Blo 1160639 1746311 := bstep (se 1 (by rfl) ⟨1309733, by rfl⟩ : syracuseStep 1746311 = 2619467) B2619467
theorem B1746347 : Blo 1160639 1746347 := bstep (se 1 (by rfl) ⟨1309760, by rfl⟩ : syracuseStep 1746347 = 2619521) B2619521
theorem B1746377 : Blo 1160639 1746377 := bstep (se 2 (by rfl) ⟨654891, by rfl⟩ : syracuseStep 1746377 = 1309783) B1309783
theorem B14165533 : Blo 1160639 14165533 := bstep (se 3 (by rfl) ⟨2656037, by rfl⟩ : syracuseStep 14165533 = 5312075) B5312075
theorem B1746491 : Blo 1160639 1746491 := bstep (se 1 (by rfl) ⟨1309868, by rfl⟩ : syracuseStep 1746491 = 2619737) B2619737
theorem B1746551 : Blo 1160639 1746551 := bstep (se 1 (by rfl) ⟨1309913, by rfl⟩ : syracuseStep 1746551 = 2619827) B2619827
theorem B1746575 : Blo 1160639 1746575 := bstep (se 1 (by rfl) ⟨1309931, by rfl⟩ : syracuseStep 1746575 = 2619863) B2619863
theorem B2795161 : Blo 1160639 2795161 := bstep (se 2 (by rfl) ⟨1048185, by rfl⟩ : syracuseStep 2795161 = 2096371) B2096371
theorem B1746617 : Blo 1160639 1746617 := bstep (se 2 (by rfl) ⟨654981, by rfl⟩ : syracuseStep 1746617 = 1309963) B1309963
theorem B1746695 : Blo 1160639 1746695 := bstep (se 1 (by rfl) ⟨1310021, by rfl⟩ : syracuseStep 1746695 = 2620043) B2620043
theorem B1746731 : Blo 1160639 1746731 := bstep (se 1 (by rfl) ⟨1310048, by rfl⟩ : syracuseStep 1746731 = 2620097) B2620097
theorem B6367027 : Blo 1160639 6367027 := bstep (se 1 (by rfl) ⟨4775270, by rfl⟩ : syracuseStep 6367027 = 9550541) B9550541
theorem B1746761 : Blo 1160639 1746761 := bstep (se 2 (by rfl) ⟨655035, by rfl⟩ : syracuseStep 1746761 = 1310071) B1310071
theorem B2205559 : Blo 1160639 2205559 := bstep (se 1 (by rfl) ⟨1654169, by rfl⟩ : syracuseStep 2205559 = 3308339) B3308339
theorem B10758041 : Blo 1160639 10758041 := bstep (se 2 (by rfl) ⟨4034265, by rfl⟩ : syracuseStep 10758041 = 8068531) B8068531
theorem B1746875 : Blo 1160639 1746875 := bstep (se 1 (by rfl) ⟨1310156, by rfl⟩ : syracuseStep 1746875 = 2620313) B2620313
theorem B1746935 : Blo 1160639 1746935 := bstep (se 1 (by rfl) ⟨1310201, by rfl⟩ : syracuseStep 1746935 = 2620403) B2620403
theorem B1746959 : Blo 1160639 1746959 := bstep (se 1 (by rfl) ⟨1310219, by rfl⟩ : syracuseStep 1746959 = 2620439) B2620439
theorem B2795563 : Blo 1160639 2795563 := bstep (se 1 (by rfl) ⟨2096672, by rfl⟩ : syracuseStep 2795563 = 4193345) B4193345
theorem B3975425 : Blo 1160639 3975425 := bstep (se 2 (by rfl) ⟨1490784, by rfl⟩ : syracuseStep 3975425 = 2981569) B2981569
theorem B8825273 : Blo 1160639 8825273 := bstep (se 2 (by rfl) ⟨3309477, by rfl⟩ : syracuseStep 8825273 = 6618955) B6618955
theorem B4958749 : Blo 1160639 4958749 := bstep (se 3 (by rfl) ⟨929765, by rfl⟩ : syracuseStep 4958749 = 1859531) B1859531
theorem B4958921 : Blo 1160639 4958921 := bstep (se 2 (by rfl) ⟨1859595, by rfl⟩ : syracuseStep 4958921 = 3719191) B3719191
theorem B5975005 : Blo 1160639 5975005 := bstep (se 3 (by rfl) ⟨1120313, by rfl⟩ : syracuseStep 5975005 = 2240627) B2240627
theorem B14134445 : Blo 1160639 14134445 := bstep (se 3 (by rfl) ⟨2650208, by rfl⟩ : syracuseStep 14134445 = 5300417) B5300417
theorem B12725635 : Blo 1160639 12725635 := bstep (se 1 (by rfl) ⟨9544226, by rfl⟩ : syracuseStep 12725635 = 19088453) B19088453
theorem B12758477 : Blo 1160639 12758477 := bstep (se 3 (by rfl) ⟨2392214, by rfl⟩ : syracuseStep 12758477 = 4784429) B4784429
theorem B14888549 : Blo 1160639 14888549 := bstep (se 4 (by rfl) ⟨1395801, by rfl⟩ : syracuseStep 14888549 = 2791603) B2791603
theorem B2207351 : Blo 1160639 2207351 := bstep (se 1 (by rfl) ⟨1655513, by rfl⟩ : syracuseStep 2207351 = 3311027) B3311027
theorem B2207503 : Blo 1160639 2207503 := bstep (se 1 (by rfl) ⟨1655627, by rfl⟩ : syracuseStep 2207503 = 3311255) B3311255
theorem B21245975 : Blo 1160639 21245975 := bstep (se 1 (by rfl) ⟨15934481, by rfl⟩ : syracuseStep 21245975 = 31868963) B31868963
theorem B2207891 : Blo 1160639 2207891 := bstep (se 1 (by rfl) ⟨1655918, by rfl⟩ : syracuseStep 2207891 = 3311837) B3311837
theorem B5878169 : Blo 1160639 5878169 := bstep (se 2 (by rfl) ⟨2204313, by rfl⟩ : syracuseStep 5878169 = 4408627) B4408627
theorem B1323535 : Blo 1160639 1323535 := bstep (se 1 (by rfl) ⟨992651, by rfl⟩ : syracuseStep 1323535 = 1985303) B1985303
theorem B4960835 : Blo 1160639 4960835 := bstep (se 1 (by rfl) ⟨3720626, by rfl⟩ : syracuseStep 4960835 = 7441253) B7441253
theorem B1160711 : Blo 1160639 1160711 := bstep (se 1 (by rfl) ⟨870533, by rfl⟩ : syracuseStep 1160711 = 1741067) B1741067
theorem B1160719 : Blo 1160639 1160719 := bstep (se 1 (by rfl) ⟨870539, by rfl⟩ : syracuseStep 1160719 = 1741079) B1741079
theorem B2209295 : Blo 1160639 2209295 := bstep (se 1 (by rfl) ⟨1656971, by rfl⟩ : syracuseStep 2209295 = 3313943) B3313943
theorem B1160763 : Blo 1160639 1160763 := bstep (se 1 (by rfl) ⟨870572, by rfl⟩ : syracuseStep 1160763 = 1741145) B1741145
theorem B1324603 : Blo 1160639 1324603 := bstep (se 1 (by rfl) ⟨993452, by rfl⟩ : syracuseStep 1324603 = 1986905) B1986905
theorem B1160839 : Blo 1160639 1160839 := bstep (se 1 (by rfl) ⟨870629, by rfl⟩ : syracuseStep 1160839 = 1741259) B1741259
theorem B1160847 : Blo 1160639 1160847 := bstep (se 1 (by rfl) ⟨870635, by rfl⟩ : syracuseStep 1160847 = 1741271) B1741271
theorem B1160891 : Blo 1160639 1160891 := bstep (se 1 (by rfl) ⟨870668, by rfl⟩ : syracuseStep 1160891 = 1741337) B1741337
theorem B1160967 : Blo 1160639 1160967 := bstep (se 1 (by rfl) ⟨870725, by rfl⟩ : syracuseStep 1160967 = 1741451) B1741451
theorem B1160975 : Blo 1160639 1160975 := bstep (se 1 (by rfl) ⟨870731, by rfl⟩ : syracuseStep 1160975 = 1741463) B1741463
theorem B1161019 : Blo 1160639 1161019 := bstep (se 1 (by rfl) ⟨870764, by rfl⟩ : syracuseStep 1161019 = 1741529) B1741529
theorem B1161095 : Blo 1160639 1161095 := bstep (se 1 (by rfl) ⟨870821, by rfl⟩ : syracuseStep 1161095 = 1741643) B1741643
theorem B1161103 : Blo 1160639 1161103 := bstep (se 1 (by rfl) ⟨870827, by rfl⟩ : syracuseStep 1161103 = 1741655) B1741655
theorem B1161147 : Blo 1160639 1161147 := bstep (se 1 (by rfl) ⟨870860, by rfl⟩ : syracuseStep 1161147 = 1741721) B1741721
theorem B1161223 : Blo 1160639 1161223 := bstep (se 1 (by rfl) ⟨870917, by rfl⟩ : syracuseStep 1161223 = 1741835) B1741835
theorem B1161231 : Blo 1160639 1161231 := bstep (se 1 (by rfl) ⟨870923, by rfl⟩ : syracuseStep 1161231 = 1741847) B1741847
theorem B2209835 : Blo 1160639 2209835 := bstep (se 1 (by rfl) ⟨1657376, by rfl⟩ : syracuseStep 2209835 = 3314753) B3314753
theorem B1161275 : Blo 1160639 1161275 := bstep (se 1 (by rfl) ⟨870956, by rfl⟩ : syracuseStep 1161275 = 1741913) B1741913
theorem B2832499 : Blo 1160639 2832499 := bstep (se 1 (by rfl) ⟨2124374, by rfl⟩ : syracuseStep 2832499 = 4248749) B4248749
theorem B1161351 : Blo 1160639 1161351 := bstep (se 1 (by rfl) ⟨871013, by rfl⟩ : syracuseStep 1161351 = 1742027) B1742027
theorem B1161359 : Blo 1160639 1161359 := bstep (se 1 (by rfl) ⟨871019, by rfl⟩ : syracuseStep 1161359 = 1742039) B1742039
theorem B1161403 : Blo 1160639 1161403 := bstep (se 1 (by rfl) ⟨871052, by rfl⟩ : syracuseStep 1161403 = 1742105) B1742105
theorem B1161479 : Blo 1160639 1161479 := bstep (se 1 (by rfl) ⟨871109, by rfl⟩ : syracuseStep 1161479 = 1742219) B1742219
theorem B1161487 : Blo 1160639 1161487 := bstep (se 1 (by rfl) ⟨871115, by rfl⟩ : syracuseStep 1161487 = 1742231) B1742231
theorem B1161531 : Blo 1160639 1161531 := bstep (se 1 (by rfl) ⟨871148, by rfl⟩ : syracuseStep 1161531 = 1742297) B1742297
theorem B11155805 : Blo 1160639 11155805 := bstep (se 3 (by rfl) ⟨2091713, by rfl⟩ : syracuseStep 11155805 = 4183427) B4183427
theorem B1161607 : Blo 1160639 1161607 := bstep (se 1 (by rfl) ⟨871205, by rfl⟩ : syracuseStep 1161607 = 1742411) B1742411
theorem B1161615 : Blo 1160639 1161615 := bstep (se 1 (by rfl) ⟨871211, by rfl⟩ : syracuseStep 1161615 = 1742423) B1742423
theorem B1161659 : Blo 1160639 1161659 := bstep (se 1 (by rfl) ⟨871244, by rfl⟩ : syracuseStep 1161659 = 1742489) B1742489
theorem B1161735 : Blo 1160639 1161735 := bstep (se 1 (by rfl) ⟨871301, by rfl⟩ : syracuseStep 1161735 = 1742603) B1742603
theorem B7256587 : Blo 1160639 7256587 := bstep (se 1 (by rfl) ⟨5442440, by rfl⟩ : syracuseStep 7256587 = 10884881) B10884881
theorem B1161743 : Blo 1160639 1161743 := bstep (se 1 (by rfl) ⟨871307, by rfl⟩ : syracuseStep 1161743 = 1742615) B1742615
theorem B1161787 : Blo 1160639 1161787 := bstep (se 1 (by rfl) ⟨871340, by rfl⟩ : syracuseStep 1161787 = 1742681) B1742681
theorem B1653367 : Blo 1160639 1653367 := bstep (se 1 (by rfl) ⟨1240025, by rfl⟩ : syracuseStep 1653367 = 2480051) B2480051
theorem B1161863 : Blo 1160639 1161863 := bstep (se 1 (by rfl) ⟨871397, by rfl⟩ : syracuseStep 1161863 = 1742795) B1742795
theorem B1161871 : Blo 1160639 1161871 := bstep (se 1 (by rfl) ⟨871403, by rfl⟩ : syracuseStep 1161871 = 1742807) B1742807
theorem B1161915 : Blo 1160639 1161915 := bstep (se 1 (by rfl) ⟨871436, by rfl⟩ : syracuseStep 1161915 = 1742873) B1742873
theorem B1161991 : Blo 1160639 1161991 := bstep (se 1 (by rfl) ⟨871493, by rfl⟩ : syracuseStep 1161991 = 1742987) B1742987
theorem B1161999 : Blo 1160639 1161999 := bstep (se 1 (by rfl) ⟨871499, by rfl⟩ : syracuseStep 1161999 = 1742999) B1742999
theorem B1162043 : Blo 1160639 1162043 := bstep (se 1 (by rfl) ⟨871532, by rfl⟩ : syracuseStep 1162043 = 1743065) B1743065
theorem B1162119 : Blo 1160639 1162119 := bstep (se 1 (by rfl) ⟨871589, by rfl⟩ : syracuseStep 1162119 = 1743179) B1743179
theorem B1162127 : Blo 1160639 1162127 := bstep (se 1 (by rfl) ⟨871595, by rfl⟩ : syracuseStep 1162127 = 1743191) B1743191
theorem B5880761 : Blo 1160639 5880761 := bstep (se 2 (by rfl) ⟨2205285, by rfl⟩ : syracuseStep 5880761 = 4410571) B4410571
theorem B1653691 : Blo 1160639 1653691 := bstep (se 1 (by rfl) ⟨1240268, by rfl⟩ : syracuseStep 1653691 = 2480537) B2480537
theorem B1162171 : Blo 1160639 1162171 := bstep (se 1 (by rfl) ⟨871628, by rfl⟩ : syracuseStep 1162171 = 1743257) B1743257
theorem B1162247 : Blo 1160639 1162247 := bstep (se 1 (by rfl) ⟨871685, by rfl⟩ : syracuseStep 1162247 = 1743371) B1743371
theorem B1162255 : Blo 1160639 1162255 := bstep (se 1 (by rfl) ⟨871691, by rfl⟩ : syracuseStep 1162255 = 1743383) B1743383
theorem B1162299 : Blo 1160639 1162299 := bstep (se 1 (by rfl) ⟨871724, by rfl⟩ : syracuseStep 1162299 = 1743449) B1743449
theorem B1162375 : Blo 1160639 1162375 := bstep (se 1 (by rfl) ⟨871781, by rfl⟩ : syracuseStep 1162375 = 1743563) B1743563
theorem B2210951 : Blo 1160639 2210951 := bstep (se 1 (by rfl) ⟨1658213, by rfl⟩ : syracuseStep 2210951 = 3316427) B3316427
theorem B1162383 : Blo 1160639 1162383 := bstep (se 1 (by rfl) ⟨871787, by rfl⟩ : syracuseStep 1162383 = 1743575) B1743575
theorem B1162427 : Blo 1160639 1162427 := bstep (se 1 (by rfl) ⟨871820, by rfl⟩ : syracuseStep 1162427 = 1743641) B1743641
theorem B3718345 : Blo 1160639 3718345 := bstep (se 2 (by rfl) ⟨1394379, by rfl⟩ : syracuseStep 3718345 = 2788759) B2788759
theorem B1162503 : Blo 1160639 1162503 := bstep (se 1 (by rfl) ⟨871877, by rfl⟩ : syracuseStep 1162503 = 1743755) B1743755
theorem B1162511 : Blo 1160639 1162511 := bstep (se 1 (by rfl) ⟨871883, by rfl⟩ : syracuseStep 1162511 = 1743767) B1743767
theorem B3226913 : Blo 1160639 3226913 := bstep (se 2 (by rfl) ⟨1210092, by rfl⟩ : syracuseStep 3226913 = 2420185) B2420185
theorem B1162555 : Blo 1160639 1162555 := bstep (se 1 (by rfl) ⟨871916, by rfl⟩ : syracuseStep 1162555 = 1743833) B1743833
theorem B1162631 : Blo 1160639 1162631 := bstep (se 1 (by rfl) ⟨871973, by rfl⟩ : syracuseStep 1162631 = 1743947) B1743947
theorem B1162639 : Blo 1160639 1162639 := bstep (se 1 (by rfl) ⟨871979, by rfl⟩ : syracuseStep 1162639 = 1743959) B1743959
theorem B1162683 : Blo 1160639 1162683 := bstep (se 1 (by rfl) ⟨872012, by rfl⟩ : syracuseStep 1162683 = 1744025) B1744025
theorem B1162759 : Blo 1160639 1162759 := bstep (se 1 (by rfl) ⟨872069, by rfl⟩ : syracuseStep 1162759 = 1744139) B1744139
theorem B1162767 : Blo 1160639 1162767 := bstep (se 1 (by rfl) ⟨872075, by rfl⟩ : syracuseStep 1162767 = 1744151) B1744151
theorem B1162811 : Blo 1160639 1162811 := bstep (se 1 (by rfl) ⟨872108, by rfl⟩ : syracuseStep 1162811 = 1744217) B1744217
theorem B1162887 : Blo 1160639 1162887 := bstep (se 1 (by rfl) ⟨872165, by rfl⟩ : syracuseStep 1162887 = 1744331) B1744331
theorem B1162895 : Blo 1160639 1162895 := bstep (se 1 (by rfl) ⟨872171, by rfl⟩ : syracuseStep 1162895 = 1744343) B1744343
theorem B1162939 : Blo 1160639 1162939 := bstep (se 1 (by rfl) ⟨872204, by rfl⟩ : syracuseStep 1162939 = 1744409) B1744409
theorem B1163015 : Blo 1160639 1163015 := bstep (se 1 (by rfl) ⟨872261, by rfl⟩ : syracuseStep 1163015 = 1744523) B1744523
theorem B1163023 : Blo 1160639 1163023 := bstep (se 1 (by rfl) ⟨872267, by rfl⟩ : syracuseStep 1163023 = 1744535) B1744535
theorem B1163067 : Blo 1160639 1163067 := bstep (se 1 (by rfl) ⟨872300, by rfl⟩ : syracuseStep 1163067 = 1744601) B1744601
theorem B4407155 : Blo 1160639 4407155 := bstep (se 1 (by rfl) ⟨3305366, by rfl⟩ : syracuseStep 4407155 = 6610733) B6610733
theorem B1163143 : Blo 1160639 1163143 := bstep (se 1 (by rfl) ⟨872357, by rfl⟩ : syracuseStep 1163143 = 1744715) B1744715
theorem B1163151 : Blo 1160639 1163151 := bstep (se 1 (by rfl) ⟨872363, by rfl⟩ : syracuseStep 1163151 = 1744727) B1744727
theorem B1163195 : Blo 1160639 1163195 := bstep (se 1 (by rfl) ⟨872396, by rfl⟩ : syracuseStep 1163195 = 1744793) B1744793
theorem B1163271 : Blo 1160639 1163271 := bstep (se 1 (by rfl) ⟨872453, by rfl⟩ : syracuseStep 1163271 = 1744907) B1744907
theorem B1163279 : Blo 1160639 1163279 := bstep (se 1 (by rfl) ⟨872459, by rfl⟩ : syracuseStep 1163279 = 1744919) B1744919
theorem B1163323 : Blo 1160639 1163323 := bstep (se 1 (by rfl) ⟨872492, by rfl⟩ : syracuseStep 1163323 = 1744985) B1744985
theorem B1163399 : Blo 1160639 1163399 := bstep (se 1 (by rfl) ⟨872549, by rfl⟩ : syracuseStep 1163399 = 1745099) B1745099
theorem B1163407 : Blo 1160639 1163407 := bstep (se 1 (by rfl) ⟨872555, by rfl⟩ : syracuseStep 1163407 = 1745111) B1745111
theorem B1163451 : Blo 1160639 1163451 := bstep (se 1 (by rfl) ⟨872588, by rfl⟩ : syracuseStep 1163451 = 1745177) B1745177
theorem B5882057 : Blo 1160639 5882057 := bstep (se 2 (by rfl) ⟨2205771, by rfl⟩ : syracuseStep 5882057 = 4411543) B4411543
theorem B8732873 : Blo 1160639 8732873 := bstep (se 2 (by rfl) ⟨3274827, by rfl⟩ : syracuseStep 8732873 = 6549655) B6549655
theorem B4473089 : Blo 1160639 4473089 := bstep (se 2 (by rfl) ⟨1677408, by rfl⟩ : syracuseStep 4473089 = 3354817) B3354817
theorem B1163527 : Blo 1160639 1163527 := bstep (se 1 (by rfl) ⟨872645, by rfl⟩ : syracuseStep 1163527 = 1745291) B1745291
theorem B1163535 : Blo 1160639 1163535 := bstep (se 1 (by rfl) ⟨872651, by rfl⟩ : syracuseStep 1163535 = 1745303) B1745303
theorem B1163579 : Blo 1160639 1163579 := bstep (se 1 (by rfl) ⟨872684, by rfl⟩ : syracuseStep 1163579 = 1745369) B1745369
theorem B1163655 : Blo 1160639 1163655 := bstep (se 1 (by rfl) ⟨872741, by rfl⟩ : syracuseStep 1163655 = 1745483) B1745483
theorem B1163663 : Blo 1160639 1163663 := bstep (se 1 (by rfl) ⟨872747, by rfl⟩ : syracuseStep 1163663 = 1745495) B1745495
theorem B1163707 : Blo 1160639 1163707 := bstep (se 1 (by rfl) ⟨872780, by rfl⟩ : syracuseStep 1163707 = 1745561) B1745561
theorem B1163783 : Blo 1160639 1163783 := bstep (se 1 (by rfl) ⟨872837, by rfl⟩ : syracuseStep 1163783 = 1745675) B1745675
theorem B1163791 : Blo 1160639 1163791 := bstep (se 1 (by rfl) ⟨872843, by rfl⟩ : syracuseStep 1163791 = 1745687) B1745687
theorem B1163835 : Blo 1160639 1163835 := bstep (se 1 (by rfl) ⟨872876, by rfl⟩ : syracuseStep 1163835 = 1745753) B1745753
theorem B1163911 : Blo 1160639 1163911 := bstep (se 1 (by rfl) ⟨872933, by rfl⟩ : syracuseStep 1163911 = 1745867) B1745867
theorem B1163919 : Blo 1160639 1163919 := bstep (se 1 (by rfl) ⟨872939, by rfl⟩ : syracuseStep 1163919 = 1745879) B1745879
theorem B1163963 : Blo 1160639 1163963 := bstep (se 1 (by rfl) ⟨872972, by rfl⟩ : syracuseStep 1163963 = 1745945) B1745945
theorem B5587649 : Blo 1160639 5587649 := bstep (se 2 (by rfl) ⟨2095368, by rfl⟩ : syracuseStep 5587649 = 4190737) B4190737
theorem B9061121 : Blo 1160639 9061121 := bstep (se 2 (by rfl) ⟨3397920, by rfl⟩ : syracuseStep 9061121 = 6795841) B6795841
theorem B1164039 : Blo 1160639 1164039 := bstep (se 1 (by rfl) ⟨873029, by rfl⟩ : syracuseStep 1164039 = 1746059) B1746059
theorem B1164047 : Blo 1160639 1164047 := bstep (se 1 (by rfl) ⟨873035, by rfl⟩ : syracuseStep 1164047 = 1746071) B1746071
theorem B1164091 : Blo 1160639 1164091 := bstep (se 1 (by rfl) ⟨873068, by rfl⟩ : syracuseStep 1164091 = 1746137) B1746137
theorem B1164167 : Blo 1160639 1164167 := bstep (se 1 (by rfl) ⟨873125, by rfl⟩ : syracuseStep 1164167 = 1746251) B1746251
theorem B1164175 : Blo 1160639 1164175 := bstep (se 1 (by rfl) ⟨873131, by rfl⟩ : syracuseStep 1164175 = 1746263) B1746263
theorem B1164219 : Blo 1160639 1164219 := bstep (se 1 (by rfl) ⟨873164, by rfl⟩ : syracuseStep 1164219 = 1746329) B1746329
theorem B1164295 : Blo 1160639 1164295 := bstep (se 1 (by rfl) ⟨873221, by rfl⟩ : syracuseStep 1164295 = 1746443) B1746443
theorem B1164303 : Blo 1160639 1164303 := bstep (se 1 (by rfl) ⟨873227, by rfl⟩ : syracuseStep 1164303 = 1746455) B1746455
theorem B1164347 : Blo 1160639 1164347 := bstep (se 1 (by rfl) ⟨873260, by rfl⟩ : syracuseStep 1164347 = 1746521) B1746521
theorem B1164423 : Blo 1160639 1164423 := bstep (se 1 (by rfl) ⟨873317, by rfl⟩ : syracuseStep 1164423 = 1746635) B1746635
theorem B1164431 : Blo 1160639 1164431 := bstep (se 1 (by rfl) ⟨873323, by rfl⟩ : syracuseStep 1164431 = 1746647) B1746647
theorem B1164475 : Blo 1160639 1164475 := bstep (se 1 (by rfl) ⟨873356, by rfl⟩ : syracuseStep 1164475 = 1746713) B1746713
theorem B1656055 : Blo 1160639 1656055 := bstep (se 1 (by rfl) ⟨1242041, by rfl⟩ : syracuseStep 1656055 = 2484083) B2484083
theorem B1164551 : Blo 1160639 1164551 := bstep (se 1 (by rfl) ⟨873413, by rfl⟩ : syracuseStep 1164551 = 1746827) B1746827
theorem B1164559 : Blo 1160639 1164559 := bstep (se 1 (by rfl) ⟨873419, by rfl⟩ : syracuseStep 1164559 = 1746839) B1746839
theorem B1164603 : Blo 1160639 1164603 := bstep (se 1 (by rfl) ⟨873452, by rfl⟩ : syracuseStep 1164603 = 1746905) B1746905
theorem B1656379 : Blo 1160639 1656379 := bstep (se 1 (by rfl) ⟨1242284, by rfl⟩ : syracuseStep 1656379 = 2484569) B2484569
theorem B3917753 : Blo 1160639 3917753 := bstep (se 2 (by rfl) ⟨1469157, by rfl⟩ : syracuseStep 3917753 = 2938315) B2938315
theorem B37668887 : Blo 1160639 37668887 := bstep (se 1 (by rfl) ⟨28251665, by rfl⟩ : syracuseStep 37668887 = 56503331) B56503331
theorem B4409387 : Blo 1160639 4409387 := bstep (se 1 (by rfl) ⟨3307040, by rfl⟩ : syracuseStep 4409387 = 6614081) B6614081
theorem B1656875 : Blo 1160639 1656875 := bstep (se 1 (by rfl) ⟨1242656, by rfl⟩ : syracuseStep 1656875 = 2485313) B2485313
theorem B3360811 : Blo 1160639 3360811 := bstep (se 1 (by rfl) ⟨2520608, by rfl⟩ : syracuseStep 3360811 = 5041217) B5041217
theorem B3918347 : Blo 1160639 3918347 := bstep (se 1 (by rfl) ⟨2938760, by rfl⟩ : syracuseStep 3918347 = 5877521) B5877521
theorem B3918455 : Blo 1160639 3918455 := bstep (se 1 (by rfl) ⟨2938841, by rfl⟩ : syracuseStep 3918455 = 5877683) B5877683
theorem B28691587 : Blo 1160639 28691587 := bstep (se 1 (by rfl) ⟨21518690, by rfl⟩ : syracuseStep 28691587 = 43037381) B43037381
theorem B3919049 : Blo 1160639 3919049 := bstep (se 2 (by rfl) ⟨1469643, by rfl⟩ : syracuseStep 3919049 = 2939287) B2939287
theorem B1789327 : Blo 1160639 1789327 := bstep (se 1 (by rfl) ⟨1341995, by rfl⟩ : syracuseStep 1789327 = 2683991) B2683991
theorem B5590417 : Blo 1160639 5590417 := bstep (se 2 (by rfl) ⟨2096406, by rfl⟩ : syracuseStep 5590417 = 4192813) B4192813
theorem B19844837 : Blo 1160639 19844837 := bstep (se 4 (by rfl) ⟨1860453, by rfl⟩ : syracuseStep 19844837 = 3720907) B3720907
theorem B3919751 : Blo 1160639 3919751 := bstep (se 1 (by rfl) ⟨2939813, by rfl⟩ : syracuseStep 3919751 = 5879627) B5879627
theorem B5591051 : Blo 1160639 5591051 := bstep (se 1 (by rfl) ⟨4193288, by rfl⟩ : syracuseStep 5591051 = 8386577) B8386577
theorem B3920129 : Blo 1160639 3920129 := bstep (se 2 (by rfl) ⟨1470048, by rfl⟩ : syracuseStep 3920129 = 2940097) B2940097
theorem B1397263 : Blo 1160639 1397263 := bstep (se 1 (by rfl) ⟨1047947, by rfl⟩ : syracuseStep 1397263 = 2095895) B2095895
theorem B7459447 : Blo 1160639 7459447 := bstep (se 1 (by rfl) ⟨5594585, by rfl⟩ : syracuseStep 7459447 = 11189171) B11189171
theorem B2478863 : Blo 1160639 2478863 := bstep (se 1 (by rfl) ⟨1859147, by rfl⟩ : syracuseStep 2478863 = 3718295) B3718295
theorem B1987343 : Blo 1160639 1987343 := bstep (se 1 (by rfl) ⟨1490507, by rfl⟩ : syracuseStep 1987343 = 2981015) B2981015
theorem B1397647 : Blo 1160639 1397647 := bstep (se 1 (by rfl) ⟨1048235, by rfl⟩ : syracuseStep 1397647 = 2096471) B2096471
theorem B2479033 : Blo 1160639 2479033 := bstep (se 2 (by rfl) ⟨929637, by rfl⟩ : syracuseStep 2479033 = 1859275) B1859275
theorem B3920939 : Blo 1160639 3920939 := bstep (se 1 (by rfl) ⟨2940704, by rfl⟩ : syracuseStep 3920939 = 5881409) B5881409
theorem B5592125 : Blo 1160639 5592125 := bstep (se 3 (by rfl) ⟨1048523, by rfl⟩ : syracuseStep 5592125 = 2097047) B2097047
theorem B2937971 : Blo 1160639 2937971 := bstep (se 1 (by rfl) ⟨2203478, by rfl⟩ : syracuseStep 2937971 = 4406957) B4406957
theorem B2937991 : Blo 1160639 2937991 := bstep (se 1 (by rfl) ⟨2203493, by rfl⟩ : syracuseStep 2937991 = 4406987) B4406987
theorem B4707719 : Blo 1160639 4707719 := bstep (se 1 (by rfl) ⟨3530789, by rfl⟩ : syracuseStep 4707719 = 7061579) B7061579
theorem B4412819 : Blo 1160639 4412819 := bstep (se 1 (by rfl) ⟨3309614, by rfl⟩ : syracuseStep 4412819 = 6619229) B6619229
theorem B2938265 : Blo 1160639 2938265 := bstep (se 2 (by rfl) ⟨1101849, by rfl⟩ : syracuseStep 2938265 = 2203699) B2203699
theorem B2938427 : Blo 1160639 2938427 := bstep (se 1 (by rfl) ⟨2203820, by rfl⟩ : syracuseStep 2938427 = 4407641) B4407641
theorem B7067197 : Blo 1160639 7067197 := bstep (se 3 (by rfl) ⟨1325099, by rfl⟩ : syracuseStep 7067197 = 2650199) B2650199
theorem B2479751 : Blo 1160639 2479751 := bstep (se 1 (by rfl) ⟨1859813, by rfl⟩ : syracuseStep 2479751 = 3719627) B3719627
theorem B1988231 : Blo 1160639 1988231 := bstep (se 1 (by rfl) ⟨1491173, by rfl⟩ : syracuseStep 1988231 = 2982347) B2982347
theorem B2938639 : Blo 1160639 2938639 := bstep (se 1 (by rfl) ⟨2203979, by rfl⟩ : syracuseStep 2938639 = 4407959) B4407959
theorem B5887889 : Blo 1160639 5887889 := bstep (se 2 (by rfl) ⟨2207958, by rfl⟩ : syracuseStep 5887889 = 4415917) B4415917
theorem B9426851 : Blo 1160639 9426851 := bstep (se 1 (by rfl) ⟨7070138, by rfl⟩ : syracuseStep 9426851 = 14140277) B14140277
theorem B21485591 : Blo 1160639 21485591 := bstep (se 1 (by rfl) ⟨16114193, by rfl⟩ : syracuseStep 21485591 = 32228387) B32228387
theorem B2938913 : Blo 1160639 2938913 := bstep (se 2 (by rfl) ⟨1102092, by rfl⟩ : syracuseStep 2938913 = 2204185) B2204185
theorem B2480161 : Blo 1160639 2480161 := bstep (se 2 (by rfl) ⟨930060, by rfl⟩ : syracuseStep 2480161 = 1860121) B1860121
theorem B2513015 : Blo 1160639 2513015 := bstep (se 1 (by rfl) ⟨1884761, by rfl⟩ : syracuseStep 2513015 = 3769523) B3769523
theorem B3922235 : Blo 1160639 3922235 := bstep (se 1 (by rfl) ⟨2941676, by rfl⟩ : syracuseStep 3922235 = 5883353) B5883353
theorem B2480503 : Blo 1160639 2480503 := bstep (se 1 (by rfl) ⟨1860377, by rfl⟩ : syracuseStep 2480503 = 3720755) B3720755
theorem B13228433 : Blo 1160639 13228433 := bstep (se 2 (by rfl) ⟨4960662, by rfl⟩ : syracuseStep 13228433 = 9921325) B9921325
theorem B2611727 : Blo 1160639 2611727 := bstep (se 1 (by rfl) ⟨1958795, by rfl⟩ : syracuseStep 2611727 = 3917591) B3917591
theorem B2611745 : Blo 1160639 2611745 := bstep (se 2 (by rfl) ⟨979404, by rfl⟩ : syracuseStep 2611745 = 1958809) B1958809
theorem B3922721 : Blo 1160639 3922721 := bstep (se 2 (by rfl) ⟨1471020, by rfl⟩ : syracuseStep 3922721 = 2942041) B2942041
theorem B2480939 : Blo 1160639 2480939 := bstep (se 1 (by rfl) ⟨1860704, by rfl⟩ : syracuseStep 2480939 = 3721409) B3721409
theorem B2612087 : Blo 1160639 2612087 := bstep (se 1 (by rfl) ⟨1959065, by rfl⟩ : syracuseStep 2612087 = 3918131) B3918131
theorem B11164567 : Blo 1160639 11164567 := bstep (se 1 (by rfl) ⟨8373425, by rfl⟩ : syracuseStep 11164567 = 16746851) B16746851
theorem B2939915 : Blo 1160639 2939915 := bstep (se 1 (by rfl) ⟨2204936, by rfl⟩ : syracuseStep 2939915 = 4409873) B4409873
theorem B7167005 : Blo 1160639 7167005 := bstep (se 3 (by rfl) ⟨1343813, by rfl⟩ : syracuseStep 7167005 = 2687627) B2687627
theorem B2612267 : Blo 1160639 2612267 := bstep (se 1 (by rfl) ⟨1959200, by rfl⟩ : syracuseStep 2612267 = 3918401) B3918401
theorem B16735319 : Blo 1160639 16735319 := bstep (se 1 (by rfl) ⟨12551489, by rfl⟩ : syracuseStep 16735319 = 25102979) B25102979
theorem B14146849 : Blo 1160639 14146849 := bstep (se 2 (by rfl) ⟨5305068, by rfl⟩ : syracuseStep 14146849 = 10610137) B10610137
theorem B3923315 : Blo 1160639 3923315 := bstep (se 1 (by rfl) ⟨2942486, by rfl⟩ : syracuseStep 3923315 = 5884973) B5884973
theorem B2612627 : Blo 1160639 2612627 := bstep (se 1 (by rfl) ⟨1959470, by rfl⟩ : syracuseStep 2612627 = 3918941) B3918941
theorem B3726739 : Blo 1160639 3726739 := bstep (se 1 (by rfl) ⟨2795054, by rfl⟩ : syracuseStep 3726739 = 5590109) B5590109
theorem B2612681 : Blo 1160639 2612681 := bstep (se 2 (by rfl) ⟨979755, by rfl⟩ : syracuseStep 2612681 = 1959511) B1959511
theorem B4972043 : Blo 1160639 4972043 := bstep (se 1 (by rfl) ⟨3729032, by rfl⟩ : syracuseStep 4972043 = 7458065) B7458065
theorem B2940563 : Blo 1160639 2940563 := bstep (se 1 (by rfl) ⟨2205422, by rfl⟩ : syracuseStep 2940563 = 4410845) B4410845
theorem B7069555 : Blo 1160639 7069555 := bstep (se 1 (by rfl) ⟨5302166, by rfl⟩ : syracuseStep 7069555 = 10604333) B10604333
theorem B4186009 : Blo 1160639 4186009 := bstep (se 2 (by rfl) ⟨1569753, by rfl⟩ : syracuseStep 4186009 = 3139507) B3139507
theorem B2940857 : Blo 1160639 2940857 := bstep (se 2 (by rfl) ⟨1102821, by rfl⟩ : syracuseStep 2940857 = 2205643) B2205643
theorem B4415417 : Blo 1160639 4415417 := bstep (se 2 (by rfl) ⟨1655781, by rfl⟩ : syracuseStep 4415417 = 3311563) B3311563
theorem B5889995 : Blo 1160639 5889995 := bstep (se 1 (by rfl) ⟨4417496, by rfl⟩ : syracuseStep 5889995 = 8834993) B8834993
theorem B11919365 : Blo 1160639 11919365 := bstep (se 4 (by rfl) ⟨1117440, by rfl⟩ : syracuseStep 11919365 = 2234881) B2234881
theorem B2613383 : Blo 1160639 2613383 := bstep (se 1 (by rfl) ⟨1960037, by rfl⟩ : syracuseStep 2613383 = 3920075) B3920075
theorem B5890319 : Blo 1160639 5890319 := bstep (se 1 (by rfl) ⟨4417739, by rfl⟩ : syracuseStep 5890319 = 8835479) B8835479
theorem B2613563 : Blo 1160639 2613563 := bstep (se 1 (by rfl) ⟨1960172, by rfl⟩ : syracuseStep 2613563 = 3920345) B3920345
theorem B2482579 : Blo 1160639 2482579 := bstep (se 1 (by rfl) ⟨1861934, by rfl⟩ : syracuseStep 2482579 = 3723869) B3723869
theorem B2613689 : Blo 1160639 2613689 := bstep (se 2 (by rfl) ⟨980133, by rfl⟩ : syracuseStep 2613689 = 1960267) B1960267
theorem B5300747 : Blo 1160639 5300747 := bstep (se 1 (by rfl) ⟨3975560, by rfl⟩ : syracuseStep 5300747 = 7951121) B7951121
theorem B13263425 : Blo 1160639 13263425 := bstep (se 2 (by rfl) ⟨4973784, by rfl⟩ : syracuseStep 13263425 = 9947569) B9947569
theorem B2941555 : Blo 1160639 2941555 := bstep (se 1 (by rfl) ⟨2206166, by rfl⟩ : syracuseStep 2941555 = 4412333) B4412333
theorem B2941697 : Blo 1160639 2941697 := bstep (se 2 (by rfl) ⟨1103136, by rfl⟩ : syracuseStep 2941697 = 2206273) B2206273
theorem B2614031 : Blo 1160639 2614031 := bstep (se 1 (by rfl) ⟨1960523, by rfl⟩ : syracuseStep 2614031 = 3921047) B3921047
theorem B2614049 : Blo 1160639 2614049 := bstep (se 2 (by rfl) ⟨980268, by rfl⟩ : syracuseStep 2614049 = 1960537) B1960537
theorem B8938291 : Blo 1160639 8938291 := bstep (se 1 (by rfl) ⟨6703718, by rfl⟩ : syracuseStep 8938291 = 13407437) B13407437
theorem B4416403 : Blo 1160639 4416403 := bstep (se 1 (by rfl) ⟨3312302, by rfl⟩ : syracuseStep 4416403 = 6624605) B6624605
theorem B1958971 : Blo 1160639 1958971 := bstep (se 1 (by rfl) ⟨1469228, by rfl⟩ : syracuseStep 1958971 = 2938457) B2938457
theorem B8381501 : Blo 1160639 8381501 := bstep (se 3 (by rfl) ⟨1571531, by rfl⟩ : syracuseStep 8381501 = 3143063) B3143063
theorem B2614391 : Blo 1160639 2614391 := bstep (se 1 (by rfl) ⟨1960793, by rfl⟩ : syracuseStep 2614391 = 3921587) B3921587
theorem B1959113 : Blo 1160639 1959113 := bstep (se 2 (by rfl) ⟨734667, by rfl⟩ : syracuseStep 1959113 = 1469335) B1469335
theorem B2942153 : Blo 1160639 2942153 := bstep (se 2 (by rfl) ⟨1103307, by rfl⟩ : syracuseStep 2942153 = 2206615) B2206615
theorem B7070921 : Blo 1160639 7070921 := bstep (se 2 (by rfl) ⟨2651595, by rfl⟩ : syracuseStep 7070921 = 5303191) B5303191
theorem B3728585 : Blo 1160639 3728585 := bstep (se 2 (by rfl) ⟨1398219, by rfl⟩ : syracuseStep 3728585 = 2796439) B2796439
theorem B13231349 : Blo 1160639 13231349 := bstep (se 5 (by rfl) ⟨620219, by rfl⟩ : syracuseStep 13231349 = 1240439) B1240439
theorem B15099169 : Blo 1160639 15099169 := bstep (se 2 (by rfl) ⟨5662188, by rfl⟩ : syracuseStep 15099169 = 11324377) B11324377
theorem B2614571 : Blo 1160639 2614571 := bstep (se 1 (by rfl) ⟨1960928, by rfl⟩ : syracuseStep 2614571 = 3921857) B3921857
theorem B2942507 : Blo 1160639 2942507 := bstep (se 1 (by rfl) ⟨2206880, by rfl⟩ : syracuseStep 2942507 = 4413761) B4413761
theorem B2614931 : Blo 1160639 2614931 := bstep (se 1 (by rfl) ⟨1961198, by rfl⟩ : syracuseStep 2614931 = 3922397) B3922397
theorem B5891777 : Blo 1160639 5891777 := bstep (se 2 (by rfl) ⟨2209416, by rfl⟩ : syracuseStep 5891777 = 4418833) B4418833
theorem B2614985 : Blo 1160639 2614985 := bstep (se 2 (by rfl) ⟨980619, by rfl⟩ : syracuseStep 2614985 = 1961239) B1961239
theorem B4974317 : Blo 1160639 4974317 := bstep (se 3 (by rfl) ⟨932684, by rfl⟩ : syracuseStep 4974317 = 1865369) B1865369
theorem B1959815 : Blo 1160639 1959815 := bstep (se 1 (by rfl) ⟨1469861, by rfl⟩ : syracuseStep 1959815 = 2939723) B2939723
theorem B3925907 : Blo 1160639 3925907 := bstep (se 1 (by rfl) ⟨2944430, by rfl⟩ : syracuseStep 3925907 = 5888861) B5888861
theorem B4712377 : Blo 1160639 4712377 := bstep (se 2 (by rfl) ⟨1767141, by rfl⟩ : syracuseStep 4712377 = 3534283) B3534283
theorem B2484425 : Blo 1160639 2484425 := bstep (se 2 (by rfl) ⟨931659, by rfl⟩ : syracuseStep 2484425 = 1863319) B1863319
theorem B6285605 : Blo 1160639 6285605 := bstep (se 4 (by rfl) ⟨589275, by rfl⟩ : syracuseStep 6285605 = 1178551) B1178551
theorem B2615687 : Blo 1160639 2615687 := bstep (se 1 (by rfl) ⟨1961765, by rfl⟩ : syracuseStep 2615687 = 3923531) B3923531
theorem B2943499 : Blo 1160639 2943499 := bstep (se 1 (by rfl) ⟨2207624, by rfl⟩ : syracuseStep 2943499 = 4415249) B4415249
theorem B1960463 : Blo 1160639 1960463 := bstep (se 1 (by rfl) ⟨1470347, by rfl⟩ : syracuseStep 1960463 = 2940695) B2940695
theorem B2615867 : Blo 1160639 2615867 := bstep (se 1 (by rfl) ⟨1961900, by rfl⟩ : syracuseStep 2615867 = 3923801) B3923801
theorem B4418135 : Blo 1160639 4418135 := bstep (se 1 (by rfl) ⟨3313601, by rfl⟩ : syracuseStep 4418135 = 6627203) B6627203
theorem B3533465 : Blo 1160639 3533465 := bstep (se 2 (by rfl) ⟨1325049, by rfl⟩ : syracuseStep 3533465 = 2650099) B2650099
theorem B2943641 : Blo 1160639 2943641 := bstep (se 2 (by rfl) ⟨1103865, by rfl⟩ : syracuseStep 2943641 = 2207731) B2207731
theorem B2615993 : Blo 1160639 2615993 := bstep (se 2 (by rfl) ⟨980997, by rfl⟩ : syracuseStep 2615993 = 1961995) B1961995
theorem B1862345 : Blo 1160639 1862345 := bstep (se 2 (by rfl) ⟨698379, by rfl⟩ : syracuseStep 1862345 = 1396759) B1396759
theorem B2943803 : Blo 1160639 2943803 := bstep (se 1 (by rfl) ⟨2207852, by rfl⟩ : syracuseStep 2943803 = 4415705) B4415705
theorem B1239995 : Blo 1160639 1239995 := bstep (se 1 (by rfl) ⟨929996, by rfl⟩ : syracuseStep 1239995 = 1859993) B1859993
theorem B5893073 : Blo 1160639 5893073 := bstep (se 2 (by rfl) ⟨2209902, by rfl⟩ : syracuseStep 5893073 = 4419805) B4419805
theorem B1469431 : Blo 1160639 1469431 := bstep (se 1 (by rfl) ⟨1102073, by rfl⟩ : syracuseStep 1469431 = 2204147) B2204147
theorem B35843077 : Blo 1160639 35843077 := bstep (se 4 (by rfl) ⟨3360288, by rfl⟩ : syracuseStep 35843077 = 6720577) B6720577
theorem B2616335 : Blo 1160639 2616335 := bstep (se 1 (by rfl) ⟨1962251, by rfl⟩ : syracuseStep 2616335 = 3924503) B3924503
theorem B1862671 : Blo 1160639 1862671 := bstep (se 1 (by rfl) ⟨1397003, by rfl⟩ : syracuseStep 1862671 = 2794007) B2794007
theorem B2616353 : Blo 1160639 2616353 := bstep (se 2 (by rfl) ⟨981132, by rfl⟩ : syracuseStep 2616353 = 1962265) B1962265
theorem B1961003 : Blo 1160639 1961003 := bstep (se 1 (by rfl) ⟨1470752, by rfl⟩ : syracuseStep 1961003 = 2941505) B2941505
theorem B4418621 : Blo 1160639 4418621 := bstep (se 3 (by rfl) ⟨828491, by rfl⟩ : syracuseStep 4418621 = 1656983) B1656983
theorem B2944147 : Blo 1160639 2944147 := bstep (se 1 (by rfl) ⟨2208110, by rfl⟩ : syracuseStep 2944147 = 4416221) B4416221
theorem B1305787 : Blo 1160639 1305787 := bstep (se 1 (by rfl) ⟨979340, by rfl⟩ : syracuseStep 1305787 = 1958681) B1958681
theorem B3927311 : Blo 1160639 3927311 := bstep (se 1 (by rfl) ⟨2945483, by rfl⟩ : syracuseStep 3927311 = 5890967) B5890967
theorem B2944289 : Blo 1160639 2944289 := bstep (se 2 (by rfl) ⟨1104108, by rfl⟩ : syracuseStep 2944289 = 2208217) B2208217
theorem B1469755 : Blo 1160639 1469755 := bstep (se 1 (by rfl) ⟨1102316, by rfl⟩ : syracuseStep 1469755 = 2204633) B2204633
theorem B2616695 : Blo 1160639 2616695 := bstep (se 1 (by rfl) ⟨1962521, by rfl⟩ : syracuseStep 2616695 = 3925043) B3925043
theorem B1961401 : Blo 1160639 1961401 := bstep (se 2 (by rfl) ⟨735525, by rfl⟩ : syracuseStep 1961401 = 1471051) B1471051
theorem B3927581 : Blo 1160639 3927581 := bstep (se 3 (by rfl) ⟨736421, by rfl⟩ : syracuseStep 3927581 = 1472843) B1472843
theorem B2616875 : Blo 1160639 2616875 := bstep (se 1 (by rfl) ⟨1962656, by rfl⟩ : syracuseStep 2616875 = 3925313) B3925313
theorem B1306255 : Blo 1160639 1306255 := bstep (se 1 (by rfl) ⟨979691, by rfl⟩ : syracuseStep 1306255 = 1959383) B1959383
theorem B1470251 : Blo 1160639 1470251 := bstep (se 1 (by rfl) ⟨1102688, by rfl⟩ : syracuseStep 1470251 = 2205377) B2205377
theorem B4190087 : Blo 1160639 4190087 := bstep (se 1 (by rfl) ⟨3142565, by rfl⟩ : syracuseStep 4190087 = 6285131) B6285131
theorem B2617235 : Blo 1160639 2617235 := bstep (se 1 (by rfl) ⟨1962926, by rfl⟩ : syracuseStep 2617235 = 3925853) B3925853
theorem B2617289 : Blo 1160639 2617289 := bstep (se 2 (by rfl) ⟨981483, by rfl⟩ : syracuseStep 2617289 = 1962967) B1962967
theorem B6615107 : Blo 1160639 6615107 := bstep (se 1 (by rfl) ⟨4961330, by rfl⟩ : syracuseStep 6615107 = 9922661) B9922661
theorem B1962103 : Blo 1160639 1962103 := bstep (se 1 (by rfl) ⟨1471577, by rfl⟩ : syracuseStep 1962103 = 2943155) B2943155
theorem B1306759 : Blo 1160639 1306759 := bstep (se 1 (by rfl) ⟨980069, by rfl⟩ : syracuseStep 1306759 = 1960139) B1960139
theorem B3141767 : Blo 1160639 3141767 := bstep (se 1 (by rfl) ⟨2356325, by rfl⟩ : syracuseStep 3141767 = 4712651) B4712651
theorem B2945281 : Blo 1160639 2945281 := bstep (se 2 (by rfl) ⟨1104480, by rfl⟩ : syracuseStep 2945281 = 2208961) B2208961
theorem B1470727 : Blo 1160639 1470727 := bstep (se 1 (by rfl) ⟨1103045, by rfl⟩ : syracuseStep 1470727 = 2206091) B2206091
theorem B19853585 : Blo 1160639 19853585 := bstep (se 2 (by rfl) ⟨7445094, by rfl⟩ : syracuseStep 19853585 = 14890189) B14890189
theorem B1306939 : Blo 1160639 1306939 := bstep (se 1 (by rfl) ⟨980204, by rfl⟩ : syracuseStep 1306939 = 1960409) B1960409
theorem B1962299 : Blo 1160639 1962299 := bstep (se 1 (by rfl) ⟨1471724, by rfl⟩ : syracuseStep 1962299 = 2943449) B2943449
theorem B8843741 : Blo 1160639 8843741 := bstep (se 3 (by rfl) ⟨1658201, by rfl⟩ : syracuseStep 8843741 = 3316403) B3316403
theorem B2617991 : Blo 1160639 2617991 := bstep (se 1 (by rfl) ⟨1963493, by rfl⟩ : syracuseStep 2617991 = 3926987) B3926987
theorem B1569451 : Blo 1160639 1569451 := bstep (se 1 (by rfl) ⟨1177088, by rfl⟩ : syracuseStep 1569451 = 2354177) B2354177
theorem B1962697 : Blo 1160639 1962697 := bstep (se 2 (by rfl) ⟨736011, by rfl⟩ : syracuseStep 1962697 = 1472023) B1472023
theorem B1471223 : Blo 1160639 1471223 := bstep (se 1 (by rfl) ⟨1103417, by rfl⟩ : syracuseStep 1471223 = 2206835) B2206835
theorem B1307407 : Blo 1160639 1307407 := bstep (se 1 (by rfl) ⟨980555, by rfl⟩ : syracuseStep 1307407 = 1961111) B1961111
theorem B3142415 : Blo 1160639 3142415 := bstep (se 1 (by rfl) ⟨2356811, by rfl⟩ : syracuseStep 3142415 = 4713623) B4713623
theorem B2618171 : Blo 1160639 2618171 := bstep (se 1 (by rfl) ⟨1963628, by rfl⟩ : syracuseStep 2618171 = 3927257) B3927257
theorem B2945879 : Blo 1160639 2945879 := bstep (se 1 (by rfl) ⟨2209409, by rfl⟩ : syracuseStep 2945879 = 4418819) B4418819
theorem B1471375 : Blo 1160639 1471375 := bstep (se 1 (by rfl) ⟨1103531, by rfl⟩ : syracuseStep 1471375 = 2207063) B2207063
theorem B3928985 : Blo 1160639 3928985 := bstep (se 2 (by rfl) ⟨1473369, by rfl⟩ : syracuseStep 3928985 = 2946739) B2946739
theorem B2618297 : Blo 1160639 2618297 := bstep (se 2 (by rfl) ⟨981861, by rfl⟩ : syracuseStep 2618297 = 1963723) B1963723
theorem B5895179 : Blo 1160639 5895179 := bstep (se 1 (by rfl) ⟨4421384, by rfl⟩ : syracuseStep 5895179 = 8842769) B8842769
theorem B2946091 : Blo 1160639 2946091 := bstep (se 1 (by rfl) ⟨2209568, by rfl⟩ : syracuseStep 2946091 = 4419137) B4419137
theorem B1471547 : Blo 1160639 1471547 := bstep (se 1 (by rfl) ⟨1103660, by rfl⟩ : syracuseStep 1471547 = 2207321) B2207321
theorem B5895341 : Blo 1160639 5895341 := bstep (se 3 (by rfl) ⟨1105376, by rfl⟩ : syracuseStep 5895341 = 2210753) B2210753
theorem B2946233 : Blo 1160639 2946233 := bstep (se 2 (by rfl) ⟨1104837, by rfl⟩ : syracuseStep 2946233 = 2209675) B2209675
theorem B1307911 : Blo 1160639 1307911 := bstep (se 1 (by rfl) ⟨980933, by rfl⟩ : syracuseStep 1307911 = 1961867) B1961867
theorem B1242383 : Blo 1160639 1242383 := bstep (se 1 (by rfl) ⟨931787, by rfl⟩ : syracuseStep 1242383 = 1863575) B1863575
theorem B2618639 : Blo 1160639 2618639 := bstep (se 1 (by rfl) ⟨1963979, by rfl⟩ : syracuseStep 2618639 = 3927959) B3927959
theorem B11171105 : Blo 1160639 11171105 := bstep (se 2 (by rfl) ⟨4189164, by rfl⟩ : syracuseStep 11171105 = 8378329) B8378329
theorem B2618657 : Blo 1160639 2618657 := bstep (se 2 (by rfl) ⟨981996, by rfl⟩ : syracuseStep 2618657 = 1963993) B1963993
theorem B1963399 : Blo 1160639 1963399 := bstep (se 1 (by rfl) ⟨1472549, by rfl⟩ : syracuseStep 1963399 = 2945099) B2945099
theorem B6714809 : Blo 1160639 6714809 := bstep (se 2 (by rfl) ⟨2518053, by rfl⟩ : syracuseStep 6714809 = 5036107) B5036107
theorem B1308091 : Blo 1160639 1308091 := bstep (se 1 (by rfl) ⟨981068, by rfl⟩ : syracuseStep 1308091 = 1962137) B1962137
theorem B2356681 : Blo 1160639 2356681 := bstep (se 2 (by rfl) ⟨883755, by rfl⟩ : syracuseStep 2356681 = 1767511) B1767511
theorem B2094625 : Blo 1160639 2094625 := bstep (se 2 (by rfl) ⟨785484, by rfl⟩ : syracuseStep 2094625 = 1570969) B1570969
theorem B3929687 : Blo 1160639 3929687 := bstep (se 1 (by rfl) ⟨2947265, by rfl⟩ : syracuseStep 3929687 = 5894531) B5894531
theorem B2618999 : Blo 1160639 2618999 := bstep (se 1 (by rfl) ⟨1964249, by rfl⟩ : syracuseStep 2618999 = 3928499) B3928499
theorem B2619179 : Blo 1160639 2619179 := bstep (se 1 (by rfl) ⟨1964384, by rfl⟩ : syracuseStep 2619179 = 3928769) B3928769
theorem B2094907 : Blo 1160639 2094907 := bstep (se 1 (by rfl) ⟨1571180, by rfl⟩ : syracuseStep 2094907 = 3142361) B3142361
theorem B3143539 : Blo 1160639 3143539 := bstep (se 1 (by rfl) ⟨2357654, by rfl⟩ : syracuseStep 3143539 = 4715309) B4715309
theorem B41318261 : Blo 1160639 41318261 := bstep (se 5 (by rfl) ⟨1936793, by rfl⟩ : syracuseStep 41318261 = 3873587) B3873587
theorem B5175175 : Blo 1160639 5175175 := bstep (se 1 (by rfl) ⟨3881381, by rfl⟩ : syracuseStep 5175175 = 7762763) B7762763
theorem B1308559 : Blo 1160639 1308559 := bstep (se 1 (by rfl) ⟨981419, by rfl⟩ : syracuseStep 1308559 = 1962839) B1962839
theorem B1472519 : Blo 1160639 1472519 := bstep (se 1 (by rfl) ⟨1104389, by rfl⟩ : syracuseStep 1472519 = 2208779) B2208779
theorem B1964047 : Blo 1160639 1964047 := bstep (se 1 (by rfl) ⟨1473035, by rfl⟩ : syracuseStep 1964047 = 2946071) B2946071
theorem B3930173 : Blo 1160639 3930173 := bstep (se 3 (by rfl) ⟨736907, by rfl⟩ : syracuseStep 3930173 = 1473815) B1473815
theorem B3307655 : Blo 1160639 3307655 := bstep (se 1 (by rfl) ⟨2480741, by rfl⟩ : syracuseStep 3307655 = 4961483) B4961483
theorem B2619539 : Blo 1160639 2619539 := bstep (se 1 (by rfl) ⟨1964654, by rfl⟩ : syracuseStep 2619539 = 3929309) B3929309
theorem B2947225 : Blo 1160639 2947225 := bstep (se 2 (by rfl) ⟨1105209, by rfl⟩ : syracuseStep 2947225 = 2210419) B2210419
theorem B2095289 : Blo 1160639 2095289 := bstep (se 2 (by rfl) ⟨785733, by rfl⟩ : syracuseStep 2095289 = 1571467) B1571467
theorem B2619593 : Blo 1160639 2619593 := bstep (se 2 (by rfl) ⟨982347, by rfl⟩ : syracuseStep 2619593 = 1964695) B1964695
theorem B3537211 : Blo 1160639 3537211 := bstep (se 1 (by rfl) ⟨2652908, by rfl⟩ : syracuseStep 3537211 = 5305817) B5305817
theorem B2947387 : Blo 1160639 2947387 := bstep (se 1 (by rfl) ⟨2210540, by rfl⟩ : syracuseStep 2947387 = 4421081) B4421081
theorem B6453593 : Blo 1160639 6453593 := bstep (se 2 (by rfl) ⟨2420097, by rfl⟩ : syracuseStep 6453593 = 4840195) B4840195
theorem B1309063 : Blo 1160639 1309063 := bstep (se 1 (by rfl) ⟨981797, by rfl⟩ : syracuseStep 1309063 = 1963595) B1963595
theorem B6617497 : Blo 1160639 6617497 := bstep (se 2 (by rfl) ⟨2481561, by rfl⟩ : syracuseStep 6617497 = 4963123) B4963123
theorem B2947529 : Blo 1160639 2947529 := bstep (se 2 (by rfl) ⟨1105323, by rfl⟩ : syracuseStep 2947529 = 2210647) B2210647
theorem B1964587 : Blo 1160639 1964587 := bstep (se 1 (by rfl) ⟨1473440, by rfl⟩ : syracuseStep 1964587 = 2946881) B2946881
theorem B1309243 : Blo 1160639 1309243 := bstep (se 1 (by rfl) ⟨981932, by rfl⟩ : syracuseStep 1309243 = 1963865) B1963865
theorem B1473167 : Blo 1160639 1473167 := bstep (se 1 (by rfl) ⟨1104875, by rfl⟩ : syracuseStep 1473167 = 2209751) B2209751
theorem B1964729 : Blo 1160639 1964729 := bstep (se 2 (by rfl) ⟨736773, by rfl⟩ : syracuseStep 1964729 = 1473547) B1473547
theorem B2947873 : Blo 1160639 2947873 := bstep (se 2 (by rfl) ⟨1105452, by rfl⟩ : syracuseStep 2947873 = 2210905) B2210905
theorem B14875427 : Blo 1160639 14875427 := bstep (se 1 (by rfl) ⟨11156570, by rfl⟩ : syracuseStep 14875427 = 22313141) B22313141
theorem B3144491 : Blo 1160639 3144491 := bstep (se 1 (by rfl) ⟨2358368, by rfl⟩ : syracuseStep 3144491 = 4716737) B4716737
theorem B2620295 : Blo 1160639 2620295 := bstep (se 1 (by rfl) ⟨1965221, by rfl⟩ : syracuseStep 2620295 = 3930443) B3930443
theorem B5962681 : Blo 1160639 5962681 := bstep (se 2 (by rfl) ⟨2236005, by rfl⟩ : syracuseStep 5962681 = 4472011) B4472011
theorem B1309711 : Blo 1160639 1309711 := bstep (se 1 (by rfl) ⟨982283, by rfl⟩ : syracuseStep 1309711 = 1964567) B1964567
theorem B11926919 : Blo 1160639 11926919 := bstep (se 1 (by rfl) ⟨8945189, by rfl⟩ : syracuseStep 11926919 = 17890379) B17890379
theorem B1310215 : Blo 1160639 1310215 := bstep (se 1 (by rfl) ⟨982661, by rfl⟩ : syracuseStep 1310215 = 1965323) B1965323
theorem B11337317 : Blo 1160639 11337317 := bstep (se 4 (by rfl) ⟨1062873, by rfl⟩ : syracuseStep 11337317 = 2125747) B2125747
theorem B2358919 : Blo 1160639 2358919 := bstep (se 1 (by rfl) ⟨1769189, by rfl⟩ : syracuseStep 2358919 = 3538379) B3538379
theorem B16777297 : Blo 1160639 16777297 := bstep (se 2 (by rfl) ⟨6291486, by rfl⟩ : syracuseStep 16777297 = 12582973) B12582973
theorem B2982059 : Blo 1160639 2982059 := bstep (se 1 (by rfl) ⟨2236544, by rfl⟩ : syracuseStep 2982059 = 4473089) B4473089
theorem B4194499 : Blo 1160639 4194499 := bstep (se 1 (by rfl) ⟨3145874, by rfl⟩ : syracuseStep 4194499 = 6291749) B6291749
theorem B14909669 : Blo 1160639 14909669 := bstep (se 4 (by rfl) ⟨1397781, by rfl⟩ : syracuseStep 14909669 = 2795563) B2795563
theorem B2359625 : Blo 1160639 2359625 := bstep (se 2 (by rfl) ⟨884859, by rfl⟩ : syracuseStep 2359625 = 1769719) B1769719
theorem B2097595 : Blo 1160639 2097595 := bstep (se 1 (by rfl) ⟨1573196, by rfl⟩ : syracuseStep 2097595 = 3146393) B3146393
theorem B3310105 : Blo 1160639 3310105 := bstep (se 2 (by rfl) ⟨1241289, by rfl⟩ : syracuseStep 3310105 = 2482579) B2482579
theorem B2097913 : Blo 1160639 2097913 := bstep (se 2 (by rfl) ⟨786717, by rfl⟩ : syracuseStep 2097913 = 1573435) B1573435
theorem B4195247 : Blo 1160639 4195247 := bstep (se 1 (by rfl) ⟨3146435, by rfl⟩ : syracuseStep 4195247 = 6292871) B6292871
theorem B2098273 : Blo 1160639 2098273 := bstep (se 2 (by rfl) ⟨786852, by rfl⟩ : syracuseStep 2098273 = 1573705) B1573705
theorem B4195709 : Blo 1160639 4195709 := bstep (se 3 (by rfl) ⟨786695, by rfl⟩ : syracuseStep 4195709 = 1573391) B1573391
theorem B9439537 : Blo 1160639 9439537 := bstep (se 2 (by rfl) ⟨3539826, by rfl⟩ : syracuseStep 9439537 = 7079653) B7079653
theorem B8489369 : Blo 1160639 8489369 := bstep (se 2 (by rfl) ⟨3183513, by rfl⟩ : syracuseStep 8489369 = 6367027) B6367027
theorem B4721341 : Blo 1160639 4721341 := bstep (se 3 (by rfl) ⟨885251, by rfl⟩ : syracuseStep 4721341 = 1770503) B1770503
theorem B25168715 : Blo 1160639 25168715 := bstep (se 1 (by rfl) ⟨18876536, by rfl⟩ : syracuseStep 25168715 = 37753073) B37753073
theorem B14912333 : Blo 1160639 14912333 := bstep (se 3 (by rfl) ⟨2796062, by rfl⟩ : syracuseStep 14912333 = 5592125) B5592125
theorem B3313021 : Blo 1160639 3313021 := bstep (se 3 (by rfl) ⟨621191, by rfl⟩ : syracuseStep 3313021 = 1242383) B1242383
theorem B8392339 : Blo 1160639 8392339 := bstep (se 1 (by rfl) ⟨6294254, by rfl⟩ : syracuseStep 8392339 = 12588509) B12588509
theorem B7966673 : Blo 1160639 7966673 := bstep (se 2 (by rfl) ⟨2987502, by rfl⟩ : syracuseStep 7966673 = 5975005) B5975005
theorem B14323727 : Blo 1160639 14323727 := bstep (se 1 (by rfl) ⟨10742795, by rfl⟩ : syracuseStep 14323727 = 21485591) B21485591
theorem B1675343 : Blo 1160639 1675343 := bstep (se 1 (by rfl) ⟨1256507, by rfl⟩ : syracuseStep 1675343 = 2513015) B2513015
theorem B1741049 : Blo 1160639 1741049 := bstep (se 2 (by rfl) ⟨652893, by rfl⟩ : syracuseStep 1741049 = 1305787) B1305787
theorem B8818955 : Blo 1160639 8818955 := bstep (se 1 (by rfl) ⟨6614216, by rfl⟩ : syracuseStep 8818955 = 13228433) B13228433
theorem B1741151 : Blo 1160639 1741151 := bstep (se 1 (by rfl) ⟨1305863, by rfl⟩ : syracuseStep 1741151 = 2611727) B2611727
theorem B1741163 : Blo 1160639 1741163 := bstep (se 1 (by rfl) ⟨1305872, by rfl⟩ : syracuseStep 1741163 = 2611745) B2611745
theorem B1741391 : Blo 1160639 1741391 := bstep (se 1 (by rfl) ⟨1306043, by rfl⟩ : syracuseStep 1741391 = 2612087) B2612087
theorem B1741511 : Blo 1160639 1741511 := bstep (se 1 (by rfl) ⟨1306133, by rfl⟩ : syracuseStep 1741511 = 2612267) B2612267
theorem B1741673 : Blo 1160639 1741673 := bstep (se 2 (by rfl) ⟨653127, by rfl⟩ : syracuseStep 1741673 = 1306255) B1306255
theorem B1741751 : Blo 1160639 1741751 := bstep (se 1 (by rfl) ⟨1306313, by rfl⟩ : syracuseStep 1741751 = 2612627) B2612627
theorem B1741787 : Blo 1160639 1741787 := bstep (se 1 (by rfl) ⟨1306340, by rfl⟩ : syracuseStep 1741787 = 2612681) B2612681
theorem B3314695 : Blo 1160639 3314695 := bstep (se 1 (by rfl) ⟨2486021, by rfl⟩ : syracuseStep 3314695 = 4972043) B4972043
theorem B1742255 : Blo 1160639 1742255 := bstep (se 1 (by rfl) ⟨1306691, by rfl⟩ : syracuseStep 1742255 = 2613383) B2613383
theorem B8394185 : Blo 1160639 8394185 := bstep (se 2 (by rfl) ⟨3147819, by rfl⟩ : syracuseStep 8394185 = 6295639) B6295639
theorem B1742345 : Blo 1160639 1742345 := bstep (se 2 (by rfl) ⟨653379, by rfl⟩ : syracuseStep 1742345 = 1306759) B1306759
theorem B1742375 : Blo 1160639 1742375 := bstep (se 1 (by rfl) ⟨1306781, by rfl⟩ : syracuseStep 1742375 = 2613563) B2613563
theorem B1742459 : Blo 1160639 1742459 := bstep (se 1 (by rfl) ⟨1306844, by rfl⟩ : syracuseStep 1742459 = 2613689) B2613689
theorem B8066699 : Blo 1160639 8066699 := bstep (se 1 (by rfl) ⟨6050024, by rfl⟩ : syracuseStep 8066699 = 12100049) B12100049
theorem B8820413 : Blo 1160639 8820413 := bstep (se 3 (by rfl) ⟨1653827, by rfl⟩ : syracuseStep 8820413 = 3307655) B3307655
theorem B1742585 : Blo 1160639 1742585 := bstep (se 2 (by rfl) ⟨653469, by rfl⟩ : syracuseStep 1742585 = 1306939) B1306939
theorem B1742687 : Blo 1160639 1742687 := bstep (se 1 (by rfl) ⟨1307015, by rfl⟩ : syracuseStep 1742687 = 2614031) B2614031
theorem B1742699 : Blo 1160639 1742699 := bstep (se 1 (by rfl) ⟨1307024, by rfl⟩ : syracuseStep 1742699 = 2614049) B2614049
theorem B16979971 : Blo 1160639 16979971 := bstep (se 1 (by rfl) ⟨12734978, by rfl⟩ : syracuseStep 16979971 = 25469957) B25469957
theorem B1742927 : Blo 1160639 1742927 := bstep (se 1 (by rfl) ⟨1307195, by rfl⟩ : syracuseStep 1742927 = 2614391) B2614391
theorem B8820899 : Blo 1160639 8820899 := bstep (se 1 (by rfl) ⟨6615674, by rfl⟩ : syracuseStep 8820899 = 13231349) B13231349
theorem B1743047 : Blo 1160639 1743047 := bstep (se 1 (by rfl) ⟨1307285, by rfl⟩ : syracuseStep 1743047 = 2614571) B2614571
theorem B1743209 : Blo 1160639 1743209 := bstep (se 2 (by rfl) ⟨653703, by rfl⟩ : syracuseStep 1743209 = 1307407) B1307407
theorem B1743287 : Blo 1160639 1743287 := bstep (se 1 (by rfl) ⟨1307465, by rfl⟩ : syracuseStep 1743287 = 2614931) B2614931
theorem B1743323 : Blo 1160639 1743323 := bstep (se 1 (by rfl) ⟨1307492, by rfl⟩ : syracuseStep 1743323 = 2614985) B2614985
theorem B3316211 : Blo 1160639 3316211 := bstep (se 1 (by rfl) ⟨2487158, by rfl⟩ : syracuseStep 3316211 = 4974317) B4974317
theorem B14162465 : Blo 1160639 14162465 := bstep (se 2 (by rfl) ⟨5310924, by rfl⟩ : syracuseStep 14162465 = 10621849) B10621849
theorem B1743791 : Blo 1160639 1743791 := bstep (se 1 (by rfl) ⟨1307843, by rfl⟩ : syracuseStep 1743791 = 2615687) B2615687
theorem B1743881 : Blo 1160639 1743881 := bstep (se 2 (by rfl) ⟨653955, by rfl⟩ : syracuseStep 1743881 = 1307911) B1307911
theorem B1743911 : Blo 1160639 1743911 := bstep (se 1 (by rfl) ⟨1307933, by rfl⟩ : syracuseStep 1743911 = 2615867) B2615867
theorem B1743995 : Blo 1160639 1743995 := bstep (se 1 (by rfl) ⟨1307996, by rfl⟩ : syracuseStep 1743995 = 2615993) B2615993
theorem B1744121 : Blo 1160639 1744121 := bstep (se 2 (by rfl) ⟨654045, by rfl⟩ : syracuseStep 1744121 = 1308091) B1308091
theorem B1744223 : Blo 1160639 1744223 := bstep (se 1 (by rfl) ⟨1308167, by rfl⟩ : syracuseStep 1744223 = 2616335) B2616335
theorem B1744235 : Blo 1160639 1744235 := bstep (se 1 (by rfl) ⟨1308176, by rfl⟩ : syracuseStep 1744235 = 2616353) B2616353
theorem B1744463 : Blo 1160639 1744463 := bstep (se 1 (by rfl) ⟨1308347, by rfl⟩ : syracuseStep 1744463 = 2616695) B2616695
theorem B1744583 : Blo 1160639 1744583 := bstep (se 1 (by rfl) ⟨1308437, by rfl⟩ : syracuseStep 1744583 = 2616875) B2616875
theorem B2793209 : Blo 1160639 2793209 := bstep (se 2 (by rfl) ⟨1047453, by rfl⟩ : syracuseStep 2793209 = 2094907) B2094907
theorem B1744745 : Blo 1160639 1744745 := bstep (se 2 (by rfl) ⟨654279, by rfl⟩ : syracuseStep 1744745 = 1308559) B1308559
theorem B1744823 : Blo 1160639 1744823 := bstep (se 1 (by rfl) ⟨1308617, by rfl⟩ : syracuseStep 1744823 = 2617235) B2617235
theorem B1744859 : Blo 1160639 1744859 := bstep (se 1 (by rfl) ⟨1308644, by rfl⟩ : syracuseStep 1744859 = 2617289) B2617289
theorem B14163983 : Blo 1160639 14163983 := bstep (se 1 (by rfl) ⟨10622987, by rfl⟩ : syracuseStep 14163983 = 21245975) B21245975
theorem B3776665 : Blo 1160639 3776665 := bstep (se 2 (by rfl) ⟨1416249, by rfl⟩ : syracuseStep 3776665 = 2832499) B2832499
theorem B1745327 : Blo 1160639 1745327 := bstep (se 1 (by rfl) ⟨1308995, by rfl⟩ : syracuseStep 1745327 = 2617991) B2617991
theorem B1745417 : Blo 1160639 1745417 := bstep (se 2 (by rfl) ⟨654531, by rfl⟩ : syracuseStep 1745417 = 1309063) B1309063
theorem B8823329 : Blo 1160639 8823329 := bstep (se 2 (by rfl) ⟨3308748, by rfl⟩ : syracuseStep 8823329 = 6617497) B6617497
theorem B1745447 : Blo 1160639 1745447 := bstep (se 1 (by rfl) ⟨1309085, by rfl⟩ : syracuseStep 1745447 = 2618171) B2618171
theorem B1745531 : Blo 1160639 1745531 := bstep (se 1 (by rfl) ⟨1309148, by rfl⟩ : syracuseStep 1745531 = 2618297) B2618297
theorem B9675449 : Blo 1160639 9675449 := bstep (se 2 (by rfl) ⟨3628293, by rfl⟩ : syracuseStep 9675449 = 7256587) B7256587
theorem B1745657 : Blo 1160639 1745657 := bstep (se 2 (by rfl) ⟨654621, by rfl⟩ : syracuseStep 1745657 = 1309243) B1309243
theorem B2204489 : Blo 1160639 2204489 := bstep (se 2 (by rfl) ⟨826683, by rfl⟩ : syracuseStep 2204489 = 1653367) B1653367
theorem B1745759 : Blo 1160639 1745759 := bstep (se 1 (by rfl) ⟨1309319, by rfl⟩ : syracuseStep 1745759 = 2618639) B2618639
theorem B7447403 : Blo 1160639 7447403 := bstep (se 1 (by rfl) ⟨5585552, by rfl⟩ : syracuseStep 7447403 = 11171105) B11171105
theorem B1745771 : Blo 1160639 1745771 := bstep (se 1 (by rfl) ⟨1309328, by rfl⟩ : syracuseStep 1745771 = 2618657) B2618657
theorem B1745999 : Blo 1160639 1745999 := bstep (se 1 (by rfl) ⟨1309499, by rfl⟩ : syracuseStep 1745999 = 2618999) B2618999
theorem B1746119 : Blo 1160639 1746119 := bstep (se 1 (by rfl) ⟨1309589, by rfl⟩ : syracuseStep 1746119 = 2619179) B2619179
theorem B14886089 : Blo 1160639 14886089 := bstep (se 2 (by rfl) ⟨5582283, by rfl⟩ : syracuseStep 14886089 = 11164567) B11164567
theorem B34022605 : Blo 1160639 34022605 := bstep (se 3 (by rfl) ⟨6379238, by rfl⟩ : syracuseStep 34022605 = 12758477) B12758477
theorem B2204921 : Blo 1160639 2204921 := bstep (se 2 (by rfl) ⟨826845, by rfl⟩ : syracuseStep 2204921 = 1653691) B1653691
theorem B1746281 : Blo 1160639 1746281 := bstep (se 2 (by rfl) ⟨654855, by rfl⟩ : syracuseStep 1746281 = 1309711) B1309711
theorem B1746359 : Blo 1160639 1746359 := bstep (se 1 (by rfl) ⟨1309769, by rfl⟩ : syracuseStep 1746359 = 2619539) B2619539
theorem B1746395 : Blo 1160639 1746395 := bstep (se 1 (by rfl) ⟨1309796, by rfl⟩ : syracuseStep 1746395 = 2619593) B2619593
theorem B4302395 : Blo 1160639 4302395 := bstep (se 1 (by rfl) ⟨3226796, by rfl⟩ : syracuseStep 4302395 = 6453593) B6453593
theorem B4957793 : Blo 1160639 4957793 := bstep (se 2 (by rfl) ⟨1859172, by rfl⟩ : syracuseStep 4957793 = 3718345) B3718345
theorem B149038841 : Blo 1160639 149038841 := bstep (se 2 (by rfl) ⟨55889565, by rfl⟩ : syracuseStep 149038841 = 111779131) B111779131
theorem B1746863 : Blo 1160639 1746863 := bstep (se 1 (by rfl) ⟨1310147, by rfl⟩ : syracuseStep 1746863 = 2620295) B2620295
theorem B1746953 : Blo 1160639 1746953 := bstep (se 2 (by rfl) ⟨655107, by rfl⟩ : syracuseStep 1746953 = 1310215) B1310215
theorem B5581345 : Blo 1160639 5581345 := bstep (se 2 (by rfl) ⟨2093004, by rfl⟩ : syracuseStep 5581345 = 4186009) B4186009
theorem B2206379 : Blo 1160639 2206379 := bstep (se 1 (by rfl) ⟨1654784, by rfl⟩ : syracuseStep 2206379 = 3309569) B3309569
theorem B12724937 : Blo 1160639 12724937 := bstep (se 2 (by rfl) ⟨4771851, by rfl⟩ : syracuseStep 12724937 = 9543703) B9543703
theorem B2206759 : Blo 1160639 2206759 := bstep (se 1 (by rfl) ⟨1655069, by rfl⟩ : syracuseStep 2206759 = 3310139) B3310139
theorem B2796601 : Blo 1160639 2796601 := bstep (se 2 (by rfl) ⟨1048725, by rfl⟩ : syracuseStep 2796601 = 2097451) B2097451
theorem B6040747 : Blo 1160639 6040747 := bstep (se 1 (by rfl) ⟨4530560, by rfl⟩ : syracuseStep 6040747 = 9061121) B9061121
theorem B2206919 : Blo 1160639 2206919 := bstep (se 1 (by rfl) ⟨1655189, by rfl⟩ : syracuseStep 2206919 = 3310379) B3310379
theorem B25112591 : Blo 1160639 25112591 := bstep (se 1 (by rfl) ⟨18834443, by rfl⟩ : syracuseStep 25112591 = 37668887) B37668887
theorem B2208073 : Blo 1160639 2208073 := bstep (se 2 (by rfl) ⟨828027, by rfl⟩ : syracuseStep 2208073 = 1656055) B1656055
theorem B20132225 : Blo 1160639 20132225 := bstep (se 2 (by rfl) ⟨7549584, by rfl⟩ : syracuseStep 20132225 = 15099169) B15099169
theorem B11186711 : Blo 1160639 11186711 := bstep (se 1 (by rfl) ⟨8390033, by rfl⟩ : syracuseStep 11186711 = 16780067) B16780067
theorem B5878331 : Blo 1160639 5878331 := bstep (se 1 (by rfl) ⟨4408748, by rfl⟩ : syracuseStep 5878331 = 8817497) B8817497
theorem B18887377 : Blo 1160639 18887377 := bstep (se 2 (by rfl) ⟨7082766, by rfl⟩ : syracuseStep 18887377 = 14165533) B14165533
theorem B5878979 : Blo 1160639 5878979 := bstep (se 1 (by rfl) ⟨4409234, by rfl⟩ : syracuseStep 5878979 = 8818469) B8818469
theorem B25146571 : Blo 1160639 25146571 := bstep (se 1 (by rfl) ⟨18859928, by rfl⟩ : syracuseStep 25146571 = 37719857) B37719857
theorem B3978487 : Blo 1160639 3978487 := bstep (se 1 (by rfl) ⟨2983865, by rfl⟩ : syracuseStep 3978487 = 5967731) B5967731
theorem B1160647 : Blo 1160639 1160647 := bstep (se 1 (by rfl) ⟨870485, by rfl⟩ : syracuseStep 1160647 = 1740971) B1740971
theorem B1160667 : Blo 1160639 1160667 := bstep (se 1 (by rfl) ⟨870500, by rfl⟩ : syracuseStep 1160667 = 1741001) B1741001
theorem B1160743 : Blo 1160639 1160743 := bstep (se 1 (by rfl) ⟨870557, by rfl⟩ : syracuseStep 1160743 = 1741115) B1741115
theorem B1160783 : Blo 1160639 1160783 := bstep (se 1 (by rfl) ⟨870587, by rfl⟩ : syracuseStep 1160783 = 1741175) B1741175
theorem B1160799 : Blo 1160639 1160799 := bstep (se 1 (by rfl) ⟨870599, by rfl⟩ : syracuseStep 1160799 = 1741199) B1741199
theorem B1160827 : Blo 1160639 1160827 := bstep (se 1 (by rfl) ⟨870620, by rfl⟩ : syracuseStep 1160827 = 1741241) B1741241
theorem B1160879 : Blo 1160639 1160879 := bstep (se 1 (by rfl) ⟨870659, by rfl⟩ : syracuseStep 1160879 = 1741319) B1741319
theorem B34420405 : Blo 1160639 34420405 := bstep (se 5 (by rfl) ⟨1613456, by rfl⟩ : syracuseStep 34420405 = 3226913) B3226913
theorem B1160903 : Blo 1160639 1160903 := bstep (se 1 (by rfl) ⟨870677, by rfl⟩ : syracuseStep 1160903 = 1741355) B1741355
theorem B137803463 : Blo 1160639 137803463 := bstep (se 1 (by rfl) ⟨103352597, by rfl⟩ : syracuseStep 137803463 = 206705195) B206705195
theorem B1160923 : Blo 1160639 1160923 := bstep (se 1 (by rfl) ⟨870692, by rfl⟩ : syracuseStep 1160923 = 1741385) B1741385
theorem B1160999 : Blo 1160639 1160999 := bstep (se 1 (by rfl) ⟨870749, by rfl⟩ : syracuseStep 1160999 = 1741499) B1741499
theorem B1161039 : Blo 1160639 1161039 := bstep (se 1 (by rfl) ⟨870779, by rfl⟩ : syracuseStep 1161039 = 1741559) B1741559
theorem B1652575 : Blo 1160639 1652575 := bstep (se 1 (by rfl) ⟨1239431, by rfl⟩ : syracuseStep 1652575 = 2478863) B2478863
theorem B1161055 : Blo 1160639 1161055 := bstep (se 1 (by rfl) ⟨870791, by rfl⟩ : syracuseStep 1161055 = 1741583) B1741583
theorem B1324895 : Blo 1160639 1324895 := bstep (se 1 (by rfl) ⟨993671, by rfl⟩ : syracuseStep 1324895 = 1987343) B1987343
theorem B4962167 : Blo 1160639 4962167 := bstep (se 1 (by rfl) ⟨3721625, by rfl⟩ : syracuseStep 4962167 = 7443251) B7443251
theorem B1161083 : Blo 1160639 1161083 := bstep (se 1 (by rfl) ⟨870812, by rfl⟩ : syracuseStep 1161083 = 1741625) B1741625
theorem B1161135 : Blo 1160639 1161135 := bstep (se 1 (by rfl) ⟨870851, by rfl⟩ : syracuseStep 1161135 = 1741703) B1741703
theorem B4962235 : Blo 1160639 4962235 := bstep (se 1 (by rfl) ⟨3721676, by rfl⟩ : syracuseStep 4962235 = 7443353) B7443353
theorem B1161159 : Blo 1160639 1161159 := bstep (se 1 (by rfl) ⟨870869, by rfl⟩ : syracuseStep 1161159 = 1741739) B1741739
theorem B1161179 : Blo 1160639 1161179 := bstep (se 1 (by rfl) ⟨870884, by rfl⟩ : syracuseStep 1161179 = 1741769) B1741769
theorem B1161255 : Blo 1160639 1161255 := bstep (se 1 (by rfl) ⟨870941, by rfl⟩ : syracuseStep 1161255 = 1741883) B1741883
theorem B1161295 : Blo 1160639 1161295 := bstep (se 1 (by rfl) ⟨870971, by rfl⟩ : syracuseStep 1161295 = 1741943) B1741943
theorem B1161311 : Blo 1160639 1161311 := bstep (se 1 (by rfl) ⟨870983, by rfl⟩ : syracuseStep 1161311 = 1741967) B1741967
theorem B1161339 : Blo 1160639 1161339 := bstep (se 1 (by rfl) ⟨871004, by rfl⟩ : syracuseStep 1161339 = 1742009) B1742009
theorem B1161391 : Blo 1160639 1161391 := bstep (se 1 (by rfl) ⟨871043, by rfl⟩ : syracuseStep 1161391 = 1742087) B1742087
theorem B1161415 : Blo 1160639 1161415 := bstep (se 1 (by rfl) ⟨871061, by rfl⟩ : syracuseStep 1161415 = 1742123) B1742123
theorem B1161435 : Blo 1160639 1161435 := bstep (se 1 (by rfl) ⟨871076, by rfl⟩ : syracuseStep 1161435 = 1742153) B1742153
theorem B1161511 : Blo 1160639 1161511 := bstep (se 1 (by rfl) ⟨871133, by rfl⟩ : syracuseStep 1161511 = 1742267) B1742267
theorem B1161551 : Blo 1160639 1161551 := bstep (se 1 (by rfl) ⟨871163, by rfl⟩ : syracuseStep 1161551 = 1742327) B1742327
theorem B1161567 : Blo 1160639 1161567 := bstep (se 1 (by rfl) ⟨871175, by rfl⟩ : syracuseStep 1161567 = 1742351) B1742351
theorem B1161595 : Blo 1160639 1161595 := bstep (se 1 (by rfl) ⟨871196, by rfl⟩ : syracuseStep 1161595 = 1742393) B1742393
theorem B1653167 : Blo 1160639 1653167 := bstep (se 1 (by rfl) ⟨1239875, by rfl⟩ : syracuseStep 1653167 = 2479751) B2479751
theorem B1161647 : Blo 1160639 1161647 := bstep (se 1 (by rfl) ⟨871235, by rfl⟩ : syracuseStep 1161647 = 1742471) B1742471
theorem B1161671 : Blo 1160639 1161671 := bstep (se 1 (by rfl) ⟨871253, by rfl⟩ : syracuseStep 1161671 = 1742507) B1742507
theorem B1161691 : Blo 1160639 1161691 := bstep (se 1 (by rfl) ⟨871268, by rfl⟩ : syracuseStep 1161691 = 1742537) B1742537
theorem B2210267 : Blo 1160639 2210267 := bstep (se 1 (by rfl) ⟨1657700, by rfl⟩ : syracuseStep 2210267 = 3315401) B3315401
theorem B1161767 : Blo 1160639 1161767 := bstep (se 1 (by rfl) ⟨871325, by rfl⟩ : syracuseStep 1161767 = 1742651) B1742651
theorem B1161807 : Blo 1160639 1161807 := bstep (se 1 (by rfl) ⟨871355, by rfl⟩ : syracuseStep 1161807 = 1742711) B1742711
theorem B1161823 : Blo 1160639 1161823 := bstep (se 1 (by rfl) ⟨871367, by rfl⟩ : syracuseStep 1161823 = 1742735) B1742735
theorem B1161851 : Blo 1160639 1161851 := bstep (se 1 (by rfl) ⟨871388, by rfl⟩ : syracuseStep 1161851 = 1742777) B1742777
theorem B1161903 : Blo 1160639 1161903 := bstep (se 1 (by rfl) ⟨871427, by rfl⟩ : syracuseStep 1161903 = 1742855) B1742855
theorem B47790769 : Blo 1160639 47790769 := bstep (se 2 (by rfl) ⟨17921538, by rfl⟩ : syracuseStep 47790769 = 35843077) B35843077
theorem B1161927 : Blo 1160639 1161927 := bstep (se 1 (by rfl) ⟨871445, by rfl⟩ : syracuseStep 1161927 = 1742891) B1742891
theorem B2210503 : Blo 1160639 2210503 := bstep (se 1 (by rfl) ⟨1657877, by rfl⟩ : syracuseStep 2210503 = 3315755) B3315755
theorem B1161947 : Blo 1160639 1161947 := bstep (se 1 (by rfl) ⟨871460, by rfl⟩ : syracuseStep 1161947 = 1742921) B1742921
theorem B1162023 : Blo 1160639 1162023 := bstep (se 1 (by rfl) ⟨871517, by rfl⟩ : syracuseStep 1162023 = 1743035) B1743035
theorem B1162063 : Blo 1160639 1162063 := bstep (se 1 (by rfl) ⟨871547, by rfl⟩ : syracuseStep 1162063 = 1743095) B1743095
theorem B38255449 : Blo 1160639 38255449 := bstep (se 2 (by rfl) ⟨14345793, by rfl⟩ : syracuseStep 38255449 = 28691587) B28691587
theorem B1162079 : Blo 1160639 1162079 := bstep (se 1 (by rfl) ⟨871559, by rfl⟩ : syracuseStep 1162079 = 1743119) B1743119
theorem B1162107 : Blo 1160639 1162107 := bstep (se 1 (by rfl) ⟨871580, by rfl⟩ : syracuseStep 1162107 = 1743161) B1743161
theorem B1162159 : Blo 1160639 1162159 := bstep (se 1 (by rfl) ⟨871619, by rfl⟩ : syracuseStep 1162159 = 1743239) B1743239
theorem B1162183 : Blo 1160639 1162183 := bstep (se 1 (by rfl) ⟨871637, by rfl⟩ : syracuseStep 1162183 = 1743275) B1743275
theorem B1162203 : Blo 1160639 1162203 := bstep (se 1 (by rfl) ⟨871652, by rfl⟩ : syracuseStep 1162203 = 1743305) B1743305
theorem B1162279 : Blo 1160639 1162279 := bstep (se 1 (by rfl) ⟨871709, by rfl⟩ : syracuseStep 1162279 = 1743419) B1743419
theorem B1162319 : Blo 1160639 1162319 := bstep (se 1 (by rfl) ⟨871739, by rfl⟩ : syracuseStep 1162319 = 1743479) B1743479
theorem B1162335 : Blo 1160639 1162335 := bstep (se 1 (by rfl) ⟨871751, by rfl⟩ : syracuseStep 1162335 = 1743503) B1743503
theorem B1162363 : Blo 1160639 1162363 := bstep (se 1 (by rfl) ⟨871772, by rfl⟩ : syracuseStep 1162363 = 1743545) B1743545
theorem B1162415 : Blo 1160639 1162415 := bstep (se 1 (by rfl) ⟨871811, by rfl⟩ : syracuseStep 1162415 = 1743623) B1743623
theorem B7453889 : Blo 1160639 7453889 := bstep (se 2 (by rfl) ⟨2795208, by rfl⟩ : syracuseStep 7453889 = 5590417) B5590417
theorem B1653959 : Blo 1160639 1653959 := bstep (se 1 (by rfl) ⟨1240469, by rfl⟩ : syracuseStep 1653959 = 2480939) B2480939
theorem B1162439 : Blo 1160639 1162439 := bstep (se 1 (by rfl) ⟨871829, by rfl⟩ : syracuseStep 1162439 = 1743659) B1743659
theorem B1162459 : Blo 1160639 1162459 := bstep (se 1 (by rfl) ⟨871844, by rfl⟩ : syracuseStep 1162459 = 1743689) B1743689
theorem B3980555 : Blo 1160639 3980555 := bstep (se 1 (by rfl) ⟨2985416, by rfl⟩ : syracuseStep 3980555 = 5970833) B5970833
theorem B13221143 : Blo 1160639 13221143 := bstep (se 1 (by rfl) ⟨9915857, by rfl⟩ : syracuseStep 13221143 = 19831715) B19831715
theorem B1162535 : Blo 1160639 1162535 := bstep (se 1 (by rfl) ⟨871901, by rfl⟩ : syracuseStep 1162535 = 1743803) B1743803
theorem B1162575 : Blo 1160639 1162575 := bstep (se 1 (by rfl) ⟨871931, by rfl⟩ : syracuseStep 1162575 = 1743863) B1743863
theorem B1162591 : Blo 1160639 1162591 := bstep (se 1 (by rfl) ⟨871943, by rfl⟩ : syracuseStep 1162591 = 1743887) B1743887
theorem B1162619 : Blo 1160639 1162619 := bstep (se 1 (by rfl) ⟨871964, by rfl⟩ : syracuseStep 1162619 = 1743929) B1743929
theorem B11156879 : Blo 1160639 11156879 := bstep (se 1 (by rfl) ⟨8367659, by rfl⟩ : syracuseStep 11156879 = 16735319) B16735319
theorem B1162671 : Blo 1160639 1162671 := bstep (se 1 (by rfl) ⟨872003, by rfl⟩ : syracuseStep 1162671 = 1744007) B1744007
theorem B1162695 : Blo 1160639 1162695 := bstep (se 1 (by rfl) ⟨872021, by rfl⟩ : syracuseStep 1162695 = 1744043) B1744043
theorem B1162715 : Blo 1160639 1162715 := bstep (se 1 (by rfl) ⟨872036, by rfl⟩ : syracuseStep 1162715 = 1744073) B1744073
theorem B1162791 : Blo 1160639 1162791 := bstep (se 1 (by rfl) ⟨872093, by rfl⟩ : syracuseStep 1162791 = 1744187) B1744187
theorem B1162831 : Blo 1160639 1162831 := bstep (se 1 (by rfl) ⟨872123, by rfl⟩ : syracuseStep 1162831 = 1744247) B1744247
theorem B1162847 : Blo 1160639 1162847 := bstep (se 1 (by rfl) ⟨872135, by rfl⟩ : syracuseStep 1162847 = 1744271) B1744271
theorem B1162875 : Blo 1160639 1162875 := bstep (se 1 (by rfl) ⟨872156, by rfl⟩ : syracuseStep 1162875 = 1744313) B1744313
theorem B1162927 : Blo 1160639 1162927 := bstep (se 1 (by rfl) ⟨872195, by rfl⟩ : syracuseStep 1162927 = 1744391) B1744391
theorem B1162951 : Blo 1160639 1162951 := bstep (se 1 (by rfl) ⟨872213, by rfl⟩ : syracuseStep 1162951 = 1744427) B1744427
theorem B8371927 : Blo 1160639 8371927 := bstep (se 1 (by rfl) ⟨6278945, by rfl⟩ : syracuseStep 8371927 = 12557891) B12557891
theorem B1162971 : Blo 1160639 1162971 := bstep (se 1 (by rfl) ⟨872228, by rfl⟩ : syracuseStep 1162971 = 1744457) B1744457
theorem B1163047 : Blo 1160639 1163047 := bstep (se 1 (by rfl) ⟨872285, by rfl⟩ : syracuseStep 1163047 = 1744571) B1744571
theorem B1163087 : Blo 1160639 1163087 := bstep (se 1 (by rfl) ⟨872315, by rfl⟩ : syracuseStep 1163087 = 1744631) B1744631
theorem B1163103 : Blo 1160639 1163103 := bstep (se 1 (by rfl) ⟨872327, by rfl⟩ : syracuseStep 1163103 = 1744655) B1744655
theorem B1163131 : Blo 1160639 1163131 := bstep (se 1 (by rfl) ⟨872348, by rfl⟩ : syracuseStep 1163131 = 1744697) B1744697
theorem B1163183 : Blo 1160639 1163183 := bstep (se 1 (by rfl) ⟨872387, by rfl⟩ : syracuseStep 1163183 = 1744775) B1744775
theorem B1163207 : Blo 1160639 1163207 := bstep (se 1 (by rfl) ⟨872405, by rfl⟩ : syracuseStep 1163207 = 1744811) B1744811
theorem B1163227 : Blo 1160639 1163227 := bstep (se 1 (by rfl) ⟨872420, by rfl⟩ : syracuseStep 1163227 = 1744841) B1744841
theorem B7946243 : Blo 1160639 7946243 := bstep (se 1 (by rfl) ⟨5959682, by rfl⟩ : syracuseStep 7946243 = 11919365) B11919365
theorem B1163303 : Blo 1160639 1163303 := bstep (se 1 (by rfl) ⟨872477, by rfl⟩ : syracuseStep 1163303 = 1744955) B1744955
theorem B1163343 : Blo 1160639 1163343 := bstep (se 1 (by rfl) ⟨872507, by rfl⟩ : syracuseStep 1163343 = 1745015) B1745015
theorem B1163359 : Blo 1160639 1163359 := bstep (se 1 (by rfl) ⟨872519, by rfl⟩ : syracuseStep 1163359 = 1745039) B1745039
theorem B1163387 : Blo 1160639 1163387 := bstep (se 1 (by rfl) ⟨872540, by rfl⟩ : syracuseStep 1163387 = 1745081) B1745081
theorem B1163439 : Blo 1160639 1163439 := bstep (se 1 (by rfl) ⟨872579, by rfl⟩ : syracuseStep 1163439 = 1745159) B1745159
theorem B1163463 : Blo 1160639 1163463 := bstep (se 1 (by rfl) ⟨872597, by rfl⟩ : syracuseStep 1163463 = 1745195) B1745195
theorem B1163483 : Blo 1160639 1163483 := bstep (se 1 (by rfl) ⟨872612, by rfl⟩ : syracuseStep 1163483 = 1745225) B1745225
theorem B1163559 : Blo 1160639 1163559 := bstep (se 1 (by rfl) ⟨872669, by rfl⟩ : syracuseStep 1163559 = 1745339) B1745339
theorem B7258429 : Blo 1160639 7258429 := bstep (se 3 (by rfl) ⟨1360955, by rfl⟩ : syracuseStep 7258429 = 2721911) B2721911
theorem B1163599 : Blo 1160639 1163599 := bstep (se 1 (by rfl) ⟨872699, by rfl⟩ : syracuseStep 1163599 = 1745399) B1745399
theorem B1163615 : Blo 1160639 1163615 := bstep (se 1 (by rfl) ⟨872711, by rfl⟩ : syracuseStep 1163615 = 1745423) B1745423
theorem B1163643 : Blo 1160639 1163643 := bstep (se 1 (by rfl) ⟨872732, by rfl⟩ : syracuseStep 1163643 = 1745465) B1745465
theorem B1163695 : Blo 1160639 1163695 := bstep (se 1 (by rfl) ⟨872771, by rfl⟩ : syracuseStep 1163695 = 1745543) B1745543
theorem B1163719 : Blo 1160639 1163719 := bstep (se 1 (by rfl) ⟨872789, by rfl⟩ : syracuseStep 1163719 = 1745579) B1745579
theorem B1163739 : Blo 1160639 1163739 := bstep (se 1 (by rfl) ⟨872804, by rfl⟩ : syracuseStep 1163739 = 1745609) B1745609
theorem B1163815 : Blo 1160639 1163815 := bstep (se 1 (by rfl) ⟨872861, by rfl⟩ : syracuseStep 1163815 = 1745723) B1745723
theorem B1163855 : Blo 1160639 1163855 := bstep (se 1 (by rfl) ⟨872891, by rfl⟩ : syracuseStep 1163855 = 1745783) B1745783
theorem B1163871 : Blo 1160639 1163871 := bstep (se 1 (by rfl) ⟨872903, by rfl⟩ : syracuseStep 1163871 = 1745807) B1745807
theorem B1163899 : Blo 1160639 1163899 := bstep (se 1 (by rfl) ⟨872924, by rfl⟩ : syracuseStep 1163899 = 1745849) B1745849
theorem B1163951 : Blo 1160639 1163951 := bstep (se 1 (by rfl) ⟨872963, by rfl⟩ : syracuseStep 1163951 = 1745927) B1745927
theorem B1163975 : Blo 1160639 1163975 := bstep (se 1 (by rfl) ⟨872981, by rfl⟩ : syracuseStep 1163975 = 1745963) B1745963
theorem B5587667 : Blo 1160639 5587667 := bstep (se 1 (by rfl) ⟨4190750, by rfl⟩ : syracuseStep 5587667 = 8381501) B8381501
theorem B1163995 : Blo 1160639 1163995 := bstep (se 1 (by rfl) ⟨872996, by rfl⟩ : syracuseStep 1163995 = 1745993) B1745993
theorem B16761613 : Blo 1160639 16761613 := bstep (se 3 (by rfl) ⟨3142802, by rfl⟩ : syracuseStep 16761613 = 6285605) B6285605
theorem B1164071 : Blo 1160639 1164071 := bstep (se 1 (by rfl) ⟨873053, by rfl⟩ : syracuseStep 1164071 = 1746107) B1746107
theorem B9945929 : Blo 1160639 9945929 := bstep (se 2 (by rfl) ⟨3729723, by rfl⟩ : syracuseStep 9945929 = 7459447) B7459447
theorem B1164111 : Blo 1160639 1164111 := bstep (se 1 (by rfl) ⟨873083, by rfl⟩ : syracuseStep 1164111 = 1746167) B1746167
theorem B1164127 : Blo 1160639 1164127 := bstep (se 1 (by rfl) ⟨873095, by rfl⟩ : syracuseStep 1164127 = 1746191) B1746191
theorem B1164155 : Blo 1160639 1164155 := bstep (se 1 (by rfl) ⟨873116, by rfl⟩ : syracuseStep 1164155 = 1746233) B1746233
theorem B1164207 : Blo 1160639 1164207 := bstep (se 1 (by rfl) ⟨873155, by rfl⟩ : syracuseStep 1164207 = 1746311) B1746311
theorem B1164231 : Blo 1160639 1164231 := bstep (se 1 (by rfl) ⟨873173, by rfl⟩ : syracuseStep 1164231 = 1746347) B1746347
theorem B1164251 : Blo 1160639 1164251 := bstep (se 1 (by rfl) ⟨873188, by rfl⟩ : syracuseStep 1164251 = 1746377) B1746377
theorem B1164327 : Blo 1160639 1164327 := bstep (se 1 (by rfl) ⟨873245, by rfl⟩ : syracuseStep 1164327 = 1746491) B1746491
theorem B1164367 : Blo 1160639 1164367 := bstep (se 1 (by rfl) ⟨873275, by rfl⟩ : syracuseStep 1164367 = 1746551) B1746551
theorem B1164383 : Blo 1160639 1164383 := bstep (se 1 (by rfl) ⟨873287, by rfl⟩ : syracuseStep 1164383 = 1746575) B1746575
theorem B1164411 : Blo 1160639 1164411 := bstep (se 1 (by rfl) ⟨873308, by rfl⟩ : syracuseStep 1164411 = 1746617) B1746617
theorem B1164463 : Blo 1160639 1164463 := bstep (se 1 (by rfl) ⟨873347, by rfl⟩ : syracuseStep 1164463 = 1746695) B1746695
theorem B1164487 : Blo 1160639 1164487 := bstep (se 1 (by rfl) ⟨873365, by rfl⟩ : syracuseStep 1164487 = 1746731) B1746731
theorem B1164507 : Blo 1160639 1164507 := bstep (se 1 (by rfl) ⟨873380, by rfl⟩ : syracuseStep 1164507 = 1746761) B1746761
theorem B1164583 : Blo 1160639 1164583 := bstep (se 1 (by rfl) ⟨873437, by rfl⟩ : syracuseStep 1164583 = 1746875) B1746875
theorem B1164623 : Blo 1160639 1164623 := bstep (se 1 (by rfl) ⟨873467, by rfl⟩ : syracuseStep 1164623 = 1746935) B1746935
theorem B1164639 : Blo 1160639 1164639 := bstep (se 1 (by rfl) ⟨873479, by rfl⟩ : syracuseStep 1164639 = 1746959) B1746959
theorem B1656283 : Blo 1160639 1656283 := bstep (se 1 (by rfl) ⟨1242212, by rfl⟩ : syracuseStep 1656283 = 2484425) B2484425
theorem B3917321 : Blo 1160639 3917321 := bstep (se 2 (by rfl) ⟨1468995, by rfl⟩ : syracuseStep 3917321 = 2937991) B2937991
theorem B5883515 : Blo 1160639 5883515 := bstep (se 1 (by rfl) ⟨4412636, by rfl⟩ : syracuseStep 5883515 = 8825273) B8825273
theorem B3983033 : Blo 1160639 3983033 := bstep (se 2 (by rfl) ⟨1493637, by rfl⟩ : syracuseStep 3983033 = 2987275) B2987275
theorem B9422929 : Blo 1160639 9422929 := bstep (se 2 (by rfl) ⟨3533598, by rfl⟩ : syracuseStep 9422929 = 7067197) B7067197
theorem B9422963 : Blo 1160639 9422963 := bstep (se 1 (by rfl) ⟨7067222, by rfl⟩ : syracuseStep 9422963 = 14134445) B14134445
theorem B3918185 : Blo 1160639 3918185 := bstep (se 2 (by rfl) ⟨1469319, by rfl⟩ : syracuseStep 3918185 = 2938639) B2938639
theorem B6900233 : Blo 1160639 6900233 := bstep (se 2 (by rfl) ⟨2587587, by rfl⟩ : syracuseStep 6900233 = 5175175) B5175175
theorem B3983905 : Blo 1160639 3983905 := bstep (se 2 (by rfl) ⟨1493964, by rfl⟩ : syracuseStep 3983905 = 2987929) B2987929
theorem B4410071 : Blo 1160639 4410071 := bstep (se 1 (by rfl) ⟨3307553, by rfl⟩ : syracuseStep 4410071 = 6615107) B6615107
theorem B3918779 : Blo 1160639 3918779 := bstep (se 1 (by rfl) ⟨2939084, by rfl⟩ : syracuseStep 3918779 = 5878169) B5878169
theorem B8834021 : Blo 1160639 8834021 := bstep (se 4 (by rfl) ⟨828189, by rfl⟩ : syracuseStep 8834021 = 1656379) B1656379
theorem B4476539 : Blo 1160639 4476539 := bstep (se 1 (by rfl) ⟨3357404, by rfl⟩ : syracuseStep 4476539 = 6714809) B6714809
theorem B7950241 : Blo 1160639 7950241 := bstep (se 2 (by rfl) ⟨2981340, by rfl⟩ : syracuseStep 7950241 = 5962681) B5962681
theorem B27545507 : Blo 1160639 27545507 := bstep (se 1 (by rfl) ⟨20659130, by rfl⟩ : syracuseStep 27545507 = 41318261) B41318261
theorem B1396859 : Blo 1160639 1396859 := bstep (se 1 (by rfl) ⟨1047644, by rfl⟩ : syracuseStep 1396859 = 2095289) B2095289
theorem B5886269 : Blo 1160639 5886269 := bstep (se 3 (by rfl) ⟨1103675, by rfl⟩ : syracuseStep 5886269 = 2207351) B2207351
theorem B18862465 : Blo 1160639 18862465 := bstep (se 2 (by rfl) ⟨7073424, by rfl⟩ : syracuseStep 18862465 = 14146849) B14146849
theorem B9916951 : Blo 1160639 9916951 := bstep (se 1 (by rfl) ⟨7437713, by rfl⟩ : syracuseStep 9916951 = 14875427) B14875427
theorem B4968985 : Blo 1160639 4968985 := bstep (se 2 (by rfl) ⟨1863369, by rfl⟩ : syracuseStep 4968985 = 3726739) B3726739
theorem B16765541 : Blo 1160639 16765541 := bstep (se 4 (by rfl) ⟨1571769, by rfl⟩ : syracuseStep 16765541 = 3143539) B3143539
theorem B3920507 : Blo 1160639 3920507 := bstep (se 1 (by rfl) ⟨2940380, by rfl⟩ : syracuseStep 3920507 = 5880761) B5880761
theorem B3920669 : Blo 1160639 3920669 := bstep (se 3 (by rfl) ⟨735125, by rfl⟩ : syracuseStep 3920669 = 1470251) B1470251
theorem B7951279 : Blo 1160639 7951279 := bstep (se 1 (by rfl) ⟨5963459, by rfl⟩ : syracuseStep 7951279 = 11926919) B11926919
theorem B7558211 : Blo 1160639 7558211 := bstep (se 1 (by rfl) ⟨5668658, by rfl⟩ : syracuseStep 7558211 = 11337317) B11337317
theorem B9426073 : Blo 1160639 9426073 := bstep (se 2 (by rfl) ⟨3534777, by rfl⟩ : syracuseStep 9426073 = 7069555) B7069555
theorem B2938103 : Blo 1160639 2938103 := bstep (se 1 (by rfl) ⟨2203577, by rfl⟩ : syracuseStep 2938103 = 4407155) B4407155
theorem B3921371 : Blo 1160639 3921371 := bstep (se 1 (by rfl) ⟨2941028, by rfl⟩ : syracuseStep 3921371 = 5882057) B5882057
theorem B5821915 : Blo 1160639 5821915 := bstep (se 1 (by rfl) ⟨4366436, by rfl⟩ : syracuseStep 5821915 = 8732873) B8732873
theorem B4412987 : Blo 1160639 4412987 := bstep (se 1 (by rfl) ⟨3309740, by rfl⟩ : syracuseStep 4412987 = 6619481) B6619481
theorem B3725099 : Blo 1160639 3725099 := bstep (se 1 (by rfl) ⟨2793824, by rfl⟩ : syracuseStep 3725099 = 5587649) B5587649
theorem B3922073 : Blo 1160639 3922073 := bstep (se 2 (by rfl) ⟨1470777, by rfl⟩ : syracuseStep 3922073 = 2941555) B2941555
theorem B11917721 : Blo 1160639 11917721 := bstep (se 2 (by rfl) ⟨4469145, by rfl⟩ : syracuseStep 11917721 = 8938291) B8938291
theorem B5888537 : Blo 1160639 5888537 := bstep (se 2 (by rfl) ⟨2208201, by rfl⟩ : syracuseStep 5888537 = 4416403) B4416403
theorem B2611835 : Blo 1160639 2611835 := bstep (se 1 (by rfl) ⟨1958876, by rfl⟩ : syracuseStep 2611835 = 3917753) B3917753
theorem B2939591 : Blo 1160639 2939591 := bstep (se 1 (by rfl) ⟨2204693, by rfl⟩ : syracuseStep 2939591 = 4409387) B4409387
theorem B2611961 : Blo 1160639 2611961 := bstep (se 2 (by rfl) ⟨979485, by rfl⟩ : syracuseStep 2611961 = 1958971) B1958971
theorem B2612231 : Blo 1160639 2612231 := bstep (se 1 (by rfl) ⟨1959173, by rfl⟩ : syracuseStep 2612231 = 3918347) B3918347
theorem B2612303 : Blo 1160639 2612303 := bstep (se 1 (by rfl) ⟨1959227, by rfl⟩ : syracuseStep 2612303 = 3918455) B3918455
theorem B4480267 : Blo 1160639 4480267 := bstep (se 1 (by rfl) ⟨3360200, by rfl⟩ : syracuseStep 4480267 = 6720401) B6720401
theorem B3923261 : Blo 1160639 3923261 := bstep (se 3 (by rfl) ⟨735611, by rfl⟩ : syracuseStep 3923261 = 1471223) B1471223
theorem B8379773 : Blo 1160639 8379773 := bstep (se 3 (by rfl) ⟨1571207, by rfl⟩ : syracuseStep 8379773 = 3142415) B3142415
theorem B2612699 : Blo 1160639 2612699 := bstep (se 1 (by rfl) ⟨1959524, by rfl⟩ : syracuseStep 2612699 = 3919049) B3919049
theorem B3726881 : Blo 1160639 3726881 := bstep (se 2 (by rfl) ⟨1397580, by rfl⟩ : syracuseStep 3726881 = 2795161) B2795161
theorem B13229891 : Blo 1160639 13229891 := bstep (se 1 (by rfl) ⟨9922418, by rfl⟩ : syracuseStep 13229891 = 19844837) B19844837
theorem B2940745 : Blo 1160639 2940745 := bstep (se 2 (by rfl) ⟨1102779, by rfl⟩ : syracuseStep 2940745 = 2205559) B2205559
theorem B6283169 : Blo 1160639 6283169 := bstep (se 2 (by rfl) ⟨2356188, by rfl⟩ : syracuseStep 6283169 = 4712377) B4712377
theorem B2613167 : Blo 1160639 2613167 := bstep (se 1 (by rfl) ⟨1959875, by rfl⟩ : syracuseStep 2613167 = 3919751) B3919751
theorem B3727367 : Blo 1160639 3727367 := bstep (se 1 (by rfl) ⟨2795525, by rfl⟩ : syracuseStep 3727367 = 5591051) B5591051
theorem B4481081 : Blo 1160639 4481081 := bstep (se 2 (by rfl) ⟨1680405, by rfl⟩ : syracuseStep 4481081 = 3360811) B3360811
theorem B3924125 : Blo 1160639 3924125 := bstep (se 3 (by rfl) ⟨735773, by rfl⟩ : syracuseStep 3924125 = 1471547) B1471547
theorem B2613419 : Blo 1160639 2613419 := bstep (se 1 (by rfl) ⟨1960064, by rfl⟩ : syracuseStep 2613419 = 3920129) B3920129
theorem B4415735 : Blo 1160639 4415735 := bstep (se 1 (by rfl) ⟨3311801, by rfl⟩ : syracuseStep 4415735 = 6623603) B6623603
theorem B6709819 : Blo 1160639 6709819 := bstep (se 1 (by rfl) ⟨5032364, by rfl⟩ : syracuseStep 6709819 = 10064729) B10064729
theorem B7955003 : Blo 1160639 7955003 := bstep (se 1 (by rfl) ⟨5966252, by rfl⟩ : syracuseStep 7955003 = 11932505) B11932505
theorem B8839853 : Blo 1160639 8839853 := bstep (se 3 (by rfl) ⟨1657472, by rfl⟩ : syracuseStep 8839853 = 3314945) B3314945
theorem B3924665 : Blo 1160639 3924665 := bstep (se 2 (by rfl) ⟨1471749, by rfl⟩ : syracuseStep 3924665 = 2943499) B2943499
theorem B2613959 : Blo 1160639 2613959 := bstep (se 1 (by rfl) ⟨1960469, by rfl⟩ : syracuseStep 2613959 = 3920939) B3920939
theorem B6611665 : Blo 1160639 6611665 := bstep (se 2 (by rfl) ⟨2479374, by rfl⟩ : syracuseStep 6611665 = 4958749) B4958749
theorem B1958647 : Blo 1160639 1958647 := bstep (se 1 (by rfl) ⟨1468985, by rfl⟩ : syracuseStep 1958647 = 2937971) B2937971
theorem B3138479 : Blo 1160639 3138479 := bstep (se 1 (by rfl) ⟨2353859, by rfl⟩ : syracuseStep 3138479 = 4707719) B4707719
theorem B2941879 : Blo 1160639 2941879 := bstep (se 1 (by rfl) ⟨2206409, by rfl⟩ : syracuseStep 2941879 = 4412819) B4412819
theorem B1958843 : Blo 1160639 1958843 := bstep (se 1 (by rfl) ⟨1469132, by rfl⟩ : syracuseStep 1958843 = 2938265) B2938265
theorem B1958951 : Blo 1160639 1958951 := bstep (se 1 (by rfl) ⟨1469213, by rfl⟩ : syracuseStep 1958951 = 2938427) B2938427
theorem B4416707 : Blo 1160639 4416707 := bstep (se 1 (by rfl) ⟨3312530, by rfl⟩ : syracuseStep 4416707 = 6625061) B6625061
theorem B3925259 : Blo 1160639 3925259 := bstep (se 1 (by rfl) ⟨2943944, by rfl⟩ : syracuseStep 3925259 = 5887889) B5887889
theorem B6284567 : Blo 1160639 6284567 := bstep (se 1 (by rfl) ⟨4713425, by rfl⟩ : syracuseStep 6284567 = 9426851) B9426851
theorem B1959241 : Blo 1160639 1959241 := bstep (se 2 (by rfl) ⟨734715, by rfl⟩ : syracuseStep 1959241 = 1469431) B1469431
theorem B2483561 : Blo 1160639 2483561 := bstep (se 2 (by rfl) ⟨931335, by rfl⟩ : syracuseStep 2483561 = 1862671) B1862671
theorem B1959275 : Blo 1160639 1959275 := bstep (se 1 (by rfl) ⟨1469456, by rfl⟩ : syracuseStep 1959275 = 2938913) B2938913
theorem B5891453 : Blo 1160639 5891453 := bstep (se 3 (by rfl) ⟨1104647, by rfl⟩ : syracuseStep 5891453 = 2209295) B2209295
theorem B3925529 : Blo 1160639 3925529 := bstep (se 2 (by rfl) ⟨1472073, by rfl⟩ : syracuseStep 3925529 = 2944147) B2944147
theorem B2614823 : Blo 1160639 2614823 := bstep (se 1 (by rfl) ⟨1961117, by rfl⟩ : syracuseStep 2614823 = 3922235) B3922235
theorem B4417163 : Blo 1160639 4417163 := bstep (se 1 (by rfl) ⟨3312872, by rfl⟩ : syracuseStep 4417163 = 6625745) B6625745
theorem B5301949 : Blo 1160639 5301949 := bstep (se 3 (by rfl) ⟨994115, by rfl⟩ : syracuseStep 5301949 = 1988231) B1988231
theorem B1959673 : Blo 1160639 1959673 := bstep (se 2 (by rfl) ⟨734877, by rfl⟩ : syracuseStep 1959673 = 1469755) B1469755
theorem B16967513 : Blo 1160639 16967513 := bstep (se 2 (by rfl) ⟨6362817, by rfl⟩ : syracuseStep 16967513 = 12725635) B12725635
theorem B4417375 : Blo 1160639 4417375 := bstep (se 1 (by rfl) ⟨3313031, by rfl⟩ : syracuseStep 4417375 = 6626063) B6626063
theorem B2385769 : Blo 1160639 2385769 := bstep (se 2 (by rfl) ⟨894663, by rfl⟩ : syracuseStep 2385769 = 1789327) B1789327
theorem B2615147 : Blo 1160639 2615147 := bstep (se 1 (by rfl) ⟨1961360, by rfl⟩ : syracuseStep 2615147 = 3922721) B3922721
theorem B2615201 : Blo 1160639 2615201 := bstep (se 2 (by rfl) ⟨980700, by rfl⟩ : syracuseStep 2615201 = 1961401) B1961401
theorem B1959943 : Blo 1160639 1959943 := bstep (se 1 (by rfl) ⟨1469957, by rfl⟩ : syracuseStep 1959943 = 2939915) B2939915
theorem B4778003 : Blo 1160639 4778003 := bstep (se 1 (by rfl) ⟨3583502, by rfl⟩ : syracuseStep 4778003 = 7167005) B7167005
theorem B2615543 : Blo 1160639 2615543 := bstep (se 1 (by rfl) ⟨1961657, by rfl⟩ : syracuseStep 2615543 = 3923315) B3923315
theorem B2943337 : Blo 1160639 2943337 := bstep (se 2 (by rfl) ⟨1103751, by rfl⟩ : syracuseStep 2943337 = 2207503) B2207503
theorem B1960375 : Blo 1160639 1960375 := bstep (se 1 (by rfl) ⟨1470281, by rfl⟩ : syracuseStep 1960375 = 2940563) B2940563
theorem B1960571 : Blo 1160639 1960571 := bstep (se 1 (by rfl) ⟨1470428, by rfl⟩ : syracuseStep 1960571 = 2940857) B2940857
theorem B2943611 : Blo 1160639 2943611 := bstep (se 1 (by rfl) ⟨2207708, by rfl⟩ : syracuseStep 2943611 = 4415417) B4415417
theorem B3926663 : Blo 1160639 3926663 := bstep (se 1 (by rfl) ⟨2944997, by rfl⟩ : syracuseStep 3926663 = 5889995) B5889995
theorem B3926717 : Blo 1160639 3926717 := bstep (se 3 (by rfl) ⟨736259, by rfl⟩ : syracuseStep 3926717 = 1472519) B1472519
theorem B4418333 : Blo 1160639 4418333 := bstep (se 3 (by rfl) ⟨828437, by rfl⟩ : syracuseStep 4418333 = 1656875) B1656875
theorem B4418347 : Blo 1160639 4418347 := bstep (se 1 (by rfl) ⟨3313760, by rfl⟩ : syracuseStep 4418347 = 6627521) B6627521
theorem B2616137 : Blo 1160639 2616137 := bstep (se 2 (by rfl) ⟨981051, by rfl⟩ : syracuseStep 2616137 = 1962103) B1962103
theorem B1469279 : Blo 1160639 1469279 := bstep (se 1 (by rfl) ⟨1101959, by rfl⟩ : syracuseStep 1469279 = 2203919) B2203919
theorem B3926879 : Blo 1160639 3926879 := bstep (se 1 (by rfl) ⟨2945159, by rfl⟩ : syracuseStep 3926879 = 5890319) B5890319
theorem B3927041 : Blo 1160639 3927041 := bstep (se 2 (by rfl) ⟨1472640, by rfl⟩ : syracuseStep 3927041 = 2945281) B2945281
theorem B3533831 : Blo 1160639 3533831 := bstep (se 1 (by rfl) ⟨2650373, by rfl⟩ : syracuseStep 3533831 = 5300747) B5300747
theorem B1960969 : Blo 1160639 1960969 := bstep (se 2 (by rfl) ⟨735363, by rfl⟩ : syracuseStep 1960969 = 1470727) B1470727
theorem B8842283 : Blo 1160639 8842283 := bstep (se 1 (by rfl) ⟨6631712, by rfl⟩ : syracuseStep 8842283 = 13263425) B13263425
theorem B1961131 : Blo 1160639 1961131 := bstep (se 1 (by rfl) ⟨1470848, by rfl⟩ : syracuseStep 1961131 = 2941697) B2941697
theorem B1764713 : Blo 1160639 1764713 := bstep (se 2 (by rfl) ⟨661767, by rfl⟩ : syracuseStep 1764713 = 1323535) B1323535
theorem B1863017 : Blo 1160639 1863017 := bstep (se 2 (by rfl) ⟨698631, by rfl⟩ : syracuseStep 1863017 = 1397263) B1397263
theorem B1306075 : Blo 1160639 1306075 := bstep (se 1 (by rfl) ⟨979556, by rfl⟩ : syracuseStep 1306075 = 1959113) B1959113
theorem B1961435 : Blo 1160639 1961435 := bstep (se 1 (by rfl) ⟨1471076, by rfl⟩ : syracuseStep 1961435 = 2942153) B2942153
theorem B4713947 : Blo 1160639 4713947 := bstep (se 1 (by rfl) ⟨3535460, by rfl⟩ : syracuseStep 4713947 = 7070921) B7070921
theorem B2485723 : Blo 1160639 2485723 := bstep (se 1 (by rfl) ⟨1864292, by rfl⟩ : syracuseStep 2485723 = 3728585) B3728585
theorem B2092601 : Blo 1160639 2092601 := bstep (se 2 (by rfl) ⟨784725, by rfl⟩ : syracuseStep 2092601 = 1569451) B1569451
theorem B2616929 : Blo 1160639 2616929 := bstep (se 2 (by rfl) ⟨981348, by rfl⟩ : syracuseStep 2616929 = 1962697) B1962697
theorem B1961671 : Blo 1160639 1961671 := bstep (se 1 (by rfl) ⟨1471253, by rfl⟩ : syracuseStep 1961671 = 2942507) B2942507
theorem B42430169 : Blo 1160639 42430169 := bstep (se 2 (by rfl) ⟨15911313, by rfl⟩ : syracuseStep 42430169 = 31822627) B31822627
theorem B3927851 : Blo 1160639 3927851 := bstep (se 1 (by rfl) ⟨2945888, by rfl⟩ : syracuseStep 3927851 = 5891777) B5891777
theorem B1961833 : Blo 1160639 1961833 := bstep (se 2 (by rfl) ⟨735687, by rfl⟩ : syracuseStep 1961833 = 1471375) B1471375
theorem B1863529 : Blo 1160639 1863529 := bstep (se 2 (by rfl) ⟨698823, by rfl⟩ : syracuseStep 1863529 = 1397647) B1397647
theorem B3305377 : Blo 1160639 3305377 := bstep (se 2 (by rfl) ⟨1239516, by rfl⟩ : syracuseStep 3305377 = 2479033) B2479033
theorem B1306543 : Blo 1160639 1306543 := bstep (se 1 (by rfl) ⟨979907, by rfl⟩ : syracuseStep 1306543 = 1959815) B1959815
theorem B2617271 : Blo 1160639 2617271 := bstep (se 1 (by rfl) ⟨1962953, by rfl⟩ : syracuseStep 2617271 = 3925907) B3925907
theorem B7172027 : Blo 1160639 7172027 := bstep (se 1 (by rfl) ⟨5379020, by rfl⟩ : syracuseStep 7172027 = 10758041) B10758041
theorem B3928121 : Blo 1160639 3928121 := bstep (se 2 (by rfl) ⟨1473045, by rfl⟩ : syracuseStep 3928121 = 2946091) B2946091
theorem B2650283 : Blo 1160639 2650283 := bstep (se 1 (by rfl) ⟨1987712, by rfl⟩ : syracuseStep 2650283 = 3975425) B3975425
theorem B1306975 : Blo 1160639 1306975 := bstep (se 1 (by rfl) ⟨980231, by rfl⟩ : syracuseStep 1306975 = 1960463) B1960463
theorem B3928445 : Blo 1160639 3928445 := bstep (se 3 (by rfl) ⟨736583, by rfl⟩ : syracuseStep 3928445 = 1473167) B1473167
theorem B2945423 : Blo 1160639 2945423 := bstep (se 1 (by rfl) ⟨2209067, by rfl⟩ : syracuseStep 2945423 = 4418135) B4418135
theorem B2355643 : Blo 1160639 2355643 := bstep (se 1 (by rfl) ⟨1766732, by rfl⟩ : syracuseStep 2355643 = 3533465) B3533465
theorem B1962427 : Blo 1160639 1962427 := bstep (se 1 (by rfl) ⟨1471820, by rfl⟩ : syracuseStep 1962427 = 2943641) B2943641
theorem B3305947 : Blo 1160639 3305947 := bstep (se 1 (by rfl) ⟨2479460, by rfl⟩ : syracuseStep 3305947 = 4958921) B4958921
theorem B1241563 : Blo 1160639 1241563 := bstep (se 1 (by rfl) ⟨931172, by rfl⟩ : syracuseStep 1241563 = 1862345) B1862345
theorem B2617865 : Blo 1160639 2617865 := bstep (se 2 (by rfl) ⟨981699, by rfl⟩ : syracuseStep 2617865 = 1963399) B1963399
theorem B1962535 : Blo 1160639 1962535 := bstep (se 1 (by rfl) ⟨1471901, by rfl⟩ : syracuseStep 1962535 = 2943803) B2943803
theorem B3142241 : Blo 1160639 3142241 := bstep (se 2 (by rfl) ⟨1178340, by rfl⟩ : syracuseStep 3142241 = 2356681) B2356681
theorem B3928715 : Blo 1160639 3928715 := bstep (se 1 (by rfl) ⟨2946536, by rfl⟩ : syracuseStep 3928715 = 5893073) B5893073
theorem B1307335 : Blo 1160639 1307335 := bstep (se 1 (by rfl) ⟨980501, by rfl⟩ : syracuseStep 1307335 = 1961003) B1961003
theorem B2945747 : Blo 1160639 2945747 := bstep (se 1 (by rfl) ⟨2209310, by rfl⟩ : syracuseStep 2945747 = 4418621) B4418621
theorem B1766137 : Blo 1160639 1766137 := bstep (se 2 (by rfl) ⟨662301, by rfl⟩ : syracuseStep 1766137 = 1324603) B1324603
theorem B2618207 : Blo 1160639 2618207 := bstep (se 1 (by rfl) ⟨1963655, by rfl⟩ : syracuseStep 2618207 = 3927311) B3927311
theorem B1962859 : Blo 1160639 1962859 := bstep (se 1 (by rfl) ⟨1472144, by rfl⟩ : syracuseStep 1962859 = 2944289) B2944289
theorem B2618387 : Blo 1160639 2618387 := bstep (se 1 (by rfl) ⟨1963790, by rfl⟩ : syracuseStep 2618387 = 3927581) B3927581
theorem B9925699 : Blo 1160639 9925699 := bstep (se 1 (by rfl) ⟨7444274, by rfl⟩ : syracuseStep 9925699 = 14888549) B14888549
theorem B3306653 : Blo 1160639 3306653 := bstep (se 3 (by rfl) ⟨619997, by rfl⟩ : syracuseStep 3306653 = 1239995) B1239995
theorem B2618729 : Blo 1160639 2618729 := bstep (se 2 (by rfl) ⟨982023, by rfl⟩ : syracuseStep 2618729 = 1964047) B1964047
theorem B3306881 : Blo 1160639 3306881 := bstep (se 2 (by rfl) ⟨1240080, by rfl⟩ : syracuseStep 3306881 = 2480161) B2480161
theorem B2094511 : Blo 1160639 2094511 := bstep (se 1 (by rfl) ⟨1570883, by rfl⟩ : syracuseStep 2094511 = 3141767) B3141767
theorem B1471927 : Blo 1160639 1471927 := bstep (se 1 (by rfl) ⟨1103945, by rfl⟩ : syracuseStep 1471927 = 2207891) B2207891
theorem B11171333 : Blo 1160639 11171333 := bstep (se 4 (by rfl) ⟨1047312, by rfl⟩ : syracuseStep 11171333 = 2094625) B2094625
theorem B13235723 : Blo 1160639 13235723 := bstep (se 1 (by rfl) ⟨9926792, by rfl⟩ : syracuseStep 13235723 = 19853585) B19853585
theorem B3929633 : Blo 1160639 3929633 := bstep (se 2 (by rfl) ⟨1473612, by rfl⟩ : syracuseStep 3929633 = 2947225) B2947225
theorem B1308199 : Blo 1160639 1308199 := bstep (se 1 (by rfl) ⟨981149, by rfl⟩ : syracuseStep 1308199 = 1962299) B1962299
theorem B5895827 : Blo 1160639 5895827 := bstep (se 1 (by rfl) ⟨4421870, by rfl⟩ : syracuseStep 5895827 = 8843741) B8843741
theorem B3307223 : Blo 1160639 3307223 := bstep (se 1 (by rfl) ⟨2480417, by rfl⟩ : syracuseStep 3307223 = 4960835) B4960835
theorem B4716281 : Blo 1160639 4716281 := bstep (se 2 (by rfl) ⟨1768605, by rfl⟩ : syracuseStep 4716281 = 3537211) B3537211
theorem B7960313 : Blo 1160639 7960313 := bstep (se 2 (by rfl) ⟨2985117, by rfl⟩ : syracuseStep 7960313 = 5970235) B5970235
theorem B3929849 : Blo 1160639 3929849 := bstep (se 2 (by rfl) ⟨1473693, by rfl⟩ : syracuseStep 3929849 = 2947387) B2947387
theorem B3307337 : Blo 1160639 3307337 := bstep (se 2 (by rfl) ⟨1240251, by rfl⟩ : syracuseStep 3307337 = 2480503) B2480503
theorem B1963919 : Blo 1160639 1963919 := bstep (se 1 (by rfl) ⟨1472939, by rfl⟩ : syracuseStep 1963919 = 2945879) B2945879
theorem B4421537 : Blo 1160639 4421537 := bstep (se 2 (by rfl) ⟨1658076, by rfl⟩ : syracuseStep 4421537 = 3316153) B3316153
theorem B2619323 : Blo 1160639 2619323 := bstep (se 1 (by rfl) ⟨1964492, by rfl⟩ : syracuseStep 2619323 = 3928985) B3928985
theorem B77559761 : Blo 1160639 77559761 := bstep (se 2 (by rfl) ⟨29084910, by rfl⟩ : syracuseStep 77559761 = 58169821) B58169821
theorem B3930119 : Blo 1160639 3930119 := bstep (se 1 (by rfl) ⟨2947589, by rfl⟩ : syracuseStep 3930119 = 5895179) B5895179
theorem B2619449 : Blo 1160639 2619449 := bstep (se 2 (by rfl) ⟨982293, by rfl⟩ : syracuseStep 2619449 = 1964587) B1964587
theorem B3930227 : Blo 1160639 3930227 := bstep (se 1 (by rfl) ⟨2947670, by rfl⟩ : syracuseStep 3930227 = 5895341) B5895341
theorem B1964155 : Blo 1160639 1964155 := bstep (se 1 (by rfl) ⟨1473116, by rfl⟩ : syracuseStep 1964155 = 2946233) B2946233
theorem B3930497 : Blo 1160639 3930497 := bstep (se 2 (by rfl) ⟨1473936, by rfl⟩ : syracuseStep 3930497 = 2947873) B2947873
theorem B2619791 : Blo 1160639 2619791 := bstep (se 1 (by rfl) ⟨1964843, by rfl⟩ : syracuseStep 2619791 = 3929687) B3929687
theorem B1473223 : Blo 1160639 1473223 := bstep (se 1 (by rfl) ⟨1104917, by rfl⟩ : syracuseStep 1473223 = 2209835) B2209835
theorem B2620115 : Blo 1160639 2620115 := bstep (se 1 (by rfl) ⟨1965086, by rfl⟩ : syracuseStep 2620115 = 3930173) B3930173
theorem B7437203 : Blo 1160639 7437203 := bstep (se 1 (by rfl) ⟨5577902, by rfl⟩ : syracuseStep 7437203 = 11155805) B11155805
theorem B1965019 : Blo 1160639 1965019 := bstep (se 1 (by rfl) ⟨1473764, by rfl⟩ : syracuseStep 1965019 = 2947529) B2947529
theorem B1309819 : Blo 1160639 1309819 := bstep (se 1 (by rfl) ⟨982364, by rfl⟩ : syracuseStep 1309819 = 1964729) B1964729
theorem B2096327 : Blo 1160639 2096327 := bstep (se 1 (by rfl) ⟨1572245, by rfl⟩ : syracuseStep 2096327 = 3144491) B3144491
theorem B1473967 : Blo 1160639 1473967 := bstep (se 1 (by rfl) ⟨1105475, by rfl⟩ : syracuseStep 1473967 = 2210951) B2210951
theorem B3145225 : Blo 1160639 3145225 := bstep (se 2 (by rfl) ⟨1179459, by rfl⟩ : syracuseStep 3145225 = 2358919) B2358919
theorem B11173565 : Blo 1160639 11173565 := bstep (se 3 (by rfl) ⟨2095043, by rfl⟩ : syracuseStep 11173565 = 4190087) B4190087
theorem B8946425 : Blo 1160639 8946425 := bstep (se 2 (by rfl) ⟨3354909, by rfl⟩ : syracuseStep 8946425 = 6709819) B6709819
theorem B6292333 : Blo 1160639 6292333 := bstep (se 3 (by rfl) ⟨1179812, by rfl⟩ : syracuseStep 6292333 = 2359625) B2359625
theorem B8815553 : Blo 1160639 8815553 := bstep (se 2 (by rfl) ⟨3305832, by rfl⟩ : syracuseStep 8815553 = 6611665) B6611665
theorem B22348817 : Blo 1160639 22348817 := bstep (se 2 (by rfl) ⟨8380806, by rfl⟩ : syracuseStep 22348817 = 16761613) B16761613
theorem B2655355 : Blo 1160639 2655355 := bstep (se 1 (by rfl) ⟨1991516, by rfl⟩ : syracuseStep 2655355 = 3983033) B3983033
theorem B16779143 : Blo 1160639 16779143 := bstep (se 1 (by rfl) ⟨12584357, by rfl⟩ : syracuseStep 16779143 = 25168715) B25168715
theorem B2984359 : Blo 1160639 2984359 := bstep (se 1 (by rfl) ⟨2238269, by rfl⟩ : syracuseStep 2984359 = 4476539) B4476539
theorem B3181025 : Blo 1160639 3181025 := bstep (se 2 (by rfl) ⟨1192884, by rfl⟩ : syracuseStep 3181025 = 2385769) B2385769
theorem B5311115 : Blo 1160639 5311115 := bstep (se 1 (by rfl) ⟨3983336, by rfl⟩ : syracuseStep 5311115 = 7966673) B7966673
theorem B12586049 : Blo 1160639 12586049 := bstep (se 2 (by rfl) ⟨4719768, by rfl⟩ : syracuseStep 12586049 = 9439537) B9439537
theorem B11177027 : Blo 1160639 11177027 := bstep (se 1 (by rfl) ⟨8382770, by rfl⟩ : syracuseStep 11177027 = 16765541) B16765541
theorem B7441793 : Blo 1160639 7441793 := bstep (se 2 (by rfl) ⟨2790672, by rfl⟩ : syracuseStep 7441793 = 5581345) B5581345
theorem B5311873 : Blo 1160639 5311873 := bstep (se 2 (by rfl) ⟨1991952, by rfl⟩ : syracuseStep 5311873 = 3983905) B3983905
theorem B6295121 : Blo 1160639 6295121 := bstep (se 2 (by rfl) ⟨2360670, by rfl⟩ : syracuseStep 6295121 = 4721341) B4721341
theorem B6622829 : Blo 1160639 6622829 := bstep (se 3 (by rfl) ⟨1241780, by rfl⟩ : syracuseStep 6622829 = 2483561) B2483561
theorem B5377799 : Blo 1160639 5377799 := bstep (se 1 (by rfl) ⟨4033349, by rfl⟩ : syracuseStep 5377799 = 8066699) B8066699
theorem B1741223 : Blo 1160639 1741223 := bstep (se 1 (by rfl) ⟨1305917, by rfl⟩ : syracuseStep 1741223 = 2611835) B2611835
theorem B1741307 : Blo 1160639 1741307 := bstep (se 1 (by rfl) ⟨1305980, by rfl⟩ : syracuseStep 1741307 = 2611961) B2611961
theorem B3314297 : Blo 1160639 3314297 := bstep (se 2 (by rfl) ⟨1242861, by rfl⟩ : syracuseStep 3314297 = 2485723) B2485723
theorem B1741433 : Blo 1160639 1741433 := bstep (se 2 (by rfl) ⟨653037, by rfl⟩ : syracuseStep 1741433 = 1306075) B1306075
theorem B1741487 : Blo 1160639 1741487 := bstep (se 1 (by rfl) ⟨1306115, by rfl⟩ : syracuseStep 1741487 = 2612231) B2612231
theorem B1741535 : Blo 1160639 1741535 := bstep (se 1 (by rfl) ⟨1306151, by rfl⟩ : syracuseStep 1741535 = 2612303) B2612303
theorem B1741799 : Blo 1160639 1741799 := bstep (se 1 (by rfl) ⟨1306349, by rfl⟩ : syracuseStep 1741799 = 2612699) B2612699
theorem B8819927 : Blo 1160639 8819927 := bstep (se 1 (by rfl) ⟨6614945, by rfl⟩ : syracuseStep 8819927 = 13229891) B13229891
theorem B1742057 : Blo 1160639 1742057 := bstep (se 2 (by rfl) ⟨653271, by rfl⟩ : syracuseStep 1742057 = 1306543) B1306543
theorem B1742111 : Blo 1160639 1742111 := bstep (se 1 (by rfl) ⟨1306583, by rfl⟩ : syracuseStep 1742111 = 2613167) B2613167
theorem B9442655 : Blo 1160639 9442655 := bstep (se 1 (by rfl) ⟨7081991, by rfl⟩ : syracuseStep 9442655 = 14163983) B14163983
theorem B2987387 : Blo 1160639 2987387 := bstep (se 1 (by rfl) ⟨2240540, by rfl⟩ : syracuseStep 2987387 = 4481081) B4481081
theorem B1742279 : Blo 1160639 1742279 := bstep (se 1 (by rfl) ⟨1306709, by rfl⟩ : syracuseStep 1742279 = 2613419) B2613419
theorem B1742633 : Blo 1160639 1742633 := bstep (se 2 (by rfl) ⟨653487, by rfl⟩ : syracuseStep 1742633 = 1306975) B1306975
theorem B1742639 : Blo 1160639 1742639 := bstep (se 1 (by rfl) ⟨1306979, by rfl⟩ : syracuseStep 1742639 = 2613959) B2613959
theorem B6625313 : Blo 1160639 6625313 := bstep (se 2 (by rfl) ⟨2484492, by rfl⟩ : syracuseStep 6625313 = 4968985) B4968985
theorem B1743113 : Blo 1160639 1743113 := bstep (se 2 (by rfl) ⟨653667, by rfl⟩ : syracuseStep 1743113 = 1307335) B1307335
theorem B1743215 : Blo 1160639 1743215 := bstep (se 1 (by rfl) ⟨1307411, by rfl⟩ : syracuseStep 1743215 = 2614823) B2614823
theorem B99359227 : Blo 1160639 99359227 := bstep (se 1 (by rfl) ⟨74519420, by rfl⟩ : syracuseStep 99359227 = 149038841) B149038841
theorem B1743431 : Blo 1160639 1743431 := bstep (se 1 (by rfl) ⟨1307573, by rfl⟩ : syracuseStep 1743431 = 2615147) B2615147
theorem B1743467 : Blo 1160639 1743467 := bstep (se 1 (by rfl) ⟨1307600, by rfl⟩ : syracuseStep 1743467 = 2615201) B2615201
theorem B3185335 : Blo 1160639 3185335 := bstep (se 1 (by rfl) ⟨2389001, by rfl⟩ : syracuseStep 3185335 = 4778003) B4778003
theorem B1743695 : Blo 1160639 1743695 := bstep (se 1 (by rfl) ⟨1307771, by rfl⟩ : syracuseStep 1743695 = 2615543) B2615543
theorem B33528761 : Blo 1160639 33528761 := bstep (se 2 (by rfl) ⟨12573285, by rfl⟩ : syracuseStep 33528761 = 25146571) B25146571
theorem B1744091 : Blo 1160639 1744091 := bstep (se 1 (by rfl) ⟨1308068, by rfl⟩ : syracuseStep 1744091 = 2616137) B2616137
theorem B2792681 : Blo 1160639 2792681 := bstep (se 2 (by rfl) ⟨1047255, by rfl⟩ : syracuseStep 2792681 = 2094511) B2094511
theorem B1744265 : Blo 1160639 1744265 := bstep (se 2 (by rfl) ⟨654099, by rfl⟩ : syracuseStep 1744265 = 1308199) B1308199
theorem B1744619 : Blo 1160639 1744619 := bstep (se 1 (by rfl) ⟨1308464, by rfl⟩ : syracuseStep 1744619 = 2616929) B2616929
theorem B2203433 : Blo 1160639 2203433 := bstep (se 2 (by rfl) ⟨826287, by rfl⟩ : syracuseStep 2203433 = 1652575) B1652575
theorem B28286779 : Blo 1160639 28286779 := bstep (se 1 (by rfl) ⟨21215084, by rfl⟩ : syracuseStep 28286779 = 42430169) B42430169
theorem B1744847 : Blo 1160639 1744847 := bstep (se 1 (by rfl) ⟨1308635, by rfl⟩ : syracuseStep 1744847 = 2617271) B2617271
theorem B1745243 : Blo 1160639 1745243 := bstep (se 1 (by rfl) ⟨1308932, by rfl⟩ : syracuseStep 1745243 = 2617865) B2617865
theorem B1745471 : Blo 1160639 1745471 := bstep (se 1 (by rfl) ⟨1309103, by rfl⟩ : syracuseStep 1745471 = 2618207) B2618207
theorem B1745591 : Blo 1160639 1745591 := bstep (se 1 (by rfl) ⟨1309193, by rfl⟩ : syracuseStep 1745591 = 2618387) B2618387
theorem B2204435 : Blo 1160639 2204435 := bstep (se 1 (by rfl) ⟨1653326, by rfl⟩ : syracuseStep 2204435 = 3306653) B3306653
theorem B1745819 : Blo 1160639 1745819 := bstep (se 1 (by rfl) ⟨1309364, by rfl⟩ : syracuseStep 1745819 = 2618729) B2618729
theorem B2204587 : Blo 1160639 2204587 := bstep (se 1 (by rfl) ⟨1653440, by rfl⟩ : syracuseStep 2204587 = 3306881) B3306881
theorem B7447555 : Blo 1160639 7447555 := bstep (se 1 (by rfl) ⟨5585666, by rfl⟩ : syracuseStep 7447555 = 11171333) B11171333
theorem B8823815 : Blo 1160639 8823815 := bstep (se 1 (by rfl) ⟨6617861, by rfl⟩ : syracuseStep 8823815 = 13235723) B13235723
theorem B2204815 : Blo 1160639 2204815 := bstep (se 1 (by rfl) ⟨1653611, by rfl⟩ : syracuseStep 2204815 = 3307223) B3307223
theorem B2204891 : Blo 1160639 2204891 := bstep (se 1 (by rfl) ⟨1653668, by rfl⟩ : syracuseStep 2204891 = 3307337) B3307337
theorem B1746215 : Blo 1160639 1746215 := bstep (se 1 (by rfl) ⟨1309661, by rfl⟩ : syracuseStep 1746215 = 2619323) B2619323
theorem B1746299 : Blo 1160639 1746299 := bstep (se 1 (by rfl) ⟨1309724, by rfl⟩ : syracuseStep 1746299 = 2619449) B2619449
theorem B1746425 : Blo 1160639 1746425 := bstep (se 2 (by rfl) ⟨654909, by rfl⟩ : syracuseStep 1746425 = 1309819) B1309819
theorem B1746527 : Blo 1160639 1746527 := bstep (se 1 (by rfl) ⟨1309895, by rfl⟩ : syracuseStep 1746527 = 2619791) B2619791
theorem B5973689 : Blo 1160639 5973689 := bstep (se 2 (by rfl) ⟨2240133, by rfl⟩ : syracuseStep 5973689 = 4480267) B4480267
theorem B1746743 : Blo 1160639 1746743 := bstep (se 1 (by rfl) ⟨1310057, by rfl⟩ : syracuseStep 1746743 = 2620115) B2620115
theorem B9938821 : Blo 1160639 9938821 := bstep (se 4 (by rfl) ⟨931764, by rfl⟩ : syracuseStep 9938821 = 1863529) B1863529
theorem B4958135 : Blo 1160639 4958135 := bstep (se 1 (by rfl) ⟨3718601, by rfl⟩ : syracuseStep 4958135 = 7437203) B7437203
theorem B7448557 : Blo 1160639 7448557 := bstep (se 3 (by rfl) ⟨1396604, by rfl⟩ : syracuseStep 7448557 = 2793209) B2793209
theorem B7449043 : Blo 1160639 7449043 := bstep (se 1 (by rfl) ⟨5586782, by rfl⟩ : syracuseStep 7449043 = 11173565) B11173565
theorem B9939779 : Blo 1160639 9939779 := bstep (se 1 (by rfl) ⟨7454834, by rfl⟩ : syracuseStep 9939779 = 14909669) B14909669
theorem B4467581 : Blo 1160639 4467581 := bstep (se 3 (by rfl) ⟨837671, by rfl⟩ : syracuseStep 4467581 = 1675343) B1675343
theorem B9677905 : Blo 1160639 9677905 := bstep (se 2 (by rfl) ⟨3629214, by rfl⟩ : syracuseStep 9677905 = 7258429) B7258429
theorem B6630619 : Blo 1160639 6630619 := bstep (se 1 (by rfl) ⟨4972964, by rfl⟩ : syracuseStep 6630619 = 9945929) B9945929
theorem B2797139 : Blo 1160639 2797139 := bstep (se 1 (by rfl) ⟨2097854, by rfl⟩ : syracuseStep 2797139 = 4195709) B4195709
theorem B2797217 : Blo 1160639 2797217 := bstep (se 2 (by rfl) ⟨1048956, by rfl⟩ : syracuseStep 2797217 = 2097913) B2097913
theorem B2797697 : Blo 1160639 2797697 := bstep (se 2 (by rfl) ⟨1049136, by rfl⟩ : syracuseStep 2797697 = 2098273) B2098273
theorem B45363473 : Blo 1160639 45363473 := bstep (se 2 (by rfl) ⟨17011302, by rfl⟩ : syracuseStep 45363473 = 34022605) B34022605
theorem B9941555 : Blo 1160639 9941555 := bstep (se 1 (by rfl) ⟨7456166, by rfl⟩ : syracuseStep 9941555 = 14912333) B14912333
theorem B2208377 : Blo 1160639 2208377 := bstep (se 2 (by rfl) ⟨828141, by rfl⟩ : syracuseStep 2208377 = 1656283) B1656283
theorem B11187173 : Blo 1160639 11187173 := bstep (se 4 (by rfl) ⟨1048797, by rfl⟩ : syracuseStep 11187173 = 2097595) B2097595
theorem B11187325 : Blo 1160639 11187325 := bstep (se 3 (by rfl) ⟨2097623, by rfl⟩ : syracuseStep 11187325 = 4195247) B4195247
theorem B18363671 : Blo 1160639 18363671 := bstep (se 1 (by rfl) ⟨13772753, by rfl⟩ : syracuseStep 18363671 = 27545507) B27545507
theorem B12563905 : Blo 1160639 12563905 := bstep (se 2 (by rfl) ⟨4711464, by rfl⟩ : syracuseStep 12563905 = 9422929) B9422929
theorem B1160699 : Blo 1160639 1160699 := bstep (se 1 (by rfl) ⟨870524, by rfl⟩ : syracuseStep 1160699 = 1741049) B1741049
theorem B5879303 : Blo 1160639 5879303 := bstep (se 1 (by rfl) ⟨4409477, by rfl⟩ : syracuseStep 5879303 = 8818955) B8818955
theorem B1160767 : Blo 1160639 1160767 := bstep (se 1 (by rfl) ⟨870575, by rfl⟩ : syracuseStep 1160767 = 1741151) B1741151
theorem B1160775 : Blo 1160639 1160775 := bstep (se 1 (by rfl) ⟨870581, by rfl⟩ : syracuseStep 1160775 = 1741163) B1741163
theorem B1160927 : Blo 1160639 1160927 := bstep (se 1 (by rfl) ⟨870695, by rfl⟩ : syracuseStep 1160927 = 1741391) B1741391
theorem B1161007 : Blo 1160639 1161007 := bstep (se 1 (by rfl) ⟨870755, by rfl⟩ : syracuseStep 1161007 = 1741511) B1741511
theorem B1161115 : Blo 1160639 1161115 := bstep (se 1 (by rfl) ⟨870836, by rfl⟩ : syracuseStep 1161115 = 1741673) B1741673
theorem B1161167 : Blo 1160639 1161167 := bstep (se 1 (by rfl) ⟨870875, by rfl⟩ : syracuseStep 1161167 = 1741751) B1741751
theorem B1161191 : Blo 1160639 1161191 := bstep (se 1 (by rfl) ⟨870893, by rfl⟩ : syracuseStep 1161191 = 1741787) B1741787
theorem B5879789 : Blo 1160639 5879789 := bstep (se 3 (by rfl) ⟨1102460, by rfl⟩ : syracuseStep 5879789 = 2204921) B2204921
theorem B16758845 : Blo 1160639 16758845 := bstep (se 3 (by rfl) ⟨3142283, by rfl⟩ : syracuseStep 16758845 = 6284567) B6284567
theorem B1161503 : Blo 1160639 1161503 := bstep (se 1 (by rfl) ⟨871127, by rfl⟩ : syracuseStep 1161503 = 1742255) B1742255
theorem B1161563 : Blo 1160639 1161563 := bstep (se 1 (by rfl) ⟨871172, by rfl⟩ : syracuseStep 1161563 = 1742345) B1742345
theorem B1161583 : Blo 1160639 1161583 := bstep (se 1 (by rfl) ⟨871187, by rfl⟩ : syracuseStep 1161583 = 1742375) B1742375
theorem B1161639 : Blo 1160639 1161639 := bstep (se 1 (by rfl) ⟨871229, by rfl⟩ : syracuseStep 1161639 = 1742459) B1742459
theorem B5880275 : Blo 1160639 5880275 := bstep (se 1 (by rfl) ⟨4410206, by rfl⟩ : syracuseStep 5880275 = 8820413) B8820413
theorem B1161723 : Blo 1160639 1161723 := bstep (se 1 (by rfl) ⟨871292, by rfl⟩ : syracuseStep 1161723 = 1742585) B1742585
theorem B1161791 : Blo 1160639 1161791 := bstep (se 1 (by rfl) ⟨871343, by rfl⟩ : syracuseStep 1161791 = 1742687) B1742687
theorem B1161799 : Blo 1160639 1161799 := bstep (se 1 (by rfl) ⟨871349, by rfl⟩ : syracuseStep 1161799 = 1742699) B1742699
theorem B1161951 : Blo 1160639 1161951 := bstep (se 1 (by rfl) ⟨871463, by rfl⟩ : syracuseStep 1161951 = 1742927) B1742927
theorem B5880599 : Blo 1160639 5880599 := bstep (se 1 (by rfl) ⟨4410449, by rfl⟩ : syracuseStep 5880599 = 8820899) B8820899
theorem B1162031 : Blo 1160639 1162031 := bstep (se 1 (by rfl) ⟨871523, by rfl⟩ : syracuseStep 1162031 = 1743047) B1743047
theorem B1162139 : Blo 1160639 1162139 := bstep (se 1 (by rfl) ⟨871604, by rfl⟩ : syracuseStep 1162139 = 1743209) B1743209
theorem B7945147 : Blo 1160639 7945147 := bstep (se 1 (by rfl) ⟨5958860, by rfl⟩ : syracuseStep 7945147 = 11917721) B11917721
theorem B1162191 : Blo 1160639 1162191 := bstep (se 1 (by rfl) ⟨871643, by rfl⟩ : syracuseStep 1162191 = 1743287) B1743287
theorem B1162215 : Blo 1160639 1162215 := bstep (se 1 (by rfl) ⟨871661, by rfl⟩ : syracuseStep 1162215 = 1743323) B1743323
theorem B2210807 : Blo 1160639 2210807 := bstep (se 1 (by rfl) ⟨1658105, by rfl⟩ : syracuseStep 2210807 = 3316211) B3316211
theorem B1162527 : Blo 1160639 1162527 := bstep (se 1 (by rfl) ⟨871895, by rfl⟩ : syracuseStep 1162527 = 1743791) B1743791
theorem B1162587 : Blo 1160639 1162587 := bstep (se 1 (by rfl) ⟨871940, by rfl⟩ : syracuseStep 1162587 = 1743881) B1743881
theorem B1162607 : Blo 1160639 1162607 := bstep (se 1 (by rfl) ⟨871955, by rfl⟩ : syracuseStep 1162607 = 1743911) B1743911
theorem B1162663 : Blo 1160639 1162663 := bstep (se 1 (by rfl) ⟨871997, by rfl⟩ : syracuseStep 1162663 = 1743995) B1743995
theorem B1162747 : Blo 1160639 1162747 := bstep (se 1 (by rfl) ⟨872060, by rfl⟩ : syracuseStep 1162747 = 1744121) B1744121
theorem B1162815 : Blo 1160639 1162815 := bstep (se 1 (by rfl) ⟨872111, by rfl⟩ : syracuseStep 1162815 = 1744223) B1744223
theorem B1162823 : Blo 1160639 1162823 := bstep (se 1 (by rfl) ⟨872117, by rfl⟩ : syracuseStep 1162823 = 1744235) B1744235
theorem B5586515 : Blo 1160639 5586515 := bstep (se 1 (by rfl) ⟨4189886, by rfl⟩ : syracuseStep 5586515 = 8379773) B8379773
theorem B1162975 : Blo 1160639 1162975 := bstep (se 1 (by rfl) ⟨872231, by rfl⟩ : syracuseStep 1162975 = 1744463) B1744463
theorem B1163055 : Blo 1160639 1163055 := bstep (se 1 (by rfl) ⟨872291, by rfl⟩ : syracuseStep 1163055 = 1744583) B1744583
theorem B4407169 : Blo 1160639 4407169 := bstep (se 2 (by rfl) ⟨1652688, by rfl⟩ : syracuseStep 4407169 = 3305377) B3305377
theorem B10600321 : Blo 1160639 10600321 := bstep (se 2 (by rfl) ⟨3975120, by rfl⟩ : syracuseStep 10600321 = 7950241) B7950241
theorem B1163163 : Blo 1160639 1163163 := bstep (se 1 (by rfl) ⟨872372, by rfl⟩ : syracuseStep 1163163 = 1744745) B1744745
theorem B1163215 : Blo 1160639 1163215 := bstep (se 1 (by rfl) ⟨872411, by rfl⟩ : syracuseStep 1163215 = 1744823) B1744823
theorem B1163239 : Blo 1160639 1163239 := bstep (se 1 (by rfl) ⟨872429, by rfl⟩ : syracuseStep 1163239 = 1744859) B1744859
theorem B1163551 : Blo 1160639 1163551 := bstep (se 1 (by rfl) ⟨872663, by rfl⟩ : syracuseStep 1163551 = 1745327) B1745327
theorem B1163611 : Blo 1160639 1163611 := bstep (se 1 (by rfl) ⟨872708, by rfl⟩ : syracuseStep 1163611 = 1745417) B1745417
theorem B5882219 : Blo 1160639 5882219 := bstep (se 1 (by rfl) ⟨4411664, by rfl⟩ : syracuseStep 5882219 = 8823329) B8823329
theorem B1163631 : Blo 1160639 1163631 := bstep (se 1 (by rfl) ⟨872723, by rfl⟩ : syracuseStep 1163631 = 1745447) B1745447
theorem B1163687 : Blo 1160639 1163687 := bstep (se 1 (by rfl) ⟨872765, by rfl⟩ : syracuseStep 1163687 = 1745531) B1745531
theorem B1163771 : Blo 1160639 1163771 := bstep (se 1 (by rfl) ⟨872828, by rfl⟩ : syracuseStep 1163771 = 1745657) B1745657
theorem B25149953 : Blo 1160639 25149953 := bstep (se 2 (by rfl) ⟨9431232, by rfl⟩ : syracuseStep 25149953 = 18862465) B18862465
theorem B1163839 : Blo 1160639 1163839 := bstep (se 1 (by rfl) ⟨872879, by rfl⟩ : syracuseStep 1163839 = 1745759) B1745759
theorem B4964935 : Blo 1160639 4964935 := bstep (se 1 (by rfl) ⟨3723701, by rfl⟩ : syracuseStep 4964935 = 7447403) B7447403
theorem B1163847 : Blo 1160639 1163847 := bstep (se 1 (by rfl) ⟨872885, by rfl⟩ : syracuseStep 1163847 = 1745771) B1745771
theorem B4407929 : Blo 1160639 4407929 := bstep (se 2 (by rfl) ⟨1652973, by rfl⟩ : syracuseStep 4407929 = 3305947) B3305947
theorem B1655417 : Blo 1160639 1655417 := bstep (se 2 (by rfl) ⟨620781, by rfl⟩ : syracuseStep 1655417 = 1241563) B1241563
theorem B13222601 : Blo 1160639 13222601 := bstep (se 2 (by rfl) ⟨4958475, by rfl⟩ : syracuseStep 13222601 = 9916951) B9916951
theorem B1163999 : Blo 1160639 1163999 := bstep (se 1 (by rfl) ⟨872999, by rfl⟩ : syracuseStep 1163999 = 1745999) B1745999
theorem B1164079 : Blo 1160639 1164079 := bstep (se 1 (by rfl) ⟨873059, by rfl⟩ : syracuseStep 1164079 = 1746119) B1746119
theorem B1164187 : Blo 1160639 1164187 := bstep (se 1 (by rfl) ⟨873140, by rfl⟩ : syracuseStep 1164187 = 1746281) B1746281
theorem B25183169 : Blo 1160639 25183169 := bstep (se 2 (by rfl) ⟨9443688, by rfl⟩ : syracuseStep 25183169 = 18887377) B18887377
theorem B1164239 : Blo 1160639 1164239 := bstep (se 1 (by rfl) ⟨873179, by rfl⟩ : syracuseStep 1164239 = 1746359) B1746359
theorem B1164263 : Blo 1160639 1164263 := bstep (se 1 (by rfl) ⟨873197, by rfl⟩ : syracuseStep 1164263 = 1746395) B1746395
theorem B2868263 : Blo 1160639 2868263 := bstep (se 1 (by rfl) ⟨2151197, by rfl⟩ : syracuseStep 2868263 = 4302395) B4302395
theorem B4408445 : Blo 1160639 4408445 := bstep (se 3 (by rfl) ⟨826583, by rfl⟩ : syracuseStep 4408445 = 1653167) B1653167
theorem B10601705 : Blo 1160639 10601705 := bstep (se 2 (by rfl) ⟨3975639, by rfl⟩ : syracuseStep 10601705 = 7951279) B7951279
theorem B1164575 : Blo 1160639 1164575 := bstep (se 1 (by rfl) ⟨873431, by rfl⟩ : syracuseStep 1164575 = 1746863) B1746863
theorem B1164635 : Blo 1160639 1164635 := bstep (se 1 (by rfl) ⟨873476, by rfl⟩ : syracuseStep 1164635 = 1746953) B1746953
theorem B18400621 : Blo 1160639 18400621 := bstep (se 3 (by rfl) ⟨3450116, by rfl⟩ : syracuseStep 18400621 = 6900233) B6900233
theorem B37766573 : Blo 1160639 37766573 := bstep (se 3 (by rfl) ⟨7081232, by rfl⟩ : syracuseStep 37766573 = 14162465) B14162465
theorem B12568097 : Blo 1160639 12568097 := bstep (se 2 (by rfl) ⟨4713036, by rfl⟩ : syracuseStep 12568097 = 9426073) B9426073
theorem B5883677 : Blo 1160639 5883677 := bstep (se 3 (by rfl) ⟨1103189, by rfl⟩ : syracuseStep 5883677 = 2206379) B2206379
theorem B45893873 : Blo 1160639 45893873 := bstep (se 2 (by rfl) ⟨17210202, by rfl⟩ : syracuseStep 45893873 = 34420405) B34420405
theorem B3918077 : Blo 1160639 3918077 := bstep (se 3 (by rfl) ⟨734639, by rfl⟩ : syracuseStep 3918077 = 1469279) B1469279
theorem B1395067 : Blo 1160639 1395067 := bstep (se 1 (by rfl) ⟨1046300, by rfl⟩ : syracuseStep 1395067 = 2092601) B2092601
theorem B13421483 : Blo 1160639 13421483 := bstep (se 1 (by rfl) ⟨10066112, by rfl⟩ : syracuseStep 13421483 = 20132225) B20132225
theorem B7457807 : Blo 1160639 7457807 := bstep (se 1 (by rfl) ⟨5593355, by rfl⟩ : syracuseStep 7457807 = 11186711) B11186711
theorem B3918887 : Blo 1160639 3918887 := bstep (se 1 (by rfl) ⟨2939165, by rfl⟩ : syracuseStep 3918887 = 5878331) B5878331
theorem B4410557 : Blo 1160639 4410557 := bstep (se 3 (by rfl) ⟨826979, by rfl⟩ : syracuseStep 4410557 = 1653959) B1653959
theorem B5590205 : Blo 1160639 5590205 := bstep (se 3 (by rfl) ⟨1048163, by rfl⟩ : syracuseStep 5590205 = 2096327) B2096327
theorem B3919319 : Blo 1160639 3919319 := bstep (se 1 (by rfl) ⟨2939489, by rfl⟩ : syracuseStep 3919319 = 5878979) B5878979
theorem B63721025 : Blo 1160639 63721025 := bstep (se 2 (by rfl) ⟨23895384, by rfl⟩ : syracuseStep 63721025 = 47790769) B47790769
theorem B51007265 : Blo 1160639 51007265 := bstep (se 2 (by rfl) ⟨19127724, by rfl⟩ : syracuseStep 51007265 = 38255449) B38255449
theorem B91868975 : Blo 1160639 91868975 := bstep (se 1 (by rfl) ⟨68901731, by rfl⟩ : syracuseStep 91868975 = 137803463) B137803463
theorem B4969259 : Blo 1160639 4969259 := bstep (se 1 (by rfl) ⟨3726944, by rfl⟩ : syracuseStep 4969259 = 7453889) B7453889
theorem B11162569 : Blo 1160639 11162569 := bstep (se 2 (by rfl) ⟨4185963, by rfl⟩ : syracuseStep 11162569 = 8371927) B8371927
theorem B3920993 : Blo 1160639 3920993 := bstep (se 2 (by rfl) ⟨1470372, by rfl⟩ : syracuseStep 3920993 = 2940745) B2940745
theorem B5297495 : Blo 1160639 5297495 := bstep (se 1 (by rfl) ⟨3973121, by rfl⟩ : syracuseStep 5297495 = 7946243) B7946243
theorem B38196605 : Blo 1160639 38196605 := bstep (se 3 (by rfl) ⟨7161863, by rfl⟩ : syracuseStep 38196605 = 14323727) B14323727
theorem B22369729 : Blo 1160639 22369729 := bstep (se 2 (by rfl) ⟨8388648, by rfl⟩ : syracuseStep 22369729 = 16777297) B16777297
theorem B1988039 : Blo 1160639 1988039 := bstep (se 1 (by rfl) ⟨1491029, by rfl⟩ : syracuseStep 1988039 = 2982059) B2982059
theorem B5035553 : Blo 1160639 5035553 := bstep (se 2 (by rfl) ⟨1888332, by rfl⟩ : syracuseStep 5035553 = 3776665) B3776665
theorem B5592665 : Blo 1160639 5592665 := bstep (se 2 (by rfl) ⟨2097249, by rfl⟩ : syracuseStep 5592665 = 4194499) B4194499
theorem B3724957 : Blo 1160639 3724957 := bstep (se 3 (by rfl) ⟨698429, by rfl⟩ : syracuseStep 3724957 = 1396859) B1396859
theorem B3725111 : Blo 1160639 3725111 := bstep (se 1 (by rfl) ⟨2793833, by rfl⟩ : syracuseStep 3725111 = 5587667) B5587667
theorem B4413473 : Blo 1160639 4413473 := bstep (se 2 (by rfl) ⟨1655052, by rfl⟩ : syracuseStep 4413473 = 3310105) B3310105
theorem B2611529 : Blo 1160639 2611529 := bstep (se 2 (by rfl) ⟨979323, by rfl⟩ : syracuseStep 2611529 = 1958647) B1958647
theorem B2611547 : Blo 1160639 2611547 := bstep (se 1 (by rfl) ⟨1958660, by rfl⟩ : syracuseStep 2611547 = 3917321) B3917321
theorem B3922343 : Blo 1160639 3922343 := bstep (se 1 (by rfl) ⟨2941757, by rfl⟩ : syracuseStep 3922343 = 5883515) B5883515
theorem B3922505 : Blo 1160639 3922505 := bstep (se 2 (by rfl) ⟨1470939, by rfl⟩ : syracuseStep 3922505 = 2941879) B2941879
theorem B6281975 : Blo 1160639 6281975 := bstep (se 1 (by rfl) ⟨4711481, by rfl⟩ : syracuseStep 6281975 = 9422963) B9422963
theorem B2612123 : Blo 1160639 2612123 := bstep (se 1 (by rfl) ⟨1959092, by rfl⟩ : syracuseStep 2612123 = 3918185) B3918185
theorem B5659579 : Blo 1160639 5659579 := bstep (se 1 (by rfl) ⟨4244684, by rfl⟩ : syracuseStep 5659579 = 8489369) B8489369
theorem B2612321 : Blo 1160639 2612321 := bstep (se 2 (by rfl) ⟨979620, by rfl⟩ : syracuseStep 2612321 = 1959241) B1959241
theorem B2940047 : Blo 1160639 2940047 := bstep (se 1 (by rfl) ⟨2205035, by rfl⟩ : syracuseStep 2940047 = 4410071) B4410071
theorem B2612519 : Blo 1160639 2612519 := bstep (se 1 (by rfl) ⟨1959389, by rfl⟩ : syracuseStep 2612519 = 3918779) B3918779
theorem B5889347 : Blo 1160639 5889347 := bstep (se 1 (by rfl) ⟨4417010, by rfl⟩ : syracuseStep 5889347 = 8834021) B8834021
theorem B7069265 : Blo 1160639 7069265 := bstep (se 2 (by rfl) ⟨2650974, by rfl⟩ : syracuseStep 7069265 = 5301949) B5301949
theorem B2612897 : Blo 1160639 2612897 := bstep (se 2 (by rfl) ⟨979836, by rfl⟩ : syracuseStep 2612897 = 1959673) B1959673
theorem B5889833 : Blo 1160639 5889833 := bstep (se 2 (by rfl) ⟨2208687, by rfl⟩ : syracuseStep 5889833 = 4417375) B4417375
theorem B2613257 : Blo 1160639 2613257 := bstep (se 2 (by rfl) ⟨979971, by rfl⟩ : syracuseStep 2613257 = 1959943) B1959943
theorem B3924179 : Blo 1160639 3924179 := bstep (se 1 (by rfl) ⟨2943134, by rfl⟩ : syracuseStep 3924179 = 5886269) B5886269
theorem B2613671 : Blo 1160639 2613671 := bstep (se 1 (by rfl) ⟨1960253, by rfl⟩ : syracuseStep 2613671 = 3920507) B3920507
theorem B3924449 : Blo 1160639 3924449 := bstep (se 2 (by rfl) ⟨1471668, by rfl⟩ : syracuseStep 3924449 = 2943337) B2943337
theorem B2613779 : Blo 1160639 2613779 := bstep (se 1 (by rfl) ⟨1960334, by rfl⟩ : syracuseStep 2613779 = 3920669) B3920669
theorem B2613833 : Blo 1160639 2613833 := bstep (se 2 (by rfl) ⟨980187, by rfl⟩ : syracuseStep 2613833 = 1960375) B1960375
theorem B5038807 : Blo 1160639 5038807 := bstep (se 1 (by rfl) ⟨3779105, by rfl⟩ : syracuseStep 5038807 = 7558211) B7558211
theorem B1958735 : Blo 1160639 1958735 := bstep (se 1 (by rfl) ⟨1469051, by rfl⟩ : syracuseStep 1958735 = 2938103) B2938103
theorem B5596123 : Blo 1160639 5596123 := bstep (se 1 (by rfl) ⟨4197092, by rfl⟩ : syracuseStep 5596123 = 8394185) B8394185
theorem B2614247 : Blo 1160639 2614247 := bstep (se 1 (by rfl) ⟨1960685, by rfl⟩ : syracuseStep 2614247 = 3921371) B3921371
theorem B2941991 : Blo 1160639 2941991 := bstep (se 1 (by rfl) ⟨2206493, by rfl⟩ : syracuseStep 2941991 = 4412987) B4412987
theorem B5891129 : Blo 1160639 5891129 := bstep (se 2 (by rfl) ⟨2209173, by rfl⟩ : syracuseStep 5891129 = 4418347) B4418347
theorem B2483399 : Blo 1160639 2483399 := bstep (se 1 (by rfl) ⟨1862549, by rfl⟩ : syracuseStep 2483399 = 3725099) B3725099
theorem B2614625 : Blo 1160639 2614625 := bstep (se 2 (by rfl) ⟨980484, by rfl⟩ : syracuseStep 2614625 = 1960969) B1960969
theorem B2942345 : Blo 1160639 2942345 := bstep (se 2 (by rfl) ⟨1103379, by rfl⟩ : syracuseStep 2942345 = 2206759) B2206759
theorem B3728801 : Blo 1160639 3728801 := bstep (se 2 (by rfl) ⟨1398300, by rfl⟩ : syracuseStep 3728801 = 2796601) B2796601
theorem B2614715 : Blo 1160639 2614715 := bstep (se 1 (by rfl) ⟨1961036, by rfl⟩ : syracuseStep 2614715 = 3922073) B3922073
theorem B8054329 : Blo 1160639 8054329 := bstep (se 2 (by rfl) ⟨3020373, by rfl⟩ : syracuseStep 8054329 = 6040747) B6040747
theorem B2614841 : Blo 1160639 2614841 := bstep (se 2 (by rfl) ⟨980565, by rfl⟩ : syracuseStep 2614841 = 1961131) B1961131
theorem B3925691 : Blo 1160639 3925691 := bstep (se 1 (by rfl) ⟨2944268, by rfl⟩ : syracuseStep 3925691 = 5888537) B5888537
theorem B1959727 : Blo 1160639 1959727 := bstep (se 1 (by rfl) ⟨1469795, by rfl⟩ : syracuseStep 1959727 = 2939591) B2939591
theorem B4417361 : Blo 1160639 4417361 := bstep (se 2 (by rfl) ⟨1656510, by rfl⟩ : syracuseStep 4417361 = 3313021) B3313021
theorem B21227501 : Blo 1160639 21227501 := bstep (se 3 (by rfl) ⟨3980156, by rfl⟩ : syracuseStep 21227501 = 7960313) B7960313
theorem B2615507 : Blo 1160639 2615507 := bstep (se 1 (by rfl) ⟨1961630, by rfl⟩ : syracuseStep 2615507 = 3923261) B3923261
theorem B45246701 : Blo 1160639 45246701 := bstep (se 3 (by rfl) ⟨8483756, by rfl⟩ : syracuseStep 45246701 = 16967513) B16967513
theorem B3533053 : Blo 1160639 3533053 := bstep (se 3 (by rfl) ⟨662447, by rfl⟩ : syracuseStep 3533053 = 1324895) B1324895
theorem B2615561 : Blo 1160639 2615561 := bstep (se 2 (by rfl) ⟨980835, by rfl⟩ : syracuseStep 2615561 = 1961671) B1961671
theorem B2484587 : Blo 1160639 2484587 := bstep (se 1 (by rfl) ⟨1863440, by rfl⟩ : syracuseStep 2484587 = 3726881) B3726881
theorem B2615777 : Blo 1160639 2615777 := bstep (se 2 (by rfl) ⟨980916, by rfl⟩ : syracuseStep 2615777 = 1961833) B1961833
theorem B4188779 : Blo 1160639 4188779 := bstep (se 1 (by rfl) ⟨3141584, by rfl⟩ : syracuseStep 4188779 = 6283169) B6283169
theorem B2484911 : Blo 1160639 2484911 := bstep (se 1 (by rfl) ⟨1863683, by rfl⟩ : syracuseStep 2484911 = 3727367) B3727367
theorem B2616083 : Blo 1160639 2616083 := bstep (se 1 (by rfl) ⟨1962062, by rfl⟩ : syracuseStep 2616083 = 3924125) B3924125
theorem B2943823 : Blo 1160639 2943823 := bstep (se 1 (by rfl) ⟨2207867, by rfl⟩ : syracuseStep 2943823 = 4415735) B4415735
theorem B5303335 : Blo 1160639 5303335 := bstep (se 1 (by rfl) ⟨3977501, by rfl⟩ : syracuseStep 5303335 = 7955003) B7955003
theorem B2944097 : Blo 1160639 2944097 := bstep (se 2 (by rfl) ⟨1104036, by rfl⟩ : syracuseStep 2944097 = 2208073) B2208073
theorem B5893235 : Blo 1160639 5893235 := bstep (se 1 (by rfl) ⟨4419926, by rfl⟩ : syracuseStep 5893235 = 8839853) B8839853
theorem B6450299 : Blo 1160639 6450299 := bstep (se 1 (by rfl) ⟨4837724, by rfl⟩ : syracuseStep 6450299 = 9675449) B9675449
theorem B2616443 : Blo 1160639 2616443 := bstep (se 1 (by rfl) ⟨1962332, by rfl⟩ : syracuseStep 2616443 = 3924665) B3924665
theorem B1469659 : Blo 1160639 1469659 := bstep (se 1 (by rfl) ⟨1102244, by rfl⟩ : syracuseStep 1469659 = 2204489) B2204489
theorem B3140857 : Blo 1160639 3140857 := bstep (se 2 (by rfl) ⟨1177821, by rfl⟩ : syracuseStep 3140857 = 2355643) B2355643
theorem B2616569 : Blo 1160639 2616569 := bstep (se 2 (by rfl) ⟨981213, by rfl⟩ : syracuseStep 2616569 = 1962427) B1962427
theorem B2092319 : Blo 1160639 2092319 := bstep (se 1 (by rfl) ⟨1569239, by rfl⟩ : syracuseStep 2092319 = 3138479) B3138479
theorem B1305895 : Blo 1160639 1305895 := bstep (se 1 (by rfl) ⟨979421, by rfl⟩ : syracuseStep 1305895 = 1958843) B1958843
theorem B1305967 : Blo 1160639 1305967 := bstep (se 1 (by rfl) ⟨979475, by rfl⟩ : syracuseStep 1305967 = 1958951) B1958951
theorem B2616713 : Blo 1160639 2616713 := bstep (se 2 (by rfl) ⟨981267, by rfl⟩ : syracuseStep 2616713 = 1962535) B1962535
theorem B2944471 : Blo 1160639 2944471 := bstep (se 1 (by rfl) ⟨2208353, by rfl⟩ : syracuseStep 2944471 = 4416707) B4416707
theorem B9924059 : Blo 1160639 9924059 := bstep (se 1 (by rfl) ⟨7443044, by rfl⟩ : syracuseStep 9924059 = 14886089) B14886089
theorem B2616839 : Blo 1160639 2616839 := bstep (se 1 (by rfl) ⟨1962629, by rfl⟩ : syracuseStep 2616839 = 3925259) B3925259
theorem B1306183 : Blo 1160639 1306183 := bstep (se 1 (by rfl) ⟨979637, by rfl⟩ : syracuseStep 1306183 = 1959275) B1959275
theorem B3927635 : Blo 1160639 3927635 := bstep (se 1 (by rfl) ⟨2945726, by rfl⟩ : syracuseStep 3927635 = 5891453) B5891453
theorem B2354849 : Blo 1160639 2354849 := bstep (se 2 (by rfl) ⟨883068, by rfl⟩ : syracuseStep 2354849 = 1766137) B1766137
theorem B2617019 : Blo 1160639 2617019 := bstep (se 1 (by rfl) ⟨1962764, by rfl⟩ : syracuseStep 2617019 = 3925529) B3925529
theorem B3305195 : Blo 1160639 3305195 := bstep (se 1 (by rfl) ⟨2478896, by rfl⟩ : syracuseStep 3305195 = 4957793) B4957793
theorem B2944775 : Blo 1160639 2944775 := bstep (se 1 (by rfl) ⟨2208581, by rfl⟩ : syracuseStep 2944775 = 4417163) B4417163
theorem B2617145 : Blo 1160639 2617145 := bstep (se 2 (by rfl) ⟨981429, by rfl⟩ : syracuseStep 2617145 = 1962859) B1962859
theorem B5894045 : Blo 1160639 5894045 := bstep (se 3 (by rfl) ⟨1105133, by rfl⟩ : syracuseStep 5894045 = 2210267) B2210267
theorem B4419593 : Blo 1160639 4419593 := bstep (se 2 (by rfl) ⟨1657347, by rfl⟩ : syracuseStep 4419593 = 3314695) B3314695
theorem B13234265 : Blo 1160639 13234265 := bstep (se 2 (by rfl) ⟨4962849, by rfl⟩ : syracuseStep 13234265 = 9925699) B9925699
theorem B5304649 : Blo 1160639 5304649 := bstep (se 2 (by rfl) ⟨1989243, by rfl⟩ : syracuseStep 5304649 = 3978487) B3978487
theorem B1307047 : Blo 1160639 1307047 := bstep (se 1 (by rfl) ⟨980285, by rfl⟩ : syracuseStep 1307047 = 1960571) B1960571
theorem B1962407 : Blo 1160639 1962407 := bstep (se 1 (by rfl) ⟨1471805, by rfl⟩ : syracuseStep 1962407 = 2943611) B2943611
theorem B2617775 : Blo 1160639 2617775 := bstep (se 1 (by rfl) ⟨1963331, by rfl⟩ : syracuseStep 2617775 = 3926663) B3926663
theorem B2617811 : Blo 1160639 2617811 := bstep (se 1 (by rfl) ⟨1963358, by rfl⟩ : syracuseStep 2617811 = 3926717) B3926717
theorem B8483291 : Blo 1160639 8483291 := bstep (se 1 (by rfl) ⟨6362468, by rfl⟩ : syracuseStep 8483291 = 12724937) B12724937
theorem B2945555 : Blo 1160639 2945555 := bstep (se 1 (by rfl) ⟨2209166, by rfl⟩ : syracuseStep 2945555 = 4418333) B4418333
theorem B2617919 : Blo 1160639 2617919 := bstep (se 1 (by rfl) ⟨1963439, by rfl⟩ : syracuseStep 2617919 = 3926879) B3926879
theorem B1962569 : Blo 1160639 1962569 := bstep (se 2 (by rfl) ⟨735963, by rfl⟩ : syracuseStep 1962569 = 1471927) B1471927
theorem B7762553 : Blo 1160639 7762553 := bstep (se 2 (by rfl) ⟨2910957, by rfl⟩ : syracuseStep 7762553 = 5821915) B5821915
theorem B2618027 : Blo 1160639 2618027 := bstep (se 1 (by rfl) ⟨1963520, by rfl⟩ : syracuseStep 2618027 = 3927041) B3927041
theorem B2355887 : Blo 1160639 2355887 := bstep (se 1 (by rfl) ⟨1766915, by rfl⟩ : syracuseStep 2355887 = 3533831) B3533831
theorem B5894855 : Blo 1160639 5894855 := bstep (se 1 (by rfl) ⟨4421141, by rfl⟩ : syracuseStep 5894855 = 8842283) B8842283
theorem B1471279 : Blo 1160639 1471279 := bstep (se 1 (by rfl) ⟨1103459, by rfl⟩ : syracuseStep 1471279 = 2206919) B2206919
theorem B1176475 : Blo 1160639 1176475 := bstep (se 1 (by rfl) ⟨882356, by rfl⟩ : syracuseStep 1176475 = 1764713) B1764713
theorem B1242011 : Blo 1160639 1242011 := bstep (se 1 (by rfl) ⟨931508, by rfl⟩ : syracuseStep 1242011 = 1863017) B1863017
theorem B1307623 : Blo 1160639 1307623 := bstep (se 1 (by rfl) ⟨980717, by rfl⟩ : syracuseStep 1307623 = 1961435) B1961435
theorem B3142631 : Blo 1160639 3142631 := bstep (se 1 (by rfl) ⟨2356973, by rfl⟩ : syracuseStep 3142631 = 4713947) B4713947
theorem B2618567 : Blo 1160639 2618567 := bstep (se 1 (by rfl) ⟨1963925, by rfl⟩ : syracuseStep 2618567 = 3927851) B3927851
theorem B6616313 : Blo 1160639 6616313 := bstep (se 2 (by rfl) ⟨2481117, by rfl⟩ : syracuseStep 6616313 = 4962235) B4962235
theorem B4781351 : Blo 1160639 4781351 := bstep (se 1 (by rfl) ⟨3586013, by rfl⟩ : syracuseStep 4781351 = 7172027) B7172027
theorem B22639961 : Blo 1160639 22639961 := bstep (se 2 (by rfl) ⟨8489985, by rfl⟩ : syracuseStep 22639961 = 16979971) B16979971
theorem B16741727 : Blo 1160639 16741727 := bstep (se 1 (by rfl) ⟨12556295, by rfl⟩ : syracuseStep 16741727 = 25112591) B25112591
theorem B2618747 : Blo 1160639 2618747 := bstep (se 1 (by rfl) ⟨1964060, by rfl⟩ : syracuseStep 2618747 = 3928121) B3928121
theorem B1766855 : Blo 1160639 1766855 := bstep (se 1 (by rfl) ⟨1325141, by rfl⟩ : syracuseStep 1766855 = 2650283) B2650283
theorem B2618873 : Blo 1160639 2618873 := bstep (se 2 (by rfl) ⟨982077, by rfl⟩ : syracuseStep 2618873 = 1964155) B1964155
theorem B2618963 : Blo 1160639 2618963 := bstep (se 1 (by rfl) ⟨1964222, by rfl⟩ : syracuseStep 2618963 = 3928445) B3928445
theorem B1963615 : Blo 1160639 1963615 := bstep (se 1 (by rfl) ⟨1472711, by rfl⟩ : syracuseStep 1963615 = 2945423) B2945423
theorem B2094827 : Blo 1160639 2094827 := bstep (se 1 (by rfl) ⟨1571120, by rfl⟩ : syracuseStep 2094827 = 3142241) B3142241
theorem B2619143 : Blo 1160639 2619143 := bstep (se 1 (by rfl) ⟨1964357, by rfl⟩ : syracuseStep 2619143 = 3928715) B3928715
theorem B1963831 : Blo 1160639 1963831 := bstep (se 1 (by rfl) ⟨1472873, by rfl⟩ : syracuseStep 1963831 = 2945747) B2945747
theorem B44759141 : Blo 1160639 44759141 := bstep (se 4 (by rfl) ⟨4196169, by rfl⟩ : syracuseStep 44759141 = 8392339) B8392339
theorem B1964297 : Blo 1160639 1964297 := bstep (se 2 (by rfl) ⟨736611, by rfl⟩ : syracuseStep 1964297 = 1473223) B1473223
theorem B2947337 : Blo 1160639 2947337 := bstep (se 2 (by rfl) ⟨1105251, by rfl⟩ : syracuseStep 2947337 = 2210503) B2210503
theorem B2619755 : Blo 1160639 2619755 := bstep (se 1 (by rfl) ⟨1964816, by rfl⟩ : syracuseStep 2619755 = 3929633) B3929633
theorem B3930551 : Blo 1160639 3930551 := bstep (se 1 (by rfl) ⟨2947913, by rfl⟩ : syracuseStep 3930551 = 5895827) B5895827
theorem B3144187 : Blo 1160639 3144187 := bstep (se 1 (by rfl) ⟨2358140, by rfl⟩ : syracuseStep 3144187 = 4716281) B4716281
theorem B2619899 : Blo 1160639 2619899 := bstep (se 1 (by rfl) ⟨1964924, by rfl⟩ : syracuseStep 2619899 = 3929849) B3929849
theorem B3308111 : Blo 1160639 3308111 := bstep (se 1 (by rfl) ⟨2481083, by rfl⟩ : syracuseStep 3308111 = 4962167) B4962167
theorem B1309279 : Blo 1160639 1309279 := bstep (se 1 (by rfl) ⟨981959, by rfl⟩ : syracuseStep 1309279 = 1963919) B1963919
theorem B2947691 : Blo 1160639 2947691 := bstep (se 1 (by rfl) ⟨2210768, by rfl⟩ : syracuseStep 2947691 = 4421537) B4421537
theorem B2620025 : Blo 1160639 2620025 := bstep (se 2 (by rfl) ⟨982509, by rfl⟩ : syracuseStep 2620025 = 1965019) B1965019
theorem B51706507 : Blo 1160639 51706507 := bstep (se 1 (by rfl) ⟨38779880, by rfl⟩ : syracuseStep 51706507 = 77559761) B77559761
theorem B2620079 : Blo 1160639 2620079 := bstep (se 1 (by rfl) ⟨1965059, by rfl⟩ : syracuseStep 2620079 = 3930119) B3930119
theorem B2620151 : Blo 1160639 2620151 := bstep (se 1 (by rfl) ⟨1965113, by rfl⟩ : syracuseStep 2620151 = 3930227) B3930227
theorem B2620331 : Blo 1160639 2620331 := bstep (se 1 (by rfl) ⟨1965248, by rfl⟩ : syracuseStep 2620331 = 3930497) B3930497
theorem B1965289 : Blo 1160639 1965289 := bstep (se 2 (by rfl) ⟨736983, by rfl⟩ : syracuseStep 1965289 = 1473967) B1473967
theorem B4193633 : Blo 1160639 4193633 := bstep (se 2 (by rfl) ⟨1572612, by rfl⟩ : syracuseStep 4193633 = 3145225) B3145225
theorem B2653703 : Blo 1160639 2653703 := bstep (se 1 (by rfl) ⟨1990277, by rfl⟩ : syracuseStep 2653703 = 3980555) B3980555
theorem B8814095 : Blo 1160639 8814095 := bstep (se 1 (by rfl) ⟨6610571, by rfl⟩ : syracuseStep 8814095 = 13221143) B13221143
theorem B7437919 : Blo 1160639 7437919 := bstep (se 1 (by rfl) ⟨5578439, by rfl⟩ : syracuseStep 7437919 = 11156879) B11156879
theorem B8815067 : Blo 1160639 8815067 := bstep (se 1 (by rfl) ⟨6611300, by rfl⟩ : syracuseStep 8815067 = 13222601) B13222601
theorem B5964283 : Blo 1160639 5964283 := bstep (se 1 (by rfl) ⟨4473212, by rfl⟩ : syracuseStep 5964283 = 8946425) B8946425
theorem B6619913 : Blo 1160639 6619913 := bstep (se 2 (by rfl) ⟨2482467, by rfl⟩ : syracuseStep 6619913 = 4964935) B4964935
theorem B6718409 : Blo 1160639 6718409 := bstep (se 2 (by rfl) ⟨2519403, by rfl⟩ : syracuseStep 6718409 = 5038807) B5038807
theorem B8389777 : Blo 1160639 8389777 := bstep (se 2 (by rfl) ⟨3146166, by rfl⟩ : syracuseStep 8389777 = 6292333) B6292333
theorem B9930073 : Blo 1160639 9930073 := bstep (se 2 (by rfl) ⟨3723777, by rfl⟩ : syracuseStep 9930073 = 7447555) B7447555
theorem B3540473 : Blo 1160639 3540473 := bstep (se 2 (by rfl) ⟨1327677, by rfl⟩ : syracuseStep 3540473 = 2655355) B2655355
theorem B3540743 : Blo 1160639 3540743 := bstep (se 1 (by rfl) ⟨2655557, by rfl⟩ : syracuseStep 3540743 = 5311115) B5311115
theorem B8947655 : Blo 1160639 8947655 := bstep (se 1 (by rfl) ⟨6710741, by rfl⟩ : syracuseStep 8947655 = 13421483) B13421483
theorem B8390699 : Blo 1160639 8390699 := bstep (se 1 (by rfl) ⟨6293024, by rfl⟩ : syracuseStep 8390699 = 12586049) B12586049
theorem B4196747 : Blo 1160639 4196747 := bstep (se 1 (by rfl) ⟨3147560, by rfl⟩ : syracuseStep 4196747 = 6295121) B6295121
theorem B3312029 : Blo 1160639 3312029 := bstep (se 3 (by rfl) ⟨621005, by rfl⟩ : syracuseStep 3312029 = 1242011) B1242011
theorem B61245983 : Blo 1160639 61245983 := bstep (se 1 (by rfl) ⟨45934487, by rfl⟩ : syracuseStep 61245983 = 91868975) B91868975
theorem B9931409 : Blo 1160639 9931409 := bstep (se 2 (by rfl) ⟨3724278, by rfl⟩ : syracuseStep 9931409 = 7448557) B7448557
theorem B6622397 : Blo 1160639 6622397 := bstep (se 3 (by rfl) ⟨1241699, by rfl⟩ : syracuseStep 6622397 = 2483399) B2483399
theorem B3312839 : Blo 1160639 3312839 := bstep (se 1 (by rfl) ⟨2484629, by rfl⟩ : syracuseStep 3312839 = 4969259) B4969259
theorem B9932057 : Blo 1160639 9932057 := bstep (se 2 (by rfl) ⟨3724521, by rfl⟩ : syracuseStep 9932057 = 7449043) B7449043
theorem B14126653 : Blo 1160639 14126653 := bstep (se 3 (by rfl) ⟨2648747, by rfl⟩ : syracuseStep 14126653 = 5297495) B5297495
theorem B6295103 : Blo 1160639 6295103 := bstep (se 1 (by rfl) ⟨4721327, by rfl⟩ : syracuseStep 6295103 = 9442655) B9442655
theorem B25464403 : Blo 1160639 25464403 := bstep (se 1 (by rfl) ⟨19098302, by rfl⟩ : syracuseStep 25464403 = 38196605) B38196605
theorem B1741019 : Blo 1160639 1741019 := bstep (se 1 (by rfl) ⟨1305764, by rfl⟩ : syracuseStep 1741019 = 2611529) B2611529
theorem B1741031 : Blo 1160639 1741031 := bstep (se 1 (by rfl) ⟨1305773, by rfl⟩ : syracuseStep 1741031 = 2611547) B2611547
theorem B1741193 : Blo 1160639 1741193 := bstep (se 2 (by rfl) ⟨652947, by rfl⟩ : syracuseStep 1741193 = 1305895) B1305895
theorem B1741289 : Blo 1160639 1741289 := bstep (se 2 (by rfl) ⟨652983, by rfl⟩ : syracuseStep 1741289 = 1305967) B1305967
theorem B7082497 : Blo 1160639 7082497 := bstep (se 2 (by rfl) ⟨2655936, by rfl⟩ : syracuseStep 7082497 = 5311873) B5311873
theorem B1741415 : Blo 1160639 1741415 := bstep (se 1 (by rfl) ⟨1306061, by rfl⟩ : syracuseStep 1741415 = 2612123) B2612123
theorem B22352507 : Blo 1160639 22352507 := bstep (se 1 (by rfl) ⟨16764380, by rfl⟩ : syracuseStep 22352507 = 33528761) B33528761
theorem B1741547 : Blo 1160639 1741547 := bstep (se 1 (by rfl) ⟨1306160, by rfl⟩ : syracuseStep 1741547 = 2612321) B2612321
theorem B1741577 : Blo 1160639 1741577 := bstep (se 2 (by rfl) ⟨653091, by rfl⟩ : syracuseStep 1741577 = 1306183) B1306183
theorem B1741679 : Blo 1160639 1741679 := bstep (se 1 (by rfl) ⟨1306259, by rfl⟩ : syracuseStep 1741679 = 2612519) B2612519
theorem B42374117 : Blo 1160639 42374117 := bstep (se 4 (by rfl) ⟨3972573, by rfl⟩ : syracuseStep 42374117 = 7945147) B7945147
theorem B1741931 : Blo 1160639 1741931 := bstep (se 1 (by rfl) ⟨1306448, by rfl⟩ : syracuseStep 1741931 = 2612897) B2612897
theorem B1742171 : Blo 1160639 1742171 := bstep (se 1 (by rfl) ⟨1306628, by rfl⟩ : syracuseStep 1742171 = 2613257) B2613257
theorem B1742447 : Blo 1160639 1742447 := bstep (se 1 (by rfl) ⟨1306835, by rfl⟩ : syracuseStep 1742447 = 2613671) B2613671
theorem B1742519 : Blo 1160639 1742519 := bstep (se 1 (by rfl) ⟨1306889, by rfl⟩ : syracuseStep 1742519 = 2613779) B2613779
theorem B1742555 : Blo 1160639 1742555 := bstep (se 1 (by rfl) ⟨1306916, by rfl⟩ : syracuseStep 1742555 = 2613833) B2613833
theorem B1742729 : Blo 1160639 1742729 := bstep (se 2 (by rfl) ⟨653523, by rfl⟩ : syracuseStep 1742729 = 1307047) B1307047
theorem B120657869 : Blo 1160639 120657869 := bstep (se 3 (by rfl) ⟨22623350, by rfl⟩ : syracuseStep 120657869 = 45246701) B45246701
theorem B1742831 : Blo 1160639 1742831 := bstep (se 1 (by rfl) ⟨1307123, by rfl⟩ : syracuseStep 1742831 = 2614247) B2614247
theorem B1743083 : Blo 1160639 1743083 := bstep (se 1 (by rfl) ⟨1307312, by rfl⟩ : syracuseStep 1743083 = 2614625) B2614625
theorem B1743143 : Blo 1160639 1743143 := bstep (se 1 (by rfl) ⟨1307357, by rfl⟩ : syracuseStep 1743143 = 2614715) B2614715
theorem B1743227 : Blo 1160639 1743227 := bstep (se 1 (by rfl) ⟨1307420, by rfl⟩ : syracuseStep 1743227 = 2614841) B2614841
theorem B14883425 : Blo 1160639 14883425 := bstep (se 2 (by rfl) ⟨5581284, by rfl⟩ : syracuseStep 14883425 = 11162569) B11162569
theorem B1743497 : Blo 1160639 1743497 := bstep (se 2 (by rfl) ⟨653811, by rfl⟩ : syracuseStep 1743497 = 1307623) B1307623
theorem B1743671 : Blo 1160639 1743671 := bstep (se 1 (by rfl) ⟨1307753, by rfl⟩ : syracuseStep 1743671 = 2615507) B2615507
theorem B14916433 : Blo 1160639 14916433 := bstep (se 2 (by rfl) ⟨5593662, by rfl⟩ : syracuseStep 14916433 = 11187325) B11187325
theorem B1743707 : Blo 1160639 1743707 := bstep (se 1 (by rfl) ⟨1307780, by rfl⟩ : syracuseStep 1743707 = 2615561) B2615561
theorem B1743851 : Blo 1160639 1743851 := bstep (se 1 (by rfl) ⟨1307888, by rfl⟩ : syracuseStep 1743851 = 2615777) B2615777
theorem B2792519 : Blo 1160639 2792519 := bstep (se 1 (by rfl) ⟨2094389, by rfl⟩ : syracuseStep 2792519 = 4188779) B4188779
theorem B1744055 : Blo 1160639 1744055 := bstep (se 1 (by rfl) ⟨1308041, by rfl⟩ : syracuseStep 1744055 = 2616083) B2616083
theorem B6626519 : Blo 1160639 6626519 := bstep (se 1 (by rfl) ⟨4969889, by rfl⟩ : syracuseStep 6626519 = 9939779) B9939779
theorem B16751873 : Blo 1160639 16751873 := bstep (se 2 (by rfl) ⟨6281952, by rfl⟩ : syracuseStep 16751873 = 12563905) B12563905
theorem B29826305 : Blo 1160639 29826305 := bstep (se 2 (by rfl) ⟨11184864, by rfl⟩ : syracuseStep 29826305 = 22369729) B22369729
theorem B4300199 : Blo 1160639 4300199 := bstep (se 1 (by rfl) ⟨3225149, by rfl⟩ : syracuseStep 4300199 = 6450299) B6450299
theorem B1744295 : Blo 1160639 1744295 := bstep (se 1 (by rfl) ⟨1308221, by rfl⟩ : syracuseStep 1744295 = 2616443) B2616443
theorem B1744379 : Blo 1160639 1744379 := bstep (se 1 (by rfl) ⟨1308284, by rfl⟩ : syracuseStep 1744379 = 2616569) B2616569
theorem B1744475 : Blo 1160639 1744475 := bstep (se 1 (by rfl) ⟨1308356, by rfl⟩ : syracuseStep 1744475 = 2616713) B2616713
theorem B1744559 : Blo 1160639 1744559 := bstep (se 1 (by rfl) ⟨1308419, by rfl⟩ : syracuseStep 1744559 = 2616839) B2616839
theorem B1744679 : Blo 1160639 1744679 := bstep (se 1 (by rfl) ⟨1308509, by rfl⟩ : syracuseStep 1744679 = 2617019) B2617019
theorem B2203463 : Blo 1160639 2203463 := bstep (se 1 (by rfl) ⟨1652597, by rfl⟩ : syracuseStep 2203463 = 3305195) B3305195
theorem B1744763 : Blo 1160639 1744763 := bstep (se 1 (by rfl) ⟨1308572, by rfl⟩ : syracuseStep 1744763 = 2617145) B2617145
theorem B8822843 : Blo 1160639 8822843 := bstep (se 1 (by rfl) ⟨6617132, by rfl⟩ : syracuseStep 8822843 = 13234265) B13234265
theorem B1745183 : Blo 1160639 1745183 := bstep (se 1 (by rfl) ⟨1308887, by rfl⟩ : syracuseStep 1745183 = 2617775) B2617775
theorem B1745207 : Blo 1160639 1745207 := bstep (se 1 (by rfl) ⟨1308905, by rfl⟩ : syracuseStep 1745207 = 2617811) B2617811
theorem B6627703 : Blo 1160639 6627703 := bstep (se 1 (by rfl) ⟨4970777, by rfl⟩ : syracuseStep 6627703 = 9941555) B9941555
theorem B1745279 : Blo 1160639 1745279 := bstep (se 1 (by rfl) ⟨1308959, by rfl⟩ : syracuseStep 1745279 = 2617919) B2617919
theorem B1745351 : Blo 1160639 1745351 := bstep (se 1 (by rfl) ⟨1309013, by rfl⟩ : syracuseStep 1745351 = 2618027) B2618027
theorem B1745705 : Blo 1160639 1745705 := bstep (se 2 (by rfl) ⟨654639, by rfl⟩ : syracuseStep 1745705 = 1309279) B1309279
theorem B1745711 : Blo 1160639 1745711 := bstep (se 1 (by rfl) ⟨1309283, by rfl⟩ : syracuseStep 1745711 = 2618567) B2618567
theorem B3187567 : Blo 1160639 3187567 := bstep (se 1 (by rfl) ⟨2390675, by rfl⟩ : syracuseStep 3187567 = 4781351) B4781351
theorem B1745831 : Blo 1160639 1745831 := bstep (se 1 (by rfl) ⟨1309373, by rfl⟩ : syracuseStep 1745831 = 2618747) B2618747
theorem B11183021 : Blo 1160639 11183021 := bstep (se 3 (by rfl) ⟨2096816, by rfl⟩ : syracuseStep 11183021 = 4193633) B4193633
theorem B1745915 : Blo 1160639 1745915 := bstep (se 1 (by rfl) ⟨1309436, by rfl⟩ : syracuseStep 1745915 = 2618873) B2618873
theorem B1745975 : Blo 1160639 1745975 := bstep (se 1 (by rfl) ⟨1309481, by rfl⟩ : syracuseStep 1745975 = 2618963) B2618963
theorem B1746095 : Blo 1160639 1746095 := bstep (se 1 (by rfl) ⟨1309571, by rfl⟩ : syracuseStep 1746095 = 2619143) B2619143
theorem B7546105 : Blo 1160639 7546105 := bstep (se 2 (by rfl) ⟨2829789, by rfl⟩ : syracuseStep 7546105 = 5659579) B5659579
theorem B1746503 : Blo 1160639 1746503 := bstep (se 1 (by rfl) ⟨1309877, by rfl⟩ : syracuseStep 1746503 = 2619755) B2619755
theorem B1746599 : Blo 1160639 1746599 := bstep (se 1 (by rfl) ⟨1309949, by rfl⟩ : syracuseStep 1746599 = 2619899) B2619899
theorem B2205407 : Blo 1160639 2205407 := bstep (se 1 (by rfl) ⟨1654055, by rfl⟩ : syracuseStep 2205407 = 3308111) B3308111
theorem B1746683 : Blo 1160639 1746683 := bstep (se 1 (by rfl) ⟨1310012, by rfl⟩ : syracuseStep 1746683 = 2620025) B2620025
theorem B1746719 : Blo 1160639 1746719 := bstep (se 1 (by rfl) ⟨1310039, by rfl⟩ : syracuseStep 1746719 = 2620079) B2620079
theorem B1746767 : Blo 1160639 1746767 := bstep (se 1 (by rfl) ⟨1310075, by rfl⟩ : syracuseStep 1746767 = 2620151) B2620151
theorem B1746887 : Blo 1160639 1746887 := bstep (se 1 (by rfl) ⟨1310165, by rfl⟩ : syracuseStep 1746887 = 2620331) B2620331
theorem B5876063 : Blo 1160639 5876063 := bstep (se 1 (by rfl) ⟨4407047, by rfl⟩ : syracuseStep 5876063 = 8814095) B8814095
theorem B5876225 : Blo 1160639 5876225 := bstep (se 2 (by rfl) ⟨2203584, by rfl⟩ : syracuseStep 5876225 = 4407169) B4407169
theorem B14133761 : Blo 1160639 14133761 := bstep (se 2 (by rfl) ⟨5300160, by rfl⟩ : syracuseStep 14133761 = 10600321) B10600321
theorem B5877035 : Blo 1160639 5877035 := bstep (se 1 (by rfl) ⟨4407776, by rfl⟩ : syracuseStep 5877035 = 8815553) B8815553
theorem B16788779 : Blo 1160639 16788779 := bstep (se 1 (by rfl) ⟨12591584, by rfl⟩ : syracuseStep 16788779 = 25183169) B25183169
theorem B1912175 : Blo 1160639 1912175 := bstep (se 1 (by rfl) ⟨1434131, by rfl⟩ : syracuseStep 1912175 = 2868263) B2868263
theorem B25177715 : Blo 1160639 25177715 := bstep (se 1 (by rfl) ⟨18883286, by rfl⟩ : syracuseStep 25177715 = 37766573) B37766573
theorem B11186095 : Blo 1160639 11186095 := bstep (se 1 (by rfl) ⟨8389571, by rfl⟩ : syracuseStep 11186095 = 16779143) B16779143
theorem B7451351 : Blo 1160639 7451351 := bstep (se 1 (by rfl) ⟨5588513, by rfl⟩ : syracuseStep 7451351 = 11177027) B11177027
theorem B5878493 : Blo 1160639 5878493 := bstep (se 3 (by rfl) ⟨1102217, by rfl⟩ : syracuseStep 5878493 = 2204435) B2204435
theorem B4961195 : Blo 1160639 4961195 := bstep (se 1 (by rfl) ⟨3720896, by rfl⟩ : syracuseStep 4961195 = 7441793) B7441793
theorem B42480683 : Blo 1160639 42480683 := bstep (se 1 (by rfl) ⟨31860512, by rfl⟩ : syracuseStep 42480683 = 63721025) B63721025
theorem B13251761 : Blo 1160639 13251761 := bstep (se 2 (by rfl) ⟨4969410, by rfl⟩ : syracuseStep 13251761 = 9938821) B9938821
theorem B1160815 : Blo 1160639 1160815 := bstep (se 1 (by rfl) ⟨870611, by rfl⟩ : syracuseStep 1160815 = 1741223) B1741223
theorem B1160871 : Blo 1160639 1160871 := bstep (se 1 (by rfl) ⟨870653, by rfl⟩ : syracuseStep 1160871 = 1741307) B1741307
theorem B2209531 : Blo 1160639 2209531 := bstep (se 1 (by rfl) ⟨1657148, by rfl⟩ : syracuseStep 2209531 = 3314297) B3314297
theorem B1160955 : Blo 1160639 1160955 := bstep (se 1 (by rfl) ⟨870716, by rfl⟩ : syracuseStep 1160955 = 1741433) B1741433
theorem B1160991 : Blo 1160639 1160991 := bstep (se 1 (by rfl) ⟨870743, by rfl⟩ : syracuseStep 1160991 = 1741487) B1741487
theorem B1161023 : Blo 1160639 1161023 := bstep (se 1 (by rfl) ⟨870767, by rfl⟩ : syracuseStep 1161023 = 1741535) B1741535
theorem B3979145 : Blo 1160639 3979145 := bstep (se 2 (by rfl) ⟨1492179, by rfl⟩ : syracuseStep 3979145 = 2984359) B2984359
theorem B1161199 : Blo 1160639 1161199 := bstep (se 1 (by rfl) ⟨870899, by rfl⟩ : syracuseStep 1161199 = 1741799) B1741799
theorem B5879951 : Blo 1160639 5879951 := bstep (se 1 (by rfl) ⟨4409963, by rfl⟩ : syracuseStep 5879951 = 8819927) B8819927
theorem B1161371 : Blo 1160639 1161371 := bstep (se 1 (by rfl) ⟨871028, by rfl⟩ : syracuseStep 1161371 = 1742057) B1742057
theorem B1161407 : Blo 1160639 1161407 := bstep (se 1 (by rfl) ⟨871055, by rfl⟩ : syracuseStep 1161407 = 1742111) B1742111
theorem B1161519 : Blo 1160639 1161519 := bstep (se 1 (by rfl) ⟨871139, by rfl⟩ : syracuseStep 1161519 = 1742279) B1742279
theorem B1325359 : Blo 1160639 1325359 := bstep (se 1 (by rfl) ⟨994019, by rfl⟩ : syracuseStep 1325359 = 1988039) B1988039
theorem B3357035 : Blo 1160639 3357035 := bstep (se 1 (by rfl) ⟨2517776, by rfl⟩ : syracuseStep 3357035 = 5035553) B5035553
theorem B9943469 : Blo 1160639 9943469 := bstep (se 3 (by rfl) ⟨1864400, by rfl⟩ : syracuseStep 9943469 = 3728801) B3728801
theorem B1161755 : Blo 1160639 1161755 := bstep (se 1 (by rfl) ⟨871316, by rfl⟩ : syracuseStep 1161755 = 1742633) B1742633
theorem B1161759 : Blo 1160639 1161759 := bstep (se 1 (by rfl) ⟨871319, by rfl⟩ : syracuseStep 1161759 = 1742639) B1742639
theorem B1162075 : Blo 1160639 1162075 := bstep (se 1 (by rfl) ⟨871556, by rfl⟩ : syracuseStep 1162075 = 1743113) B1743113
theorem B1162143 : Blo 1160639 1162143 := bstep (se 1 (by rfl) ⟨871607, by rfl⟩ : syracuseStep 1162143 = 1743215) B1743215
theorem B1162287 : Blo 1160639 1162287 := bstep (se 1 (by rfl) ⟨871715, by rfl⟩ : syracuseStep 1162287 = 1743431) B1743431
theorem B1162311 : Blo 1160639 1162311 := bstep (se 1 (by rfl) ⟨871733, by rfl⟩ : syracuseStep 1162311 = 1743467) B1743467
theorem B1162463 : Blo 1160639 1162463 := bstep (se 1 (by rfl) ⟨871847, by rfl⟩ : syracuseStep 1162463 = 1743695) B1743695
theorem B1162727 : Blo 1160639 1162727 := bstep (se 1 (by rfl) ⟨872045, by rfl⟩ : syracuseStep 1162727 = 1744091) B1744091
theorem B1162843 : Blo 1160639 1162843 := bstep (se 1 (by rfl) ⟨872132, by rfl⟩ : syracuseStep 1162843 = 1744265) B1744265
theorem B1163079 : Blo 1160639 1163079 := bstep (se 1 (by rfl) ⟨872309, by rfl⟩ : syracuseStep 1163079 = 1744619) B1744619
theorem B1163231 : Blo 1160639 1163231 := bstep (se 1 (by rfl) ⟨872423, by rfl⟩ : syracuseStep 1163231 = 1744847) B1744847
theorem B1163495 : Blo 1160639 1163495 := bstep (se 1 (by rfl) ⟨872621, by rfl⟩ : syracuseStep 1163495 = 1745243) B1745243
theorem B1163647 : Blo 1160639 1163647 := bstep (se 1 (by rfl) ⟨872735, by rfl⟩ : syracuseStep 1163647 = 1745471) B1745471
theorem B1163727 : Blo 1160639 1163727 := bstep (se 1 (by rfl) ⟨872795, by rfl⟩ : syracuseStep 1163727 = 1745591) B1745591
theorem B1163879 : Blo 1160639 1163879 := bstep (se 1 (by rfl) ⟨872909, by rfl⟩ : syracuseStep 1163879 = 1745819) B1745819
theorem B5882543 : Blo 1160639 5882543 := bstep (se 1 (by rfl) ⟨4411907, by rfl⟩ : syracuseStep 5882543 = 8823815) B8823815
theorem B1164143 : Blo 1160639 1164143 := bstep (se 1 (by rfl) ⟨873107, by rfl⟩ : syracuseStep 1164143 = 1746215) B1746215
theorem B1164199 : Blo 1160639 1164199 := bstep (se 1 (by rfl) ⟨873149, by rfl⟩ : syracuseStep 1164199 = 1746299) B1746299
theorem B1164283 : Blo 1160639 1164283 := bstep (se 1 (by rfl) ⟨873212, by rfl⟩ : syracuseStep 1164283 = 1746425) B1746425
theorem B1164351 : Blo 1160639 1164351 := bstep (se 1 (by rfl) ⟨873263, by rfl⟩ : syracuseStep 1164351 = 1746527) B1746527
theorem B3982459 : Blo 1160639 3982459 := bstep (se 1 (by rfl) ⟨2986844, by rfl⟩ : syracuseStep 3982459 = 5973689) B5973689
theorem B1164495 : Blo 1160639 1164495 := bstep (se 1 (by rfl) ⟨873371, by rfl⟩ : syracuseStep 1164495 = 1746743) B1746743
theorem B1656391 : Blo 1160639 1656391 := bstep (se 1 (by rfl) ⟨1242293, by rfl⟩ : syracuseStep 1656391 = 2484587) B2484587
theorem B1656607 : Blo 1160639 1656607 := bstep (se 1 (by rfl) ⟨1242455, by rfl⟩ : syracuseStep 1656607 = 2484911) B2484911
theorem B1394879 : Blo 1160639 1394879 := bstep (se 1 (by rfl) ⟨1046159, by rfl⟩ : syracuseStep 1394879 = 2092319) B2092319
theorem B4966609 : Blo 1160639 4966609 := bstep (se 2 (by rfl) ⟨1862478, by rfl⟩ : syracuseStep 4966609 = 3724957) B3724957
theorem B5655527 : Blo 1160639 5655527 := bstep (se 1 (by rfl) ⟨4241645, by rfl⟩ : syracuseStep 5655527 = 8483291) B8483291
theorem B7458115 : Blo 1160639 7458115 := bstep (se 1 (by rfl) ⟨5593586, by rfl⟩ : syracuseStep 7458115 = 11187173) B11187173
theorem B4410875 : Blo 1160639 4410875 := bstep (se 1 (by rfl) ⟨3308156, by rfl⟩ : syracuseStep 4410875 = 6616313) B6616313
theorem B12242447 : Blo 1160639 12242447 := bstep (se 1 (by rfl) ⟨9181835, by rfl⟩ : syracuseStep 12242447 = 18363671) B18363671
theorem B15093307 : Blo 1160639 15093307 := bstep (se 1 (by rfl) ⟨11319980, by rfl⟩ : syracuseStep 15093307 = 22639961) B22639961
theorem B11161151 : Blo 1160639 11161151 := bstep (se 1 (by rfl) ⟨8370863, by rfl⟩ : syracuseStep 11161151 = 16741727) B16741727
theorem B4247113 : Blo 1160639 4247113 := bstep (se 2 (by rfl) ⟨1592667, by rfl⟩ : syracuseStep 4247113 = 3185335) B3185335
theorem B3919535 : Blo 1160639 3919535 := bstep (se 1 (by rfl) ⟨2939651, by rfl⟩ : syracuseStep 3919535 = 5879303) B5879303
theorem B3919859 : Blo 1160639 3919859 := bstep (se 1 (by rfl) ⟨2939894, by rfl⟩ : syracuseStep 3919859 = 5879789) B5879789
theorem B29839427 : Blo 1160639 29839427 := bstep (se 1 (by rfl) ⟨22379570, by rfl⟩ : syracuseStep 29839427 = 44759141) B44759141
theorem B7459037 : Blo 1160639 7459037 := bstep (se 3 (by rfl) ⟨1398569, by rfl⟩ : syracuseStep 7459037 = 2797139) B2797139
theorem B3920183 : Blo 1160639 3920183 := bstep (se 1 (by rfl) ⟨2940137, by rfl⟩ : syracuseStep 3920183 = 5880275) B5880275
theorem B3920399 : Blo 1160639 3920399 := bstep (se 1 (by rfl) ⟨2940299, by rfl⟩ : syracuseStep 3920399 = 5880599) B5880599
theorem B14340797 : Blo 1160639 14340797 := bstep (se 3 (by rfl) ⟨2688899, by rfl⟩ : syracuseStep 14340797 = 5377799) B5377799
theorem B9917225 : Blo 1160639 9917225 := bstep (se 2 (by rfl) ⟨3718959, by rfl⟩ : syracuseStep 9917225 = 7437919) B7437919
theorem B3724343 : Blo 1160639 3724343 := bstep (se 1 (by rfl) ⟨2793257, by rfl⟩ : syracuseStep 3724343 = 5586515) B5586515
theorem B3921479 : Blo 1160639 3921479 := bstep (se 1 (by rfl) ⟨2941109, by rfl⟩ : syracuseStep 3921479 = 5882219) B5882219
theorem B16766635 : Blo 1160639 16766635 := bstep (se 1 (by rfl) ⟨12574976, by rfl⟩ : syracuseStep 16766635 = 25149953) B25149953
theorem B7460525 : Blo 1160639 7460525 := bstep (se 3 (by rfl) ⟨1398848, by rfl⟩ : syracuseStep 7460525 = 2797697) B2797697
theorem B2938619 : Blo 1160639 2938619 := bstep (se 1 (by rfl) ⟨2203964, by rfl⟩ : syracuseStep 2938619 = 4407929) B4407929
theorem B14899211 : Blo 1160639 14899211 := bstep (se 1 (by rfl) ⟨11174408, by rfl⟩ : syracuseStep 14899211 = 22348817) B22348817
theorem B2938963 : Blo 1160639 2938963 := bstep (se 1 (by rfl) ⟨2204222, by rfl⟩ : syracuseStep 2938963 = 4408445) B4408445
theorem B8378731 : Blo 1160639 8378731 := bstep (se 1 (by rfl) ⟨6284048, by rfl⟩ : syracuseStep 8378731 = 12568097) B12568097
theorem B3922451 : Blo 1160639 3922451 := bstep (se 1 (by rfl) ⟨2941838, by rfl⟩ : syracuseStep 3922451 = 5883677) B5883677
theorem B2939449 : Blo 1160639 2939449 := bstep (se 2 (by rfl) ⟨1102293, by rfl⟩ : syracuseStep 2939449 = 2204587) B2204587
theorem B7461497 : Blo 1160639 7461497 := bstep (se 2 (by rfl) ⟨2798061, by rfl⟩ : syracuseStep 7461497 = 5596123) B5596123
theorem B30595915 : Blo 1160639 30595915 := bstep (se 1 (by rfl) ⟨22946936, by rfl⟩ : syracuseStep 30595915 = 45893873) B45893873
theorem B2612051 : Blo 1160639 2612051 := bstep (se 1 (by rfl) ⟨1959038, by rfl⟩ : syracuseStep 2612051 = 3918077) B3918077
theorem B2939753 : Blo 1160639 2939753 := bstep (se 2 (by rfl) ⟨1102407, by rfl⟩ : syracuseStep 2939753 = 2204815) B2204815
theorem B4414445 : Blo 1160639 4414445 := bstep (se 3 (by rfl) ⟨827708, by rfl⟩ : syracuseStep 4414445 = 1655417) B1655417
theorem B206461973 : Blo 1160639 206461973 := bstep (se 6 (by rfl) ⟨4838952, by rfl⟩ : syracuseStep 206461973 = 9677905) B9677905
theorem B24534161 : Blo 1160639 24534161 := bstep (se 2 (by rfl) ⟨9200310, by rfl⟩ : syracuseStep 24534161 = 18400621) B18400621
theorem B4971871 : Blo 1160639 4971871 := bstep (se 1 (by rfl) ⟨3728903, by rfl⟩ : syracuseStep 4971871 = 7457807) B7457807
theorem B2612591 : Blo 1160639 2612591 := bstep (se 1 (by rfl) ⟨1959443, by rfl⟩ : syracuseStep 2612591 = 3918887) B3918887
theorem B10739105 : Blo 1160639 10739105 := bstep (se 2 (by rfl) ⟨4027164, by rfl⟩ : syracuseStep 10739105 = 8054329) B8054329
theorem B2940371 : Blo 1160639 2940371 := bstep (se 1 (by rfl) ⟨2205278, by rfl⟩ : syracuseStep 2940371 = 4410557) B4410557
theorem B3726803 : Blo 1160639 3726803 := bstep (se 1 (by rfl) ⟨2795102, by rfl⟩ : syracuseStep 3726803 = 5590205) B5590205
theorem B2612879 : Blo 1160639 2612879 := bstep (se 1 (by rfl) ⟨1959659, by rfl⟩ : syracuseStep 2612879 = 3919319) B3919319
theorem B2612969 : Blo 1160639 2612969 := bstep (se 2 (by rfl) ⟨979863, by rfl⟩ : syracuseStep 2612969 = 1959727) B1959727
theorem B4415219 : Blo 1160639 4415219 := bstep (se 1 (by rfl) ⟨3311414, by rfl⟩ : syracuseStep 4415219 = 6622829) B6622829
theorem B34004843 : Blo 1160639 34004843 := bstep (se 1 (by rfl) ⟨25503632, by rfl⟩ : syracuseStep 34004843 = 51007265) B51007265
theorem B529915877 : Blo 1160639 529915877 := bstep (se 4 (by rfl) ⟨49679613, by rfl⟩ : syracuseStep 529915877 = 99359227) B99359227
theorem B4710737 : Blo 1160639 4710737 := bstep (se 2 (by rfl) ⟨1766526, by rfl⟩ : syracuseStep 4710737 = 3533053) B3533053
theorem B1860089 : Blo 1160639 1860089 := bstep (se 2 (by rfl) ⟨697533, by rfl⟩ : syracuseStep 1860089 = 1395067) B1395067
theorem B28271213 : Blo 1160639 28271213 := bstep (se 3 (by rfl) ⟨5300852, by rfl⟩ : syracuseStep 28271213 = 10601705) B10601705
theorem B2613995 : Blo 1160639 2613995 := bstep (se 1 (by rfl) ⟨1960496, by rfl⟩ : syracuseStep 2613995 = 3920993) B3920993
theorem B1991591 : Blo 1160639 1991591 := bstep (se 1 (by rfl) ⟨1493693, by rfl⟩ : syracuseStep 1991591 = 2987387) B2987387
theorem B3728443 : Blo 1160639 3728443 := bstep (se 1 (by rfl) ⟨2796332, by rfl⟩ : syracuseStep 3728443 = 5592665) B5592665
theorem B3925097 : Blo 1160639 3925097 := bstep (se 2 (by rfl) ⟨1471911, by rfl⟩ : syracuseStep 3925097 = 2943823) B2943823
theorem B2483407 : Blo 1160639 2483407 := bstep (se 1 (by rfl) ⟨1862555, by rfl⟩ : syracuseStep 2483407 = 3725111) B3725111
theorem B2942315 : Blo 1160639 2942315 := bstep (se 1 (by rfl) ⟨2206736, by rfl⟩ : syracuseStep 2942315 = 4413473) B4413473
theorem B4416875 : Blo 1160639 4416875 := bstep (se 1 (by rfl) ⟨3312656, by rfl⟩ : syracuseStep 4416875 = 6625313) B6625313
theorem B7071113 : Blo 1160639 7071113 := bstep (se 2 (by rfl) ⟨2651667, by rfl⟩ : syracuseStep 7071113 = 5303335) B5303335
theorem B2614895 : Blo 1160639 2614895 := bstep (se 1 (by rfl) ⟨1961171, by rfl⟩ : syracuseStep 2614895 = 3922343) B3922343
theorem B1959545 : Blo 1160639 1959545 := bstep (se 2 (by rfl) ⟨734829, by rfl⟩ : syracuseStep 1959545 = 1469659) B1469659
theorem B8840825 : Blo 1160639 8840825 := bstep (se 2 (by rfl) ⟨3315309, by rfl⟩ : syracuseStep 8840825 = 6630619) B6630619
theorem B4187809 : Blo 1160639 4187809 := bstep (se 2 (by rfl) ⟨1570428, by rfl⟩ : syracuseStep 4187809 = 3140857) B3140857
theorem B2615003 : Blo 1160639 2615003 := bstep (se 1 (by rfl) ⟨1961252, by rfl⟩ : syracuseStep 2615003 = 3922505) B3922505
theorem B4187983 : Blo 1160639 4187983 := bstep (se 1 (by rfl) ⟨3140987, by rfl⟩ : syracuseStep 4187983 = 6281975) B6281975
theorem B3925961 : Blo 1160639 3925961 := bstep (se 2 (by rfl) ⟨1472235, by rfl⟩ : syracuseStep 3925961 = 2944471) B2944471
theorem B1960031 : Blo 1160639 1960031 := bstep (se 1 (by rfl) ⟨1470023, by rfl⟩ : syracuseStep 1960031 = 2940047) B2940047
theorem B1861787 : Blo 1160639 1861787 := bstep (se 1 (by rfl) ⟨1396340, by rfl⟩ : syracuseStep 1861787 = 2792681) B2792681
theorem B3926231 : Blo 1160639 3926231 := bstep (se 1 (by rfl) ⟨2944673, by rfl⟩ : syracuseStep 3926231 = 5889347) B5889347
theorem B4712843 : Blo 1160639 4712843 := bstep (se 1 (by rfl) ⟨3534632, by rfl⟩ : syracuseStep 4712843 = 7069265) B7069265
theorem B1468955 : Blo 1160639 1468955 := bstep (se 1 (by rfl) ⟨1101716, by rfl⟩ : syracuseStep 1468955 = 2203433) B2203433
theorem B3926555 : Blo 1160639 3926555 := bstep (se 1 (by rfl) ⟨2944916, by rfl⟩ : syracuseStep 3926555 = 5889833) B5889833
theorem B2616119 : Blo 1160639 2616119 := bstep (se 1 (by rfl) ⟨1962089, by rfl⟩ : syracuseStep 2616119 = 3924179) B3924179
theorem B2616299 : Blo 1160639 2616299 := bstep (se 1 (by rfl) ⟨1962224, by rfl⟩ : syracuseStep 2616299 = 3924449) B3924449
theorem B7072865 : Blo 1160639 7072865 := bstep (se 2 (by rfl) ⟨2652324, by rfl⟩ : syracuseStep 7072865 = 5304649) B5304649
theorem B1305823 : Blo 1160639 1305823 := bstep (se 1 (by rfl) ⟨979367, by rfl⟩ : syracuseStep 1305823 = 1958735) B1958735
theorem B1961327 : Blo 1160639 1961327 := bstep (se 1 (by rfl) ⟨1470995, by rfl⟩ : syracuseStep 1961327 = 2941991) B2941991
theorem B3927419 : Blo 1160639 3927419 := bstep (se 1 (by rfl) ⟨2945564, by rfl⟩ : syracuseStep 3927419 = 5891129) B5891129
theorem B1469927 : Blo 1160639 1469927 := bstep (se 1 (by rfl) ⟨1102445, by rfl⟩ : syracuseStep 1469927 = 2204891) B2204891
theorem B1961563 : Blo 1160639 1961563 := bstep (se 1 (by rfl) ⟨1471172, by rfl⟩ : syracuseStep 1961563 = 2942345) B2942345
theorem B1961705 : Blo 1160639 1961705 := bstep (se 2 (by rfl) ⟨735639, by rfl⟩ : syracuseStep 1961705 = 1471279) B1471279
theorem B2617127 : Blo 1160639 2617127 := bstep (se 1 (by rfl) ⟨1962845, by rfl⟩ : syracuseStep 2617127 = 3925691) B3925691
theorem B2944907 : Blo 1160639 2944907 := bstep (se 1 (by rfl) ⟨2208680, by rfl⟩ : syracuseStep 2944907 = 4417361) B4417361
theorem B8482733 : Blo 1160639 8482733 := bstep (se 3 (by rfl) ⟨1590512, by rfl⟩ : syracuseStep 8482733 = 3181025) B3181025
theorem B3305423 : Blo 1160639 3305423 := bstep (se 1 (by rfl) ⟨2479067, by rfl⟩ : syracuseStep 3305423 = 4958135) B4958135
theorem B14151667 : Blo 1160639 14151667 := bstep (se 1 (by rfl) ⟨10613750, by rfl⟩ : syracuseStep 14151667 = 21227501) B21227501
theorem B2978387 : Blo 1160639 2978387 := bstep (se 1 (by rfl) ⟨2233790, by rfl⟩ : syracuseStep 2978387 = 4467581) B4467581
theorem B1962731 : Blo 1160639 1962731 := bstep (se 1 (by rfl) ⟨1472048, by rfl⟩ : syracuseStep 1962731 = 2944097) B2944097
theorem B3928823 : Blo 1160639 3928823 := bstep (se 1 (by rfl) ⟨2946617, by rfl⟩ : syracuseStep 3928823 = 5893235) B5893235
theorem B2618153 : Blo 1160639 2618153 := bstep (se 2 (by rfl) ⟨981807, by rfl⟩ : syracuseStep 2618153 = 1963615) B1963615
theorem B6616039 : Blo 1160639 6616039 := bstep (se 1 (by rfl) ⟨4962029, by rfl⟩ : syracuseStep 6616039 = 9924059) B9924059
theorem B2618423 : Blo 1160639 2618423 := bstep (se 1 (by rfl) ⟨1963817, by rfl⟩ : syracuseStep 2618423 = 3927635) B3927635
theorem B2618441 : Blo 1160639 2618441 := bstep (se 2 (by rfl) ⟨981915, by rfl⟩ : syracuseStep 2618441 = 1963831) B1963831
theorem B1569899 : Blo 1160639 1569899 := bstep (se 1 (by rfl) ⟨1177424, by rfl⟩ : syracuseStep 1569899 = 2354849) B2354849
theorem B1864811 : Blo 1160639 1864811 := bstep (se 1 (by rfl) ⟨1398608, by rfl⟩ : syracuseStep 1864811 = 2797217) B2797217
theorem B22344821 : Blo 1160639 22344821 := bstep (se 5 (by rfl) ⟨1047413, by rfl⟩ : syracuseStep 22344821 = 2094827) B2094827
theorem B1963183 : Blo 1160639 1963183 := bstep (se 1 (by rfl) ⟨1472387, by rfl⟩ : syracuseStep 1963183 = 2944775) B2944775
theorem B3929363 : Blo 1160639 3929363 := bstep (se 1 (by rfl) ⟨2947022, by rfl⟩ : syracuseStep 3929363 = 5894045) B5894045
theorem B2946395 : Blo 1160639 2946395 := bstep (se 1 (by rfl) ⟨2209796, by rfl⟩ : syracuseStep 2946395 = 4419593) B4419593
theorem B30242315 : Blo 1160639 30242315 := bstep (se 1 (by rfl) ⟨22681736, by rfl⟩ : syracuseStep 30242315 = 45363473) B45363473
theorem B1308271 : Blo 1160639 1308271 := bstep (se 1 (by rfl) ⟨981203, by rfl⟩ : syracuseStep 1308271 = 1962407) B1962407
theorem B1963703 : Blo 1160639 1963703 := bstep (se 1 (by rfl) ⟨1472777, by rfl⟩ : syracuseStep 1963703 = 2945555) B2945555
theorem B1308379 : Blo 1160639 1308379 := bstep (se 1 (by rfl) ⟨981284, by rfl⟩ : syracuseStep 1308379 = 1962569) B1962569
theorem B1472251 : Blo 1160639 1472251 := bstep (se 1 (by rfl) ⟨1104188, by rfl⟩ : syracuseStep 1472251 = 2208377) B2208377
theorem B5175035 : Blo 1160639 5175035 := bstep (se 1 (by rfl) ⟨3881276, by rfl⟩ : syracuseStep 5175035 = 7762553) B7762553
theorem B1570591 : Blo 1160639 1570591 := bstep (se 1 (by rfl) ⟨1177943, by rfl⟩ : syracuseStep 1570591 = 2355887) B2355887
theorem B3929903 : Blo 1160639 3929903 := bstep (se 1 (by rfl) ⟨2947427, by rfl⟩ : syracuseStep 3929903 = 5894855) B5894855
theorem B25098133 : Blo 1160639 25098133 := bstep (se 6 (by rfl) ⟨588237, by rfl⟩ : syracuseStep 25098133 = 1176475) B1176475
theorem B2095087 : Blo 1160639 2095087 := bstep (se 1 (by rfl) ⟨1571315, by rfl⟩ : syracuseStep 2095087 = 3142631) B3142631
theorem B4192249 : Blo 1160639 4192249 := bstep (se 2 (by rfl) ⟨1572093, by rfl⟩ : syracuseStep 4192249 = 3144187) B3144187
theorem B68942009 : Blo 1160639 68942009 := bstep (se 2 (by rfl) ⟨25853253, by rfl⟩ : syracuseStep 68942009 = 51706507) B51706507
theorem B1177903 : Blo 1160639 1177903 := bstep (se 1 (by rfl) ⟨883427, by rfl⟩ : syracuseStep 1177903 = 1766855) B1766855
theorem B11172563 : Blo 1160639 11172563 := bstep (se 1 (by rfl) ⟨8379422, by rfl⟩ : syracuseStep 11172563 = 16758845) B16758845
theorem B1309531 : Blo 1160639 1309531 := bstep (se 1 (by rfl) ⟨982148, by rfl⟩ : syracuseStep 1309531 = 1964297) B1964297
theorem B1964891 : Blo 1160639 1964891 := bstep (se 1 (by rfl) ⟨1473668, by rfl⟩ : syracuseStep 1964891 = 2947337) B2947337
theorem B2620367 : Blo 1160639 2620367 := bstep (se 1 (by rfl) ⟨1965275, by rfl⟩ : syracuseStep 2620367 = 3930551) B3930551
theorem B2620385 : Blo 1160639 2620385 := bstep (se 2 (by rfl) ⟨982644, by rfl⟩ : syracuseStep 2620385 = 1965289) B1965289
theorem B1965127 : Blo 1160639 1965127 := bstep (se 1 (by rfl) ⟨1473845, by rfl⟩ : syracuseStep 1965127 = 2947691) B2947691
theorem B1473871 : Blo 1160639 1473871 := bstep (se 1 (by rfl) ⟨1105403, by rfl⟩ : syracuseStep 1473871 = 2210807) B2210807
theorem B1769135 : Blo 1160639 1769135 := bstep (se 1 (by rfl) ⟨1326851, by rfl⟩ : syracuseStep 1769135 = 2653703) B2653703
theorem B37715705 : Blo 1160639 37715705 := bstep (se 2 (by rfl) ⟨14143389, by rfl⟩ : syracuseStep 37715705 = 28286779) B28286779
theorem B2360315 : Blo 1160639 2360315 := bstep (se 1 (by rfl) ⟨1770236, by rfl⟩ : syracuseStep 2360315 = 3540473) B3540473
theorem B2360495 : Blo 1160639 2360495 := bstep (se 1 (by rfl) ⟨1770371, by rfl⟩ : syracuseStep 2360495 = 3540743) B3540743
theorem B5965103 : Blo 1160639 5965103 := bstep (se 1 (by rfl) ⟨4473827, by rfl⟩ : syracuseStep 5965103 = 8947655) B8947655
theorem B5309945 : Blo 1160639 5309945 := bstep (se 2 (by rfl) ⟨1991229, by rfl⟩ : syracuseStep 5309945 = 3982459) B3982459
theorem B3311209 : Blo 1160639 3311209 := bstep (se 2 (by rfl) ⟨1241703, by rfl⟩ : syracuseStep 3311209 = 2483407) B2483407
theorem B40830655 : Blo 1160639 40830655 := bstep (se 1 (by rfl) ⟨30622991, by rfl⟩ : syracuseStep 40830655 = 61245983) B61245983
theorem B6620939 : Blo 1160639 6620939 := bstep (se 1 (by rfl) ⟨4965704, by rfl⟩ : syracuseStep 6620939 = 9931409) B9931409
theorem B13240097 : Blo 1160639 13240097 := bstep (se 2 (by rfl) ⟨4965036, by rfl⟩ : syracuseStep 13240097 = 9930073) B9930073
theorem B3770351 : Blo 1160639 3770351 := bstep (se 1 (by rfl) ⟨2827763, by rfl⟩ : syracuseStep 3770351 = 5655527) B5655527
theorem B6621371 : Blo 1160639 6621371 := bstep (se 1 (by rfl) ⟨4966028, by rfl⟩ : syracuseStep 6621371 = 9932057) B9932057
theorem B8161631 : Blo 1160639 8161631 := bstep (se 1 (by rfl) ⟨6121223, by rfl⟩ : syracuseStep 8161631 = 12242447) B12242447
theorem B7440767 : Blo 1160639 7440767 := bstep (se 1 (by rfl) ⟨5580575, by rfl⟩ : syracuseStep 7440767 = 11161151) B11161151
theorem B4196735 : Blo 1160639 4196735 := bstep (se 1 (by rfl) ⟨3147551, by rfl⟩ : syracuseStep 4196735 = 6295103) B6295103
theorem B19892951 : Blo 1160639 19892951 := bstep (se 1 (by rfl) ⟨14919713, by rfl⟩ : syracuseStep 19892951 = 29839427) B29839427
theorem B6622145 : Blo 1160639 6622145 := bstep (se 2 (by rfl) ⟨2483304, by rfl⟩ : syracuseStep 6622145 = 4966609) B4966609
theorem B28249411 : Blo 1160639 28249411 := bstep (se 1 (by rfl) ⟨21187058, by rfl⟩ : syracuseStep 28249411 = 42374117) B42374117
theorem B9932807 : Blo 1160639 9932807 := bstep (se 1 (by rfl) ⟨7449605, by rfl⟩ : syracuseStep 9932807 = 14899211) B14899211
theorem B1741097 : Blo 1160639 1741097 := bstep (se 2 (by rfl) ⟨652911, by rfl⟩ : syracuseStep 1741097 = 1305823) B1305823
theorem B1741367 : Blo 1160639 1741367 := bstep (se 1 (by rfl) ⟨1306025, by rfl⟩ : syracuseStep 1741367 = 2612051) B2612051
theorem B20124409 : Blo 1160639 20124409 := bstep (se 2 (by rfl) ⟨7546653, by rfl⟩ : syracuseStep 20124409 = 15093307) B15093307
theorem B16356107 : Blo 1160639 16356107 := bstep (se 1 (by rfl) ⟨12267080, by rfl⟩ : syracuseStep 16356107 = 24534161) B24534161
theorem B33952537 : Blo 1160639 33952537 := bstep (se 2 (by rfl) ⟨12732201, by rfl⟩ : syracuseStep 33952537 = 25464403) B25464403
theorem B1741727 : Blo 1160639 1741727 := bstep (se 1 (by rfl) ⟨1306295, by rfl⟩ : syracuseStep 1741727 = 2612591) B2612591
theorem B1741919 : Blo 1160639 1741919 := bstep (se 1 (by rfl) ⟨1306439, by rfl⟩ : syracuseStep 1741919 = 2612879) B2612879
theorem B1741979 : Blo 1160639 1741979 := bstep (se 1 (by rfl) ⟨1306484, by rfl⟩ : syracuseStep 1741979 = 2612969) B2612969
theorem B14914793 : Blo 1160639 14914793 := bstep (se 2 (by rfl) ⟨5593047, by rfl⟩ : syracuseStep 14914793 = 11186095) B11186095
theorem B353277251 : Blo 1160639 353277251 := bstep (se 1 (by rfl) ⟨264957938, by rfl⟩ : syracuseStep 353277251 = 529915877) B529915877
theorem B18847475 : Blo 1160639 18847475 := bstep (se 1 (by rfl) ⟨14135606, by rfl⟩ : syracuseStep 18847475 = 28271213) B28271213
theorem B1742663 : Blo 1160639 1742663 := bstep (se 1 (by rfl) ⟨1306997, by rfl⟩ : syracuseStep 1742663 = 2613995) B2613995
theorem B1743263 : Blo 1160639 1743263 := bstep (se 1 (by rfl) ⟨1307447, by rfl⟩ : syracuseStep 1743263 = 2614895) B2614895
theorem B1743335 : Blo 1160639 1743335 := bstep (se 1 (by rfl) ⟨1307501, by rfl⟩ : syracuseStep 1743335 = 2615003) B2615003
theorem B40245893 : Blo 1160639 40245893 := bstep (se 4 (by rfl) ⟨3773052, by rfl⟩ : syracuseStep 40245893 = 7546105) B7546105
theorem B8821385 : Blo 1160639 8821385 := bstep (se 2 (by rfl) ⟨3308019, by rfl⟩ : syracuseStep 8821385 = 6616039) B6616039
theorem B19897325 : Blo 1160639 19897325 := bstep (se 3 (by rfl) ⟨3730748, by rfl⟩ : syracuseStep 19897325 = 7461497) B7461497
theorem B1744079 : Blo 1160639 1744079 := bstep (se 1 (by rfl) ⟨1308059, by rfl⟩ : syracuseStep 1744079 = 2616119) B2616119
theorem B1744199 : Blo 1160639 1744199 := bstep (se 1 (by rfl) ⟨1308149, by rfl⟩ : syracuseStep 1744199 = 2616299) B2616299
theorem B1744361 : Blo 1160639 1744361 := bstep (se 2 (by rfl) ⟨654135, by rfl⟩ : syracuseStep 1744361 = 1308271) B1308271
theorem B22355513 : Blo 1160639 22355513 := bstep (se 2 (by rfl) ⟨8383317, by rfl⟩ : syracuseStep 22355513 = 16766635) B16766635
theorem B1744505 : Blo 1160639 1744505 := bstep (se 2 (by rfl) ⟨654189, by rfl⟩ : syracuseStep 1744505 = 1308379) B1308379
theorem B16785143 : Blo 1160639 16785143 := bstep (se 1 (by rfl) ⟨12588857, by rfl⟩ : syracuseStep 16785143 = 25177715) B25177715
theorem B1744751 : Blo 1160639 1744751 := bstep (se 1 (by rfl) ⟨1308563, by rfl⟩ : syracuseStep 1744751 = 2617127) B2617127
theorem B33464177 : Blo 1160639 33464177 := bstep (se 2 (by rfl) ⟨12549066, by rfl⟩ : syracuseStep 33464177 = 25098133) B25098133
theorem B2203615 : Blo 1160639 2203615 := bstep (se 1 (by rfl) ⟨1652711, by rfl⟩ : syracuseStep 2203615 = 3305423) B3305423
theorem B2793449 : Blo 1160639 2793449 := bstep (se 2 (by rfl) ⟨1047543, by rfl⟩ : syracuseStep 2793449 = 2095087) B2095087
theorem B75342149 : Blo 1160639 75342149 := bstep (se 4 (by rfl) ⟨7063326, by rfl⟩ : syracuseStep 75342149 = 14126653) B14126653
theorem B1745435 : Blo 1160639 1745435 := bstep (se 1 (by rfl) ⟨1309076, by rfl⟩ : syracuseStep 1745435 = 2618153) B2618153
theorem B28320455 : Blo 1160639 28320455 := bstep (se 1 (by rfl) ⟨21240341, by rfl⟩ : syracuseStep 28320455 = 42480683) B42480683
theorem B1745615 : Blo 1160639 1745615 := bstep (se 1 (by rfl) ⟨1309211, by rfl⟩ : syracuseStep 1745615 = 2618423) B2618423
theorem B1745627 : Blo 1160639 1745627 := bstep (se 1 (by rfl) ⟨1309220, by rfl⟩ : syracuseStep 1745627 = 2618441) B2618441
theorem B20161543 : Blo 1160639 20161543 := bstep (se 1 (by rfl) ⟨15121157, by rfl⟩ : syracuseStep 20161543 = 30242315) B30242315
theorem B1746041 : Blo 1160639 1746041 := bstep (se 2 (by rfl) ⟨654765, by rfl⟩ : syracuseStep 1746041 = 1309531) B1309531
theorem B3450023 : Blo 1160639 3450023 := bstep (se 1 (by rfl) ⟨2587517, by rfl⟩ : syracuseStep 3450023 = 5175035) B5175035
theorem B2238023 : Blo 1160639 2238023 := bstep (se 1 (by rfl) ⟨1678517, by rfl⟩ : syracuseStep 2238023 = 3357035) B3357035
theorem B6628979 : Blo 1160639 6628979 := bstep (se 1 (by rfl) ⟨4971734, by rfl⟩ : syracuseStep 6628979 = 9943469) B9943469
theorem B6629161 : Blo 1160639 6629161 := bstep (se 2 (by rfl) ⟨2485935, by rfl⟩ : syracuseStep 6629161 = 4971871) B4971871
theorem B7448375 : Blo 1160639 7448375 := bstep (se 1 (by rfl) ⟨5586281, by rfl⟩ : syracuseStep 7448375 = 11172563) B11172563
theorem B1746911 : Blo 1160639 1746911 := bstep (se 1 (by rfl) ⟨1310183, by rfl⟩ : syracuseStep 1746911 = 2620367) B2620367
theorem B1746923 : Blo 1160639 1746923 := bstep (se 1 (by rfl) ⟨1310192, by rfl⟩ : syracuseStep 1746923 = 2620385) B2620385
theorem B5875901 : Blo 1160639 5875901 := bstep (se 3 (by rfl) ⟨1101731, by rfl⟩ : syracuseStep 5875901 = 2203463) B2203463
theorem B25143803 : Blo 1160639 25143803 := bstep (se 1 (by rfl) ⟨18857852, by rfl⟩ : syracuseStep 25143803 = 37715705) B37715705
theorem B5876711 : Blo 1160639 5876711 := bstep (se 1 (by rfl) ⟨4407533, by rfl⟩ : syracuseStep 5876711 = 8815067) B8815067
theorem B4960237 : Blo 1160639 4960237 := bstep (se 3 (by rfl) ⟨930044, by rfl⟩ : syracuseStep 4960237 = 1860089) B1860089
theorem B11186369 : Blo 1160639 11186369 := bstep (se 2 (by rfl) ⟨4194888, by rfl⟩ : syracuseStep 11186369 = 8389777) B8389777
theorem B2797831 : Blo 1160639 2797831 := bstep (se 1 (by rfl) ⟨2098373, by rfl⟩ : syracuseStep 2797831 = 4196747) B4196747
theorem B2208521 : Blo 1160639 2208521 := bstep (se 2 (by rfl) ⟨828195, by rfl⟩ : syracuseStep 2208521 = 1656391) B1656391
theorem B2208559 : Blo 1160639 2208559 := bstep (se 1 (by rfl) ⟨1656419, by rfl⟩ : syracuseStep 2208559 = 3312839) B3312839
theorem B5583745 : Blo 1160639 5583745 := bstep (se 2 (by rfl) ⟨2093904, by rfl⟩ : syracuseStep 5583745 = 4187809) B4187809
theorem B2208809 : Blo 1160639 2208809 := bstep (se 2 (by rfl) ⟨828303, by rfl⟩ : syracuseStep 2208809 = 1656607) B1656607
theorem B5583977 : Blo 1160639 5583977 := bstep (se 2 (by rfl) ⟨2093991, by rfl⟩ : syracuseStep 5583977 = 4187983) B4187983
theorem B1160679 : Blo 1160639 1160679 := bstep (se 1 (by rfl) ⟨870509, by rfl⟩ : syracuseStep 1160679 = 1741019) B1741019
theorem B1160687 : Blo 1160639 1160687 := bstep (se 1 (by rfl) ⟨870515, by rfl⟩ : syracuseStep 1160687 = 1741031) B1741031
theorem B1160795 : Blo 1160639 1160795 := bstep (se 1 (by rfl) ⟨870596, by rfl⟩ : syracuseStep 1160795 = 1741193) B1741193
theorem B1160859 : Blo 1160639 1160859 := bstep (se 1 (by rfl) ⟨870644, by rfl⟩ : syracuseStep 1160859 = 1741289) B1741289
theorem B1160943 : Blo 1160639 1160943 := bstep (se 1 (by rfl) ⟨870707, by rfl⟩ : syracuseStep 1160943 = 1741415) B1741415
theorem B1161031 : Blo 1160639 1161031 := bstep (se 1 (by rfl) ⟨870773, by rfl⟩ : syracuseStep 1161031 = 1741547) B1741547
theorem B1161051 : Blo 1160639 1161051 := bstep (se 1 (by rfl) ⟨870788, by rfl⟩ : syracuseStep 1161051 = 1741577) B1741577
theorem B1161119 : Blo 1160639 1161119 := bstep (se 1 (by rfl) ⟨870839, by rfl⟩ : syracuseStep 1161119 = 1741679) B1741679
theorem B1161287 : Blo 1160639 1161287 := bstep (se 1 (by rfl) ⟨870965, by rfl⟩ : syracuseStep 1161287 = 1741931) B1741931
theorem B1161447 : Blo 1160639 1161447 := bstep (se 1 (by rfl) ⟨871085, by rfl⟩ : syracuseStep 1161447 = 1742171) B1742171
theorem B1161631 : Blo 1160639 1161631 := bstep (se 1 (by rfl) ⟨871223, by rfl⟩ : syracuseStep 1161631 = 1742447) B1742447
theorem B1161679 : Blo 1160639 1161679 := bstep (se 1 (by rfl) ⟨871259, by rfl⟩ : syracuseStep 1161679 = 1742519) B1742519
theorem B1161703 : Blo 1160639 1161703 := bstep (se 1 (by rfl) ⟨871277, by rfl⟩ : syracuseStep 1161703 = 1742555) B1742555
theorem B1161819 : Blo 1160639 1161819 := bstep (se 1 (by rfl) ⟨871364, by rfl⟩ : syracuseStep 1161819 = 1742729) B1742729
theorem B1161887 : Blo 1160639 1161887 := bstep (se 1 (by rfl) ⟨871415, by rfl⟩ : syracuseStep 1161887 = 1742831) B1742831
theorem B1162055 : Blo 1160639 1162055 := bstep (se 1 (by rfl) ⟨871541, by rfl⟩ : syracuseStep 1162055 = 1743083) B1743083
theorem B1162095 : Blo 1160639 1162095 := bstep (se 1 (by rfl) ⟨871571, by rfl⟩ : syracuseStep 1162095 = 1743143) B1743143
theorem B1162151 : Blo 1160639 1162151 := bstep (se 1 (by rfl) ⟨871613, by rfl⟩ : syracuseStep 1162151 = 1743227) B1743227
theorem B9944153 : Blo 1160639 9944153 := bstep (se 2 (by rfl) ⟨3729057, by rfl⟩ : syracuseStep 9944153 = 7458115) B7458115
theorem B1162331 : Blo 1160639 1162331 := bstep (se 1 (by rfl) ⟨871748, by rfl⟩ : syracuseStep 1162331 = 1743497) B1743497
theorem B1162447 : Blo 1160639 1162447 := bstep (se 1 (by rfl) ⟨871835, by rfl⟩ : syracuseStep 1162447 = 1743671) B1743671
theorem B1162471 : Blo 1160639 1162471 := bstep (se 1 (by rfl) ⟨871853, by rfl⟩ : syracuseStep 1162471 = 1743707) B1743707
theorem B5881085 : Blo 1160639 5881085 := bstep (se 3 (by rfl) ⟨1102703, by rfl⟩ : syracuseStep 5881085 = 2205407) B2205407
theorem B1162567 : Blo 1160639 1162567 := bstep (se 1 (by rfl) ⟨871925, by rfl⟩ : syracuseStep 1162567 = 1743851) B1743851
theorem B137641315 : Blo 1160639 137641315 := bstep (se 1 (by rfl) ⟨103230986, by rfl⟩ : syracuseStep 137641315 = 206461973) B206461973
theorem B1162703 : Blo 1160639 1162703 := bstep (se 1 (by rfl) ⟨872027, by rfl⟩ : syracuseStep 1162703 = 1744055) B1744055
theorem B7159403 : Blo 1160639 7159403 := bstep (se 1 (by rfl) ⟨5369552, by rfl⟩ : syracuseStep 7159403 = 10739105) B10739105
theorem B2866799 : Blo 1160639 2866799 := bstep (se 1 (by rfl) ⟨2150099, by rfl⟩ : syracuseStep 2866799 = 4300199) B4300199
theorem B1162863 : Blo 1160639 1162863 := bstep (se 1 (by rfl) ⟨872147, by rfl⟩ : syracuseStep 1162863 = 1744295) B1744295
theorem B1162919 : Blo 1160639 1162919 := bstep (se 1 (by rfl) ⟨872189, by rfl⟩ : syracuseStep 1162919 = 1744379) B1744379
theorem B1162983 : Blo 1160639 1162983 := bstep (se 1 (by rfl) ⟨872237, by rfl⟩ : syracuseStep 1162983 = 1744475) B1744475
theorem B1163039 : Blo 1160639 1163039 := bstep (se 1 (by rfl) ⟨872279, by rfl⟩ : syracuseStep 1163039 = 1744559) B1744559
theorem B1163119 : Blo 1160639 1163119 := bstep (se 1 (by rfl) ⟨872339, by rfl⟩ : syracuseStep 1163119 = 1744679) B1744679
theorem B1163175 : Blo 1160639 1163175 := bstep (se 1 (by rfl) ⟨872381, by rfl⟩ : syracuseStep 1163175 = 1744763) B1744763
theorem B5881895 : Blo 1160639 5881895 := bstep (se 1 (by rfl) ⟨4411421, by rfl⟩ : syracuseStep 5881895 = 8822843) B8822843
theorem B1163455 : Blo 1160639 1163455 := bstep (se 1 (by rfl) ⟨872591, by rfl⟩ : syracuseStep 1163455 = 1745183) B1745183
theorem B1163471 : Blo 1160639 1163471 := bstep (se 1 (by rfl) ⟨872603, by rfl⟩ : syracuseStep 1163471 = 1745207) B1745207
theorem B1163519 : Blo 1160639 1163519 := bstep (se 1 (by rfl) ⟨872639, by rfl⟩ : syracuseStep 1163519 = 1745279) B1745279
theorem B1163567 : Blo 1160639 1163567 := bstep (se 1 (by rfl) ⟨872675, by rfl⟩ : syracuseStep 1163567 = 1745351) B1745351
theorem B3719677 : Blo 1160639 3719677 := bstep (se 3 (by rfl) ⟨697439, by rfl⟩ : syracuseStep 3719677 = 1394879) B1394879
theorem B1163803 : Blo 1160639 1163803 := bstep (se 1 (by rfl) ⟨872852, by rfl⟩ : syracuseStep 1163803 = 1745705) B1745705
theorem B1163807 : Blo 1160639 1163807 := bstep (se 1 (by rfl) ⟨872855, by rfl⟩ : syracuseStep 1163807 = 1745711) B1745711
theorem B1163887 : Blo 1160639 1163887 := bstep (se 1 (by rfl) ⟨872915, by rfl⟩ : syracuseStep 1163887 = 1745831) B1745831
theorem B1327727 : Blo 1160639 1327727 := bstep (se 1 (by rfl) ⟨995795, by rfl⟩ : syracuseStep 1327727 = 1991591) B1991591
theorem B7455347 : Blo 1160639 7455347 := bstep (se 1 (by rfl) ⟨5591510, by rfl⟩ : syracuseStep 7455347 = 11183021) B11183021
theorem B1163943 : Blo 1160639 1163943 := bstep (se 1 (by rfl) ⟨872957, by rfl⟩ : syracuseStep 1163943 = 1745915) B1745915
theorem B1163983 : Blo 1160639 1163983 := bstep (se 1 (by rfl) ⟨872987, by rfl⟩ : syracuseStep 1163983 = 1745975) B1745975
theorem B1164063 : Blo 1160639 1164063 := bstep (se 1 (by rfl) ⟨873047, by rfl⟩ : syracuseStep 1164063 = 1746095) B1746095
theorem B12567581 : Blo 1160639 12567581 := bstep (se 3 (by rfl) ⟨2356421, by rfl⟩ : syracuseStep 12567581 = 4712843) B4712843
theorem B1164335 : Blo 1160639 1164335 := bstep (se 1 (by rfl) ⟨873251, by rfl⟩ : syracuseStep 1164335 = 1746503) B1746503
theorem B8832077 : Blo 1160639 8832077 := bstep (se 3 (by rfl) ⟨1656014, by rfl⟩ : syracuseStep 8832077 = 3312029) B3312029
theorem B1164399 : Blo 1160639 1164399 := bstep (se 1 (by rfl) ⟨873299, by rfl⟩ : syracuseStep 1164399 = 1746599) B1746599
theorem B1164455 : Blo 1160639 1164455 := bstep (se 1 (by rfl) ⟨873341, by rfl⟩ : syracuseStep 1164455 = 1746683) B1746683
theorem B1164479 : Blo 1160639 1164479 := bstep (se 1 (by rfl) ⟨873359, by rfl⟩ : syracuseStep 1164479 = 1746719) B1746719
theorem B1164511 : Blo 1160639 1164511 := bstep (se 1 (by rfl) ⟨873383, by rfl⟩ : syracuseStep 1164511 = 1746767) B1746767
theorem B1164591 : Blo 1160639 1164591 := bstep (se 1 (by rfl) ⟨873443, by rfl⟩ : syracuseStep 1164591 = 1746887) B1746887
theorem B3917213 : Blo 1160639 3917213 := bstep (se 3 (by rfl) ⟨734477, by rfl⟩ : syracuseStep 3917213 = 1468955) B1468955
theorem B3917375 : Blo 1160639 3917375 := bstep (se 1 (by rfl) ⟨2938031, by rfl⟩ : syracuseStep 3917375 = 5876063) B5876063
theorem B3917483 : Blo 1160639 3917483 := bstep (se 1 (by rfl) ⟨2938112, by rfl⟩ : syracuseStep 3917483 = 5876225) B5876225
theorem B9422507 : Blo 1160639 9422507 := bstep (se 1 (by rfl) ⟨7066880, by rfl⟩ : syracuseStep 9422507 = 14133761) B14133761
theorem B3918023 : Blo 1160639 3918023 := bstep (se 1 (by rfl) ⟨2938517, by rfl⟩ : syracuseStep 3918023 = 5877035) B5877035
theorem B11192519 : Blo 1160639 11192519 := bstep (se 1 (by rfl) ⟨8394389, by rfl⟩ : syracuseStep 11192519 = 16788779) B16788779
theorem B5655155 : Blo 1160639 5655155 := bstep (se 1 (by rfl) ⟨4241366, by rfl⟩ : syracuseStep 5655155 = 8482733) B8482733
theorem B5589665 : Blo 1160639 5589665 := bstep (se 2 (by rfl) ⟨2096124, by rfl⟩ : syracuseStep 5589665 = 4192249) B4192249
theorem B3918617 : Blo 1160639 3918617 := bstep (se 2 (by rfl) ⟨1469481, by rfl⟩ : syracuseStep 3918617 = 2938963) B2938963
theorem B1985591 : Blo 1160639 1985591 := bstep (se 1 (by rfl) ⟨1489193, by rfl⟩ : syracuseStep 1985591 = 2978387) B2978387
theorem B4967567 : Blo 1160639 4967567 := bstep (se 1 (by rfl) ⟨3725675, by rfl⟩ : syracuseStep 4967567 = 7451351) B7451351
theorem B3918995 : Blo 1160639 3918995 := bstep (se 1 (by rfl) ⟨2939246, by rfl⟩ : syracuseStep 3918995 = 5878493) B5878493
theorem B3919265 : Blo 1160639 3919265 := bstep (se 2 (by rfl) ⟨1469724, by rfl⟩ : syracuseStep 3919265 = 2939449) B2939449
theorem B14896547 : Blo 1160639 14896547 := bstep (se 1 (by rfl) ⟨11172410, by rfl⟩ : syracuseStep 14896547 = 22344821) B22344821
theorem B8834507 : Blo 1160639 8834507 := bstep (se 1 (by rfl) ⟨6625880, by rfl⟩ : syracuseStep 8834507 = 13251761) B13251761
theorem B3919805 : Blo 1160639 3919805 := bstep (se 3 (by rfl) ⟨734963, by rfl⟩ : syracuseStep 3919805 = 1469927) B1469927
theorem B3919967 : Blo 1160639 3919967 := bstep (se 1 (by rfl) ⟨2939975, by rfl⟩ : syracuseStep 3919967 = 5879951) B5879951
theorem B45961339 : Blo 1160639 45961339 := bstep (se 1 (by rfl) ⟨34471004, by rfl⟩ : syracuseStep 45961339 = 68942009) B68942009
theorem B3921695 : Blo 1160639 3921695 := bstep (se 1 (by rfl) ⟨2941271, by rfl⟩ : syracuseStep 3921695 = 5882543) B5882543
theorem B8836937 : Blo 1160639 8836937 := bstep (se 2 (by rfl) ⟨3313851, by rfl⟩ : syracuseStep 8836937 = 6627703) B6627703
theorem B4413275 : Blo 1160639 4413275 := bstep (se 1 (by rfl) ⟨3309956, by rfl⟩ : syracuseStep 4413275 = 6619913) B6619913
theorem B4478939 : Blo 1160639 4478939 := bstep (se 1 (by rfl) ⟨3359204, by rfl⟩ : syracuseStep 4478939 = 6718409) B6718409
theorem B7952377 : Blo 1160639 7952377 := bstep (se 2 (by rfl) ⟨2982141, by rfl⟩ : syracuseStep 7952377 = 5964283) B5964283
theorem B4250089 : Blo 1160639 4250089 := bstep (se 2 (by rfl) ⟨1593783, by rfl⟩ : syracuseStep 4250089 = 3187567) B3187567
theorem B5593799 : Blo 1160639 5593799 := bstep (se 1 (by rfl) ⟨4195349, by rfl⟩ : syracuseStep 5593799 = 8390699) B8390699
theorem B4971257 : Blo 1160639 4971257 := bstep (se 2 (by rfl) ⟨1864221, by rfl⟩ : syracuseStep 4971257 = 3728443) B3728443
theorem B7068581 : Blo 1160639 7068581 := bstep (se 4 (by rfl) ⟨662679, by rfl⟩ : syracuseStep 7068581 = 1325359) B1325359
theorem B4414931 : Blo 1160639 4414931 := bstep (se 1 (by rfl) ⟨3311198, by rfl⟩ : syracuseStep 4414931 = 6622397) B6622397
theorem B2940583 : Blo 1160639 2940583 := bstep (se 1 (by rfl) ⟨2205437, by rfl⟩ : syracuseStep 2940583 = 4410875) B4410875
theorem B2613023 : Blo 1160639 2613023 := bstep (se 1 (by rfl) ⟨1959767, by rfl⟩ : syracuseStep 2613023 = 3919535) B3919535
theorem B2613239 : Blo 1160639 2613239 := bstep (se 1 (by rfl) ⟨1959929, by rfl⟩ : syracuseStep 2613239 = 3919859) B3919859
theorem B37773317 : Blo 1160639 37773317 := bstep (se 4 (by rfl) ⟨3541248, by rfl⟩ : syracuseStep 37773317 = 7082497) B7082497
theorem B4972691 : Blo 1160639 4972691 := bstep (se 1 (by rfl) ⟨3729518, by rfl⟩ : syracuseStep 4972691 = 7459037) B7459037
theorem B2613455 : Blo 1160639 2613455 := bstep (se 1 (by rfl) ⟨1960091, by rfl⟩ : syracuseStep 2613455 = 3920183) B3920183
theorem B4186397 : Blo 1160639 4186397 := bstep (se 3 (by rfl) ⟨784949, by rfl⟩ : syracuseStep 4186397 = 1569899) B1569899
theorem B2613599 : Blo 1160639 2613599 := bstep (se 1 (by rfl) ⟨1960199, by rfl⟩ : syracuseStep 2613599 = 3920399) B3920399
theorem B14901671 : Blo 1160639 14901671 := bstep (se 1 (by rfl) ⟨11176253, by rfl⟩ : syracuseStep 14901671 = 22352507) B22352507
theorem B9560531 : Blo 1160639 9560531 := bstep (se 1 (by rfl) ⟨7170398, by rfl⟩ : syracuseStep 9560531 = 14340797) B14340797
theorem B6611483 : Blo 1160639 6611483 := bstep (se 1 (by rfl) ⟨4958612, by rfl⟩ : syracuseStep 6611483 = 9917225) B9917225
theorem B2482895 : Blo 1160639 2482895 := bstep (se 1 (by rfl) ⟨1862171, by rfl⟩ : syracuseStep 2482895 = 3724343) B3724343
theorem B2614319 : Blo 1160639 2614319 := bstep (se 1 (by rfl) ⟨1960739, by rfl⟩ : syracuseStep 2614319 = 3921479) B3921479
theorem B4973683 : Blo 1160639 4973683 := bstep (se 1 (by rfl) ⟨3730262, by rfl⟩ : syracuseStep 4973683 = 7460525) B7460525
theorem B1959079 : Blo 1160639 1959079 := bstep (se 1 (by rfl) ⟨1469309, by rfl⟩ : syracuseStep 1959079 = 2938619) B2938619
theorem B80438579 : Blo 1160639 80438579 := bstep (se 1 (by rfl) ⟨60328934, by rfl⟩ : syracuseStep 80438579 = 120657869) B120657869
theorem B2614967 : Blo 1160639 2614967 := bstep (se 1 (by rfl) ⟨1961225, by rfl⟩ : syracuseStep 2614967 = 3922451) B3922451
theorem B9922283 : Blo 1160639 9922283 := bstep (se 1 (by rfl) ⟨7441712, by rfl⟩ : syracuseStep 9922283 = 14883425) B14883425
theorem B1959835 : Blo 1160639 1959835 := bstep (se 1 (by rfl) ⟨1469876, by rfl⟩ : syracuseStep 1959835 = 2939753) B2939753
theorem B2942963 : Blo 1160639 2942963 := bstep (se 1 (by rfl) ⟨2207222, by rfl⟩ : syracuseStep 2942963 = 4414445) B4414445
theorem B1861679 : Blo 1160639 1861679 := bstep (se 1 (by rfl) ⟨1396259, by rfl⟩ : syracuseStep 1861679 = 2792519) B2792519
theorem B5662817 : Blo 1160639 5662817 := bstep (se 2 (by rfl) ⟨2123556, by rfl⟩ : syracuseStep 5662817 = 4247113) B4247113
theorem B2615417 : Blo 1160639 2615417 := bstep (se 2 (by rfl) ⟨980781, by rfl⟩ : syracuseStep 2615417 = 1961563) B1961563
theorem B4417679 : Blo 1160639 4417679 := bstep (se 1 (by rfl) ⟨3313259, by rfl⟩ : syracuseStep 4417679 = 6626519) B6626519
theorem B11167915 : Blo 1160639 11167915 := bstep (se 1 (by rfl) ⟨8375936, by rfl⟩ : syracuseStep 11167915 = 16751873) B16751873
theorem B19884203 : Blo 1160639 19884203 := bstep (se 1 (by rfl) ⟨14913152, by rfl⟩ : syracuseStep 19884203 = 29826305) B29826305
theorem B1960247 : Blo 1160639 1960247 := bstep (se 1 (by rfl) ⟨1470185, by rfl⟩ : syracuseStep 1960247 = 2940371) B2940371
theorem B2484535 : Blo 1160639 2484535 := bstep (se 1 (by rfl) ⟨1863401, by rfl⟩ : syracuseStep 2484535 = 3726803) B3726803
theorem B2943479 : Blo 1160639 2943479 := bstep (se 1 (by rfl) ⟨2207609, by rfl⟩ : syracuseStep 2943479 = 4415219) B4415219
theorem B22669895 : Blo 1160639 22669895 := bstep (se 1 (by rfl) ⟨17002421, by rfl⟩ : syracuseStep 22669895 = 34004843) B34004843
theorem B18868889 : Blo 1160639 18868889 := bstep (se 2 (by rfl) ⟨7075833, by rfl⟩ : syracuseStep 18868889 = 14151667) B14151667
theorem B3140491 : Blo 1160639 3140491 := bstep (se 1 (by rfl) ⟨2355368, by rfl⟩ : syracuseStep 3140491 = 4710737) B4710737
theorem B2616731 : Blo 1160639 2616731 := bstep (se 1 (by rfl) ⟨1962548, by rfl⟩ : syracuseStep 2616731 = 3925097) B3925097
theorem B1961543 : Blo 1160639 1961543 := bstep (se 1 (by rfl) ⟨1471157, by rfl⟩ : syracuseStep 1961543 = 2942315) B2942315
theorem B2944583 : Blo 1160639 2944583 := bstep (se 1 (by rfl) ⟨2208437, by rfl⟩ : syracuseStep 2944583 = 4416875) B4416875
theorem B4714075 : Blo 1160639 4714075 := bstep (se 1 (by rfl) ⟨3535556, by rfl⟩ : syracuseStep 4714075 = 7071113) B7071113
theorem B1306363 : Blo 1160639 1306363 := bstep (se 1 (by rfl) ⟨979772, by rfl⟩ : syracuseStep 1306363 = 1959545) B1959545
theorem B5893883 : Blo 1160639 5893883 := bstep (se 1 (by rfl) ⟨4420412, by rfl⟩ : syracuseStep 5893883 = 8840825) B8840825
theorem B2617307 : Blo 1160639 2617307 := bstep (se 1 (by rfl) ⟨1962980, by rfl⟩ : syracuseStep 2617307 = 3925961) B3925961
theorem B1306687 : Blo 1160639 1306687 := bstep (se 1 (by rfl) ⟨980015, by rfl⟩ : syracuseStep 1306687 = 1960031) B1960031
theorem B1241191 : Blo 1160639 1241191 := bstep (se 1 (by rfl) ⟨930893, by rfl⟩ : syracuseStep 1241191 = 1861787) B1861787
theorem B2617487 : Blo 1160639 2617487 := bstep (se 1 (by rfl) ⟨1963115, by rfl⟩ : syracuseStep 2617487 = 3926231) B3926231
theorem B2617577 : Blo 1160639 2617577 := bstep (se 2 (by rfl) ⟨981591, by rfl⟩ : syracuseStep 2617577 = 1963183) B1963183
theorem B2617703 : Blo 1160639 2617703 := bstep (se 1 (by rfl) ⟨1963277, by rfl⟩ : syracuseStep 2617703 = 3926555) B3926555
theorem B4715243 : Blo 1160639 4715243 := bstep (se 1 (by rfl) ⟨3536432, by rfl⟩ : syracuseStep 4715243 = 7072865) B7072865
theorem B1274783 : Blo 1160639 1274783 := bstep (se 1 (by rfl) ⟨956087, by rfl⟩ : syracuseStep 1274783 = 1912175) B1912175
theorem B1307551 : Blo 1160639 1307551 := bstep (se 1 (by rfl) ⟨980663, by rfl⟩ : syracuseStep 1307551 = 1961327) B1961327
theorem B2618279 : Blo 1160639 2618279 := bstep (se 1 (by rfl) ⟨1963709, by rfl⟩ : syracuseStep 2618279 = 3927419) B3927419
theorem B1963001 : Blo 1160639 1963001 := bstep (se 2 (by rfl) ⟨736125, by rfl⟩ : syracuseStep 1963001 = 1472251) B1472251
theorem B2946041 : Blo 1160639 2946041 := bstep (se 2 (by rfl) ⟨1104765, by rfl⟩ : syracuseStep 2946041 = 2209531) B2209531
theorem B2094121 : Blo 1160639 2094121 := bstep (se 2 (by rfl) ⟨785295, by rfl⟩ : syracuseStep 2094121 = 1570591) B1570591
theorem B1307803 : Blo 1160639 1307803 := bstep (se 1 (by rfl) ⟨980852, by rfl⟩ : syracuseStep 1307803 = 1961705) B1961705
theorem B1963271 : Blo 1160639 1963271 := bstep (se 1 (by rfl) ⟨1472453, by rfl⟩ : syracuseStep 1963271 = 2944907) B2944907
theorem B1570537 : Blo 1160639 1570537 := bstep (se 2 (by rfl) ⟨588951, by rfl⟩ : syracuseStep 1570537 = 1177903) B1177903
theorem B11171641 : Blo 1160639 11171641 := bstep (se 2 (by rfl) ⟨4189365, by rfl⟩ : syracuseStep 11171641 = 8378731) B8378731
theorem B1308487 : Blo 1160639 1308487 := bstep (se 1 (by rfl) ⟨981365, by rfl⟩ : syracuseStep 1308487 = 1962731) B1962731
theorem B2619215 : Blo 1160639 2619215 := bstep (se 1 (by rfl) ⟨1964411, by rfl⟩ : syracuseStep 2619215 = 3928823) B3928823
theorem B3307463 : Blo 1160639 3307463 := bstep (se 1 (by rfl) ⟨2480597, by rfl⟩ : syracuseStep 3307463 = 4961195) B4961195
theorem B1243207 : Blo 1160639 1243207 := bstep (se 1 (by rfl) ⟨932405, by rfl⟩ : syracuseStep 1243207 = 1864811) B1864811
theorem B2619575 : Blo 1160639 2619575 := bstep (se 1 (by rfl) ⟨1964681, by rfl⟩ : syracuseStep 2619575 = 3929363) B3929363
theorem B1964263 : Blo 1160639 1964263 := bstep (se 1 (by rfl) ⟨1473197, by rfl⟩ : syracuseStep 1964263 = 2946395) B2946395
theorem B40794553 : Blo 1160639 40794553 := bstep (se 2 (by rfl) ⟨15297957, by rfl⟩ : syracuseStep 40794553 = 30595915) B30595915
theorem B19888577 : Blo 1160639 19888577 := bstep (se 2 (by rfl) ⟨7458216, by rfl⟩ : syracuseStep 19888577 = 14916433) B14916433
theorem B1309135 : Blo 1160639 1309135 := bstep (se 1 (by rfl) ⟨981851, by rfl⟩ : syracuseStep 1309135 = 1963703) B1963703
theorem B2619935 : Blo 1160639 2619935 := bstep (se 1 (by rfl) ⟨1964951, by rfl⟩ : syracuseStep 2619935 = 3929903) B3929903
theorem B2652763 : Blo 1160639 2652763 := bstep (se 1 (by rfl) ⟨1989572, by rfl⟩ : syracuseStep 2652763 = 3979145) B3979145
theorem B2620169 : Blo 1160639 2620169 := bstep (se 2 (by rfl) ⟨982563, by rfl⟩ : syracuseStep 2620169 = 1965127) B1965127
theorem B1965161 : Blo 1160639 1965161 := bstep (se 2 (by rfl) ⟨736935, by rfl⟩ : syracuseStep 1965161 = 1473871) B1473871
theorem B4717693 : Blo 1160639 4717693 := bstep (se 3 (by rfl) ⟨884567, by rfl⟩ : syracuseStep 4717693 = 1769135) B1769135
theorem B1309927 : Blo 1160639 1309927 := bstep (se 1 (by rfl) ⟨982445, by rfl⟩ : syracuseStep 1309927 = 1964891) B1964891
theorem B1573543 : Blo 1160639 1573543 := bstep (se 1 (by rfl) ⟨1180157, by rfl⟩ : syracuseStep 1573543 = 2360315) B2360315
theorem B1573663 : Blo 1160639 1573663 := bstep (se 1 (by rfl) ⟨1180247, by rfl⟩ : syracuseStep 1573663 = 2360495) B2360495
theorem B3539963 : Blo 1160639 3539963 := bstep (se 1 (by rfl) ⟨2654972, by rfl⟩ : syracuseStep 3539963 = 5309945) B5309945
theorem B25494749 : Blo 1160639 25494749 := bstep (se 3 (by rfl) ⟨4780265, by rfl⟩ : syracuseStep 25494749 = 9560531) B9560531
theorem B5441087 : Blo 1160639 5441087 := bstep (se 1 (by rfl) ⟨4080815, by rfl⟩ : syracuseStep 5441087 = 8161631) B8161631
theorem B3540605 : Blo 1160639 3540605 := bstep (se 3 (by rfl) ⟨663863, by rfl⟩ : syracuseStep 3540605 = 1327727) B1327727
theorem B3311711 : Blo 1160639 3311711 := bstep (se 1 (by rfl) ⟨2483783, by rfl⟩ : syracuseStep 3311711 = 4967567) B4967567
theorem B9931031 : Blo 1160639 9931031 := bstep (se 1 (by rfl) ⟨7448273, by rfl⟩ : syracuseStep 9931031 = 14896547) B14896547
theorem B6621871 : Blo 1160639 6621871 := bstep (se 1 (by rfl) ⟨4966403, by rfl⟩ : syracuseStep 6621871 = 9932807) B9932807
theorem B3312713 : Blo 1160639 3312713 := bstep (se 2 (by rfl) ⟨1242267, by rfl⟩ : syracuseStep 3312713 = 2484535) B2484535
theorem B2985959 : Blo 1160639 2985959 := bstep (se 1 (by rfl) ⟨2239469, by rfl⟩ : syracuseStep 2985959 = 4478939) B4478939
theorem B181080197 : Blo 1160639 181080197 := bstep (se 4 (by rfl) ⟨16976268, by rfl⟩ : syracuseStep 181080197 = 33952537) B33952537
theorem B3314171 : Blo 1160639 3314171 := bstep (se 1 (by rfl) ⟨2485628, by rfl⟩ : syracuseStep 3314171 = 4971257) B4971257
theorem B19862333 : Blo 1160639 19862333 := bstep (se 3 (by rfl) ⟨3724187, by rfl⟩ : syracuseStep 19862333 = 7448375) B7448375
theorem B1741817 : Blo 1160639 1741817 := bstep (se 2 (by rfl) ⟨653181, by rfl⟩ : syracuseStep 1741817 = 1306363) B1306363
theorem B1742015 : Blo 1160639 1742015 := bstep (se 1 (by rfl) ⟨1306511, by rfl⟩ : syracuseStep 1742015 = 2613023) B2613023
theorem B1742159 : Blo 1160639 1742159 := bstep (se 1 (by rfl) ⟨1306619, by rfl⟩ : syracuseStep 1742159 = 2613239) B2613239
theorem B1742249 : Blo 1160639 1742249 := bstep (se 2 (by rfl) ⟨653343, by rfl⟩ : syracuseStep 1742249 = 1306687) B1306687
theorem B1742303 : Blo 1160639 1742303 := bstep (se 1 (by rfl) ⟨1306727, by rfl⟩ : syracuseStep 1742303 = 2613455) B2613455
theorem B61281785 : Blo 1160639 61281785 := bstep (se 2 (by rfl) ⟨22980669, by rfl⟩ : syracuseStep 61281785 = 45961339) B45961339
theorem B2790931 : Blo 1160639 2790931 := bstep (se 1 (by rfl) ⟨2093198, by rfl⟩ : syracuseStep 2790931 = 4186397) B4186397
theorem B1742399 : Blo 1160639 1742399 := bstep (se 1 (by rfl) ⟨1306799, by rfl⟩ : syracuseStep 1742399 = 2613599) B2613599
theorem B9934447 : Blo 1160639 9934447 := bstep (se 1 (by rfl) ⟨7450835, by rfl⟩ : syracuseStep 9934447 = 14901671) B14901671
theorem B18880303 : Blo 1160639 18880303 := bstep (se 1 (by rfl) ⟨14160227, by rfl⟩ : syracuseStep 18880303 = 28320455) B28320455
theorem B1742879 : Blo 1160639 1742879 := bstep (se 1 (by rfl) ⟨1307159, by rfl⟩ : syracuseStep 1742879 = 2614319) B2614319
theorem B2300015 : Blo 1160639 2300015 := bstep (se 1 (by rfl) ⟨1725011, by rfl⟩ : syracuseStep 2300015 = 3450023) B3450023
theorem B1743311 : Blo 1160639 1743311 := bstep (se 1 (by rfl) ⟨1307483, by rfl⟩ : syracuseStep 1743311 = 2614967) B2614967
theorem B7444993 : Blo 1160639 7444993 := bstep (se 2 (by rfl) ⟨2791872, by rfl⟩ : syracuseStep 7444993 = 5583745) B5583745
theorem B1743401 : Blo 1160639 1743401 := bstep (se 2 (by rfl) ⟨653775, by rfl⟩ : syracuseStep 1743401 = 1307551) B1307551
theorem B2792161 : Blo 1160639 2792161 := bstep (se 2 (by rfl) ⟨1047060, by rfl⟩ : syracuseStep 2792161 = 2094121) B2094121
theorem B3775211 : Blo 1160639 3775211 := bstep (se 1 (by rfl) ⟨2831408, by rfl⟩ : syracuseStep 3775211 = 5662817) B5662817
theorem B1743611 : Blo 1160639 1743611 := bstep (se 1 (by rfl) ⟨1307708, by rfl⟩ : syracuseStep 1743611 = 2615417) B2615417
theorem B1743737 : Blo 1160639 1743737 := bstep (se 2 (by rfl) ⟨653901, by rfl⟩ : syracuseStep 1743737 = 1307803) B1307803
theorem B15080413 : Blo 1160639 15080413 := bstep (se 3 (by rfl) ⟨2827577, by rfl⟩ : syracuseStep 15080413 = 5655155) B5655155
theorem B15113263 : Blo 1160639 15113263 := bstep (se 1 (by rfl) ⟨11334947, by rfl⟩ : syracuseStep 15113263 = 22669895) B22669895
theorem B14916797 : Blo 1160639 14916797 := bstep (se 3 (by rfl) ⟨2796899, by rfl⟩ : syracuseStep 14916797 = 5593799) B5593799
theorem B1744487 : Blo 1160639 1744487 := bstep (se 1 (by rfl) ⟨1308365, by rfl⟩ : syracuseStep 1744487 = 2616731) B2616731
theorem B1744649 : Blo 1160639 1744649 := bstep (se 2 (by rfl) ⟨654243, by rfl⟩ : syracuseStep 1744649 = 1308487) B1308487
theorem B1744871 : Blo 1160639 1744871 := bstep (se 1 (by rfl) ⟨1308653, by rfl⟩ : syracuseStep 1744871 = 2617307) B2617307
theorem B1744991 : Blo 1160639 1744991 := bstep (se 1 (by rfl) ⟨1308743, by rfl⟩ : syracuseStep 1744991 = 2617487) B2617487
theorem B1745051 : Blo 1160639 1745051 := bstep (se 1 (by rfl) ⟨1308788, by rfl⟩ : syracuseStep 1745051 = 2617577) B2617577
theorem B1745135 : Blo 1160639 1745135 := bstep (se 1 (by rfl) ⟨1308851, by rfl⟩ : syracuseStep 1745135 = 2617703) B2617703
theorem B1745513 : Blo 1160639 1745513 := bstep (se 2 (by rfl) ⟨654567, by rfl⟩ : syracuseStep 1745513 = 1309135) B1309135
theorem B1745519 : Blo 1160639 1745519 := bstep (se 1 (by rfl) ⟨1309139, by rfl⟩ : syracuseStep 1745519 = 2618279) B2618279
theorem B1746143 : Blo 1160639 1746143 := bstep (se 1 (by rfl) ⟨1309607, by rfl⟩ : syracuseStep 1746143 = 2619215) B2619215
theorem B2204975 : Blo 1160639 2204975 := bstep (se 1 (by rfl) ⟨1653731, by rfl⟩ : syracuseStep 2204975 = 3307463) B3307463
theorem B1746383 : Blo 1160639 1746383 := bstep (se 1 (by rfl) ⟨1309787, by rfl⟩ : syracuseStep 1746383 = 2619575) B2619575
theorem B1746569 : Blo 1160639 1746569 := bstep (se 2 (by rfl) ⟨654963, by rfl⟩ : syracuseStep 1746569 = 1309927) B1309927
theorem B1746623 : Blo 1160639 1746623 := bstep (se 1 (by rfl) ⟨1309967, by rfl⟩ : syracuseStep 1746623 = 2619935) B2619935
theorem B1746779 : Blo 1160639 1746779 := bstep (se 1 (by rfl) ⟨1310084, by rfl⟩ : syracuseStep 1746779 = 2620169) B2620169
theorem B6629435 : Blo 1160639 6629435 := bstep (se 1 (by rfl) ⟨4972076, by rfl⟩ : syracuseStep 6629435 = 9944153) B9944153
theorem B1911199 : Blo 1160639 1911199 := bstep (se 1 (by rfl) ⟨1433399, by rfl⟩ : syracuseStep 1911199 = 2866799) B2866799
theorem B6630437 : Blo 1160639 6630437 := bstep (se 4 (by rfl) ⟨621603, by rfl⟩ : syracuseStep 6630437 = 1243207) B1243207
theorem B4959569 : Blo 1160639 4959569 := bstep (se 2 (by rfl) ⟨1859838, by rfl⟩ : syracuseStep 4959569 = 3719677) B3719677
theorem B8826731 : Blo 1160639 8826731 := bstep (se 1 (by rfl) ⟨6620048, by rfl⟩ : syracuseStep 8826731 = 13240097) B13240097
theorem B26882057 : Blo 1160639 26882057 := bstep (se 2 (by rfl) ⟨10080771, by rfl⟩ : syracuseStep 26882057 = 20161543) B20161543
theorem B14921765 : Blo 1160639 14921765 := bstep (se 4 (by rfl) ⟨1398915, by rfl⟩ : syracuseStep 14921765 = 2797831) B2797831
theorem B6631577 : Blo 1160639 6631577 := bstep (se 2 (by rfl) ⟨2486841, by rfl⟩ : syracuseStep 6631577 = 4973683) B4973683
theorem B4960511 : Blo 1160639 4960511 := bstep (se 1 (by rfl) ⟨3720383, by rfl⟩ : syracuseStep 4960511 = 7440767) B7440767
theorem B2797823 : Blo 1160639 2797823 := bstep (se 1 (by rfl) ⟨2098367, by rfl⟩ : syracuseStep 2797823 = 4196735) B4196735
theorem B54440873 : Blo 1160639 54440873 := bstep (se 2 (by rfl) ⟨20415327, by rfl⟩ : syracuseStep 54440873 = 40830655) B40830655
theorem B1160731 : Blo 1160639 1160731 := bstep (se 1 (by rfl) ⟨870548, by rfl⟩ : syracuseStep 1160731 = 1741097) B1741097
theorem B14890553 : Blo 1160639 14890553 := bstep (se 2 (by rfl) ⟨5583957, by rfl⟩ : syracuseStep 14890553 = 11167915) B11167915
theorem B1160911 : Blo 1160639 1160911 := bstep (se 1 (by rfl) ⟨870683, by rfl⟩ : syracuseStep 1160911 = 1741367) B1741367
theorem B1161151 : Blo 1160639 1161151 := bstep (se 1 (by rfl) ⟨870863, by rfl⟩ : syracuseStep 1161151 = 1741727) B1741727
theorem B1161279 : Blo 1160639 1161279 := bstep (se 1 (by rfl) ⟨870959, by rfl⟩ : syracuseStep 1161279 = 1741919) B1741919
theorem B1161319 : Blo 1160639 1161319 := bstep (se 1 (by rfl) ⟨870989, by rfl⟩ : syracuseStep 1161319 = 1741979) B1741979
theorem B15906941 : Blo 1160639 15906941 := bstep (se 3 (by rfl) ⟨2982551, by rfl⟩ : syracuseStep 15906941 = 5965103) B5965103
theorem B9943195 : Blo 1160639 9943195 := bstep (se 1 (by rfl) ⟨7457396, by rfl⟩ : syracuseStep 9943195 = 14914793) B14914793
theorem B235518167 : Blo 1160639 235518167 := bstep (se 1 (by rfl) ⟨176638625, by rfl⟩ : syracuseStep 235518167 = 353277251) B353277251
theorem B12564983 : Blo 1160639 12564983 := bstep (se 1 (by rfl) ⟨9423737, by rfl⟩ : syracuseStep 12564983 = 18847475) B18847475
theorem B1161775 : Blo 1160639 1161775 := bstep (se 1 (by rfl) ⟨871331, by rfl⟩ : syracuseStep 1161775 = 1742663) B1742663
theorem B1162175 : Blo 1160639 1162175 := bstep (se 1 (by rfl) ⟨871631, by rfl⟩ : syracuseStep 1162175 = 1743263) B1743263
theorem B1162223 : Blo 1160639 1162223 := bstep (se 1 (by rfl) ⟨871667, by rfl⟩ : syracuseStep 1162223 = 1743335) B1743335
theorem B37665881 : Blo 1160639 37665881 := bstep (se 2 (by rfl) ⟨14124705, by rfl⟩ : syracuseStep 37665881 = 28249411) B28249411
theorem B5880923 : Blo 1160639 5880923 := bstep (se 1 (by rfl) ⟨4410692, by rfl⟩ : syracuseStep 5880923 = 8821385) B8821385
theorem B1162719 : Blo 1160639 1162719 := bstep (se 1 (by rfl) ⟨872039, by rfl⟩ : syracuseStep 1162719 = 1744079) B1744079
theorem B1162799 : Blo 1160639 1162799 := bstep (se 1 (by rfl) ⟨872099, by rfl⟩ : syracuseStep 1162799 = 1744199) B1744199
theorem B1162907 : Blo 1160639 1162907 := bstep (se 1 (by rfl) ⟨872180, by rfl⟩ : syracuseStep 1162907 = 1744361) B1744361
theorem B1163003 : Blo 1160639 1163003 := bstep (se 1 (by rfl) ⟨872252, by rfl⟩ : syracuseStep 1163003 = 1744505) B1744505
theorem B11190095 : Blo 1160639 11190095 := bstep (se 1 (by rfl) ⟨8392571, by rfl⟩ : syracuseStep 11190095 = 16785143) B16785143
theorem B1163167 : Blo 1160639 1163167 := bstep (se 1 (by rfl) ⟨872375, by rfl⟩ : syracuseStep 1163167 = 1744751) B1744751
theorem B25182211 : Blo 1160639 25182211 := bstep (se 1 (by rfl) ⟨18886658, by rfl⟩ : syracuseStep 25182211 = 37773317) B37773317
theorem B1654921 : Blo 1160639 1654921 := bstep (se 2 (by rfl) ⟨620595, by rfl⟩ : syracuseStep 1654921 = 1241191) B1241191
theorem B4407655 : Blo 1160639 4407655 := bstep (se 1 (by rfl) ⟨3305741, by rfl⟩ : syracuseStep 4407655 = 6611483) B6611483
theorem B1163623 : Blo 1160639 1163623 := bstep (se 1 (by rfl) ⟨872717, by rfl⟩ : syracuseStep 1163623 = 1745435) B1745435
theorem B1655263 : Blo 1160639 1655263 := bstep (se 1 (by rfl) ⟨1241447, by rfl⟩ : syracuseStep 1655263 = 2482895) B2482895
theorem B1163743 : Blo 1160639 1163743 := bstep (se 1 (by rfl) ⟨872807, by rfl⟩ : syracuseStep 1163743 = 1745615) B1745615
theorem B1163751 : Blo 1160639 1163751 := bstep (se 1 (by rfl) ⟨872813, by rfl⟩ : syracuseStep 1163751 = 1745627) B1745627
theorem B1164027 : Blo 1160639 1164027 := bstep (se 1 (by rfl) ⟨873020, by rfl⟩ : syracuseStep 1164027 = 1746041) B1746041
theorem B53625719 : Blo 1160639 53625719 := bstep (se 1 (by rfl) ⟨40219289, by rfl⟩ : syracuseStep 53625719 = 80438579) B80438579
theorem B1492015 : Blo 1160639 1492015 := bstep (se 1 (by rfl) ⟨1119011, by rfl⟩ : syracuseStep 1492015 = 2238023) B2238023
theorem B1164607 : Blo 1160639 1164607 := bstep (se 1 (by rfl) ⟨873455, by rfl⟩ : syracuseStep 1164607 = 1746911) B1746911
theorem B1164615 : Blo 1160639 1164615 := bstep (se 1 (by rfl) ⟨873461, by rfl⟩ : syracuseStep 1164615 = 1746923) B1746923
theorem B13256135 : Blo 1160639 13256135 := bstep (se 1 (by rfl) ⟨9942101, by rfl⟩ : syracuseStep 13256135 = 19884203) B19884203
theorem B3917267 : Blo 1160639 3917267 := bstep (se 1 (by rfl) ⟨2937950, by rfl⟩ : syracuseStep 3917267 = 5875901) B5875901
theorem B16762535 : Blo 1160639 16762535 := bstep (se 1 (by rfl) ⟨12571901, by rfl⟩ : syracuseStep 16762535 = 25143803) B25143803
theorem B3917807 : Blo 1160639 3917807 := bstep (se 1 (by rfl) ⟨2938355, by rfl⟩ : syracuseStep 3917807 = 5876711) B5876711
theorem B14895521 : Blo 1160639 14895521 := bstep (se 2 (by rfl) ⟨5585820, by rfl⟩ : syracuseStep 14895521 = 11171641) B11171641
theorem B10603169 : Blo 1160639 10603169 := bstep (se 2 (by rfl) ⟨3976188, by rfl⟩ : syracuseStep 10603169 = 7952377) B7952377
theorem B7457579 : Blo 1160639 7457579 := bstep (se 1 (by rfl) ⟨5593184, by rfl⟩ : syracuseStep 7457579 = 11186369) B11186369
theorem B5294909 : Blo 1160639 5294909 := bstep (se 3 (by rfl) ⟨992795, by rfl⟩ : syracuseStep 5294909 = 1985591) B1985591
theorem B3722651 : Blo 1160639 3722651 := bstep (se 1 (by rfl) ⟨2791988, by rfl⟩ : syracuseStep 3722651 = 5583977) B5583977
theorem B13259051 : Blo 1160639 13259051 := bstep (se 1 (by rfl) ⟨9944288, by rfl⟩ : syracuseStep 13259051 = 19888577) B19888577
theorem B183521753 : Blo 1160639 183521753 := bstep (se 2 (by rfl) ⟨68820657, by rfl⟩ : syracuseStep 183521753 = 137641315) B137641315
theorem B3920723 : Blo 1160639 3920723 := bstep (se 1 (by rfl) ⟨2940542, by rfl⟩ : syracuseStep 3920723 = 5881085) B5881085
theorem B3920777 : Blo 1160639 3920777 := bstep (se 2 (by rfl) ⟨1470291, by rfl⟩ : syracuseStep 3920777 = 2940583) B2940583
theorem B4772935 : Blo 1160639 4772935 := bstep (se 1 (by rfl) ⟨3579701, by rfl⟩ : syracuseStep 4772935 = 7159403) B7159403
theorem B2938153 : Blo 1160639 2938153 := bstep (se 2 (by rfl) ⟨1101807, by rfl⟩ : syracuseStep 2938153 = 2203615) B2203615
theorem B3921263 : Blo 1160639 3921263 := bstep (se 1 (by rfl) ⟨2940947, by rfl⟩ : syracuseStep 3921263 = 5881895) B5881895
theorem B13260509 : Blo 1160639 13260509 := bstep (se 3 (by rfl) ⟨2486345, by rfl⟩ : syracuseStep 13260509 = 4972691) B4972691
theorem B4970231 : Blo 1160639 4970231 := bstep (se 1 (by rfl) ⟨3727673, by rfl⟩ : syracuseStep 4970231 = 7455347) B7455347
theorem B8378387 : Blo 1160639 8378387 := bstep (se 1 (by rfl) ⟨6283790, by rfl⟩ : syracuseStep 8378387 = 12567581) B12567581
theorem B5888051 : Blo 1160639 5888051 := bstep (se 1 (by rfl) ⟨4416038, by rfl⟩ : syracuseStep 5888051 = 8832077) B8832077
theorem B2611475 : Blo 1160639 2611475 := bstep (se 1 (by rfl) ⟨1958606, by rfl⟩ : syracuseStep 2611475 = 3917213) B3917213
theorem B2611583 : Blo 1160639 2611583 := bstep (se 1 (by rfl) ⟨1958687, by rfl⟩ : syracuseStep 2611583 = 3917375) B3917375
theorem B2611655 : Blo 1160639 2611655 := bstep (se 1 (by rfl) ⟨1958741, by rfl⟩ : syracuseStep 2611655 = 3917483) B3917483
theorem B4413959 : Blo 1160639 4413959 := bstep (se 1 (by rfl) ⟨3310469, by rfl⟩ : syracuseStep 4413959 = 6620939) B6620939
theorem B2513567 : Blo 1160639 2513567 := bstep (se 1 (by rfl) ⟨1885175, by rfl⟩ : syracuseStep 2513567 = 3770351) B3770351
theorem B4414247 : Blo 1160639 4414247 := bstep (se 1 (by rfl) ⟨3310685, by rfl⟩ : syracuseStep 4414247 = 6621371) B6621371
theorem B2612015 : Blo 1160639 2612015 := bstep (se 1 (by rfl) ⟨1959011, by rfl⟩ : syracuseStep 2612015 = 3918023) B3918023
theorem B7461679 : Blo 1160639 7461679 := bstep (se 1 (by rfl) ⟨5596259, by rfl⟩ : syracuseStep 7461679 = 11192519) B11192519
theorem B2612105 : Blo 1160639 2612105 := bstep (se 2 (by rfl) ⟨979539, by rfl⟩ : syracuseStep 2612105 = 1959079) B1959079
theorem B3726443 : Blo 1160639 3726443 := bstep (se 1 (by rfl) ⟨2794832, by rfl⟩ : syracuseStep 3726443 = 5589665) B5589665
theorem B13261967 : Blo 1160639 13261967 := bstep (se 1 (by rfl) ⟨9946475, by rfl⟩ : syracuseStep 13261967 = 19892951) B19892951
theorem B2612411 : Blo 1160639 2612411 := bstep (se 1 (by rfl) ⟨1959308, by rfl⟩ : syracuseStep 2612411 = 3918617) B3918617
theorem B4414763 : Blo 1160639 4414763 := bstep (se 1 (by rfl) ⟨3311072, by rfl⟩ : syracuseStep 4414763 = 6622145) B6622145
theorem B2612663 : Blo 1160639 2612663 := bstep (se 1 (by rfl) ⟨1959497, by rfl⟩ : syracuseStep 2612663 = 3918995) B3918995
theorem B4414945 : Blo 1160639 4414945 := bstep (se 2 (by rfl) ⟨1655604, by rfl⟩ : syracuseStep 4414945 = 3311209) B3311209
theorem B2612843 : Blo 1160639 2612843 := bstep (se 1 (by rfl) ⟨1959632, by rfl⟩ : syracuseStep 2612843 = 3919265) B3919265
theorem B5889671 : Blo 1160639 5889671 := bstep (se 1 (by rfl) ⟨4417253, by rfl⟩ : syracuseStep 5889671 = 8834507) B8834507
theorem B8838881 : Blo 1160639 8838881 := bstep (se 2 (by rfl) ⟨3314580, by rfl⟩ : syracuseStep 8838881 = 6629161) B6629161
theorem B3399421 : Blo 1160639 3399421 := bstep (se 3 (by rfl) ⟨637391, by rfl⟩ : syracuseStep 3399421 = 1274783) B1274783
theorem B2613113 : Blo 1160639 2613113 := bstep (se 2 (by rfl) ⟨979917, by rfl⟩ : syracuseStep 2613113 = 1959835) B1959835
theorem B22667141 : Blo 1160639 22667141 := bstep (se 4 (by rfl) ⟨2125044, by rfl⟩ : syracuseStep 22667141 = 4250089) B4250089
theorem B2613203 : Blo 1160639 2613203 := bstep (se 1 (by rfl) ⟨1959902, by rfl⟩ : syracuseStep 2613203 = 3919805) B3919805
theorem B2613311 : Blo 1160639 2613311 := bstep (se 1 (by rfl) ⟨1959983, by rfl⟩ : syracuseStep 2613311 = 3919967) B3919967
theorem B5890157 : Blo 1160639 5890157 := bstep (se 3 (by rfl) ⟨1104404, by rfl⟩ : syracuseStep 5890157 = 2208809) B2208809
theorem B10904071 : Blo 1160639 10904071 := bstep (se 1 (by rfl) ⟨8178053, by rfl⟩ : syracuseStep 10904071 = 16356107) B16356107
theorem B4187321 : Blo 1160639 4187321 := bstep (se 2 (by rfl) ⟨1570245, by rfl⟩ : syracuseStep 4187321 = 3140491) B3140491
theorem B2614463 : Blo 1160639 2614463 := bstep (se 1 (by rfl) ⟨1960847, by rfl⟩ : syracuseStep 2614463 = 3921695) B3921695
theorem B5891291 : Blo 1160639 5891291 := bstep (se 1 (by rfl) ⟨4418468, by rfl⟩ : syracuseStep 5891291 = 8836937) B8836937
theorem B2942183 : Blo 1160639 2942183 := bstep (se 1 (by rfl) ⟨2206637, by rfl⟩ : syracuseStep 2942183 = 4413275) B4413275
theorem B26830595 : Blo 1160639 26830595 := bstep (se 1 (by rfl) ⟨20122946, by rfl⟩ : syracuseStep 26830595 = 40245893) B40245893
theorem B25126685 : Blo 1160639 25126685 := bstep (se 3 (by rfl) ⟨4711253, by rfl⟩ : syracuseStep 25126685 = 9422507) B9422507
theorem B4712387 : Blo 1160639 4712387 := bstep (se 1 (by rfl) ⟨3534290, by rfl⟩ : syracuseStep 4712387 = 7068581) B7068581
theorem B13264883 : Blo 1160639 13264883 := bstep (se 1 (by rfl) ⟨9948662, by rfl⟩ : syracuseStep 13264883 = 19897325) B19897325
theorem B6285433 : Blo 1160639 6285433 := bstep (se 2 (by rfl) ⟨2357037, by rfl⟩ : syracuseStep 6285433 = 4714075) B4714075
theorem B2943287 : Blo 1160639 2943287 := bstep (se 1 (by rfl) ⟨2207465, by rfl⟩ : syracuseStep 2943287 = 4414931) B4414931
theorem B14903675 : Blo 1160639 14903675 := bstep (se 1 (by rfl) ⟨11177756, by rfl⟩ : syracuseStep 14903675 = 22355513) B22355513
theorem B22309451 : Blo 1160639 22309451 := bstep (se 1 (by rfl) ⟨16732088, by rfl⟩ : syracuseStep 22309451 = 33464177) B33464177
theorem B6613649 : Blo 1160639 6613649 := bstep (se 2 (by rfl) ⟨2480118, by rfl⟩ : syracuseStep 6613649 = 4960237) B4960237
theorem B1862299 : Blo 1160639 1862299 := bstep (se 1 (by rfl) ⟨1396724, by rfl⟩ : syracuseStep 1862299 = 2793449) B2793449
theorem B50228099 : Blo 1160639 50228099 := bstep (se 1 (by rfl) ⟨37671074, by rfl⟩ : syracuseStep 50228099 = 75342149) B75342149
theorem B26832545 : Blo 1160639 26832545 := bstep (se 2 (by rfl) ⟨10062204, by rfl⟩ : syracuseStep 26832545 = 20124409) B20124409
theorem B2944745 : Blo 1160639 2944745 := bstep (se 2 (by rfl) ⟨1104279, by rfl⟩ : syracuseStep 2944745 = 2208559) B2208559
theorem B4419319 : Blo 1160639 4419319 := bstep (se 1 (by rfl) ⟨3314489, by rfl⟩ : syracuseStep 4419319 = 6628979) B6628979
theorem B6614855 : Blo 1160639 6614855 := bstep (se 1 (by rfl) ⟨4961141, by rfl⟩ : syracuseStep 6614855 = 9922283) B9922283
theorem B1961975 : Blo 1160639 1961975 := bstep (se 1 (by rfl) ⟨1471481, by rfl⟩ : syracuseStep 1961975 = 2942963) B2942963
theorem B1241119 : Blo 1160639 1241119 := bstep (se 1 (by rfl) ⟨930839, by rfl⟩ : syracuseStep 1241119 = 1861679) B1861679
theorem B2945119 : Blo 1160639 2945119 := bstep (se 1 (by rfl) ⟨2208839, by rfl⟩ : syracuseStep 2945119 = 4417679) B4417679
theorem B1306831 : Blo 1160639 1306831 := bstep (se 1 (by rfl) ⟨980123, by rfl⟩ : syracuseStep 1306831 = 1960247) B1960247
theorem B1962319 : Blo 1160639 1962319 := bstep (se 1 (by rfl) ⟨1471739, by rfl⟩ : syracuseStep 1962319 = 2943479) B2943479
theorem B12579259 : Blo 1160639 12579259 := bstep (se 1 (by rfl) ⟨9434444, by rfl⟩ : syracuseStep 12579259 = 18868889) B18868889
theorem B2094049 : Blo 1160639 2094049 := bstep (se 2 (by rfl) ⟨785268, by rfl⟩ : syracuseStep 2094049 = 1570537) B1570537
theorem B1307695 : Blo 1160639 1307695 := bstep (se 1 (by rfl) ⟨980771, by rfl⟩ : syracuseStep 1307695 = 1961543) B1961543
theorem B1963055 : Blo 1160639 1963055 := bstep (se 1 (by rfl) ⟨1472291, by rfl⟩ : syracuseStep 1963055 = 2944583) B2944583
theorem B3929255 : Blo 1160639 3929255 := bstep (se 1 (by rfl) ⟨2946941, by rfl⟩ : syracuseStep 3929255 = 5893883) B5893883
theorem B2619017 : Blo 1160639 2619017 := bstep (se 2 (by rfl) ⟨982131, by rfl⟩ : syracuseStep 2619017 = 1964263) B1964263
theorem B3143495 : Blo 1160639 3143495 := bstep (se 1 (by rfl) ⟨2357621, by rfl⟩ : syracuseStep 3143495 = 4715243) B4715243
theorem B1472347 : Blo 1160639 1472347 := bstep (se 1 (by rfl) ⟨1104260, by rfl⟩ : syracuseStep 1472347 = 2208521) B2208521
theorem B54392737 : Blo 1160639 54392737 := bstep (se 2 (by rfl) ⟨20397276, by rfl⟩ : syracuseStep 54392737 = 40794553) B40794553
theorem B1308667 : Blo 1160639 1308667 := bstep (se 1 (by rfl) ⟨981500, by rfl⟩ : syracuseStep 1308667 = 1963001) B1963001
theorem B1964027 : Blo 1160639 1964027 := bstep (se 1 (by rfl) ⟨1473020, by rfl⟩ : syracuseStep 1964027 = 2946041) B2946041
theorem B3537017 : Blo 1160639 3537017 := bstep (se 2 (by rfl) ⟨1326381, by rfl⟩ : syracuseStep 3537017 = 2652763) B2652763
theorem B1308847 : Blo 1160639 1308847 := bstep (se 1 (by rfl) ⟨981635, by rfl⟩ : syracuseStep 1308847 = 1963271) B1963271
theorem B6290257 : Blo 1160639 6290257 := bstep (se 2 (by rfl) ⟨2358846, by rfl⟩ : syracuseStep 6290257 = 4717693) B4717693
theorem B1310107 : Blo 1160639 1310107 := bstep (se 1 (by rfl) ⟨982580, by rfl⟩ : syracuseStep 1310107 = 1965161) B1965161
theorem B35750479 : Blo 1160639 35750479 := bstep (se 1 (by rfl) ⟨26812859, by rfl⟩ : syracuseStep 35750479 = 53625719) B53625719
theorem B2359975 : Blo 1160639 2359975 := bstep (se 1 (by rfl) ⟨1769981, by rfl⟩ : syracuseStep 2359975 = 3539963) B3539963
theorem B2098057 : Blo 1160639 2098057 := bstep (se 2 (by rfl) ⟨786771, by rfl⟩ : syracuseStep 2098057 = 1573543) B1573543
theorem B2098217 : Blo 1160639 2098217 := bstep (se 2 (by rfl) ⟨786831, by rfl⟩ : syracuseStep 2098217 = 1573663) B1573663
theorem B11175023 : Blo 1160639 11175023 := bstep (se 1 (by rfl) ⟨8381267, by rfl⟩ : syracuseStep 11175023 = 16762535) B16762535
theorem B6620687 : Blo 1160639 6620687 := bstep (se 1 (by rfl) ⟨4965515, by rfl⟩ : syracuseStep 6620687 = 9931031) B9931031
theorem B9930347 : Blo 1160639 9930347 := bstep (se 1 (by rfl) ⟨7447760, by rfl⟩ : syracuseStep 9930347 = 14895521) B14895521
theorem B120720131 : Blo 1160639 120720131 := bstep (se 1 (by rfl) ⟨90540098, by rfl⟩ : syracuseStep 120720131 = 181080197) B181080197
theorem B13241555 : Blo 1160639 13241555 := bstep (se 1 (by rfl) ⟨9931166, by rfl⟩ : syracuseStep 13241555 = 19862333) B19862333
theorem B3313487 : Blo 1160639 3313487 := bstep (se 1 (by rfl) ⟨2485115, by rfl⟩ : syracuseStep 3313487 = 4970231) B4970231
theorem B163418093 : Blo 1160639 163418093 := bstep (se 3 (by rfl) ⟨30640892, by rfl⟩ : syracuseStep 163418093 = 61281785) B61281785
theorem B1740983 : Blo 1160639 1740983 := bstep (se 1 (by rfl) ⟨1305737, by rfl⟩ : syracuseStep 1740983 = 2611475) B2611475
theorem B1741055 : Blo 1160639 1741055 := bstep (se 1 (by rfl) ⟨1305791, by rfl⟩ : syracuseStep 1741055 = 2611583) B2611583
theorem B1741103 : Blo 1160639 1741103 := bstep (se 1 (by rfl) ⟨1305827, by rfl⟩ : syracuseStep 1741103 = 2611655) B2611655
theorem B9441613 : Blo 1160639 9441613 := bstep (se 3 (by rfl) ⟨1770302, by rfl⟩ : syracuseStep 9441613 = 3540605) B3540605
theorem B1675711 : Blo 1160639 1675711 := bstep (se 1 (by rfl) ⟨1256783, by rfl⟩ : syracuseStep 1675711 = 2513567) B2513567
theorem B1741343 : Blo 1160639 1741343 := bstep (se 1 (by rfl) ⟨1306007, by rfl⟩ : syracuseStep 1741343 = 2612015) B2612015
theorem B1741403 : Blo 1160639 1741403 := bstep (se 1 (by rfl) ⟨1306052, by rfl⟩ : syracuseStep 1741403 = 2612105) B2612105
theorem B1741607 : Blo 1160639 1741607 := bstep (se 1 (by rfl) ⟨1306205, by rfl⟩ : syracuseStep 1741607 = 2612411) B2612411
theorem B1741775 : Blo 1160639 1741775 := bstep (se 1 (by rfl) ⟨1306331, by rfl⟩ : syracuseStep 1741775 = 2612663) B2612663
theorem B1741895 : Blo 1160639 1741895 := bstep (se 1 (by rfl) ⟨1306421, by rfl⟩ : syracuseStep 1741895 = 2612843) B2612843
theorem B1742075 : Blo 1160639 1742075 := bstep (se 1 (by rfl) ⟨1306556, by rfl⟩ : syracuseStep 1742075 = 2613113) B2613113
theorem B1742135 : Blo 1160639 1742135 := bstep (se 1 (by rfl) ⟨1306601, by rfl⟩ : syracuseStep 1742135 = 2613203) B2613203
theorem B1742207 : Blo 1160639 1742207 := bstep (se 1 (by rfl) ⟨1306655, by rfl⟩ : syracuseStep 1742207 = 2613311) B2613311
theorem B1742441 : Blo 1160639 1742441 := bstep (se 2 (by rfl) ⟨653415, by rfl⟩ : syracuseStep 1742441 = 1306831) B1306831
theorem B2791547 : Blo 1160639 2791547 := bstep (se 1 (by rfl) ⟨2093660, by rfl⟩ : syracuseStep 2791547 = 4187321) B4187321
theorem B1742975 : Blo 1160639 1742975 := bstep (se 1 (by rfl) ⟨1307231, by rfl⟩ : syracuseStep 1742975 = 2614463) B2614463
theorem B16751123 : Blo 1160639 16751123 := bstep (se 1 (by rfl) ⟨12563342, by rfl⟩ : syracuseStep 16751123 = 25126685) B25126685
theorem B2792065 : Blo 1160639 2792065 := bstep (se 2 (by rfl) ⟨1047024, by rfl⟩ : syracuseStep 2792065 = 2094049) B2094049
theorem B1743593 : Blo 1160639 1743593 := bstep (se 2 (by rfl) ⟨653847, by rfl⟩ : syracuseStep 1743593 = 1307695) B1307695
theorem B6363913 : Blo 1160639 6363913 := bstep (se 2 (by rfl) ⟨2386467, by rfl⟩ : syracuseStep 6363913 = 4772935) B4772935
theorem B9935783 : Blo 1160639 9935783 := bstep (se 1 (by rfl) ⟨7451837, by rfl⟩ : syracuseStep 9935783 = 14903675) B14903675
theorem B13245929 : Blo 1160639 13245929 := bstep (se 2 (by rfl) ⟨4967223, by rfl⟩ : syracuseStep 13245929 = 9934447) B9934447
theorem B25173737 : Blo 1160639 25173737 := bstep (se 2 (by rfl) ⟨9440151, by rfl⟩ : syracuseStep 25173737 = 18880303) B18880303
theorem B72523649 : Blo 1160639 72523649 := bstep (se 2 (by rfl) ⟨27196368, by rfl⟩ : syracuseStep 72523649 = 54392737) B54392737
theorem B1744889 : Blo 1160639 1744889 := bstep (se 2 (by rfl) ⟨654333, by rfl⟩ : syracuseStep 1744889 = 1308667) B1308667
theorem B1745129 : Blo 1160639 1745129 := bstep (se 2 (by rfl) ⟨654423, by rfl⟩ : syracuseStep 1745129 = 1308847) B1308847
theorem B9937181 : Blo 1160639 9937181 := bstep (se 3 (by rfl) ⟨1863221, by rfl⟩ : syracuseStep 9937181 = 3726443) B3726443
theorem B1746011 : Blo 1160639 1746011 := bstep (se 1 (by rfl) ⟨1309508, by rfl⟩ : syracuseStep 1746011 = 2619017) B2619017
theorem B1746809 : Blo 1160639 1746809 := bstep (se 2 (by rfl) ⟨655053, by rfl⟩ : syracuseStep 1746809 = 1310107) B1310107
theorem B25110587 : Blo 1160639 25110587 := bstep (se 1 (by rfl) ⟨18832940, by rfl⟩ : syracuseStep 25110587 = 37665881) B37665881
theorem B4532561 : Blo 1160639 4532561 := bstep (se 2 (by rfl) ⟨1699710, by rfl⟩ : syracuseStep 4532561 = 3399421) B3399421
theorem B5876873 : Blo 1160639 5876873 := bstep (se 2 (by rfl) ⟨2203827, by rfl⟩ : syracuseStep 5876873 = 4407655) B4407655
theorem B2207017 : Blo 1160639 2207017 := bstep (se 2 (by rfl) ⟨827631, by rfl⟩ : syracuseStep 2207017 = 1655263) B1655263
theorem B8826245 : Blo 1160639 8826245 := bstep (se 4 (by rfl) ⟨827460, by rfl⟩ : syracuseStep 8826245 = 1654921) B1654921
theorem B2207807 : Blo 1160639 2207807 := bstep (se 1 (by rfl) ⟨1655855, by rfl⟩ : syracuseStep 2207807 = 3311711) B3311711
theorem B2208475 : Blo 1160639 2208475 := bstep (se 1 (by rfl) ⟨1656356, by rfl⟩ : syracuseStep 2208475 = 3312713) B3312713
theorem B2209447 : Blo 1160639 2209447 := bstep (se 1 (by rfl) ⟨1657085, by rfl⟩ : syracuseStep 2209447 = 3314171) B3314171
theorem B1161211 : Blo 1160639 1161211 := bstep (se 1 (by rfl) ⟨870908, by rfl⟩ : syracuseStep 1161211 = 1741817) B1741817
theorem B1161343 : Blo 1160639 1161343 := bstep (se 1 (by rfl) ⟨871007, by rfl⟩ : syracuseStep 1161343 = 1742015) B1742015
theorem B1161439 : Blo 1160639 1161439 := bstep (se 1 (by rfl) ⟨871079, by rfl⟩ : syracuseStep 1161439 = 1742159) B1742159
theorem B8829161 : Blo 1160639 8829161 := bstep (se 2 (by rfl) ⟨3310935, by rfl⟩ : syracuseStep 8829161 = 6621871) B6621871
theorem B1161499 : Blo 1160639 1161499 := bstep (se 1 (by rfl) ⟨871124, by rfl⟩ : syracuseStep 1161499 = 1742249) B1742249
theorem B1161535 : Blo 1160639 1161535 := bstep (se 1 (by rfl) ⟨871151, by rfl⟩ : syracuseStep 1161535 = 1742303) B1742303
theorem B1161599 : Blo 1160639 1161599 := bstep (se 1 (by rfl) ⟨871199, by rfl⟩ : syracuseStep 1161599 = 1742399) B1742399
theorem B14891525 : Blo 1160639 14891525 := bstep (se 4 (by rfl) ⟨1396080, by rfl⟩ : syracuseStep 14891525 = 2792161) B2792161
theorem B5585591 : Blo 1160639 5585591 := bstep (se 1 (by rfl) ⟨4189193, by rfl⟩ : syracuseStep 5585591 = 8378387) B8378387
theorem B1161919 : Blo 1160639 1161919 := bstep (se 1 (by rfl) ⟨871439, by rfl⟩ : syracuseStep 1161919 = 1742879) B1742879
theorem B1162207 : Blo 1160639 1162207 := bstep (se 1 (by rfl) ⟨871655, by rfl⟩ : syracuseStep 1162207 = 1743311) B1743311
theorem B1162267 : Blo 1160639 1162267 := bstep (se 1 (by rfl) ⟨871700, by rfl⟩ : syracuseStep 1162267 = 1743401) B1743401
theorem B1162407 : Blo 1160639 1162407 := bstep (se 1 (by rfl) ⟨871805, by rfl⟩ : syracuseStep 1162407 = 1743611) B1743611
theorem B1162491 : Blo 1160639 1162491 := bstep (se 1 (by rfl) ⟨871868, by rfl⟩ : syracuseStep 1162491 = 1743737) B1743737
theorem B9944531 : Blo 1160639 9944531 := bstep (se 1 (by rfl) ⟨7458398, by rfl⟩ : syracuseStep 9944531 = 14916797) B14916797
theorem B1162991 : Blo 1160639 1162991 := bstep (se 1 (by rfl) ⟨872243, by rfl⟩ : syracuseStep 1162991 = 1744487) B1744487
theorem B1163099 : Blo 1160639 1163099 := bstep (se 1 (by rfl) ⟨872324, by rfl⟩ : syracuseStep 1163099 = 1744649) B1744649
theorem B1163247 : Blo 1160639 1163247 := bstep (se 1 (by rfl) ⟨872435, by rfl⟩ : syracuseStep 1163247 = 1744871) B1744871
theorem B1654825 : Blo 1160639 1654825 := bstep (se 2 (by rfl) ⟨620559, by rfl⟩ : syracuseStep 1654825 = 1241119) B1241119
theorem B1163327 : Blo 1160639 1163327 := bstep (se 1 (by rfl) ⟨872495, by rfl⟩ : syracuseStep 1163327 = 1744991) B1744991
theorem B1163367 : Blo 1160639 1163367 := bstep (se 1 (by rfl) ⟨872525, by rfl⟩ : syracuseStep 1163367 = 1745051) B1745051
theorem B1163423 : Blo 1160639 1163423 := bstep (se 1 (by rfl) ⟨872567, by rfl⟩ : syracuseStep 1163423 = 1745135) B1745135
theorem B1163675 : Blo 1160639 1163675 := bstep (se 1 (by rfl) ⟨872756, by rfl⟩ : syracuseStep 1163675 = 1745513) B1745513
theorem B1163679 : Blo 1160639 1163679 := bstep (se 1 (by rfl) ⟨872759, by rfl⟩ : syracuseStep 1163679 = 1745519) B1745519
theorem B1164095 : Blo 1160639 1164095 := bstep (se 1 (by rfl) ⟨873071, by rfl⟩ : syracuseStep 1164095 = 1746143) B1746143
theorem B1164255 : Blo 1160639 1164255 := bstep (se 1 (by rfl) ⟨873191, by rfl⟩ : syracuseStep 1164255 = 1746383) B1746383
theorem B1164379 : Blo 1160639 1164379 := bstep (se 1 (by rfl) ⟨873284, by rfl⟩ : syracuseStep 1164379 = 1746569) B1746569
theorem B1164415 : Blo 1160639 1164415 := bstep (se 1 (by rfl) ⟨873311, by rfl⟩ : syracuseStep 1164415 = 1746623) B1746623
theorem B1164519 : Blo 1160639 1164519 := bstep (se 1 (by rfl) ⟨873389, by rfl⟩ : syracuseStep 1164519 = 1746779) B1746779
theorem B3917537 : Blo 1160639 3917537 := bstep (se 2 (by rfl) ⟨1469076, by rfl⟩ : syracuseStep 3917537 = 2938153) B2938153
theorem B4409099 : Blo 1160639 4409099 := bstep (se 1 (by rfl) ⟨3306824, by rfl⟩ : syracuseStep 4409099 = 6613649) B6613649
theorem B3721241 : Blo 1160639 3721241 := bstep (se 2 (by rfl) ⟨1395465, by rfl⟩ : syracuseStep 3721241 = 2790931) B2790931
theorem B4409903 : Blo 1160639 4409903 := bstep (se 1 (by rfl) ⟨3307427, by rfl⟩ : syracuseStep 4409903 = 6614855) B6614855
theorem B5884487 : Blo 1160639 5884487 := bstep (se 1 (by rfl) ⟨4413365, by rfl⟩ : syracuseStep 5884487 = 8826731) B8826731
theorem B9947843 : Blo 1160639 9947843 := bstep (se 1 (by rfl) ⟨7460882, by rfl⟩ : syracuseStep 9947843 = 14921765) B14921765
theorem B13257593 : Blo 1160639 13257593 := bstep (se 2 (by rfl) ⟨4971597, by rfl⟩ : syracuseStep 13257593 = 9943195) B9943195
theorem B36293915 : Blo 1160639 36293915 := bstep (se 1 (by rfl) ⟨27220436, by rfl⟩ : syracuseStep 36293915 = 54440873) B54440873
theorem B13225517 : Blo 1160639 13225517 := bstep (se 3 (by rfl) ⟨2479784, by rfl⟩ : syracuseStep 13225517 = 4959569) B4959569
theorem B9948905 : Blo 1160639 9948905 := bstep (se 2 (by rfl) ⟨3730839, by rfl⟩ : syracuseStep 9948905 = 7461679) B7461679
theorem B20107217 : Blo 1160639 20107217 := bstep (se 2 (by rfl) ⟨7540206, by rfl⟩ : syracuseStep 20107217 = 15080413) B15080413
theorem B10604627 : Blo 1160639 10604627 := bstep (se 1 (by rfl) ⟨7953470, by rfl⟩ : syracuseStep 10604627 = 15906941) B15906941
theorem B157012111 : Blo 1160639 157012111 := bstep (se 1 (by rfl) ⟨117759083, by rfl⟩ : syracuseStep 157012111 = 235518167) B235518167
theorem B8376655 : Blo 1160639 8376655 := bstep (se 1 (by rfl) ⟨6282491, by rfl⟩ : syracuseStep 8376655 = 12564983) B12564983
theorem B5886593 : Blo 1160639 5886593 := bstep (se 2 (by rfl) ⟨2207472, by rfl⟩ : syracuseStep 5886593 = 4414945) B4414945
theorem B3920615 : Blo 1160639 3920615 := bstep (se 1 (by rfl) ⟨2940461, by rfl⟩ : syracuseStep 3920615 = 5880923) B5880923
theorem B60445709 : Blo 1160639 60445709 := bstep (se 3 (by rfl) ⟨11333570, by rfl⟩ : syracuseStep 60445709 = 22667141) B22667141
theorem B7460063 : Blo 1160639 7460063 := bstep (se 1 (by rfl) ⟨5595047, by rfl⟩ : syracuseStep 7460063 = 11190095) B11190095
theorem B33576281 : Blo 1160639 33576281 := bstep (se 2 (by rfl) ⟨12591105, by rfl⟩ : syracuseStep 33576281 = 25182211) B25182211
theorem B71685485 : Blo 1160639 71685485 := bstep (se 3 (by rfl) ⟨13441028, by rfl⟩ : syracuseStep 71685485 = 26882057) B26882057
theorem B14538761 : Blo 1160639 14538761 := bstep (se 2 (by rfl) ⟨5452035, by rfl⟩ : syracuseStep 14538761 = 10904071) B10904071
theorem B16996499 : Blo 1160639 16996499 := bstep (se 1 (by rfl) ⟨12747374, by rfl⟩ : syracuseStep 16996499 = 25494749) B25494749
theorem B8837423 : Blo 1160639 8837423 := bstep (se 1 (by rfl) ⟨6628067, by rfl⟩ : syracuseStep 8837423 = 13256135) B13256135
theorem B2611511 : Blo 1160639 2611511 := bstep (se 1 (by rfl) ⟨1958633, by rfl⟩ : syracuseStep 2611511 = 3917267) B3917267
theorem B3627391 : Blo 1160639 3627391 := bstep (se 1 (by rfl) ⟨2720543, by rfl⟩ : syracuseStep 3627391 = 5441087) B5441087
theorem B2611871 : Blo 1160639 2611871 := bstep (se 1 (by rfl) ⟨1958903, by rfl⟩ : syracuseStep 2611871 = 3917807) B3917807
theorem B1989353 : Blo 1160639 1989353 := bstep (se 2 (by rfl) ⟨746007, by rfl⟩ : syracuseStep 1989353 = 1492015) B1492015
theorem B7068779 : Blo 1160639 7068779 := bstep (se 1 (by rfl) ⟨5301584, by rfl⟩ : syracuseStep 7068779 = 10603169) B10603169
theorem B4971719 : Blo 1160639 4971719 := bstep (se 1 (by rfl) ⟨3728789, by rfl⟩ : syracuseStep 4971719 = 7457579) B7457579
theorem B3529939 : Blo 1160639 3529939 := bstep (se 1 (by rfl) ⟨2647454, by rfl⟩ : syracuseStep 3529939 = 5294909) B5294909
theorem B2481767 : Blo 1160639 2481767 := bstep (se 1 (by rfl) ⟨1861325, by rfl⟩ : syracuseStep 2481767 = 3722651) B3722651
theorem B1990639 : Blo 1160639 1990639 := bstep (se 1 (by rfl) ⟨1492979, by rfl⟩ : syracuseStep 1990639 = 2985959) B2985959
theorem B8380577 : Blo 1160639 8380577 := bstep (se 2 (by rfl) ⟨3142716, by rfl⟩ : syracuseStep 8380577 = 6285433) B6285433
theorem B8839367 : Blo 1160639 8839367 := bstep (se 1 (by rfl) ⟨6629525, by rfl⟩ : syracuseStep 8839367 = 13259051) B13259051
theorem B122347835 : Blo 1160639 122347835 := bstep (se 1 (by rfl) ⟨91760876, by rfl⟩ : syracuseStep 122347835 = 183521753) B183521753
theorem B2548265 : Blo 1160639 2548265 := bstep (se 2 (by rfl) ⟨955599, by rfl⟩ : syracuseStep 2548265 = 1911199) B1911199
theorem B2613815 : Blo 1160639 2613815 := bstep (se 1 (by rfl) ⟨1960361, by rfl⟩ : syracuseStep 2613815 = 3920723) B3920723
theorem B2613851 : Blo 1160639 2613851 := bstep (se 1 (by rfl) ⟨1960388, by rfl⟩ : syracuseStep 2613851 = 3920777) B3920777
theorem B2483065 : Blo 1160639 2483065 := bstep (se 2 (by rfl) ⟨931149, by rfl⟩ : syracuseStep 2483065 = 1862299) B1862299
theorem B2614175 : Blo 1160639 2614175 := bstep (se 1 (by rfl) ⟨1960631, by rfl⟩ : syracuseStep 2614175 = 3921263) B3921263
theorem B8840339 : Blo 1160639 8840339 := bstep (se 1 (by rfl) ⟨6630254, by rfl⟩ : syracuseStep 8840339 = 13260509) B13260509
theorem B3925367 : Blo 1160639 3925367 := bstep (se 1 (by rfl) ⟨2944025, by rfl⟩ : syracuseStep 3925367 = 5888051) B5888051
theorem B1533343 : Blo 1160639 1533343 := bstep (se 1 (by rfl) ⟨1150007, by rfl⟩ : syracuseStep 1533343 = 2300015) B2300015
theorem B2942639 : Blo 1160639 2942639 := bstep (se 1 (by rfl) ⟨2206979, by rfl⟩ : syracuseStep 2942639 = 4413959) B4413959
theorem B2516807 : Blo 1160639 2516807 := bstep (se 1 (by rfl) ⟨1887605, by rfl⟩ : syracuseStep 2516807 = 3775211) B3775211
theorem B2942831 : Blo 1160639 2942831 := bstep (se 1 (by rfl) ⟨2207123, by rfl⟩ : syracuseStep 2942831 = 4414247) B4414247
theorem B8841311 : Blo 1160639 8841311 := bstep (se 1 (by rfl) ⟨6630983, by rfl⟩ : syracuseStep 8841311 = 13261967) B13261967
theorem B8382653 : Blo 1160639 8382653 := bstep (se 3 (by rfl) ⟨1571747, by rfl⟩ : syracuseStep 8382653 = 3143495) B3143495
theorem B2943175 : Blo 1160639 2943175 := bstep (se 1 (by rfl) ⟨2207381, by rfl⟩ : syracuseStep 2943175 = 4414763) B4414763
theorem B5892425 : Blo 1160639 5892425 := bstep (se 2 (by rfl) ⟨2209659, by rfl⟩ : syracuseStep 5892425 = 4419319) B4419319
theorem B3926447 : Blo 1160639 3926447 := bstep (se 1 (by rfl) ⟨2944835, by rfl⟩ : syracuseStep 3926447 = 5889671) B5889671
theorem B5892587 : Blo 1160639 5892587 := bstep (se 1 (by rfl) ⟨4419440, by rfl⟩ : syracuseStep 5892587 = 8838881) B8838881
theorem B3926771 : Blo 1160639 3926771 := bstep (se 1 (by rfl) ⟨2945078, by rfl⟩ : syracuseStep 3926771 = 5890157) B5890157
theorem B3926825 : Blo 1160639 3926825 := bstep (se 2 (by rfl) ⟨1472559, by rfl⟩ : syracuseStep 3926825 = 2945119) B2945119
theorem B2616425 : Blo 1160639 2616425 := bstep (se 2 (by rfl) ⟨981159, by rfl⟩ : syracuseStep 2616425 = 1962319) B1962319
theorem B16772345 : Blo 1160639 16772345 := bstep (se 2 (by rfl) ⟨6289629, by rfl⟩ : syracuseStep 16772345 = 12579259) B12579259
theorem B3927527 : Blo 1160639 3927527 := bstep (se 1 (by rfl) ⟨2945645, by rfl⟩ : syracuseStep 3927527 = 5891291) B5891291
theorem B1961455 : Blo 1160639 1961455 := bstep (se 1 (by rfl) ⟨1471091, by rfl⟩ : syracuseStep 1961455 = 2942183) B2942183
theorem B1469983 : Blo 1160639 1469983 := bstep (se 1 (by rfl) ⟨1102487, by rfl⟩ : syracuseStep 1469983 = 2204975) B2204975
theorem B17887063 : Blo 1160639 17887063 := bstep (se 1 (by rfl) ⟨13415297, by rfl⟩ : syracuseStep 17887063 = 26830595) B26830595
theorem B8843255 : Blo 1160639 8843255 := bstep (se 1 (by rfl) ⟨6632441, by rfl⟩ : syracuseStep 8843255 = 13264883) B13264883
theorem B4419623 : Blo 1160639 4419623 := bstep (se 1 (by rfl) ⟨3314717, by rfl⟩ : syracuseStep 4419623 = 6629435) B6629435
theorem B1962191 : Blo 1160639 1962191 := bstep (se 1 (by rfl) ⟨1471643, by rfl⟩ : syracuseStep 1962191 = 2943287) B2943287
theorem B14872967 : Blo 1160639 14872967 := bstep (se 1 (by rfl) ⟨11154725, by rfl⟩ : syracuseStep 14872967 = 22309451) B22309451
theorem B33485399 : Blo 1160639 33485399 := bstep (se 1 (by rfl) ⟨25114049, by rfl⟩ : syracuseStep 33485399 = 50228099) B50228099
theorem B4420291 : Blo 1160639 4420291 := bstep (se 1 (by rfl) ⟨3315218, by rfl⟩ : syracuseStep 4420291 = 6630437) B6630437
theorem B17888363 : Blo 1160639 17888363 := bstep (se 1 (by rfl) ⟨13416272, by rfl⟩ : syracuseStep 17888363 = 26832545) B26832545
theorem B1963129 : Blo 1160639 1963129 := bstep (se 2 (by rfl) ⟨736173, by rfl⟩ : syracuseStep 1963129 = 1472347) B1472347
theorem B1963163 : Blo 1160639 1963163 := bstep (se 1 (by rfl) ⟨1472372, by rfl⟩ : syracuseStep 1963163 = 2944745) B2944745
theorem B1307983 : Blo 1160639 1307983 := bstep (se 1 (by rfl) ⟨980987, by rfl⟩ : syracuseStep 1307983 = 1961975) B1961975
theorem B4421051 : Blo 1160639 4421051 := bstep (se 1 (by rfl) ⟨3315788, by rfl⟩ : syracuseStep 4421051 = 6631577) B6631577
theorem B3307007 : Blo 1160639 3307007 := bstep (se 1 (by rfl) ⟨2480255, by rfl⟩ : syracuseStep 3307007 = 4960511) B4960511
theorem B1865215 : Blo 1160639 1865215 := bstep (se 1 (by rfl) ⟨1398911, by rfl⟩ : syracuseStep 1865215 = 2797823) B2797823
theorem B9926657 : Blo 1160639 9926657 := bstep (se 2 (by rfl) ⟨3722496, by rfl⟩ : syracuseStep 9926657 = 7444993) B7444993
theorem B1308703 : Blo 1160639 1308703 := bstep (se 1 (by rfl) ⟨981527, by rfl⟩ : syracuseStep 1308703 = 1963055) B1963055
theorem B2619503 : Blo 1160639 2619503 := bstep (se 1 (by rfl) ⟨1964627, by rfl⟩ : syracuseStep 2619503 = 3929255) B3929255
theorem B9927035 : Blo 1160639 9927035 := bstep (se 1 (by rfl) ⟨7445276, by rfl⟩ : syracuseStep 9927035 = 14890553) B14890553
theorem B8387009 : Blo 1160639 8387009 := bstep (se 2 (by rfl) ⟨3145128, by rfl⟩ : syracuseStep 8387009 = 6290257) B6290257
theorem B1309351 : Blo 1160639 1309351 := bstep (se 1 (by rfl) ⟨982013, by rfl⟩ : syracuseStep 1309351 = 1964027) B1964027
theorem B20151017 : Blo 1160639 20151017 := bstep (se 2 (by rfl) ⟨7556631, by rfl⟩ : syracuseStep 20151017 = 15113263) B15113263
theorem B2358011 : Blo 1160639 2358011 := bstep (se 1 (by rfl) ⟨1768508, by rfl⟩ : syracuseStep 2358011 = 3537017) B3537017
theorem B50265461 : Blo 1160639 50265461 := bstep (se 5 (by rfl) ⟨2356193, by rfl⟩ : syracuseStep 50265461 = 4712387) B4712387
theorem B3146633 : Blo 1160639 3146633 := bstep (se 2 (by rfl) ⟨1179987, by rfl⟩ : syracuseStep 3146633 = 2359975) B2359975
theorem B6620231 : Blo 1160639 6620231 := bstep (se 1 (by rfl) ⟨4965173, by rfl⟩ : syracuseStep 6620231 = 9930347) B9930347
theorem B80480087 : Blo 1160639 80480087 := bstep (se 1 (by rfl) ⟨60360065, by rfl⟩ : syracuseStep 80480087 = 120720131) B120720131
theorem B8817011 : Blo 1160639 8817011 := bstep (se 1 (by rfl) ⟨6612758, by rfl⟩ : syracuseStep 8817011 = 13225517) B13225517
theorem B13404811 : Blo 1160639 13404811 := bstep (se 1 (by rfl) ⟨10053608, by rfl⟩ : syracuseStep 13404811 = 20107217) B20107217
theorem B22384187 : Blo 1160639 22384187 := bstep (se 1 (by rfl) ⟨16788140, by rfl⟩ : syracuseStep 22384187 = 33576281) B33576281
theorem B1741007 : Blo 1160639 1741007 := bstep (se 1 (by rfl) ⟨1305755, by rfl⟩ : syracuseStep 1741007 = 2611511) B2611511
theorem B1741247 : Blo 1160639 1741247 := bstep (se 1 (by rfl) ⟨1305935, by rfl⟩ : syracuseStep 1741247 = 2611871) B2611871
theorem B6623855 : Blo 1160639 6623855 := bstep (se 1 (by rfl) ⟨4967891, by rfl⟩ : syracuseStep 6623855 = 9935783) B9935783
theorem B13243013 : Blo 1160639 13243013 := bstep (se 4 (by rfl) ⟨1241532, by rfl⟩ : syracuseStep 13243013 = 2483065) B2483065
theorem B3314479 : Blo 1160639 3314479 := bstep (se 1 (by rfl) ⟨2485859, by rfl⟩ : syracuseStep 3314479 = 4971719) B4971719
theorem B16782491 : Blo 1160639 16782491 := bstep (se 1 (by rfl) ⟨12586868, by rfl⟩ : syracuseStep 16782491 = 25173737) B25173737
theorem B6624787 : Blo 1160639 6624787 := bstep (se 1 (by rfl) ⟨4968590, by rfl⟩ : syracuseStep 6624787 = 9937181) B9937181
theorem B81565223 : Blo 1160639 81565223 := bstep (se 1 (by rfl) ⟨61173917, by rfl⟩ : syracuseStep 81565223 = 122347835) B122347835
theorem B1742543 : Blo 1160639 1742543 := bstep (se 1 (by rfl) ⟨1306907, by rfl⟩ : syracuseStep 1742543 = 2613815) B2613815
theorem B1742567 : Blo 1160639 1742567 := bstep (se 1 (by rfl) ⟨1306925, by rfl⟩ : syracuseStep 1742567 = 2613851) B2613851
theorem B12588817 : Blo 1160639 12588817 := bstep (se 2 (by rfl) ⟨4720806, by rfl⟩ : syracuseStep 12588817 = 9441613) B9441613
theorem B1742783 : Blo 1160639 1742783 := bstep (se 1 (by rfl) ⟨1307087, by rfl⟩ : syracuseStep 1742783 = 2614175) B2614175
theorem B1677871 : Blo 1160639 1677871 := bstep (se 1 (by rfl) ⟨1258403, by rfl⟩ : syracuseStep 1677871 = 2516807) B2516807
theorem B3021707 : Blo 1160639 3021707 := bstep (se 1 (by rfl) ⟨2266280, by rfl⟩ : syracuseStep 3021707 = 4532561) B4532561
theorem B1743977 : Blo 1160639 1743977 := bstep (se 2 (by rfl) ⟨653991, by rfl⟩ : syracuseStep 1743977 = 1307983) B1307983
theorem B1744283 : Blo 1160639 1744283 := bstep (se 1 (by rfl) ⟨1308212, by rfl⟩ : syracuseStep 1744283 = 2616425) B2616425
theorem B11181563 : Blo 1160639 11181563 := bstep (se 1 (by rfl) ⟨8386172, by rfl⟩ : syracuseStep 11181563 = 16772345) B16772345
theorem B1744937 : Blo 1160639 1744937 := bstep (se 2 (by rfl) ⟨654351, by rfl⟩ : syracuseStep 1744937 = 1308703) B1308703
theorem B22323599 : Blo 1160639 22323599 := bstep (se 1 (by rfl) ⟨16742699, by rfl⟩ : syracuseStep 22323599 = 33485399) B33485399
theorem B1745801 : Blo 1160639 1745801 := bstep (se 2 (by rfl) ⟨654675, by rfl⟩ : syracuseStep 1745801 = 1309351) B1309351
theorem B2204671 : Blo 1160639 2204671 := bstep (se 1 (by rfl) ⟨1653503, by rfl⟩ : syracuseStep 2204671 = 3307007) B3307007
theorem B1746335 : Blo 1160639 1746335 := bstep (se 1 (by rfl) ⟨1309751, by rfl⟩ : syracuseStep 1746335 = 2619503) B2619503
theorem B6629687 : Blo 1160639 6629687 := bstep (se 1 (by rfl) ⟨4972265, by rfl⟩ : syracuseStep 6629687 = 9944531) B9944531
theorem B2206433 : Blo 1160639 2206433 := bstep (se 2 (by rfl) ⟨827412, by rfl⟩ : syracuseStep 2206433 = 1654825) B1654825
theorem B837397925 : Blo 1160639 837397925 := bstep (se 4 (by rfl) ⟨78506055, by rfl⟩ : syracuseStep 837397925 = 157012111) B157012111
theorem B2797409 : Blo 1160639 2797409 := bstep (se 2 (by rfl) ⟨1049028, by rfl⟩ : syracuseStep 2797409 = 2098057) B2098057
theorem B6631895 : Blo 1160639 6631895 := bstep (se 1 (by rfl) ⟨4973921, by rfl⟩ : syracuseStep 6631895 = 9947843) B9947843
theorem B2044457 : Blo 1160639 2044457 := bstep (se 2 (by rfl) ⟨766671, by rfl⟩ : syracuseStep 2044457 = 1533343) B1533343
theorem B8827703 : Blo 1160639 8827703 := bstep (se 1 (by rfl) ⟨6620777, by rfl⟩ : syracuseStep 8827703 = 13241555) B13241555
theorem B24195943 : Blo 1160639 24195943 := bstep (se 1 (by rfl) ⟨18146957, by rfl⟩ : syracuseStep 24195943 = 36293915) B36293915
theorem B6632603 : Blo 1160639 6632603 := bstep (se 1 (by rfl) ⟨4974452, by rfl⟩ : syracuseStep 6632603 = 9948905) B9948905
theorem B1160655 : Blo 1160639 1160655 := bstep (se 1 (by rfl) ⟨870491, by rfl⟩ : syracuseStep 1160655 = 1740983) B1740983
theorem B1160703 : Blo 1160639 1160703 := bstep (se 1 (by rfl) ⟨870527, by rfl⟩ : syracuseStep 1160703 = 1741055) B1741055
theorem B1160735 : Blo 1160639 1160735 := bstep (se 1 (by rfl) ⟨870551, by rfl⟩ : syracuseStep 1160735 = 1741103) B1741103
theorem B29800061 : Blo 1160639 29800061 := bstep (se 3 (by rfl) ⟨5587511, by rfl⟩ : syracuseStep 29800061 = 11175023) B11175023
theorem B1160895 : Blo 1160639 1160895 := bstep (se 1 (by rfl) ⟨870671, by rfl⟩ : syracuseStep 1160895 = 1741343) B1741343
theorem B1160935 : Blo 1160639 1160935 := bstep (se 1 (by rfl) ⟨870701, by rfl⟩ : syracuseStep 1160935 = 1741403) B1741403
theorem B1161071 : Blo 1160639 1161071 := bstep (se 1 (by rfl) ⟨870803, by rfl⟩ : syracuseStep 1161071 = 1741607) B1741607
theorem B1161183 : Blo 1160639 1161183 := bstep (se 1 (by rfl) ⟨870887, by rfl⟩ : syracuseStep 1161183 = 1741775) B1741775
theorem B1161263 : Blo 1160639 1161263 := bstep (se 1 (by rfl) ⟨870947, by rfl⟩ : syracuseStep 1161263 = 1741895) B1741895
theorem B1161383 : Blo 1160639 1161383 := bstep (se 1 (by rfl) ⟨871037, by rfl⟩ : syracuseStep 1161383 = 1742075) B1742075
theorem B1161423 : Blo 1160639 1161423 := bstep (se 1 (by rfl) ⟨871067, by rfl⟩ : syracuseStep 1161423 = 1742135) B1742135
theorem B47790323 : Blo 1160639 47790323 := bstep (se 1 (by rfl) ⟨35842742, by rfl⟩ : syracuseStep 47790323 = 71685485) B71685485
theorem B1161471 : Blo 1160639 1161471 := bstep (se 1 (by rfl) ⟨871103, by rfl⟩ : syracuseStep 1161471 = 1742207) B1742207
theorem B1161627 : Blo 1160639 1161627 := bstep (se 1 (by rfl) ⟨871220, by rfl⟩ : syracuseStep 1161627 = 1742441) B1742441
theorem B1161983 : Blo 1160639 1161983 := bstep (se 1 (by rfl) ⟨871487, by rfl⟩ : syracuseStep 1161983 = 1742975) B1742975
theorem B1162395 : Blo 1160639 1162395 := bstep (se 1 (by rfl) ⟨871796, by rfl⟩ : syracuseStep 1162395 = 1743593) B1743593
theorem B1326235 : Blo 1160639 1326235 := bstep (se 1 (by rfl) ⟨994676, by rfl⟩ : syracuseStep 1326235 = 1989353) B1989353
theorem B8830619 : Blo 1160639 8830619 := bstep (se 1 (by rfl) ⟨6622964, by rfl⟩ : syracuseStep 8830619 = 13245929) B13245929
theorem B1654511 : Blo 1160639 1654511 := bstep (se 1 (by rfl) ⟨1240883, by rfl⟩ : syracuseStep 1654511 = 2481767) B2481767
theorem B48349099 : Blo 1160639 48349099 := bstep (se 1 (by rfl) ⟨36261824, by rfl⟩ : syracuseStep 48349099 = 72523649) B72523649
theorem B1163259 : Blo 1160639 1163259 := bstep (se 1 (by rfl) ⟨872444, by rfl⟩ : syracuseStep 1163259 = 1744889) B1744889
theorem B5587051 : Blo 1160639 5587051 := bstep (se 1 (by rfl) ⟨4190288, by rfl⟩ : syracuseStep 5587051 = 8380577) B8380577
theorem B1163419 : Blo 1160639 1163419 := bstep (se 1 (by rfl) ⟨872564, by rfl⟩ : syracuseStep 1163419 = 1745129) B1745129
theorem B66961565 : Blo 1160639 66961565 := bstep (se 3 (by rfl) ⟨12555293, by rfl⟩ : syracuseStep 66961565 = 25110587) B25110587
theorem B27181493 : Blo 1160639 27181493 := bstep (se 5 (by rfl) ⟨1274132, by rfl⟩ : syracuseStep 27181493 = 2548265) B2548265
theorem B1164007 : Blo 1160639 1164007 := bstep (se 1 (by rfl) ⟨873005, by rfl⟩ : syracuseStep 1164007 = 1746011) B1746011
theorem B1164539 : Blo 1160639 1164539 := bstep (se 1 (by rfl) ⟨873404, by rfl⟩ : syracuseStep 1164539 = 1746809) B1746809
theorem B5588435 : Blo 1160639 5588435 := bstep (se 1 (by rfl) ⟨4191326, by rfl⟩ : syracuseStep 5588435 = 8382653) B8382653
theorem B3917915 : Blo 1160639 3917915 := bstep (se 1 (by rfl) ⟨2938436, by rfl⟩ : syracuseStep 3917915 = 5876873) B5876873
theorem B5884163 : Blo 1160639 5884163 := bstep (se 1 (by rfl) ⟨4413122, by rfl⟩ : syracuseStep 5884163 = 8826245) B8826245
theorem B9915311 : Blo 1160639 9915311 := bstep (se 1 (by rfl) ⟨7436483, by rfl⟩ : syracuseStep 9915311 = 14872967) B14872967
theorem B4836521 : Blo 1160639 4836521 := bstep (se 2 (by rfl) ⟨1813695, by rfl⟩ : syracuseStep 4836521 = 3627391) B3627391
theorem B3722753 : Blo 1160639 3722753 := bstep (se 2 (by rfl) ⟨1396032, by rfl⟩ : syracuseStep 3722753 = 2792065) B2792065
theorem B5886107 : Blo 1160639 5886107 := bstep (se 1 (by rfl) ⟨4414580, by rfl⟩ : syracuseStep 5886107 = 8829161) B8829161
theorem B4706585 : Blo 1160639 4706585 := bstep (se 2 (by rfl) ⟨1764969, by rfl⟩ : syracuseStep 4706585 = 3529939) B3529939
theorem B5591339 : Blo 1160639 5591339 := bstep (se 1 (by rfl) ⟨4193504, by rfl⟩ : syracuseStep 5591339 = 8387009) B8387009
theorem B3723727 : Blo 1160639 3723727 := bstep (se 1 (by rfl) ⟨2792795, by rfl⟩ : syracuseStep 3723727 = 5585591) B5585591
theorem B8835965 : Blo 1160639 8835965 := bstep (se 3 (by rfl) ⟨1656743, by rfl⟩ : syracuseStep 8835965 = 3313487) B3313487
theorem B33510307 : Blo 1160639 33510307 := bstep (se 1 (by rfl) ⟨25132730, by rfl⟩ : syracuseStep 33510307 = 50265461) B50265461
theorem B1398811 : Blo 1160639 1398811 := bstep (se 1 (by rfl) ⟨1049108, by rfl⟩ : syracuseStep 1398811 = 2098217) B2098217
theorem B47667305 : Blo 1160639 47667305 := bstep (se 2 (by rfl) ⟨17875239, by rfl⟩ : syracuseStep 47667305 = 35750479) B35750479
theorem B4413791 : Blo 1160639 4413791 := bstep (se 1 (by rfl) ⟨3310343, by rfl⟩ : syracuseStep 4413791 = 6620687) B6620687
theorem B2611691 : Blo 1160639 2611691 := bstep (se 1 (by rfl) ⟨1958768, by rfl⟩ : syracuseStep 2611691 = 3917537) B3917537
theorem B2939399 : Blo 1160639 2939399 := bstep (se 1 (by rfl) ⟨2204549, by rfl⟩ : syracuseStep 2939399 = 4409099) B4409099
theorem B2939935 : Blo 1160639 2939935 := bstep (se 1 (by rfl) ⟨2204951, by rfl⟩ : syracuseStep 2939935 = 4409903) B4409903
theorem B3922991 : Blo 1160639 3922991 := bstep (se 1 (by rfl) ⟨2942243, by rfl⟩ : syracuseStep 3922991 = 5884487) B5884487
theorem B8838395 : Blo 1160639 8838395 := bstep (se 1 (by rfl) ⟨6628796, by rfl⟩ : syracuseStep 8838395 = 13257593) B13257593
theorem B8937125 : Blo 1160639 8937125 := bstep (se 4 (by rfl) ⟨837855, by rfl⟩ : syracuseStep 8937125 = 1675711) B1675711
theorem B108945395 : Blo 1160639 108945395 := bstep (se 1 (by rfl) ⟨81709046, by rfl⟩ : syracuseStep 108945395 = 163418093) B163418093
theorem B7069751 : Blo 1160639 7069751 := bstep (se 1 (by rfl) ⟨5302313, by rfl⟩ : syracuseStep 7069751 = 10604627) B10604627
theorem B3924233 : Blo 1160639 3924233 := bstep (se 2 (by rfl) ⟨1471587, by rfl⟩ : syracuseStep 3924233 = 2943175) B2943175
theorem B3924395 : Blo 1160639 3924395 := bstep (se 1 (by rfl) ⟨2943296, by rfl⟩ : syracuseStep 3924395 = 5886593) B5886593
theorem B2613743 : Blo 1160639 2613743 := bstep (se 1 (by rfl) ⟨1960307, by rfl⟩ : syracuseStep 2613743 = 3920615) B3920615
theorem B40297139 : Blo 1160639 40297139 := bstep (se 1 (by rfl) ⟨30222854, by rfl⟩ : syracuseStep 40297139 = 60445709) B60445709
theorem B4973375 : Blo 1160639 4973375 := bstep (se 1 (by rfl) ⟨3730031, by rfl⟩ : syracuseStep 4973375 = 7460063) B7460063
theorem B9692507 : Blo 1160639 9692507 := bstep (se 1 (by rfl) ⟨7269380, by rfl⟩ : syracuseStep 9692507 = 14538761) B14538761
theorem B1861031 : Blo 1160639 1861031 := bstep (se 1 (by rfl) ⟨1395773, by rfl⟩ : syracuseStep 1861031 = 2791547) B2791547
theorem B11330999 : Blo 1160639 11330999 := bstep (se 1 (by rfl) ⟨8498249, by rfl⟩ : syracuseStep 11330999 = 16996499) B16996499
theorem B5891615 : Blo 1160639 5891615 := bstep (se 1 (by rfl) ⟨4418711, by rfl⟩ : syracuseStep 5891615 = 8837423) B8837423
theorem B11167415 : Blo 1160639 11167415 := bstep (se 1 (by rfl) ⟨8375561, by rfl⟩ : syracuseStep 11167415 = 16751123) B16751123
theorem B2942689 : Blo 1160639 2942689 := bstep (se 2 (by rfl) ⟨1103508, by rfl⟩ : syracuseStep 2942689 = 2207017) B2207017
theorem B2615273 : Blo 1160639 2615273 := bstep (se 2 (by rfl) ⟨980727, by rfl⟩ : syracuseStep 2615273 = 1961455) B1961455
theorem B1959977 : Blo 1160639 1959977 := bstep (se 2 (by rfl) ⟨734991, by rfl⟩ : syracuseStep 1959977 = 1469983) B1469983
theorem B4712519 : Blo 1160639 4712519 := bstep (se 1 (by rfl) ⟨3534389, by rfl⟩ : syracuseStep 4712519 = 7068779) B7068779
theorem B23849417 : Blo 1160639 23849417 := bstep (se 2 (by rfl) ⟨8943531, by rfl⟩ : syracuseStep 23849417 = 17887063) B17887063
theorem B9923309 : Blo 1160639 9923309 := bstep (se 3 (by rfl) ⟨1860620, by rfl⟩ : syracuseStep 9923309 = 3721241) B3721241
theorem B5892911 : Blo 1160639 5892911 := bstep (se 1 (by rfl) ⟨4419683, by rfl⟩ : syracuseStep 5892911 = 8839367) B8839367
theorem B11168873 : Blo 1160639 11168873 := bstep (se 2 (by rfl) ⟨4188327, by rfl⟩ : syracuseStep 11168873 = 8376655) B8376655
theorem B5893559 : Blo 1160639 5893559 := bstep (se 1 (by rfl) ⟨4420169, by rfl⟩ : syracuseStep 5893559 = 8840339) B8840339
theorem B2616911 : Blo 1160639 2616911 := bstep (se 1 (by rfl) ⟨1962683, by rfl⟩ : syracuseStep 2616911 = 3925367) B3925367
theorem B5893721 : Blo 1160639 5893721 := bstep (se 2 (by rfl) ⟨2210145, by rfl⟩ : syracuseStep 5893721 = 4420291) B4420291
theorem B2944633 : Blo 1160639 2944633 := bstep (se 2 (by rfl) ⟨1104237, by rfl⟩ : syracuseStep 2944633 = 2208475) B2208475
theorem B1961759 : Blo 1160639 1961759 := bstep (se 1 (by rfl) ⟨1471319, by rfl⟩ : syracuseStep 1961759 = 2942639) B2942639
theorem B1961887 : Blo 1160639 1961887 := bstep (se 1 (by rfl) ⟨1471415, by rfl⟩ : syracuseStep 1961887 = 2942831) B2942831
theorem B5894207 : Blo 1160639 5894207 := bstep (se 1 (by rfl) ⟨4420655, by rfl⟩ : syracuseStep 5894207 = 8841311) B8841311
theorem B2617505 : Blo 1160639 2617505 := bstep (se 2 (by rfl) ⟨981564, by rfl⟩ : syracuseStep 2617505 = 1963129) B1963129
theorem B3928283 : Blo 1160639 3928283 := bstep (se 1 (by rfl) ⟨2946212, by rfl⟩ : syracuseStep 3928283 = 5892425) B5892425
theorem B2617631 : Blo 1160639 2617631 := bstep (se 1 (by rfl) ⟨1963223, by rfl⟩ : syracuseStep 2617631 = 3926447) B3926447
theorem B3928391 : Blo 1160639 3928391 := bstep (se 1 (by rfl) ⟨2946293, by rfl⟩ : syracuseStep 3928391 = 5892587) B5892587
theorem B2617847 : Blo 1160639 2617847 := bstep (se 1 (by rfl) ⟨1963385, by rfl⟩ : syracuseStep 2617847 = 3926771) B3926771
theorem B2617883 : Blo 1160639 2617883 := bstep (se 1 (by rfl) ⟨1963412, by rfl⟩ : syracuseStep 2617883 = 3926825) B3926825
theorem B6288029 : Blo 1160639 6288029 := bstep (se 3 (by rfl) ⟨1179005, by rfl⟩ : syracuseStep 6288029 = 2358011) B2358011
theorem B2486953 : Blo 1160639 2486953 := bstep (se 2 (by rfl) ⟨932607, by rfl⟩ : syracuseStep 2486953 = 1865215) B1865215
theorem B2945929 : Blo 1160639 2945929 := bstep (se 2 (by rfl) ⟨1104723, by rfl⟩ : syracuseStep 2945929 = 2209447) B2209447
theorem B2618351 : Blo 1160639 2618351 := bstep (se 1 (by rfl) ⟨1963763, by rfl⟩ : syracuseStep 2618351 = 3927527) B3927527
theorem B5895503 : Blo 1160639 5895503 := bstep (se 1 (by rfl) ⟨4421627, by rfl⟩ : syracuseStep 5895503 = 8843255) B8843255
theorem B2946415 : Blo 1160639 2946415 := bstep (se 1 (by rfl) ⟨2209811, by rfl⟩ : syracuseStep 2946415 = 4419623) B4419623
theorem B1471871 : Blo 1160639 1471871 := bstep (se 1 (by rfl) ⟨1103903, by rfl⟩ : syracuseStep 1471871 = 2207807) B2207807
theorem B1308127 : Blo 1160639 1308127 := bstep (se 1 (by rfl) ⟨981095, by rfl⟩ : syracuseStep 1308127 = 1962191) B1962191
theorem B11925575 : Blo 1160639 11925575 := bstep (se 1 (by rfl) ⟨8944181, by rfl⟩ : syracuseStep 11925575 = 17888363) B17888363
theorem B1308775 : Blo 1160639 1308775 := bstep (se 1 (by rfl) ⟨981581, by rfl⟩ : syracuseStep 1308775 = 1963163) B1963163
theorem B2947367 : Blo 1160639 2947367 := bstep (se 1 (by rfl) ⟨2210525, by rfl⟩ : syracuseStep 2947367 = 4421051) B4421051
theorem B8485217 : Blo 1160639 8485217 := bstep (se 2 (by rfl) ⟨3181956, by rfl⟩ : syracuseStep 8485217 = 6363913) B6363913
theorem B6617771 : Blo 1160639 6617771 := bstep (se 1 (by rfl) ⟨4963328, by rfl⟩ : syracuseStep 6617771 = 9926657) B9926657
theorem B6618023 : Blo 1160639 6618023 := bstep (se 1 (by rfl) ⟨4963517, by rfl⟩ : syracuseStep 6618023 = 9927035) B9927035
theorem B9927683 : Blo 1160639 9927683 := bstep (se 1 (by rfl) ⟨7445762, by rfl⟩ : syracuseStep 9927683 = 14891525) B14891525
theorem B13434011 : Blo 1160639 13434011 := bstep (se 1 (by rfl) ⟨10075508, by rfl⟩ : syracuseStep 13434011 = 20151017) B20151017
theorem B10616741 : Blo 1160639 10616741 := bstep (se 4 (by rfl) ⟨995319, by rfl⟩ : syracuseStep 10616741 = 1990639) B1990639
theorem B18120995 : Blo 1160639 18120995 := bstep (se 1 (by rfl) ⟨13590746, by rfl⟩ : syracuseStep 18120995 = 27181493) B27181493
theorem B2097755 : Blo 1160639 2097755 := bstep (se 1 (by rfl) ⟨1573316, by rfl⟩ : syracuseStep 2097755 = 3146633) B3146633
theorem B1741127 : Blo 1160639 1741127 := bstep (se 1 (by rfl) ⟨1305845, by rfl⟩ : syracuseStep 1741127 = 2611691) B2611691
theorem B14882399 : Blo 1160639 14882399 := bstep (se 1 (by rfl) ⟨11161799, by rfl⟩ : syracuseStep 14882399 = 22323599) B22323599
theorem B1742495 : Blo 1160639 1742495 := bstep (se 1 (by rfl) ⟨1306871, by rfl⟩ : syracuseStep 1742495 = 2613743) B2613743
theorem B870029045 : Blo 1160639 870029045 := bstep (se 5 (by rfl) ⟨40782611, by rfl⟩ : syracuseStep 870029045 = 81565223) B81565223
theorem B3315583 : Blo 1160639 3315583 := bstep (se 1 (by rfl) ⟨2486687, by rfl⟩ : syracuseStep 3315583 = 4973375) B4973375
theorem B3315937 : Blo 1160639 3315937 := bstep (se 2 (by rfl) ⟨1243476, by rfl⟩ : syracuseStep 3315937 = 2486953) B2486953
theorem B7444943 : Blo 1160639 7444943 := bstep (se 1 (by rfl) ⟨5583707, by rfl⟩ : syracuseStep 7444943 = 11167415) B11167415
theorem B1743515 : Blo 1160639 1743515 := bstep (se 1 (by rfl) ⟨1307636, by rfl⟩ : syracuseStep 1743515 = 2615273) B2615273
theorem B15899611 : Blo 1160639 15899611 := bstep (se 1 (by rfl) ⟨11924708, by rfl⟩ : syracuseStep 15899611 = 23849417) B23849417
theorem B1744169 : Blo 1160639 1744169 := bstep (se 2 (by rfl) ⟨654063, by rfl⟩ : syracuseStep 1744169 = 1308127) B1308127
theorem B7445915 : Blo 1160639 7445915 := bstep (se 1 (by rfl) ⟨5584436, by rfl⟩ : syracuseStep 7445915 = 11168873) B11168873
theorem B16785089 : Blo 1160639 16785089 := bstep (se 2 (by rfl) ⟨6294408, by rfl⟩ : syracuseStep 16785089 = 12588817) B12588817
theorem B1744607 : Blo 1160639 1744607 := bstep (se 1 (by rfl) ⟨1308455, by rfl⟩ : syracuseStep 1744607 = 2616911) B2616911
theorem B1745003 : Blo 1160639 1745003 := bstep (se 1 (by rfl) ⟨1308752, by rfl⟩ : syracuseStep 1745003 = 2617505) B2617505
theorem B1745033 : Blo 1160639 1745033 := bstep (se 2 (by rfl) ⟨654387, by rfl⟩ : syracuseStep 1745033 = 1308775) B1308775
theorem B1745087 : Blo 1160639 1745087 := bstep (se 1 (by rfl) ⟨1308815, by rfl⟩ : syracuseStep 1745087 = 2617631) B2617631
theorem B1745231 : Blo 1160639 1745231 := bstep (se 1 (by rfl) ⟨1308923, by rfl⟩ : syracuseStep 1745231 = 2617847) B2617847
theorem B1745255 : Blo 1160639 1745255 := bstep (se 1 (by rfl) ⟨1308941, by rfl⟩ : syracuseStep 1745255 = 2617883) B2617883
theorem B1745567 : Blo 1160639 1745567 := bstep (se 1 (by rfl) ⟨1309175, by rfl⟩ : syracuseStep 1745567 = 2618351) B2618351
theorem B2237161 : Blo 1160639 2237161 := bstep (se 2 (by rfl) ⟨838935, by rfl⟩ : syracuseStep 2237161 = 1677871) B1677871
theorem B19866707 : Blo 1160639 19866707 := bstep (se 1 (by rfl) ⟨14900030, by rfl⟩ : syracuseStep 19866707 = 29800061) B29800061
theorem B31860215 : Blo 1160639 31860215 := bstep (se 1 (by rfl) ⟨23895161, by rfl⟩ : syracuseStep 31860215 = 47790323) B47790323
theorem B8956007 : Blo 1160639 8956007 := bstep (se 1 (by rfl) ⟨6717005, by rfl⟩ : syracuseStep 8956007 = 13434011) B13434011
theorem B64465465 : Blo 1160639 64465465 := bstep (se 2 (by rfl) ⟨24174549, by rfl⟩ : syracuseStep 64465465 = 48349099) B48349099
theorem B44641043 : Blo 1160639 44641043 := bstep (se 1 (by rfl) ⟨33480782, by rfl⟩ : syracuseStep 44641043 = 66961565) B66961565
theorem B7449401 : Blo 1160639 7449401 := bstep (se 2 (by rfl) ⟨2793525, by rfl⟩ : syracuseStep 7449401 = 5587051) B5587051
theorem B53653391 : Blo 1160639 53653391 := bstep (se 1 (by rfl) ⟨40240043, by rfl⟩ : syracuseStep 53653391 = 80480087) B80480087
theorem B5878007 : Blo 1160639 5878007 := bstep (se 1 (by rfl) ⟨4408505, by rfl⟩ : syracuseStep 5878007 = 8817011) B8817011
theorem B14922791 : Blo 1160639 14922791 := bstep (se 1 (by rfl) ⟨11192093, by rfl⟩ : syracuseStep 14922791 = 22384187) B22384187
theorem B1160671 : Blo 1160639 1160671 := bstep (se 1 (by rfl) ⟨870503, by rfl⟩ : syracuseStep 1160671 = 1741007) B1741007
theorem B1160831 : Blo 1160639 1160831 := bstep (se 1 (by rfl) ⟨870623, by rfl⟩ : syracuseStep 1160831 = 1741247) B1741247
theorem B8828675 : Blo 1160639 8828675 := bstep (se 1 (by rfl) ⟨6621506, by rfl⟩ : syracuseStep 8828675 = 13243013) B13243013
theorem B11188327 : Blo 1160639 11188327 := bstep (se 1 (by rfl) ⟨8391245, by rfl⟩ : syracuseStep 11188327 = 16782491) B16782491
theorem B17873081 : Blo 1160639 17873081 := bstep (se 2 (by rfl) ⟨6702405, by rfl⟩ : syracuseStep 17873081 = 13404811) B13404811
theorem B1161695 : Blo 1160639 1161695 := bstep (se 1 (by rfl) ⟨871271, by rfl⟩ : syracuseStep 1161695 = 1742543) B1742543
theorem B1161711 : Blo 1160639 1161711 := bstep (se 1 (by rfl) ⟨871283, by rfl⟩ : syracuseStep 1161711 = 1742567) B1742567
theorem B1161855 : Blo 1160639 1161855 := bstep (se 1 (by rfl) ⟨871391, by rfl⟩ : syracuseStep 1161855 = 1742783) B1742783
theorem B2014471 : Blo 1160639 2014471 := bstep (se 1 (by rfl) ⟨1510853, by rfl⟩ : syracuseStep 2014471 = 3021707) B3021707
theorem B1162651 : Blo 1160639 1162651 := bstep (se 1 (by rfl) ⟨871988, by rfl⟩ : syracuseStep 1162651 = 1743977) B1743977
theorem B1162855 : Blo 1160639 1162855 := bstep (se 1 (by rfl) ⟨872141, by rfl⟩ : syracuseStep 1162855 = 1744283) B1744283
theorem B7454375 : Blo 1160639 7454375 := bstep (se 1 (by rfl) ⟨5590781, by rfl⟩ : syracuseStep 7454375 = 11181563) B11181563
theorem B72630263 : Blo 1160639 72630263 := bstep (se 1 (by rfl) ⟨54472697, by rfl⟩ : syracuseStep 72630263 = 108945395) B108945395
theorem B1163291 : Blo 1160639 1163291 := bstep (se 1 (by rfl) ⟨872468, by rfl⟩ : syracuseStep 1163291 = 1744937) B1744937
theorem B1163867 : Blo 1160639 1163867 := bstep (se 1 (by rfl) ⟨872900, by rfl⟩ : syracuseStep 1163867 = 1745801) B1745801
theorem B4964969 : Blo 1160639 4964969 := bstep (se 2 (by rfl) ⟨1861863, by rfl⟩ : syracuseStep 4964969 = 3723727) B3723727
theorem B1164223 : Blo 1160639 1164223 := bstep (se 1 (by rfl) ⟨873167, by rfl⟩ : syracuseStep 1164223 = 1746335) B1746335
theorem B7553999 : Blo 1160639 7553999 := bstep (se 1 (by rfl) ⟨5665499, by rfl⟩ : syracuseStep 7553999 = 11330999) B11330999
theorem B32261257 : Blo 1160639 32261257 := bstep (se 2 (by rfl) ⟨12097971, by rfl⟩ : syracuseStep 32261257 = 24195943) B24195943
theorem B44680409 : Blo 1160639 44680409 := bstep (se 2 (by rfl) ⟨16755153, by rfl⟩ : syracuseStep 44680409 = 33510307) B33510307
theorem B8833049 : Blo 1160639 8833049 := bstep (se 2 (by rfl) ⟨3312393, by rfl⟩ : syracuseStep 8833049 = 6624787) B6624787
theorem B1362971 : Blo 1160639 1362971 := bstep (se 1 (by rfl) ⟨1022228, by rfl⟩ : syracuseStep 1362971 = 2044457) B2044457
theorem B12897389 : Blo 1160639 12897389 := bstep (se 3 (by rfl) ⟨2418260, by rfl⟩ : syracuseStep 12897389 = 4836521) B4836521
theorem B5885135 : Blo 1160639 5885135 := bstep (se 1 (by rfl) ⟨4413851, by rfl⟩ : syracuseStep 5885135 = 8827703) B8827703
theorem B3919913 : Blo 1160639 3919913 := bstep (se 2 (by rfl) ⟨1469967, by rfl⟩ : syracuseStep 3919913 = 2939935) B2939935
theorem B7950383 : Blo 1160639 7950383 := bstep (se 1 (by rfl) ⟨5962787, by rfl⟩ : syracuseStep 7950383 = 11925575) B11925575
theorem B5656811 : Blo 1160639 5656811 := bstep (se 1 (by rfl) ⟨4242608, by rfl⟩ : syracuseStep 5656811 = 8485217) B8485217
theorem B4411847 : Blo 1160639 4411847 := bstep (se 1 (by rfl) ⟨3308885, by rfl⟩ : syracuseStep 4411847 = 6617771) B6617771
theorem B4412015 : Blo 1160639 4412015 := bstep (se 1 (by rfl) ⟨3309011, by rfl⟩ : syracuseStep 4412015 = 6618023) B6618023
theorem B4412029 : Blo 1160639 4412029 := bstep (se 3 (by rfl) ⟨827255, by rfl⟩ : syracuseStep 4412029 = 1654511) B1654511
theorem B5887079 : Blo 1160639 5887079 := bstep (se 1 (by rfl) ⟨4415309, by rfl⟩ : syracuseStep 5887079 = 8830619) B8830619
theorem B4413487 : Blo 1160639 4413487 := bstep (se 1 (by rfl) ⟨3310115, by rfl⟩ : syracuseStep 4413487 = 6620231) B6620231
theorem B3725623 : Blo 1160639 3725623 := bstep (se 1 (by rfl) ⟨2794217, by rfl⟩ : syracuseStep 3725623 = 5588435) B5588435
theorem B2939561 : Blo 1160639 2939561 := bstep (se 2 (by rfl) ⟨1102335, by rfl⟩ : syracuseStep 2939561 = 2204671) B2204671
theorem B2611943 : Blo 1160639 2611943 := bstep (se 1 (by rfl) ⟨1958957, by rfl⟩ : syracuseStep 2611943 = 3917915) B3917915
theorem B3922775 : Blo 1160639 3922775 := bstep (se 1 (by rfl) ⟨2942081, by rfl⟩ : syracuseStep 3922775 = 5884163) B5884163
theorem B6610207 : Blo 1160639 6610207 := bstep (se 1 (by rfl) ⟨4957655, by rfl⟩ : syracuseStep 6610207 = 9915311) B9915311
theorem B3923585 : Blo 1160639 3923585 := bstep (se 2 (by rfl) ⟨1471344, by rfl⟩ : syracuseStep 3923585 = 2942689) B2942689
theorem B2481835 : Blo 1160639 2481835 := bstep (se 1 (by rfl) ⟨1861376, by rfl⟩ : syracuseStep 2481835 = 3722753) B3722753
theorem B3924071 : Blo 1160639 3924071 := bstep (se 1 (by rfl) ⟨2943053, by rfl⟩ : syracuseStep 3924071 = 5886107) B5886107
theorem B3137723 : Blo 1160639 3137723 := bstep (se 1 (by rfl) ⟨2353292, by rfl⟩ : syracuseStep 3137723 = 4706585) B4706585
theorem B3727559 : Blo 1160639 3727559 := bstep (se 1 (by rfl) ⟨2795669, by rfl⟩ : syracuseStep 3727559 = 5591339) B5591339
theorem B4415903 : Blo 1160639 4415903 := bstep (se 1 (by rfl) ⟨3311927, by rfl⟩ : syracuseStep 4415903 = 6623855) B6623855
theorem B5890643 : Blo 1160639 5890643 := bstep (se 1 (by rfl) ⟨4417982, by rfl⟩ : syracuseStep 5890643 = 8835965) B8835965
theorem B25846685 : Blo 1160639 25846685 := bstep (se 3 (by rfl) ⟨4846253, by rfl⟩ : syracuseStep 25846685 = 9692507) B9692507
theorem B3924989 : Blo 1160639 3924989 := bstep (se 3 (by rfl) ⟨735935, by rfl⟩ : syracuseStep 3924989 = 1471871) B1471871
theorem B31778203 : Blo 1160639 31778203 := bstep (se 1 (by rfl) ⟨23833652, by rfl⟩ : syracuseStep 31778203 = 47667305) B47667305
theorem B2942527 : Blo 1160639 2942527 := bstep (se 1 (by rfl) ⟨2206895, by rfl⟩ : syracuseStep 2942527 = 4413791) B4413791
theorem B1959599 : Blo 1160639 1959599 := bstep (se 1 (by rfl) ⟨1469699, by rfl⟩ : syracuseStep 1959599 = 2939399) B2939399
theorem B2615327 : Blo 1160639 2615327 := bstep (se 1 (by rfl) ⟨1961495, by rfl⟩ : syracuseStep 2615327 = 3922991) B3922991
theorem B3926177 : Blo 1160639 3926177 := bstep (se 2 (by rfl) ⟨1472316, by rfl⟩ : syracuseStep 3926177 = 2944633) B2944633
theorem B5892263 : Blo 1160639 5892263 := bstep (se 1 (by rfl) ⟨4419197, by rfl⟩ : syracuseStep 5892263 = 8838395) B8838395
theorem B5958083 : Blo 1160639 5958083 := bstep (se 1 (by rfl) ⟨4468562, by rfl⟩ : syracuseStep 5958083 = 8937125) B8937125
theorem B2615849 : Blo 1160639 2615849 := bstep (se 2 (by rfl) ⟨980943, by rfl⟩ : syracuseStep 2615849 = 1961887) B1961887
theorem B4713167 : Blo 1160639 4713167 := bstep (se 1 (by rfl) ⟨3534875, by rfl⟩ : syracuseStep 4713167 = 7069751) B7069751
theorem B2616155 : Blo 1160639 2616155 := bstep (se 1 (by rfl) ⟨1962116, by rfl⟩ : syracuseStep 2616155 = 3924233) B3924233
theorem B2616263 : Blo 1160639 2616263 := bstep (se 1 (by rfl) ⟨1962197, by rfl⟩ : syracuseStep 2616263 = 3924395) B3924395
theorem B26864759 : Blo 1160639 26864759 := bstep (se 1 (by rfl) ⟨20148569, by rfl⟩ : syracuseStep 26864759 = 40297139) B40297139
theorem B1240687 : Blo 1160639 1240687 := bstep (se 1 (by rfl) ⟨930515, by rfl⟩ : syracuseStep 1240687 = 1861031) B1861031
theorem B3927743 : Blo 1160639 3927743 := bstep (se 1 (by rfl) ⟨2945807, by rfl⟩ : syracuseStep 3927743 = 5891615) B5891615
theorem B4419305 : Blo 1160639 4419305 := bstep (se 2 (by rfl) ⟨1657239, by rfl⟩ : syracuseStep 4419305 = 3314479) B3314479
theorem B3927905 : Blo 1160639 3927905 := bstep (se 2 (by rfl) ⟨1472964, by rfl⟩ : syracuseStep 3927905 = 2945929) B2945929
theorem B1306651 : Blo 1160639 1306651 := bstep (se 1 (by rfl) ⟨979988, by rfl⟩ : syracuseStep 1306651 = 1959977) B1959977
theorem B3141679 : Blo 1160639 3141679 := bstep (se 1 (by rfl) ⟨2356259, by rfl⟩ : syracuseStep 3141679 = 4712519) B4712519
theorem B4419791 : Blo 1160639 4419791 := bstep (se 1 (by rfl) ⟨3314843, by rfl⟩ : syracuseStep 4419791 = 6629687) B6629687
theorem B3928553 : Blo 1160639 3928553 := bstep (se 2 (by rfl) ⟨1473207, by rfl⟩ : syracuseStep 3928553 = 2946415) B2946415
theorem B1470955 : Blo 1160639 1470955 := bstep (se 1 (by rfl) ⟨1103216, by rfl⟩ : syracuseStep 1470955 = 2206433) B2206433
theorem B6615539 : Blo 1160639 6615539 := bstep (se 1 (by rfl) ⟨4961654, by rfl⟩ : syracuseStep 6615539 = 9923309) B9923309
theorem B3928607 : Blo 1160639 3928607 := bstep (se 1 (by rfl) ⟨2946455, by rfl⟩ : syracuseStep 3928607 = 5892911) B5892911
theorem B558265283 : Blo 1160639 558265283 := bstep (se 1 (by rfl) ⟨418698962, by rfl⟩ : syracuseStep 558265283 = 837397925) B837397925
theorem B3929039 : Blo 1160639 3929039 := bstep (se 1 (by rfl) ⟨2946779, by rfl⟩ : syracuseStep 3929039 = 5893559) B5893559
theorem B3929147 : Blo 1160639 3929147 := bstep (se 1 (by rfl) ⟨2946860, by rfl⟩ : syracuseStep 3929147 = 5893721) B5893721
theorem B1307839 : Blo 1160639 1307839 := bstep (se 1 (by rfl) ⟨980879, by rfl⟩ : syracuseStep 1307839 = 1961759) B1961759
theorem B1864939 : Blo 1160639 1864939 := bstep (se 1 (by rfl) ⟨1398704, by rfl⟩ : syracuseStep 1864939 = 2797409) B2797409
theorem B1865081 : Blo 1160639 1865081 := bstep (se 2 (by rfl) ⟨699405, by rfl⟩ : syracuseStep 1865081 = 1398811) B1398811
theorem B3929471 : Blo 1160639 3929471 := bstep (se 1 (by rfl) ⟨2947103, by rfl⟩ : syracuseStep 3929471 = 5894207) B5894207
theorem B2618855 : Blo 1160639 2618855 := bstep (se 1 (by rfl) ⟨1964141, by rfl⟩ : syracuseStep 2618855 = 3928283) B3928283
theorem B2618927 : Blo 1160639 2618927 := bstep (se 1 (by rfl) ⟨1964195, by rfl⟩ : syracuseStep 2618927 = 3928391) B3928391
theorem B4421263 : Blo 1160639 4421263 := bstep (se 1 (by rfl) ⟨3315947, by rfl⟩ : syracuseStep 4421263 = 6631895) B6631895
theorem B4192019 : Blo 1160639 4192019 := bstep (se 1 (by rfl) ⟨3144014, by rfl⟩ : syracuseStep 4192019 = 6288029) B6288029
theorem B4421735 : Blo 1160639 4421735 := bstep (se 1 (by rfl) ⟨3316301, by rfl⟩ : syracuseStep 4421735 = 6632603) B6632603
theorem B3930335 : Blo 1160639 3930335 := bstep (se 1 (by rfl) ⟨2947751, by rfl⟩ : syracuseStep 3930335 = 5895503) B5895503
theorem B1964911 : Blo 1160639 1964911 := bstep (se 1 (by rfl) ⟨1473683, by rfl⟩ : syracuseStep 1964911 = 2947367) B2947367
theorem B1768313 : Blo 1160639 1768313 := bstep (se 2 (by rfl) ⟨663117, by rfl⟩ : syracuseStep 1768313 = 1326235) B1326235
theorem B6618455 : Blo 1160639 6618455 := bstep (se 1 (by rfl) ⟨4963841, by rfl⟩ : syracuseStep 6618455 = 9927683) B9927683
theorem B7077827 : Blo 1160639 7077827 := bstep (se 1 (by rfl) ⟨5308370, by rfl⟩ : syracuseStep 7077827 = 10616741) B10616741
theorem B3309979 : Blo 1160639 3309979 := bstep (se 1 (by rfl) ⟨2482484, by rfl⟩ : syracuseStep 3309979 = 4964969) B4964969
theorem B29786939 : Blo 1160639 29786939 := bstep (se 1 (by rfl) ⟨22340204, by rfl⟩ : syracuseStep 29786939 = 44680409) B44680409
theorem B2982881 : Blo 1160639 2982881 := bstep (se 2 (by rfl) ⟨1118580, by rfl⟩ : syracuseStep 2982881 = 2237161) B2237161
theorem B42370937 : Blo 1160639 42370937 := bstep (se 2 (by rfl) ⟨15889101, by rfl⟩ : syracuseStep 42370937 = 31778203) B31778203
theorem B85953953 : Blo 1160639 85953953 := bstep (se 2 (by rfl) ⟨32232732, by rfl⟩ : syracuseStep 85953953 = 64465465) B64465465
theorem B1741295 : Blo 1160639 1741295 := bstep (se 1 (by rfl) ⟨1305971, by rfl⟩ : syracuseStep 1741295 = 2611943) B2611943
theorem B1742201 : Blo 1160639 1742201 := bstep (se 2 (by rfl) ⟨653325, by rfl⟩ : syracuseStep 1742201 = 1306651) B1306651
theorem B13244471 : Blo 1160639 13244471 := bstep (se 1 (by rfl) ⟨9933353, by rfl⟩ : syracuseStep 13244471 = 19866707) B19866707
theorem B21240143 : Blo 1160639 21240143 := bstep (se 1 (by rfl) ⟨15930107, by rfl⟩ : syracuseStep 21240143 = 31860215) B31860215
theorem B1743551 : Blo 1160639 1743551 := bstep (se 1 (by rfl) ⟨1307663, by rfl⟩ : syracuseStep 1743551 = 2615327) B2615327
theorem B5970671 : Blo 1160639 5970671 := bstep (se 1 (by rfl) ⟨4478003, by rfl⟩ : syracuseStep 5970671 = 8956007) B8956007
theorem B1743785 : Blo 1160639 1743785 := bstep (se 2 (by rfl) ⟨653919, by rfl⟩ : syracuseStep 1743785 = 1307839) B1307839
theorem B1743899 : Blo 1160639 1743899 := bstep (se 1 (by rfl) ⟨1307924, by rfl⟩ : syracuseStep 1743899 = 2615849) B2615849
theorem B29760695 : Blo 1160639 29760695 := bstep (se 1 (by rfl) ⟨22320521, by rfl⟩ : syracuseStep 29760695 = 44641043) B44641043
theorem B1744103 : Blo 1160639 1744103 := bstep (se 1 (by rfl) ⟨1308077, by rfl⟩ : syracuseStep 1744103 = 2616155) B2616155
theorem B1744175 : Blo 1160639 1744175 := bstep (se 1 (by rfl) ⟨1308131, by rfl⟩ : syracuseStep 1744175 = 2616263) B2616263
theorem B14917769 : Blo 1160639 14917769 := bstep (se 2 (by rfl) ⟨5594163, by rfl⟩ : syracuseStep 14917769 = 11188327) B11188327
theorem B1745903 : Blo 1160639 1745903 := bstep (se 1 (by rfl) ⟨1309427, by rfl⟩ : syracuseStep 1745903 = 2618855) B2618855
theorem B1745951 : Blo 1160639 1745951 := bstep (se 1 (by rfl) ⟨1309463, by rfl⟩ : syracuseStep 1745951 = 2618927) B2618927
theorem B2794679 : Blo 1160639 2794679 := bstep (se 1 (by rfl) ⟨2096009, by rfl⟩ : syracuseStep 2794679 = 4192019) B4192019
theorem B9940157 : Blo 1160639 9940157 := bstep (se 3 (by rfl) ⟨1863779, by rfl⟩ : syracuseStep 9940157 = 3727559) B3727559
theorem B15084829 : Blo 1160639 15084829 := bstep (se 3 (by rfl) ⟨2828405, by rfl⟩ : syracuseStep 15084829 = 5656811) B5656811
theorem B8598259 : Blo 1160639 8598259 := bstep (se 1 (by rfl) ⟨6448694, by rfl⟩ : syracuseStep 8598259 = 12897389) B12897389
theorem B1160751 : Blo 1160639 1160751 := bstep (se 1 (by rfl) ⟨870563, by rfl⟩ : syracuseStep 1160751 = 1741127) B1741127
theorem B1161663 : Blo 1160639 1161663 := bstep (se 1 (by rfl) ⟨871247, by rfl⟩ : syracuseStep 1161663 = 1742495) B1742495
theorem B4963295 : Blo 1160639 4963295 := bstep (se 1 (by rfl) ⟨3722471, by rfl⟩ : syracuseStep 4963295 = 7444943) B7444943
theorem B1162343 : Blo 1160639 1162343 := bstep (se 1 (by rfl) ⟨871757, by rfl⟩ : syracuseStep 1162343 = 1743515) B1743515
theorem B1162779 : Blo 1160639 1162779 := bstep (se 1 (by rfl) ⟨872084, by rfl⟩ : syracuseStep 1162779 = 1744169) B1744169
theorem B4963943 : Blo 1160639 4963943 := bstep (se 1 (by rfl) ⟨3722957, by rfl⟩ : syracuseStep 4963943 = 7445915) B7445915
theorem B11190059 : Blo 1160639 11190059 := bstep (se 1 (by rfl) ⟨8392544, by rfl⟩ : syracuseStep 11190059 = 16785089) B16785089
theorem B1163071 : Blo 1160639 1163071 := bstep (se 1 (by rfl) ⟨872303, by rfl⟩ : syracuseStep 1163071 = 1744607) B1744607
theorem B1163335 : Blo 1160639 1163335 := bstep (se 1 (by rfl) ⟨872501, by rfl⟩ : syracuseStep 1163335 = 1745003) B1745003
theorem B1163355 : Blo 1160639 1163355 := bstep (se 1 (by rfl) ⟨872516, by rfl⟩ : syracuseStep 1163355 = 1745033) B1745033
theorem B1163391 : Blo 1160639 1163391 := bstep (se 1 (by rfl) ⟨872543, by rfl⟩ : syracuseStep 1163391 = 1745087) B1745087
theorem B1163487 : Blo 1160639 1163487 := bstep (se 1 (by rfl) ⟨872615, by rfl⟩ : syracuseStep 1163487 = 1745231) B1745231
theorem B1163503 : Blo 1160639 1163503 := bstep (se 1 (by rfl) ⟨872627, by rfl⟩ : syracuseStep 1163503 = 1745255) B1745255
theorem B1163711 : Blo 1160639 1163711 := bstep (se 1 (by rfl) ⟨872783, by rfl⟩ : syracuseStep 1163711 = 1745567) B1745567
theorem B5882705 : Blo 1160639 5882705 := bstep (se 2 (by rfl) ⟨2206014, by rfl⟩ : syracuseStep 5882705 = 4412029) B4412029
theorem B4966267 : Blo 1160639 4966267 := bstep (se 1 (by rfl) ⟨3724700, by rfl⟩ : syracuseStep 4966267 = 7449401) B7449401
theorem B12568445 : Blo 1160639 12568445 := bstep (se 3 (by rfl) ⟨2356583, by rfl⟩ : syracuseStep 12568445 = 4713167) B4713167
theorem B17909839 : Blo 1160639 17909839 := bstep (se 1 (by rfl) ⟨13432379, by rfl⟩ : syracuseStep 17909839 = 26864759) B26864759
theorem B35768927 : Blo 1160639 35768927 := bstep (se 1 (by rfl) ⟨26826695, by rfl⟩ : syracuseStep 35768927 = 53653391) B53653391
theorem B5884649 : Blo 1160639 5884649 := bstep (se 2 (by rfl) ⟨2206743, by rfl⟩ : syracuseStep 5884649 = 4413487) B4413487
theorem B3918671 : Blo 1160639 3918671 := bstep (se 1 (by rfl) ⟨2939003, by rfl⟩ : syracuseStep 3918671 = 5878007) B5878007
theorem B4410359 : Blo 1160639 4410359 := bstep (se 1 (by rfl) ⟨3307769, by rfl⟩ : syracuseStep 4410359 = 6615539) B6615539
theorem B4967497 : Blo 1160639 4967497 := bstep (se 2 (by rfl) ⟨1862811, by rfl⟩ : syracuseStep 4967497 = 3725623) B3725623
theorem B9948527 : Blo 1160639 9948527 := bstep (se 1 (by rfl) ⟨7461395, by rfl⟩ : syracuseStep 9948527 = 14922791) B14922791
theorem B5885783 : Blo 1160639 5885783 := bstep (se 1 (by rfl) ⟨4414337, by rfl⟩ : syracuseStep 5885783 = 8828675) B8828675
theorem B11915387 : Blo 1160639 11915387 := bstep (se 1 (by rfl) ⟨8936540, by rfl⟩ : syracuseStep 11915387 = 17873081) B17873081
theorem B4412303 : Blo 1160639 4412303 := bstep (se 1 (by rfl) ⟨3309227, by rfl⟩ : syracuseStep 4412303 = 6618455) B6618455
theorem B4969583 : Blo 1160639 4969583 := bstep (se 1 (by rfl) ⟨3727187, by rfl⟩ : syracuseStep 4969583 = 7454375) B7454375
theorem B48420175 : Blo 1160639 48420175 := bstep (se 1 (by rfl) ⟨36315131, by rfl⟩ : syracuseStep 48420175 = 72630263) B72630263
theorem B12080663 : Blo 1160639 12080663 := bstep (se 1 (by rfl) ⟨9060497, by rfl⟩ : syracuseStep 12080663 = 18120995) B18120995
theorem B1398503 : Blo 1160639 1398503 := bstep (se 1 (by rfl) ⟨1048877, by rfl⟩ : syracuseStep 1398503 = 2097755) B2097755
theorem B5888699 : Blo 1160639 5888699 := bstep (se 1 (by rfl) ⟨4416524, by rfl⟩ : syracuseStep 5888699 = 8833049) B8833049
theorem B43015009 : Blo 1160639 43015009 := bstep (se 2 (by rfl) ⟨16130628, by rfl⟩ : syracuseStep 43015009 = 32261257) B32261257
theorem B3923369 : Blo 1160639 3923369 := bstep (se 2 (by rfl) ⟨1471263, by rfl⟩ : syracuseStep 3923369 = 2942527) B2942527
theorem B3923423 : Blo 1160639 3923423 := bstep (se 1 (by rfl) ⟨2942567, by rfl⟩ : syracuseStep 3923423 = 5885135) B5885135
theorem B20143997 : Blo 1160639 20143997 := bstep (se 3 (by rfl) ⟨3776999, by rfl⟩ : syracuseStep 20143997 = 7553999) B7553999
theorem B2613275 : Blo 1160639 2613275 := bstep (se 1 (by rfl) ⟨1959956, by rfl⟩ : syracuseStep 2613275 = 3919913) B3919913
theorem B5300255 : Blo 1160639 5300255 := bstep (se 1 (by rfl) ⟨3975191, by rfl⟩ : syracuseStep 5300255 = 7950383) B7950383
theorem B2941231 : Blo 1160639 2941231 := bstep (se 1 (by rfl) ⟨2205923, by rfl⟩ : syracuseStep 2941231 = 4411847) B4411847
theorem B2941343 : Blo 1160639 2941343 := bstep (se 1 (by rfl) ⟨2206007, by rfl⟩ : syracuseStep 2941343 = 4412015) B4412015
theorem B3924719 : Blo 1160639 3924719 := bstep (se 1 (by rfl) ⟨2943539, by rfl⟩ : syracuseStep 3924719 = 5887079) B5887079
theorem B9921599 : Blo 1160639 9921599 := bstep (se 1 (by rfl) ⟨7441199, by rfl⟩ : syracuseStep 9921599 = 14882399) B14882399
theorem B580019363 : Blo 1160639 580019363 := bstep (se 1 (by rfl) ⟨435014522, by rfl⟩ : syracuseStep 580019363 = 870029045) B870029045
theorem B1959707 : Blo 1160639 1959707 := bstep (se 1 (by rfl) ⟨1469780, by rfl⟩ : syracuseStep 1959707 = 2939561) B2939561
theorem B2615183 : Blo 1160639 2615183 := bstep (se 1 (by rfl) ⟨1961387, by rfl⟩ : syracuseStep 2615183 = 3922775) B3922775
theorem B2615723 : Blo 1160639 2615723 := bstep (se 1 (by rfl) ⟨1961792, by rfl⟩ : syracuseStep 2615723 = 3923585) B3923585
theorem B4188905 : Blo 1160639 4188905 := bstep (se 2 (by rfl) ⟨1570839, by rfl⟩ : syracuseStep 4188905 = 3141679) B3141679
theorem B2616047 : Blo 1160639 2616047 := bstep (se 1 (by rfl) ⟨1962035, by rfl⟩ : syracuseStep 2616047 = 3924071) B3924071
theorem B2091815 : Blo 1160639 2091815 := bstep (se 1 (by rfl) ⟨1568861, by rfl⟩ : syracuseStep 2091815 = 3137723) B3137723
theorem B2943935 : Blo 1160639 2943935 := bstep (se 1 (by rfl) ⟨2207951, by rfl⟩ : syracuseStep 2943935 = 4415903) B4415903
theorem B3927095 : Blo 1160639 3927095 := bstep (se 1 (by rfl) ⟨2945321, by rfl⟩ : syracuseStep 3927095 = 5890643) B5890643
theorem B17231123 : Blo 1160639 17231123 := bstep (se 1 (by rfl) ⟨12923342, by rfl⟩ : syracuseStep 17231123 = 25846685) B25846685
theorem B1961273 : Blo 1160639 1961273 := bstep (se 2 (by rfl) ⟨735477, by rfl⟩ : syracuseStep 1961273 = 1470955) B1470955
theorem B2616659 : Blo 1160639 2616659 := bstep (se 1 (by rfl) ⟨1962494, by rfl⟩ : syracuseStep 2616659 = 3924989) B3924989
theorem B1306399 : Blo 1160639 1306399 := bstep (se 1 (by rfl) ⟨979799, by rfl⟩ : syracuseStep 1306399 = 1959599) B1959599
theorem B15888221 : Blo 1160639 15888221 := bstep (se 3 (by rfl) ⟨2979041, by rfl⟩ : syracuseStep 15888221 = 5958083) B5958083
theorem B2617451 : Blo 1160639 2617451 := bstep (se 1 (by rfl) ⟨1963088, by rfl⟩ : syracuseStep 2617451 = 3926177) B3926177
theorem B3928175 : Blo 1160639 3928175 := bstep (se 1 (by rfl) ⟨2946131, by rfl⟩ : syracuseStep 3928175 = 5892263) B5892263
theorem B2486585 : Blo 1160639 2486585 := bstep (se 2 (by rfl) ⟨932469, by rfl⟩ : syracuseStep 2486585 = 1864939) B1864939
theorem B5895017 : Blo 1160639 5895017 := bstep (se 2 (by rfl) ⟨2210631, by rfl⟩ : syracuseStep 5895017 = 4421263) B4421263
theorem B4715501 : Blo 1160639 4715501 := bstep (se 3 (by rfl) ⟨884156, by rfl⟩ : syracuseStep 4715501 = 1768313) B1768313
theorem B2618495 : Blo 1160639 2618495 := bstep (se 1 (by rfl) ⟨1963871, by rfl⟩ : syracuseStep 2618495 = 3927743) B3927743
theorem B2946203 : Blo 1160639 2946203 := bstep (se 1 (by rfl) ⟨2209652, by rfl⟩ : syracuseStep 2946203 = 4419305) B4419305
theorem B4420777 : Blo 1160639 4420777 := bstep (se 2 (by rfl) ⟨1657791, by rfl⟩ : syracuseStep 4420777 = 3315583) B3315583
theorem B2618603 : Blo 1160639 2618603 := bstep (se 1 (by rfl) ⟨1963952, by rfl⟩ : syracuseStep 2618603 = 3927905) B3927905
theorem B3634589 : Blo 1160639 3634589 := bstep (se 3 (by rfl) ⟨681485, by rfl⟩ : syracuseStep 3634589 = 1362971) B1362971
theorem B2946527 : Blo 1160639 2946527 := bstep (se 1 (by rfl) ⟨2209895, by rfl⟩ : syracuseStep 2946527 = 4419791) B4419791
theorem B4421249 : Blo 1160639 4421249 := bstep (se 2 (by rfl) ⟨1657968, by rfl⟩ : syracuseStep 4421249 = 3315937) B3315937
theorem B2619035 : Blo 1160639 2619035 := bstep (se 1 (by rfl) ⟨1964276, by rfl⟩ : syracuseStep 2619035 = 3928553) B3928553
theorem B2619071 : Blo 1160639 2619071 := bstep (se 1 (by rfl) ⟨1964303, by rfl⟩ : syracuseStep 2619071 = 3928607) B3928607
theorem B6616997 : Blo 1160639 6616997 := bstep (se 4 (by rfl) ⟨620343, by rfl⟩ : syracuseStep 6616997 = 1240687) B1240687
theorem B372176855 : Blo 1160639 372176855 := bstep (se 1 (by rfl) ⟨279132641, by rfl⟩ : syracuseStep 372176855 = 558265283) B558265283
theorem B2619359 : Blo 1160639 2619359 := bstep (se 1 (by rfl) ⟨1964519, by rfl⟩ : syracuseStep 2619359 = 3929039) B3929039
theorem B2619431 : Blo 1160639 2619431 := bstep (se 1 (by rfl) ⟨1964573, by rfl⟩ : syracuseStep 2619431 = 3929147) B3929147
theorem B1243387 : Blo 1160639 1243387 := bstep (se 1 (by rfl) ⟨932540, by rfl⟩ : syracuseStep 1243387 = 1865081) B1865081
theorem B2619647 : Blo 1160639 2619647 := bstep (se 1 (by rfl) ⟨1964735, by rfl⟩ : syracuseStep 2619647 = 3929471) B3929471
theorem B2619881 : Blo 1160639 2619881 := bstep (se 2 (by rfl) ⟨982455, by rfl⟩ : syracuseStep 2619881 = 1964911) B1964911
theorem B21199481 : Blo 1160639 21199481 := bstep (se 2 (by rfl) ⟨7949805, by rfl⟩ : syracuseStep 21199481 = 15899611) B15899611
theorem B2947823 : Blo 1160639 2947823 := bstep (se 1 (by rfl) ⟨2210867, by rfl⟩ : syracuseStep 2947823 = 4421735) B4421735
theorem B2620223 : Blo 1160639 2620223 := bstep (se 1 (by rfl) ⟨1965167, by rfl⟩ : syracuseStep 2620223 = 3930335) B3930335
theorem B2685961 : Blo 1160639 2685961 := bstep (se 2 (by rfl) ⟨1007235, by rfl⟩ : syracuseStep 2685961 = 2014471) B2014471
theorem B8813609 : Blo 1160639 8813609 := bstep (se 2 (by rfl) ⟨3305103, by rfl⟩ : syracuseStep 8813609 = 6610207) B6610207
theorem B3309113 : Blo 1160639 3309113 := bstep (se 2 (by rfl) ⟨1240917, by rfl⟩ : syracuseStep 3309113 = 2481835) B2481835
theorem B18874205 : Blo 1160639 18874205 := bstep (se 3 (by rfl) ⟨3538913, by rfl⟩ : syracuseStep 18874205 = 7077827) B7077827
theorem B19857959 : Blo 1160639 19857959 := bstep (se 1 (by rfl) ⟨14893469, by rfl⟩ : syracuseStep 19857959 = 29786939) B29786939
theorem B28247291 : Blo 1160639 28247291 := bstep (se 1 (by rfl) ⟨21185468, by rfl⟩ : syracuseStep 28247291 = 42370937) B42370937
theorem B6621689 : Blo 1160639 6621689 := bstep (se 2 (by rfl) ⟨2483133, by rfl⟩ : syracuseStep 6621689 = 4966267) B4966267
theorem B3313055 : Blo 1160639 3313055 := bstep (se 1 (by rfl) ⟨2484791, by rfl⟩ : syracuseStep 3313055 = 4969583) B4969583
theorem B6623329 : Blo 1160639 6623329 := bstep (se 2 (by rfl) ⟨2483748, by rfl⟩ : syracuseStep 6623329 = 4967497) B4967497
theorem B14160095 : Blo 1160639 14160095 := bstep (se 1 (by rfl) ⟨10620071, by rfl⟩ : syracuseStep 14160095 = 21240143) B21240143
theorem B1741865 : Blo 1160639 1741865 := bstep (se 2 (by rfl) ⟨653199, by rfl⟩ : syracuseStep 1741865 = 1306399) B1306399
theorem B1742183 : Blo 1160639 1742183 := bstep (se 1 (by rfl) ⟨1306637, by rfl⟩ : syracuseStep 1742183 = 2613275) B2613275
theorem B1743455 : Blo 1160639 1743455 := bstep (se 1 (by rfl) ⟨1307591, by rfl⟩ : syracuseStep 1743455 = 2615183) B2615183
theorem B1743815 : Blo 1160639 1743815 := bstep (se 1 (by rfl) ⟨1307861, by rfl⟩ : syracuseStep 1743815 = 2615723) B2615723
theorem B64560233 : Blo 1160639 64560233 := bstep (se 2 (by rfl) ⟨24210087, by rfl⟩ : syracuseStep 64560233 = 48420175) B48420175
theorem B2792603 : Blo 1160639 2792603 := bstep (se 1 (by rfl) ⟨2094452, by rfl⟩ : syracuseStep 2792603 = 4188905) B4188905
theorem B1744031 : Blo 1160639 1744031 := bstep (se 1 (by rfl) ⟨1308023, by rfl⟩ : syracuseStep 1744031 = 2616047) B2616047
theorem B6626771 : Blo 1160639 6626771 := bstep (se 1 (by rfl) ⟨4970078, by rfl⟩ : syracuseStep 6626771 = 9940157) B9940157
theorem B1744439 : Blo 1160639 1744439 := bstep (se 1 (by rfl) ⟨1308329, by rfl⟩ : syracuseStep 1744439 = 2616659) B2616659
theorem B10592147 : Blo 1160639 10592147 := bstep (se 1 (by rfl) ⟨7944110, by rfl⟩ : syracuseStep 10592147 = 15888221) B15888221
theorem B1744967 : Blo 1160639 1744967 := bstep (se 1 (by rfl) ⟨1308725, by rfl⟩ : syracuseStep 1744967 = 2617451) B2617451
theorem B1745663 : Blo 1160639 1745663 := bstep (se 1 (by rfl) ⟨1309247, by rfl⟩ : syracuseStep 1745663 = 2618495) B2618495
theorem B1745735 : Blo 1160639 1745735 := bstep (se 1 (by rfl) ⟨1309301, by rfl⟩ : syracuseStep 1745735 = 2618603) B2618603
theorem B1746023 : Blo 1160639 1746023 := bstep (se 1 (by rfl) ⟨1309517, by rfl⟩ : syracuseStep 1746023 = 2619035) B2619035
theorem B1746047 : Blo 1160639 1746047 := bstep (se 1 (by rfl) ⟨1309535, by rfl⟩ : syracuseStep 1746047 = 2619071) B2619071
theorem B57353345 : Blo 1160639 57353345 := bstep (se 2 (by rfl) ⟨21507504, by rfl⟩ : syracuseStep 57353345 = 43015009) B43015009
theorem B1746239 : Blo 1160639 1746239 := bstep (se 1 (by rfl) ⟨1309679, by rfl⟩ : syracuseStep 1746239 = 2619359) B2619359
theorem B3581281 : Blo 1160639 3581281 := bstep (se 2 (by rfl) ⟨1342980, by rfl⟩ : syracuseStep 3581281 = 2685961) B2685961
theorem B1746287 : Blo 1160639 1746287 := bstep (se 1 (by rfl) ⟨1309715, by rfl⟩ : syracuseStep 1746287 = 2619431) B2619431
theorem B8824301 : Blo 1160639 8824301 := bstep (se 3 (by rfl) ⟨1654556, by rfl⟩ : syracuseStep 8824301 = 3309113) B3309113
theorem B1746431 : Blo 1160639 1746431 := bstep (se 1 (by rfl) ⟨1309823, by rfl⟩ : syracuseStep 1746431 = 2619647) B2619647
theorem B1746587 : Blo 1160639 1746587 := bstep (se 1 (by rfl) ⟨1309940, by rfl⟩ : syracuseStep 1746587 = 2619881) B2619881
theorem B14132987 : Blo 1160639 14132987 := bstep (se 1 (by rfl) ⟨10599740, by rfl⟩ : syracuseStep 14132987 = 21199481) B21199481
theorem B1746815 : Blo 1160639 1746815 := bstep (se 1 (by rfl) ⟨1310111, by rfl⟩ : syracuseStep 1746815 = 2620223) B2620223
theorem B5875739 : Blo 1160639 5875739 := bstep (se 1 (by rfl) ⟨4406804, by rfl⟩ : syracuseStep 5875739 = 8813609) B8813609
theorem B14134013 : Blo 1160639 14134013 := bstep (se 3 (by rfl) ⟨2650127, by rfl⟩ : syracuseStep 14134013 = 5300255) B5300255
theorem B6630893 : Blo 1160639 6630893 := bstep (se 3 (by rfl) ⟨1243292, by rfl⟩ : syracuseStep 6630893 = 2486585) B2486585
theorem B6632351 : Blo 1160639 6632351 := bstep (se 1 (by rfl) ⟨4974263, by rfl⟩ : syracuseStep 6632351 = 9948527) B9948527
theorem B7943591 : Blo 1160639 7943591 := bstep (se 1 (by rfl) ⟨5957693, by rfl⟩ : syracuseStep 7943591 = 11915387) B11915387
theorem B1160863 : Blo 1160639 1160863 := bstep (se 1 (by rfl) ⟨870647, by rfl⟩ : syracuseStep 1160863 = 1741295) B1741295
theorem B1161467 : Blo 1160639 1161467 := bstep (se 1 (by rfl) ⟨871100, by rfl⟩ : syracuseStep 1161467 = 1742201) B1742201
theorem B8829647 : Blo 1160639 8829647 := bstep (se 1 (by rfl) ⟨6622235, by rfl⟩ : syracuseStep 8829647 = 13244471) B13244471
theorem B1162367 : Blo 1160639 1162367 := bstep (se 1 (by rfl) ⟨871775, by rfl⟩ : syracuseStep 1162367 = 1743551) B1743551
theorem B3980447 : Blo 1160639 3980447 := bstep (se 1 (by rfl) ⟨2985335, by rfl⟩ : syracuseStep 3980447 = 5970671) B5970671
theorem B1162523 : Blo 1160639 1162523 := bstep (se 1 (by rfl) ⟨871892, by rfl⟩ : syracuseStep 1162523 = 1743785) B1743785
theorem B1162599 : Blo 1160639 1162599 := bstep (se 1 (by rfl) ⟨871949, by rfl⟩ : syracuseStep 1162599 = 1743899) B1743899
theorem B19840463 : Blo 1160639 19840463 := bstep (se 1 (by rfl) ⟨14880347, by rfl⟩ : syracuseStep 19840463 = 29760695) B29760695
theorem B1162735 : Blo 1160639 1162735 := bstep (se 1 (by rfl) ⟨872051, by rfl⟩ : syracuseStep 1162735 = 1744103) B1744103
theorem B1162783 : Blo 1160639 1162783 := bstep (se 1 (by rfl) ⟨872087, by rfl⟩ : syracuseStep 1162783 = 1744175) B1744175
theorem B9945179 : Blo 1160639 9945179 := bstep (se 1 (by rfl) ⟨7458884, by rfl⟩ : syracuseStep 9945179 = 14917769) B14917769
theorem B1163935 : Blo 1160639 1163935 := bstep (se 1 (by rfl) ⟨872951, by rfl⟩ : syracuseStep 1163935 = 1745903) B1745903
theorem B1163967 : Blo 1160639 1163967 := bstep (se 1 (by rfl) ⟨872975, by rfl⟩ : syracuseStep 1163967 = 1745951) B1745951
theorem B386679575 : Blo 1160639 386679575 := bstep (se 1 (by rfl) ⟨290009681, by rfl⟩ : syracuseStep 386679575 = 580019363) B580019363
theorem B1394543 : Blo 1160639 1394543 := bstep (se 1 (by rfl) ⟨1045907, by rfl⟩ : syracuseStep 1394543 = 2091815) B2091815
theorem B11487415 : Blo 1160639 11487415 := bstep (se 1 (by rfl) ⟨8615561, by rfl⟩ : syracuseStep 11487415 = 17231123) B17231123
theorem B1657849 : Blo 1160639 1657849 := bstep (se 2 (by rfl) ⟨621693, by rfl⟩ : syracuseStep 1657849 = 1243387) B1243387
theorem B4411331 : Blo 1160639 4411331 := bstep (se 1 (by rfl) ⟨3308498, by rfl⟩ : syracuseStep 4411331 = 6616997) B6616997
theorem B7460039 : Blo 1160639 7460039 := bstep (se 1 (by rfl) ⟨5595029, by rfl⟩ : syracuseStep 7460039 = 11190059) B11190059
theorem B3921641 : Blo 1160639 3921641 := bstep (se 2 (by rfl) ⟨1470615, by rfl⟩ : syracuseStep 3921641 = 2941231) B2941231
theorem B4413305 : Blo 1160639 4413305 := bstep (se 2 (by rfl) ⟨1654989, by rfl⟩ : syracuseStep 4413305 = 3309979) B3309979
theorem B3921803 : Blo 1160639 3921803 := bstep (se 1 (by rfl) ⟨2941352, by rfl⟩ : syracuseStep 3921803 = 5882705) B5882705
theorem B1988587 : Blo 1160639 1988587 := bstep (se 1 (by rfl) ⟨1491440, by rfl⟩ : syracuseStep 1988587 = 2982881) B2982881
theorem B8378963 : Blo 1160639 8378963 := bstep (se 1 (by rfl) ⟨6284222, by rfl⟩ : syracuseStep 8378963 = 12568445) B12568445
theorem B23845951 : Blo 1160639 23845951 := bstep (se 1 (by rfl) ⟨17884463, by rfl⟩ : syracuseStep 23845951 = 35768927) B35768927
theorem B3923099 : Blo 1160639 3923099 := bstep (se 1 (by rfl) ⟨2942324, by rfl⟩ : syracuseStep 3923099 = 5884649) B5884649
theorem B2612447 : Blo 1160639 2612447 := bstep (se 1 (by rfl) ⟨1959335, by rfl⟩ : syracuseStep 2612447 = 3918671) B3918671
theorem B2940239 : Blo 1160639 2940239 := bstep (se 1 (by rfl) ⟨2205179, by rfl⟩ : syracuseStep 2940239 = 4410359) B4410359
theorem B57302635 : Blo 1160639 57302635 := bstep (se 1 (by rfl) ⟨42976976, by rfl⟩ : syracuseStep 57302635 = 85953953) B85953953
theorem B3923855 : Blo 1160639 3923855 := bstep (se 1 (by rfl) ⟨2942891, by rfl⟩ : syracuseStep 3923855 = 5885783) B5885783
theorem B23879785 : Blo 1160639 23879785 := bstep (se 2 (by rfl) ⟨8954919, by rfl⟩ : syracuseStep 23879785 = 17909839) B17909839
theorem B2941535 : Blo 1160639 2941535 := bstep (se 1 (by rfl) ⟨2206151, by rfl⟩ : syracuseStep 2941535 = 4412303) B4412303
theorem B8053775 : Blo 1160639 8053775 := bstep (se 1 (by rfl) ⟨6040331, by rfl⟩ : syracuseStep 8053775 = 12080663) B12080663
theorem B9692237 : Blo 1160639 9692237 := bstep (se 3 (by rfl) ⟨1817294, by rfl⟩ : syracuseStep 9692237 = 3634589) B3634589
theorem B20113105 : Blo 1160639 20113105 := bstep (se 2 (by rfl) ⟨7542414, by rfl⟩ : syracuseStep 20113105 = 15084829) B15084829
theorem B3925799 : Blo 1160639 3925799 := bstep (se 1 (by rfl) ⟨2944349, by rfl⟩ : syracuseStep 3925799 = 5888699) B5888699
theorem B3729341 : Blo 1160639 3729341 := bstep (se 3 (by rfl) ⟨699251, by rfl⟩ : syracuseStep 3729341 = 1398503) B1398503
theorem B2615579 : Blo 1160639 2615579 := bstep (se 1 (by rfl) ⟨1961684, by rfl⟩ : syracuseStep 2615579 = 3923369) B3923369
theorem B2615615 : Blo 1160639 2615615 := bstep (se 1 (by rfl) ⟨1961711, by rfl⟩ : syracuseStep 2615615 = 3923423) B3923423
theorem B13429331 : Blo 1160639 13429331 := bstep (se 1 (by rfl) ⟨10071998, by rfl⟩ : syracuseStep 13429331 = 20143997) B20143997
theorem B1960895 : Blo 1160639 1960895 := bstep (se 1 (by rfl) ⟨1470671, by rfl⟩ : syracuseStep 1960895 = 2941343) B2941343
theorem B2616479 : Blo 1160639 2616479 := bstep (se 1 (by rfl) ⟨1962359, by rfl⟩ : syracuseStep 2616479 = 3924719) B3924719
theorem B6614399 : Blo 1160639 6614399 := bstep (se 1 (by rfl) ⟨4960799, by rfl⟩ : syracuseStep 6614399 = 9921599) B9921599
theorem B1863119 : Blo 1160639 1863119 := bstep (se 1 (by rfl) ⟨1397339, by rfl⟩ : syracuseStep 1863119 = 2794679) B2794679
theorem B11464345 : Blo 1160639 11464345 := bstep (se 2 (by rfl) ⟨4299129, by rfl⟩ : syracuseStep 11464345 = 8598259) B8598259
theorem B1306471 : Blo 1160639 1306471 := bstep (se 1 (by rfl) ⟨979853, by rfl⟩ : syracuseStep 1306471 = 1959707) B1959707
theorem B5894369 : Blo 1160639 5894369 := bstep (se 2 (by rfl) ⟨2210388, by rfl⟩ : syracuseStep 5894369 = 4420777) B4420777
theorem B1962623 : Blo 1160639 1962623 := bstep (se 1 (by rfl) ⟨1471967, by rfl⟩ : syracuseStep 1962623 = 2943935) B2943935
theorem B2618063 : Blo 1160639 2618063 := bstep (se 1 (by rfl) ⟨1963547, by rfl⟩ : syracuseStep 2618063 = 3927095) B3927095
theorem B1307515 : Blo 1160639 1307515 := bstep (se 1 (by rfl) ⟨980636, by rfl⟩ : syracuseStep 1307515 = 1961273) B1961273
theorem B2618783 : Blo 1160639 2618783 := bstep (se 1 (by rfl) ⟨1964087, by rfl⟩ : syracuseStep 2618783 = 3928175) B3928175
theorem B3930011 : Blo 1160639 3930011 := bstep (se 1 (by rfl) ⟨2947508, by rfl⟩ : syracuseStep 3930011 = 5895017) B5895017
theorem B1964135 : Blo 1160639 1964135 := bstep (se 1 (by rfl) ⟨1473101, by rfl⟩ : syracuseStep 1964135 = 2946203) B2946203
theorem B1964351 : Blo 1160639 1964351 := bstep (se 1 (by rfl) ⟨1473263, by rfl⟩ : syracuseStep 1964351 = 2946527) B2946527
theorem B2947499 : Blo 1160639 2947499 := bstep (se 1 (by rfl) ⟨2210624, by rfl⟩ : syracuseStep 2947499 = 4421249) B4421249
theorem B248117903 : Blo 1160639 248117903 := bstep (se 1 (by rfl) ⟨186088427, by rfl⟩ : syracuseStep 248117903 = 372176855) B372176855
theorem B13237181 : Blo 1160639 13237181 := bstep (se 3 (by rfl) ⟨2481971, by rfl⟩ : syracuseStep 13237181 = 4963943) B4963943
theorem B1965215 : Blo 1160639 1965215 := bstep (se 1 (by rfl) ⟨1473911, by rfl⟩ : syracuseStep 1965215 = 2947823) B2947823
theorem B3308863 : Blo 1160639 3308863 := bstep (se 1 (by rfl) ⟨2481647, by rfl⟩ : syracuseStep 3308863 = 4963295) B4963295
theorem B50298677 : Blo 1160639 50298677 := bstep (se 5 (by rfl) ⟨2357750, by rfl⟩ : syracuseStep 50298677 = 4715501) B4715501
theorem B12582803 : Blo 1160639 12582803 := bstep (se 1 (by rfl) ⟨9437102, by rfl⟩ : syracuseStep 12582803 = 18874205) B18874205
theorem B13238639 : Blo 1160639 13238639 := bstep (se 1 (by rfl) ⟨9928979, by rfl⟩ : syracuseStep 13238639 = 19857959) B19857959
theorem B257786383 : Blo 1160639 257786383 := bstep (se 1 (by rfl) ⟨193339787, by rfl⟩ : syracuseStep 257786383 = 386679575) B386679575
theorem B9440063 : Blo 1160639 9440063 := bstep (se 1 (by rfl) ⟨7080047, by rfl⟩ : syracuseStep 9440063 = 14160095) B14160095
theorem B1741631 : Blo 1160639 1741631 := bstep (se 1 (by rfl) ⟨1306223, by rfl⟩ : syracuseStep 1741631 = 2612447) B2612447
theorem B1741961 : Blo 1160639 1741961 := bstep (se 2 (by rfl) ⟨653235, by rfl⟩ : syracuseStep 1741961 = 1306471) B1306471
theorem B6461491 : Blo 1160639 6461491 := bstep (se 1 (by rfl) ⟨4846118, by rfl⟩ : syracuseStep 6461491 = 9692237) B9692237
theorem B1743353 : Blo 1160639 1743353 := bstep (se 2 (by rfl) ⟨653757, by rfl⟩ : syracuseStep 1743353 = 1307515) B1307515
theorem B1743719 : Blo 1160639 1743719 := bstep (se 1 (by rfl) ⟨1307789, by rfl⟩ : syracuseStep 1743719 = 2615579) B2615579
theorem B1743743 : Blo 1160639 1743743 := bstep (se 1 (by rfl) ⟨1307807, by rfl⟩ : syracuseStep 1743743 = 2615615) B2615615
theorem B8952887 : Blo 1160639 8952887 := bstep (se 1 (by rfl) ⟨6714665, by rfl⟩ : syracuseStep 8952887 = 13429331) B13429331
theorem B1744319 : Blo 1160639 1744319 := bstep (se 1 (by rfl) ⟨1308239, by rfl⟩ : syracuseStep 1744319 = 2616479) B2616479
theorem B7446941 : Blo 1160639 7446941 := bstep (se 3 (by rfl) ⟨1396301, by rfl⟩ : syracuseStep 7446941 = 2792603) B2792603
theorem B1745375 : Blo 1160639 1745375 := bstep (se 1 (by rfl) ⟨1309031, by rfl⟩ : syracuseStep 1745375 = 2618063) B2618063
theorem B1745855 : Blo 1160639 1745855 := bstep (se 1 (by rfl) ⟨1309391, by rfl⟩ : syracuseStep 1745855 = 2618783) B2618783
theorem B31794601 : Blo 1160639 31794601 := bstep (se 2 (by rfl) ⟨11922975, by rfl⟩ : syracuseStep 31794601 = 23845951) B23845951
theorem B8824787 : Blo 1160639 8824787 := bstep (se 1 (by rfl) ⟨6618590, by rfl⟩ : syracuseStep 8824787 = 13237181) B13237181
theorem B33532451 : Blo 1160639 33532451 := bstep (se 1 (by rfl) ⟨25149338, by rfl⟩ : syracuseStep 33532451 = 50298677) B50298677
theorem B6630119 : Blo 1160639 6630119 := bstep (se 1 (by rfl) ⟨4972589, by rfl⟩ : syracuseStep 6630119 = 9945179) B9945179
theorem B2208703 : Blo 1160639 2208703 := bstep (se 1 (by rfl) ⟨1656527, by rfl⟩ : syracuseStep 2208703 = 3313055) B3313055
theorem B26817473 : Blo 1160639 26817473 := bstep (se 2 (by rfl) ⟨10056552, by rfl⟩ : syracuseStep 26817473 = 20113105) B20113105
theorem B15316553 : Blo 1160639 15316553 := bstep (se 2 (by rfl) ⟨5743707, by rfl⟩ : syracuseStep 15316553 = 11487415) B11487415
theorem B1161243 : Blo 1160639 1161243 := bstep (se 1 (by rfl) ⟨870932, by rfl⟩ : syracuseStep 1161243 = 1741865) B1741865
theorem B1161455 : Blo 1160639 1161455 := bstep (se 1 (by rfl) ⟨871091, by rfl⟩ : syracuseStep 1161455 = 1742183) B1742183
theorem B2210465 : Blo 1160639 2210465 := bstep (se 2 (by rfl) ⟨828924, by rfl⟩ : syracuseStep 2210465 = 1657849) B1657849
theorem B5585975 : Blo 1160639 5585975 := bstep (se 1 (by rfl) ⟨4189481, by rfl⟩ : syracuseStep 5585975 = 8378963) B8378963
theorem B1162303 : Blo 1160639 1162303 := bstep (se 1 (by rfl) ⟨871727, by rfl⟩ : syracuseStep 1162303 = 1743455) B1743455
theorem B1162543 : Blo 1160639 1162543 := bstep (se 1 (by rfl) ⟨871907, by rfl⟩ : syracuseStep 1162543 = 1743815) B1743815
theorem B43040155 : Blo 1160639 43040155 := bstep (se 1 (by rfl) ⟨32280116, by rfl⟩ : syracuseStep 43040155 = 64560233) B64560233
theorem B1162687 : Blo 1160639 1162687 := bstep (se 1 (by rfl) ⟨872015, by rfl⟩ : syracuseStep 1162687 = 1744031) B1744031
theorem B15285793 : Blo 1160639 15285793 := bstep (se 2 (by rfl) ⟨5732172, by rfl⟩ : syracuseStep 15285793 = 11464345) B11464345
theorem B3718781 : Blo 1160639 3718781 := bstep (se 3 (by rfl) ⟨697271, by rfl⟩ : syracuseStep 3718781 = 1394543) B1394543
theorem B1162959 : Blo 1160639 1162959 := bstep (se 1 (by rfl) ⟨872219, by rfl⟩ : syracuseStep 1162959 = 1744439) B1744439
theorem B7061431 : Blo 1160639 7061431 := bstep (se 1 (by rfl) ⟨5296073, by rfl⟩ : syracuseStep 7061431 = 10592147) B10592147
theorem B1163311 : Blo 1160639 1163311 := bstep (se 1 (by rfl) ⟨872483, by rfl⟩ : syracuseStep 1163311 = 1744967) B1744967
theorem B8831105 : Blo 1160639 8831105 := bstep (se 2 (by rfl) ⟨3311664, by rfl⟩ : syracuseStep 8831105 = 6623329) B6623329
theorem B1163775 : Blo 1160639 1163775 := bstep (se 1 (by rfl) ⟨872831, by rfl⟩ : syracuseStep 1163775 = 1745663) B1745663
theorem B1163823 : Blo 1160639 1163823 := bstep (se 1 (by rfl) ⟨872867, by rfl⟩ : syracuseStep 1163823 = 1745735) B1745735
theorem B1164015 : Blo 1160639 1164015 := bstep (se 1 (by rfl) ⟨873011, by rfl⟩ : syracuseStep 1164015 = 1746023) B1746023
theorem B1164031 : Blo 1160639 1164031 := bstep (se 1 (by rfl) ⟨873023, by rfl⟩ : syracuseStep 1164031 = 1746047) B1746047
theorem B1164159 : Blo 1160639 1164159 := bstep (se 1 (by rfl) ⟨873119, by rfl⟩ : syracuseStep 1164159 = 1746239) B1746239
theorem B1164191 : Blo 1160639 1164191 := bstep (se 1 (by rfl) ⟨873143, by rfl⟩ : syracuseStep 1164191 = 1746287) B1746287
theorem B5882867 : Blo 1160639 5882867 := bstep (se 1 (by rfl) ⟨4412150, by rfl⟩ : syracuseStep 5882867 = 8824301) B8824301
theorem B1164287 : Blo 1160639 1164287 := bstep (se 1 (by rfl) ⟨873215, by rfl⟩ : syracuseStep 1164287 = 1746431) B1746431
theorem B1164391 : Blo 1160639 1164391 := bstep (se 1 (by rfl) ⟨873293, by rfl⟩ : syracuseStep 1164391 = 1746587) B1746587
theorem B9421991 : Blo 1160639 9421991 := bstep (se 1 (by rfl) ⟨7066493, by rfl⟩ : syracuseStep 9421991 = 14132987) B14132987
theorem B1164543 : Blo 1160639 1164543 := bstep (se 1 (by rfl) ⟨873407, by rfl⟩ : syracuseStep 1164543 = 1746815) B1746815
theorem B3917159 : Blo 1160639 3917159 := bstep (se 1 (by rfl) ⟨2937869, by rfl⟩ : syracuseStep 3917159 = 5875739) B5875739
theorem B9422675 : Blo 1160639 9422675 := bstep (se 1 (by rfl) ⟨7067006, by rfl⟩ : syracuseStep 9422675 = 14134013) B14134013
theorem B4409599 : Blo 1160639 4409599 := bstep (se 1 (by rfl) ⟨3307199, by rfl⟩ : syracuseStep 4409599 = 6614399) B6614399
theorem B5295727 : Blo 1160639 5295727 := bstep (se 1 (by rfl) ⟨3971795, by rfl⟩ : syracuseStep 5295727 = 7943591) B7943591
theorem B4968317 : Blo 1160639 4968317 := bstep (se 3 (by rfl) ⟨931559, by rfl⟩ : syracuseStep 4968317 = 1863119) B1863119
theorem B4411817 : Blo 1160639 4411817 := bstep (se 2 (by rfl) ⟨1654431, by rfl⟩ : syracuseStep 4411817 = 3308863) B3308863
theorem B5886431 : Blo 1160639 5886431 := bstep (se 1 (by rfl) ⟨4414823, by rfl⟩ : syracuseStep 5886431 = 8829647) B8829647
theorem B76403513 : Blo 1160639 76403513 := bstep (se 2 (by rfl) ⟨28651317, by rfl⟩ : syracuseStep 76403513 = 57302635) B57302635
theorem B13226975 : Blo 1160639 13226975 := bstep (se 1 (by rfl) ⟨9920231, by rfl⟩ : syracuseStep 13226975 = 19840463) B19840463
theorem B31839713 : Blo 1160639 31839713 := bstep (se 2 (by rfl) ⟨11939892, by rfl⟩ : syracuseStep 31839713 = 23879785) B23879785
theorem B18831527 : Blo 1160639 18831527 := bstep (se 1 (by rfl) ⟨14123645, by rfl⟩ : syracuseStep 18831527 = 28247291) B28247291
theorem B4414459 : Blo 1160639 4414459 := bstep (se 1 (by rfl) ⟨3310844, by rfl⟩ : syracuseStep 4414459 = 6621689) B6621689
theorem B4775041 : Blo 1160639 4775041 := bstep (se 2 (by rfl) ⟨1790640, by rfl⟩ : syracuseStep 4775041 = 3581281) B3581281
theorem B2940887 : Blo 1160639 2940887 := bstep (se 1 (by rfl) ⟨2205665, by rfl⟩ : syracuseStep 2940887 = 4411331) B4411331
theorem B4973359 : Blo 1160639 4973359 := bstep (se 1 (by rfl) ⟨3730019, by rfl⟩ : syracuseStep 4973359 = 7460039) B7460039
theorem B2614427 : Blo 1160639 2614427 := bstep (se 1 (by rfl) ⟨1960820, by rfl⟩ : syracuseStep 2614427 = 3921641) B3921641
theorem B2942203 : Blo 1160639 2942203 := bstep (se 1 (by rfl) ⟨2206652, by rfl⟩ : syracuseStep 2942203 = 4413305) B4413305
theorem B2614535 : Blo 1160639 2614535 := bstep (se 1 (by rfl) ⟨1960901, by rfl⟩ : syracuseStep 2614535 = 3921803) B3921803
theorem B2615399 : Blo 1160639 2615399 := bstep (se 1 (by rfl) ⟨1961549, by rfl⟩ : syracuseStep 2615399 = 3923099) B3923099
theorem B1960159 : Blo 1160639 1960159 := bstep (se 1 (by rfl) ⟨1470119, by rfl⟩ : syracuseStep 1960159 = 2940239) B2940239
theorem B4417847 : Blo 1160639 4417847 := bstep (se 1 (by rfl) ⟨3313385, by rfl⟩ : syracuseStep 4417847 = 6626771) B6626771
theorem B2615903 : Blo 1160639 2615903 := bstep (se 1 (by rfl) ⟨1961927, by rfl⟩ : syracuseStep 2615903 = 3923855) B3923855
theorem B1961023 : Blo 1160639 1961023 := bstep (se 1 (by rfl) ⟨1470767, by rfl⟩ : syracuseStep 1961023 = 2941535) B2941535
theorem B5369183 : Blo 1160639 5369183 := bstep (se 1 (by rfl) ⟨4026887, by rfl⟩ : syracuseStep 5369183 = 8053775) B8053775
theorem B38235563 : Blo 1160639 38235563 := bstep (se 1 (by rfl) ⟨28676672, by rfl⟩ : syracuseStep 38235563 = 57353345) B57353345
theorem B2617199 : Blo 1160639 2617199 := bstep (se 1 (by rfl) ⟨1962899, by rfl⟩ : syracuseStep 2617199 = 3925799) B3925799
theorem B2486227 : Blo 1160639 2486227 := bstep (se 1 (by rfl) ⟨1864670, by rfl⟩ : syracuseStep 2486227 = 3729341) B3729341
theorem B1307263 : Blo 1160639 1307263 := bstep (se 1 (by rfl) ⟨980447, by rfl⟩ : syracuseStep 1307263 = 1960895) B1960895
theorem B4420595 : Blo 1160639 4420595 := bstep (se 1 (by rfl) ⟨3315446, by rfl⟩ : syracuseStep 4420595 = 6630893) B6630893
theorem B2651449 : Blo 1160639 2651449 := bstep (se 2 (by rfl) ⟨994293, by rfl⟩ : syracuseStep 2651449 = 1988587) B1988587
theorem B3929579 : Blo 1160639 3929579 := bstep (se 1 (by rfl) ⟨2947184, by rfl⟩ : syracuseStep 3929579 = 5894369) B5894369
theorem B1308415 : Blo 1160639 1308415 := bstep (se 1 (by rfl) ⟨981311, by rfl⟩ : syracuseStep 1308415 = 1962623) B1962623
theorem B4421567 : Blo 1160639 4421567 := bstep (se 1 (by rfl) ⟨3316175, by rfl⟩ : syracuseStep 4421567 = 6632351) B6632351
theorem B2620007 : Blo 1160639 2620007 := bstep (se 1 (by rfl) ⟨1965005, by rfl⟩ : syracuseStep 2620007 = 3930011) B3930011
theorem B1309423 : Blo 1160639 1309423 := bstep (se 1 (by rfl) ⟨982067, by rfl⟩ : syracuseStep 1309423 = 1964135) B1964135
theorem B1309567 : Blo 1160639 1309567 := bstep (se 1 (by rfl) ⟨982175, by rfl⟩ : syracuseStep 1309567 = 1964351) B1964351
theorem B1964999 : Blo 1160639 1964999 := bstep (se 1 (by rfl) ⟨1473749, by rfl⟩ : syracuseStep 1964999 = 2947499) B2947499
theorem B165411935 : Blo 1160639 165411935 := bstep (se 1 (by rfl) ⟨124058951, by rfl⟩ : syracuseStep 165411935 = 248117903) B248117903
theorem B2653631 : Blo 1160639 2653631 := bstep (se 1 (by rfl) ⟨1990223, by rfl⟩ : syracuseStep 2653631 = 3980447) B3980447
theorem B1310143 : Blo 1160639 1310143 := bstep (se 1 (by rfl) ⟨982607, by rfl⟩ : syracuseStep 1310143 = 1965215) B1965215
theorem B8388535 : Blo 1160639 8388535 := bstep (se 1 (by rfl) ⟨6291401, by rfl⟩ : syracuseStep 8388535 = 12582803) B12582803
theorem B6293375 : Blo 1160639 6293375 := bstep (se 1 (by rfl) ⟨4720031, by rfl⟩ : syracuseStep 6293375 = 9440063) B9440063
theorem B8817983 : Blo 1160639 8817983 := bstep (se 1 (by rfl) ⟨6613487, by rfl⟩ : syracuseStep 8817983 = 13226975) B13226975
theorem B12554351 : Blo 1160639 12554351 := bstep (se 1 (by rfl) ⟨9415763, by rfl⟩ : syracuseStep 12554351 = 18831527) B18831527
theorem B3314969 : Blo 1160639 3314969 := bstep (se 2 (by rfl) ⟨1243113, by rfl⟩ : syracuseStep 3314969 = 2486227) B2486227
theorem B1742951 : Blo 1160639 1742951 := bstep (se 1 (by rfl) ⟨1307213, by rfl⟩ : syracuseStep 1742951 = 2614427) B2614427
theorem B1743017 : Blo 1160639 1743017 := bstep (se 2 (by rfl) ⟨653631, by rfl⟩ : syracuseStep 1743017 = 1307263) B1307263
theorem B1743023 : Blo 1160639 1743023 := bstep (se 1 (by rfl) ⟨1307267, by rfl⟩ : syracuseStep 1743023 = 2614535) B2614535
theorem B1743599 : Blo 1160639 1743599 := bstep (se 1 (by rfl) ⟨1307699, by rfl⟩ : syracuseStep 1743599 = 2615399) B2615399
theorem B22354967 : Blo 1160639 22354967 := bstep (se 1 (by rfl) ⟨16766225, by rfl⟩ : syracuseStep 22354967 = 33532451) B33532451
theorem B1743935 : Blo 1160639 1743935 := bstep (se 1 (by rfl) ⟨1307951, by rfl⟩ : syracuseStep 1743935 = 2615903) B2615903
theorem B3579455 : Blo 1160639 3579455 := bstep (se 1 (by rfl) ⟨2684591, by rfl⟩ : syracuseStep 3579455 = 5369183) B5369183
theorem B1744553 : Blo 1160639 1744553 := bstep (se 2 (by rfl) ⟨654207, by rfl⟩ : syracuseStep 1744553 = 1308415) B1308415
theorem B1744799 : Blo 1160639 1744799 := bstep (se 1 (by rfl) ⟨1308599, by rfl⟩ : syracuseStep 1744799 = 2617199) B2617199
theorem B1745897 : Blo 1160639 1745897 := bstep (se 2 (by rfl) ⟨654711, by rfl⟩ : syracuseStep 1745897 = 1309423) B1309423
theorem B1746089 : Blo 1160639 1746089 := bstep (se 2 (by rfl) ⟨654783, by rfl⟩ : syracuseStep 1746089 = 1309567) B1309567
theorem B6366721 : Blo 1160639 6366721 := bstep (se 2 (by rfl) ⟨2387520, by rfl⟩ : syracuseStep 6366721 = 4775041) B4775041
theorem B1746671 : Blo 1160639 1746671 := bstep (se 1 (by rfl) ⟨1310003, by rfl⟩ : syracuseStep 1746671 = 2620007) B2620007
theorem B57386873 : Blo 1160639 57386873 := bstep (se 2 (by rfl) ⟨21520077, by rfl⟩ : syracuseStep 57386873 = 43040155) B43040155
theorem B1746857 : Blo 1160639 1746857 := bstep (se 2 (by rfl) ⟨655071, by rfl⟩ : syracuseStep 1746857 = 1310143) B1310143
theorem B110274623 : Blo 1160639 110274623 := bstep (se 1 (by rfl) ⟨82705967, by rfl⟩ : syracuseStep 110274623 = 165411935) B165411935
theorem B13248845 : Blo 1160639 13248845 := bstep (se 3 (by rfl) ⟨2484158, by rfl⟩ : syracuseStep 13248845 = 4968317) B4968317
theorem B9415241 : Blo 1160639 9415241 := bstep (se 2 (by rfl) ⟨3530715, by rfl⟩ : syracuseStep 9415241 = 7061431) B7061431
theorem B11184713 : Blo 1160639 11184713 := bstep (se 2 (by rfl) ⟨4194267, by rfl⟩ : syracuseStep 11184713 = 8388535) B8388535
theorem B8825759 : Blo 1160639 8825759 := bstep (se 1 (by rfl) ⟨6619319, by rfl⟩ : syracuseStep 8825759 = 13238639) B13238639
theorem B343715177 : Blo 1160639 343715177 := bstep (se 2 (by rfl) ⟨128893191, by rfl⟩ : syracuseStep 343715177 = 257786383) B257786383
theorem B6631145 : Blo 1160639 6631145 := bstep (se 2 (by rfl) ⟨2486679, by rfl⟩ : syracuseStep 6631145 = 4973359) B4973359
theorem B5879465 : Blo 1160639 5879465 := bstep (se 2 (by rfl) ⟨2204799, by rfl⟩ : syracuseStep 5879465 = 4409599) B4409599
theorem B50935675 : Blo 1160639 50935675 := bstep (se 1 (by rfl) ⟨38201756, by rfl⟩ : syracuseStep 50935675 = 76403513) B76403513
theorem B1161087 : Blo 1160639 1161087 := bstep (se 1 (by rfl) ⟨870815, by rfl⟩ : syracuseStep 1161087 = 1741631) B1741631
theorem B1161307 : Blo 1160639 1161307 := bstep (se 1 (by rfl) ⟨870980, by rfl⟩ : syracuseStep 1161307 = 1741961) B1741961
theorem B1162235 : Blo 1160639 1162235 := bstep (se 1 (by rfl) ⟨871676, by rfl⟩ : syracuseStep 1162235 = 1743353) B1743353
theorem B1162479 : Blo 1160639 1162479 := bstep (se 1 (by rfl) ⟨871859, by rfl⟩ : syracuseStep 1162479 = 1743719) B1743719
theorem B1162495 : Blo 1160639 1162495 := bstep (se 1 (by rfl) ⟨871871, by rfl⟩ : syracuseStep 1162495 = 1743743) B1743743
theorem B7060969 : Blo 1160639 7060969 := bstep (se 2 (by rfl) ⟨2647863, by rfl⟩ : syracuseStep 7060969 = 5295727) B5295727
theorem B1162879 : Blo 1160639 1162879 := bstep (se 1 (by rfl) ⟨872159, by rfl⟩ : syracuseStep 1162879 = 1744319) B1744319
theorem B4964627 : Blo 1160639 4964627 := bstep (se 1 (by rfl) ⟨3723470, by rfl⟩ : syracuseStep 4964627 = 7446941) B7446941
theorem B1163583 : Blo 1160639 1163583 := bstep (se 1 (by rfl) ⟨872687, by rfl⟩ : syracuseStep 1163583 = 1745375) B1745375
theorem B1163903 : Blo 1160639 1163903 := bstep (se 1 (by rfl) ⟨872927, by rfl⟩ : syracuseStep 1163903 = 1745855) B1745855
theorem B5883191 : Blo 1160639 5883191 := bstep (se 1 (by rfl) ⟨4412393, by rfl⟩ : syracuseStep 5883191 = 8824787) B8824787
theorem B23874365 : Blo 1160639 23874365 := bstep (se 3 (by rfl) ⟨4476443, by rfl⟩ : syracuseStep 23874365 = 8952887) B8952887
theorem B17878315 : Blo 1160639 17878315 := bstep (se 1 (by rfl) ⟨13408736, by rfl⟩ : syracuseStep 17878315 = 26817473) B26817473
theorem B10211035 : Blo 1160639 10211035 := bstep (se 1 (by rfl) ⟨7658276, by rfl⟩ : syracuseStep 10211035 = 15316553) B15316553
theorem B5885945 : Blo 1160639 5885945 := bstep (se 2 (by rfl) ⟨2207229, by rfl⟩ : syracuseStep 5885945 = 4414459) B4414459
theorem B3723983 : Blo 1160639 3723983 := bstep (se 1 (by rfl) ⟨2792987, by rfl⟩ : syracuseStep 3723983 = 5585975) B5585975
theorem B2479187 : Blo 1160639 2479187 := bstep (se 1 (by rfl) ⟨1859390, by rfl⟩ : syracuseStep 2479187 = 3718781) B3718781
theorem B5887403 : Blo 1160639 5887403 := bstep (se 1 (by rfl) ⟨4415552, by rfl⟩ : syracuseStep 5887403 = 8831105) B8831105
theorem B3921911 : Blo 1160639 3921911 := bstep (se 1 (by rfl) ⟨2941433, by rfl⟩ : syracuseStep 3921911 = 5882867) B5882867
theorem B6281327 : Blo 1160639 6281327 := bstep (se 1 (by rfl) ⟨4710995, by rfl⟩ : syracuseStep 6281327 = 9421991) B9421991
theorem B2611439 : Blo 1160639 2611439 := bstep (se 1 (by rfl) ⟨1958579, by rfl⟩ : syracuseStep 2611439 = 3917159) B3917159
theorem B6281783 : Blo 1160639 6281783 := bstep (se 1 (by rfl) ⟨4711337, by rfl⟩ : syracuseStep 6281783 = 9422675) B9422675
theorem B3922937 : Blo 1160639 3922937 := bstep (se 2 (by rfl) ⟨1471101, by rfl⟩ : syracuseStep 3922937 = 2942203) B2942203
theorem B42392801 : Blo 1160639 42392801 := bstep (se 2 (by rfl) ⟨15897300, by rfl⟩ : syracuseStep 42392801 = 31794601) B31794601
theorem B2941211 : Blo 1160639 2941211 := bstep (se 1 (by rfl) ⟨2205908, by rfl⟩ : syracuseStep 2941211 = 4411817) B4411817
theorem B2613545 : Blo 1160639 2613545 := bstep (se 2 (by rfl) ⟨980079, by rfl⟩ : syracuseStep 2613545 = 1960159) B1960159
theorem B3924287 : Blo 1160639 3924287 := bstep (se 1 (by rfl) ⟨2943215, by rfl⟩ : syracuseStep 3924287 = 5886431) B5886431
theorem B21226475 : Blo 1160639 21226475 := bstep (se 1 (by rfl) ⟨15919856, by rfl⟩ : syracuseStep 21226475 = 31839713) B31839713
theorem B2614697 : Blo 1160639 2614697 := bstep (se 2 (by rfl) ⟨980511, by rfl⟩ : syracuseStep 2614697 = 1961023) B1961023
theorem B1960591 : Blo 1160639 1960591 := bstep (se 1 (by rfl) ⟨1470443, by rfl⟩ : syracuseStep 1960591 = 2940887) B2940887
theorem B2944937 : Blo 1160639 2944937 := bstep (se 2 (by rfl) ⟨1104351, by rfl⟩ : syracuseStep 2944937 = 2208703) B2208703
theorem B2945231 : Blo 1160639 2945231 := bstep (se 1 (by rfl) ⟨2208923, by rfl⟩ : syracuseStep 2945231 = 4417847) B4417847
theorem B3535265 : Blo 1160639 3535265 := bstep (se 2 (by rfl) ⟨1325724, by rfl⟩ : syracuseStep 3535265 = 2651449) B2651449
theorem B4420079 : Blo 1160639 4420079 := bstep (se 1 (by rfl) ⟨3315059, by rfl⟩ : syracuseStep 4420079 = 6630119) B6630119
theorem B25490375 : Blo 1160639 25490375 := bstep (se 1 (by rfl) ⟨19117781, by rfl⟩ : syracuseStep 25490375 = 38235563) B38235563
theorem B8615321 : Blo 1160639 8615321 := bstep (se 2 (by rfl) ⟨3230745, by rfl⟩ : syracuseStep 8615321 = 6461491) B6461491
theorem B2947063 : Blo 1160639 2947063 := bstep (se 1 (by rfl) ⟨2210297, by rfl⟩ : syracuseStep 2947063 = 4420595) B4420595
theorem B2619719 : Blo 1160639 2619719 := bstep (se 1 (by rfl) ⟨1964789, by rfl⟩ : syracuseStep 2619719 = 3929579) B3929579
theorem B2947711 : Blo 1160639 2947711 := bstep (se 1 (by rfl) ⟨2210783, by rfl⟩ : syracuseStep 2947711 = 4421567) B4421567
theorem B1473643 : Blo 1160639 1473643 := bstep (se 1 (by rfl) ⟨1105232, by rfl⟩ : syracuseStep 1473643 = 2210465) B2210465
theorem B1309999 : Blo 1160639 1309999 := bstep (se 1 (by rfl) ⟨982499, by rfl⟩ : syracuseStep 1309999 = 1964999) B1964999
theorem B20381057 : Blo 1160639 20381057 := bstep (se 2 (by rfl) ⟨7642896, by rfl⟩ : syracuseStep 20381057 = 15285793) B15285793
theorem B1769087 : Blo 1160639 1769087 := bstep (se 1 (by rfl) ⟨1326815, by rfl⟩ : syracuseStep 1769087 = 2653631) B2653631
theorem B3309751 : Blo 1160639 3309751 := bstep (se 1 (by rfl) ⟨2482313, by rfl⟩ : syracuseStep 3309751 = 4964627) B4964627
theorem B4195583 : Blo 1160639 4195583 := bstep (se 1 (by rfl) ⟨3146687, by rfl⟩ : syracuseStep 4195583 = 6293375) B6293375
theorem B8488961 : Blo 1160639 8488961 := bstep (se 2 (by rfl) ⟨3183360, by rfl⟩ : syracuseStep 8488961 = 6366721) B6366721
theorem B1740959 : Blo 1160639 1740959 := bstep (se 1 (by rfl) ⟨1305719, by rfl⟩ : syracuseStep 1740959 = 2611439) B2611439
theorem B1742363 : Blo 1160639 1742363 := bstep (se 1 (by rfl) ⟨1306772, by rfl⟩ : syracuseStep 1742363 = 2613545) B2613545
theorem B1743131 : Blo 1160639 1743131 := bstep (se 1 (by rfl) ⟨1307348, by rfl⟩ : syracuseStep 1743131 = 2614697) B2614697
theorem B5743547 : Blo 1160639 5743547 := bstep (se 1 (by rfl) ⟨4307660, by rfl⟩ : syracuseStep 5743547 = 8615321) B8615321
theorem B1746479 : Blo 1160639 1746479 := bstep (se 1 (by rfl) ⟨1309859, by rfl⟩ : syracuseStep 1746479 = 2619719) B2619719
theorem B1746665 : Blo 1160639 1746665 := bstep (se 2 (by rfl) ⟨654999, by rfl⟩ : syracuseStep 1746665 = 1309999) B1309999
theorem B9414625 : Blo 1160639 9414625 := bstep (se 2 (by rfl) ⟨3530484, by rfl⟩ : syracuseStep 9414625 = 7060969) B7060969
theorem B5878655 : Blo 1160639 5878655 := bstep (se 1 (by rfl) ⟨4408991, by rfl⟩ : syracuseStep 5878655 = 8817983) B8817983
theorem B56603933 : Blo 1160639 56603933 := bstep (se 3 (by rfl) ⟨10613237, by rfl⟩ : syracuseStep 56603933 = 21226475) B21226475
theorem B8369567 : Blo 1160639 8369567 := bstep (se 1 (by rfl) ⟨6277175, by rfl⟩ : syracuseStep 8369567 = 12554351) B12554351
theorem B2209979 : Blo 1160639 2209979 := bstep (se 1 (by rfl) ⟨1657484, by rfl⟩ : syracuseStep 2209979 = 3314969) B3314969
theorem B1161967 : Blo 1160639 1161967 := bstep (se 1 (by rfl) ⟨871475, by rfl⟩ : syracuseStep 1161967 = 1742951) B1742951
theorem B1162011 : Blo 1160639 1162011 := bstep (se 1 (by rfl) ⟨871508, by rfl⟩ : syracuseStep 1162011 = 1743017) B1743017
theorem B1162015 : Blo 1160639 1162015 := bstep (se 1 (by rfl) ⟨871511, by rfl⟩ : syracuseStep 1162015 = 1743023) B1743023
theorem B23837753 : Blo 1160639 23837753 := bstep (se 2 (by rfl) ⟨8939157, by rfl⟩ : syracuseStep 23837753 = 17878315) B17878315
theorem B1162399 : Blo 1160639 1162399 := bstep (se 1 (by rfl) ⟨871799, by rfl⟩ : syracuseStep 1162399 = 1743599) B1743599
theorem B1162623 : Blo 1160639 1162623 := bstep (se 1 (by rfl) ⟨871967, by rfl⟩ : syracuseStep 1162623 = 1743935) B1743935
theorem B28261867 : Blo 1160639 28261867 := bstep (se 1 (by rfl) ⟨21196400, by rfl⟩ : syracuseStep 28261867 = 42392801) B42392801
theorem B13614713 : Blo 1160639 13614713 := bstep (se 2 (by rfl) ⟨5105517, by rfl⟩ : syracuseStep 13614713 = 10211035) B10211035
theorem B1163035 : Blo 1160639 1163035 := bstep (se 1 (by rfl) ⟨872276, by rfl⟩ : syracuseStep 1163035 = 1744553) B1744553
theorem B1163199 : Blo 1160639 1163199 := bstep (se 1 (by rfl) ⟨872399, by rfl⟩ : syracuseStep 1163199 = 1744799) B1744799
theorem B1163931 : Blo 1160639 1163931 := bstep (se 1 (by rfl) ⟨872948, by rfl⟩ : syracuseStep 1163931 = 1745897) B1745897
theorem B1164059 : Blo 1160639 1164059 := bstep (se 1 (by rfl) ⟨873044, by rfl⟩ : syracuseStep 1164059 = 1746089) B1746089
theorem B1164447 : Blo 1160639 1164447 := bstep (se 1 (by rfl) ⟨873335, by rfl⟩ : syracuseStep 1164447 = 1746671) B1746671
theorem B38257915 : Blo 1160639 38257915 := bstep (se 1 (by rfl) ⟨28693436, by rfl⟩ : syracuseStep 38257915 = 57386873) B57386873
theorem B1164571 : Blo 1160639 1164571 := bstep (se 1 (by rfl) ⟨873428, by rfl⟩ : syracuseStep 1164571 = 1746857) B1746857
theorem B73516415 : Blo 1160639 73516415 := bstep (se 1 (by rfl) ⟨55137311, by rfl⟩ : syracuseStep 73516415 = 110274623) B110274623
theorem B8832563 : Blo 1160639 8832563 := bstep (se 1 (by rfl) ⟨6624422, by rfl⟩ : syracuseStep 8832563 = 13248845) B13248845
theorem B6276827 : Blo 1160639 6276827 := bstep (se 1 (by rfl) ⟨4707620, by rfl⟩ : syracuseStep 6276827 = 9415241) B9415241
theorem B7456475 : Blo 1160639 7456475 := bstep (se 1 (by rfl) ⟨5592356, by rfl⟩ : syracuseStep 7456475 = 11184713) B11184713
theorem B5883839 : Blo 1160639 5883839 := bstep (se 1 (by rfl) ⟨4412879, by rfl⟩ : syracuseStep 5883839 = 8825759) B8825759
theorem B67914233 : Blo 1160639 67914233 := bstep (se 2 (by rfl) ⟨25467837, by rfl⟩ : syracuseStep 67914233 = 50935675) B50935675
theorem B16993583 : Blo 1160639 16993583 := bstep (se 1 (by rfl) ⟨12745187, by rfl⟩ : syracuseStep 16993583 = 25490375) B25490375
theorem B916573805 : Blo 1160639 916573805 := bstep (se 3 (by rfl) ⟨171857588, by rfl⟩ : syracuseStep 916573805 = 343715177) B343715177
theorem B3919643 : Blo 1160639 3919643 := bstep (se 1 (by rfl) ⟨2939732, by rfl⟩ : syracuseStep 3919643 = 5879465) B5879465
theorem B13587371 : Blo 1160639 13587371 := bstep (se 1 (by rfl) ⟨10190528, by rfl⟩ : syracuseStep 13587371 = 20381057) B20381057
theorem B3922127 : Blo 1160639 3922127 := bstep (se 1 (by rfl) ⟨2941595, by rfl⟩ : syracuseStep 3922127 = 5883191) B5883191
theorem B9427373 : Blo 1160639 9427373 := bstep (se 3 (by rfl) ⟨1767632, by rfl⟩ : syracuseStep 9427373 = 3535265) B3535265
theorem B3923963 : Blo 1160639 3923963 := bstep (se 1 (by rfl) ⟨2942972, by rfl⟩ : syracuseStep 3923963 = 5885945) B5885945
theorem B6611165 : Blo 1160639 6611165 := bstep (se 3 (by rfl) ⟨1239593, by rfl⟩ : syracuseStep 6611165 = 2479187) B2479187
theorem B2482655 : Blo 1160639 2482655 := bstep (se 1 (by rfl) ⟨1861991, by rfl⟩ : syracuseStep 2482655 = 3723983) B3723983
theorem B2614121 : Blo 1160639 2614121 := bstep (se 2 (by rfl) ⟨980295, by rfl⟩ : syracuseStep 2614121 = 1960591) B1960591
theorem B3924935 : Blo 1160639 3924935 := bstep (se 1 (by rfl) ⟨2943701, by rfl⟩ : syracuseStep 3924935 = 5887403) B5887403
theorem B2614607 : Blo 1160639 2614607 := bstep (se 1 (by rfl) ⟨1960955, by rfl⟩ : syracuseStep 2614607 = 3921911) B3921911
theorem B4187551 : Blo 1160639 4187551 := bstep (se 1 (by rfl) ⟨3140663, by rfl⟩ : syracuseStep 4187551 = 6281327) B6281327
theorem B4187855 : Blo 1160639 4187855 := bstep (se 1 (by rfl) ⟨3140891, by rfl⟩ : syracuseStep 4187855 = 6281783) B6281783
theorem B2615291 : Blo 1160639 2615291 := bstep (se 1 (by rfl) ⟨1961468, by rfl⟩ : syracuseStep 2615291 = 3922937) B3922937
theorem B14903311 : Blo 1160639 14903311 := bstep (se 1 (by rfl) ⟨11177483, by rfl⟩ : syracuseStep 14903311 = 22354967) B22354967
theorem B2386303 : Blo 1160639 2386303 := bstep (se 1 (by rfl) ⟨1789727, by rfl⟩ : syracuseStep 2386303 = 3579455) B3579455
theorem B1960807 : Blo 1160639 1960807 := bstep (se 1 (by rfl) ⟨1470605, by rfl⟩ : syracuseStep 1960807 = 2941211) B2941211
theorem B2616191 : Blo 1160639 2616191 := bstep (se 1 (by rfl) ⟨1962143, by rfl⟩ : syracuseStep 2616191 = 3924287) B3924287
theorem B63664973 : Blo 1160639 63664973 := bstep (se 3 (by rfl) ⟨11937182, by rfl⟩ : syracuseStep 63664973 = 23874365) B23874365
theorem B4420763 : Blo 1160639 4420763 := bstep (se 1 (by rfl) ⟨3315572, by rfl⟩ : syracuseStep 4420763 = 6631145) B6631145
theorem B1963291 : Blo 1160639 1963291 := bstep (se 1 (by rfl) ⟨1472468, by rfl⟩ : syracuseStep 1963291 = 2944937) B2944937
theorem B3929417 : Blo 1160639 3929417 := bstep (se 2 (by rfl) ⟨1473531, by rfl⟩ : syracuseStep 3929417 = 2947063) B2947063
theorem B1963487 : Blo 1160639 1963487 := bstep (se 1 (by rfl) ⟨1472615, by rfl⟩ : syracuseStep 1963487 = 2945231) B2945231
theorem B2946719 : Blo 1160639 2946719 := bstep (se 1 (by rfl) ⟨2210039, by rfl⟩ : syracuseStep 2946719 = 4420079) B4420079
theorem B3930281 : Blo 1160639 3930281 := bstep (se 2 (by rfl) ⟨1473855, by rfl⟩ : syracuseStep 3930281 = 2947711) B2947711
theorem B1964857 : Blo 1160639 1964857 := bstep (se 2 (by rfl) ⟨736821, by rfl⟩ : syracuseStep 1964857 = 1473643) B1473643
theorem B4717565 : Blo 1160639 4717565 := bstep (se 3 (by rfl) ⟨884543, by rfl⟩ : syracuseStep 4717565 = 1769087) B1769087
theorem B6620413 : Blo 1160639 6620413 := bstep (se 3 (by rfl) ⟨1241327, by rfl⟩ : syracuseStep 6620413 = 2482655) B2482655
theorem B12552833 : Blo 1160639 12552833 := bstep (se 2 (by rfl) ⟨4707312, by rfl⟩ : syracuseStep 12552833 = 9414625) B9414625
theorem B1742747 : Blo 1160639 1742747 := bstep (se 1 (by rfl) ⟨1307060, by rfl⟩ : syracuseStep 1742747 = 2614121) B2614121
theorem B1743071 : Blo 1160639 1743071 := bstep (se 1 (by rfl) ⟨1307303, by rfl⟩ : syracuseStep 1743071 = 2614607) B2614607
theorem B2791903 : Blo 1160639 2791903 := bstep (se 1 (by rfl) ⟨2093927, by rfl⟩ : syracuseStep 2791903 = 4187855) B4187855
theorem B1743527 : Blo 1160639 1743527 := bstep (se 1 (by rfl) ⟨1307645, by rfl⟩ : syracuseStep 1743527 = 2615291) B2615291
theorem B1744127 : Blo 1160639 1744127 := bstep (se 1 (by rfl) ⟨1308095, by rfl⟩ : syracuseStep 1744127 = 2616191) B2616191
theorem B42443315 : Blo 1160639 42443315 := bstep (se 1 (by rfl) ⟨31832486, by rfl⟩ : syracuseStep 42443315 = 63664973) B63664973
theorem B5579711 : Blo 1160639 5579711 := bstep (se 1 (by rfl) ⟨4184783, by rfl⟩ : syracuseStep 5579711 = 8369567) B8369567
theorem B2797055 : Blo 1160639 2797055 := bstep (se 1 (by rfl) ⟨2097791, by rfl⟩ : syracuseStep 2797055 = 4195583) B4195583
theorem B5583401 : Blo 1160639 5583401 := bstep (se 2 (by rfl) ⟨2093775, by rfl⟩ : syracuseStep 5583401 = 4187551) B4187551
theorem B12726949 : Blo 1160639 12726949 := bstep (se 4 (by rfl) ⟨1193151, by rfl⟩ : syracuseStep 12726949 = 2386303) B2386303
theorem B19871081 : Blo 1160639 19871081 := bstep (se 2 (by rfl) ⟨7451655, by rfl⟩ : syracuseStep 19871081 = 14903311) B14903311
theorem B1160639 : Blo 1160639 1160639 := bstep (se 1 (by rfl) ⟨870479, by rfl⟩ : syracuseStep 1160639 = 1740959) B1740959
theorem B9058247 : Blo 1160639 9058247 := bstep (se 1 (by rfl) ⟨6793685, by rfl⟩ : syracuseStep 9058247 = 13587371) B13587371
theorem B1161575 : Blo 1160639 1161575 := bstep (se 1 (by rfl) ⟨871181, by rfl⟩ : syracuseStep 1161575 = 1742363) B1742363
theorem B1162087 : Blo 1160639 1162087 := bstep (se 1 (by rfl) ⟨871565, by rfl⟩ : syracuseStep 1162087 = 1743131) B1743131
theorem B4407443 : Blo 1160639 4407443 := bstep (se 1 (by rfl) ⟨3305582, by rfl⟩ : syracuseStep 4407443 = 6611165) B6611165
theorem B1164319 : Blo 1160639 1164319 := bstep (se 1 (by rfl) ⟨873239, by rfl⟩ : syracuseStep 1164319 = 1746479) B1746479
theorem B1164443 : Blo 1160639 1164443 := bstep (se 1 (by rfl) ⟨873332, by rfl⟩ : syracuseStep 1164443 = 1746665) B1746665
theorem B3919103 : Blo 1160639 3919103 := bstep (se 1 (by rfl) ⟨2939327, by rfl⟩ : syracuseStep 3919103 = 5878655) B5878655
theorem B37735955 : Blo 1160639 37735955 := bstep (se 1 (by rfl) ⟨28301966, by rfl⟩ : syracuseStep 37735955 = 56603933) B56603933
theorem B4413001 : Blo 1160639 4413001 := bstep (se 2 (by rfl) ⟨1654875, by rfl⟩ : syracuseStep 4413001 = 3309751) B3309751
theorem B5888375 : Blo 1160639 5888375 := bstep (se 1 (by rfl) ⟨4416281, by rfl⟩ : syracuseStep 5888375 = 8832563) B8832563
theorem B4184551 : Blo 1160639 4184551 := bstep (se 1 (by rfl) ⟨3138413, by rfl⟩ : syracuseStep 4184551 = 6276827) B6276827
theorem B4970983 : Blo 1160639 4970983 := bstep (se 1 (by rfl) ⟨3728237, by rfl⟩ : syracuseStep 4970983 = 7456475) B7456475
theorem B3922559 : Blo 1160639 3922559 := bstep (se 1 (by rfl) ⟨2941919, by rfl⟩ : syracuseStep 3922559 = 5883839) B5883839
theorem B5659307 : Blo 1160639 5659307 := bstep (se 1 (by rfl) ⟨4244480, by rfl⟩ : syracuseStep 5659307 = 8488961) B8488961
theorem B51010553 : Blo 1160639 51010553 := bstep (se 2 (by rfl) ⟨19128957, by rfl⟩ : syracuseStep 51010553 = 38257915) B38257915
theorem B45276155 : Blo 1160639 45276155 := bstep (se 1 (by rfl) ⟨33957116, by rfl⟩ : syracuseStep 45276155 = 67914233) B67914233
theorem B11329055 : Blo 1160639 11329055 := bstep (se 1 (by rfl) ⟨8496791, by rfl⟩ : syracuseStep 11329055 = 16993583) B16993583
theorem B611049203 : Blo 1160639 611049203 := bstep (se 1 (by rfl) ⟨458286902, by rfl⟩ : syracuseStep 611049203 = 916573805) B916573805
theorem B2613095 : Blo 1160639 2613095 := bstep (se 1 (by rfl) ⟨1959821, by rfl⟩ : syracuseStep 2613095 = 3919643) B3919643
theorem B196043773 : Blo 1160639 196043773 := bstep (se 3 (by rfl) ⟨36758207, by rfl⟩ : syracuseStep 196043773 = 73516415) B73516415
theorem B2614409 : Blo 1160639 2614409 := bstep (se 2 (by rfl) ⟨980403, by rfl⟩ : syracuseStep 2614409 = 1960807) B1960807
theorem B2614751 : Blo 1160639 2614751 := bstep (se 1 (by rfl) ⟨1961063, by rfl⟩ : syracuseStep 2614751 = 3922127) B3922127
theorem B6284915 : Blo 1160639 6284915 := bstep (se 1 (by rfl) ⟨4713686, by rfl⟩ : syracuseStep 6284915 = 9427373) B9427373
theorem B2615975 : Blo 1160639 2615975 := bstep (se 1 (by rfl) ⟨1961981, by rfl⟩ : syracuseStep 2615975 = 3923963) B3923963
theorem B3829031 : Blo 1160639 3829031 := bstep (se 1 (by rfl) ⟨2871773, by rfl⟩ : syracuseStep 3829031 = 5743547) B5743547
theorem B2616623 : Blo 1160639 2616623 := bstep (se 1 (by rfl) ⟨1962467, by rfl⟩ : syracuseStep 2616623 = 3924935) B3924935
theorem B2617721 : Blo 1160639 2617721 := bstep (se 2 (by rfl) ⟨981645, by rfl⟩ : syracuseStep 2617721 = 1963291) B1963291
theorem B2947175 : Blo 1160639 2947175 := bstep (se 1 (by rfl) ⟨2210381, by rfl⟩ : syracuseStep 2947175 = 4420763) B4420763
theorem B2619611 : Blo 1160639 2619611 := bstep (se 1 (by rfl) ⟨1964708, by rfl⟩ : syracuseStep 2619611 = 3929417) B3929417
theorem B1308991 : Blo 1160639 1308991 := bstep (se 1 (by rfl) ⟨981743, by rfl⟩ : syracuseStep 1308991 = 1963487) B1963487
theorem B2619809 : Blo 1160639 2619809 := bstep (se 2 (by rfl) ⟨982428, by rfl⟩ : syracuseStep 2619809 = 1964857) B1964857
theorem B1964479 : Blo 1160639 1964479 := bstep (se 1 (by rfl) ⟨1473359, by rfl⟩ : syracuseStep 1964479 = 2946719) B2946719
theorem B2620187 : Blo 1160639 2620187 := bstep (se 1 (by rfl) ⟨1965140, by rfl⟩ : syracuseStep 2620187 = 3930281) B3930281
theorem B1473319 : Blo 1160639 1473319 := bstep (se 1 (by rfl) ⟨1104989, by rfl⟩ : syracuseStep 1473319 = 2209979) B2209979
theorem B37682489 : Blo 1160639 37682489 := bstep (se 2 (by rfl) ⟨14130933, by rfl⟩ : syracuseStep 37682489 = 28261867) B28261867
theorem B3145043 : Blo 1160639 3145043 := bstep (se 1 (by rfl) ⟨2358782, by rfl⟩ : syracuseStep 3145043 = 4717565) B4717565
theorem B15891835 : Blo 1160639 15891835 := bstep (se 1 (by rfl) ⟨11918876, by rfl⟩ : syracuseStep 15891835 = 23837753) B23837753
theorem B9076475 : Blo 1160639 9076475 := bstep (se 1 (by rfl) ⟨6807356, by rfl⟩ : syracuseStep 9076475 = 13614713) B13614713
theorem B261391697 : Blo 1160639 261391697 := bstep (se 2 (by rfl) ⟨98021886, by rfl⟩ : syracuseStep 261391697 = 196043773) B196043773
theorem B22317605 : Blo 1160639 22317605 := bstep (se 4 (by rfl) ⟨2092275, by rfl⟩ : syracuseStep 22317605 = 4184551) B4184551
theorem B3772871 : Blo 1160639 3772871 := bstep (se 1 (by rfl) ⟨2829653, by rfl⟩ : syracuseStep 3772871 = 5659307) B5659307
theorem B30184103 : Blo 1160639 30184103 := bstep (se 1 (by rfl) ⟨22638077, by rfl⟩ : syracuseStep 30184103 = 45276155) B45276155
theorem B1742063 : Blo 1160639 1742063 := bstep (se 1 (by rfl) ⟨1306547, by rfl⟩ : syracuseStep 1742063 = 2613095) B2613095
theorem B1742939 : Blo 1160639 1742939 := bstep (se 1 (by rfl) ⟨1307204, by rfl⟩ : syracuseStep 1742939 = 2614409) B2614409
theorem B1743167 : Blo 1160639 1743167 := bstep (se 1 (by rfl) ⟨1307375, by rfl⟩ : syracuseStep 1743167 = 2614751) B2614751
theorem B1743983 : Blo 1160639 1743983 := bstep (se 1 (by rfl) ⟨1307987, by rfl⟩ : syracuseStep 1743983 = 2615975) B2615975
theorem B1744415 : Blo 1160639 1744415 := bstep (se 1 (by rfl) ⟨1308311, by rfl⟩ : syracuseStep 1744415 = 2616623) B2616623
theorem B1745147 : Blo 1160639 1745147 := bstep (se 1 (by rfl) ⟨1308860, by rfl⟩ : syracuseStep 1745147 = 2617721) B2617721
theorem B1745321 : Blo 1160639 1745321 := bstep (se 2 (by rfl) ⟨654495, by rfl⟩ : syracuseStep 1745321 = 1308991) B1308991
theorem B6627977 : Blo 1160639 6627977 := bstep (se 2 (by rfl) ⟨2485491, by rfl⟩ : syracuseStep 6627977 = 4970983) B4970983
theorem B13247387 : Blo 1160639 13247387 := bstep (se 1 (by rfl) ⟨9935540, by rfl⟩ : syracuseStep 13247387 = 19871081) B19871081
theorem B6038831 : Blo 1160639 6038831 := bstep (se 1 (by rfl) ⟨4529123, by rfl⟩ : syracuseStep 6038831 = 9058247) B9058247
theorem B1746407 : Blo 1160639 1746407 := bstep (se 1 (by rfl) ⟨1309805, by rfl⟩ : syracuseStep 1746407 = 2619611) B2619611
theorem B1746539 : Blo 1160639 1746539 := bstep (se 1 (by rfl) ⟨1309904, by rfl⟩ : syracuseStep 1746539 = 2619809) B2619809
theorem B1746791 : Blo 1160639 1746791 := bstep (se 1 (by rfl) ⟨1310093, by rfl⟩ : syracuseStep 1746791 = 2620187) B2620187
theorem B8827217 : Blo 1160639 8827217 := bstep (se 2 (by rfl) ⟨3310206, by rfl⟩ : syracuseStep 8827217 = 6620413) B6620413
theorem B1161831 : Blo 1160639 1161831 := bstep (se 1 (by rfl) ⟨871373, by rfl⟩ : syracuseStep 1161831 = 1742747) B1742747
theorem B1162047 : Blo 1160639 1162047 := bstep (se 1 (by rfl) ⟨871535, by rfl⟩ : syracuseStep 1162047 = 1743071) B1743071
theorem B1162351 : Blo 1160639 1162351 := bstep (se 1 (by rfl) ⟨871763, by rfl⟩ : syracuseStep 1162351 = 1743527) B1743527
theorem B1162751 : Blo 1160639 1162751 := bstep (se 1 (by rfl) ⟨872063, by rfl⟩ : syracuseStep 1162751 = 1744127) B1744127
theorem B7552703 : Blo 1160639 7552703 := bstep (se 1 (by rfl) ⟨5664527, by rfl⟩ : syracuseStep 7552703 = 11329055) B11329055
theorem B28295543 : Blo 1160639 28295543 := bstep (se 1 (by rfl) ⟨21221657, by rfl⟩ : syracuseStep 28295543 = 42443315) B42443315
theorem B3719807 : Blo 1160639 3719807 := bstep (se 1 (by rfl) ⟨2789855, by rfl⟩ : syracuseStep 3719807 = 5579711) B5579711
theorem B33474221 : Blo 1160639 33474221 := bstep (se 3 (by rfl) ⟨6276416, by rfl⟩ : syracuseStep 33474221 = 12552833) B12552833
theorem B5884001 : Blo 1160639 5884001 := bstep (se 2 (by rfl) ⟨2206500, by rfl⟩ : syracuseStep 5884001 = 4413001) B4413001
theorem B3722267 : Blo 1160639 3722267 := bstep (se 1 (by rfl) ⟨2791700, by rfl⟩ : syracuseStep 3722267 = 5583401) B5583401
theorem B3722537 : Blo 1160639 3722537 := bstep (se 2 (by rfl) ⟨1395951, by rfl⟩ : syracuseStep 3722537 = 2791903) B2791903
theorem B21189113 : Blo 1160639 21189113 := bstep (se 2 (by rfl) ⟨7945917, by rfl⟩ : syracuseStep 21189113 = 15891835) B15891835
theorem B25121659 : Blo 1160639 25121659 := bstep (se 1 (by rfl) ⟨18841244, by rfl⟩ : syracuseStep 25121659 = 37682489) B37682489
theorem B6050983 : Blo 1160639 6050983 := bstep (se 1 (by rfl) ⟨4538237, by rfl⟩ : syracuseStep 6050983 = 9076475) B9076475
theorem B2938295 : Blo 1160639 2938295 := bstep (se 1 (by rfl) ⟨2203721, by rfl⟩ : syracuseStep 2938295 = 4407443) B4407443
theorem B2612735 : Blo 1160639 2612735 := bstep (se 1 (by rfl) ⟨1959551, by rfl⟩ : syracuseStep 2612735 = 3919103) B3919103
theorem B25157303 : Blo 1160639 25157303 := bstep (se 1 (by rfl) ⟨18867977, by rfl⟩ : syracuseStep 25157303 = 37735955) B37735955
theorem B3925583 : Blo 1160639 3925583 := bstep (se 1 (by rfl) ⟨2944187, by rfl⟩ : syracuseStep 3925583 = 5888375) B5888375
theorem B2615039 : Blo 1160639 2615039 := bstep (se 1 (by rfl) ⟨1961279, by rfl⟩ : syracuseStep 2615039 = 3922559) B3922559
theorem B34007035 : Blo 1160639 34007035 := bstep (se 1 (by rfl) ⟨25505276, by rfl⟩ : syracuseStep 34007035 = 51010553) B51010553
theorem B407366135 : Blo 1160639 407366135 := bstep (se 1 (by rfl) ⟨305524601, by rfl⟩ : syracuseStep 407366135 = 611049203) B611049203
theorem B16969265 : Blo 1160639 16969265 := bstep (se 2 (by rfl) ⟨6363474, by rfl⟩ : syracuseStep 16969265 = 12726949) B12726949
theorem B4189943 : Blo 1160639 4189943 := bstep (se 1 (by rfl) ⟨3142457, by rfl⟩ : syracuseStep 4189943 = 6284915) B6284915
theorem B2552687 : Blo 1160639 2552687 := bstep (se 1 (by rfl) ⟨1914515, by rfl⟩ : syracuseStep 2552687 = 3829031) B3829031
theorem B1864703 : Blo 1160639 1864703 := bstep (se 1 (by rfl) ⟨1398527, by rfl⟩ : syracuseStep 1864703 = 2797055) B2797055
theorem B2619305 : Blo 1160639 2619305 := bstep (se 2 (by rfl) ⟨982239, by rfl⟩ : syracuseStep 2619305 = 1964479) B1964479
theorem B1964425 : Blo 1160639 1964425 := bstep (se 2 (by rfl) ⟨736659, by rfl⟩ : syracuseStep 1964425 = 1473319) B1473319
theorem B1964783 : Blo 1160639 1964783 := bstep (se 1 (by rfl) ⟨1473587, by rfl⟩ : syracuseStep 1964783 = 2947175) B2947175
theorem B2096695 : Blo 1160639 2096695 := bstep (se 1 (by rfl) ⟨1572521, by rfl⟩ : syracuseStep 2096695 = 3145043) B3145043
theorem B174261131 : Blo 1160639 174261131 := bstep (se 1 (by rfl) ⟨130695848, by rfl⟩ : syracuseStep 174261131 = 261391697) B261391697
theorem B22316147 : Blo 1160639 22316147 := bstep (se 1 (by rfl) ⟨16737110, by rfl⟩ : syracuseStep 22316147 = 33474221) B33474221
theorem B14878403 : Blo 1160639 14878403 := bstep (se 1 (by rfl) ⟨11158802, by rfl⟩ : syracuseStep 14878403 = 22317605) B22317605
theorem B14126075 : Blo 1160639 14126075 := bstep (se 1 (by rfl) ⟨10594556, by rfl⟩ : syracuseStep 14126075 = 21189113) B21189113
theorem B1741823 : Blo 1160639 1741823 := bstep (se 1 (by rfl) ⟨1306367, by rfl⟩ : syracuseStep 1741823 = 2612735) B2612735
theorem B33495545 : Blo 1160639 33495545 := bstep (se 2 (by rfl) ⟨12560829, by rfl⟩ : syracuseStep 33495545 = 25121659) B25121659
theorem B1743359 : Blo 1160639 1743359 := bstep (se 1 (by rfl) ⟨1307519, by rfl⟩ : syracuseStep 1743359 = 2615039) B2615039
theorem B8067977 : Blo 1160639 8067977 := bstep (se 2 (by rfl) ⟨3025491, by rfl⟩ : syracuseStep 8067977 = 6050983) B6050983
theorem B11312843 : Blo 1160639 11312843 := bstep (se 1 (by rfl) ⟨8484632, by rfl⟩ : syracuseStep 11312843 = 16969265) B16969265
theorem B2793295 : Blo 1160639 2793295 := bstep (se 1 (by rfl) ⟨2094971, by rfl⟩ : syracuseStep 2793295 = 4189943) B4189943
theorem B11182373 : Blo 1160639 11182373 := bstep (se 4 (by rfl) ⟨1048347, by rfl⟩ : syracuseStep 11182373 = 2096695) B2096695
theorem B1746203 : Blo 1160639 1746203 := bstep (se 1 (by rfl) ⟨1309652, by rfl⟩ : syracuseStep 1746203 = 2619305) B2619305
theorem B80490941 : Blo 1160639 80490941 := bstep (se 3 (by rfl) ⟨15092051, by rfl⟩ : syracuseStep 80490941 = 30184103) B30184103
theorem B16103549 : Blo 1160639 16103549 := bstep (se 3 (by rfl) ⟨3019415, by rfl⟩ : syracuseStep 16103549 = 6038831) B6038831
theorem B1161375 : Blo 1160639 1161375 := bstep (se 1 (by rfl) ⟨871031, by rfl⟩ : syracuseStep 1161375 = 1742063) B1742063
theorem B1161959 : Blo 1160639 1161959 := bstep (se 1 (by rfl) ⟨871469, by rfl⟩ : syracuseStep 1161959 = 1742939) B1742939
theorem B1162111 : Blo 1160639 1162111 := bstep (se 1 (by rfl) ⟨871583, by rfl⟩ : syracuseStep 1162111 = 1743167) B1743167
theorem B1162655 : Blo 1160639 1162655 := bstep (se 1 (by rfl) ⟨871991, by rfl⟩ : syracuseStep 1162655 = 1743983) B1743983
theorem B1162943 : Blo 1160639 1162943 := bstep (se 1 (by rfl) ⟨872207, by rfl⟩ : syracuseStep 1162943 = 1744415) B1744415
theorem B1163431 : Blo 1160639 1163431 := bstep (se 1 (by rfl) ⟨872573, by rfl⟩ : syracuseStep 1163431 = 1745147) B1745147
theorem B1163547 : Blo 1160639 1163547 := bstep (se 1 (by rfl) ⟨872660, by rfl⟩ : syracuseStep 1163547 = 1745321) B1745321
theorem B8831591 : Blo 1160639 8831591 := bstep (se 1 (by rfl) ⟨6623693, by rfl⟩ : syracuseStep 8831591 = 13247387) B13247387
theorem B1164271 : Blo 1160639 1164271 := bstep (se 1 (by rfl) ⟨873203, by rfl⟩ : syracuseStep 1164271 = 1746407) B1746407
theorem B1164359 : Blo 1160639 1164359 := bstep (se 1 (by rfl) ⟨873269, by rfl⟩ : syracuseStep 1164359 = 1746539) B1746539
theorem B1164527 : Blo 1160639 1164527 := bstep (se 1 (by rfl) ⟨873395, by rfl⟩ : syracuseStep 1164527 = 1746791) B1746791
theorem B5884811 : Blo 1160639 5884811 := bstep (se 1 (by rfl) ⟨4413608, by rfl⟩ : syracuseStep 5884811 = 8827217) B8827217
theorem B5035135 : Blo 1160639 5035135 := bstep (se 1 (by rfl) ⟨3776351, by rfl⟩ : syracuseStep 5035135 = 7552703) B7552703
theorem B18863695 : Blo 1160639 18863695 := bstep (se 1 (by rfl) ⟨14147771, by rfl⟩ : syracuseStep 18863695 = 28295543) B28295543
theorem B2479871 : Blo 1160639 2479871 := bstep (se 1 (by rfl) ⟨1859903, by rfl⟩ : syracuseStep 2479871 = 3719807) B3719807
theorem B3922667 : Blo 1160639 3922667 := bstep (se 1 (by rfl) ⟨2942000, by rfl⟩ : syracuseStep 3922667 = 5884001) B5884001
theorem B2481511 : Blo 1160639 2481511 := bstep (se 1 (by rfl) ⟨1861133, by rfl⟩ : syracuseStep 2481511 = 3722267) B3722267
theorem B2481691 : Blo 1160639 2481691 := bstep (se 1 (by rfl) ⟨1861268, by rfl⟩ : syracuseStep 2481691 = 3722537) B3722537
theorem B45342713 : Blo 1160639 45342713 := bstep (se 2 (by rfl) ⟨17003517, by rfl⟩ : syracuseStep 45342713 = 34007035) B34007035
theorem B2515247 : Blo 1160639 2515247 := bstep (se 1 (by rfl) ⟨1886435, by rfl⟩ : syracuseStep 2515247 = 3772871) B3772871
theorem B1958863 : Blo 1160639 1958863 := bstep (se 1 (by rfl) ⟨1469147, by rfl⟩ : syracuseStep 1958863 = 2938295) B2938295
theorem B16771535 : Blo 1160639 16771535 := bstep (se 1 (by rfl) ⟨12578651, by rfl⟩ : syracuseStep 16771535 = 25157303) B25157303
theorem B4418651 : Blo 1160639 4418651 := bstep (se 1 (by rfl) ⟨3313988, by rfl⟩ : syracuseStep 4418651 = 6627977) B6627977
theorem B2617055 : Blo 1160639 2617055 := bstep (se 1 (by rfl) ⟨1962791, by rfl⟩ : syracuseStep 2617055 = 3925583) B3925583
theorem B271577423 : Blo 1160639 271577423 := bstep (se 1 (by rfl) ⟨203683067, by rfl⟩ : syracuseStep 271577423 = 407366135) B407366135
theorem B2619233 : Blo 1160639 2619233 := bstep (se 2 (by rfl) ⟨982212, by rfl⟩ : syracuseStep 2619233 = 1964425) B1964425
theorem B1701791 : Blo 1160639 1701791 := bstep (se 1 (by rfl) ⟨1276343, by rfl⟩ : syracuseStep 1701791 = 2552687) B2552687
theorem B1243135 : Blo 1160639 1243135 := bstep (se 1 (by rfl) ⟨932351, by rfl⟩ : syracuseStep 1243135 = 1864703) B1864703
theorem B1309855 : Blo 1160639 1309855 := bstep (se 1 (by rfl) ⟨982391, by rfl⟩ : syracuseStep 1309855 = 1964783) B1964783
theorem B14877431 : Blo 1160639 14877431 := bstep (se 1 (by rfl) ⟨11158073, by rfl⟩ : syracuseStep 14877431 = 22316147) B22316147
theorem B5378651 : Blo 1160639 5378651 := bstep (se 1 (by rfl) ⟨4033988, by rfl⟩ : syracuseStep 5378651 = 8067977) B8067977
theorem B1676831 : Blo 1160639 1676831 := bstep (se 1 (by rfl) ⟨1257623, by rfl⟩ : syracuseStep 1676831 = 2515247) B2515247
theorem B11181023 : Blo 1160639 11181023 := bstep (se 1 (by rfl) ⟨8385767, by rfl⟩ : syracuseStep 11181023 = 16771535) B16771535
theorem B1744703 : Blo 1160639 1744703 := bstep (se 1 (by rfl) ⟨1308527, by rfl⟩ : syracuseStep 1744703 = 2617055) B2617055
theorem B181051615 : Blo 1160639 181051615 := bstep (se 1 (by rfl) ⟨135788711, by rfl⟩ : syracuseStep 181051615 = 271577423) B271577423
theorem B1746155 : Blo 1160639 1746155 := bstep (se 1 (by rfl) ⟨1309616, by rfl⟩ : syracuseStep 1746155 = 2619233) B2619233
theorem B1746473 : Blo 1160639 1746473 := bstep (se 2 (by rfl) ⟨654927, by rfl⟩ : syracuseStep 1746473 = 1309855) B1309855
theorem B116174087 : Blo 1160639 116174087 := bstep (se 1 (by rfl) ⟨87130565, by rfl⟩ : syracuseStep 116174087 = 174261131) B174261131
theorem B9417383 : Blo 1160639 9417383 := bstep (se 1 (by rfl) ⟨7063037, by rfl⟩ : syracuseStep 9417383 = 14126075) B14126075
theorem B1161215 : Blo 1160639 1161215 := bstep (se 1 (by rfl) ⟨870911, by rfl⟩ : syracuseStep 1161215 = 1741823) B1741823
theorem B1653247 : Blo 1160639 1653247 := bstep (se 1 (by rfl) ⟨1239935, by rfl⟩ : syracuseStep 1653247 = 2479871) B2479871
theorem B22330363 : Blo 1160639 22330363 := bstep (se 1 (by rfl) ⟨16747772, by rfl⟩ : syracuseStep 22330363 = 33495545) B33495545
theorem B1162239 : Blo 1160639 1162239 := bstep (se 1 (by rfl) ⟨871679, by rfl⟩ : syracuseStep 1162239 = 1743359) B1743359
theorem B30228475 : Blo 1160639 30228475 := bstep (se 1 (by rfl) ⟨22671356, by rfl⟩ : syracuseStep 30228475 = 45342713) B45342713
theorem B7454915 : Blo 1160639 7454915 := bstep (se 1 (by rfl) ⟨5591186, by rfl⟩ : syracuseStep 7454915 = 11182373) B11182373
theorem B1164135 : Blo 1160639 1164135 := bstep (se 1 (by rfl) ⟨873101, by rfl⟩ : syracuseStep 1164135 = 1746203) B1746203
theorem B25151593 : Blo 1160639 25151593 := bstep (se 2 (by rfl) ⟨9431847, by rfl⟩ : syracuseStep 25151593 = 18863695) B18863695
theorem B1657513 : Blo 1160639 1657513 := bstep (se 2 (by rfl) ⟨621567, by rfl⟩ : syracuseStep 1657513 = 1243135) B1243135
theorem B53660627 : Blo 1160639 53660627 := bstep (se 1 (by rfl) ⟨40245470, by rfl⟩ : syracuseStep 53660627 = 80490941) B80490941
theorem B10735699 : Blo 1160639 10735699 := bstep (se 1 (by rfl) ⟨8051774, by rfl⟩ : syracuseStep 10735699 = 16103549) B16103549
theorem B30167581 : Blo 1160639 30167581 := bstep (se 3 (by rfl) ⟨5656421, by rfl⟩ : syracuseStep 30167581 = 11312843) B11312843
theorem B3724393 : Blo 1160639 3724393 := bstep (se 2 (by rfl) ⟨1396647, by rfl⟩ : syracuseStep 3724393 = 2793295) B2793295
theorem B5887727 : Blo 1160639 5887727 := bstep (se 1 (by rfl) ⟨4415795, by rfl⟩ : syracuseStep 5887727 = 8831591) B8831591
theorem B9918935 : Blo 1160639 9918935 := bstep (se 1 (by rfl) ⟨7439201, by rfl⟩ : syracuseStep 9918935 = 14878403) B14878403
theorem B2611817 : Blo 1160639 2611817 := bstep (se 2 (by rfl) ⟨979431, by rfl⟩ : syracuseStep 2611817 = 1958863) B1958863
theorem B3923207 : Blo 1160639 3923207 := bstep (se 1 (by rfl) ⟨2942405, by rfl⟩ : syracuseStep 3923207 = 5884811) B5884811
theorem B2615111 : Blo 1160639 2615111 := bstep (se 1 (by rfl) ⟨1961333, by rfl⟩ : syracuseStep 2615111 = 3922667) B3922667
theorem B6713513 : Blo 1160639 6713513 := bstep (se 2 (by rfl) ⟨2517567, by rfl⟩ : syracuseStep 6713513 = 5035135) B5035135
theorem B2945767 : Blo 1160639 2945767 := bstep (se 1 (by rfl) ⟨2209325, by rfl⟩ : syracuseStep 2945767 = 4418651) B4418651
theorem B18152437 : Blo 1160639 18152437 := bstep (se 5 (by rfl) ⟨850895, by rfl⟩ : syracuseStep 18152437 = 1701791) B1701791
theorem B3308681 : Blo 1160639 3308681 := bstep (se 2 (by rfl) ⟨1240755, by rfl⟩ : syracuseStep 3308681 = 2481511) B2481511
theorem B3308921 : Blo 1160639 3308921 := bstep (se 2 (by rfl) ⟨1240845, by rfl⟩ : syracuseStep 3308921 = 2481691) B2481691
theorem B241402153 : Blo 1160639 241402153 := bstep (se 2 (by rfl) ⟨90525807, by rfl⟩ : syracuseStep 241402153 = 181051615) B181051615
theorem B1741211 : Blo 1160639 1741211 := bstep (se 1 (by rfl) ⟨1305908, by rfl⟩ : syracuseStep 1741211 = 2611817) B2611817
theorem B1743407 : Blo 1160639 1743407 := bstep (se 1 (by rfl) ⟨1307555, by rfl⟩ : syracuseStep 1743407 = 2615111) B2615111
theorem B2204329 : Blo 1160639 2204329 := bstep (se 2 (by rfl) ⟨826623, by rfl⟩ : syracuseStep 2204329 = 1653247) B1653247
theorem B2205787 : Blo 1160639 2205787 := bstep (se 1 (by rfl) ⟨1654340, by rfl⟩ : syracuseStep 2205787 = 3308681) B3308681
theorem B2205947 : Blo 1160639 2205947 := bstep (se 1 (by rfl) ⟨1654460, by rfl⟩ : syracuseStep 2205947 = 3308921) B3308921
theorem B33535457 : Blo 1160639 33535457 := bstep (se 2 (by rfl) ⟨12575796, by rfl⟩ : syracuseStep 33535457 = 25151593) B25151593
theorem B3585767 : Blo 1160639 3585767 := bstep (se 1 (by rfl) ⟨2689325, by rfl⟩ : syracuseStep 3585767 = 5378651) B5378651
theorem B2210017 : Blo 1160639 2210017 := bstep (se 2 (by rfl) ⟨828756, by rfl⟩ : syracuseStep 2210017 = 1657513) B1657513
theorem B7454015 : Blo 1160639 7454015 := bstep (se 1 (by rfl) ⟨5590511, by rfl⟩ : syracuseStep 7454015 = 11181023) B11181023
theorem B1163135 : Blo 1160639 1163135 := bstep (se 1 (by rfl) ⟨872351, by rfl⟩ : syracuseStep 1163135 = 1744703) B1744703
theorem B40223441 : Blo 1160639 40223441 := bstep (se 2 (by rfl) ⟨15083790, by rfl⟩ : syracuseStep 40223441 = 30167581) B30167581
theorem B1164103 : Blo 1160639 1164103 := bstep (se 1 (by rfl) ⟨873077, by rfl⟩ : syracuseStep 1164103 = 1746155) B1746155
theorem B1164315 : Blo 1160639 1164315 := bstep (se 1 (by rfl) ⟨873236, by rfl⟩ : syracuseStep 1164315 = 1746473) B1746473
theorem B4965857 : Blo 1160639 4965857 := bstep (se 2 (by rfl) ⟨1862196, by rfl⟩ : syracuseStep 4965857 = 3724393) B3724393
theorem B77449391 : Blo 1160639 77449391 := bstep (se 1 (by rfl) ⟨58087043, by rfl⟩ : syracuseStep 77449391 = 116174087) B116174087
theorem B4475675 : Blo 1160639 4475675 := bstep (se 1 (by rfl) ⟨3356756, by rfl⟩ : syracuseStep 4475675 = 6713513) B6713513
theorem B6278255 : Blo 1160639 6278255 := bstep (se 1 (by rfl) ⟨4708691, by rfl⟩ : syracuseStep 6278255 = 9417383) B9417383
theorem B24203249 : Blo 1160639 24203249 := bstep (se 2 (by rfl) ⟨9076218, by rfl⟩ : syracuseStep 24203249 = 18152437) B18152437
theorem B29773817 : Blo 1160639 29773817 := bstep (se 2 (by rfl) ⟨11165181, by rfl⟩ : syracuseStep 29773817 = 22330363) B22330363
theorem B4969943 : Blo 1160639 4969943 := bstep (se 1 (by rfl) ⟨3727457, by rfl⟩ : syracuseStep 4969943 = 7454915) B7454915
theorem B9918287 : Blo 1160639 9918287 := bstep (se 1 (by rfl) ⟨7438715, by rfl⟩ : syracuseStep 9918287 = 14877431) B14877431
theorem B35773751 : Blo 1160639 35773751 := bstep (se 1 (by rfl) ⟨26830313, by rfl⟩ : syracuseStep 35773751 = 53660627) B53660627
theorem B3925151 : Blo 1160639 3925151 := bstep (se 1 (by rfl) ⟨2943863, by rfl⟩ : syracuseStep 3925151 = 5887727) B5887727
theorem B6612623 : Blo 1160639 6612623 := bstep (se 1 (by rfl) ⟨4959467, by rfl⟩ : syracuseStep 6612623 = 9918935) B9918935
theorem B2615471 : Blo 1160639 2615471 := bstep (se 1 (by rfl) ⟨1961603, by rfl⟩ : syracuseStep 2615471 = 3923207) B3923207
theorem B14314265 : Blo 1160639 14314265 := bstep (se 2 (by rfl) ⟨5367849, by rfl⟩ : syracuseStep 14314265 = 10735699) B10735699
theorem B17886197 : Blo 1160639 17886197 := bstep (se 5 (by rfl) ⟨838415, by rfl⟩ : syracuseStep 17886197 = 1676831) B1676831
theorem B3927689 : Blo 1160639 3927689 := bstep (se 2 (by rfl) ⟨1472883, by rfl⟩ : syracuseStep 3927689 = 2945767) B2945767
theorem B40304633 : Blo 1160639 40304633 := bstep (se 2 (by rfl) ⟨15114237, by rfl⟩ : syracuseStep 40304633 = 30228475) B30228475
theorem B3310571 : Blo 1160639 3310571 := bstep (se 1 (by rfl) ⟨2482928, by rfl⟩ : syracuseStep 3310571 = 4965857) B4965857
theorem B3313295 : Blo 1160639 3313295 := bstep (se 1 (by rfl) ⟨2484971, by rfl⟩ : syracuseStep 3313295 = 4969943) B4969943
theorem B1743647 : Blo 1160639 1743647 := bstep (se 1 (by rfl) ⟨1307735, by rfl⟩ : syracuseStep 1743647 = 2615471) B2615471
theorem B9542843 : Blo 1160639 9542843 := bstep (se 1 (by rfl) ⟨7157132, by rfl⟩ : syracuseStep 9542843 = 14314265) B14314265
theorem B11935133 : Blo 1160639 11935133 := bstep (se 3 (by rfl) ⟨2237837, by rfl⟩ : syracuseStep 11935133 = 4475675) B4475675
theorem B22356971 : Blo 1160639 22356971 := bstep (se 1 (by rfl) ⟨16767728, by rfl⟩ : syracuseStep 22356971 = 33535457) B33535457
theorem B26815627 : Blo 1160639 26815627 := bstep (se 1 (by rfl) ⟨20111720, by rfl⟩ : syracuseStep 26815627 = 40223441) B40223441
theorem B16135499 : Blo 1160639 16135499 := bstep (se 1 (by rfl) ⟨12101624, by rfl⟩ : syracuseStep 16135499 = 24203249) B24203249
theorem B1160807 : Blo 1160639 1160807 := bstep (se 1 (by rfl) ⟨870605, by rfl⟩ : syracuseStep 1160807 = 1741211) B1741211
theorem B1162271 : Blo 1160639 1162271 := bstep (se 1 (by rfl) ⟨871703, by rfl⟩ : syracuseStep 1162271 = 1743407) B1743407
theorem B4408415 : Blo 1160639 4408415 := bstep (se 1 (by rfl) ⟨3306311, by rfl⟩ : syracuseStep 4408415 = 6612623) B6612623
theorem B47696525 : Blo 1160639 47696525 := bstep (se 3 (by rfl) ⟨8943098, by rfl⟩ : syracuseStep 47696525 = 17886197) B17886197
theorem B4969343 : Blo 1160639 4969343 := bstep (se 1 (by rfl) ⟨3727007, by rfl⟩ : syracuseStep 4969343 = 7454015) B7454015
theorem B321869537 : Blo 1160639 321869537 := bstep (se 2 (by rfl) ⟨120701076, by rfl⟩ : syracuseStep 321869537 = 241402153) B241402153
theorem B2939105 : Blo 1160639 2939105 := bstep (se 2 (by rfl) ⟨1102164, by rfl⟩ : syracuseStep 2939105 = 2204329) B2204329
theorem B51632927 : Blo 1160639 51632927 := bstep (se 1 (by rfl) ⟨38724695, by rfl⟩ : syracuseStep 51632927 = 77449391) B77449391
theorem B4185503 : Blo 1160639 4185503 := bstep (se 1 (by rfl) ⟨3139127, by rfl⟩ : syracuseStep 4185503 = 6278255) B6278255
theorem B19849211 : Blo 1160639 19849211 := bstep (se 1 (by rfl) ⟨14886908, by rfl⟩ : syracuseStep 19849211 = 29773817) B29773817
theorem B2941049 : Blo 1160639 2941049 := bstep (se 2 (by rfl) ⟨1102893, by rfl⟩ : syracuseStep 2941049 = 2205787) B2205787
theorem B6612191 : Blo 1160639 6612191 := bstep (se 1 (by rfl) ⟨4959143, by rfl⟩ : syracuseStep 6612191 = 9918287) B9918287
theorem B9562045 : Blo 1160639 9562045 := bstep (se 3 (by rfl) ⟨1792883, by rfl⟩ : syracuseStep 9562045 = 3585767) B3585767
theorem B23849167 : Blo 1160639 23849167 := bstep (se 1 (by rfl) ⟨17886875, by rfl⟩ : syracuseStep 23849167 = 35773751) B35773751
theorem B2616767 : Blo 1160639 2616767 := bstep (se 1 (by rfl) ⟨1962575, by rfl⟩ : syracuseStep 2616767 = 3925151) B3925151
theorem B1470631 : Blo 1160639 1470631 := bstep (se 1 (by rfl) ⟨1102973, by rfl⟩ : syracuseStep 1470631 = 2205947) B2205947
theorem B2618459 : Blo 1160639 2618459 := bstep (se 1 (by rfl) ⟨1963844, by rfl⟩ : syracuseStep 2618459 = 3927689) B3927689
theorem B2946689 : Blo 1160639 2946689 := bstep (se 2 (by rfl) ⟨1105008, by rfl⟩ : syracuseStep 2946689 = 2210017) B2210017
theorem B107479021 : Blo 1160639 107479021 := bstep (se 3 (by rfl) ⟨20152316, by rfl⟩ : syracuseStep 107479021 = 40304633) B40304633
theorem B12749393 : Blo 1160639 12749393 := bstep (se 2 (by rfl) ⟨4781022, by rfl⟩ : syracuseStep 12749393 = 9562045) B9562045
theorem B3312895 : Blo 1160639 3312895 := bstep (se 1 (by rfl) ⟨2484671, by rfl⟩ : syracuseStep 3312895 = 4969343) B4969343
theorem B35754169 : Blo 1160639 35754169 := bstep (se 2 (by rfl) ⟨13407813, by rfl⟩ : syracuseStep 35754169 = 26815627) B26815627
theorem B6361895 : Blo 1160639 6361895 := bstep (se 1 (by rfl) ⟨4771421, by rfl⟩ : syracuseStep 6361895 = 9542843) B9542843
theorem B2790335 : Blo 1160639 2790335 := bstep (se 1 (by rfl) ⟨2092751, by rfl⟩ : syracuseStep 2790335 = 4185503) B4185503
theorem B1744511 : Blo 1160639 1744511 := bstep (se 1 (by rfl) ⟨1308383, by rfl⟩ : syracuseStep 1744511 = 2616767) B2616767
theorem B1745639 : Blo 1160639 1745639 := bstep (se 1 (by rfl) ⟨1309229, by rfl⟩ : syracuseStep 1745639 = 2618459) B2618459
theorem B10756999 : Blo 1160639 10756999 := bstep (se 1 (by rfl) ⟨8067749, by rfl⟩ : syracuseStep 10756999 = 16135499) B16135499
theorem B143305361 : Blo 1160639 143305361 := bstep (se 2 (by rfl) ⟨53739510, by rfl⟩ : syracuseStep 143305361 = 107479021) B107479021
theorem B31797683 : Blo 1160639 31797683 := bstep (se 1 (by rfl) ⟨23848262, by rfl⟩ : syracuseStep 31797683 = 47696525) B47696525
theorem B2208863 : Blo 1160639 2208863 := bstep (se 1 (by rfl) ⟨1656647, by rfl⟩ : syracuseStep 2208863 = 3313295) B3313295
theorem B8828189 : Blo 1160639 8828189 := bstep (se 3 (by rfl) ⟨1655285, by rfl⟩ : syracuseStep 8828189 = 3310571) B3310571
theorem B31798889 : Blo 1160639 31798889 := bstep (se 2 (by rfl) ⟨11924583, by rfl⟩ : syracuseStep 31798889 = 23849167) B23849167
theorem B214579691 : Blo 1160639 214579691 := bstep (se 1 (by rfl) ⟨160934768, by rfl⟩ : syracuseStep 214579691 = 321869537) B321869537
theorem B34421951 : Blo 1160639 34421951 := bstep (se 1 (by rfl) ⟨25816463, by rfl⟩ : syracuseStep 34421951 = 51632927) B51632927
theorem B1162431 : Blo 1160639 1162431 := bstep (se 1 (by rfl) ⟨871823, by rfl⟩ : syracuseStep 1162431 = 1743647) B1743647
theorem B4408127 : Blo 1160639 4408127 := bstep (se 1 (by rfl) ⟨3306095, by rfl⟩ : syracuseStep 4408127 = 6612191) B6612191
theorem B2938943 : Blo 1160639 2938943 := bstep (se 1 (by rfl) ⟨2204207, by rfl⟩ : syracuseStep 2938943 = 4408415) B4408415
theorem B1959403 : Blo 1160639 1959403 := bstep (se 1 (by rfl) ⟨1469552, by rfl⟩ : syracuseStep 1959403 = 2939105) B2939105
theorem B7956755 : Blo 1160639 7956755 := bstep (se 1 (by rfl) ⟨5967566, by rfl⟩ : syracuseStep 7956755 = 11935133) B11935133
theorem B13232807 : Blo 1160639 13232807 := bstep (se 1 (by rfl) ⟨9924605, by rfl⟩ : syracuseStep 13232807 = 19849211) B19849211
theorem B1960699 : Blo 1160639 1960699 := bstep (se 1 (by rfl) ⟨1470524, by rfl⟩ : syracuseStep 1960699 = 2941049) B2941049
theorem B1960841 : Blo 1160639 1960841 := bstep (se 2 (by rfl) ⟨735315, by rfl⟩ : syracuseStep 1960841 = 1470631) B1470631
theorem B14904647 : Blo 1160639 14904647 := bstep (se 1 (by rfl) ⟨11178485, by rfl⟩ : syracuseStep 14904647 = 22356971) B22356971
theorem B1964459 : Blo 1160639 1964459 := bstep (se 1 (by rfl) ⟨1473344, by rfl⟩ : syracuseStep 1964459 = 2946689) B2946689
theorem B7440893 : Blo 1160639 7440893 := bstep (se 3 (by rfl) ⟨1395167, by rfl⟩ : syracuseStep 7440893 = 2790335) B2790335
theorem B8821871 : Blo 1160639 8821871 := bstep (se 1 (by rfl) ⟨6616403, by rfl⟩ : syracuseStep 8821871 = 13232807) B13232807
theorem B9936431 : Blo 1160639 9936431 := bstep (se 1 (by rfl) ⟨7452323, by rfl⟩ : syracuseStep 9936431 = 14904647) B14904647
theorem B22947967 : Blo 1160639 22947967 := bstep (se 1 (by rfl) ⟨17210975, by rfl⟩ : syracuseStep 22947967 = 34421951) B34421951
theorem B8499595 : Blo 1160639 8499595 := bstep (se 1 (by rfl) ⟨6374696, by rfl⟩ : syracuseStep 8499595 = 12749393) B12749393
theorem B4241263 : Blo 1160639 4241263 := bstep (se 1 (by rfl) ⟨3180947, by rfl⟩ : syracuseStep 4241263 = 6361895) B6361895
theorem B1163007 : Blo 1160639 1163007 := bstep (se 1 (by rfl) ⟨872255, by rfl⟩ : syracuseStep 1163007 = 1744511) B1744511
theorem B1163759 : Blo 1160639 1163759 := bstep (se 1 (by rfl) ⟨872819, by rfl⟩ : syracuseStep 1163759 = 1745639) B1745639
theorem B95536907 : Blo 1160639 95536907 := bstep (se 1 (by rfl) ⟨71652680, by rfl⟩ : syracuseStep 95536907 = 143305361) B143305361
theorem B5885459 : Blo 1160639 5885459 := bstep (se 1 (by rfl) ⟨4414094, by rfl⟩ : syracuseStep 5885459 = 8828189) B8828189
theorem B143053127 : Blo 1160639 143053127 := bstep (se 1 (by rfl) ⟨107289845, by rfl⟩ : syracuseStep 143053127 = 214579691) B214579691
theorem B2938751 : Blo 1160639 2938751 := bstep (se 1 (by rfl) ⟨2204063, by rfl⟩ : syracuseStep 2938751 = 4408127) B4408127
theorem B14342665 : Blo 1160639 14342665 := bstep (se 2 (by rfl) ⟨5378499, by rfl⟩ : syracuseStep 14342665 = 10756999) B10756999
theorem B2612537 : Blo 1160639 2612537 := bstep (se 2 (by rfl) ⟨979701, by rfl⟩ : syracuseStep 2612537 = 1959403) B1959403
theorem B2614265 : Blo 1160639 2614265 := bstep (se 2 (by rfl) ⟨980349, by rfl⟩ : syracuseStep 2614265 = 1960699) B1960699
theorem B1959295 : Blo 1160639 1959295 := bstep (se 1 (by rfl) ⟨1469471, by rfl⟩ : syracuseStep 1959295 = 2938943) B2938943
theorem B4417193 : Blo 1160639 4417193 := bstep (se 2 (by rfl) ⟨1656447, by rfl⟩ : syracuseStep 4417193 = 3312895) B3312895
theorem B47672225 : Blo 1160639 47672225 := bstep (se 2 (by rfl) ⟨17877084, by rfl⟩ : syracuseStep 47672225 = 35754169) B35754169
theorem B5304503 : Blo 1160639 5304503 := bstep (se 1 (by rfl) ⟨3978377, by rfl⟩ : syracuseStep 5304503 = 7956755) B7956755
theorem B1307227 : Blo 1160639 1307227 := bstep (se 1 (by rfl) ⟨980420, by rfl⟩ : syracuseStep 1307227 = 1960841) B1960841
theorem B21198455 : Blo 1160639 21198455 := bstep (se 1 (by rfl) ⟨15898841, by rfl⟩ : syracuseStep 21198455 = 31797683) B31797683
theorem B1472575 : Blo 1160639 1472575 := bstep (se 1 (by rfl) ⟨1104431, by rfl⟩ : syracuseStep 1472575 = 2208863) B2208863
theorem B21199259 : Blo 1160639 21199259 := bstep (se 1 (by rfl) ⟨15899444, by rfl⟩ : syracuseStep 21199259 = 31798889) B31798889
theorem B1309639 : Blo 1160639 1309639 := bstep (se 1 (by rfl) ⟨982229, by rfl⟩ : syracuseStep 1309639 = 1964459) B1964459
theorem B122389157 : Blo 1160639 122389157 := bstep (se 4 (by rfl) ⟨11473983, by rfl⟩ : syracuseStep 122389157 = 22947967) B22947967
theorem B1741691 : Blo 1160639 1741691 := bstep (se 1 (by rfl) ⟨1306268, by rfl⟩ : syracuseStep 1741691 = 2612537) B2612537
theorem B6624287 : Blo 1160639 6624287 := bstep (se 1 (by rfl) ⟨4968215, by rfl⟩ : syracuseStep 6624287 = 9936431) B9936431
theorem B1742843 : Blo 1160639 1742843 := bstep (se 1 (by rfl) ⟨1307132, by rfl⟩ : syracuseStep 1742843 = 2614265) B2614265
theorem B1742969 : Blo 1160639 1742969 := bstep (se 2 (by rfl) ⟨653613, by rfl⟩ : syracuseStep 1742969 = 1307227) B1307227
theorem B14132303 : Blo 1160639 14132303 := bstep (se 1 (by rfl) ⟨10599227, by rfl⟩ : syracuseStep 14132303 = 21198455) B21198455
theorem B1746185 : Blo 1160639 1746185 := bstep (se 2 (by rfl) ⟨654819, by rfl⟩ : syracuseStep 1746185 = 1309639) B1309639
theorem B14132839 : Blo 1160639 14132839 := bstep (se 1 (by rfl) ⟨10599629, by rfl⟩ : syracuseStep 14132839 = 21199259) B21199259
theorem B4960595 : Blo 1160639 4960595 := bstep (se 1 (by rfl) ⟨3720446, by rfl⟩ : syracuseStep 4960595 = 7440893) B7440893
theorem B95368751 : Blo 1160639 95368751 := bstep (se 1 (by rfl) ⟨71526563, by rfl⟩ : syracuseStep 95368751 = 143053127) B143053127
theorem B5881247 : Blo 1160639 5881247 := bstep (se 1 (by rfl) ⟨4410935, by rfl⟩ : syracuseStep 5881247 = 8821871) B8821871
theorem B5655017 : Blo 1160639 5655017 := bstep (se 2 (by rfl) ⟨2120631, by rfl⟩ : syracuseStep 5655017 = 4241263) B4241263
theorem B19123553 : Blo 1160639 19123553 := bstep (se 2 (by rfl) ⟨7171332, by rfl⟩ : syracuseStep 19123553 = 14342665) B14342665
theorem B63691271 : Blo 1160639 63691271 := bstep (se 1 (by rfl) ⟨47768453, by rfl⟩ : syracuseStep 63691271 = 95536907) B95536907
theorem B2612393 : Blo 1160639 2612393 := bstep (se 2 (by rfl) ⟨979647, by rfl⟩ : syracuseStep 2612393 = 1959295) B1959295
theorem B3923639 : Blo 1160639 3923639 := bstep (se 1 (by rfl) ⟨2942729, by rfl⟩ : syracuseStep 3923639 = 5885459) B5885459
theorem B1959167 : Blo 1160639 1959167 := bstep (se 1 (by rfl) ⟨1469375, by rfl⟩ : syracuseStep 1959167 = 2938751) B2938751
theorem B11332793 : Blo 1160639 11332793 := bstep (se 2 (by rfl) ⟨4249797, by rfl⟩ : syracuseStep 11332793 = 8499595) B8499595
theorem B2944795 : Blo 1160639 2944795 := bstep (se 1 (by rfl) ⟨2208596, by rfl⟩ : syracuseStep 2944795 = 4417193) B4417193
theorem B31781483 : Blo 1160639 31781483 := bstep (se 1 (by rfl) ⟨23836112, by rfl⟩ : syracuseStep 31781483 = 47672225) B47672225
theorem B1963433 : Blo 1160639 1963433 := bstep (se 2 (by rfl) ⟨736287, by rfl⟩ : syracuseStep 1963433 = 1472575) B1472575
theorem B3536335 : Blo 1160639 3536335 := bstep (se 1 (by rfl) ⟨2652251, by rfl⟩ : syracuseStep 3536335 = 5304503) B5304503
theorem B81592771 : Blo 1160639 81592771 := bstep (se 1 (by rfl) ⟨61194578, by rfl⟩ : syracuseStep 81592771 = 122389157) B122389157
theorem B3770011 : Blo 1160639 3770011 := bstep (se 1 (by rfl) ⟨2827508, by rfl⟩ : syracuseStep 3770011 = 5655017) B5655017
theorem B18843785 : Blo 1160639 18843785 := bstep (se 2 (by rfl) ⟨7066419, by rfl⟩ : syracuseStep 18843785 = 14132839) B14132839
theorem B12749035 : Blo 1160639 12749035 := bstep (se 1 (by rfl) ⟨9561776, by rfl⟩ : syracuseStep 12749035 = 19123553) B19123553
theorem B1741595 : Blo 1160639 1741595 := bstep (se 1 (by rfl) ⟨1306196, by rfl⟩ : syracuseStep 1741595 = 2612393) B2612393
theorem B63579167 : Blo 1160639 63579167 := bstep (se 1 (by rfl) ⟨47684375, by rfl⟩ : syracuseStep 63579167 = 95368751) B95368751
theorem B1161127 : Blo 1160639 1161127 := bstep (se 1 (by rfl) ⟨870845, by rfl⟩ : syracuseStep 1161127 = 1741691) B1741691
theorem B1161895 : Blo 1160639 1161895 := bstep (se 1 (by rfl) ⟨871421, by rfl⟩ : syracuseStep 1161895 = 1742843) B1742843
theorem B1161979 : Blo 1160639 1161979 := bstep (se 1 (by rfl) ⟨871484, by rfl⟩ : syracuseStep 1161979 = 1742969) B1742969
theorem B9421535 : Blo 1160639 9421535 := bstep (se 1 (by rfl) ⟨7066151, by rfl⟩ : syracuseStep 9421535 = 14132303) B14132303
theorem B1164123 : Blo 1160639 1164123 := bstep (se 1 (by rfl) ⟨873092, by rfl⟩ : syracuseStep 1164123 = 1746185) B1746185
theorem B7555195 : Blo 1160639 7555195 := bstep (se 1 (by rfl) ⟨5666396, by rfl⟩ : syracuseStep 7555195 = 11332793) B11332793
theorem B21187655 : Blo 1160639 21187655 := bstep (se 1 (by rfl) ⟨15890741, by rfl⟩ : syracuseStep 21187655 = 31781483) B31781483
theorem B3920831 : Blo 1160639 3920831 := bstep (se 1 (by rfl) ⟨2940623, by rfl⟩ : syracuseStep 3920831 = 5881247) B5881247
theorem B4416191 : Blo 1160639 4416191 := bstep (se 1 (by rfl) ⟨3312143, by rfl⟩ : syracuseStep 4416191 = 6624287) B6624287
theorem B42460847 : Blo 1160639 42460847 := bstep (se 1 (by rfl) ⟨31845635, by rfl⟩ : syracuseStep 42460847 = 63691271) B63691271
theorem B3926393 : Blo 1160639 3926393 := bstep (se 2 (by rfl) ⟨1472397, by rfl⟩ : syracuseStep 3926393 = 2944795) B2944795
theorem B2615759 : Blo 1160639 2615759 := bstep (se 1 (by rfl) ⟨1961819, by rfl⟩ : syracuseStep 2615759 = 3923639) B3923639
theorem B1306111 : Blo 1160639 1306111 := bstep (se 1 (by rfl) ⟨979583, by rfl⟩ : syracuseStep 1306111 = 1959167) B1959167
theorem B4715113 : Blo 1160639 4715113 := bstep (se 2 (by rfl) ⟨1768167, by rfl⟩ : syracuseStep 4715113 = 3536335) B3536335
theorem B3307063 : Blo 1160639 3307063 := bstep (se 1 (by rfl) ⟨2480297, by rfl⟩ : syracuseStep 3307063 = 4960595) B4960595
theorem B1308955 : Blo 1160639 1308955 := bstep (se 1 (by rfl) ⟨981716, by rfl⟩ : syracuseStep 1308955 = 1963433) B1963433
theorem B108790361 : Blo 1160639 108790361 := bstep (se 2 (by rfl) ⟨40796385, by rfl⟩ : syracuseStep 108790361 = 81592771) B81592771
theorem B14125103 : Blo 1160639 14125103 := bstep (se 1 (by rfl) ⟨10593827, by rfl⟩ : syracuseStep 14125103 = 21187655) B21187655
theorem B1741481 : Blo 1160639 1741481 := bstep (se 2 (by rfl) ⟨653055, by rfl⟩ : syracuseStep 1741481 = 1306111) B1306111
theorem B1743839 : Blo 1160639 1743839 := bstep (se 1 (by rfl) ⟨1307879, by rfl⟩ : syracuseStep 1743839 = 2615759) B2615759
theorem B1745273 : Blo 1160639 1745273 := bstep (se 2 (by rfl) ⟨654477, by rfl⟩ : syracuseStep 1745273 = 1308955) B1308955
theorem B12562523 : Blo 1160639 12562523 := bstep (se 1 (by rfl) ⟨9421892, by rfl⟩ : syracuseStep 12562523 = 18843785) B18843785
theorem B5026681 : Blo 1160639 5026681 := bstep (se 2 (by rfl) ⟨1885005, by rfl⟩ : syracuseStep 5026681 = 3770011) B3770011
theorem B10073593 : Blo 1160639 10073593 := bstep (se 2 (by rfl) ⟨3777597, by rfl⟩ : syracuseStep 10073593 = 7555195) B7555195
theorem B1161063 : Blo 1160639 1161063 := bstep (se 1 (by rfl) ⟨870797, by rfl⟩ : syracuseStep 1161063 = 1741595) B1741595
theorem B42386111 : Blo 1160639 42386111 := bstep (se 1 (by rfl) ⟨31789583, by rfl⟩ : syracuseStep 42386111 = 63579167) B63579167
theorem B4409417 : Blo 1160639 4409417 := bstep (se 2 (by rfl) ⟨1653531, by rfl⟩ : syracuseStep 4409417 = 3307063) B3307063
theorem B6281023 : Blo 1160639 6281023 := bstep (se 1 (by rfl) ⟨4710767, by rfl⟩ : syracuseStep 6281023 = 9421535) B9421535
theorem B16998713 : Blo 1160639 16998713 := bstep (se 2 (by rfl) ⟨6374517, by rfl⟩ : syracuseStep 16998713 = 12749035) B12749035
theorem B2613887 : Blo 1160639 2613887 := bstep (se 1 (by rfl) ⟨1960415, by rfl⟩ : syracuseStep 2613887 = 3920831) B3920831
theorem B2944127 : Blo 1160639 2944127 := bstep (se 1 (by rfl) ⟨2208095, by rfl⟩ : syracuseStep 2944127 = 4416191) B4416191
theorem B6286817 : Blo 1160639 6286817 := bstep (se 2 (by rfl) ⟨2357556, by rfl⟩ : syracuseStep 6286817 = 4715113) B4715113
theorem B28307231 : Blo 1160639 28307231 := bstep (se 1 (by rfl) ⟨21230423, by rfl⟩ : syracuseStep 28307231 = 42460847) B42460847
theorem B2617595 : Blo 1160639 2617595 := bstep (se 1 (by rfl) ⟨1963196, by rfl⟩ : syracuseStep 2617595 = 3926393) B3926393
theorem B26808965 : Blo 1160639 26808965 := bstep (se 4 (by rfl) ⟨2513340, by rfl⟩ : syracuseStep 26808965 = 5026681) B5026681
theorem B1742591 : Blo 1160639 1742591 := bstep (se 1 (by rfl) ⟨1306943, by rfl⟩ : syracuseStep 1742591 = 2613887) B2613887
theorem B1745063 : Blo 1160639 1745063 := bstep (se 1 (by rfl) ⟨1308797, by rfl⟩ : syracuseStep 1745063 = 2617595) B2617595
theorem B72526907 : Blo 1160639 72526907 := bstep (se 1 (by rfl) ⟨54395180, by rfl⟩ : syracuseStep 72526907 = 108790361) B108790361
theorem B28257407 : Blo 1160639 28257407 := bstep (se 1 (by rfl) ⟨21193055, by rfl⟩ : syracuseStep 28257407 = 42386111) B42386111
theorem B9416735 : Blo 1160639 9416735 := bstep (se 1 (by rfl) ⟨7062551, by rfl⟩ : syracuseStep 9416735 = 14125103) B14125103
theorem B1160987 : Blo 1160639 1160987 := bstep (se 1 (by rfl) ⟨870740, by rfl⟩ : syracuseStep 1160987 = 1741481) B1741481
theorem B1162559 : Blo 1160639 1162559 := bstep (se 1 (by rfl) ⟨871919, by rfl⟩ : syracuseStep 1162559 = 1743839) B1743839
theorem B1163515 : Blo 1160639 1163515 := bstep (se 1 (by rfl) ⟨872636, by rfl⟩ : syracuseStep 1163515 = 1745273) B1745273
theorem B8374697 : Blo 1160639 8374697 := bstep (se 2 (by rfl) ⟨3140511, by rfl⟩ : syracuseStep 8374697 = 6281023) B6281023
theorem B8375015 : Blo 1160639 8375015 := bstep (se 1 (by rfl) ⟨6281261, by rfl⟩ : syracuseStep 8375015 = 12562523) B12562523
theorem B2939611 : Blo 1160639 2939611 := bstep (se 1 (by rfl) ⟨2204708, by rfl⟩ : syracuseStep 2939611 = 4409417) B4409417
theorem B11332475 : Blo 1160639 11332475 := bstep (se 1 (by rfl) ⟨8499356, by rfl⟩ : syracuseStep 11332475 = 16998713) B16998713
theorem B13431457 : Blo 1160639 13431457 := bstep (se 2 (by rfl) ⟨5036796, by rfl⟩ : syracuseStep 13431457 = 10073593) B10073593
theorem B1962751 : Blo 1160639 1962751 := bstep (se 1 (by rfl) ⟨1472063, by rfl⟩ : syracuseStep 1962751 = 2944127) B2944127
theorem B4191211 : Blo 1160639 4191211 := bstep (se 1 (by rfl) ⟨3143408, by rfl⟩ : syracuseStep 4191211 = 6286817) B6286817
theorem B18871487 : Blo 1160639 18871487 := bstep (se 1 (by rfl) ⟨14153615, by rfl⟩ : syracuseStep 18871487 = 28307231) B28307231
theorem B5583131 : Blo 1160639 5583131 := bstep (se 1 (by rfl) ⟨4187348, by rfl⟩ : syracuseStep 5583131 = 8374697) B8374697
theorem B5583343 : Blo 1160639 5583343 := bstep (se 1 (by rfl) ⟨4187507, by rfl⟩ : syracuseStep 5583343 = 8375015) B8375015
theorem B17872643 : Blo 1160639 17872643 := bstep (se 1 (by rfl) ⟨13404482, by rfl⟩ : syracuseStep 17872643 = 26808965) B26808965
theorem B1161727 : Blo 1160639 1161727 := bstep (se 1 (by rfl) ⟨871295, by rfl⟩ : syracuseStep 1161727 = 1742591) B1742591
theorem B1163375 : Blo 1160639 1163375 := bstep (se 1 (by rfl) ⟨872531, by rfl⟩ : syracuseStep 1163375 = 1745063) B1745063
theorem B17908609 : Blo 1160639 17908609 := bstep (se 2 (by rfl) ⟨6715728, by rfl⟩ : syracuseStep 17908609 = 13431457) B13431457
theorem B5588281 : Blo 1160639 5588281 := bstep (se 2 (by rfl) ⟨2095605, by rfl⟩ : syracuseStep 5588281 = 4191211) B4191211
theorem B48351271 : Blo 1160639 48351271 := bstep (se 1 (by rfl) ⟨36263453, by rfl⟩ : syracuseStep 48351271 = 72526907) B72526907
theorem B6277823 : Blo 1160639 6277823 := bstep (se 1 (by rfl) ⟨4708367, by rfl⟩ : syracuseStep 6277823 = 9416735) B9416735
theorem B3919481 : Blo 1160639 3919481 := bstep (se 2 (by rfl) ⟨1469805, by rfl⟩ : syracuseStep 3919481 = 2939611) B2939611
theorem B483518933 : Blo 1160639 483518933 := bstep (se 7 (by rfl) ⟨5666237, by rfl⟩ : syracuseStep 483518933 = 11332475) B11332475
theorem B2617001 : Blo 1160639 2617001 := bstep (se 2 (by rfl) ⟨981375, by rfl⟩ : syracuseStep 2617001 = 1962751) B1962751
theorem B18838271 : Blo 1160639 18838271 := bstep (se 1 (by rfl) ⟨14128703, by rfl⟩ : syracuseStep 18838271 = 28257407) B28257407
theorem B12580991 : Blo 1160639 12580991 := bstep (se 1 (by rfl) ⟨9435743, by rfl⟩ : syracuseStep 12580991 = 18871487) B18871487
theorem B7444457 : Blo 1160639 7444457 := bstep (se 2 (by rfl) ⟨2791671, by rfl⟩ : syracuseStep 7444457 = 5583343) B5583343
theorem B322345955 : Blo 1160639 322345955 := bstep (se 1 (by rfl) ⟨241759466, by rfl⟩ : syracuseStep 322345955 = 483518933) B483518933
theorem B1744667 : Blo 1160639 1744667 := bstep (se 1 (by rfl) ⟨1308500, by rfl⟩ : syracuseStep 1744667 = 2617001) B2617001
theorem B12558847 : Blo 1160639 12558847 := bstep (se 1 (by rfl) ⟨9419135, by rfl⟩ : syracuseStep 12558847 = 18838271) B18838271
theorem B7451041 : Blo 1160639 7451041 := bstep (se 2 (by rfl) ⟨2794140, by rfl⟩ : syracuseStep 7451041 = 5588281) B5588281
theorem B64468361 : Blo 1160639 64468361 := bstep (se 2 (by rfl) ⟨24175635, by rfl⟩ : syracuseStep 64468361 = 48351271) B48351271
theorem B3722087 : Blo 1160639 3722087 := bstep (se 1 (by rfl) ⟨2791565, by rfl⟩ : syracuseStep 3722087 = 5583131) B5583131
theorem B11915095 : Blo 1160639 11915095 := bstep (se 1 (by rfl) ⟨8936321, by rfl⟩ : syracuseStep 11915095 = 17872643) B17872643
theorem B23878145 : Blo 1160639 23878145 := bstep (se 2 (by rfl) ⟨8954304, by rfl⟩ : syracuseStep 23878145 = 17908609) B17908609
theorem B4185215 : Blo 1160639 4185215 := bstep (se 1 (by rfl) ⟨3138911, by rfl⟩ : syracuseStep 4185215 = 6277823) B6277823
theorem B2612987 : Blo 1160639 2612987 := bstep (se 1 (by rfl) ⟨1959740, by rfl⟩ : syracuseStep 2612987 = 3919481) B3919481
theorem B8387327 : Blo 1160639 8387327 := bstep (se 1 (by rfl) ⟨6290495, by rfl⟩ : syracuseStep 8387327 = 12580991) B12580991
theorem B16745129 : Blo 1160639 16745129 := bstep (se 2 (by rfl) ⟨6279423, by rfl⟩ : syracuseStep 16745129 = 12558847) B12558847
theorem B214897303 : Blo 1160639 214897303 := bstep (se 1 (by rfl) ⟨161172977, by rfl⟩ : syracuseStep 214897303 = 322345955) B322345955
theorem B2790143 : Blo 1160639 2790143 := bstep (se 1 (by rfl) ⟨2092607, by rfl⟩ : syracuseStep 2790143 = 4185215) B4185215
theorem B1741991 : Blo 1160639 1741991 := bstep (se 1 (by rfl) ⟨1306493, by rfl⟩ : syracuseStep 1741991 = 2612987) B2612987
theorem B9934721 : Blo 1160639 9934721 := bstep (se 2 (by rfl) ⟨3725520, by rfl⟩ : syracuseStep 9934721 = 7451041) B7451041
theorem B4962971 : Blo 1160639 4962971 := bstep (se 1 (by rfl) ⟨3722228, by rfl⟩ : syracuseStep 4962971 = 7444457) B7444457
theorem B1163111 : Blo 1160639 1163111 := bstep (se 1 (by rfl) ⟨872333, by rfl⟩ : syracuseStep 1163111 = 1744667) B1744667
theorem B42978907 : Blo 1160639 42978907 := bstep (se 1 (by rfl) ⟨32234180, by rfl⟩ : syracuseStep 42978907 = 64468361) B64468361
theorem B5591551 : Blo 1160639 5591551 := bstep (se 1 (by rfl) ⟨4193663, by rfl⟩ : syracuseStep 5591551 = 8387327) B8387327
theorem B2481391 : Blo 1160639 2481391 := bstep (se 1 (by rfl) ⟨1861043, by rfl⟩ : syracuseStep 2481391 = 3722087) B3722087
theorem B15918763 : Blo 1160639 15918763 := bstep (se 1 (by rfl) ⟨11939072, by rfl⟩ : syracuseStep 15918763 = 23878145) B23878145
theorem B15886793 : Blo 1160639 15886793 := bstep (se 2 (by rfl) ⟨5957547, by rfl⟩ : syracuseStep 15886793 = 11915095) B11915095
theorem B6623147 : Blo 1160639 6623147 := bstep (se 1 (by rfl) ⟨4967360, by rfl⟩ : syracuseStep 6623147 = 9934721) B9934721
theorem B286529737 : Blo 1160639 286529737 := bstep (se 2 (by rfl) ⟨107448651, by rfl⟩ : syracuseStep 286529737 = 214897303) B214897303
theorem B10591195 : Blo 1160639 10591195 := bstep (se 1 (by rfl) ⟨7943396, by rfl⟩ : syracuseStep 10591195 = 15886793) B15886793
theorem B229220837 : Blo 1160639 229220837 := bstep (se 4 (by rfl) ⟨21489453, by rfl⟩ : syracuseStep 229220837 = 42978907) B42978907
theorem B1161327 : Blo 1160639 1161327 := bstep (se 1 (by rfl) ⟨870995, by rfl⟩ : syracuseStep 1161327 = 1741991) B1741991
theorem B7455401 : Blo 1160639 7455401 := bstep (se 2 (by rfl) ⟨2795775, by rfl⟩ : syracuseStep 7455401 = 5591551) B5591551
theorem B11163419 : Blo 1160639 11163419 := bstep (se 1 (by rfl) ⟨8372564, by rfl⟩ : syracuseStep 11163419 = 16745129) B16745129
theorem B21225017 : Blo 1160639 21225017 := bstep (se 2 (by rfl) ⟨7959381, by rfl⟩ : syracuseStep 21225017 = 15918763) B15918763
theorem B1860095 : Blo 1160639 1860095 := bstep (se 1 (by rfl) ⟨1395071, by rfl⟩ : syracuseStep 1860095 = 2790143) B2790143
theorem B3308521 : Blo 1160639 3308521 := bstep (se 2 (by rfl) ⟨1240695, by rfl⟩ : syracuseStep 3308521 = 2481391) B2481391
theorem B3308647 : Blo 1160639 3308647 := bstep (se 1 (by rfl) ⟨2481485, by rfl⟩ : syracuseStep 3308647 = 4962971) B4962971
theorem B7442279 : Blo 1160639 7442279 := bstep (se 1 (by rfl) ⟨5581709, by rfl⟩ : syracuseStep 7442279 = 11163419) B11163419
theorem B4960253 : Blo 1160639 4960253 := bstep (se 3 (by rfl) ⟨930047, by rfl⟩ : syracuseStep 4960253 = 1860095) B1860095
theorem B152813891 : Blo 1160639 152813891 := bstep (se 1 (by rfl) ⟨114610418, by rfl⟩ : syracuseStep 152813891 = 229220837) B229220837
theorem B4411361 : Blo 1160639 4411361 := bstep (se 2 (by rfl) ⟨1654260, by rfl⟩ : syracuseStep 4411361 = 3308521) B3308521
theorem B4411529 : Blo 1160639 4411529 := bstep (se 2 (by rfl) ⟨1654323, by rfl⟩ : syracuseStep 4411529 = 3308647) B3308647
theorem B4970267 : Blo 1160639 4970267 := bstep (se 1 (by rfl) ⟨3727700, by rfl⟩ : syracuseStep 4970267 = 7455401) B7455401
theorem B4415431 : Blo 1160639 4415431 := bstep (se 1 (by rfl) ⟨3311573, by rfl⟩ : syracuseStep 4415431 = 6623147) B6623147
theorem B14150011 : Blo 1160639 14150011 := bstep (se 1 (by rfl) ⟨10612508, by rfl⟩ : syracuseStep 14150011 = 21225017) B21225017
theorem B382039649 : Blo 1160639 382039649 := bstep (se 2 (by rfl) ⟨143264868, by rfl⟩ : syracuseStep 382039649 = 286529737) B286529737
theorem B14121593 : Blo 1160639 14121593 := bstep (se 2 (by rfl) ⟨5295597, by rfl⟩ : syracuseStep 14121593 = 10591195) B10591195
theorem B101875927 : Blo 1160639 101875927 := bstep (se 1 (by rfl) ⟨76406945, by rfl⟩ : syracuseStep 101875927 = 152813891) B152813891
theorem B3313511 : Blo 1160639 3313511 := bstep (se 1 (by rfl) ⟨2485133, by rfl⟩ : syracuseStep 3313511 = 4970267) B4970267
theorem B9414395 : Blo 1160639 9414395 := bstep (se 1 (by rfl) ⟨7060796, by rfl⟩ : syracuseStep 9414395 = 14121593) B14121593
theorem B4961519 : Blo 1160639 4961519 := bstep (se 1 (by rfl) ⟨3721139, by rfl⟩ : syracuseStep 4961519 = 7442279) B7442279
theorem B254693099 : Blo 1160639 254693099 := bstep (se 1 (by rfl) ⟨191019824, by rfl⟩ : syracuseStep 254693099 = 382039649) B382039649
theorem B5887241 : Blo 1160639 5887241 := bstep (se 2 (by rfl) ⟨2207715, by rfl⟩ : syracuseStep 5887241 = 4415431) B4415431
theorem B2940907 : Blo 1160639 2940907 := bstep (se 1 (by rfl) ⟨2205680, by rfl⟩ : syracuseStep 2940907 = 4411361) B4411361
theorem B2941019 : Blo 1160639 2941019 := bstep (se 1 (by rfl) ⟨2205764, by rfl⟩ : syracuseStep 2941019 = 4411529) B4411529
theorem B18866681 : Blo 1160639 18866681 := bstep (se 2 (by rfl) ⟨7075005, by rfl⟩ : syracuseStep 18866681 = 14150011) B14150011
theorem B3306835 : Blo 1160639 3306835 := bstep (se 1 (by rfl) ⟨2480126, by rfl⟩ : syracuseStep 3306835 = 4960253) B4960253
theorem B135834569 : Blo 1160639 135834569 := bstep (se 2 (by rfl) ⟨50937963, by rfl⟩ : syracuseStep 135834569 = 101875927) B101875927
theorem B2209007 : Blo 1160639 2209007 := bstep (se 1 (by rfl) ⟨1656755, by rfl⟩ : syracuseStep 2209007 = 3313511) B3313511
theorem B6276263 : Blo 1160639 6276263 := bstep (se 1 (by rfl) ⟨4707197, by rfl⟩ : syracuseStep 6276263 = 9414395) B9414395
theorem B4409113 : Blo 1160639 4409113 := bstep (se 2 (by rfl) ⟨1653417, by rfl⟩ : syracuseStep 4409113 = 3306835) B3306835
theorem B3921209 : Blo 1160639 3921209 := bstep (se 2 (by rfl) ⟨1470453, by rfl⟩ : syracuseStep 3921209 = 2940907) B2940907
theorem B169795399 : Blo 1160639 169795399 := bstep (se 1 (by rfl) ⟨127346549, by rfl⟩ : syracuseStep 169795399 = 254693099) B254693099
theorem B3924827 : Blo 1160639 3924827 := bstep (se 1 (by rfl) ⟨2943620, by rfl⟩ : syracuseStep 3924827 = 5887241) B5887241
theorem B1960679 : Blo 1160639 1960679 := bstep (se 1 (by rfl) ⟨1470509, by rfl⟩ : syracuseStep 1960679 = 2941019) B2941019
theorem B12577787 : Blo 1160639 12577787 := bstep (se 1 (by rfl) ⟨9433340, by rfl⟩ : syracuseStep 12577787 = 18866681) B18866681
theorem B3307679 : Blo 1160639 3307679 := bstep (se 1 (by rfl) ⟨2480759, by rfl⟩ : syracuseStep 3307679 = 4961519) B4961519
theorem B2205119 : Blo 1160639 2205119 := bstep (se 1 (by rfl) ⟨1653839, by rfl⟩ : syracuseStep 2205119 = 3307679) B3307679
theorem B5878817 : Blo 1160639 5878817 := bstep (se 2 (by rfl) ⟨2204556, by rfl⟩ : syracuseStep 5878817 = 4409113) B4409113
theorem B90556379 : Blo 1160639 90556379 := bstep (se 1 (by rfl) ⟨67917284, by rfl⟩ : syracuseStep 90556379 = 135834569) B135834569
theorem B16736701 : Blo 1160639 16736701 := bstep (se 3 (by rfl) ⟨3138131, by rfl⟩ : syracuseStep 16736701 = 6276263) B6276263
theorem B2614139 : Blo 1160639 2614139 := bstep (se 1 (by rfl) ⟨1960604, by rfl⟩ : syracuseStep 2614139 = 3921209) B3921209
theorem B2616551 : Blo 1160639 2616551 := bstep (se 1 (by rfl) ⟨1962413, by rfl⟩ : syracuseStep 2616551 = 3924827) B3924827
theorem B1307119 : Blo 1160639 1307119 := bstep (se 1 (by rfl) ⟨980339, by rfl⟩ : syracuseStep 1307119 = 1960679) B1960679
theorem B8385191 : Blo 1160639 8385191 := bstep (se 1 (by rfl) ⟨6288893, by rfl⟩ : syracuseStep 8385191 = 12577787) B12577787
theorem B1472671 : Blo 1160639 1472671 := bstep (se 1 (by rfl) ⟨1104503, by rfl⟩ : syracuseStep 1472671 = 2209007) B2209007
theorem B226393865 : Blo 1160639 226393865 := bstep (se 2 (by rfl) ⟨84897699, by rfl⟩ : syracuseStep 226393865 = 169795399) B169795399
theorem B22315601 : Blo 1160639 22315601 := bstep (se 2 (by rfl) ⟨8368350, by rfl⟩ : syracuseStep 22315601 = 16736701) B16736701
theorem B1742759 : Blo 1160639 1742759 := bstep (se 1 (by rfl) ⟨1307069, by rfl⟩ : syracuseStep 1742759 = 2614139) B2614139
theorem B1742825 : Blo 1160639 1742825 := bstep (se 2 (by rfl) ⟨653559, by rfl⟩ : syracuseStep 1742825 = 1307119) B1307119
theorem B1744367 : Blo 1160639 1744367 := bstep (se 1 (by rfl) ⟨1308275, by rfl⟩ : syracuseStep 1744367 = 2616551) B2616551
theorem B60370919 : Blo 1160639 60370919 := bstep (se 1 (by rfl) ⟨45278189, by rfl⟩ : syracuseStep 60370919 = 90556379) B90556379
theorem B5590127 : Blo 1160639 5590127 := bstep (se 1 (by rfl) ⟨4192595, by rfl⟩ : syracuseStep 5590127 = 8385191) B8385191
theorem B3919211 : Blo 1160639 3919211 := bstep (se 1 (by rfl) ⟨2939408, by rfl⟩ : syracuseStep 3919211 = 5878817) B5878817
theorem B1470079 : Blo 1160639 1470079 := bstep (se 1 (by rfl) ⟨1102559, by rfl⟩ : syracuseStep 1470079 = 2205119) B2205119
theorem B1963561 : Blo 1160639 1963561 := bstep (se 2 (by rfl) ⟨736335, by rfl⟩ : syracuseStep 1963561 = 1472671) B1472671
theorem B150929243 : Blo 1160639 150929243 := bstep (se 1 (by rfl) ⟨113196932, by rfl⟩ : syracuseStep 150929243 = 226393865) B226393865
theorem B14877067 : Blo 1160639 14877067 := bstep (se 1 (by rfl) ⟨11157800, by rfl⟩ : syracuseStep 14877067 = 22315601) B22315601
theorem B40247279 : Blo 1160639 40247279 := bstep (se 1 (by rfl) ⟨30185459, by rfl⟩ : syracuseStep 40247279 = 60370919) B60370919
theorem B1161839 : Blo 1160639 1161839 := bstep (se 1 (by rfl) ⟨871379, by rfl⟩ : syracuseStep 1161839 = 1742759) B1742759
theorem B1161883 : Blo 1160639 1161883 := bstep (se 1 (by rfl) ⟨871412, by rfl⟩ : syracuseStep 1161883 = 1742825) B1742825
theorem B1162911 : Blo 1160639 1162911 := bstep (se 1 (by rfl) ⟨872183, by rfl⟩ : syracuseStep 1162911 = 1744367) B1744367
theorem B100619495 : Blo 1160639 100619495 := bstep (se 1 (by rfl) ⟨75464621, by rfl⟩ : syracuseStep 100619495 = 150929243) B150929243
theorem B3726751 : Blo 1160639 3726751 := bstep (se 1 (by rfl) ⟨2795063, by rfl⟩ : syracuseStep 3726751 = 5590127) B5590127
theorem B2612807 : Blo 1160639 2612807 := bstep (se 1 (by rfl) ⟨1959605, by rfl⟩ : syracuseStep 2612807 = 3919211) B3919211
theorem B1960105 : Blo 1160639 1960105 := bstep (se 2 (by rfl) ⟨735039, by rfl⟩ : syracuseStep 1960105 = 1470079) B1470079
theorem B2618081 : Blo 1160639 2618081 := bstep (se 2 (by rfl) ⟨981780, by rfl⟩ : syracuseStep 2618081 = 1963561) B1963561
theorem B67079663 : Blo 1160639 67079663 := bstep (se 1 (by rfl) ⟨50309747, by rfl⟩ : syracuseStep 67079663 = 100619495) B100619495
theorem B1741871 : Blo 1160639 1741871 := bstep (se 1 (by rfl) ⟨1306403, by rfl⟩ : syracuseStep 1741871 = 2612807) B2612807
theorem B1745387 : Blo 1160639 1745387 := bstep (se 1 (by rfl) ⟨1309040, by rfl⟩ : syracuseStep 1745387 = 2618081) B2618081
theorem B19836089 : Blo 1160639 19836089 := bstep (se 2 (by rfl) ⟨7438533, by rfl⟩ : syracuseStep 19836089 = 14877067) B14877067
theorem B4969001 : Blo 1160639 4969001 := bstep (se 2 (by rfl) ⟨1863375, by rfl⟩ : syracuseStep 4969001 = 3726751) B3726751
theorem B2613473 : Blo 1160639 2613473 := bstep (se 2 (by rfl) ⟨980052, by rfl⟩ : syracuseStep 2613473 = 1960105) B1960105
theorem B26831519 : Blo 1160639 26831519 := bstep (se 1 (by rfl) ⟨20123639, by rfl⟩ : syracuseStep 26831519 = 40247279) B40247279
theorem B3312667 : Blo 1160639 3312667 := bstep (se 1 (by rfl) ⟨2484500, by rfl⟩ : syracuseStep 3312667 = 4969001) B4969001
theorem B1742315 : Blo 1160639 1742315 := bstep (se 1 (by rfl) ⟨1306736, by rfl⟩ : syracuseStep 1742315 = 2613473) B2613473
theorem B1161247 : Blo 1160639 1161247 := bstep (se 1 (by rfl) ⟨870935, by rfl⟩ : syracuseStep 1161247 = 1741871) B1741871
theorem B1163591 : Blo 1160639 1163591 := bstep (se 1 (by rfl) ⟨872693, by rfl⟩ : syracuseStep 1163591 = 1745387) B1745387
theorem B13224059 : Blo 1160639 13224059 := bstep (se 1 (by rfl) ⟨9918044, by rfl⟩ : syracuseStep 13224059 = 19836089) B19836089
theorem B44719775 : Blo 1160639 44719775 := bstep (se 1 (by rfl) ⟨33539831, by rfl⟩ : syracuseStep 44719775 = 67079663) B67079663
theorem B17887679 : Blo 1160639 17887679 := bstep (se 1 (by rfl) ⟨13415759, by rfl⟩ : syracuseStep 17887679 = 26831519) B26831519
theorem B8816039 : Blo 1160639 8816039 := bstep (se 1 (by rfl) ⟨6612029, by rfl⟩ : syracuseStep 8816039 = 13224059) B13224059
theorem B1161543 : Blo 1160639 1161543 := bstep (se 1 (by rfl) ⟨871157, by rfl⟩ : syracuseStep 1161543 = 1742315) B1742315
theorem B4416889 : Blo 1160639 4416889 := bstep (se 2 (by rfl) ⟨1656333, by rfl⟩ : syracuseStep 4416889 = 3312667) B3312667
theorem B29813183 : Blo 1160639 29813183 := bstep (se 1 (by rfl) ⟨22359887, by rfl⟩ : syracuseStep 29813183 = 44719775) B44719775
theorem B11925119 : Blo 1160639 11925119 := bstep (se 1 (by rfl) ⟨8943839, by rfl⟩ : syracuseStep 11925119 = 17887679) B17887679
theorem B5877359 : Blo 1160639 5877359 := bstep (se 1 (by rfl) ⟨4408019, by rfl⟩ : syracuseStep 5877359 = 8816039) B8816039
theorem B19875455 : Blo 1160639 19875455 := bstep (se 1 (by rfl) ⟨14906591, by rfl⟩ : syracuseStep 19875455 = 29813183) B29813183
theorem B7950079 : Blo 1160639 7950079 := bstep (se 1 (by rfl) ⟨5962559, by rfl⟩ : syracuseStep 7950079 = 11925119) B11925119
theorem B5889185 : Blo 1160639 5889185 := bstep (se 2 (by rfl) ⟨2208444, by rfl⟩ : syracuseStep 5889185 = 4416889) B4416889
theorem B13250303 : Blo 1160639 13250303 := bstep (se 1 (by rfl) ⟨9937727, by rfl⟩ : syracuseStep 13250303 = 19875455) B19875455
theorem B10600105 : Blo 1160639 10600105 := bstep (se 2 (by rfl) ⟨3975039, by rfl⟩ : syracuseStep 10600105 = 7950079) B7950079
theorem B3918239 : Blo 1160639 3918239 := bstep (se 1 (by rfl) ⟨2938679, by rfl⟩ : syracuseStep 3918239 = 5877359) B5877359
theorem B3926123 : Blo 1160639 3926123 := bstep (se 1 (by rfl) ⟨2944592, by rfl⟩ : syracuseStep 3926123 = 5889185) B5889185
theorem B14133473 : Blo 1160639 14133473 := bstep (se 2 (by rfl) ⟨5300052, by rfl⟩ : syracuseStep 14133473 = 10600105) B10600105
theorem B8833535 : Blo 1160639 8833535 := bstep (se 1 (by rfl) ⟨6625151, by rfl⟩ : syracuseStep 8833535 = 13250303) B13250303
theorem B2612159 : Blo 1160639 2612159 := bstep (se 1 (by rfl) ⟨1959119, by rfl⟩ : syracuseStep 2612159 = 3918239) B3918239
theorem B2617415 : Blo 1160639 2617415 := bstep (se 1 (by rfl) ⟨1963061, by rfl⟩ : syracuseStep 2617415 = 3926123) B3926123
theorem B1741439 : Blo 1160639 1741439 := bstep (se 1 (by rfl) ⟨1306079, by rfl⟩ : syracuseStep 1741439 = 2612159) B2612159
theorem B1744943 : Blo 1160639 1744943 := bstep (se 1 (by rfl) ⟨1308707, by rfl⟩ : syracuseStep 1744943 = 2617415) B2617415
theorem B9422315 : Blo 1160639 9422315 := bstep (se 1 (by rfl) ⟨7066736, by rfl⟩ : syracuseStep 9422315 = 14133473) B14133473
theorem B5889023 : Blo 1160639 5889023 := bstep (se 1 (by rfl) ⟨4416767, by rfl⟩ : syracuseStep 5889023 = 8833535) B8833535
theorem B1160959 : Blo 1160639 1160959 := bstep (se 1 (by rfl) ⟨870719, by rfl⟩ : syracuseStep 1160959 = 1741439) B1741439
theorem B1163295 : Blo 1160639 1163295 := bstep (se 1 (by rfl) ⟨872471, by rfl⟩ : syracuseStep 1163295 = 1744943) B1744943
theorem B6281543 : Blo 1160639 6281543 := bstep (se 1 (by rfl) ⟨4711157, by rfl⟩ : syracuseStep 6281543 = 9422315) B9422315
theorem B3926015 : Blo 1160639 3926015 := bstep (se 1 (by rfl) ⟨2944511, by rfl⟩ : syracuseStep 3926015 = 5889023) B5889023
theorem B4187695 : Blo 1160639 4187695 := bstep (se 1 (by rfl) ⟨3140771, by rfl⟩ : syracuseStep 4187695 = 6281543) B6281543
theorem B2617343 : Blo 1160639 2617343 := bstep (se 1 (by rfl) ⟨1963007, by rfl⟩ : syracuseStep 2617343 = 3926015) B3926015
theorem B1744895 : Blo 1160639 1744895 := bstep (se 1 (by rfl) ⟨1308671, by rfl⟩ : syracuseStep 1744895 = 2617343) B2617343
theorem B5583593 : Blo 1160639 5583593 := bstep (se 2 (by rfl) ⟨2093847, by rfl⟩ : syracuseStep 5583593 = 4187695) B4187695
theorem B1163263 : Blo 1160639 1163263 := bstep (se 1 (by rfl) ⟨872447, by rfl⟩ : syracuseStep 1163263 = 1744895) B1744895
theorem B3722395 : Blo 1160639 3722395 := bstep (se 1 (by rfl) ⟨2791796, by rfl⟩ : syracuseStep 3722395 = 5583593) B5583593
theorem B4963193 : Blo 1160639 4963193 := bstep (se 2 (by rfl) ⟨1861197, by rfl⟩ : syracuseStep 4963193 = 3722395) B3722395
theorem B3308795 : Blo 1160639 3308795 := bstep (se 1 (by rfl) ⟨2481596, by rfl⟩ : syracuseStep 3308795 = 4963193) B4963193
theorem B2205863 : Blo 1160639 2205863 := bstep (se 1 (by rfl) ⟨1654397, by rfl⟩ : syracuseStep 2205863 = 3308795) B3308795
theorem B1470575 : Blo 1160639 1470575 := bstep (se 1 (by rfl) ⟨1102931, by rfl⟩ : syracuseStep 1470575 = 2205863) B2205863
theorem B3921533 : Blo 1160639 3921533 := bstep (se 3 (by rfl) ⟨735287, by rfl⟩ : syracuseStep 3921533 = 1470575) B1470575
theorem B2614355 : Blo 1160639 2614355 := bstep (se 1 (by rfl) ⟨1960766, by rfl⟩ : syracuseStep 2614355 = 3921533) B3921533
theorem B1742903 : Blo 1160639 1742903 := bstep (se 1 (by rfl) ⟨1307177, by rfl⟩ : syracuseStep 1742903 = 2614355) B2614355
theorem B1161935 : Blo 1160639 1161935 := bstep (se 1 (by rfl) ⟨871451, by rfl⟩ : syracuseStep 1161935 = 1742903) B1742903

theorem C0 (j : ℕ) (h1 : 290159 ≤ j) (h2 : j ≤ 290858) : Blo 1160639 (4 * j + 3) := by
  interval_cases j
  · exact B1160639
  · exact B1160643
  · exact B1160647
  · exact B1160651
  · exact B1160655
  · exact B1160659
  · exact B1160663
  · exact B1160667
  · exact B1160671
  · exact B1160675
  · exact B1160679
  · exact B1160683
  · exact B1160687
  · exact B1160691
  · exact B1160695
  · exact B1160699
  · exact B1160703
  · exact B1160707
  · exact B1160711
  · exact B1160715
  · exact B1160719
  · exact B1160723
  · exact B1160727
  · exact B1160731
  · exact B1160735
  · exact B1160739
  · exact B1160743
  · exact B1160747
  · exact B1160751
  · exact B1160755
  · exact B1160759
  · exact B1160763
  · exact B1160767
  · exact B1160771
  · exact B1160775
  · exact B1160779
  · exact B1160783
  · exact B1160787
  · exact B1160791
  · exact B1160795
  · exact B1160799
  · exact B1160803
  · exact B1160807
  · exact B1160811
  · exact B1160815
  · exact B1160819
  · exact B1160823
  · exact B1160827
  · exact B1160831
  · exact B1160835
  · exact B1160839
  · exact B1160843
  · exact B1160847
  · exact B1160851
  · exact B1160855
  · exact B1160859
  · exact B1160863
  · exact B1160867
  · exact B1160871
  · exact B1160875
  · exact B1160879
  · exact B1160883
  · exact B1160887
  · exact B1160891
  · exact B1160895
  · exact B1160899
  · exact B1160903
  · exact B1160907
  · exact B1160911
  · exact B1160915
  · exact B1160919
  · exact B1160923
  · exact B1160927
  · exact B1160931
  · exact B1160935
  · exact B1160939
  · exact B1160943
  · exact B1160947
  · exact B1160951
  · exact B1160955
  · exact B1160959
  · exact B1160963
  · exact B1160967
  · exact B1160971
  · exact B1160975
  · exact B1160979
  · exact B1160983
  · exact B1160987
  · exact B1160991
  · exact B1160995
  · exact B1160999
  · exact B1161003
  · exact B1161007
  · exact B1161011
  · exact B1161015
  · exact B1161019
  · exact B1161023
  · exact B1161027
  · exact B1161031
  · exact B1161035
  · exact B1161039
  · exact B1161043
  · exact B1161047
  · exact B1161051
  · exact B1161055
  · exact B1161059
  · exact B1161063
  · exact B1161067
  · exact B1161071
  · exact B1161075
  · exact B1161079
  · exact B1161083
  · exact B1161087
  · exact B1161091
  · exact B1161095
  · exact B1161099
  · exact B1161103
  · exact B1161107
  · exact B1161111
  · exact B1161115
  · exact B1161119
  · exact B1161123
  · exact B1161127
  · exact B1161131
  · exact B1161135
  · exact B1161139
  · exact B1161143
  · exact B1161147
  · exact B1161151
  · exact B1161155
  · exact B1161159
  · exact B1161163
  · exact B1161167
  · exact B1161171
  · exact B1161175
  · exact B1161179
  · exact B1161183
  · exact B1161187
  · exact B1161191
  · exact B1161195
  · exact B1161199
  · exact B1161203
  · exact B1161207
  · exact B1161211
  · exact B1161215
  · exact B1161219
  · exact B1161223
  · exact B1161227
  · exact B1161231
  · exact B1161235
  · exact B1161239
  · exact B1161243
  · exact B1161247
  · exact B1161251
  · exact B1161255
  · exact B1161259
  · exact B1161263
  · exact B1161267
  · exact B1161271
  · exact B1161275
  · exact B1161279
  · exact B1161283
  · exact B1161287
  · exact B1161291
  · exact B1161295
  · exact B1161299
  · exact B1161303
  · exact B1161307
  · exact B1161311
  · exact B1161315
  · exact B1161319
  · exact B1161323
  · exact B1161327
  · exact B1161331
  · exact B1161335
  · exact B1161339
  · exact B1161343
  · exact B1161347
  · exact B1161351
  · exact B1161355
  · exact B1161359
  · exact B1161363
  · exact B1161367
  · exact B1161371
  · exact B1161375
  · exact B1161379
  · exact B1161383
  · exact B1161387
  · exact B1161391
  · exact B1161395
  · exact B1161399
  · exact B1161403
  · exact B1161407
  · exact B1161411
  · exact B1161415
  · exact B1161419
  · exact B1161423
  · exact B1161427
  · exact B1161431
  · exact B1161435
  · exact B1161439
  · exact B1161443
  · exact B1161447
  · exact B1161451
  · exact B1161455
  · exact B1161459
  · exact B1161463
  · exact B1161467
  · exact B1161471
  · exact B1161475
  · exact B1161479
  · exact B1161483
  · exact B1161487
  · exact B1161491
  · exact B1161495
  · exact B1161499
  · exact B1161503
  · exact B1161507
  · exact B1161511
  · exact B1161515
  · exact B1161519
  · exact B1161523
  · exact B1161527
  · exact B1161531
  · exact B1161535
  · exact B1161539
  · exact B1161543
  · exact B1161547
  · exact B1161551
  · exact B1161555
  · exact B1161559
  · exact B1161563
  · exact B1161567
  · exact B1161571
  · exact B1161575
  · exact B1161579
  · exact B1161583
  · exact B1161587
  · exact B1161591
  · exact B1161595
  · exact B1161599
  · exact B1161603
  · exact B1161607
  · exact B1161611
  · exact B1161615
  · exact B1161619
  · exact B1161623
  · exact B1161627
  · exact B1161631
  · exact B1161635
  · exact B1161639
  · exact B1161643
  · exact B1161647
  · exact B1161651
  · exact B1161655
  · exact B1161659
  · exact B1161663
  · exact B1161667
  · exact B1161671
  · exact B1161675
  · exact B1161679
  · exact B1161683
  · exact B1161687
  · exact B1161691
  · exact B1161695
  · exact B1161699
  · exact B1161703
  · exact B1161707
  · exact B1161711
  · exact B1161715
  · exact B1161719
  · exact B1161723
  · exact B1161727
  · exact B1161731
  · exact B1161735
  · exact B1161739
  · exact B1161743
  · exact B1161747
  · exact B1161751
  · exact B1161755
  · exact B1161759
  · exact B1161763
  · exact B1161767
  · exact B1161771
  · exact B1161775
  · exact B1161779
  · exact B1161783
  · exact B1161787
  · exact B1161791
  · exact B1161795
  · exact B1161799
  · exact B1161803
  · exact B1161807
  · exact B1161811
  · exact B1161815
  · exact B1161819
  · exact B1161823
  · exact B1161827
  · exact B1161831
  · exact B1161835
  · exact B1161839
  · exact B1161843
  · exact B1161847
  · exact B1161851
  · exact B1161855
  · exact B1161859
  · exact B1161863
  · exact B1161867
  · exact B1161871
  · exact B1161875
  · exact B1161879
  · exact B1161883
  · exact B1161887
  · exact B1161891
  · exact B1161895
  · exact B1161899
  · exact B1161903
  · exact B1161907
  · exact B1161911
  · exact B1161915
  · exact B1161919
  · exact B1161923
  · exact B1161927
  · exact B1161931
  · exact B1161935
  · exact B1161939
  · exact B1161943
  · exact B1161947
  · exact B1161951
  · exact B1161955
  · exact B1161959
  · exact B1161963
  · exact B1161967
  · exact B1161971
  · exact B1161975
  · exact B1161979
  · exact B1161983
  · exact B1161987
  · exact B1161991
  · exact B1161995
  · exact B1161999
  · exact B1162003
  · exact B1162007
  · exact B1162011
  · exact B1162015
  · exact B1162019
  · exact B1162023
  · exact B1162027
  · exact B1162031
  · exact B1162035
  · exact B1162039
  · exact B1162043
  · exact B1162047
  · exact B1162051
  · exact B1162055
  · exact B1162059
  · exact B1162063
  · exact B1162067
  · exact B1162071
  · exact B1162075
  · exact B1162079
  · exact B1162083
  · exact B1162087
  · exact B1162091
  · exact B1162095
  · exact B1162099
  · exact B1162103
  · exact B1162107
  · exact B1162111
  · exact B1162115
  · exact B1162119
  · exact B1162123
  · exact B1162127
  · exact B1162131
  · exact B1162135
  · exact B1162139
  · exact B1162143
  · exact B1162147
  · exact B1162151
  · exact B1162155
  · exact B1162159
  · exact B1162163
  · exact B1162167
  · exact B1162171
  · exact B1162175
  · exact B1162179
  · exact B1162183
  · exact B1162187
  · exact B1162191
  · exact B1162195
  · exact B1162199
  · exact B1162203
  · exact B1162207
  · exact B1162211
  · exact B1162215
  · exact B1162219
  · exact B1162223
  · exact B1162227
  · exact B1162231
  · exact B1162235
  · exact B1162239
  · exact B1162243
  · exact B1162247
  · exact B1162251
  · exact B1162255
  · exact B1162259
  · exact B1162263
  · exact B1162267
  · exact B1162271
  · exact B1162275
  · exact B1162279
  · exact B1162283
  · exact B1162287
  · exact B1162291
  · exact B1162295
  · exact B1162299
  · exact B1162303
  · exact B1162307
  · exact B1162311
  · exact B1162315
  · exact B1162319
  · exact B1162323
  · exact B1162327
  · exact B1162331
  · exact B1162335
  · exact B1162339
  · exact B1162343
  · exact B1162347
  · exact B1162351
  · exact B1162355
  · exact B1162359
  · exact B1162363
  · exact B1162367
  · exact B1162371
  · exact B1162375
  · exact B1162379
  · exact B1162383
  · exact B1162387
  · exact B1162391
  · exact B1162395
  · exact B1162399
  · exact B1162403
  · exact B1162407
  · exact B1162411
  · exact B1162415
  · exact B1162419
  · exact B1162423
  · exact B1162427
  · exact B1162431
  · exact B1162435
  · exact B1162439
  · exact B1162443
  · exact B1162447
  · exact B1162451
  · exact B1162455
  · exact B1162459
  · exact B1162463
  · exact B1162467
  · exact B1162471
  · exact B1162475
  · exact B1162479
  · exact B1162483
  · exact B1162487
  · exact B1162491
  · exact B1162495
  · exact B1162499
  · exact B1162503
  · exact B1162507
  · exact B1162511
  · exact B1162515
  · exact B1162519
  · exact B1162523
  · exact B1162527
  · exact B1162531
  · exact B1162535
  · exact B1162539
  · exact B1162543
  · exact B1162547
  · exact B1162551
  · exact B1162555
  · exact B1162559
  · exact B1162563
  · exact B1162567
  · exact B1162571
  · exact B1162575
  · exact B1162579
  · exact B1162583
  · exact B1162587
  · exact B1162591
  · exact B1162595
  · exact B1162599
  · exact B1162603
  · exact B1162607
  · exact B1162611
  · exact B1162615
  · exact B1162619
  · exact B1162623
  · exact B1162627
  · exact B1162631
  · exact B1162635
  · exact B1162639
  · exact B1162643
  · exact B1162647
  · exact B1162651
  · exact B1162655
  · exact B1162659
  · exact B1162663
  · exact B1162667
  · exact B1162671
  · exact B1162675
  · exact B1162679
  · exact B1162683
  · exact B1162687
  · exact B1162691
  · exact B1162695
  · exact B1162699
  · exact B1162703
  · exact B1162707
  · exact B1162711
  · exact B1162715
  · exact B1162719
  · exact B1162723
  · exact B1162727
  · exact B1162731
  · exact B1162735
  · exact B1162739
  · exact B1162743
  · exact B1162747
  · exact B1162751
  · exact B1162755
  · exact B1162759
  · exact B1162763
  · exact B1162767
  · exact B1162771
  · exact B1162775
  · exact B1162779
  · exact B1162783
  · exact B1162787
  · exact B1162791
  · exact B1162795
  · exact B1162799
  · exact B1162803
  · exact B1162807
  · exact B1162811
  · exact B1162815
  · exact B1162819
  · exact B1162823
  · exact B1162827
  · exact B1162831
  · exact B1162835
  · exact B1162839
  · exact B1162843
  · exact B1162847
  · exact B1162851
  · exact B1162855
  · exact B1162859
  · exact B1162863
  · exact B1162867
  · exact B1162871
  · exact B1162875
  · exact B1162879
  · exact B1162883
  · exact B1162887
  · exact B1162891
  · exact B1162895
  · exact B1162899
  · exact B1162903
  · exact B1162907
  · exact B1162911
  · exact B1162915
  · exact B1162919
  · exact B1162923
  · exact B1162927
  · exact B1162931
  · exact B1162935
  · exact B1162939
  · exact B1162943
  · exact B1162947
  · exact B1162951
  · exact B1162955
  · exact B1162959
  · exact B1162963
  · exact B1162967
  · exact B1162971
  · exact B1162975
  · exact B1162979
  · exact B1162983
  · exact B1162987
  · exact B1162991
  · exact B1162995
  · exact B1162999
  · exact B1163003
  · exact B1163007
  · exact B1163011
  · exact B1163015
  · exact B1163019
  · exact B1163023
  · exact B1163027
  · exact B1163031
  · exact B1163035
  · exact B1163039
  · exact B1163043
  · exact B1163047
  · exact B1163051
  · exact B1163055
  · exact B1163059
  · exact B1163063
  · exact B1163067
  · exact B1163071
  · exact B1163075
  · exact B1163079
  · exact B1163083
  · exact B1163087
  · exact B1163091
  · exact B1163095
  · exact B1163099
  · exact B1163103
  · exact B1163107
  · exact B1163111
  · exact B1163115
  · exact B1163119
  · exact B1163123
  · exact B1163127
  · exact B1163131
  · exact B1163135
  · exact B1163139
  · exact B1163143
  · exact B1163147
  · exact B1163151
  · exact B1163155
  · exact B1163159
  · exact B1163163
  · exact B1163167
  · exact B1163171
  · exact B1163175
  · exact B1163179
  · exact B1163183
  · exact B1163187
  · exact B1163191
  · exact B1163195
  · exact B1163199
  · exact B1163203
  · exact B1163207
  · exact B1163211
  · exact B1163215
  · exact B1163219
  · exact B1163223
  · exact B1163227
  · exact B1163231
  · exact B1163235
  · exact B1163239
  · exact B1163243
  · exact B1163247
  · exact B1163251
  · exact B1163255
  · exact B1163259
  · exact B1163263
  · exact B1163267
  · exact B1163271
  · exact B1163275
  · exact B1163279
  · exact B1163283
  · exact B1163287
  · exact B1163291
  · exact B1163295
  · exact B1163299
  · exact B1163303
  · exact B1163307
  · exact B1163311
  · exact B1163315
  · exact B1163319
  · exact B1163323
  · exact B1163327
  · exact B1163331
  · exact B1163335
  · exact B1163339
  · exact B1163343
  · exact B1163347
  · exact B1163351
  · exact B1163355
  · exact B1163359
  · exact B1163363
  · exact B1163367
  · exact B1163371
  · exact B1163375
  · exact B1163379
  · exact B1163383
  · exact B1163387
  · exact B1163391
  · exact B1163395
  · exact B1163399
  · exact B1163403
  · exact B1163407
  · exact B1163411
  · exact B1163415
  · exact B1163419
  · exact B1163423
  · exact B1163427
  · exact B1163431
  · exact B1163435

theorem C1 (j : ℕ) (h1 : 290859 ≤ j) (h2 : j ≤ 291159) : Blo 1160639 (4 * j + 3) := by
  interval_cases j
  · exact B1163439
  · exact B1163443
  · exact B1163447
  · exact B1163451
  · exact B1163455
  · exact B1163459
  · exact B1163463
  · exact B1163467
  · exact B1163471
  · exact B1163475
  · exact B1163479
  · exact B1163483
  · exact B1163487
  · exact B1163491
  · exact B1163495
  · exact B1163499
  · exact B1163503
  · exact B1163507
  · exact B1163511
  · exact B1163515
  · exact B1163519
  · exact B1163523
  · exact B1163527
  · exact B1163531
  · exact B1163535
  · exact B1163539
  · exact B1163543
  · exact B1163547
  · exact B1163551
  · exact B1163555
  · exact B1163559
  · exact B1163563
  · exact B1163567
  · exact B1163571
  · exact B1163575
  · exact B1163579
  · exact B1163583
  · exact B1163587
  · exact B1163591
  · exact B1163595
  · exact B1163599
  · exact B1163603
  · exact B1163607
  · exact B1163611
  · exact B1163615
  · exact B1163619
  · exact B1163623
  · exact B1163627
  · exact B1163631
  · exact B1163635
  · exact B1163639
  · exact B1163643
  · exact B1163647
  · exact B1163651
  · exact B1163655
  · exact B1163659
  · exact B1163663
  · exact B1163667
  · exact B1163671
  · exact B1163675
  · exact B1163679
  · exact B1163683
  · exact B1163687
  · exact B1163691
  · exact B1163695
  · exact B1163699
  · exact B1163703
  · exact B1163707
  · exact B1163711
  · exact B1163715
  · exact B1163719
  · exact B1163723
  · exact B1163727
  · exact B1163731
  · exact B1163735
  · exact B1163739
  · exact B1163743
  · exact B1163747
  · exact B1163751
  · exact B1163755
  · exact B1163759
  · exact B1163763
  · exact B1163767
  · exact B1163771
  · exact B1163775
  · exact B1163779
  · exact B1163783
  · exact B1163787
  · exact B1163791
  · exact B1163795
  · exact B1163799
  · exact B1163803
  · exact B1163807
  · exact B1163811
  · exact B1163815
  · exact B1163819
  · exact B1163823
  · exact B1163827
  · exact B1163831
  · exact B1163835
  · exact B1163839
  · exact B1163843
  · exact B1163847
  · exact B1163851
  · exact B1163855
  · exact B1163859
  · exact B1163863
  · exact B1163867
  · exact B1163871
  · exact B1163875
  · exact B1163879
  · exact B1163883
  · exact B1163887
  · exact B1163891
  · exact B1163895
  · exact B1163899
  · exact B1163903
  · exact B1163907
  · exact B1163911
  · exact B1163915
  · exact B1163919
  · exact B1163923
  · exact B1163927
  · exact B1163931
  · exact B1163935
  · exact B1163939
  · exact B1163943
  · exact B1163947
  · exact B1163951
  · exact B1163955
  · exact B1163959
  · exact B1163963
  · exact B1163967
  · exact B1163971
  · exact B1163975
  · exact B1163979
  · exact B1163983
  · exact B1163987
  · exact B1163991
  · exact B1163995
  · exact B1163999
  · exact B1164003
  · exact B1164007
  · exact B1164011
  · exact B1164015
  · exact B1164019
  · exact B1164023
  · exact B1164027
  · exact B1164031
  · exact B1164035
  · exact B1164039
  · exact B1164043
  · exact B1164047
  · exact B1164051
  · exact B1164055
  · exact B1164059
  · exact B1164063
  · exact B1164067
  · exact B1164071
  · exact B1164075
  · exact B1164079
  · exact B1164083
  · exact B1164087
  · exact B1164091
  · exact B1164095
  · exact B1164099
  · exact B1164103
  · exact B1164107
  · exact B1164111
  · exact B1164115
  · exact B1164119
  · exact B1164123
  · exact B1164127
  · exact B1164131
  · exact B1164135
  · exact B1164139
  · exact B1164143
  · exact B1164147
  · exact B1164151
  · exact B1164155
  · exact B1164159
  · exact B1164163
  · exact B1164167
  · exact B1164171
  · exact B1164175
  · exact B1164179
  · exact B1164183
  · exact B1164187
  · exact B1164191
  · exact B1164195
  · exact B1164199
  · exact B1164203
  · exact B1164207
  · exact B1164211
  · exact B1164215
  · exact B1164219
  · exact B1164223
  · exact B1164227
  · exact B1164231
  · exact B1164235
  · exact B1164239
  · exact B1164243
  · exact B1164247
  · exact B1164251
  · exact B1164255
  · exact B1164259
  · exact B1164263
  · exact B1164267
  · exact B1164271
  · exact B1164275
  · exact B1164279
  · exact B1164283
  · exact B1164287
  · exact B1164291
  · exact B1164295
  · exact B1164299
  · exact B1164303
  · exact B1164307
  · exact B1164311
  · exact B1164315
  · exact B1164319
  · exact B1164323
  · exact B1164327
  · exact B1164331
  · exact B1164335
  · exact B1164339
  · exact B1164343
  · exact B1164347
  · exact B1164351
  · exact B1164355
  · exact B1164359
  · exact B1164363
  · exact B1164367
  · exact B1164371
  · exact B1164375
  · exact B1164379
  · exact B1164383
  · exact B1164387
  · exact B1164391
  · exact B1164395
  · exact B1164399
  · exact B1164403
  · exact B1164407
  · exact B1164411
  · exact B1164415
  · exact B1164419
  · exact B1164423
  · exact B1164427
  · exact B1164431
  · exact B1164435
  · exact B1164439
  · exact B1164443
  · exact B1164447
  · exact B1164451
  · exact B1164455
  · exact B1164459
  · exact B1164463
  · exact B1164467
  · exact B1164471
  · exact B1164475
  · exact B1164479
  · exact B1164483
  · exact B1164487
  · exact B1164491
  · exact B1164495
  · exact B1164499
  · exact B1164503
  · exact B1164507
  · exact B1164511
  · exact B1164515
  · exact B1164519
  · exact B1164523
  · exact B1164527
  · exact B1164531
  · exact B1164535
  · exact B1164539
  · exact B1164543
  · exact B1164547
  · exact B1164551
  · exact B1164555
  · exact B1164559
  · exact B1164563
  · exact B1164567
  · exact B1164571
  · exact B1164575
  · exact B1164579
  · exact B1164583
  · exact B1164587
  · exact B1164591
  · exact B1164595
  · exact B1164599
  · exact B1164603
  · exact B1164607
  · exact B1164611
  · exact B1164615
  · exact B1164619
  · exact B1164623
  · exact B1164627
  · exact B1164631
  · exact B1164635
  · exact B1164639

theorem solution (m : ℕ) (hlo : 1160639 ≤ m) (hhi : m ≤ 1164639) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 290159 ≤ j := by omega
    have hj2 : j ≤ 291159 := by omega
    have hb : Blo 1160639 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 290859 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
