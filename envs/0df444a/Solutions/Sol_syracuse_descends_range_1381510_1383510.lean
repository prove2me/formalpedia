-- Prove2me | solution 1 for syracuse_descends_range_1381510_1383510
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:40:22.670591+00:00
-- url     : https://prove2.me/submissions/b9a1b0c5-ce69-4aa8-9851-a2eef711292c

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


theorem B2072597 : Blo 1381510 2072597 := bbase (se 6 (by rfl) ⟨48576, by rfl⟩ : syracuseStep 2072597 = 97153) (by norm_num)
theorem B3498005 : Blo 1381510 3498005 := bbase (se 6 (by rfl) ⟨81984, by rfl⟩ : syracuseStep 3498005 = 163969) (by norm_num)
theorem B2072621 : Blo 1381510 2072621 := bbase (se 3 (by rfl) ⟨388616, by rfl⟩ : syracuseStep 2072621 = 777233) (by norm_num)
theorem B2072645 : Blo 1381510 2072645 := bbase (se 4 (by rfl) ⟨194310, by rfl⟩ : syracuseStep 2072645 = 388621) (by norm_num)
theorem B2072669 : Blo 1381510 2072669 := bbase (se 3 (by rfl) ⟨388625, by rfl⟩ : syracuseStep 2072669 = 777251) (by norm_num)
theorem B2072693 : Blo 1381510 2072693 := bbase (se 5 (by rfl) ⟨97157, by rfl⟩ : syracuseStep 2072693 = 194315) (by norm_num)
theorem B2072717 : Blo 1381510 2072717 := bbase (se 3 (by rfl) ⟨388634, by rfl⟩ : syracuseStep 2072717 = 777269) (by norm_num)
theorem B2072741 : Blo 1381510 2072741 := bbase (se 4 (by rfl) ⟨194319, by rfl⟩ : syracuseStep 2072741 = 388639) (by norm_num)
theorem B1401001 : Blo 1381510 1401001 := bbase (se 2 (by rfl) ⟨525375, by rfl⟩ : syracuseStep 1401001 = 1050751) (by norm_num)
theorem B2072765 : Blo 1381510 2072765 := bbase (se 3 (by rfl) ⟨388643, by rfl⟩ : syracuseStep 2072765 = 777287) (by norm_num)
theorem B2072789 : Blo 1381510 2072789 := bbase (se 7 (by rfl) ⟨24290, by rfl⟩ : syracuseStep 2072789 = 48581) (by norm_num)
theorem B2072813 : Blo 1381510 2072813 := bbase (se 3 (by rfl) ⟨388652, by rfl⟩ : syracuseStep 2072813 = 777305) (by norm_num)
theorem B10494197 : Blo 1381510 10494197 := bbase (se 5 (by rfl) ⟨491915, by rfl⟩ : syracuseStep 10494197 = 983831) (by norm_num)
theorem B5906677 : Blo 1381510 5906677 := bbase (se 5 (by rfl) ⟨276875, by rfl⟩ : syracuseStep 5906677 = 553751) (by norm_num)
theorem B2072837 : Blo 1381510 2072837 := bbase (se 4 (by rfl) ⟨194328, by rfl⟩ : syracuseStep 2072837 = 388657) (by norm_num)
theorem B14180629 : Blo 1381510 14180629 := bbase (se 6 (by rfl) ⟨332358, by rfl⟩ : syracuseStep 14180629 = 664717) (by norm_num)
theorem B9969941 : Blo 1381510 9969941 := bbase (se 6 (by rfl) ⟨233670, by rfl⟩ : syracuseStep 9969941 = 467341) (by norm_num)
theorem B2072861 : Blo 1381510 2072861 := bbase (se 3 (by rfl) ⟨388661, by rfl⟩ : syracuseStep 2072861 = 777323) (by norm_num)
theorem B2072885 : Blo 1381510 2072885 := bbase (se 5 (by rfl) ⟨97166, by rfl⟩ : syracuseStep 2072885 = 194333) (by norm_num)
theorem B6996293 : Blo 1381510 6996293 := bbase (se 4 (by rfl) ⟨655902, by rfl⟩ : syracuseStep 6996293 = 1311805) (by norm_num)
theorem B2072909 : Blo 1381510 2072909 := bbase (se 3 (by rfl) ⟨388670, by rfl⟩ : syracuseStep 2072909 = 777341) (by norm_num)
theorem B2072933 : Blo 1381510 2072933 := bbase (se 4 (by rfl) ⟨194337, by rfl⟩ : syracuseStep 2072933 = 388675) (by norm_num)
theorem B3498349 : Blo 1381510 3498349 := bbase (se 3 (by rfl) ⟨655940, by rfl⟩ : syracuseStep 3498349 = 1311881) (by norm_num)
theorem B8864117 : Blo 1381510 8864117 := bbase (se 5 (by rfl) ⟨415505, by rfl⟩ : syracuseStep 8864117 = 831011) (by norm_num)
theorem B2072957 : Blo 1381510 2072957 := bbase (se 3 (by rfl) ⟨388679, by rfl⟩ : syracuseStep 2072957 = 777359) (by norm_num)
theorem B1401229 : Blo 1381510 1401229 := bbase (se 3 (by rfl) ⟨262730, by rfl⟩ : syracuseStep 1401229 = 525461) (by norm_num)
theorem B2072981 : Blo 1381510 2072981 := bbase (se 6 (by rfl) ⟨48585, by rfl⟩ : syracuseStep 2072981 = 97171) (by norm_num)
theorem B2245013 : Blo 1381510 2245013 := bbase (se 6 (by rfl) ⟨52617, by rfl⟩ : syracuseStep 2245013 = 105235) (by norm_num)
theorem B2523557 : Blo 1381510 2523557 := bbase (se 4 (by rfl) ⟨236583, by rfl⟩ : syracuseStep 2523557 = 473167) (by norm_num)
theorem B2073005 : Blo 1381510 2073005 := bbase (se 3 (by rfl) ⟨388688, by rfl⟩ : syracuseStep 2073005 = 777377) (by norm_num)
theorem B2130349 : Blo 1381510 2130349 := bbase (se 3 (by rfl) ⟨399440, by rfl⟩ : syracuseStep 2130349 = 798881) (by norm_num)
theorem B2073029 : Blo 1381510 2073029 := bbase (se 4 (by rfl) ⟨194346, by rfl⟩ : syracuseStep 2073029 = 388693) (by norm_num)
theorem B2245069 : Blo 1381510 2245069 := bbase (se 3 (by rfl) ⟨420950, by rfl⟩ : syracuseStep 2245069 = 841901) (by norm_num)
theorem B2073053 : Blo 1381510 2073053 := bbase (se 3 (by rfl) ⟨388697, by rfl⟩ : syracuseStep 2073053 = 777395) (by norm_num)
theorem B3498461 : Blo 1381510 3498461 := bbase (se 3 (by rfl) ⟨655961, by rfl⟩ : syracuseStep 3498461 = 1311923) (by norm_num)
theorem B5603813 : Blo 1381510 5603813 := bbase (se 4 (by rfl) ⟨525357, by rfl⟩ : syracuseStep 5603813 = 1050715) (by norm_num)
theorem B2073077 : Blo 1381510 2073077 := bbase (se 5 (by rfl) ⟨97175, by rfl⟩ : syracuseStep 2073077 = 194351) (by norm_num)
theorem B2073101 : Blo 1381510 2073101 := bbase (se 3 (by rfl) ⟨388706, by rfl⟩ : syracuseStep 2073101 = 777413) (by norm_num)
theorem B2073125 : Blo 1381510 2073125 := bbase (se 4 (by rfl) ⟨194355, by rfl⟩ : syracuseStep 2073125 = 388711) (by norm_num)
theorem B2073149 : Blo 1381510 2073149 := bbase (se 3 (by rfl) ⟨388715, by rfl⟩ : syracuseStep 2073149 = 777431) (by norm_num)
theorem B2073173 : Blo 1381510 2073173 := bbase (se 8 (by rfl) ⟨12147, by rfl⟩ : syracuseStep 2073173 = 24295) (by norm_num)
theorem B7873109 : Blo 1381510 7873109 := bbase (se 8 (by rfl) ⟨46131, by rfl⟩ : syracuseStep 7873109 = 92263) (by norm_num)
theorem B1892965 : Blo 1381510 1892965 := bbase (se 4 (by rfl) ⟨177465, by rfl⟩ : syracuseStep 1892965 = 354931) (by norm_num)
theorem B2073197 : Blo 1381510 2073197 := bbase (se 3 (by rfl) ⟨388724, by rfl⟩ : syracuseStep 2073197 = 777449) (by norm_num)
theorem B2073221 : Blo 1381510 2073221 := bbase (se 4 (by rfl) ⟨194364, by rfl⟩ : syracuseStep 2073221 = 388729) (by norm_num)
theorem B2073245 : Blo 1381510 2073245 := bbase (se 3 (by rfl) ⟨388733, by rfl⟩ : syracuseStep 2073245 = 777467) (by norm_num)
theorem B3498653 : Blo 1381510 3498653 := bbase (se 3 (by rfl) ⟨655997, by rfl⟩ : syracuseStep 3498653 = 1311995) (by norm_num)
theorem B1401517 : Blo 1381510 1401517 := bbase (se 3 (by rfl) ⟨262784, by rfl⟩ : syracuseStep 1401517 = 525569) (by norm_num)
theorem B2073269 : Blo 1381510 2073269 := bbase (se 5 (by rfl) ⟨97184, by rfl⟩ : syracuseStep 2073269 = 194369) (by norm_num)
theorem B2073293 : Blo 1381510 2073293 := bbase (se 3 (by rfl) ⟨388742, by rfl⟩ : syracuseStep 2073293 = 777485) (by norm_num)
theorem B2073317 : Blo 1381510 2073317 := bbase (se 4 (by rfl) ⟨194373, by rfl⟩ : syracuseStep 2073317 = 388747) (by norm_num)
theorem B2073341 : Blo 1381510 2073341 := bbase (se 3 (by rfl) ⟨388751, by rfl⟩ : syracuseStep 2073341 = 777503) (by norm_num)
theorem B2073365 : Blo 1381510 2073365 := bbase (se 6 (by rfl) ⟨48594, by rfl⟩ : syracuseStep 2073365 = 97189) (by norm_num)
theorem B2073389 : Blo 1381510 2073389 := bbase (se 3 (by rfl) ⟨388760, by rfl⟩ : syracuseStep 2073389 = 777521) (by norm_num)
theorem B2073413 : Blo 1381510 2073413 := bbase (se 4 (by rfl) ⟨194382, by rfl⟩ : syracuseStep 2073413 = 388765) (by norm_num)
theorem B2073437 : Blo 1381510 2073437 := bbase (se 3 (by rfl) ⟨388769, by rfl⟩ : syracuseStep 2073437 = 777539) (by norm_num)
theorem B2073461 : Blo 1381510 2073461 := bbase (se 5 (by rfl) ⟨97193, by rfl⟩ : syracuseStep 2073461 = 194387) (by norm_num)
theorem B2073485 : Blo 1381510 2073485 := bbase (se 3 (by rfl) ⟨388778, by rfl⟩ : syracuseStep 2073485 = 777557) (by norm_num)
theorem B2073509 : Blo 1381510 2073509 := bbase (se 4 (by rfl) ⟨194391, by rfl⟩ : syracuseStep 2073509 = 388783) (by norm_num)
theorem B2073533 : Blo 1381510 2073533 := bbase (se 3 (by rfl) ⟨388787, by rfl⟩ : syracuseStep 2073533 = 777575) (by norm_num)
theorem B2073557 : Blo 1381510 2073557 := bbase (se 7 (by rfl) ⟨24299, by rfl⟩ : syracuseStep 2073557 = 48599) (by norm_num)
theorem B2073581 : Blo 1381510 2073581 := bbase (se 3 (by rfl) ⟨388796, by rfl⟩ : syracuseStep 2073581 = 777593) (by norm_num)
theorem B3498997 : Blo 1381510 3498997 := bbase (se 5 (by rfl) ⟨164015, by rfl⟩ : syracuseStep 3498997 = 328031) (by norm_num)
theorem B2073605 : Blo 1381510 2073605 := bbase (se 4 (by rfl) ⟨194400, by rfl⟩ : syracuseStep 2073605 = 388801) (by norm_num)
theorem B2802709 : Blo 1381510 2802709 := bbase (se 6 (by rfl) ⟨65688, by rfl⟩ : syracuseStep 2802709 = 131377) (by norm_num)
theorem B2073629 : Blo 1381510 2073629 := bbase (se 3 (by rfl) ⟨388805, by rfl⟩ : syracuseStep 2073629 = 777611) (by norm_num)
theorem B2073653 : Blo 1381510 2073653 := bbase (se 5 (by rfl) ⟨97202, by rfl⟩ : syracuseStep 2073653 = 194405) (by norm_num)
theorem B1475653 : Blo 1381510 1475653 := bbase (se 4 (by rfl) ⟨138342, by rfl⟩ : syracuseStep 1475653 = 276685) (by norm_num)
theorem B4203589 : Blo 1381510 4203589 := bbase (se 4 (by rfl) ⟨394086, by rfl⟩ : syracuseStep 4203589 = 788173) (by norm_num)
theorem B2073677 : Blo 1381510 2073677 := bbase (se 3 (by rfl) ⟨388814, by rfl⟩ : syracuseStep 2073677 = 777629) (by norm_num)
theorem B3499109 : Blo 1381510 3499109 := bbase (se 4 (by rfl) ⟨328041, by rfl⟩ : syracuseStep 3499109 = 656083) (by norm_num)
theorem B2073701 : Blo 1381510 2073701 := bbase (se 4 (by rfl) ⟨194409, by rfl⟩ : syracuseStep 2073701 = 388819) (by norm_num)
theorem B2073725 : Blo 1381510 2073725 := bbase (se 3 (by rfl) ⟨388823, by rfl⟩ : syracuseStep 2073725 = 777647) (by norm_num)
theorem B2213005 : Blo 1381510 2213005 := bbase (se 3 (by rfl) ⟨414938, by rfl⟩ : syracuseStep 2213005 = 829877) (by norm_num)
theorem B2073749 : Blo 1381510 2073749 := bbase (se 6 (by rfl) ⟨48603, by rfl⟩ : syracuseStep 2073749 = 97207) (by norm_num)
theorem B2073773 : Blo 1381510 2073773 := bbase (se 3 (by rfl) ⟨388832, by rfl⟩ : syracuseStep 2073773 = 777665) (by norm_num)
theorem B1475777 : Blo 1381510 1475777 := bbase (se 2 (by rfl) ⟨553416, by rfl⟩ : syracuseStep 1475777 = 1106833) (by norm_num)
theorem B2073797 : Blo 1381510 2073797 := bbase (se 4 (by rfl) ⟨194418, by rfl⟩ : syracuseStep 2073797 = 388837) (by norm_num)
theorem B5252309 : Blo 1381510 5252309 := bbase (se 7 (by rfl) ⟨61550, by rfl⟩ : syracuseStep 5252309 = 123101) (by norm_num)
theorem B2073821 : Blo 1381510 2073821 := bbase (se 3 (by rfl) ⟨388841, by rfl⟩ : syracuseStep 2073821 = 777683) (by norm_num)
theorem B2073845 : Blo 1381510 2073845 := bbase (se 5 (by rfl) ⟨97211, by rfl⟩ : syracuseStep 2073845 = 194423) (by norm_num)
theorem B2073869 : Blo 1381510 2073869 := bbase (se 3 (by rfl) ⟨388850, by rfl⟩ : syracuseStep 2073869 = 777701) (by norm_num)
theorem B3499301 : Blo 1381510 3499301 := bbase (se 4 (by rfl) ⟨328059, by rfl⟩ : syracuseStep 3499301 = 656119) (by norm_num)
theorem B2073893 : Blo 1381510 2073893 := bbase (se 4 (by rfl) ⟨194427, by rfl⟩ : syracuseStep 2073893 = 388855) (by norm_num)
theorem B1402169 : Blo 1381510 1402169 := bbase (se 2 (by rfl) ⟨525813, by rfl⟩ : syracuseStep 1402169 = 1051627) (by norm_num)
theorem B2073917 : Blo 1381510 2073917 := bbase (se 3 (by rfl) ⟨388859, by rfl⟩ : syracuseStep 2073917 = 777719) (by norm_num)
theorem B1967429 : Blo 1381510 1967429 := bbase (se 4 (by rfl) ⟨184446, by rfl⟩ : syracuseStep 1967429 = 368893) (by norm_num)
theorem B2073941 : Blo 1381510 2073941 := bbase (se 12 (by rfl) ⟨759, by rfl⟩ : syracuseStep 2073941 = 1519) (by norm_num)
theorem B12617045 : Blo 1381510 12617045 := bbase (se 12 (by rfl) ⟨4620, by rfl⟩ : syracuseStep 12617045 = 9241) (by norm_num)
theorem B4662629 : Blo 1381510 4662629 := bbase (se 4 (by rfl) ⟨437121, by rfl⟩ : syracuseStep 4662629 = 874243) (by norm_num)
theorem B2073965 : Blo 1381510 2073965 := bbase (se 3 (by rfl) ⟨388868, by rfl⟩ : syracuseStep 2073965 = 777737) (by norm_num)
theorem B2073989 : Blo 1381510 2073989 := bbase (se 4 (by rfl) ⟨194436, by rfl⟩ : syracuseStep 2073989 = 388873) (by norm_num)
theorem B2074013 : Blo 1381510 2074013 := bbase (se 3 (by rfl) ⟨388877, by rfl⟩ : syracuseStep 2074013 = 777755) (by norm_num)
theorem B2074037 : Blo 1381510 2074037 := bbase (se 5 (by rfl) ⟨97220, by rfl⟩ : syracuseStep 2074037 = 194441) (by norm_num)
theorem B1476029 : Blo 1381510 1476029 := bbase (se 3 (by rfl) ⟨276755, by rfl⟩ : syracuseStep 1476029 = 553511) (by norm_num)
theorem B2950597 : Blo 1381510 2950597 := bbase (se 4 (by rfl) ⟨276618, by rfl⟩ : syracuseStep 2950597 = 553237) (by norm_num)
theorem B2074061 : Blo 1381510 2074061 := bbase (se 3 (by rfl) ⟨388886, by rfl⟩ : syracuseStep 2074061 = 777773) (by norm_num)
theorem B2074085 : Blo 1381510 2074085 := bbase (se 4 (by rfl) ⟨194445, by rfl⟩ : syracuseStep 2074085 = 388891) (by norm_num)
theorem B5252597 : Blo 1381510 5252597 := bbase (se 5 (by rfl) ⟨246215, by rfl⟩ : syracuseStep 5252597 = 492431) (by norm_num)
theorem B2074109 : Blo 1381510 2074109 := bbase (se 3 (by rfl) ⟨388895, by rfl⟩ : syracuseStep 2074109 = 777791) (by norm_num)
theorem B2074133 : Blo 1381510 2074133 := bbase (se 6 (by rfl) ⟨48612, by rfl⟩ : syracuseStep 2074133 = 97225) (by norm_num)
theorem B2074157 : Blo 1381510 2074157 := bbase (se 3 (by rfl) ⟨388904, by rfl⟩ : syracuseStep 2074157 = 777809) (by norm_num)
theorem B2074181 : Blo 1381510 2074181 := bbase (se 4 (by rfl) ⟨194454, by rfl⟩ : syracuseStep 2074181 = 388909) (by norm_num)
theorem B6997589 : Blo 1381510 6997589 := bbase (se 8 (by rfl) ⟨41001, by rfl⟩ : syracuseStep 6997589 = 82003) (by norm_num)
theorem B2074205 : Blo 1381510 2074205 := bbase (se 3 (by rfl) ⟨388913, by rfl⟩ : syracuseStep 2074205 = 777827) (by norm_num)
theorem B2074229 : Blo 1381510 2074229 := bbase (se 5 (by rfl) ⟨97229, by rfl⟩ : syracuseStep 2074229 = 194459) (by norm_num)
theorem B3499645 : Blo 1381510 3499645 := bbase (se 3 (by rfl) ⟨656183, by rfl⟩ : syracuseStep 3499645 = 1312367) (by norm_num)
theorem B2623117 : Blo 1381510 2623117 := bbase (se 3 (by rfl) ⟨491834, by rfl⟩ : syracuseStep 2623117 = 983669) (by norm_num)
theorem B2074253 : Blo 1381510 2074253 := bbase (se 3 (by rfl) ⟨388922, by rfl⟩ : syracuseStep 2074253 = 777845) (by norm_num)
theorem B6645397 : Blo 1381510 6645397 := bbase (se 6 (by rfl) ⟨155751, by rfl⟩ : syracuseStep 6645397 = 311503) (by norm_num)
theorem B2074277 : Blo 1381510 2074277 := bbase (se 4 (by rfl) ⟨194463, by rfl⟩ : syracuseStep 2074277 = 388927) (by norm_num)
theorem B2074301 : Blo 1381510 2074301 := bbase (se 3 (by rfl) ⟨388931, by rfl⟩ : syracuseStep 2074301 = 777863) (by norm_num)
theorem B2074325 : Blo 1381510 2074325 := bbase (se 7 (by rfl) ⟨24308, by rfl⟩ : syracuseStep 2074325 = 48617) (by norm_num)
theorem B3499757 : Blo 1381510 3499757 := bbase (se 3 (by rfl) ⟨656204, by rfl⟩ : syracuseStep 3499757 = 1312409) (by norm_num)
theorem B2074349 : Blo 1381510 2074349 := bbase (se 3 (by rfl) ⟨388940, by rfl⟩ : syracuseStep 2074349 = 777881) (by norm_num)
theorem B7874293 : Blo 1381510 7874293 := bbase (se 5 (by rfl) ⟨369107, by rfl⟩ : syracuseStep 7874293 = 738215) (by norm_num)
theorem B2074373 : Blo 1381510 2074373 := bbase (se 4 (by rfl) ⟨194472, by rfl⟩ : syracuseStep 2074373 = 388945) (by norm_num)
theorem B4663061 : Blo 1381510 4663061 := bbase (se 6 (by rfl) ⟨109290, by rfl⟩ : syracuseStep 4663061 = 218581) (by norm_num)
theorem B2623261 : Blo 1381510 2623261 := bbase (se 3 (by rfl) ⟨491861, by rfl⟩ : syracuseStep 2623261 = 983723) (by norm_num)
theorem B2074397 : Blo 1381510 2074397 := bbase (se 3 (by rfl) ⟨388949, by rfl⟩ : syracuseStep 2074397 = 777899) (by norm_num)
theorem B2074421 : Blo 1381510 2074421 := bbase (se 5 (by rfl) ⟨97238, by rfl⟩ : syracuseStep 2074421 = 194477) (by norm_num)
theorem B2074445 : Blo 1381510 2074445 := bbase (se 3 (by rfl) ⟨388958, by rfl⟩ : syracuseStep 2074445 = 777917) (by norm_num)
theorem B2074469 : Blo 1381510 2074469 := bbase (se 4 (by rfl) ⟨194481, by rfl⟩ : syracuseStep 2074469 = 388963) (by norm_num)
theorem B3319661 : Blo 1381510 3319661 := bbase (se 3 (by rfl) ⟨622436, by rfl⟩ : syracuseStep 3319661 = 1244873) (by norm_num)
theorem B1967981 : Blo 1381510 1967981 := bbase (se 3 (by rfl) ⟨368996, by rfl⟩ : syracuseStep 1967981 = 737993) (by norm_num)
theorem B4794229 : Blo 1381510 4794229 := bbase (se 5 (by rfl) ⟨224729, by rfl⟩ : syracuseStep 4794229 = 449459) (by norm_num)
theorem B7096181 : Blo 1381510 7096181 := bbase (se 5 (by rfl) ⟨332633, by rfl⟩ : syracuseStep 7096181 = 665267) (by norm_num)
theorem B1476473 : Blo 1381510 1476473 := bbase (se 2 (by rfl) ⟨553677, by rfl⟩ : syracuseStep 1476473 = 1107355) (by norm_num)
theorem B2074493 : Blo 1381510 2074493 := bbase (se 3 (by rfl) ⟨388967, by rfl⟩ : syracuseStep 2074493 = 777935) (by norm_num)
theorem B2074517 : Blo 1381510 2074517 := bbase (se 6 (by rfl) ⟨48621, by rfl⟩ : syracuseStep 2074517 = 97243) (by norm_num)
theorem B3499949 : Blo 1381510 3499949 := bbase (se 3 (by rfl) ⟨656240, by rfl⟩ : syracuseStep 3499949 = 1312481) (by norm_num)
theorem B2074541 : Blo 1381510 2074541 := bbase (se 3 (by rfl) ⟨388976, by rfl⟩ : syracuseStep 2074541 = 777953) (by norm_num)
theorem B2623421 : Blo 1381510 2623421 := bbase (se 3 (by rfl) ⟨491891, by rfl⟩ : syracuseStep 2623421 = 983783) (by norm_num)
theorem B2074565 : Blo 1381510 2074565 := bbase (se 4 (by rfl) ⟨194490, by rfl⟩ : syracuseStep 2074565 = 388981) (by norm_num)
theorem B2074589 : Blo 1381510 2074589 := bbase (se 3 (by rfl) ⟨388985, by rfl⟩ : syracuseStep 2074589 = 777971) (by norm_num)
theorem B2074613 : Blo 1381510 2074613 := bbase (se 5 (by rfl) ⟨97247, by rfl⟩ : syracuseStep 2074613 = 194495) (by norm_num)
theorem B2074637 : Blo 1381510 2074637 := bbase (se 3 (by rfl) ⟨388994, by rfl⟩ : syracuseStep 2074637 = 777989) (by norm_num)
theorem B2074661 : Blo 1381510 2074661 := bbase (se 4 (by rfl) ⟨194499, by rfl⟩ : syracuseStep 2074661 = 388999) (by norm_num)
theorem B2074685 : Blo 1381510 2074685 := bbase (se 3 (by rfl) ⟨389003, by rfl⟩ : syracuseStep 2074685 = 778007) (by norm_num)
theorem B3934277 : Blo 1381510 3934277 := bbase (se 4 (by rfl) ⟨368838, by rfl⟩ : syracuseStep 3934277 = 737677) (by norm_num)
theorem B2623565 : Blo 1381510 2623565 := bbase (se 3 (by rfl) ⟨491918, by rfl⟩ : syracuseStep 2623565 = 983837) (by norm_num)
theorem B2074709 : Blo 1381510 2074709 := bbase (se 8 (by rfl) ⟨12156, by rfl⟩ : syracuseStep 2074709 = 24313) (by norm_num)
theorem B2074733 : Blo 1381510 2074733 := bbase (se 3 (by rfl) ⟨389012, by rfl⟩ : syracuseStep 2074733 = 778025) (by norm_num)
theorem B1476721 : Blo 1381510 1476721 := bbase (se 2 (by rfl) ⟨553770, by rfl⟩ : syracuseStep 1476721 = 1107541) (by norm_num)
theorem B2074757 : Blo 1381510 2074757 := bbase (se 4 (by rfl) ⟨194508, by rfl⟩ : syracuseStep 2074757 = 389017) (by norm_num)
theorem B2074781 : Blo 1381510 2074781 := bbase (se 3 (by rfl) ⟨389021, by rfl⟩ : syracuseStep 2074781 = 778043) (by norm_num)
theorem B2803877 : Blo 1381510 2803877 := bbase (se 4 (by rfl) ⟨262863, by rfl⟩ : syracuseStep 2803877 = 525727) (by norm_num)
theorem B2074805 : Blo 1381510 2074805 := bbase (se 5 (by rfl) ⟨97256, by rfl⟩ : syracuseStep 2074805 = 194513) (by norm_num)
theorem B2803901 : Blo 1381510 2803901 := bbase (se 3 (by rfl) ⟨525731, by rfl⟩ : syracuseStep 2803901 = 1051463) (by norm_num)
theorem B4663493 : Blo 1381510 4663493 := bbase (se 4 (by rfl) ⟨437202, by rfl⟩ : syracuseStep 4663493 = 874405) (by norm_num)
theorem B2074829 : Blo 1381510 2074829 := bbase (se 3 (by rfl) ⟨389030, by rfl⟩ : syracuseStep 2074829 = 778061) (by norm_num)
theorem B35416277 : Blo 1381510 35416277 := bbase (se 7 (by rfl) ⟨415034, by rfl⟩ : syracuseStep 35416277 = 830069) (by norm_num)
theorem B2074853 : Blo 1381510 2074853 := bbase (se 4 (by rfl) ⟨194517, by rfl⟩ : syracuseStep 2074853 = 389035) (by norm_num)
theorem B2074877 : Blo 1381510 2074877 := bbase (se 3 (by rfl) ⟨389039, by rfl⟩ : syracuseStep 2074877 = 778079) (by norm_num)
theorem B3500293 : Blo 1381510 3500293 := bbase (se 4 (by rfl) ⟨328152, by rfl⟩ : syracuseStep 3500293 = 656305) (by norm_num)
theorem B2074901 : Blo 1381510 2074901 := bbase (se 6 (by rfl) ⟨48630, by rfl⟩ : syracuseStep 2074901 = 97261) (by norm_num)
theorem B2074925 : Blo 1381510 2074925 := bbase (se 3 (by rfl) ⟨389048, by rfl⟩ : syracuseStep 2074925 = 778097) (by norm_num)
theorem B2074949 : Blo 1381510 2074949 := bbase (se 4 (by rfl) ⟨194526, by rfl⟩ : syracuseStep 2074949 = 389053) (by norm_num)
theorem B4983125 : Blo 1381510 4983125 := bbase (se 10 (by rfl) ⟨7299, by rfl⟩ : syracuseStep 4983125 = 14599) (by norm_num)
theorem B2074973 : Blo 1381510 2074973 := bbase (se 3 (by rfl) ⟨389057, by rfl⟩ : syracuseStep 2074973 = 778115) (by norm_num)
theorem B2623853 : Blo 1381510 2623853 := bbase (se 3 (by rfl) ⟨491972, by rfl⟩ : syracuseStep 2623853 = 983945) (by norm_num)
theorem B3500405 : Blo 1381510 3500405 := bbase (se 5 (by rfl) ⟨164081, by rfl⟩ : syracuseStep 3500405 = 328163) (by norm_num)
theorem B2074997 : Blo 1381510 2074997 := bbase (se 5 (by rfl) ⟨97265, by rfl⟩ : syracuseStep 2074997 = 194531) (by norm_num)
theorem B2075021 : Blo 1381510 2075021 := bbase (se 3 (by rfl) ⟨389066, by rfl⟩ : syracuseStep 2075021 = 778133) (by norm_num)
theorem B12954005 : Blo 1381510 12954005 := bbase (se 6 (by rfl) ⟨303609, by rfl⟩ : syracuseStep 12954005 = 607219) (by norm_num)
theorem B2075045 : Blo 1381510 2075045 := bbase (se 4 (by rfl) ⟨194535, by rfl⟩ : syracuseStep 2075045 = 389071) (by norm_num)
theorem B2075069 : Blo 1381510 2075069 := bbase (se 3 (by rfl) ⟨389075, by rfl⟩ : syracuseStep 2075069 = 778151) (by norm_num)
theorem B8858069 : Blo 1381510 8858069 := bbase (se 7 (by rfl) ⟨103805, by rfl⟩ : syracuseStep 8858069 = 207611) (by norm_num)
theorem B2075093 : Blo 1381510 2075093 := bbase (se 7 (by rfl) ⟨24317, by rfl⟩ : syracuseStep 2075093 = 48635) (by norm_num)
theorem B2075117 : Blo 1381510 2075117 := bbase (se 3 (by rfl) ⟨389084, by rfl⟩ : syracuseStep 2075117 = 778169) (by norm_num)
theorem B2214389 : Blo 1381510 2214389 := bbase (se 5 (by rfl) ⟨103799, by rfl⟩ : syracuseStep 2214389 = 207599) (by norm_num)
theorem B7473653 : Blo 1381510 7473653 := bbase (se 5 (by rfl) ⟨350327, by rfl⟩ : syracuseStep 7473653 = 700655) (by norm_num)
theorem B2624005 : Blo 1381510 2624005 := bbase (se 4 (by rfl) ⟨246000, by rfl⟩ : syracuseStep 2624005 = 492001) (by norm_num)
theorem B2075141 : Blo 1381510 2075141 := bbase (se 4 (by rfl) ⟨194544, by rfl⟩ : syracuseStep 2075141 = 389089) (by norm_num)
theorem B2075165 : Blo 1381510 2075165 := bbase (se 3 (by rfl) ⟨389093, by rfl⟩ : syracuseStep 2075165 = 778187) (by norm_num)
theorem B1477165 : Blo 1381510 1477165 := bbase (se 3 (by rfl) ⟨276968, by rfl⟩ : syracuseStep 1477165 = 553937) (by norm_num)
theorem B3500597 : Blo 1381510 3500597 := bbase (se 5 (by rfl) ⟨164090, by rfl⟩ : syracuseStep 3500597 = 328181) (by norm_num)
theorem B2075189 : Blo 1381510 2075189 := bbase (se 5 (by rfl) ⟨97274, by rfl⟩ : syracuseStep 2075189 = 194549) (by norm_num)
theorem B2075213 : Blo 1381510 2075213 := bbase (se 3 (by rfl) ⟨389102, by rfl⟩ : syracuseStep 2075213 = 778205) (by norm_num)
theorem B1968733 : Blo 1381510 1968733 := bbase (se 3 (by rfl) ⟨369137, by rfl⟩ : syracuseStep 1968733 = 738275) (by norm_num)
theorem B2075237 : Blo 1381510 2075237 := bbase (se 4 (by rfl) ⟨194553, by rfl⟩ : syracuseStep 2075237 = 389107) (by norm_num)
theorem B1477225 : Blo 1381510 1477225 := bbase (se 2 (by rfl) ⟨553959, by rfl⟩ : syracuseStep 1477225 = 1107919) (by norm_num)
theorem B4663925 : Blo 1381510 4663925 := bbase (se 5 (by rfl) ⟨218621, by rfl⟩ : syracuseStep 4663925 = 437243) (by norm_num)
theorem B11815541 : Blo 1381510 11815541 := bbase (se 5 (by rfl) ⟨553853, by rfl⟩ : syracuseStep 11815541 = 1107707) (by norm_num)
theorem B2075261 : Blo 1381510 2075261 := bbase (se 3 (by rfl) ⟨389111, by rfl⟩ : syracuseStep 2075261 = 778223) (by norm_num)
theorem B11807477 : Blo 1381510 11807477 := bbase (se 5 (by rfl) ⟨553475, by rfl⟩ : syracuseStep 11807477 = 1106951) (by norm_num)
theorem B1575725 : Blo 1381510 1575725 := bbase (se 3 (by rfl) ⟨295448, by rfl⟩ : syracuseStep 1575725 = 590897) (by norm_num)
theorem B2624309 : Blo 1381510 2624309 := bbase (se 5 (by rfl) ⟨123014, by rfl⟩ : syracuseStep 2624309 = 246029) (by norm_num)
theorem B6998885 : Blo 1381510 6998885 := bbase (se 4 (by rfl) ⟨656145, by rfl⟩ : syracuseStep 6998885 = 1312291) (by norm_num)
theorem B3500941 : Blo 1381510 3500941 := bbase (se 3 (by rfl) ⟨656426, by rfl⟩ : syracuseStep 3500941 = 1312853) (by norm_num)
theorem B2952101 : Blo 1381510 2952101 := bbase (se 4 (by rfl) ⟨276759, by rfl⟩ : syracuseStep 2952101 = 553519) (by norm_num)
theorem B1420249 : Blo 1381510 1420249 := bbase (se 2 (by rfl) ⟨532593, by rfl⟩ : syracuseStep 1420249 = 1065187) (by norm_num)
theorem B3501053 : Blo 1381510 3501053 := bbase (se 3 (by rfl) ⟨656447, by rfl⟩ : syracuseStep 3501053 = 1312895) (by norm_num)
theorem B4664357 : Blo 1381510 4664357 := bbase (se 4 (by rfl) ⟨437283, by rfl⟩ : syracuseStep 4664357 = 874567) (by norm_num)
theorem B5246005 : Blo 1381510 5246005 := bbase (se 5 (by rfl) ⟨245906, by rfl⟩ : syracuseStep 5246005 = 491813) (by norm_num)
theorem B2952245 : Blo 1381510 2952245 := bbase (se 5 (by rfl) ⟨138386, by rfl⟩ : syracuseStep 2952245 = 276773) (by norm_num)
theorem B4426933 : Blo 1381510 4426933 := bbase (se 5 (by rfl) ⟨207512, by rfl⟩ : syracuseStep 4426933 = 415025) (by norm_num)
theorem B3501245 : Blo 1381510 3501245 := bbase (se 3 (by rfl) ⟨656483, by rfl⟩ : syracuseStep 3501245 = 1312967) (by norm_num)
theorem B3935461 : Blo 1381510 3935461 := bbase (se 4 (by rfl) ⟨368949, by rfl⟩ : syracuseStep 3935461 = 737899) (by norm_num)
theorem B5901605 : Blo 1381510 5901605 := bbase (se 4 (by rfl) ⟨553275, by rfl⟩ : syracuseStep 5901605 = 1106551) (by norm_num)
theorem B5246309 : Blo 1381510 5246309 := bbase (se 4 (by rfl) ⟨491841, by rfl⟩ : syracuseStep 5246309 = 983683) (by norm_num)
theorem B1969525 : Blo 1381510 1969525 := bbase (se 5 (by rfl) ⟨92321, by rfl⟩ : syracuseStep 1969525 = 184643) (by norm_num)
theorem B3935621 : Blo 1381510 3935621 := bbase (se 4 (by rfl) ⟨368964, by rfl⟩ : syracuseStep 3935621 = 737929) (by norm_num)
theorem B2952605 : Blo 1381510 2952605 := bbase (se 3 (by rfl) ⟨553613, by rfl⟩ : syracuseStep 2952605 = 1107227) (by norm_num)
theorem B2215325 : Blo 1381510 2215325 := bbase (se 3 (by rfl) ⟨415373, by rfl⟩ : syracuseStep 2215325 = 830747) (by norm_num)
theorem B4664789 : Blo 1381510 4664789 := bbase (se 7 (by rfl) ⟨54665, by rfl⟩ : syracuseStep 4664789 = 109331) (by norm_num)
theorem B17722901 : Blo 1381510 17722901 := bbase (se 6 (by rfl) ⟨415380, by rfl⟩ : syracuseStep 17722901 = 830761) (by norm_num)
theorem B3501589 : Blo 1381510 3501589 := bbase (se 6 (by rfl) ⟨82068, by rfl⟩ : syracuseStep 3501589 = 164137) (by norm_num)
theorem B2625061 : Blo 1381510 2625061 := bbase (se 4 (by rfl) ⟨246099, by rfl⟩ : syracuseStep 2625061 = 492199) (by norm_num)
theorem B5901893 : Blo 1381510 5901893 := bbase (se 4 (by rfl) ⟨553302, by rfl⟩ : syracuseStep 5901893 = 1106605) (by norm_num)
theorem B1748557 : Blo 1381510 1748557 := bbase (se 3 (by rfl) ⟨327854, by rfl⟩ : syracuseStep 1748557 = 655709) (by norm_num)
theorem B3108437 : Blo 1381510 3108437 := bbase (se 8 (by rfl) ⟨18213, by rfl⟩ : syracuseStep 3108437 = 36427) (by norm_num)
theorem B2993773 : Blo 1381510 2993773 := bbase (se 3 (by rfl) ⟨561332, by rfl⟩ : syracuseStep 2993773 = 1122665) (by norm_num)
theorem B3935861 : Blo 1381510 3935861 := bbase (se 5 (by rfl) ⟨184493, by rfl⟩ : syracuseStep 3935861 = 368987) (by norm_num)
theorem B3501701 : Blo 1381510 3501701 := bbase (se 4 (by rfl) ⟨328284, by rfl⟩ : syracuseStep 3501701 = 656569) (by norm_num)
theorem B3108509 : Blo 1381510 3108509 := bbase (se 3 (by rfl) ⟨582845, by rfl⟩ : syracuseStep 3108509 = 1165691) (by norm_num)
theorem B2625205 : Blo 1381510 2625205 := bbase (se 5 (by rfl) ⟨123056, by rfl⟩ : syracuseStep 2625205 = 246113) (by norm_num)
theorem B7876277 : Blo 1381510 7876277 := bbase (se 5 (by rfl) ⟨369200, by rfl⟩ : syracuseStep 7876277 = 738401) (by norm_num)
theorem B1969861 : Blo 1381510 1969861 := bbase (se 4 (by rfl) ⟨184674, by rfl⟩ : syracuseStep 1969861 = 369349) (by norm_num)
theorem B3108581 : Blo 1381510 3108581 := bbase (se 4 (by rfl) ⟨291429, by rfl⟩ : syracuseStep 3108581 = 582859) (by norm_num)
theorem B1748729 : Blo 1381510 1748729 := bbase (se 2 (by rfl) ⟨655773, by rfl⟩ : syracuseStep 1748729 = 1311547) (by norm_num)
theorem B3108653 : Blo 1381510 3108653 := bbase (se 3 (by rfl) ⟨582872, by rfl⟩ : syracuseStep 3108653 = 1165745) (by norm_num)
theorem B2305837 : Blo 1381510 2305837 := bbase (se 3 (by rfl) ⟨432344, by rfl⟩ : syracuseStep 2305837 = 864689) (by norm_num)
theorem B1748785 : Blo 1381510 1748785 := bbase (se 2 (by rfl) ⟨655794, by rfl⟩ : syracuseStep 1748785 = 1311589) (by norm_num)
theorem B3936053 : Blo 1381510 3936053 := bbase (se 5 (by rfl) ⟨184502, by rfl⟩ : syracuseStep 3936053 = 369005) (by norm_num)
theorem B3321661 : Blo 1381510 3321661 := bbase (se 3 (by rfl) ⟨622811, by rfl⟩ : syracuseStep 3321661 = 1245623) (by norm_num)
theorem B3501893 : Blo 1381510 3501893 := bbase (se 4 (by rfl) ⟨328302, by rfl⟩ : syracuseStep 3501893 = 656605) (by norm_num)
theorem B2625365 : Blo 1381510 2625365 := bbase (se 9 (by rfl) ⟨7691, by rfl⟩ : syracuseStep 2625365 = 15383) (by norm_num)
theorem B3108725 : Blo 1381510 3108725 := bbase (se 5 (by rfl) ⟨145721, by rfl⟩ : syracuseStep 3108725 = 291443) (by norm_num)
theorem B4665221 : Blo 1381510 4665221 := bbase (se 4 (by rfl) ⟨437364, by rfl⟩ : syracuseStep 4665221 = 874729) (by norm_num)
theorem B1748881 : Blo 1381510 1748881 := bbase (se 2 (by rfl) ⟨655830, by rfl⟩ : syracuseStep 1748881 = 1311661) (by norm_num)
theorem B3321757 : Blo 1381510 3321757 := bbase (se 3 (by rfl) ⟨622829, by rfl⟩ : syracuseStep 3321757 = 1245659) (by norm_num)
theorem B2101157 : Blo 1381510 2101157 := bbase (se 4 (by rfl) ⟨196983, by rfl⟩ : syracuseStep 2101157 = 393967) (by norm_num)
theorem B3108797 : Blo 1381510 3108797 := bbase (se 3 (by rfl) ⟨582899, by rfl⟩ : syracuseStep 3108797 = 1165799) (by norm_num)
theorem B1683409 : Blo 1381510 1683409 := bbase (se 2 (by rfl) ⟨631278, by rfl⟩ : syracuseStep 1683409 = 1262557) (by norm_num)
theorem B2625509 : Blo 1381510 2625509 := bbase (se 4 (by rfl) ⟨246141, by rfl⟩ : syracuseStep 2625509 = 492283) (by norm_num)
theorem B3108869 : Blo 1381510 3108869 := bbase (se 4 (by rfl) ⟨291456, by rfl⟩ : syracuseStep 3108869 = 582913) (by norm_num)
theorem B2215973 : Blo 1381510 2215973 := bbase (se 4 (by rfl) ⟨207747, by rfl⟩ : syracuseStep 2215973 = 415495) (by norm_num)
theorem B1749053 : Blo 1381510 1749053 := bbase (se 3 (by rfl) ⟨327947, by rfl⟩ : syracuseStep 1749053 = 655895) (by norm_num)
theorem B3108941 : Blo 1381510 3108941 := bbase (se 3 (by rfl) ⟨582926, by rfl⟩ : syracuseStep 3108941 = 1165853) (by norm_num)
theorem B1749109 : Blo 1381510 1749109 := bbase (se 5 (by rfl) ⟨81989, by rfl⟩ : syracuseStep 1749109 = 163979) (by norm_num)
theorem B7000181 : Blo 1381510 7000181 := bbase (se 5 (by rfl) ⟨328133, by rfl⟩ : syracuseStep 7000181 = 656267) (by norm_num)
theorem B3109013 : Blo 1381510 3109013 := bbase (se 6 (by rfl) ⟨72867, by rfl⟩ : syracuseStep 3109013 = 145735) (by norm_num)
theorem B1749205 : Blo 1381510 1749205 := bbase (se 7 (by rfl) ⟨20498, by rfl⟩ : syracuseStep 1749205 = 40997) (by norm_num)
theorem B3109085 : Blo 1381510 3109085 := bbase (se 3 (by rfl) ⟨582953, by rfl⟩ : syracuseStep 3109085 = 1165907) (by norm_num)
theorem B2625797 : Blo 1381510 2625797 := bbase (se 4 (by rfl) ⟨246168, by rfl⟩ : syracuseStep 2625797 = 492337) (by norm_num)
theorem B2953493 : Blo 1381510 2953493 := bbase (se 6 (by rfl) ⟨69222, by rfl⟩ : syracuseStep 2953493 = 138445) (by norm_num)
theorem B3109157 : Blo 1381510 3109157 := bbase (se 4 (by rfl) ⟨291483, by rfl⟩ : syracuseStep 3109157 = 582967) (by norm_num)
theorem B5902645 : Blo 1381510 5902645 := bbase (se 5 (by rfl) ⟨276686, by rfl⟩ : syracuseStep 5902645 = 553373) (by norm_num)
theorem B4665653 : Blo 1381510 4665653 := bbase (se 5 (by rfl) ⟨218702, by rfl⟩ : syracuseStep 4665653 = 437405) (by norm_num)
theorem B3109229 : Blo 1381510 3109229 := bbase (se 3 (by rfl) ⟨582980, by rfl⟩ : syracuseStep 3109229 = 1165961) (by norm_num)
theorem B1749377 : Blo 1381510 1749377 := bbase (se 2 (by rfl) ⟨656016, by rfl⟩ : syracuseStep 1749377 = 1312033) (by norm_num)
theorem B2625949 : Blo 1381510 2625949 := bbase (se 3 (by rfl) ⟨492365, by rfl⟩ : syracuseStep 2625949 = 984731) (by norm_num)
theorem B3109301 : Blo 1381510 3109301 := bbase (se 5 (by rfl) ⟨145748, by rfl⟩ : syracuseStep 3109301 = 291497) (by norm_num)
theorem B1749433 : Blo 1381510 1749433 := bbase (se 2 (by rfl) ⟨656037, by rfl⟩ : syracuseStep 1749433 = 1312075) (by norm_num)
theorem B3109373 : Blo 1381510 3109373 := bbase (se 3 (by rfl) ⟨583007, by rfl⟩ : syracuseStep 3109373 = 1166015) (by norm_num)
theorem B2953741 : Blo 1381510 2953741 := bbase (se 3 (by rfl) ⟨553826, by rfl⟩ : syracuseStep 2953741 = 1107653) (by norm_num)
theorem B1749529 : Blo 1381510 1749529 := bbase (se 2 (by rfl) ⟨656073, by rfl⟩ : syracuseStep 1749529 = 1312147) (by norm_num)
theorem B3109445 : Blo 1381510 3109445 := bbase (se 4 (by rfl) ⟨291510, by rfl⟩ : syracuseStep 3109445 = 583021) (by norm_num)
theorem B1577569 : Blo 1381510 1577569 := bbase (se 2 (by rfl) ⟨591588, by rfl⟩ : syracuseStep 1577569 = 1183177) (by norm_num)
theorem B3109517 : Blo 1381510 3109517 := bbase (se 3 (by rfl) ⟨583034, by rfl⟩ : syracuseStep 3109517 = 1166069) (by norm_num)
theorem B2331301 : Blo 1381510 2331301 := bbase (se 4 (by rfl) ⟨218559, by rfl⟩ : syracuseStep 2331301 = 437119) (by norm_num)
theorem B6640325 : Blo 1381510 6640325 := bbase (se 4 (by rfl) ⟨622530, by rfl⟩ : syracuseStep 6640325 = 1245061) (by norm_num)
theorem B1749701 : Blo 1381510 1749701 := bbase (se 4 (by rfl) ⟨164034, by rfl⟩ : syracuseStep 1749701 = 328069) (by norm_num)
theorem B2626253 : Blo 1381510 2626253 := bbase (se 3 (by rfl) ⟨492422, by rfl⟩ : syracuseStep 2626253 = 984845) (by norm_num)
theorem B3109589 : Blo 1381510 3109589 := bbase (se 7 (by rfl) ⟨36440, by rfl⟩ : syracuseStep 3109589 = 72881) (by norm_num)
theorem B4666085 : Blo 1381510 4666085 := bbase (se 4 (by rfl) ⟨437445, by rfl⟩ : syracuseStep 4666085 = 874891) (by norm_num)
theorem B2331389 : Blo 1381510 2331389 := bbase (se 3 (by rfl) ⟨437135, by rfl⟩ : syracuseStep 2331389 = 874271) (by norm_num)
theorem B1749757 : Blo 1381510 1749757 := bbase (se 3 (by rfl) ⟨328079, by rfl⟩ : syracuseStep 1749757 = 656159) (by norm_num)
theorem B3937045 : Blo 1381510 3937045 := bbase (se 6 (by rfl) ⟨92274, by rfl⟩ : syracuseStep 3937045 = 184549) (by norm_num)
theorem B3109661 : Blo 1381510 3109661 := bbase (se 3 (by rfl) ⟨583061, by rfl⟩ : syracuseStep 3109661 = 1166123) (by norm_num)
theorem B1749853 : Blo 1381510 1749853 := bbase (se 3 (by rfl) ⟨328097, by rfl⟩ : syracuseStep 1749853 = 656195) (by norm_num)
theorem B3109733 : Blo 1381510 3109733 := bbase (se 4 (by rfl) ⟨291537, by rfl⟩ : syracuseStep 3109733 = 583075) (by norm_num)
theorem B2331517 : Blo 1381510 2331517 := bbase (se 3 (by rfl) ⟨437159, by rfl⟩ : syracuseStep 2331517 = 874319) (by norm_num)
theorem B1659793 : Blo 1381510 1659793 := bbase (se 2 (by rfl) ⟨622422, by rfl⟩ : syracuseStep 1659793 = 1244845) (by norm_num)
theorem B3109805 : Blo 1381510 3109805 := bbase (se 3 (by rfl) ⟨583088, by rfl⟩ : syracuseStep 3109805 = 1166177) (by norm_num)
theorem B1495985 : Blo 1381510 1495985 := bbase (se 2 (by rfl) ⟨560994, by rfl⟩ : syracuseStep 1495985 = 1121989) (by norm_num)
theorem B2331605 : Blo 1381510 2331605 := bbase (se 7 (by rfl) ⟨27323, by rfl⟩ : syracuseStep 2331605 = 54647) (by norm_num)
theorem B3322853 : Blo 1381510 3322853 := bbase (se 4 (by rfl) ⟨311517, by rfl⟩ : syracuseStep 3322853 = 623035) (by norm_num)
theorem B1659889 : Blo 1381510 1659889 := bbase (se 2 (by rfl) ⟨622458, by rfl⟩ : syracuseStep 1659889 = 1244917) (by norm_num)
theorem B3109877 : Blo 1381510 3109877 := bbase (se 5 (by rfl) ⟨145775, by rfl⟩ : syracuseStep 3109877 = 291551) (by norm_num)
theorem B2954245 : Blo 1381510 2954245 := bbase (se 4 (by rfl) ⟨276960, by rfl⟩ : syracuseStep 2954245 = 553921) (by norm_num)
theorem B1750025 : Blo 1381510 1750025 := bbase (se 2 (by rfl) ⟨656259, by rfl⟩ : syracuseStep 1750025 = 1312519) (by norm_num)
theorem B5903381 : Blo 1381510 5903381 := bbase (se 6 (by rfl) ⟨138360, by rfl⟩ : syracuseStep 5903381 = 276721) (by norm_num)
theorem B3109949 : Blo 1381510 3109949 := bbase (se 3 (by rfl) ⟨583115, by rfl⟩ : syracuseStep 3109949 = 1166231) (by norm_num)
theorem B1750081 : Blo 1381510 1750081 := bbase (se 2 (by rfl) ⟨656280, by rfl⟩ : syracuseStep 1750081 = 1312561) (by norm_num)
theorem B2331733 : Blo 1381510 2331733 := bbase (se 8 (by rfl) ⟨13662, by rfl⟩ : syracuseStep 2331733 = 27325) (by norm_num)
theorem B3110021 : Blo 1381510 3110021 := bbase (se 4 (by rfl) ⟨291564, by rfl⟩ : syracuseStep 3110021 = 583129) (by norm_num)
theorem B4666517 : Blo 1381510 4666517 := bbase (se 6 (by rfl) ⟨109371, by rfl⟩ : syracuseStep 4666517 = 218743) (by norm_num)
theorem B1750177 : Blo 1381510 1750177 := bbase (se 2 (by rfl) ⟨656316, by rfl⟩ : syracuseStep 1750177 = 1312633) (by norm_num)
theorem B2331821 : Blo 1381510 2331821 := bbase (se 3 (by rfl) ⟨437216, by rfl⟩ : syracuseStep 2331821 = 874433) (by norm_num)
theorem B4986053 : Blo 1381510 4986053 := bbase (se 4 (by rfl) ⟨467442, by rfl⟩ : syracuseStep 4986053 = 934885) (by norm_num)
theorem B3110093 : Blo 1381510 3110093 := bbase (se 3 (by rfl) ⟨583142, by rfl⟩ : syracuseStep 3110093 = 1166285) (by norm_num)
theorem B6304981 : Blo 1381510 6304981 := bbase (se 7 (by rfl) ⟨73886, by rfl⟩ : syracuseStep 6304981 = 147773) (by norm_num)
theorem B1660177 : Blo 1381510 1660177 := bbase (se 2 (by rfl) ⟨622566, by rfl⟩ : syracuseStep 1660177 = 1245133) (by norm_num)
theorem B25212181 : Blo 1381510 25212181 := bbase (se 6 (by rfl) ⟨590910, by rfl⟩ : syracuseStep 25212181 = 1181821) (by norm_num)
theorem B3110165 : Blo 1381510 3110165 := bbase (se 6 (by rfl) ⟨72894, by rfl⟩ : syracuseStep 3110165 = 145789) (by norm_num)
theorem B2331949 : Blo 1381510 2331949 := bbase (se 3 (by rfl) ⟨437240, by rfl⟩ : syracuseStep 2331949 = 874481) (by norm_num)
theorem B5985589 : Blo 1381510 5985589 := bbase (se 5 (by rfl) ⟨280574, by rfl⟩ : syracuseStep 5985589 = 561149) (by norm_num)
theorem B1750349 : Blo 1381510 1750349 := bbase (se 3 (by rfl) ⟨328190, by rfl⟩ : syracuseStep 1750349 = 656381) (by norm_num)
theorem B3110237 : Blo 1381510 3110237 := bbase (se 3 (by rfl) ⟨583169, by rfl⟩ : syracuseStep 3110237 = 1166339) (by norm_num)
theorem B2332037 : Blo 1381510 2332037 := bbase (se 4 (by rfl) ⟨218628, by rfl⟩ : syracuseStep 2332037 = 437257) (by norm_num)
theorem B7001477 : Blo 1381510 7001477 := bbase (se 4 (by rfl) ⟨656388, by rfl⟩ : syracuseStep 7001477 = 1312777) (by norm_num)
theorem B1750405 : Blo 1381510 1750405 := bbase (se 4 (by rfl) ⟨164100, by rfl⟩ : syracuseStep 1750405 = 328201) (by norm_num)
theorem B5248421 : Blo 1381510 5248421 := bbase (se 4 (by rfl) ⟨492039, by rfl⟩ : syracuseStep 5248421 = 984079) (by norm_num)
theorem B3110309 : Blo 1381510 3110309 := bbase (se 4 (by rfl) ⟨291591, by rfl⟩ : syracuseStep 3110309 = 583183) (by norm_num)
theorem B1660369 : Blo 1381510 1660369 := bbase (se 2 (by rfl) ⟨622638, by rfl⟩ : syracuseStep 1660369 = 1245277) (by norm_num)
theorem B1496549 : Blo 1381510 1496549 := bbase (se 4 (by rfl) ⟨140301, by rfl⟩ : syracuseStep 1496549 = 280603) (by norm_num)
theorem B1750501 : Blo 1381510 1750501 := bbase (se 4 (by rfl) ⟨164109, by rfl⟩ : syracuseStep 1750501 = 328219) (by norm_num)
theorem B3110381 : Blo 1381510 3110381 := bbase (se 3 (by rfl) ⟨583196, by rfl⟩ : syracuseStep 3110381 = 1166393) (by norm_num)
theorem B2332165 : Blo 1381510 2332165 := bbase (se 4 (by rfl) ⟨218640, by rfl⟩ : syracuseStep 2332165 = 437281) (by norm_num)
theorem B3110453 : Blo 1381510 3110453 := bbase (se 5 (by rfl) ⟨145802, by rfl⟩ : syracuseStep 3110453 = 291605) (by norm_num)
theorem B4666949 : Blo 1381510 4666949 := bbase (se 4 (by rfl) ⟨437526, by rfl⟩ : syracuseStep 4666949 = 875053) (by norm_num)
theorem B2365013 : Blo 1381510 2365013 := bbase (se 8 (by rfl) ⟨13857, by rfl⟩ : syracuseStep 2365013 = 27715) (by norm_num)
theorem B40416853 : Blo 1381510 40416853 := bbase (se 8 (by rfl) ⟨236817, by rfl⟩ : syracuseStep 40416853 = 473635) (by norm_num)
theorem B2332253 : Blo 1381510 2332253 := bbase (se 3 (by rfl) ⟨437297, by rfl⟩ : syracuseStep 2332253 = 874595) (by norm_num)
theorem B3110525 : Blo 1381510 3110525 := bbase (se 3 (by rfl) ⟨583223, by rfl⟩ : syracuseStep 3110525 = 1166447) (by norm_num)
theorem B1750673 : Blo 1381510 1750673 := bbase (se 2 (by rfl) ⟨656502, by rfl⟩ : syracuseStep 1750673 = 1313005) (by norm_num)
theorem B5248709 : Blo 1381510 5248709 := bbase (se 4 (by rfl) ⟨492066, by rfl⟩ : syracuseStep 5248709 = 984133) (by norm_num)
theorem B3110597 : Blo 1381510 3110597 := bbase (se 4 (by rfl) ⟨291618, by rfl⟩ : syracuseStep 3110597 = 583237) (by norm_num)
theorem B1750729 : Blo 1381510 1750729 := bbase (se 2 (by rfl) ⟨656523, by rfl⟩ : syracuseStep 1750729 = 1313047) (by norm_num)
theorem B2332381 : Blo 1381510 2332381 := bbase (se 3 (by rfl) ⟨437321, by rfl⟩ : syracuseStep 2332381 = 874643) (by norm_num)
theorem B3110669 : Blo 1381510 3110669 := bbase (se 3 (by rfl) ⟨583250, by rfl⟩ : syracuseStep 3110669 = 1166501) (by norm_num)
theorem B1554205 : Blo 1381510 1554205 := bbase (se 3 (by rfl) ⟨291413, by rfl⟩ : syracuseStep 1554205 = 582827) (by norm_num)
theorem B1750825 : Blo 1381510 1750825 := bbase (se 2 (by rfl) ⟨656559, by rfl⟩ : syracuseStep 1750825 = 1313119) (by norm_num)
theorem B1996589 : Blo 1381510 1996589 := bbase (se 3 (by rfl) ⟨374360, by rfl⟩ : syracuseStep 1996589 = 748721) (by norm_num)
theorem B2332469 : Blo 1381510 2332469 := bbase (se 5 (by rfl) ⟨109334, by rfl⟩ : syracuseStep 2332469 = 218669) (by norm_num)
theorem B1554241 : Blo 1381510 1554241 := bbase (se 2 (by rfl) ⟨582840, by rfl⟩ : syracuseStep 1554241 = 1165681) (by norm_num)
theorem B3110741 : Blo 1381510 3110741 := bbase (se 9 (by rfl) ⟨9113, by rfl⟩ : syracuseStep 3110741 = 18227) (by norm_num)
theorem B7878485 : Blo 1381510 7878485 := bbase (se 9 (by rfl) ⟨23081, by rfl⟩ : syracuseStep 7878485 = 46163) (by norm_num)
theorem B1554277 : Blo 1381510 1554277 := bbase (se 4 (by rfl) ⟨145713, by rfl⟩ : syracuseStep 1554277 = 291427) (by norm_num)
theorem B3938149 : Blo 1381510 3938149 := bbase (se 4 (by rfl) ⟨369201, by rfl⟩ : syracuseStep 3938149 = 738403) (by norm_num)
theorem B1554313 : Blo 1381510 1554313 := bbase (se 2 (by rfl) ⟨582867, by rfl⟩ : syracuseStep 1554313 = 1165735) (by norm_num)
theorem B9459605 : Blo 1381510 9459605 := bbase (se 6 (by rfl) ⟨221709, by rfl⟩ : syracuseStep 9459605 = 443419) (by norm_num)
theorem B3110813 : Blo 1381510 3110813 := bbase (se 3 (by rfl) ⟨583277, by rfl⟩ : syracuseStep 3110813 = 1166555) (by norm_num)
theorem B3323813 : Blo 1381510 3323813 := bbase (se 4 (by rfl) ⟨311607, by rfl⟩ : syracuseStep 3323813 = 623215) (by norm_num)
theorem B1554349 : Blo 1381510 1554349 := bbase (se 3 (by rfl) ⟨291440, by rfl⟩ : syracuseStep 1554349 = 582881) (by norm_num)
theorem B2332597 : Blo 1381510 2332597 := bbase (se 5 (by rfl) ⟨109340, by rfl⟩ : syracuseStep 2332597 = 218681) (by norm_num)
theorem B1554385 : Blo 1381510 1554385 := bbase (se 2 (by rfl) ⟨582894, by rfl⟩ : syracuseStep 1554385 = 1165789) (by norm_num)
theorem B1750997 : Blo 1381510 1750997 := bbase (se 7 (by rfl) ⟨20519, by rfl⟩ : syracuseStep 1750997 = 41039) (by norm_num)
theorem B3110885 : Blo 1381510 3110885 := bbase (se 4 (by rfl) ⟨291645, by rfl⟩ : syracuseStep 3110885 = 583291) (by norm_num)
theorem B1554421 : Blo 1381510 1554421 := bbase (se 5 (by rfl) ⟨72863, by rfl⟩ : syracuseStep 1554421 = 145727) (by norm_num)
theorem B4667381 : Blo 1381510 4667381 := bbase (se 5 (by rfl) ⟨218783, by rfl⟩ : syracuseStep 4667381 = 437567) (by norm_num)
theorem B6641669 : Blo 1381510 6641669 := bbase (se 4 (by rfl) ⟨622656, by rfl⟩ : syracuseStep 6641669 = 1245313) (by norm_num)
theorem B4429829 : Blo 1381510 4429829 := bbase (se 4 (by rfl) ⟨415296, by rfl⟩ : syracuseStep 4429829 = 830593) (by norm_num)
theorem B2332685 : Blo 1381510 2332685 := bbase (se 3 (by rfl) ⟨437378, by rfl⟩ : syracuseStep 2332685 = 874757) (by norm_num)
theorem B1554457 : Blo 1381510 1554457 := bbase (se 2 (by rfl) ⟨582921, by rfl⟩ : syracuseStep 1554457 = 1165843) (by norm_num)
theorem B3110957 : Blo 1381510 3110957 := bbase (se 3 (by rfl) ⟨583304, by rfl⟩ : syracuseStep 3110957 = 1166609) (by norm_num)
theorem B4380725 : Blo 1381510 4380725 := bbase (se 5 (by rfl) ⟨205346, by rfl⟩ : syracuseStep 4380725 = 410693) (by norm_num)
theorem B1554493 : Blo 1381510 1554493 := bbase (se 3 (by rfl) ⟨291467, by rfl⟩ : syracuseStep 1554493 = 582935) (by norm_num)
theorem B1554529 : Blo 1381510 1554529 := bbase (se 2 (by rfl) ⟨582948, by rfl⟩ : syracuseStep 1554529 = 1165897) (by norm_num)
theorem B3111029 : Blo 1381510 3111029 := bbase (se 5 (by rfl) ⟨145829, by rfl⟩ : syracuseStep 3111029 = 291659) (by norm_num)
theorem B1554565 : Blo 1381510 1554565 := bbase (se 4 (by rfl) ⟨145740, by rfl⟩ : syracuseStep 1554565 = 291481) (by norm_num)
theorem B2332813 : Blo 1381510 2332813 := bbase (se 3 (by rfl) ⟨437402, by rfl⟩ : syracuseStep 2332813 = 874805) (by norm_num)
theorem B16824469 : Blo 1381510 16824469 := bbase (se 6 (by rfl) ⟨394323, by rfl⟩ : syracuseStep 16824469 = 788647) (by norm_num)
theorem B1554601 : Blo 1381510 1554601 := bbase (se 2 (by rfl) ⟨582975, by rfl⟩ : syracuseStep 1554601 = 1165951) (by norm_num)
theorem B3111101 : Blo 1381510 3111101 := bbase (se 3 (by rfl) ⟨583331, by rfl⟩ : syracuseStep 3111101 = 1166663) (by norm_num)
theorem B1554637 : Blo 1381510 1554637 := bbase (se 3 (by rfl) ⟨291494, by rfl⟩ : syracuseStep 1554637 = 582989) (by norm_num)
theorem B2332901 : Blo 1381510 2332901 := bbase (se 4 (by rfl) ⟨218709, by rfl⟩ : syracuseStep 2332901 = 437419) (by norm_num)
theorem B1554673 : Blo 1381510 1554673 := bbase (se 2 (by rfl) ⟨583002, by rfl⟩ : syracuseStep 1554673 = 1166005) (by norm_num)
theorem B3111173 : Blo 1381510 3111173 := bbase (se 4 (by rfl) ⟨291672, by rfl⟩ : syracuseStep 3111173 = 583345) (by norm_num)
theorem B24254741 : Blo 1381510 24254741 := bbase (se 6 (by rfl) ⟨568470, by rfl⟩ : syracuseStep 24254741 = 1136941) (by norm_num)
theorem B1554709 : Blo 1381510 1554709 := bbase (se 6 (by rfl) ⟨36438, by rfl⟩ : syracuseStep 1554709 = 72877) (by norm_num)
theorem B14194997 : Blo 1381510 14194997 := bbase (se 5 (by rfl) ⟨665390, by rfl⟩ : syracuseStep 14194997 = 1330781) (by norm_num)
theorem B1554745 : Blo 1381510 1554745 := bbase (se 2 (by rfl) ⟨583029, by rfl⟩ : syracuseStep 1554745 = 1166059) (by norm_num)
theorem B1661249 : Blo 1381510 1661249 := bbase (se 2 (by rfl) ⟨622968, by rfl⟩ : syracuseStep 1661249 = 1245937) (by norm_num)
theorem B3111245 : Blo 1381510 3111245 := bbase (se 3 (by rfl) ⟨583358, by rfl⟩ : syracuseStep 3111245 = 1166717) (by norm_num)
theorem B1554781 : Blo 1381510 1554781 := bbase (se 3 (by rfl) ⟨291521, by rfl⟩ : syracuseStep 1554781 = 583043) (by norm_num)
theorem B6822245 : Blo 1381510 6822245 := bbase (se 4 (by rfl) ⟨639585, by rfl⟩ : syracuseStep 6822245 = 1279171) (by norm_num)
theorem B2333029 : Blo 1381510 2333029 := bbase (se 4 (by rfl) ⟨218721, by rfl⟩ : syracuseStep 2333029 = 437443) (by norm_num)
theorem B1554817 : Blo 1381510 1554817 := bbase (se 2 (by rfl) ⟨583056, by rfl⟩ : syracuseStep 1554817 = 1166113) (by norm_num)
theorem B3111317 : Blo 1381510 3111317 := bbase (se 6 (by rfl) ⟨72921, by rfl⟩ : syracuseStep 3111317 = 145843) (by norm_num)
theorem B1554853 : Blo 1381510 1554853 := bbase (se 4 (by rfl) ⟨145767, by rfl⟩ : syracuseStep 1554853 = 291535) (by norm_num)
theorem B4667813 : Blo 1381510 4667813 := bbase (se 4 (by rfl) ⟨437607, by rfl⟩ : syracuseStep 4667813 = 875215) (by norm_num)
theorem B2365861 : Blo 1381510 2365861 := bbase (se 4 (by rfl) ⟨221799, by rfl⟩ : syracuseStep 2365861 = 443599) (by norm_num)
theorem B2333117 : Blo 1381510 2333117 := bbase (se 3 (by rfl) ⟨437459, by rfl⟩ : syracuseStep 2333117 = 874919) (by norm_num)
theorem B1554889 : Blo 1381510 1554889 := bbase (se 2 (by rfl) ⟨583083, by rfl⟩ : syracuseStep 1554889 = 1166167) (by norm_num)
theorem B2365901 : Blo 1381510 2365901 := bbase (se 3 (by rfl) ⟨443606, by rfl⟩ : syracuseStep 2365901 = 887213) (by norm_num)
theorem B7477717 : Blo 1381510 7477717 := bbase (se 7 (by rfl) ⟨87629, by rfl⟩ : syracuseStep 7477717 = 175259) (by norm_num)
theorem B3111389 : Blo 1381510 3111389 := bbase (se 3 (by rfl) ⟨583385, by rfl⟩ : syracuseStep 3111389 = 1166771) (by norm_num)
theorem B1554925 : Blo 1381510 1554925 := bbase (se 3 (by rfl) ⟨291548, by rfl⟩ : syracuseStep 1554925 = 583097) (by norm_num)
theorem B1554961 : Blo 1381510 1554961 := bbase (se 2 (by rfl) ⟨583110, by rfl⟩ : syracuseStep 1554961 = 1166221) (by norm_num)
theorem B3111461 : Blo 1381510 3111461 := bbase (se 4 (by rfl) ⟨291699, by rfl⟩ : syracuseStep 3111461 = 583399) (by norm_num)
theorem B1554997 : Blo 1381510 1554997 := bbase (se 5 (by rfl) ⟨72890, by rfl⟩ : syracuseStep 1554997 = 145781) (by norm_num)
theorem B2333245 : Blo 1381510 2333245 := bbase (se 3 (by rfl) ⟨437483, by rfl⟩ : syracuseStep 2333245 = 874967) (by norm_num)
theorem B2161237 : Blo 1381510 2161237 := bbase (se 8 (by rfl) ⟨12663, by rfl⟩ : syracuseStep 2161237 = 25327) (by norm_num)
theorem B1555033 : Blo 1381510 1555033 := bbase (se 2 (by rfl) ⟨583137, by rfl⟩ : syracuseStep 1555033 = 1166275) (by norm_num)
theorem B3111533 : Blo 1381510 3111533 := bbase (se 3 (by rfl) ⟨583412, by rfl⟩ : syracuseStep 3111533 = 1166825) (by norm_num)
theorem B1555069 : Blo 1381510 1555069 := bbase (se 3 (by rfl) ⟨291575, by rfl⟩ : syracuseStep 1555069 = 583151) (by norm_num)
theorem B2333333 : Blo 1381510 2333333 := bbase (se 6 (by rfl) ⟨54687, by rfl⟩ : syracuseStep 2333333 = 109375) (by norm_num)
theorem B7002773 : Blo 1381510 7002773 := bbase (se 6 (by rfl) ⟨164127, by rfl⟩ : syracuseStep 7002773 = 328255) (by norm_num)
theorem B1555105 : Blo 1381510 1555105 := bbase (se 2 (by rfl) ⟨583164, by rfl⟩ : syracuseStep 1555105 = 1166329) (by norm_num)
theorem B3111605 : Blo 1381510 3111605 := bbase (se 5 (by rfl) ⟨145856, by rfl⟩ : syracuseStep 3111605 = 291713) (by norm_num)
theorem B1555141 : Blo 1381510 1555141 := bbase (se 4 (by rfl) ⟨145794, by rfl⟩ : syracuseStep 1555141 = 291589) (by norm_num)
theorem B1555177 : Blo 1381510 1555177 := bbase (se 2 (by rfl) ⟨583191, by rfl⟩ : syracuseStep 1555177 = 1166383) (by norm_num)
theorem B3111677 : Blo 1381510 3111677 := bbase (se 3 (by rfl) ⟨583439, by rfl⟩ : syracuseStep 3111677 = 1166879) (by norm_num)
theorem B1555213 : Blo 1381510 1555213 := bbase (se 3 (by rfl) ⟨291602, by rfl⟩ : syracuseStep 1555213 = 583205) (by norm_num)
theorem B2333461 : Blo 1381510 2333461 := bbase (se 6 (by rfl) ⟨54690, by rfl⟩ : syracuseStep 2333461 = 109381) (by norm_num)
theorem B1555249 : Blo 1381510 1555249 := bbase (se 2 (by rfl) ⟨583218, by rfl⟩ : syracuseStep 1555249 = 1166437) (by norm_num)
theorem B1661753 : Blo 1381510 1661753 := bbase (se 2 (by rfl) ⟨623157, by rfl⟩ : syracuseStep 1661753 = 1246315) (by norm_num)
theorem B3111749 : Blo 1381510 3111749 := bbase (se 4 (by rfl) ⟨291726, by rfl⟩ : syracuseStep 3111749 = 583453) (by norm_num)
theorem B1555285 : Blo 1381510 1555285 := bbase (se 9 (by rfl) ⟨4556, by rfl⟩ : syracuseStep 1555285 = 9113) (by norm_num)
theorem B4668245 : Blo 1381510 4668245 := bbase (se 9 (by rfl) ⟨13676, by rfl⟩ : syracuseStep 4668245 = 27353) (by norm_num)
theorem B3545957 : Blo 1381510 3545957 := bbase (se 4 (by rfl) ⟨332433, by rfl⟩ : syracuseStep 3545957 = 664867) (by norm_num)
theorem B5249893 : Blo 1381510 5249893 := bbase (se 4 (by rfl) ⟨492177, by rfl⟩ : syracuseStep 5249893 = 984355) (by norm_num)
theorem B1661801 : Blo 1381510 1661801 := bbase (se 2 (by rfl) ⟨623175, by rfl⟩ : syracuseStep 1661801 = 1246351) (by norm_num)
theorem B2333549 : Blo 1381510 2333549 := bbase (se 3 (by rfl) ⟨437540, by rfl⟩ : syracuseStep 2333549 = 875081) (by norm_num)
theorem B1555321 : Blo 1381510 1555321 := bbase (se 2 (by rfl) ⟨583245, by rfl⟩ : syracuseStep 1555321 = 1166491) (by norm_num)
theorem B3111821 : Blo 1381510 3111821 := bbase (se 3 (by rfl) ⟨583466, by rfl⟩ : syracuseStep 3111821 = 1166933) (by norm_num)
theorem B1555357 : Blo 1381510 1555357 := bbase (se 3 (by rfl) ⟨291629, by rfl⟩ : syracuseStep 1555357 = 583259) (by norm_num)
theorem B1555393 : Blo 1381510 1555393 := bbase (se 2 (by rfl) ⟨583272, by rfl⟩ : syracuseStep 1555393 = 1166545) (by norm_num)
theorem B3152837 : Blo 1381510 3152837 := bbase (se 4 (by rfl) ⟨295578, by rfl⟩ : syracuseStep 3152837 = 591157) (by norm_num)
theorem B3111893 : Blo 1381510 3111893 := bbase (se 7 (by rfl) ⟨36467, by rfl⟩ : syracuseStep 3111893 = 72935) (by norm_num)
theorem B1555429 : Blo 1381510 1555429 := bbase (se 4 (by rfl) ⟨145821, by rfl⟩ : syracuseStep 1555429 = 291643) (by norm_num)
theorem B2333677 : Blo 1381510 2333677 := bbase (se 3 (by rfl) ⟨437564, by rfl⟩ : syracuseStep 2333677 = 875129) (by norm_num)
theorem B1555465 : Blo 1381510 1555465 := bbase (se 2 (by rfl) ⟨583299, by rfl⟩ : syracuseStep 1555465 = 1166599) (by norm_num)
theorem B9460757 : Blo 1381510 9460757 := bbase (se 6 (by rfl) ⟨221736, by rfl⟩ : syracuseStep 9460757 = 443473) (by norm_num)
theorem B3111965 : Blo 1381510 3111965 := bbase (se 3 (by rfl) ⟨583493, by rfl⟩ : syracuseStep 3111965 = 1166987) (by norm_num)
theorem B1555501 : Blo 1381510 1555501 := bbase (se 3 (by rfl) ⟨291656, by rfl⟩ : syracuseStep 1555501 = 583313) (by norm_num)
theorem B6994997 : Blo 1381510 6994997 := bbase (se 5 (by rfl) ⟨327890, by rfl⟩ : syracuseStep 6994997 = 655781) (by norm_num)
theorem B2333765 : Blo 1381510 2333765 := bbase (se 4 (by rfl) ⟨218790, by rfl⟩ : syracuseStep 2333765 = 437581) (by norm_num)
theorem B1555537 : Blo 1381510 1555537 := bbase (se 2 (by rfl) ⟨583326, by rfl⟩ : syracuseStep 1555537 = 1166653) (by norm_num)
theorem B3497053 : Blo 1381510 3497053 := bbase (se 3 (by rfl) ⟨655697, by rfl⟩ : syracuseStep 3497053 = 1311395) (by norm_num)
theorem B3112037 : Blo 1381510 3112037 := bbase (se 4 (by rfl) ⟨291753, by rfl⟩ : syracuseStep 3112037 = 583507) (by norm_num)
theorem B1662061 : Blo 1381510 1662061 := bbase (se 3 (by rfl) ⟨311636, by rfl⟩ : syracuseStep 1662061 = 623273) (by norm_num)
theorem B1555573 : Blo 1381510 1555573 := bbase (se 5 (by rfl) ⟨72917, by rfl⟩ : syracuseStep 1555573 = 145835) (by norm_num)
theorem B5250197 : Blo 1381510 5250197 := bbase (se 6 (by rfl) ⟨123051, by rfl⟩ : syracuseStep 5250197 = 246103) (by norm_num)
theorem B1555609 : Blo 1381510 1555609 := bbase (se 2 (by rfl) ⟨583353, by rfl⟩ : syracuseStep 1555609 = 1166707) (by norm_num)
theorem B3112109 : Blo 1381510 3112109 := bbase (se 3 (by rfl) ⟨583520, by rfl⟩ : syracuseStep 3112109 = 1167041) (by norm_num)
theorem B1555645 : Blo 1381510 1555645 := bbase (se 3 (by rfl) ⟨291683, by rfl⟩ : syracuseStep 1555645 = 583367) (by norm_num)
theorem B2333893 : Blo 1381510 2333893 := bbase (se 4 (by rfl) ⟨218802, by rfl⟩ : syracuseStep 2333893 = 437605) (by norm_num)
theorem B3497165 : Blo 1381510 3497165 := bbase (se 3 (by rfl) ⟨655718, by rfl⟩ : syracuseStep 3497165 = 1311437) (by norm_num)
theorem B1555681 : Blo 1381510 1555681 := bbase (se 2 (by rfl) ⟨583380, by rfl⟩ : syracuseStep 1555681 = 1166761) (by norm_num)
theorem B2489573 : Blo 1381510 2489573 := bbase (se 4 (by rfl) ⟨233397, by rfl⟩ : syracuseStep 2489573 = 466795) (by norm_num)
theorem B3112181 : Blo 1381510 3112181 := bbase (se 5 (by rfl) ⟨145883, by rfl⟩ : syracuseStep 3112181 = 291767) (by norm_num)
theorem B1555717 : Blo 1381510 1555717 := bbase (se 4 (by rfl) ⟨145848, by rfl⟩ : syracuseStep 1555717 = 291697) (by norm_num)
theorem B4668677 : Blo 1381510 4668677 := bbase (se 4 (by rfl) ⟨437688, by rfl⟩ : syracuseStep 4668677 = 875377) (by norm_num)
theorem B4431125 : Blo 1381510 4431125 := bbase (se 6 (by rfl) ⟨103854, by rfl⟩ : syracuseStep 4431125 = 207709) (by norm_num)
theorem B2333981 : Blo 1381510 2333981 := bbase (se 3 (by rfl) ⟨437621, by rfl⟩ : syracuseStep 2333981 = 875243) (by norm_num)
theorem B1555753 : Blo 1381510 1555753 := bbase (se 2 (by rfl) ⟨583407, by rfl⟩ : syracuseStep 1555753 = 1166815) (by norm_num)
theorem B3112253 : Blo 1381510 3112253 := bbase (se 3 (by rfl) ⟨583547, by rfl⟩ : syracuseStep 3112253 = 1167095) (by norm_num)
theorem B3939653 : Blo 1381510 3939653 := bbase (se 4 (by rfl) ⟨369342, by rfl⟩ : syracuseStep 3939653 = 738685) (by norm_num)
theorem B1555789 : Blo 1381510 1555789 := bbase (se 3 (by rfl) ⟨291710, by rfl⟩ : syracuseStep 1555789 = 583421) (by norm_num)
theorem B23928149 : Blo 1381510 23928149 := bbase (se 11 (by rfl) ⟨17525, by rfl⟩ : syracuseStep 23928149 = 35051) (by norm_num)
theorem B1555825 : Blo 1381510 1555825 := bbase (se 2 (by rfl) ⟨583434, by rfl⟩ : syracuseStep 1555825 = 1166869) (by norm_num)
theorem B3112325 : Blo 1381510 3112325 := bbase (se 4 (by rfl) ⟨291780, by rfl⟩ : syracuseStep 3112325 = 583561) (by norm_num)
theorem B3497357 : Blo 1381510 3497357 := bbase (se 3 (by rfl) ⟨655754, by rfl⟩ : syracuseStep 3497357 = 1311509) (by norm_num)
theorem B1555861 : Blo 1381510 1555861 := bbase (se 6 (by rfl) ⟨36465, by rfl⟩ : syracuseStep 1555861 = 72931) (by norm_num)
theorem B2334109 : Blo 1381510 2334109 := bbase (se 3 (by rfl) ⟨437645, by rfl⟩ : syracuseStep 2334109 = 875291) (by norm_num)
theorem B1555897 : Blo 1381510 1555897 := bbase (se 2 (by rfl) ⟨583461, by rfl⟩ : syracuseStep 1555897 = 1166923) (by norm_num)
theorem B2489797 : Blo 1381510 2489797 := bbase (se 4 (by rfl) ⟨233418, by rfl⟩ : syracuseStep 2489797 = 466837) (by norm_num)
theorem B3112397 : Blo 1381510 3112397 := bbase (se 3 (by rfl) ⟨583574, by rfl⟩ : syracuseStep 3112397 = 1167149) (by norm_num)
theorem B1555933 : Blo 1381510 1555933 := bbase (se 3 (by rfl) ⟨291737, by rfl⟩ : syracuseStep 1555933 = 583475) (by norm_num)
theorem B2334197 : Blo 1381510 2334197 := bbase (se 5 (by rfl) ⟨109415, by rfl⟩ : syracuseStep 2334197 = 218831) (by norm_num)
theorem B1555969 : Blo 1381510 1555969 := bbase (se 2 (by rfl) ⟨583488, by rfl⟩ : syracuseStep 1555969 = 1166977) (by norm_num)
theorem B3153421 : Blo 1381510 3153421 := bbase (se 3 (by rfl) ⟨591266, by rfl⟩ : syracuseStep 3153421 = 1182533) (by norm_num)
theorem B3112469 : Blo 1381510 3112469 := bbase (se 6 (by rfl) ⟨72948, by rfl⟩ : syracuseStep 3112469 = 145897) (by norm_num)
theorem B1556005 : Blo 1381510 1556005 := bbase (se 4 (by rfl) ⟨145875, by rfl⟩ : syracuseStep 1556005 = 291751) (by norm_num)
theorem B1556041 : Blo 1381510 1556041 := bbase (se 2 (by rfl) ⟨583515, by rfl⟩ : syracuseStep 1556041 = 1167031) (by norm_num)
theorem B3112541 : Blo 1381510 3112541 := bbase (se 3 (by rfl) ⟨583601, by rfl⟩ : syracuseStep 3112541 = 1167203) (by norm_num)
theorem B3595877 : Blo 1381510 3595877 := bbase (se 4 (by rfl) ⟨337113, by rfl⟩ : syracuseStep 3595877 = 674227) (by norm_num)
theorem B6307429 : Blo 1381510 6307429 := bbase (se 4 (by rfl) ⟨591321, by rfl⟩ : syracuseStep 6307429 = 1182643) (by norm_num)
theorem B1556077 : Blo 1381510 1556077 := bbase (se 3 (by rfl) ⟨291764, by rfl⟩ : syracuseStep 1556077 = 583529) (by norm_num)
theorem B2334325 : Blo 1381510 2334325 := bbase (se 5 (by rfl) ⟨109421, by rfl⟩ : syracuseStep 2334325 = 218843) (by norm_num)
theorem B1556113 : Blo 1381510 1556113 := bbase (se 2 (by rfl) ⟨583542, by rfl⟩ : syracuseStep 1556113 = 1167085) (by norm_num)
theorem B3112613 : Blo 1381510 3112613 := bbase (se 4 (by rfl) ⟨291807, by rfl⟩ : syracuseStep 3112613 = 583615) (by norm_num)
theorem B11206325 : Blo 1381510 11206325 := bbase (se 5 (by rfl) ⟨525296, by rfl⟩ : syracuseStep 11206325 = 1050593) (by norm_num)
theorem B1556149 : Blo 1381510 1556149 := bbase (se 5 (by rfl) ⟨72944, by rfl⟩ : syracuseStep 1556149 = 145889) (by norm_num)
theorem B4669109 : Blo 1381510 4669109 := bbase (se 5 (by rfl) ⟨218864, by rfl⟩ : syracuseStep 4669109 = 437729) (by norm_num)
theorem B2334413 : Blo 1381510 2334413 := bbase (se 3 (by rfl) ⟨437702, by rfl⟩ : syracuseStep 2334413 = 875405) (by norm_num)
theorem B3366613 : Blo 1381510 3366613 := bbase (se 7 (by rfl) ⟨39452, by rfl⟩ : syracuseStep 3366613 = 78905) (by norm_num)
theorem B1556185 : Blo 1381510 1556185 := bbase (se 2 (by rfl) ⟨583569, by rfl⟩ : syracuseStep 1556185 = 1167139) (by norm_num)
theorem B2072285 : Blo 1381510 2072285 := bbase (se 3 (by rfl) ⟨388553, by rfl⟩ : syracuseStep 2072285 = 777107) (by norm_num)
theorem B3497701 : Blo 1381510 3497701 := bbase (se 4 (by rfl) ⟨327909, by rfl⟩ : syracuseStep 3497701 = 655819) (by norm_num)
theorem B3112685 : Blo 1381510 3112685 := bbase (se 3 (by rfl) ⟨583628, by rfl⟩ : syracuseStep 3112685 = 1167257) (by norm_num)
theorem B2072309 : Blo 1381510 2072309 := bbase (se 5 (by rfl) ⟨97139, by rfl⟩ : syracuseStep 2072309 = 194279) (by norm_num)
theorem B1556221 : Blo 1381510 1556221 := bbase (se 3 (by rfl) ⟨291791, by rfl⟩ : syracuseStep 1556221 = 583583) (by norm_num)
theorem B2072333 : Blo 1381510 2072333 := bbase (se 3 (by rfl) ⟨388562, by rfl⟩ : syracuseStep 2072333 = 777125) (by norm_num)
theorem B1556257 : Blo 1381510 1556257 := bbase (se 2 (by rfl) ⟨583596, by rfl⟩ : syracuseStep 1556257 = 1167193) (by norm_num)
theorem B2072357 : Blo 1381510 2072357 := bbase (se 4 (by rfl) ⟨194283, by rfl⟩ : syracuseStep 2072357 = 388567) (by norm_num)
theorem B3112757 : Blo 1381510 3112757 := bbase (se 5 (by rfl) ⟨145910, by rfl⟩ : syracuseStep 3112757 = 291821) (by norm_num)
theorem B2072381 : Blo 1381510 2072381 := bbase (se 3 (by rfl) ⟨388571, by rfl⟩ : syracuseStep 2072381 = 777143) (by norm_num)
theorem B1556293 : Blo 1381510 1556293 := bbase (se 4 (by rfl) ⟨145902, by rfl⟩ : syracuseStep 1556293 = 291805) (by norm_num)
theorem B2334541 : Blo 1381510 2334541 := bbase (se 3 (by rfl) ⟨437726, by rfl⟩ : syracuseStep 2334541 = 875453) (by norm_num)
theorem B2072405 : Blo 1381510 2072405 := bbase (se 9 (by rfl) ⟨6071, by rfl⟩ : syracuseStep 2072405 = 12143) (by norm_num)
theorem B3497813 : Blo 1381510 3497813 := bbase (se 9 (by rfl) ⟨10247, by rfl⟩ : syracuseStep 3497813 = 20495) (by norm_num)
theorem B10501973 : Blo 1381510 10501973 := bbase (se 9 (by rfl) ⟨30767, by rfl⟩ : syracuseStep 10501973 = 61535) (by norm_num)
theorem B1556329 : Blo 1381510 1556329 := bbase (se 2 (by rfl) ⟨583623, by rfl⟩ : syracuseStep 1556329 = 1167247) (by norm_num)
theorem B2072429 : Blo 1381510 2072429 := bbase (se 3 (by rfl) ⟨388580, by rfl⟩ : syracuseStep 2072429 = 777161) (by norm_num)
theorem B3112829 : Blo 1381510 3112829 := bbase (se 3 (by rfl) ⟨583655, by rfl⟩ : syracuseStep 3112829 = 1167311) (by norm_num)
theorem B2072453 : Blo 1381510 2072453 := bbase (se 4 (by rfl) ⟨194292, by rfl⟩ : syracuseStep 2072453 = 388585) (by norm_num)
theorem B1556365 : Blo 1381510 1556365 := bbase (se 3 (by rfl) ⟨291818, by rfl⟩ : syracuseStep 1556365 = 583637) (by norm_num)
theorem B2072477 : Blo 1381510 2072477 := bbase (se 3 (by rfl) ⟨388589, by rfl⟩ : syracuseStep 2072477 = 777179) (by norm_num)
theorem B2334629 : Blo 1381510 2334629 := bbase (se 4 (by rfl) ⟨218871, by rfl⟩ : syracuseStep 2334629 = 437743) (by norm_num)
theorem B1556401 : Blo 1381510 1556401 := bbase (se 2 (by rfl) ⟨583650, by rfl⟩ : syracuseStep 1556401 = 1167301) (by norm_num)
theorem B2072501 : Blo 1381510 2072501 := bbase (se 5 (by rfl) ⟨97148, by rfl⟩ : syracuseStep 2072501 = 194297) (by norm_num)
theorem B2072525 : Blo 1381510 2072525 := bbase (se 3 (by rfl) ⟨388598, by rfl⟩ : syracuseStep 2072525 = 777197) (by norm_num)
theorem B1556437 : Blo 1381510 1556437 := bbase (se 7 (by rfl) ⟨18239, by rfl⟩ : syracuseStep 1556437 = 36479) (by norm_num)
theorem B2072549 : Blo 1381510 2072549 := bbase (se 4 (by rfl) ⟨194301, by rfl⟩ : syracuseStep 2072549 = 388603) (by norm_num)
theorem B2072573 : Blo 1381510 2072573 := bbase (se 3 (by rfl) ⟨388607, by rfl⟩ : syracuseStep 2072573 = 777215) (by norm_num)
theorem B2072579 : Blo 1381510 2072579 := bstep (se 1 (by rfl) ⟨1554434, by rfl⟩ : syracuseStep 2072579 = 3108869) B3108869
theorem B11812877 : Blo 1381510 11812877 := bstep (se 3 (by rfl) ⟨2214914, by rfl⟩ : syracuseStep 11812877 = 4429829) B4429829
theorem B2072609 : Blo 1381510 2072609 := bstep (se 2 (by rfl) ⟨777228, by rfl⟩ : syracuseStep 2072609 = 1554457) B1554457
theorem B2072627 : Blo 1381510 2072627 := bstep (se 1 (by rfl) ⟨1554470, by rfl⟩ : syracuseStep 2072627 = 3108941) B3108941
theorem B2072657 : Blo 1381510 2072657 := bstep (se 2 (by rfl) ⟨777246, by rfl⟩ : syracuseStep 2072657 = 1554493) B1554493
theorem B2072675 : Blo 1381510 2072675 := bstep (se 1 (by rfl) ⟨1554506, by rfl⟩ : syracuseStep 2072675 = 3109013) B3109013
theorem B2072705 : Blo 1381510 2072705 := bstep (se 2 (by rfl) ⟨777264, by rfl⟩ : syracuseStep 2072705 = 1554529) B1554529
theorem B7872653 : Blo 1381510 7872653 := bstep (se 3 (by rfl) ⟨1476122, by rfl⟩ : syracuseStep 7872653 = 2952245) B2952245
theorem B2072723 : Blo 1381510 2072723 := bstep (se 1 (by rfl) ⟨1554542, by rfl⟩ : syracuseStep 2072723 = 3109085) B3109085
theorem B6996131 : Blo 1381510 6996131 := bstep (se 1 (by rfl) ⟨5247098, by rfl⟩ : syracuseStep 6996131 = 10494197) B10494197
theorem B2072753 : Blo 1381510 2072753 := bstep (se 2 (by rfl) ⟨777282, by rfl⟩ : syracuseStep 2072753 = 1554565) B1554565
theorem B2072771 : Blo 1381510 2072771 := bstep (se 1 (by rfl) ⟨1554578, by rfl⟩ : syracuseStep 2072771 = 3109157) B3109157
theorem B2072801 : Blo 1381510 2072801 := bstep (se 2 (by rfl) ⟨777300, by rfl⟩ : syracuseStep 2072801 = 1554601) B1554601
theorem B2072819 : Blo 1381510 2072819 := bstep (se 1 (by rfl) ⟨1554614, by rfl⟩ : syracuseStep 2072819 = 3109229) B3109229
theorem B2072849 : Blo 1381510 2072849 := bstep (se 2 (by rfl) ⟨777318, by rfl⟩ : syracuseStep 2072849 = 1554637) B1554637
theorem B2072867 : Blo 1381510 2072867 := bstep (se 1 (by rfl) ⟨1554650, by rfl⟩ : syracuseStep 2072867 = 3109301) B3109301
theorem B2072897 : Blo 1381510 2072897 := bstep (se 2 (by rfl) ⟨777336, by rfl⟩ : syracuseStep 2072897 = 1554673) B1554673
theorem B3735875 : Blo 1381510 3735875 := bstep (se 1 (by rfl) ⟨2801906, by rfl⟩ : syracuseStep 3735875 = 5603813) B5603813
theorem B2072915 : Blo 1381510 2072915 := bstep (se 1 (by rfl) ⟨1554686, by rfl⟩ : syracuseStep 2072915 = 3109373) B3109373
theorem B18907505 : Blo 1381510 18907505 := bstep (se 2 (by rfl) ⟨7090314, by rfl⟩ : syracuseStep 18907505 = 14180629) B14180629
theorem B2072945 : Blo 1381510 2072945 := bstep (se 2 (by rfl) ⟨777354, by rfl⟩ : syracuseStep 2072945 = 1554709) B1554709
theorem B2072963 : Blo 1381510 2072963 := bstep (se 1 (by rfl) ⟨1554722, by rfl⟩ : syracuseStep 2072963 = 3109445) B3109445
theorem B2072993 : Blo 1381510 2072993 := bstep (se 2 (by rfl) ⟨777372, by rfl⟩ : syracuseStep 2072993 = 1554745) B1554745
theorem B2073011 : Blo 1381510 2073011 := bstep (se 1 (by rfl) ⟨1554758, by rfl⟩ : syracuseStep 2073011 = 3109517) B3109517
theorem B2073041 : Blo 1381510 2073041 := bstep (se 2 (by rfl) ⟨777390, by rfl⟩ : syracuseStep 2073041 = 1554781) B1554781
theorem B2073059 : Blo 1381510 2073059 := bstep (se 1 (by rfl) ⟨1554794, by rfl⟩ : syracuseStep 2073059 = 3109589) B3109589
theorem B2073089 : Blo 1381510 2073089 := bstep (se 2 (by rfl) ⟨777408, by rfl⟩ : syracuseStep 2073089 = 1554817) B1554817
theorem B2073107 : Blo 1381510 2073107 := bstep (se 1 (by rfl) ⟨1554830, by rfl⟩ : syracuseStep 2073107 = 3109661) B3109661
theorem B2073137 : Blo 1381510 2073137 := bstep (se 2 (by rfl) ⟨777426, by rfl⟩ : syracuseStep 2073137 = 1554853) B1554853
theorem B3154481 : Blo 1381510 3154481 := bstep (se 2 (by rfl) ⟨1182930, by rfl⟩ : syracuseStep 3154481 = 2365861) B2365861
theorem B2073155 : Blo 1381510 2073155 := bstep (se 1 (by rfl) ⟨1554866, by rfl⟩ : syracuseStep 2073155 = 3109733) B3109733
theorem B2073185 : Blo 1381510 2073185 := bstep (se 2 (by rfl) ⟨777444, by rfl⟩ : syracuseStep 2073185 = 1554889) B1554889
theorem B9970289 : Blo 1381510 9970289 := bstep (se 2 (by rfl) ⟨3738858, by rfl⟩ : syracuseStep 9970289 = 7477717) B7477717
theorem B2073203 : Blo 1381510 2073203 := bstep (se 1 (by rfl) ⟨1554902, by rfl⟩ : syracuseStep 2073203 = 3109805) B3109805
theorem B2073233 : Blo 1381510 2073233 := bstep (se 2 (by rfl) ⟨777462, by rfl⟩ : syracuseStep 2073233 = 1554925) B1554925
theorem B2073251 : Blo 1381510 2073251 := bstep (se 1 (by rfl) ⟨1554938, by rfl⟩ : syracuseStep 2073251 = 3109877) B3109877
theorem B3498673 : Blo 1381510 3498673 := bstep (se 2 (by rfl) ⟨1312002, by rfl⟩ : syracuseStep 3498673 = 2624005) B2624005
theorem B2073281 : Blo 1381510 2073281 := bstep (se 2 (by rfl) ⟨777480, by rfl⟩ : syracuseStep 2073281 = 1554961) B1554961
theorem B2073299 : Blo 1381510 2073299 := bstep (se 1 (by rfl) ⟨1554974, by rfl⟩ : syracuseStep 2073299 = 3109949) B3109949
theorem B2073329 : Blo 1381510 2073329 := bstep (se 2 (by rfl) ⟨777498, by rfl⟩ : syracuseStep 2073329 = 1554997) B1554997
theorem B2073347 : Blo 1381510 2073347 := bstep (se 1 (by rfl) ⟨1555010, by rfl⟩ : syracuseStep 2073347 = 3110021) B3110021
theorem B2073377 : Blo 1381510 2073377 := bstep (se 2 (by rfl) ⟨777516, by rfl⟩ : syracuseStep 2073377 = 1555033) B1555033
theorem B2523953 : Blo 1381510 2523953 := bstep (se 2 (by rfl) ⟨946482, by rfl⟩ : syracuseStep 2523953 = 1892965) B1892965
theorem B2073395 : Blo 1381510 2073395 := bstep (se 1 (by rfl) ⟨1555046, by rfl⟩ : syracuseStep 2073395 = 3110093) B3110093
theorem B2073425 : Blo 1381510 2073425 := bstep (se 2 (by rfl) ⟨777534, by rfl⟩ : syracuseStep 2073425 = 1555069) B1555069
theorem B2073443 : Blo 1381510 2073443 := bstep (se 1 (by rfl) ⟨1555082, by rfl⟩ : syracuseStep 2073443 = 3110165) B3110165
theorem B2073473 : Blo 1381510 2073473 := bstep (se 2 (by rfl) ⟨777552, by rfl⟩ : syracuseStep 2073473 = 1555105) B1555105
theorem B13288333 : Blo 1381510 13288333 := bstep (se 3 (by rfl) ⟨2491562, by rfl⟩ : syracuseStep 13288333 = 4983125) B4983125
theorem B1868689 : Blo 1381510 1868689 := bstep (se 2 (by rfl) ⟨700758, by rfl⟩ : syracuseStep 1868689 = 1401517) B1401517
theorem B2073491 : Blo 1381510 2073491 := bstep (se 1 (by rfl) ⟨1555118, by rfl⟩ : syracuseStep 2073491 = 3110237) B3110237
theorem B2073521 : Blo 1381510 2073521 := bstep (se 2 (by rfl) ⟨777570, by rfl⟩ : syracuseStep 2073521 = 1555141) B1555141
theorem B3498947 : Blo 1381510 3498947 := bstep (se 1 (by rfl) ⟨2624210, by rfl⟩ : syracuseStep 3498947 = 5248421) B5248421
theorem B2073539 : Blo 1381510 2073539 := bstep (se 1 (by rfl) ⟨1555154, by rfl⟩ : syracuseStep 2073539 = 3110309) B3110309
theorem B6996941 : Blo 1381510 6996941 := bstep (se 3 (by rfl) ⟨1311926, by rfl⟩ : syracuseStep 6996941 = 2623853) B2623853
theorem B2073569 : Blo 1381510 2073569 := bstep (se 2 (by rfl) ⟨777588, by rfl⟩ : syracuseStep 2073569 = 1555177) B1555177
theorem B2073587 : Blo 1381510 2073587 := bstep (se 1 (by rfl) ⟨1555190, by rfl⟩ : syracuseStep 2073587 = 3110381) B3110381
theorem B2073617 : Blo 1381510 2073617 := bstep (se 2 (by rfl) ⟨777606, by rfl⟩ : syracuseStep 2073617 = 1555213) B1555213
theorem B2073635 : Blo 1381510 2073635 := bstep (se 1 (by rfl) ⟨1555226, by rfl⟩ : syracuseStep 2073635 = 3110453) B3110453
theorem B2073665 : Blo 1381510 2073665 := bstep (se 2 (by rfl) ⟨777624, by rfl⟩ : syracuseStep 2073665 = 1555249) B1555249
theorem B2073683 : Blo 1381510 2073683 := bstep (se 1 (by rfl) ⟨1555262, by rfl⟩ : syracuseStep 2073683 = 3110525) B3110525
theorem B2073713 : Blo 1381510 2073713 := bstep (se 2 (by rfl) ⟨777642, by rfl⟩ : syracuseStep 2073713 = 1555285) B1555285
theorem B3499139 : Blo 1381510 3499139 := bstep (se 1 (by rfl) ⟨2624354, by rfl⟩ : syracuseStep 3499139 = 5248709) B5248709
theorem B2073731 : Blo 1381510 2073731 := bstep (se 1 (by rfl) ⟨1555298, by rfl⟩ : syracuseStep 2073731 = 3110597) B3110597
theorem B2073761 : Blo 1381510 2073761 := bstep (se 2 (by rfl) ⟨777660, by rfl⟩ : syracuseStep 2073761 = 1555321) B1555321
theorem B2073779 : Blo 1381510 2073779 := bstep (se 1 (by rfl) ⟨1555334, by rfl⟩ : syracuseStep 2073779 = 3110669) B3110669
theorem B2213057 : Blo 1381510 2213057 := bstep (se 2 (by rfl) ⟨829896, by rfl⟩ : syracuseStep 2213057 = 1659793) B1659793
theorem B2073809 : Blo 1381510 2073809 := bstep (se 2 (by rfl) ⟨777678, by rfl⟩ : syracuseStep 2073809 = 1555357) B1555357
theorem B2073827 : Blo 1381510 2073827 := bstep (se 1 (by rfl) ⟨1555370, by rfl⟩ : syracuseStep 2073827 = 3110741) B3110741
theorem B5252323 : Blo 1381510 5252323 := bstep (se 1 (by rfl) ⟨3939242, by rfl⟩ : syracuseStep 5252323 = 7878485) B7878485
theorem B2073857 : Blo 1381510 2073857 := bstep (se 2 (by rfl) ⟨777696, by rfl⟩ : syracuseStep 2073857 = 1555393) B1555393
theorem B3990797 : Blo 1381510 3990797 := bstep (se 3 (by rfl) ⟨748274, by rfl⟩ : syracuseStep 3990797 = 1496549) B1496549
theorem B2073875 : Blo 1381510 2073875 := bstep (se 1 (by rfl) ⟨1555406, by rfl⟩ : syracuseStep 2073875 = 3110813) B3110813
theorem B1893665 : Blo 1381510 1893665 := bstep (se 2 (by rfl) ⟨710124, by rfl⟩ : syracuseStep 1893665 = 1420249) B1420249
theorem B2073905 : Blo 1381510 2073905 := bstep (se 2 (by rfl) ⟨777714, by rfl⟩ : syracuseStep 2073905 = 1555429) B1555429
theorem B2213185 : Blo 1381510 2213185 := bstep (se 2 (by rfl) ⟨829944, by rfl⟩ : syracuseStep 2213185 = 1659889) B1659889
theorem B2073923 : Blo 1381510 2073923 := bstep (se 1 (by rfl) ⟨1555442, by rfl⟩ : syracuseStep 2073923 = 3110885) B3110885
theorem B2073953 : Blo 1381510 2073953 := bstep (se 2 (by rfl) ⟨777732, by rfl⟩ : syracuseStep 2073953 = 1555465) B1555465
theorem B3736945 : Blo 1381510 3736945 := bstep (se 2 (by rfl) ⟨1401354, by rfl⟩ : syracuseStep 3736945 = 2802709) B2802709
theorem B2073971 : Blo 1381510 2073971 := bstep (se 1 (by rfl) ⟨1555478, by rfl⟩ : syracuseStep 2073971 = 3110957) B3110957
theorem B2622851 : Blo 1381510 2622851 := bstep (se 1 (by rfl) ⟨1967138, by rfl⟩ : syracuseStep 2622851 = 3934277) B3934277
theorem B2074001 : Blo 1381510 2074001 := bstep (se 2 (by rfl) ⟨777750, by rfl⟩ : syracuseStep 2074001 = 1555501) B1555501
theorem B2074019 : Blo 1381510 2074019 := bstep (se 1 (by rfl) ⟨1555514, by rfl⟩ : syracuseStep 2074019 = 3111029) B3111029
theorem B1967537 : Blo 1381510 1967537 := bstep (se 2 (by rfl) ⟨737826, by rfl⟩ : syracuseStep 1967537 = 1475653) B1475653
theorem B5604785 : Blo 1381510 5604785 := bstep (se 2 (by rfl) ⟨2101794, by rfl⟩ : syracuseStep 5604785 = 4203589) B4203589
theorem B2074049 : Blo 1381510 2074049 := bstep (se 2 (by rfl) ⟨777768, by rfl⟩ : syracuseStep 2074049 = 1555537) B1555537
theorem B1869251 : Blo 1381510 1869251 := bstep (se 1 (by rfl) ⟨1401938, by rfl⟩ : syracuseStep 1869251 = 2803877) B2803877
theorem B4662737 : Blo 1381510 4662737 := bstep (se 2 (by rfl) ⟨1748526, by rfl⟩ : syracuseStep 4662737 = 3497053) B3497053
theorem B2074067 : Blo 1381510 2074067 := bstep (se 1 (by rfl) ⟨1555550, by rfl⟩ : syracuseStep 2074067 = 3111101) B3111101
theorem B23610851 : Blo 1381510 23610851 := bstep (se 1 (by rfl) ⟨17708138, by rfl⟩ : syracuseStep 23610851 = 35416277) B35416277
theorem B2074097 : Blo 1381510 2074097 := bstep (se 2 (by rfl) ⟨777786, by rfl⟩ : syracuseStep 2074097 = 1555573) B1555573
theorem B2074115 : Blo 1381510 2074115 := bstep (se 1 (by rfl) ⟨1555586, by rfl⟩ : syracuseStep 2074115 = 3111173) B3111173
theorem B2950673 : Blo 1381510 2950673 := bstep (se 2 (by rfl) ⟨1106502, by rfl⟩ : syracuseStep 2950673 = 2213005) B2213005
theorem B2074145 : Blo 1381510 2074145 := bstep (se 2 (by rfl) ⟨777804, by rfl⟩ : syracuseStep 2074145 = 1555609) B1555609
theorem B9463331 : Blo 1381510 9463331 := bstep (se 1 (by rfl) ⟨7097498, by rfl⟩ : syracuseStep 9463331 = 14194997) B14194997
theorem B2074163 : Blo 1381510 2074163 := bstep (se 1 (by rfl) ⟨1555622, by rfl⟩ : syracuseStep 2074163 = 3111245) B3111245
theorem B4548163 : Blo 1381510 4548163 := bstep (se 1 (by rfl) ⟨3411122, by rfl⟩ : syracuseStep 4548163 = 6822245) B6822245
theorem B2074193 : Blo 1381510 2074193 := bstep (se 2 (by rfl) ⟨777822, by rfl⟩ : syracuseStep 2074193 = 1555645) B1555645
theorem B8636003 : Blo 1381510 8636003 := bstep (se 1 (by rfl) ⟨6477002, by rfl⟩ : syracuseStep 8636003 = 12954005) B12954005
theorem B2074211 : Blo 1381510 2074211 := bstep (se 1 (by rfl) ⟨1555658, by rfl⟩ : syracuseStep 2074211 = 3111317) B3111317
theorem B8406641 : Blo 1381510 8406641 := bstep (se 2 (by rfl) ⟨3152490, by rfl⟩ : syracuseStep 8406641 = 6304981) B6304981
theorem B2074241 : Blo 1381510 2074241 := bstep (se 2 (by rfl) ⟨777840, by rfl⟩ : syracuseStep 2074241 = 1555681) B1555681
theorem B2074259 : Blo 1381510 2074259 := bstep (se 1 (by rfl) ⟨1555694, by rfl⟩ : syracuseStep 2074259 = 3111389) B3111389
theorem B4982435 : Blo 1381510 4982435 := bstep (se 1 (by rfl) ⟨3736826, by rfl⟩ : syracuseStep 4982435 = 7473653) B7473653
theorem B2074289 : Blo 1381510 2074289 := bstep (se 2 (by rfl) ⟨777858, by rfl⟩ : syracuseStep 2074289 = 1555717) B1555717
theorem B2213569 : Blo 1381510 2213569 := bstep (se 2 (by rfl) ⟨830088, by rfl⟩ : syracuseStep 2213569 = 1660177) B1660177
theorem B2074307 : Blo 1381510 2074307 := bstep (se 1 (by rfl) ⟨1555730, by rfl⟩ : syracuseStep 2074307 = 3111461) B3111461
theorem B2074337 : Blo 1381510 2074337 := bstep (se 2 (by rfl) ⟨777876, by rfl⟩ : syracuseStep 2074337 = 1555753) B1555753
theorem B7980785 : Blo 1381510 7980785 := bstep (se 2 (by rfl) ⟨2992794, by rfl⟩ : syracuseStep 7980785 = 5985589) B5985589
theorem B2074355 : Blo 1381510 2074355 := bstep (se 1 (by rfl) ⟨1555766, by rfl⟩ : syracuseStep 2074355 = 3111533) B3111533
theorem B2074385 : Blo 1381510 2074385 := bstep (se 2 (by rfl) ⟨777894, by rfl⟩ : syracuseStep 2074385 = 1555789) B1555789
theorem B2074403 : Blo 1381510 2074403 := bstep (se 1 (by rfl) ⟨1555802, by rfl⟩ : syracuseStep 2074403 = 3111605) B3111605
theorem B2074433 : Blo 1381510 2074433 := bstep (se 2 (by rfl) ⟨777912, by rfl⟩ : syracuseStep 2074433 = 1555825) B1555825
theorem B2074451 : Blo 1381510 2074451 := bstep (se 1 (by rfl) ⟨1555838, by rfl⟩ : syracuseStep 2074451 = 3111677) B3111677
theorem B2074481 : Blo 1381510 2074481 := bstep (se 2 (by rfl) ⟨777930, by rfl⟩ : syracuseStep 2074481 = 1555861) B1555861
theorem B2074499 : Blo 1381510 2074499 := bstep (se 1 (by rfl) ⟨1555874, by rfl⟩ : syracuseStep 2074499 = 3111749) B3111749
theorem B2074529 : Blo 1381510 2074529 := bstep (se 2 (by rfl) ⟨777948, by rfl⟩ : syracuseStep 2074529 = 1555897) B1555897
theorem B3934129 : Blo 1381510 3934129 := bstep (se 2 (by rfl) ⟨1475298, by rfl⟩ : syracuseStep 3934129 = 2950597) B2950597
theorem B2074547 : Blo 1381510 2074547 := bstep (se 1 (by rfl) ⟨1555910, by rfl⟩ : syracuseStep 2074547 = 3111821) B3111821
theorem B2213825 : Blo 1381510 2213825 := bstep (se 2 (by rfl) ⟨830184, by rfl⟩ : syracuseStep 2213825 = 1660369) B1660369
theorem B1968067 : Blo 1381510 1968067 := bstep (se 1 (by rfl) ⟨1476050, by rfl⟩ : syracuseStep 1968067 = 2952101) B2952101
theorem B2074577 : Blo 1381510 2074577 := bstep (se 2 (by rfl) ⟨777966, by rfl⟩ : syracuseStep 2074577 = 1555933) B1555933
theorem B2074595 : Blo 1381510 2074595 := bstep (se 1 (by rfl) ⟨1555946, by rfl⟩ : syracuseStep 2074595 = 3111893) B3111893
theorem B4663277 : Blo 1381510 4663277 := bstep (se 3 (by rfl) ⟨874364, by rfl⟩ : syracuseStep 4663277 = 1748729) B1748729
theorem B2074625 : Blo 1381510 2074625 := bstep (se 2 (by rfl) ⟨777984, by rfl⟩ : syracuseStep 2074625 = 1555969) B1555969
theorem B4204561 : Blo 1381510 4204561 := bstep (se 2 (by rfl) ⟨1576710, by rfl⟩ : syracuseStep 4204561 = 3153421) B3153421
theorem B2074643 : Blo 1381510 2074643 := bstep (se 1 (by rfl) ⟨1555982, by rfl⟩ : syracuseStep 2074643 = 3111965) B3111965
theorem B4663331 : Blo 1381510 4663331 := bstep (se 1 (by rfl) ⟨3497498, by rfl⟩ : syracuseStep 4663331 = 6994997) B6994997
theorem B3500081 : Blo 1381510 3500081 := bstep (se 2 (by rfl) ⟨1312530, by rfl⟩ : syracuseStep 3500081 = 2625061) B2625061
theorem B2074673 : Blo 1381510 2074673 := bstep (se 2 (by rfl) ⟨778002, by rfl⟩ : syracuseStep 2074673 = 1556005) B1556005
theorem B2074691 : Blo 1381510 2074691 := bstep (se 1 (by rfl) ⟨1556018, by rfl⟩ : syracuseStep 2074691 = 3112037) B3112037
theorem B7473221 : Blo 1381510 7473221 := bstep (se 4 (by rfl) ⟨700614, by rfl⟩ : syracuseStep 7473221 = 1401229) B1401229
theorem B2074721 : Blo 1381510 2074721 := bstep (se 2 (by rfl) ⟨778020, by rfl⟩ : syracuseStep 2074721 = 1556041) B1556041
theorem B3500131 : Blo 1381510 3500131 := bstep (se 1 (by rfl) ⟨2625098, by rfl⟩ : syracuseStep 3500131 = 5250197) B5250197
theorem B53889137 : Blo 1381510 53889137 := bstep (se 2 (by rfl) ⟨20208426, by rfl⟩ : syracuseStep 53889137 = 40416853) B40416853
theorem B2074739 : Blo 1381510 2074739 := bstep (se 1 (by rfl) ⟨1556054, by rfl⟩ : syracuseStep 2074739 = 3112109) B3112109
theorem B10496141 : Blo 1381510 10496141 := bstep (se 3 (by rfl) ⟨1968026, by rfl⟩ : syracuseStep 10496141 = 3936053) B3936053
theorem B3991697 : Blo 1381510 3991697 := bstep (se 2 (by rfl) ⟨1496886, by rfl⟩ : syracuseStep 3991697 = 2993773) B2993773
theorem B2074769 : Blo 1381510 2074769 := bstep (se 2 (by rfl) ⟨778038, by rfl⟩ : syracuseStep 2074769 = 1556077) B1556077
theorem B2074787 : Blo 1381510 2074787 := bstep (se 1 (by rfl) ⟨1556090, by rfl⟩ : syracuseStep 2074787 = 3112181) B3112181
theorem B2074817 : Blo 1381510 2074817 := bstep (se 2 (by rfl) ⟨778056, by rfl⟩ : syracuseStep 2074817 = 1556113) B1556113
theorem B3934403 : Blo 1381510 3934403 := bstep (se 1 (by rfl) ⟨2950802, by rfl⟩ : syracuseStep 3934403 = 5901605) B5901605
theorem B2074835 : Blo 1381510 2074835 := bstep (se 1 (by rfl) ⟨1556126, by rfl⟩ : syracuseStep 2074835 = 3112253) B3112253
theorem B15952099 : Blo 1381510 15952099 := bstep (se 1 (by rfl) ⟨11964074, by rfl⟩ : syracuseStep 15952099 = 23928149) B23928149
theorem B3500273 : Blo 1381510 3500273 := bstep (se 2 (by rfl) ⟨1312602, by rfl⟩ : syracuseStep 3500273 = 2625205) B2625205
theorem B2074865 : Blo 1381510 2074865 := bstep (se 2 (by rfl) ⟨778074, by rfl⟩ : syracuseStep 2074865 = 1556149) B1556149
theorem B2623747 : Blo 1381510 2623747 := bstep (se 1 (by rfl) ⟨1967810, by rfl⟩ : syracuseStep 2623747 = 3935621) B3935621
theorem B2074883 : Blo 1381510 2074883 := bstep (se 1 (by rfl) ⟨1556162, by rfl⟩ : syracuseStep 2074883 = 3112325) B3112325
theorem B1968403 : Blo 1381510 1968403 := bstep (se 1 (by rfl) ⟨1476302, by rfl⟩ : syracuseStep 1968403 = 2952605) B2952605
theorem B1476883 : Blo 1381510 1476883 := bstep (se 1 (by rfl) ⟨1107662, by rfl⟩ : syracuseStep 1476883 = 2215325) B2215325
theorem B2074913 : Blo 1381510 2074913 := bstep (se 2 (by rfl) ⟨778092, by rfl⟩ : syracuseStep 2074913 = 1556185) B1556185
theorem B4663601 : Blo 1381510 4663601 := bstep (se 2 (by rfl) ⟨1748850, by rfl⟩ : syracuseStep 4663601 = 3497701) B3497701
theorem B2074931 : Blo 1381510 2074931 := bstep (se 1 (by rfl) ⟨1556198, by rfl⟩ : syracuseStep 2074931 = 3112397) B3112397
theorem B2074961 : Blo 1381510 2074961 := bstep (se 2 (by rfl) ⟨778110, by rfl⟩ : syracuseStep 2074961 = 1556221) B1556221
theorem B11815267 : Blo 1381510 11815267 := bstep (se 1 (by rfl) ⟨8861450, by rfl⟩ : syracuseStep 11815267 = 17722901) B17722901
theorem B2074979 : Blo 1381510 2074979 := bstep (se 1 (by rfl) ⟨1556234, by rfl⟩ : syracuseStep 2074979 = 3112469) B3112469
theorem B2075009 : Blo 1381510 2075009 := bstep (se 2 (by rfl) ⟨778128, by rfl⟩ : syracuseStep 2075009 = 1556257) B1556257
theorem B3934595 : Blo 1381510 3934595 := bstep (se 1 (by rfl) ⟨2950946, by rfl⟩ : syracuseStep 3934595 = 5901893) B5901893
theorem B3074449 : Blo 1381510 3074449 := bstep (se 2 (by rfl) ⟨1152918, by rfl⟩ : syracuseStep 3074449 = 2305837) B2305837
theorem B2075027 : Blo 1381510 2075027 := bstep (se 1 (by rfl) ⟨1556270, by rfl⟩ : syracuseStep 2075027 = 3112541) B3112541
theorem B2623907 : Blo 1381510 2623907 := bstep (se 1 (by rfl) ⟨1967930, by rfl⟩ : syracuseStep 2623907 = 3935861) B3935861
theorem B2075057 : Blo 1381510 2075057 := bstep (se 2 (by rfl) ⟨778146, by rfl⟩ : syracuseStep 2075057 = 1556293) B1556293
theorem B2075075 : Blo 1381510 2075075 := bstep (se 1 (by rfl) ⟨1556306, by rfl⟩ : syracuseStep 2075075 = 3112613) B3112613
theorem B2075105 : Blo 1381510 2075105 := bstep (se 2 (by rfl) ⟨778164, by rfl⟩ : syracuseStep 2075105 = 1556329) B1556329
theorem B6392305 : Blo 1381510 6392305 := bstep (se 2 (by rfl) ⟨2397114, by rfl⟩ : syracuseStep 6392305 = 4794229) B4794229
theorem B2075123 : Blo 1381510 2075123 := bstep (se 1 (by rfl) ⟨1556342, by rfl⟩ : syracuseStep 2075123 = 3112685) B3112685
theorem B2075153 : Blo 1381510 2075153 := bstep (se 2 (by rfl) ⟨778182, by rfl⟩ : syracuseStep 2075153 = 1556365) B1556365
theorem B2075171 : Blo 1381510 2075171 := bstep (se 1 (by rfl) ⟨1556378, by rfl⟩ : syracuseStep 2075171 = 3112757) B3112757
theorem B2075201 : Blo 1381510 2075201 := bstep (se 2 (by rfl) ⟨778200, by rfl⟩ : syracuseStep 2075201 = 1556401) B1556401
theorem B2075219 : Blo 1381510 2075219 := bstep (se 1 (by rfl) ⟨1556414, by rfl⟩ : syracuseStep 2075219 = 3112829) B3112829
theorem B2075249 : Blo 1381510 2075249 := bstep (se 2 (by rfl) ⟨778218, by rfl⟩ : syracuseStep 2075249 = 1556437) B1556437
theorem B1477315 : Blo 1381510 1477315 := bstep (se 1 (by rfl) ⟨1107986, by rfl⟩ : syracuseStep 1477315 = 2215973) B2215973
theorem B1968961 : Blo 1381510 1968961 := bstep (se 2 (by rfl) ⟨738360, by rfl⟩ : syracuseStep 1968961 = 1476721) B1476721
theorem B4664141 : Blo 1381510 4664141 := bstep (se 3 (by rfl) ⟨874526, by rfl⟩ : syracuseStep 4664141 = 1749053) B1749053
theorem B1968995 : Blo 1381510 1968995 := bstep (se 1 (by rfl) ⟨1476746, by rfl⟩ : syracuseStep 1968995 = 2953493) B2953493
theorem B6646627 : Blo 1381510 6646627 := bstep (se 1 (by rfl) ⟨4984970, by rfl⟩ : syracuseStep 6646627 = 9969941) B9969941
theorem B22432625 : Blo 1381510 22432625 := bstep (se 2 (by rfl) ⟨8412234, by rfl⟩ : syracuseStep 22432625 = 16824469) B16824469
theorem B4664195 : Blo 1381510 4664195 := bstep (se 1 (by rfl) ⟨3498146, by rfl⟩ : syracuseStep 4664195 = 6996293) B6996293
theorem B5909411 : Blo 1381510 5909411 := bstep (se 1 (by rfl) ⟨4432058, by rfl⟩ : syracuseStep 5909411 = 8864117) B8864117
theorem B1682371 : Blo 1381510 1682371 := bstep (se 1 (by rfl) ⟨1261778, by rfl⟩ : syracuseStep 1682371 = 2523557) B2523557
theorem B7875569 : Blo 1381510 7875569 := bstep (se 2 (by rfl) ⟨2953338, by rfl⟩ : syracuseStep 7875569 = 5906677) B5906677
theorem B4426883 : Blo 1381510 4426883 := bstep (se 1 (by rfl) ⟨3320162, by rfl⟩ : syracuseStep 4426883 = 6640325) B6640325
theorem B4664465 : Blo 1381510 4664465 := bstep (se 2 (by rfl) ⟨1749174, by rfl⟩ : syracuseStep 4664465 = 3498349) B3498349
theorem B3935405 : Blo 1381510 3935405 := bstep (se 3 (by rfl) ⟨737888, by rfl⟩ : syracuseStep 3935405 = 1475777) B1475777
theorem B3501265 : Blo 1381510 3501265 := bstep (se 2 (by rfl) ⟨1312974, by rfl⟩ : syracuseStep 3501265 = 2625949) B2625949
theorem B6638861 : Blo 1381510 6638861 := bstep (se 3 (by rfl) ⟨1244786, by rfl⟩ : syracuseStep 6638861 = 2489573) B2489573
theorem B2993425 : Blo 1381510 2993425 := bstep (se 2 (by rfl) ⟨1122534, by rfl⟩ : syracuseStep 2993425 = 2245069) B2245069
theorem B2215235 : Blo 1381510 2215235 := bstep (se 1 (by rfl) ⟨1661426, by rfl⟩ : syracuseStep 2215235 = 3322853) B3322853
theorem B3935587 : Blo 1381510 3935587 := bstep (se 1 (by rfl) ⟨2951690, by rfl⟩ : syracuseStep 3935587 = 5903381) B5903381
theorem B1969553 : Blo 1381510 1969553 := bstep (se 2 (by rfl) ⟨738582, by rfl⟩ : syracuseStep 1969553 = 1477165) B1477165
theorem B2624977 : Blo 1381510 2624977 := bstep (se 2 (by rfl) ⟨984366, by rfl⟩ : syracuseStep 2624977 = 1968733) B1968733
theorem B1969633 : Blo 1381510 1969633 := bstep (se 2 (by rfl) ⟨738612, by rfl⟩ : syracuseStep 1969633 = 1477225) B1477225
theorem B3501539 : Blo 1381510 3501539 := bstep (se 1 (by rfl) ⟨2626154, by rfl⟩ : syracuseStep 3501539 = 5252309) B5252309
theorem B3739117 : Blo 1381510 3739117 := bstep (se 3 (by rfl) ⟨701084, by rfl⟩ : syracuseStep 3739117 = 1402169) B1402169
theorem B5246477 : Blo 1381510 5246477 := bstep (se 3 (by rfl) ⟨983714, by rfl⟩ : syracuseStep 5246477 = 1967429) B1967429
theorem B29888021 : Blo 1381510 29888021 := bstep (se 6 (by rfl) ⟨700500, by rfl⟩ : syracuseStep 29888021 = 1401001) B1401001
theorem B3108401 : Blo 1381510 3108401 := bstep (se 2 (by rfl) ⟨1165650, by rfl⟩ : syracuseStep 3108401 = 2331301) B2331301
theorem B3108419 : Blo 1381510 3108419 := bstep (se 1 (by rfl) ⟨2331314, by rfl⟩ : syracuseStep 3108419 = 4662629) B4662629
theorem B3501731 : Blo 1381510 3501731 := bstep (se 1 (by rfl) ⟨2626298, by rfl⟩ : syracuseStep 3501731 = 5252597) B5252597
theorem B4665005 : Blo 1381510 4665005 := bstep (se 3 (by rfl) ⟨874688, by rfl⟩ : syracuseStep 4665005 = 1749377) B1749377
theorem B4665059 : Blo 1381510 4665059 := bstep (se 1 (by rfl) ⟨3498794, by rfl⟩ : syracuseStep 4665059 = 6997589) B6997589
theorem B1576675 : Blo 1381510 1576675 := bstep (se 1 (by rfl) ⟨1182506, by rfl⟩ : syracuseStep 1576675 = 2365013) B2365013
theorem B6999857 : Blo 1381510 6999857 := bstep (se 2 (by rfl) ⟨2624946, by rfl⟩ : syracuseStep 6999857 = 5249893) B5249893
theorem B3936077 : Blo 1381510 3936077 := bstep (se 3 (by rfl) ⟨738014, by rfl⟩ : syracuseStep 3936077 = 1476029) B1476029
theorem B3108689 : Blo 1381510 3108689 := bstep (se 2 (by rfl) ⟨1165758, by rfl⟩ : syracuseStep 3108689 = 2331517) B2331517
theorem B3108707 : Blo 1381510 3108707 := bstep (se 1 (by rfl) ⟨2331530, by rfl⟩ : syracuseStep 3108707 = 4663061) B4663061
theorem B1748947 : Blo 1381510 1748947 := bstep (se 1 (by rfl) ⟨1311710, by rfl⟩ : syracuseStep 1748947 = 2623421) B2623421
theorem B4665329 : Blo 1381510 4665329 := bstep (se 2 (by rfl) ⟨1749498, by rfl⟩ : syracuseStep 4665329 = 3498997) B3498997
theorem B4427779 : Blo 1381510 4427779 := bstep (se 1 (by rfl) ⟨3320834, by rfl⟩ : syracuseStep 4427779 = 6641669) B6641669
theorem B2920483 : Blo 1381510 2920483 := bstep (se 1 (by rfl) ⟨2190362, by rfl⟩ : syracuseStep 2920483 = 4380725) B4380725
theorem B1749043 : Blo 1381510 1749043 := bstep (se 1 (by rfl) ⟨1311782, by rfl⟩ : syracuseStep 1749043 = 2623565) B2623565
theorem B3108977 : Blo 1381510 3108977 := bstep (se 2 (by rfl) ⟨1165866, by rfl⟩ : syracuseStep 3108977 = 2331733) B2331733
theorem B3108995 : Blo 1381510 3108995 := bstep (se 1 (by rfl) ⟨2331746, by rfl⟩ : syracuseStep 3108995 = 4663493) B4663493
theorem B2216081 : Blo 1381510 2216081 := bstep (se 2 (by rfl) ⟨831030, by rfl⟩ : syracuseStep 2216081 = 1662061) B1662061
theorem B5902577 : Blo 1381510 5902577 := bstep (se 2 (by rfl) ⟨2213466, by rfl⟩ : syracuseStep 5902577 = 4426933) B4426933
theorem B5247281 : Blo 1381510 5247281 := bstep (se 2 (by rfl) ⟨1967730, by rfl⟩ : syracuseStep 5247281 = 3935461) B3935461
theorem B1577267 : Blo 1381510 1577267 := bstep (se 1 (by rfl) ⟨1182950, by rfl⟩ : syracuseStep 1577267 = 2365901) B2365901
theorem B33616241 : Blo 1381510 33616241 := bstep (se 2 (by rfl) ⟨12606090, by rfl⟩ : syracuseStep 33616241 = 25212181) B25212181
theorem B3109265 : Blo 1381510 3109265 := bstep (se 2 (by rfl) ⟨1165974, by rfl⟩ : syracuseStep 3109265 = 2331949) B2331949
theorem B3109283 : Blo 1381510 3109283 := bstep (se 1 (by rfl) ⟨2331962, by rfl⟩ : syracuseStep 3109283 = 4663925) B4663925
theorem B7877027 : Blo 1381510 7877027 := bstep (se 1 (by rfl) ⟨5907770, by rfl⟩ : syracuseStep 7877027 = 11815541) B11815541
theorem B2626033 : Blo 1381510 2626033 := bstep (se 2 (by rfl) ⟨984762, by rfl⟩ : syracuseStep 2626033 = 1969525) B1969525
theorem B4665869 : Blo 1381510 4665869 := bstep (se 3 (by rfl) ⟨874850, by rfl⟩ : syracuseStep 4665869 = 1749701) B1749701
theorem B1749539 : Blo 1381510 1749539 := bstep (se 1 (by rfl) ⟨1312154, by rfl⟩ : syracuseStep 1749539 = 2624309) B2624309
theorem B2363971 : Blo 1381510 2363971 := bstep (se 1 (by rfl) ⟨1772978, by rfl⟩ : syracuseStep 2363971 = 3545957) B3545957
theorem B4665923 : Blo 1381510 4665923 := bstep (se 1 (by rfl) ⟨3499442, by rfl⟩ : syracuseStep 4665923 = 6998885) B6998885
theorem B2101891 : Blo 1381510 2101891 := bstep (se 1 (by rfl) ⟨1576418, by rfl⟩ : syracuseStep 2101891 = 3152837) B3152837
theorem B3109553 : Blo 1381510 3109553 := bstep (se 2 (by rfl) ⟨1166082, by rfl⟩ : syracuseStep 3109553 = 2332165) B2332165
theorem B3109571 : Blo 1381510 3109571 := bstep (se 1 (by rfl) ⟨2332178, by rfl⟩ : syracuseStep 3109571 = 4664357) B4664357
theorem B2331409 : Blo 1381510 2331409 := bstep (se 2 (by rfl) ⟨874278, by rfl⟩ : syracuseStep 2331409 = 1748557) B1748557
theorem B8409905 : Blo 1381510 8409905 := bstep (se 2 (by rfl) ⟨3153714, by rfl⟩ : syracuseStep 8409905 = 6307429) B6307429
theorem B2331443 : Blo 1381510 2331443 := bstep (se 1 (by rfl) ⟨1748582, by rfl⟩ : syracuseStep 2331443 = 3497165) B3497165
theorem B4666193 : Blo 1381510 4666193 := bstep (se 2 (by rfl) ⟨1749822, by rfl⟩ : syracuseStep 4666193 = 3499645) B3499645
theorem B2954083 : Blo 1381510 2954083 := bstep (se 1 (by rfl) ⟨2215562, by rfl⟩ : syracuseStep 2954083 = 4431125) B4431125
theorem B8860529 : Blo 1381510 8860529 := bstep (se 2 (by rfl) ⟨3322698, by rfl⟩ : syracuseStep 8860529 = 6645397) B6645397
theorem B2626435 : Blo 1381510 2626435 := bstep (se 1 (by rfl) ⟨1969826, by rfl⟩ : syracuseStep 2626435 = 3939653) B3939653
theorem B2626481 : Blo 1381510 2626481 := bstep (se 2 (by rfl) ⟨984930, by rfl⟩ : syracuseStep 2626481 = 1969861) B1969861
theorem B2331571 : Blo 1381510 2331571 := bstep (se 1 (by rfl) ⟨1748678, by rfl⟩ : syracuseStep 2331571 = 3497357) B3497357
theorem B8852429 : Blo 1381510 8852429 := bstep (se 3 (by rfl) ⟨1659830, by rfl⟩ : syracuseStep 8852429 = 3319661) B3319661
theorem B5247949 : Blo 1381510 5247949 := bstep (se 3 (by rfl) ⟨983990, by rfl⟩ : syracuseStep 5247949 = 1967981) B1967981
theorem B3109841 : Blo 1381510 3109841 := bstep (se 2 (by rfl) ⟨1166190, by rfl⟩ : syracuseStep 3109841 = 2332381) B2332381
theorem B3109859 : Blo 1381510 3109859 := bstep (se 1 (by rfl) ⟨2332394, by rfl⟩ : syracuseStep 3109859 = 4664789) B4664789
theorem B3937261 : Blo 1381510 3937261 := bstep (se 3 (by rfl) ⟨738236, by rfl⟩ : syracuseStep 3937261 = 1476473) B1476473
theorem B10499057 : Blo 1381510 10499057 := bstep (se 2 (by rfl) ⟨3937146, by rfl⟩ : syracuseStep 10499057 = 7874293) B7874293
theorem B2331713 : Blo 1381510 2331713 := bstep (se 2 (by rfl) ⟨874392, by rfl⟩ : syracuseStep 2331713 = 1748785) B1748785
theorem B2397251 : Blo 1381510 2397251 := bstep (se 1 (by rfl) ⟨1797938, by rfl⟩ : syracuseStep 2397251 = 3595877) B3595877
theorem B4428881 : Blo 1381510 4428881 := bstep (se 2 (by rfl) ⟨1660830, by rfl⟩ : syracuseStep 4428881 = 3321661) B3321661
theorem B1381523 : Blo 1381510 1381523 := bstep (se 1 (by rfl) ⟨1036142, by rfl⟩ : syracuseStep 1381523 = 2072285) B2072285
theorem B1381539 : Blo 1381510 1381539 := bstep (se 1 (by rfl) ⟨1036154, by rfl⟩ : syracuseStep 1381539 = 2072309) B2072309
theorem B1381555 : Blo 1381510 1381555 := bstep (se 1 (by rfl) ⟨1036166, by rfl⟩ : syracuseStep 1381555 = 2072333) B2072333
theorem B2331841 : Blo 1381510 2331841 := bstep (se 2 (by rfl) ⟨874440, by rfl⟩ : syracuseStep 2331841 = 1748881) B1748881
theorem B1381571 : Blo 1381510 1381571 := bstep (se 1 (by rfl) ⟨1036178, by rfl⟩ : syracuseStep 1381571 = 2072357) B2072357
theorem B4429009 : Blo 1381510 4429009 := bstep (se 2 (by rfl) ⟨1660878, by rfl⟩ : syracuseStep 4429009 = 3321757) B3321757
theorem B1381587 : Blo 1381510 1381587 := bstep (se 1 (by rfl) ⟨1036190, by rfl⟩ : syracuseStep 1381587 = 2072381) B2072381
theorem B1381603 : Blo 1381510 1381603 := bstep (se 1 (by rfl) ⟨1036202, by rfl⟩ : syracuseStep 1381603 = 2072405) B2072405
theorem B2331875 : Blo 1381510 2331875 := bstep (se 1 (by rfl) ⟨1748906, by rfl⟩ : syracuseStep 2331875 = 3497813) B3497813
theorem B1750243 : Blo 1381510 1750243 := bstep (se 1 (by rfl) ⟨1312682, by rfl⟩ : syracuseStep 1750243 = 2625365) B2625365
theorem B7001315 : Blo 1381510 7001315 := bstep (se 1 (by rfl) ⟨5250986, by rfl⟩ : syracuseStep 7001315 = 10501973) B10501973
theorem B3110129 : Blo 1381510 3110129 := bstep (se 2 (by rfl) ⟨1166298, by rfl⟩ : syracuseStep 3110129 = 2332597) B2332597
theorem B1381619 : Blo 1381510 1381619 := bstep (se 1 (by rfl) ⟨1036214, by rfl⟩ : syracuseStep 1381619 = 2072429) B2072429
theorem B1381635 : Blo 1381510 1381635 := bstep (se 1 (by rfl) ⟨1036226, by rfl⟩ : syracuseStep 1381635 = 2072453) B2072453
theorem B3110147 : Blo 1381510 3110147 := bstep (se 1 (by rfl) ⟨2332610, by rfl⟩ : syracuseStep 3110147 = 4665221) B4665221
theorem B1381651 : Blo 1381510 1381651 := bstep (se 1 (by rfl) ⟨1036238, by rfl⟩ : syracuseStep 1381651 = 2072477) B2072477
theorem B1381667 : Blo 1381510 1381667 := bstep (se 1 (by rfl) ⟨1036250, by rfl⟩ : syracuseStep 1381667 = 2072501) B2072501
theorem B1381683 : Blo 1381510 1381683 := bstep (se 1 (by rfl) ⟨1036262, by rfl⟩ : syracuseStep 1381683 = 2072525) B2072525
theorem B1381699 : Blo 1381510 1381699 := bstep (se 1 (by rfl) ⟨1036274, by rfl⟩ : syracuseStep 1381699 = 2072549) B2072549
theorem B1750339 : Blo 1381510 1750339 := bstep (se 1 (by rfl) ⟨1312754, by rfl⟩ : syracuseStep 1750339 = 2625509) B2625509
theorem B1381715 : Blo 1381510 1381715 := bstep (se 1 (by rfl) ⟨1036286, by rfl⟩ : syracuseStep 1381715 = 2072573) B2072573
theorem B1381731 : Blo 1381510 1381731 := bstep (se 1 (by rfl) ⟨1036298, by rfl⟩ : syracuseStep 1381731 = 2072597) B2072597
theorem B2332003 : Blo 1381510 2332003 := bstep (se 1 (by rfl) ⟨1749002, by rfl⟩ : syracuseStep 2332003 = 3498005) B3498005
theorem B4666733 : Blo 1381510 4666733 := bstep (se 3 (by rfl) ⟨875012, by rfl⟩ : syracuseStep 4666733 = 1750025) B1750025
theorem B1381747 : Blo 1381510 1381747 := bstep (se 1 (by rfl) ⟨1036310, by rfl⟩ : syracuseStep 1381747 = 2072621) B2072621
theorem B1381763 : Blo 1381510 1381763 := bstep (se 1 (by rfl) ⟨1036322, by rfl⟩ : syracuseStep 1381763 = 2072645) B2072645
theorem B25228685 : Blo 1381510 25228685 := bstep (se 3 (by rfl) ⟨4730378, by rfl⟩ : syracuseStep 25228685 = 9460757) B9460757
theorem B1381779 : Blo 1381510 1381779 := bstep (se 1 (by rfl) ⟨1036334, by rfl⟩ : syracuseStep 1381779 = 2072669) B2072669
theorem B1381795 : Blo 1381510 1381795 := bstep (se 1 (by rfl) ⟨1036346, by rfl⟩ : syracuseStep 1381795 = 2072693) B2072693
theorem B4666787 : Blo 1381510 4666787 := bstep (se 1 (by rfl) ⟨3500090, by rfl⟩ : syracuseStep 4666787 = 7000181) B7000181
theorem B1381811 : Blo 1381510 1381811 := bstep (se 1 (by rfl) ⟨1036358, by rfl⟩ : syracuseStep 1381811 = 2072717) B2072717
theorem B1381827 : Blo 1381510 1381827 := bstep (se 1 (by rfl) ⟨1036370, by rfl⟩ : syracuseStep 1381827 = 2072741) B2072741
theorem B1381843 : Blo 1381510 1381843 := bstep (se 1 (by rfl) ⟨1036382, by rfl⟩ : syracuseStep 1381843 = 2072765) B2072765
theorem B1381859 : Blo 1381510 1381859 := bstep (se 1 (by rfl) ⟨1036394, by rfl⟩ : syracuseStep 1381859 = 2072789) B2072789
theorem B2332145 : Blo 1381510 2332145 := bstep (se 2 (by rfl) ⟨874554, by rfl⟩ : syracuseStep 2332145 = 1749109) B1749109
theorem B1381875 : Blo 1381510 1381875 := bstep (se 1 (by rfl) ⟨1036406, by rfl⟩ : syracuseStep 1381875 = 2072813) B2072813
theorem B1381891 : Blo 1381510 1381891 := bstep (se 1 (by rfl) ⟨1036418, by rfl⟩ : syracuseStep 1381891 = 2072837) B2072837
theorem B3110417 : Blo 1381510 3110417 := bstep (se 2 (by rfl) ⟨1166406, by rfl⟩ : syracuseStep 3110417 = 2332813) B2332813
theorem B1381907 : Blo 1381510 1381907 := bstep (se 1 (by rfl) ⟨1036430, by rfl⟩ : syracuseStep 1381907 = 2072861) B2072861
theorem B1381923 : Blo 1381510 1381923 := bstep (se 1 (by rfl) ⟨1036442, by rfl⟩ : syracuseStep 1381923 = 2072885) B2072885
theorem B3110435 : Blo 1381510 3110435 := bstep (se 1 (by rfl) ⟨2332826, by rfl⟩ : syracuseStep 3110435 = 4665653) B4665653
theorem B1381939 : Blo 1381510 1381939 := bstep (se 1 (by rfl) ⟨1036454, by rfl⟩ : syracuseStep 1381939 = 2072909) B2072909
theorem B1381955 : Blo 1381510 1381955 := bstep (se 1 (by rfl) ⟨1036466, by rfl⟩ : syracuseStep 1381955 = 2072933) B2072933
theorem B1381971 : Blo 1381510 1381971 := bstep (se 1 (by rfl) ⟨1036478, by rfl⟩ : syracuseStep 1381971 = 2072957) B2072957
theorem B1381987 : Blo 1381510 1381987 := bstep (se 1 (by rfl) ⟨1036490, by rfl⟩ : syracuseStep 1381987 = 2072981) B2072981
theorem B1496675 : Blo 1381510 1496675 := bstep (se 1 (by rfl) ⟨1122506, by rfl⟩ : syracuseStep 1496675 = 2245013) B2245013
theorem B2332273 : Blo 1381510 2332273 := bstep (se 2 (by rfl) ⟨874602, by rfl⟩ : syracuseStep 2332273 = 1749205) B1749205
theorem B1382003 : Blo 1381510 1382003 := bstep (se 1 (by rfl) ⟨1036502, by rfl⟩ : syracuseStep 1382003 = 2073005) B2073005
theorem B1382019 : Blo 1381510 1382019 := bstep (se 1 (by rfl) ⟨1036514, by rfl⟩ : syracuseStep 1382019 = 2073029) B2073029
theorem B1382035 : Blo 1381510 1382035 := bstep (se 1 (by rfl) ⟨1036526, by rfl⟩ : syracuseStep 1382035 = 2073053) B2073053
theorem B2332307 : Blo 1381510 2332307 := bstep (se 1 (by rfl) ⟨1749230, by rfl⟩ : syracuseStep 2332307 = 3498461) B3498461
theorem B1382051 : Blo 1381510 1382051 := bstep (se 1 (by rfl) ⟨1036538, by rfl⟩ : syracuseStep 1382051 = 2073077) B2073077
theorem B4667057 : Blo 1381510 4667057 := bstep (se 2 (by rfl) ⟨1750146, by rfl⟩ : syracuseStep 4667057 = 3500293) B3500293
theorem B1382067 : Blo 1381510 1382067 := bstep (se 1 (by rfl) ⟨1036550, by rfl⟩ : syracuseStep 1382067 = 2073101) B2073101
theorem B1382083 : Blo 1381510 1382083 := bstep (se 1 (by rfl) ⟨1036562, by rfl⟩ : syracuseStep 1382083 = 2073125) B2073125
theorem B1382099 : Blo 1381510 1382099 := bstep (se 1 (by rfl) ⟨1036574, by rfl⟩ : syracuseStep 1382099 = 2073149) B2073149
theorem B1382115 : Blo 1381510 1382115 := bstep (se 1 (by rfl) ⟨1036586, by rfl⟩ : syracuseStep 1382115 = 2073173) B2073173
theorem B5248739 : Blo 1381510 5248739 := bstep (se 1 (by rfl) ⟨3936554, by rfl⟩ : syracuseStep 5248739 = 7873109) B7873109
theorem B7870193 : Blo 1381510 7870193 := bstep (se 2 (by rfl) ⟨2951322, by rfl⟩ : syracuseStep 7870193 = 5902645) B5902645
theorem B1382131 : Blo 1381510 1382131 := bstep (se 1 (by rfl) ⟨1036598, by rfl⟩ : syracuseStep 1382131 = 2073197) B2073197
theorem B1382147 : Blo 1381510 1382147 := bstep (se 1 (by rfl) ⟨1036610, by rfl⟩ : syracuseStep 1382147 = 2073221) B2073221
theorem B1382163 : Blo 1381510 1382163 := bstep (se 1 (by rfl) ⟨1036622, by rfl⟩ : syracuseStep 1382163 = 2073245) B2073245
theorem B2332435 : Blo 1381510 2332435 := bstep (se 1 (by rfl) ⟨1749326, by rfl⟩ : syracuseStep 2332435 = 3498653) B3498653
theorem B1382179 : Blo 1381510 1382179 := bstep (se 1 (by rfl) ⟨1036634, by rfl⟩ : syracuseStep 1382179 = 2073269) B2073269
theorem B3110705 : Blo 1381510 3110705 := bstep (se 2 (by rfl) ⟨1166514, by rfl⟩ : syracuseStep 3110705 = 2333029) B2333029
theorem B1382195 : Blo 1381510 1382195 := bstep (se 1 (by rfl) ⟨1036646, by rfl⟩ : syracuseStep 1382195 = 2073293) B2073293
theorem B16807733 : Blo 1381510 16807733 := bstep (se 5 (by rfl) ⟨787862, by rfl⟩ : syracuseStep 16807733 = 1575725) B1575725
theorem B1750835 : Blo 1381510 1750835 := bstep (se 1 (by rfl) ⟨1313126, by rfl⟩ : syracuseStep 1750835 = 2626253) B2626253
theorem B1382211 : Blo 1381510 1382211 := bstep (se 1 (by rfl) ⟨1036658, by rfl⟩ : syracuseStep 1382211 = 2073317) B2073317
theorem B3110723 : Blo 1381510 3110723 := bstep (se 1 (by rfl) ⟨2333042, by rfl⟩ : syracuseStep 3110723 = 4666085) B4666085
theorem B7477069 : Blo 1381510 7477069 := bstep (se 3 (by rfl) ⟨1401950, by rfl⟩ : syracuseStep 7477069 = 2803901) B2803901
theorem B1554259 : Blo 1381510 1554259 := bstep (se 1 (by rfl) ⟨1165694, by rfl⟩ : syracuseStep 1554259 = 2331389) B2331389
theorem B1382227 : Blo 1381510 1382227 := bstep (se 1 (by rfl) ⟨1036670, by rfl⟩ : syracuseStep 1382227 = 2073341) B2073341
theorem B1382243 : Blo 1381510 1382243 := bstep (se 1 (by rfl) ⟨1036682, by rfl⟩ : syracuseStep 1382243 = 2073365) B2073365
theorem B1382259 : Blo 1381510 1382259 := bstep (se 1 (by rfl) ⟨1036694, by rfl⟩ : syracuseStep 1382259 = 2073389) B2073389
theorem B1382275 : Blo 1381510 1382275 := bstep (se 1 (by rfl) ⟨1036706, by rfl⟩ : syracuseStep 1382275 = 2073413) B2073413
theorem B2840465 : Blo 1381510 2840465 := bstep (se 2 (by rfl) ⟨1065174, by rfl⟩ : syracuseStep 2840465 = 2130349) B2130349
theorem B1382291 : Blo 1381510 1382291 := bstep (se 1 (by rfl) ⟨1036718, by rfl⟩ : syracuseStep 1382291 = 2073437) B2073437
theorem B2332577 : Blo 1381510 2332577 := bstep (se 2 (by rfl) ⟨874716, by rfl⟩ : syracuseStep 2332577 = 1749433) B1749433
theorem B1382307 : Blo 1381510 1382307 := bstep (se 1 (by rfl) ⟨1036730, by rfl⟩ : syracuseStep 1382307 = 2073461) B2073461
theorem B1382323 : Blo 1381510 1382323 := bstep (se 1 (by rfl) ⟨1036742, by rfl⟩ : syracuseStep 1382323 = 2073485) B2073485
theorem B1382339 : Blo 1381510 1382339 := bstep (se 1 (by rfl) ⟨1036754, by rfl⟩ : syracuseStep 1382339 = 2073509) B2073509
theorem B1382355 : Blo 1381510 1382355 := bstep (se 1 (by rfl) ⟨1036766, by rfl⟩ : syracuseStep 1382355 = 2073533) B2073533
theorem B1554403 : Blo 1381510 1554403 := bstep (se 1 (by rfl) ⟨1165802, by rfl⟩ : syracuseStep 1554403 = 2331605) B2331605
theorem B1382371 : Blo 1381510 1382371 := bstep (se 1 (by rfl) ⟨1036778, by rfl⟩ : syracuseStep 1382371 = 2073557) B2073557
theorem B1382387 : Blo 1381510 1382387 := bstep (se 1 (by rfl) ⟨1036790, by rfl⟩ : syracuseStep 1382387 = 2073581) B2073581
theorem B1382403 : Blo 1381510 1382403 := bstep (se 1 (by rfl) ⟨1036802, by rfl⟩ : syracuseStep 1382403 = 2073605) B2073605
theorem B7002125 : Blo 1381510 7002125 := bstep (se 3 (by rfl) ⟨1312898, by rfl⟩ : syracuseStep 7002125 = 2625797) B2625797
theorem B3938321 : Blo 1381510 3938321 := bstep (se 2 (by rfl) ⟨1476870, by rfl⟩ : syracuseStep 3938321 = 2953741) B2953741
theorem B1382419 : Blo 1381510 1382419 := bstep (se 1 (by rfl) ⟨1036814, by rfl⟩ : syracuseStep 1382419 = 2073629) B2073629
theorem B2332705 : Blo 1381510 2332705 := bstep (se 2 (by rfl) ⟨874764, by rfl⟩ : syracuseStep 2332705 = 1749529) B1749529
theorem B1382435 : Blo 1381510 1382435 := bstep (se 1 (by rfl) ⟨1036826, by rfl⟩ : syracuseStep 1382435 = 2073653) B2073653
theorem B1382451 : Blo 1381510 1382451 := bstep (se 1 (by rfl) ⟨1036838, by rfl⟩ : syracuseStep 1382451 = 2073677) B2073677
theorem B2332739 : Blo 1381510 2332739 := bstep (se 1 (by rfl) ⟨1749554, by rfl⟩ : syracuseStep 2332739 = 3499109) B3499109
theorem B1382467 : Blo 1381510 1382467 := bstep (se 1 (by rfl) ⟨1036850, by rfl⟩ : syracuseStep 1382467 = 2073701) B2073701
theorem B3110993 : Blo 1381510 3110993 := bstep (se 2 (by rfl) ⟨1166622, by rfl⟩ : syracuseStep 3110993 = 2333245) B2333245
theorem B1382483 : Blo 1381510 1382483 := bstep (se 1 (by rfl) ⟨1036862, by rfl⟩ : syracuseStep 1382483 = 2073725) B2073725
theorem B1382499 : Blo 1381510 1382499 := bstep (se 1 (by rfl) ⟨1036874, by rfl⟩ : syracuseStep 1382499 = 2073749) B2073749
theorem B3111011 : Blo 1381510 3111011 := bstep (se 1 (by rfl) ⟨2333258, by rfl⟩ : syracuseStep 3111011 = 4666517) B4666517
theorem B2881649 : Blo 1381510 2881649 := bstep (se 2 (by rfl) ⟨1080618, by rfl⟩ : syracuseStep 2881649 = 2161237) B2161237
theorem B1554547 : Blo 1381510 1554547 := bstep (se 1 (by rfl) ⟨1165910, by rfl⟩ : syracuseStep 1554547 = 2331821) B2331821
theorem B1382515 : Blo 1381510 1382515 := bstep (se 1 (by rfl) ⟨1036886, by rfl⟩ : syracuseStep 1382515 = 2073773) B2073773
theorem B2103425 : Blo 1381510 2103425 := bstep (se 2 (by rfl) ⟨788784, by rfl⟩ : syracuseStep 2103425 = 1577569) B1577569
theorem B1382531 : Blo 1381510 1382531 := bstep (se 1 (by rfl) ⟨1036898, by rfl⟩ : syracuseStep 1382531 = 2073797) B2073797
theorem B3324035 : Blo 1381510 3324035 := bstep (se 1 (by rfl) ⟨2493026, by rfl⟩ : syracuseStep 3324035 = 4986053) B4986053
theorem B1382547 : Blo 1381510 1382547 := bstep (se 1 (by rfl) ⟨1036910, by rfl⟩ : syracuseStep 1382547 = 2073821) B2073821
theorem B1382563 : Blo 1381510 1382563 := bstep (se 1 (by rfl) ⟨1036922, by rfl⟩ : syracuseStep 1382563 = 2073845) B2073845
theorem B4429997 : Blo 1381510 4429997 := bstep (se 3 (by rfl) ⟨830624, by rfl⟩ : syracuseStep 4429997 = 1661249) B1661249
theorem B1382579 : Blo 1381510 1382579 := bstep (se 1 (by rfl) ⟨1036934, by rfl⟩ : syracuseStep 1382579 = 2073869) B2073869
theorem B2332867 : Blo 1381510 2332867 := bstep (se 1 (by rfl) ⟨1749650, by rfl⟩ : syracuseStep 2332867 = 3499301) B3499301
theorem B1382595 : Blo 1381510 1382595 := bstep (se 1 (by rfl) ⟨1036946, by rfl⟩ : syracuseStep 1382595 = 2073893) B2073893
theorem B4667597 : Blo 1381510 4667597 := bstep (se 3 (by rfl) ⟨875174, by rfl⟩ : syracuseStep 4667597 = 1750349) B1750349
theorem B1382611 : Blo 1381510 1382611 := bstep (se 1 (by rfl) ⟨1036958, by rfl⟩ : syracuseStep 1382611 = 2073917) B2073917
theorem B1382627 : Blo 1381510 1382627 := bstep (se 1 (by rfl) ⟨1036970, by rfl⟩ : syracuseStep 1382627 = 2073941) B2073941
theorem B8411363 : Blo 1381510 8411363 := bstep (se 1 (by rfl) ⟨6308522, by rfl⟩ : syracuseStep 8411363 = 12617045) B12617045
theorem B1382643 : Blo 1381510 1382643 := bstep (se 1 (by rfl) ⟨1036982, by rfl⟩ : syracuseStep 1382643 = 2073965) B2073965
theorem B1554691 : Blo 1381510 1554691 := bstep (se 1 (by rfl) ⟨1166018, by rfl⟩ : syracuseStep 1554691 = 2332037) B2332037
theorem B1382659 : Blo 1381510 1382659 := bstep (se 1 (by rfl) ⟨1036994, by rfl⟩ : syracuseStep 1382659 = 2073989) B2073989
theorem B4667651 : Blo 1381510 4667651 := bstep (se 1 (by rfl) ⟨3500738, by rfl⟩ : syracuseStep 4667651 = 7001477) B7001477
theorem B1382675 : Blo 1381510 1382675 := bstep (se 1 (by rfl) ⟨1037006, by rfl⟩ : syracuseStep 1382675 = 2074013) B2074013
theorem B1382691 : Blo 1381510 1382691 := bstep (se 1 (by rfl) ⟨1037018, by rfl⟩ : syracuseStep 1382691 = 2074037) B2074037
theorem B1382707 : Blo 1381510 1382707 := bstep (se 1 (by rfl) ⟨1037030, by rfl⟩ : syracuseStep 1382707 = 2074061) B2074061
theorem B1382723 : Blo 1381510 1382723 := bstep (se 1 (by rfl) ⟨1037042, by rfl⟩ : syracuseStep 1382723 = 2074085) B2074085
theorem B2333009 : Blo 1381510 2333009 := bstep (se 2 (by rfl) ⟨874878, by rfl⟩ : syracuseStep 2333009 = 1749757) B1749757
theorem B1382739 : Blo 1381510 1382739 := bstep (se 1 (by rfl) ⟨1037054, by rfl⟩ : syracuseStep 1382739 = 2074109) B2074109
theorem B1382755 : Blo 1381510 1382755 := bstep (se 1 (by rfl) ⟨1037066, by rfl⟩ : syracuseStep 1382755 = 2074133) B2074133
theorem B5249393 : Blo 1381510 5249393 := bstep (se 2 (by rfl) ⟨1968522, by rfl⟩ : syracuseStep 5249393 = 3937045) B3937045
theorem B1382771 : Blo 1381510 1382771 := bstep (se 1 (by rfl) ⟨1037078, by rfl⟩ : syracuseStep 1382771 = 2074157) B2074157
theorem B3111281 : Blo 1381510 3111281 := bstep (se 2 (by rfl) ⟨1166730, by rfl⟩ : syracuseStep 3111281 = 2333461) B2333461
theorem B1382787 : Blo 1381510 1382787 := bstep (se 1 (by rfl) ⟨1037090, by rfl⟩ : syracuseStep 1382787 = 2074181) B2074181
theorem B3111299 : Blo 1381510 3111299 := bstep (se 1 (by rfl) ⟨2333474, by rfl⟩ : syracuseStep 3111299 = 4666949) B4666949
theorem B1554835 : Blo 1381510 1554835 := bstep (se 1 (by rfl) ⟨1166126, by rfl⟩ : syracuseStep 1554835 = 2332253) B2332253
theorem B1382803 : Blo 1381510 1382803 := bstep (se 1 (by rfl) ⟨1037102, by rfl⟩ : syracuseStep 1382803 = 2074205) B2074205
theorem B1382819 : Blo 1381510 1382819 := bstep (se 1 (by rfl) ⟨1037114, by rfl⟩ : syracuseStep 1382819 = 2074229) B2074229
theorem B1382835 : Blo 1381510 1382835 := bstep (se 1 (by rfl) ⟨1037126, by rfl⟩ : syracuseStep 1382835 = 2074253) B2074253
theorem B17725877 : Blo 1381510 17725877 := bstep (se 5 (by rfl) ⟨830900, by rfl⟩ : syracuseStep 17725877 = 1661801) B1661801
theorem B1382851 : Blo 1381510 1382851 := bstep (se 1 (by rfl) ⟨1037138, by rfl⟩ : syracuseStep 1382851 = 2074277) B2074277
theorem B17955269 : Blo 1381510 17955269 := bstep (se 4 (by rfl) ⟨1683306, by rfl⟩ : syracuseStep 17955269 = 3366613) B3366613
theorem B2333137 : Blo 1381510 2333137 := bstep (se 2 (by rfl) ⟨874926, by rfl⟩ : syracuseStep 2333137 = 1749853) B1749853
theorem B1382867 : Blo 1381510 1382867 := bstep (se 1 (by rfl) ⟨1037150, by rfl⟩ : syracuseStep 1382867 = 2074301) B2074301
theorem B1382883 : Blo 1381510 1382883 := bstep (se 1 (by rfl) ⟨1037162, by rfl⟩ : syracuseStep 1382883 = 2074325) B2074325
theorem B2333171 : Blo 1381510 2333171 := bstep (se 1 (by rfl) ⟨1749878, by rfl⟩ : syracuseStep 2333171 = 3499757) B3499757
theorem B1382899 : Blo 1381510 1382899 := bstep (se 1 (by rfl) ⟨1037174, by rfl⟩ : syracuseStep 1382899 = 2074349) B2074349
theorem B1382915 : Blo 1381510 1382915 := bstep (se 1 (by rfl) ⟨1037186, by rfl⟩ : syracuseStep 1382915 = 2074373) B2074373
theorem B1382931 : Blo 1381510 1382931 := bstep (se 1 (by rfl) ⟨1037198, by rfl⟩ : syracuseStep 1382931 = 2074397) B2074397
theorem B4667921 : Blo 1381510 4667921 := bstep (se 2 (by rfl) ⟨1750470, by rfl⟩ : syracuseStep 4667921 = 3500941) B3500941
theorem B1554979 : Blo 1381510 1554979 := bstep (se 1 (by rfl) ⟨1166234, by rfl⟩ : syracuseStep 1554979 = 2332469) B2332469
theorem B1382947 : Blo 1381510 1382947 := bstep (se 1 (by rfl) ⟨1037210, by rfl⟩ : syracuseStep 1382947 = 2074421) B2074421
theorem B1382963 : Blo 1381510 1382963 := bstep (se 1 (by rfl) ⟨1037222, by rfl⟩ : syracuseStep 1382963 = 2074445) B2074445
theorem B1382979 : Blo 1381510 1382979 := bstep (se 1 (by rfl) ⟨1037234, by rfl⟩ : syracuseStep 1382979 = 2074469) B2074469
theorem B1382995 : Blo 1381510 1382995 := bstep (se 1 (by rfl) ⟨1037246, by rfl⟩ : syracuseStep 1382995 = 2074493) B2074493
theorem B6306403 : Blo 1381510 6306403 := bstep (se 1 (by rfl) ⟨4729802, by rfl⟩ : syracuseStep 6306403 = 9459605) B9459605
theorem B1383011 : Blo 1381510 1383011 := bstep (se 1 (by rfl) ⟨1037258, by rfl⟩ : syracuseStep 1383011 = 2074517) B2074517
theorem B2333299 : Blo 1381510 2333299 := bstep (se 1 (by rfl) ⟨1749974, by rfl⟩ : syracuseStep 2333299 = 3499949) B3499949
theorem B1383027 : Blo 1381510 1383027 := bstep (se 1 (by rfl) ⟨1037270, by rfl⟩ : syracuseStep 1383027 = 2074541) B2074541
theorem B1383043 : Blo 1381510 1383043 := bstep (se 1 (by rfl) ⟨1037282, by rfl⟩ : syracuseStep 1383043 = 2074565) B2074565
theorem B5905037 : Blo 1381510 5905037 := bstep (se 3 (by rfl) ⟨1107194, by rfl⟩ : syracuseStep 5905037 = 2214389) B2214389
theorem B3111569 : Blo 1381510 3111569 := bstep (se 2 (by rfl) ⟨1166838, by rfl⟩ : syracuseStep 3111569 = 2333677) B2333677
theorem B1383059 : Blo 1381510 1383059 := bstep (se 1 (by rfl) ⟨1037294, by rfl⟩ : syracuseStep 1383059 = 2074589) B2074589
theorem B3111587 : Blo 1381510 3111587 := bstep (se 1 (by rfl) ⟨2333690, by rfl⟩ : syracuseStep 3111587 = 4667381) B4667381
theorem B1383075 : Blo 1381510 1383075 := bstep (se 1 (by rfl) ⟨1037306, by rfl⟩ : syracuseStep 1383075 = 2074613) B2074613
theorem B3938993 : Blo 1381510 3938993 := bstep (se 2 (by rfl) ⟨1477122, by rfl⟩ : syracuseStep 3938993 = 2954245) B2954245
theorem B1555123 : Blo 1381510 1555123 := bstep (se 1 (by rfl) ⟨1166342, by rfl⟩ : syracuseStep 1555123 = 2332685) B2332685
theorem B1383091 : Blo 1381510 1383091 := bstep (se 1 (by rfl) ⟨1037318, by rfl⟩ : syracuseStep 1383091 = 2074637) B2074637
theorem B1383107 : Blo 1381510 1383107 := bstep (se 1 (by rfl) ⟨1037330, by rfl⟩ : syracuseStep 1383107 = 2074661) B2074661
theorem B1383123 : Blo 1381510 1383123 := bstep (se 1 (by rfl) ⟨1037342, by rfl⟩ : syracuseStep 1383123 = 2074685) B2074685
theorem B1383139 : Blo 1381510 1383139 := bstep (se 1 (by rfl) ⟨1037354, by rfl⟩ : syracuseStep 1383139 = 2074709) B2074709
theorem B6994673 : Blo 1381510 6994673 := bstep (se 2 (by rfl) ⟨2623002, by rfl⟩ : syracuseStep 6994673 = 5246005) B5246005
theorem B1383155 : Blo 1381510 1383155 := bstep (se 1 (by rfl) ⟨1037366, by rfl⟩ : syracuseStep 1383155 = 2074733) B2074733
theorem B2333441 : Blo 1381510 2333441 := bstep (se 2 (by rfl) ⟨875040, by rfl⟩ : syracuseStep 2333441 = 1750081) B1750081
theorem B1383171 : Blo 1381510 1383171 := bstep (se 1 (by rfl) ⟨1037378, by rfl⟩ : syracuseStep 1383171 = 2074757) B2074757
theorem B1383187 : Blo 1381510 1383187 := bstep (se 1 (by rfl) ⟨1037390, by rfl⟩ : syracuseStep 1383187 = 2074781) B2074781
theorem B1383203 : Blo 1381510 1383203 := bstep (se 1 (by rfl) ⟨1037402, by rfl⟩ : syracuseStep 1383203 = 2074805) B2074805
theorem B1383219 : Blo 1381510 1383219 := bstep (se 1 (by rfl) ⟨1037414, by rfl⟩ : syracuseStep 1383219 = 2074829) B2074829
theorem B1555267 : Blo 1381510 1555267 := bstep (se 1 (by rfl) ⟨1166450, by rfl⟩ : syracuseStep 1555267 = 2332901) B2332901
theorem B1383235 : Blo 1381510 1383235 := bstep (se 1 (by rfl) ⟨1037426, by rfl⟩ : syracuseStep 1383235 = 2074853) B2074853
theorem B1383251 : Blo 1381510 1383251 := bstep (se 1 (by rfl) ⟨1037438, by rfl⟩ : syracuseStep 1383251 = 2074877) B2074877
theorem B16169827 : Blo 1381510 16169827 := bstep (se 1 (by rfl) ⟨12127370, by rfl⟩ : syracuseStep 16169827 = 24254741) B24254741
theorem B1383267 : Blo 1381510 1383267 := bstep (se 1 (by rfl) ⟨1037450, by rfl⟩ : syracuseStep 1383267 = 2074901) B2074901
theorem B1383283 : Blo 1381510 1383283 := bstep (se 1 (by rfl) ⟨1037462, by rfl⟩ : syracuseStep 1383283 = 2074925) B2074925
theorem B2333569 : Blo 1381510 2333569 := bstep (se 2 (by rfl) ⟨875088, by rfl⟩ : syracuseStep 2333569 = 1750177) B1750177
theorem B1383299 : Blo 1381510 1383299 := bstep (se 1 (by rfl) ⟨1037474, by rfl⟩ : syracuseStep 1383299 = 2074949) B2074949
theorem B1383315 : Blo 1381510 1383315 := bstep (se 1 (by rfl) ⟨1037486, by rfl⟩ : syracuseStep 1383315 = 2074973) B2074973
theorem B2333603 : Blo 1381510 2333603 := bstep (se 1 (by rfl) ⟨1750202, by rfl⟩ : syracuseStep 2333603 = 3500405) B3500405
theorem B1383331 : Blo 1381510 1383331 := bstep (se 1 (by rfl) ⟨1037498, by rfl⟩ : syracuseStep 1383331 = 2074997) B2074997
theorem B3111857 : Blo 1381510 3111857 := bstep (se 2 (by rfl) ⟨1166946, by rfl⟩ : syracuseStep 3111857 = 2333893) B2333893
theorem B1383347 : Blo 1381510 1383347 := bstep (se 1 (by rfl) ⟨1037510, by rfl⟩ : syracuseStep 1383347 = 2075021) B2075021
theorem B3111875 : Blo 1381510 3111875 := bstep (se 1 (by rfl) ⟨2333906, by rfl⟩ : syracuseStep 3111875 = 4667813) B4667813
theorem B1383363 : Blo 1381510 1383363 := bstep (se 1 (by rfl) ⟨1037522, by rfl⟩ : syracuseStep 1383363 = 2075045) B2075045
theorem B1555411 : Blo 1381510 1555411 := bstep (se 1 (by rfl) ⟨1166558, by rfl⟩ : syracuseStep 1555411 = 2333117) B2333117
theorem B1383379 : Blo 1381510 1383379 := bstep (se 1 (by rfl) ⟨1037534, by rfl⟩ : syracuseStep 1383379 = 2075069) B2075069
theorem B5905379 : Blo 1381510 5905379 := bstep (se 1 (by rfl) ⟨4429034, by rfl⟩ : syracuseStep 5905379 = 8858069) B8858069
theorem B1383395 : Blo 1381510 1383395 := bstep (se 1 (by rfl) ⟨1037546, by rfl⟩ : syracuseStep 1383395 = 2075093) B2075093
theorem B1383411 : Blo 1381510 1383411 := bstep (se 1 (by rfl) ⟨1037558, by rfl⟩ : syracuseStep 1383411 = 2075117) B2075117
theorem B1383427 : Blo 1381510 1383427 := bstep (se 1 (by rfl) ⟨1037570, by rfl⟩ : syracuseStep 1383427 = 2075141) B2075141
theorem B1383443 : Blo 1381510 1383443 := bstep (se 1 (by rfl) ⟨1037582, by rfl⟩ : syracuseStep 1383443 = 2075165) B2075165
theorem B2333731 : Blo 1381510 2333731 := bstep (se 1 (by rfl) ⟨1750298, by rfl⟩ : syracuseStep 2333731 = 3500597) B3500597
theorem B1383459 : Blo 1381510 1383459 := bstep (se 1 (by rfl) ⟨1037594, by rfl⟩ : syracuseStep 1383459 = 2075189) B2075189
theorem B4668461 : Blo 1381510 4668461 := bstep (se 3 (by rfl) ⟨875336, by rfl⟩ : syracuseStep 4668461 = 1750673) B1750673
theorem B1383475 : Blo 1381510 1383475 := bstep (se 1 (by rfl) ⟨1037606, by rfl⟩ : syracuseStep 1383475 = 2075213) B2075213
theorem B1383491 : Blo 1381510 1383491 := bstep (se 1 (by rfl) ⟨1037618, by rfl⟩ : syracuseStep 1383491 = 2075237) B2075237
theorem B1383507 : Blo 1381510 1383507 := bstep (se 1 (by rfl) ⟨1037630, by rfl⟩ : syracuseStep 1383507 = 2075261) B2075261
theorem B1555555 : Blo 1381510 1555555 := bstep (se 1 (by rfl) ⟨1166666, by rfl⟩ : syracuseStep 1555555 = 2333333) B2333333
theorem B4668515 : Blo 1381510 4668515 := bstep (se 1 (by rfl) ⟨3501386, by rfl⟩ : syracuseStep 4668515 = 7002773) B7002773
theorem B7871651 : Blo 1381510 7871651 := bstep (se 1 (by rfl) ⟨5903738, by rfl⟩ : syracuseStep 7871651 = 11807477) B11807477
theorem B2333873 : Blo 1381510 2333873 := bstep (se 2 (by rfl) ⟨875202, by rfl⟩ : syracuseStep 2333873 = 1750405) B1750405
theorem B3112145 : Blo 1381510 3112145 := bstep (se 2 (by rfl) ⟨1167054, by rfl⟩ : syracuseStep 3112145 = 2334109) B2334109
theorem B3112163 : Blo 1381510 3112163 := bstep (se 1 (by rfl) ⟨2334122, by rfl⟩ : syracuseStep 3112163 = 4668245) B4668245
theorem B1555699 : Blo 1381510 1555699 := bstep (se 1 (by rfl) ⟨1166774, by rfl⟩ : syracuseStep 1555699 = 2333549) B2333549
theorem B2334001 : Blo 1381510 2334001 := bstep (se 2 (by rfl) ⟨875250, by rfl⟩ : syracuseStep 2334001 = 1750501) B1750501
theorem B2334035 : Blo 1381510 2334035 := bstep (se 1 (by rfl) ⟨1750526, by rfl⟩ : syracuseStep 2334035 = 3501053) B3501053
theorem B4668785 : Blo 1381510 4668785 := bstep (se 2 (by rfl) ⟨1750794, by rfl⟩ : syracuseStep 4668785 = 3501589) B3501589
theorem B1555843 : Blo 1381510 1555843 := bstep (se 1 (by rfl) ⟨1166882, by rfl⟩ : syracuseStep 1555843 = 2333765) B2333765
theorem B5324237 : Blo 1381510 5324237 := bstep (se 3 (by rfl) ⟨998294, by rfl⟩ : syracuseStep 5324237 = 1996589) B1996589
theorem B2334163 : Blo 1381510 2334163 := bstep (se 1 (by rfl) ⟨1750622, by rfl⟩ : syracuseStep 2334163 = 3501245) B3501245
theorem B4431341 : Blo 1381510 4431341 := bstep (se 3 (by rfl) ⟨830876, by rfl⟩ : syracuseStep 4431341 = 1661753) B1661753
theorem B3112433 : Blo 1381510 3112433 := bstep (se 2 (by rfl) ⟨1167162, by rfl⟩ : syracuseStep 3112433 = 2334325) B2334325
theorem B3112451 : Blo 1381510 3112451 := bstep (se 1 (by rfl) ⟨2334338, by rfl⟩ : syracuseStep 3112451 = 4668677) B4668677
theorem B3497489 : Blo 1381510 3497489 := bstep (se 2 (by rfl) ⟨1311558, by rfl⟩ : syracuseStep 3497489 = 2623117) B2623117
theorem B1555987 : Blo 1381510 1555987 := bstep (se 1 (by rfl) ⟨1166990, by rfl⟩ : syracuseStep 1555987 = 2333981) B2333981
theorem B3497539 : Blo 1381510 3497539 := bstep (se 1 (by rfl) ⟨2623154, by rfl⟩ : syracuseStep 3497539 = 5246309) B5246309
theorem B2334305 : Blo 1381510 2334305 := bstep (se 2 (by rfl) ⟨875364, by rfl⟩ : syracuseStep 2334305 = 1750729) B1750729
theorem B18923149 : Blo 1381510 18923149 := bstep (se 3 (by rfl) ⟨3548090, by rfl⟩ : syracuseStep 18923149 = 7096181) B7096181
theorem B1556131 : Blo 1381510 1556131 := bstep (se 1 (by rfl) ⟨1167098, by rfl⟩ : syracuseStep 1556131 = 2334197) B2334197
theorem B13278917 : Blo 1381510 13278917 := bstep (se 4 (by rfl) ⟨1244898, by rfl⟩ : syracuseStep 13278917 = 2489797) B2489797
theorem B2072273 : Blo 1381510 2072273 := bstep (se 2 (by rfl) ⟨777102, by rfl⟩ : syracuseStep 2072273 = 1554205) B1554205
theorem B3497681 : Blo 1381510 3497681 := bstep (se 2 (by rfl) ⟨1311630, by rfl⟩ : syracuseStep 3497681 = 2623261) B2623261
theorem B2334433 : Blo 1381510 2334433 := bstep (se 2 (by rfl) ⟨875412, by rfl⟩ : syracuseStep 2334433 = 1750825) B1750825
theorem B2072291 : Blo 1381510 2072291 := bstep (se 1 (by rfl) ⟨1554218, by rfl⟩ : syracuseStep 2072291 = 3108437) B3108437
theorem B2072321 : Blo 1381510 2072321 := bstep (se 2 (by rfl) ⟨777120, by rfl⟩ : syracuseStep 2072321 = 1554241) B1554241
theorem B2334467 : Blo 1381510 2334467 := bstep (se 1 (by rfl) ⟨1750850, by rfl⟩ : syracuseStep 2334467 = 3501701) B3501701
theorem B8863501 : Blo 1381510 8863501 := bstep (se 3 (by rfl) ⟨1661906, by rfl⟩ : syracuseStep 8863501 = 3323813) B3323813
theorem B3112721 : Blo 1381510 3112721 := bstep (se 2 (by rfl) ⟨1167270, by rfl⟩ : syracuseStep 3112721 = 2334541) B2334541
theorem B2072339 : Blo 1381510 2072339 := bstep (se 1 (by rfl) ⟨1554254, by rfl⟩ : syracuseStep 2072339 = 3108509) B3108509
theorem B7470883 : Blo 1381510 7470883 := bstep (se 1 (by rfl) ⟨5603162, by rfl⟩ : syracuseStep 7470883 = 11206325) B11206325
theorem B5250851 : Blo 1381510 5250851 := bstep (se 1 (by rfl) ⟨3938138, by rfl⟩ : syracuseStep 5250851 = 7876277) B7876277
theorem B3112739 : Blo 1381510 3112739 := bstep (se 1 (by rfl) ⟨2334554, by rfl⟩ : syracuseStep 3112739 = 4669109) B4669109
theorem B3989293 : Blo 1381510 3989293 := bstep (se 3 (by rfl) ⟨747992, by rfl⟩ : syracuseStep 3989293 = 1495985) B1495985
theorem B2072369 : Blo 1381510 2072369 := bstep (se 2 (by rfl) ⟨777138, by rfl⟩ : syracuseStep 2072369 = 1554277) B1554277
theorem B5250865 : Blo 1381510 5250865 := bstep (se 2 (by rfl) ⟨1969074, by rfl⟩ : syracuseStep 5250865 = 3938149) B3938149
theorem B1556275 : Blo 1381510 1556275 := bstep (se 1 (by rfl) ⟨1167206, by rfl⟩ : syracuseStep 1556275 = 2334413) B2334413
theorem B2072387 : Blo 1381510 2072387 := bstep (se 1 (by rfl) ⟨1554290, by rfl⟩ : syracuseStep 2072387 = 3108581) B3108581
theorem B2072417 : Blo 1381510 2072417 := bstep (se 2 (by rfl) ⟨777156, by rfl⟩ : syracuseStep 2072417 = 1554313) B1554313
theorem B2072435 : Blo 1381510 2072435 := bstep (se 1 (by rfl) ⟨1554326, by rfl⟩ : syracuseStep 2072435 = 3108653) B3108653
theorem B2334595 : Blo 1381510 2334595 := bstep (se 1 (by rfl) ⟨1750946, by rfl⟩ : syracuseStep 2334595 = 3501893) B3501893
theorem B4669325 : Blo 1381510 4669325 := bstep (se 3 (by rfl) ⟨875498, by rfl⟩ : syracuseStep 4669325 = 1750997) B1750997
theorem B2072465 : Blo 1381510 2072465 := bstep (se 2 (by rfl) ⟨777174, by rfl⟩ : syracuseStep 2072465 = 1554349) B1554349
theorem B2072483 : Blo 1381510 2072483 := bstep (se 1 (by rfl) ⟨1554362, by rfl⟩ : syracuseStep 2072483 = 3108725) B3108725
theorem B2072513 : Blo 1381510 2072513 := bstep (se 2 (by rfl) ⟨777192, by rfl⟩ : syracuseStep 2072513 = 1554385) B1554385
theorem B2244545 : Blo 1381510 2244545 := bstep (se 2 (by rfl) ⟨841704, by rfl⟩ : syracuseStep 2244545 = 1683409) B1683409
theorem B1400771 : Blo 1381510 1400771 := bstep (se 1 (by rfl) ⟨1050578, by rfl⟩ : syracuseStep 1400771 = 2101157) B2101157
theorem B1556419 : Blo 1381510 1556419 := bstep (se 1 (by rfl) ⟨1167314, by rfl⟩ : syracuseStep 1556419 = 2334629) B2334629
theorem B2072531 : Blo 1381510 2072531 := bstep (se 1 (by rfl) ⟨1554398, by rfl⟩ : syracuseStep 2072531 = 3108797) B3108797
theorem B2072561 : Blo 1381510 2072561 := bstep (se 2 (by rfl) ⟨777210, by rfl⟩ : syracuseStep 2072561 = 1554421) B1554421
theorem B2072651 : Blo 1381510 2072651 := bstep (se 1 (by rfl) ⟨1554488, by rfl⟩ : syracuseStep 2072651 = 3108977) B3108977
theorem B2072663 : Blo 1381510 2072663 := bstep (se 1 (by rfl) ⟨1554497, by rfl⟩ : syracuseStep 2072663 = 3108995) B3108995
theorem B2072729 : Blo 1381510 2072729 := bstep (se 2 (by rfl) ⟨777273, by rfl⟩ : syracuseStep 2072729 = 1554547) B1554547
theorem B3498187 : Blo 1381510 3498187 := bstep (se 1 (by rfl) ⟨2623640, by rfl⟩ : syracuseStep 3498187 = 5247281) B5247281
theorem B2490583 : Blo 1381510 2490583 := bstep (se 1 (by rfl) ⟨1867937, by rfl⟩ : syracuseStep 2490583 = 3735875) B3735875
theorem B2072843 : Blo 1381510 2072843 := bstep (se 1 (by rfl) ⟨1554632, by rfl⟩ : syracuseStep 2072843 = 3109265) B3109265
theorem B2072855 : Blo 1381510 2072855 := bstep (se 1 (by rfl) ⟨1554641, by rfl⟩ : syracuseStep 2072855 = 3109283) B3109283
theorem B5251351 : Blo 1381510 5251351 := bstep (se 1 (by rfl) ⟨3938513, by rfl⟩ : syracuseStep 5251351 = 7877027) B7877027
theorem B2072921 : Blo 1381510 2072921 := bstep (se 2 (by rfl) ⟨777345, by rfl⟩ : syracuseStep 2072921 = 1554691) B1554691
theorem B3498329 : Blo 1381510 3498329 := bstep (se 2 (by rfl) ⟨1311873, by rfl⟩ : syracuseStep 3498329 = 2623747) B2623747
theorem B8864093 : Blo 1381510 8864093 := bstep (se 3 (by rfl) ⟨1662017, by rfl⟩ : syracuseStep 8864093 = 3324035) B3324035
theorem B2073035 : Blo 1381510 2073035 := bstep (se 1 (by rfl) ⟨1554776, by rfl⟩ : syracuseStep 2073035 = 3109553) B3109553
theorem B2073047 : Blo 1381510 2073047 := bstep (se 1 (by rfl) ⟨1554785, by rfl⟩ : syracuseStep 2073047 = 3109571) B3109571
theorem B15753689 : Blo 1381510 15753689 := bstep (se 2 (by rfl) ⟨5907633, by rfl⟩ : syracuseStep 15753689 = 11815267) B11815267
theorem B2073113 : Blo 1381510 2073113 := bstep (se 2 (by rfl) ⟨777417, by rfl⟩ : syracuseStep 2073113 = 1554835) B1554835
theorem B5907019 : Blo 1381510 5907019 := bstep (se 1 (by rfl) ⟨4430264, by rfl⟩ : syracuseStep 5907019 = 8860529) B8860529
theorem B2073227 : Blo 1381510 2073227 := bstep (se 1 (by rfl) ⟨1554920, by rfl⟩ : syracuseStep 2073227 = 3109841) B3109841
theorem B2073239 : Blo 1381510 2073239 := bstep (se 1 (by rfl) ⟨1554929, by rfl⟩ : syracuseStep 2073239 = 3109859) B3109859
theorem B17703629 : Blo 1381510 17703629 := bstep (se 3 (by rfl) ⟨3319430, by rfl⟩ : syracuseStep 17703629 = 6638861) B6638861
theorem B2073305 : Blo 1381510 2073305 := bstep (se 2 (by rfl) ⟨777489, by rfl⟩ : syracuseStep 2073305 = 1554979) B1554979
theorem B1475371 : Blo 1381510 1475371 := bstep (se 1 (by rfl) ⟨1106528, by rfl⟩ : syracuseStep 1475371 = 2213057) B2213057
theorem B2073419 : Blo 1381510 2073419 := bstep (se 1 (by rfl) ⟨1555064, by rfl⟩ : syracuseStep 2073419 = 3110129) B3110129
theorem B2073431 : Blo 1381510 2073431 := bstep (se 1 (by rfl) ⟨1555073, by rfl⟩ : syracuseStep 2073431 = 3110147) B3110147
theorem B2802521 : Blo 1381510 2802521 := bstep (se 2 (by rfl) ⟨1050945, by rfl⟩ : syracuseStep 2802521 = 2101891) B2101891
theorem B5907293 : Blo 1381510 5907293 := bstep (se 3 (by rfl) ⟨1107617, by rfl⟩ : syracuseStep 5907293 = 2215235) B2215235
theorem B2073497 : Blo 1381510 2073497 := bstep (se 2 (by rfl) ⟨777561, by rfl⟩ : syracuseStep 2073497 = 1555123) B1555123
theorem B3736523 : Blo 1381510 3736523 := bstep (se 1 (by rfl) ⟨2802392, by rfl⟩ : syracuseStep 3736523 = 5604785) B5604785
theorem B2073611 : Blo 1381510 2073611 := bstep (se 1 (by rfl) ⟨1555208, by rfl⟩ : syracuseStep 2073611 = 3110417) B3110417
theorem B2073623 : Blo 1381510 2073623 := bstep (se 1 (by rfl) ⟨1555217, by rfl⟩ : syracuseStep 2073623 = 3110435) B3110435
theorem B6308887 : Blo 1381510 6308887 := bstep (se 1 (by rfl) ⟨4731665, by rfl⟩ : syracuseStep 6308887 = 9463331) B9463331
theorem B5252141 : Blo 1381510 5252141 := bstep (se 3 (by rfl) ⟨984776, by rfl⟩ : syracuseStep 5252141 = 1969553) B1969553
theorem B5604427 : Blo 1381510 5604427 := bstep (se 1 (by rfl) ⟨4203320, by rfl⟩ : syracuseStep 5604427 = 8406641) B8406641
theorem B2073689 : Blo 1381510 2073689 := bstep (se 2 (by rfl) ⟨777633, by rfl⟩ : syracuseStep 2073689 = 1555267) B1555267
theorem B3499159 : Blo 1381510 3499159 := bstep (se 1 (by rfl) ⟨2624369, by rfl⟩ : syracuseStep 3499159 = 5248739) B5248739
theorem B2073803 : Blo 1381510 2073803 := bstep (se 1 (by rfl) ⟨1555352, by rfl⟩ : syracuseStep 2073803 = 3110705) B3110705
theorem B2073815 : Blo 1381510 2073815 := bstep (se 1 (by rfl) ⟨1555361, by rfl⟩ : syracuseStep 2073815 = 3110723) B3110723
theorem B6997265 : Blo 1381510 6997265 := bstep (se 2 (by rfl) ⟨2623974, by rfl⟩ : syracuseStep 6997265 = 5247949) B5247949
theorem B2073881 : Blo 1381510 2073881 := bstep (se 2 (by rfl) ⟨777705, by rfl⟩ : syracuseStep 2073881 = 1555411) B1555411
theorem B4982147 : Blo 1381510 4982147 := bstep (se 1 (by rfl) ⟨3736610, by rfl⟩ : syracuseStep 4982147 = 7473221) B7473221
theorem B2073995 : Blo 1381510 2073995 := bstep (se 1 (by rfl) ⟨1555496, by rfl⟩ : syracuseStep 2073995 = 3110993) B3110993
theorem B2074007 : Blo 1381510 2074007 := bstep (se 1 (by rfl) ⟨1555505, by rfl⟩ : syracuseStep 2074007 = 3111011) B3111011
theorem B1402283 : Blo 1381510 1402283 := bstep (se 1 (by rfl) ⟨1051712, by rfl⟩ : syracuseStep 1402283 = 2103425) B2103425
theorem B6997427 : Blo 1381510 6997427 := bstep (se 1 (by rfl) ⟨5248070, by rfl⟩ : syracuseStep 6997427 = 10496141) B10496141
theorem B2622935 : Blo 1381510 2622935 := bstep (se 1 (by rfl) ⟨1967201, by rfl⟩ : syracuseStep 2622935 = 3934403) B3934403
theorem B2074073 : Blo 1381510 2074073 := bstep (se 2 (by rfl) ⟨777777, by rfl⟩ : syracuseStep 2074073 = 1555555) B1555555
theorem B3499595 : Blo 1381510 3499595 := bstep (se 1 (by rfl) ⟨2624696, by rfl⟩ : syracuseStep 3499595 = 5249393) B5249393
theorem B2074187 : Blo 1381510 2074187 := bstep (se 1 (by rfl) ⟨1555640, by rfl⟩ : syracuseStep 2074187 = 3111281) B3111281
theorem B2074199 : Blo 1381510 2074199 := bstep (se 1 (by rfl) ⟨1555649, by rfl⟩ : syracuseStep 2074199 = 3111299) B3111299
theorem B3991133 : Blo 1381510 3991133 := bstep (se 3 (by rfl) ⟨748337, by rfl⟩ : syracuseStep 3991133 = 1496675) B1496675
theorem B11970179 : Blo 1381510 11970179 := bstep (se 1 (by rfl) ⟨8977634, by rfl⟩ : syracuseStep 11970179 = 17955269) B17955269
theorem B2074265 : Blo 1381510 2074265 := bstep (se 2 (by rfl) ⟨777849, by rfl⟩ : syracuseStep 2074265 = 1555699) B1555699
theorem B2950913 : Blo 1381510 2950913 := bstep (se 2 (by rfl) ⟨1106592, by rfl⟩ : syracuseStep 2950913 = 2213185) B2213185
theorem B2074379 : Blo 1381510 2074379 := bstep (se 1 (by rfl) ⟨1555784, by rfl⟩ : syracuseStep 2074379 = 3111569) B3111569
theorem B2074391 : Blo 1381510 2074391 := bstep (se 1 (by rfl) ⟨1555793, by rfl⟩ : syracuseStep 2074391 = 3111587) B3111587
theorem B4663115 : Blo 1381510 4663115 := bstep (se 1 (by rfl) ⟨3497336, by rfl⟩ : syracuseStep 4663115 = 6994673) B6994673
theorem B2074457 : Blo 1381510 2074457 := bstep (se 2 (by rfl) ⟨777921, by rfl⟩ : syracuseStep 2074457 = 1555843) B1555843
theorem B3499969 : Blo 1381510 3499969 := bstep (se 2 (by rfl) ⟨1312488, by rfl⟩ : syracuseStep 3499969 = 2624977) B2624977
theorem B2074571 : Blo 1381510 2074571 := bstep (se 1 (by rfl) ⟨1555928, by rfl⟩ : syracuseStep 2074571 = 3111857) B3111857
theorem B2074583 : Blo 1381510 2074583 := bstep (se 1 (by rfl) ⟨1555937, by rfl⟩ : syracuseStep 2074583 = 3111875) B3111875
theorem B2074649 : Blo 1381510 2074649 := bstep (se 2 (by rfl) ⟨777993, by rfl⟩ : syracuseStep 2074649 = 1555987) B1555987
theorem B2951255 : Blo 1381510 2951255 := bstep (se 1 (by rfl) ⟨2213441, by rfl⟩ : syracuseStep 2951255 = 4426883) B4426883
theorem B6064217 : Blo 1381510 6064217 := bstep (se 2 (by rfl) ⟨2274081, by rfl⟩ : syracuseStep 6064217 = 4548163) B4548163
theorem B4663385 : Blo 1381510 4663385 := bstep (se 2 (by rfl) ⟨1748769, by rfl⟩ : syracuseStep 4663385 = 3497539) B3497539
theorem B2623603 : Blo 1381510 2623603 := bstep (se 1 (by rfl) ⟨1967702, by rfl⟩ : syracuseStep 2623603 = 3935405) B3935405
theorem B2074763 : Blo 1381510 2074763 := bstep (se 1 (by rfl) ⟨1556072, by rfl⟩ : syracuseStep 2074763 = 3112145) B3112145
theorem B2074775 : Blo 1381510 2074775 := bstep (se 1 (by rfl) ⟨1556081, by rfl⟩ : syracuseStep 2074775 = 3112163) B3112163
theorem B2074841 : Blo 1381510 2074841 := bstep (se 2 (by rfl) ⟨778065, by rfl⟩ : syracuseStep 2074841 = 1556131) B1556131
theorem B2951425 : Blo 1381510 2951425 := bstep (se 2 (by rfl) ⟨1106784, by rfl⟩ : syracuseStep 2951425 = 2213569) B2213569
theorem B3549491 : Blo 1381510 3549491 := bstep (se 1 (by rfl) ⟨2662118, by rfl⟩ : syracuseStep 3549491 = 5324237) B5324237
theorem B2074955 : Blo 1381510 2074955 := bstep (se 1 (by rfl) ⟨1556216, by rfl⟩ : syracuseStep 2074955 = 3112433) B3112433
theorem B2074967 : Blo 1381510 2074967 := bstep (se 1 (by rfl) ⟨1556225, by rfl⟩ : syracuseStep 2074967 = 3112451) B3112451
theorem B19925347 : Blo 1381510 19925347 := bstep (se 1 (by rfl) ⟨14944010, by rfl⟩ : syracuseStep 19925347 = 29888021) B29888021
theorem B2075033 : Blo 1381510 2075033 := bstep (se 2 (by rfl) ⟨778137, by rfl⟩ : syracuseStep 2075033 = 1556275) B1556275
theorem B2075147 : Blo 1381510 2075147 := bstep (se 1 (by rfl) ⟨1556360, by rfl⟩ : syracuseStep 2075147 = 3112721) B3112721
theorem B3500567 : Blo 1381510 3500567 := bstep (se 1 (by rfl) ⟨2625425, by rfl⟩ : syracuseStep 3500567 = 5250851) B5250851
theorem B2075159 : Blo 1381510 2075159 := bstep (se 1 (by rfl) ⟨1556369, by rfl⟩ : syracuseStep 2075159 = 3112739) B3112739
theorem B2624051 : Blo 1381510 2624051 := bstep (se 1 (by rfl) ⟨1968038, by rfl⟩ : syracuseStep 2624051 = 3936077) B3936077
theorem B5245505 : Blo 1381510 5245505 := bstep (se 2 (by rfl) ⟨1967064, by rfl⟩ : syracuseStep 5245505 = 3934129) B3934129
theorem B2624089 : Blo 1381510 2624089 := bstep (se 2 (by rfl) ⟨984033, by rfl⟩ : syracuseStep 2624089 = 1968067) B1968067
theorem B2075225 : Blo 1381510 2075225 := bstep (se 2 (by rfl) ⟨778209, by rfl⟩ : syracuseStep 2075225 = 1556419) B1556419
theorem B7875251 : Blo 1381510 7875251 := bstep (se 1 (by rfl) ⟨5906438, by rfl⟩ : syracuseStep 7875251 = 11812877) B11812877
theorem B5606081 : Blo 1381510 5606081 := bstep (se 2 (by rfl) ⟨2102280, by rfl⟩ : syracuseStep 5606081 = 4204561) B4204561
theorem B3893977 : Blo 1381510 3893977 := bstep (se 2 (by rfl) ⟨1460241, by rfl⟩ : syracuseStep 3893977 = 2920483) B2920483
theorem B1477387 : Blo 1381510 1477387 := bstep (se 1 (by rfl) ⟨1108040, by rfl⟩ : syracuseStep 1477387 = 2216081) B2216081
theorem B4664087 : Blo 1381510 4664087 := bstep (se 1 (by rfl) ⟨3498065, by rfl⟩ : syracuseStep 4664087 = 6996131) B6996131
theorem B3935051 : Blo 1381510 3935051 := bstep (se 1 (by rfl) ⟨2951288, by rfl⟩ : syracuseStep 3935051 = 5902577) B5902577
theorem B21269465 : Blo 1381510 21269465 := bstep (se 2 (by rfl) ⟨7976049, by rfl⟩ : syracuseStep 21269465 = 15952099) B15952099
theorem B2624537 : Blo 1381510 2624537 := bstep (se 2 (by rfl) ⟨984201, by rfl⟩ : syracuseStep 2624537 = 1968403) B1968403
theorem B6646859 : Blo 1381510 6646859 := bstep (se 1 (by rfl) ⟨4985144, by rfl⟩ : syracuseStep 6646859 = 9970289) B9970289
theorem B4099265 : Blo 1381510 4099265 := bstep (se 2 (by rfl) ⟨1537224, by rfl⟩ : syracuseStep 4099265 = 3074449) B3074449
theorem B1682635 : Blo 1381510 1682635 := bstep (se 1 (by rfl) ⟨1261976, by rfl⟩ : syracuseStep 1682635 = 2523953) B2523953
theorem B5606603 : Blo 1381510 5606603 := bstep (se 1 (by rfl) ⟨4204952, by rfl⟩ : syracuseStep 5606603 = 8409905) B8409905
theorem B4664627 : Blo 1381510 4664627 := bstep (se 1 (by rfl) ⟨3498470, by rfl⟩ : syracuseStep 4664627 = 6996941) B6996941
theorem B8523073 : Blo 1381510 8523073 := bstep (se 2 (by rfl) ⟨3196152, by rfl⟩ : syracuseStep 8523073 = 6392305) B6392305
theorem B3501377 : Blo 1381510 3501377 := bstep (se 2 (by rfl) ⟨1313016, by rfl⟩ : syracuseStep 3501377 = 2626033) B2626033
theorem B6999371 : Blo 1381510 6999371 := bstep (se 1 (by rfl) ⟨5249528, by rfl⟩ : syracuseStep 6999371 = 10499057) B10499057
theorem B2952587 : Blo 1381510 2952587 := bstep (se 1 (by rfl) ⟨2214440, by rfl⟩ : syracuseStep 2952587 = 4428881) B4428881
theorem B5049773 : Blo 1381510 5049773 := bstep (se 3 (by rfl) ⟨946832, by rfl⟩ : syracuseStep 5049773 = 1893665) B1893665
theorem B8408537 : Blo 1381510 8408537 := bstep (se 2 (by rfl) ⟨3153201, by rfl⟩ : syracuseStep 8408537 = 6306403) B6306403
theorem B4664897 : Blo 1381510 4664897 := bstep (se 2 (by rfl) ⟨1749336, by rfl⟩ : syracuseStep 4664897 = 3498673) B3498673
theorem B1748567 : Blo 1381510 1748567 := bstep (se 1 (by rfl) ⟨1311425, by rfl⟩ : syracuseStep 1748567 = 2622851) B2622851
theorem B1969753 : Blo 1381510 1969753 := bstep (se 2 (by rfl) ⟨738657, by rfl⟩ : syracuseStep 1969753 = 1477315) B1477315
theorem B3108491 : Blo 1381510 3108491 := bstep (se 1 (by rfl) ⟨2331368, by rfl⟩ : syracuseStep 3108491 = 4662737) B4662737
theorem B15740567 : Blo 1381510 15740567 := bstep (se 1 (by rfl) ⟨11805425, by rfl⟩ : syracuseStep 15740567 = 23610851) B23610851
theorem B3108545 : Blo 1381510 3108545 := bstep (se 2 (by rfl) ⟨1165704, by rfl⟩ : syracuseStep 3108545 = 2331409) B2331409
theorem B67276493 : Blo 1381510 67276493 := bstep (se 3 (by rfl) ⟨12614342, by rfl⟩ : syracuseStep 67276493 = 25228685) B25228685
theorem B2625281 : Blo 1381510 2625281 := bstep (se 2 (by rfl) ⟨984480, by rfl⟩ : syracuseStep 2625281 = 1968961) B1968961
theorem B3321623 : Blo 1381510 3321623 := bstep (se 1 (by rfl) ⟨2491217, by rfl⟩ : syracuseStep 3321623 = 4982435) B4982435
theorem B5246765 : Blo 1381510 5246765 := bstep (se 3 (by rfl) ⟨983768, by rfl⟩ : syracuseStep 5246765 = 1967537) B1967537
theorem B5246795 : Blo 1381510 5246795 := bstep (se 1 (by rfl) ⟨3935096, by rfl⟩ : syracuseStep 5246795 = 7870193) B7870193
theorem B5320523 : Blo 1381510 5320523 := bstep (se 1 (by rfl) ⟨3990392, by rfl⟩ : syracuseStep 5320523 = 7980785) B7980785
theorem B3501913 : Blo 1381510 3501913 := bstep (se 2 (by rfl) ⟨1313217, by rfl⟩ : syracuseStep 3501913 = 2626435) B2626435
theorem B4984669 : Blo 1381510 4984669 := bstep (se 3 (by rfl) ⟨934625, by rfl⟩ : syracuseStep 4984669 = 1869251) B1869251
theorem B8408933 : Blo 1381510 8408933 := bstep (se 4 (by rfl) ⟨788337, by rfl⟩ : syracuseStep 8408933 = 1576675) B1576675
theorem B3108761 : Blo 1381510 3108761 := bstep (se 2 (by rfl) ⟨1165785, by rfl⟩ : syracuseStep 3108761 = 2331571) B2331571
theorem B3108851 : Blo 1381510 3108851 := bstep (se 1 (by rfl) ⟨2331638, by rfl⟩ : syracuseStep 3108851 = 4663277) B4663277
theorem B2625547 : Blo 1381510 2625547 := bstep (se 1 (by rfl) ⟨1969160, by rfl⟩ : syracuseStep 2625547 = 3938321) B3938321
theorem B3108887 : Blo 1381510 3108887 := bstep (se 1 (by rfl) ⟨2331665, by rfl⟩ : syracuseStep 3108887 = 4663331) B4663331
theorem B7868461 : Blo 1381510 7868461 := bstep (se 3 (by rfl) ⟨1475336, by rfl⟩ : syracuseStep 7868461 = 2950673) B2950673
theorem B35926091 : Blo 1381510 35926091 := bstep (se 1 (by rfl) ⟨26944568, by rfl⟩ : syracuseStep 35926091 = 53889137) B53889137
theorem B1921099 : Blo 1381510 1921099 := bstep (se 1 (by rfl) ⟨1440824, by rfl⟩ : syracuseStep 1921099 = 2881649) B2881649
theorem B4665437 : Blo 1381510 4665437 := bstep (se 3 (by rfl) ⟨874769, by rfl⟩ : syracuseStep 4665437 = 1749539) B1749539
theorem B7876709 : Blo 1381510 7876709 := bstep (se 4 (by rfl) ⟨738441, by rfl⟩ : syracuseStep 7876709 = 1476883) B1476883
theorem B2953331 : Blo 1381510 2953331 := bstep (se 1 (by rfl) ⟨2214998, by rfl⟩ : syracuseStep 2953331 = 4429997) B4429997
theorem B5607575 : Blo 1381510 5607575 := bstep (se 1 (by rfl) ⟨4205681, by rfl⟩ : syracuseStep 5607575 = 8411363) B8411363
theorem B3109067 : Blo 1381510 3109067 := bstep (se 1 (by rfl) ⟨2331800, by rfl⟩ : syracuseStep 3109067 = 4663601) B4663601
theorem B3109121 : Blo 1381510 3109121 := bstep (se 2 (by rfl) ⟨1165920, by rfl⟩ : syracuseStep 3109121 = 2331841) B2331841
theorem B1749271 : Blo 1381510 1749271 := bstep (se 1 (by rfl) ⟨1311953, by rfl⟩ : syracuseStep 1749271 = 2623907) B2623907
theorem B11817251 : Blo 1381510 11817251 := bstep (se 1 (by rfl) ⟨8862938, by rfl⟩ : syracuseStep 11817251 = 17725877) B17725877
theorem B3936691 : Blo 1381510 3936691 := bstep (se 1 (by rfl) ⟨2952518, by rfl⟩ : syracuseStep 3936691 = 5905037) B5905037
theorem B2625995 : Blo 1381510 2625995 := bstep (se 1 (by rfl) ⟨1969496, by rfl⟩ : syracuseStep 2625995 = 3938993) B3938993
theorem B3109337 : Blo 1381510 3109337 := bstep (se 2 (by rfl) ⟨1166001, by rfl⟩ : syracuseStep 3109337 = 2332003) B2332003
theorem B5247449 : Blo 1381510 5247449 := bstep (se 2 (by rfl) ⟨1967793, by rfl⟩ : syracuseStep 5247449 = 3935587) B3935587
theorem B3109427 : Blo 1381510 3109427 := bstep (se 1 (by rfl) ⟨2332070, by rfl⟩ : syracuseStep 3109427 = 4664141) B4664141
theorem B14955083 : Blo 1381510 14955083 := bstep (se 1 (by rfl) ⟨11216312, by rfl⟩ : syracuseStep 14955083 = 22432625) B22432625
theorem B3109463 : Blo 1381510 3109463 := bstep (se 1 (by rfl) ⟨2332097, by rfl⟩ : syracuseStep 3109463 = 4664195) B4664195
theorem B2626177 : Blo 1381510 2626177 := bstep (se 2 (by rfl) ⟨984816, by rfl⟩ : syracuseStep 2626177 = 1969633) B1969633
theorem B4985489 : Blo 1381510 4985489 := bstep (se 2 (by rfl) ⟨1869558, by rfl⟩ : syracuseStep 4985489 = 3739117) B3739117
theorem B3936919 : Blo 1381510 3936919 := bstep (se 1 (by rfl) ⟨2952689, by rfl⟩ : syracuseStep 3936919 = 5905379) B5905379
theorem B9966341 : Blo 1381510 9966341 := bstep (se 4 (by rfl) ⟨934344, by rfl⟩ : syracuseStep 9966341 = 1868689) B1868689
theorem B3109643 : Blo 1381510 3109643 := bstep (se 1 (by rfl) ⟨2332232, by rfl⟩ : syracuseStep 3109643 = 4664465) B4664465
theorem B5247767 : Blo 1381510 5247767 := bstep (se 1 (by rfl) ⟨3935825, by rfl⟩ : syracuseStep 5247767 = 7871651) B7871651
theorem B3109697 : Blo 1381510 3109697 := bstep (se 2 (by rfl) ⟨1166136, by rfl⟩ : syracuseStep 3109697 = 2332273) B2332273
theorem B2954227 : Blo 1381510 2954227 := bstep (se 1 (by rfl) ⟨2215670, by rfl⟩ : syracuseStep 2954227 = 4431341) B4431341
theorem B2331659 : Blo 1381510 2331659 := bstep (se 1 (by rfl) ⟨1748744, by rfl⟩ : syracuseStep 2331659 = 3497489) B3497489
theorem B11818001 : Blo 1381510 11818001 := bstep (se 2 (by rfl) ⟨4431750, by rfl⟩ : syracuseStep 11818001 = 8863501) B8863501
theorem B3109913 : Blo 1381510 3109913 := bstep (se 2 (by rfl) ⟨1166217, by rfl⟩ : syracuseStep 3109913 = 2332435) B2332435
theorem B7574573 : Blo 1381510 7574573 := bstep (se 3 (by rfl) ⟨1420232, by rfl⟩ : syracuseStep 7574573 = 2840465) B2840465
theorem B7001153 : Blo 1381510 7001153 := bstep (se 2 (by rfl) ⟨2625432, by rfl⟩ : syracuseStep 7001153 = 5250865) B5250865
theorem B3110003 : Blo 1381510 3110003 := bstep (se 1 (by rfl) ⟨2332502, by rfl⟩ : syracuseStep 3110003 = 4665005) B4665005
theorem B8852611 : Blo 1381510 8852611 := bstep (se 1 (by rfl) ⟨6639458, by rfl⟩ : syracuseStep 8852611 = 13278917) B13278917
theorem B1381515 : Blo 1381510 1381515 := bstep (se 1 (by rfl) ⟨1036136, by rfl⟩ : syracuseStep 1381515 = 2072273) B2072273
theorem B2331787 : Blo 1381510 2331787 := bstep (se 1 (by rfl) ⟨1748840, by rfl⟩ : syracuseStep 2331787 = 3497681) B3497681
theorem B1381527 : Blo 1381510 1381527 := bstep (se 1 (by rfl) ⟨1036145, by rfl⟩ : syracuseStep 1381527 = 2072291) B2072291
theorem B3110039 : Blo 1381510 3110039 := bstep (se 1 (by rfl) ⟨2332529, by rfl⟩ : syracuseStep 3110039 = 4665059) B4665059
theorem B1381547 : Blo 1381510 1381547 := bstep (se 1 (by rfl) ⟨1036160, by rfl⟩ : syracuseStep 1381547 = 2072321) B2072321
theorem B5903533 : Blo 1381510 5903533 := bstep (se 3 (by rfl) ⟨1106912, by rfl⟩ : syracuseStep 5903533 = 2213825) B2213825
theorem B1381559 : Blo 1381510 1381559 := bstep (se 1 (by rfl) ⟨1036169, by rfl⟩ : syracuseStep 1381559 = 2072339) B2072339
theorem B1381579 : Blo 1381510 1381579 := bstep (se 1 (by rfl) ⟨1036184, by rfl⟩ : syracuseStep 1381579 = 2072369) B2072369
theorem B4666571 : Blo 1381510 4666571 := bstep (se 1 (by rfl) ⟨3499928, by rfl⟩ : syracuseStep 4666571 = 6999857) B6999857
theorem B23606477 : Blo 1381510 23606477 := bstep (se 3 (by rfl) ⟨4426214, by rfl⟩ : syracuseStep 23606477 = 8852429) B8852429
theorem B1381591 : Blo 1381510 1381591 := bstep (se 1 (by rfl) ⟨1036193, by rfl⟩ : syracuseStep 1381591 = 2072387) B2072387
theorem B1381611 : Blo 1381510 1381611 := bstep (se 1 (by rfl) ⟨1036208, by rfl⟩ : syracuseStep 1381611 = 2072417) B2072417
theorem B1381623 : Blo 1381510 1381623 := bstep (se 1 (by rfl) ⟨1036217, by rfl⟩ : syracuseStep 1381623 = 2072435) B2072435
theorem B1381643 : Blo 1381510 1381643 := bstep (se 1 (by rfl) ⟨1036232, by rfl⟩ : syracuseStep 1381643 = 2072465) B2072465
theorem B1381655 : Blo 1381510 1381655 := bstep (se 1 (by rfl) ⟨1036241, by rfl⟩ : syracuseStep 1381655 = 2072483) B2072483
theorem B2331929 : Blo 1381510 2331929 := bstep (se 2 (by rfl) ⟨874473, by rfl⟩ : syracuseStep 2331929 = 1748947) B1748947
theorem B1381675 : Blo 1381510 1381675 := bstep (se 1 (by rfl) ⟨1036256, by rfl⟩ : syracuseStep 1381675 = 2072513) B2072513
theorem B1496363 : Blo 1381510 1496363 := bstep (se 1 (by rfl) ⟨1122272, by rfl⟩ : syracuseStep 1496363 = 2244545) B2244545
theorem B1381687 : Blo 1381510 1381687 := bstep (se 1 (by rfl) ⟨1036265, by rfl⟩ : syracuseStep 1381687 = 2072531) B2072531
theorem B1381707 : Blo 1381510 1381707 := bstep (se 1 (by rfl) ⟨1036280, by rfl⟩ : syracuseStep 1381707 = 2072561) B2072561
theorem B3110219 : Blo 1381510 3110219 := bstep (se 1 (by rfl) ⟨2332664, by rfl⟩ : syracuseStep 3110219 = 4665329) B4665329
theorem B1381719 : Blo 1381510 1381719 := bstep (se 1 (by rfl) ⟨1036289, by rfl⟩ : syracuseStep 1381719 = 2072579) B2072579
theorem B5903705 : Blo 1381510 5903705 := bstep (se 2 (by rfl) ⟨2213889, by rfl⟩ : syracuseStep 5903705 = 4427779) B4427779
theorem B1381739 : Blo 1381510 1381739 := bstep (se 1 (by rfl) ⟨1036304, by rfl⟩ : syracuseStep 1381739 = 2072609) B2072609
theorem B1381751 : Blo 1381510 1381751 := bstep (se 1 (by rfl) ⟨1036313, by rfl⟩ : syracuseStep 1381751 = 2072627) B2072627
theorem B3110273 : Blo 1381510 3110273 := bstep (se 2 (by rfl) ⟨1166352, by rfl⟩ : syracuseStep 3110273 = 2332705) B2332705
theorem B1381771 : Blo 1381510 1381771 := bstep (se 1 (by rfl) ⟨1036328, by rfl⟩ : syracuseStep 1381771 = 2072657) B2072657
theorem B1381783 : Blo 1381510 1381783 := bstep (se 1 (by rfl) ⟨1036337, by rfl⟩ : syracuseStep 1381783 = 2072675) B2072675
theorem B2332057 : Blo 1381510 2332057 := bstep (se 2 (by rfl) ⟨874521, by rfl⟩ : syracuseStep 2332057 = 1749043) B1749043
theorem B1381803 : Blo 1381510 1381803 := bstep (se 1 (by rfl) ⟨1036352, by rfl⟩ : syracuseStep 1381803 = 2072705) B2072705
theorem B5248435 : Blo 1381510 5248435 := bstep (se 1 (by rfl) ⟨3936326, by rfl⟩ : syracuseStep 5248435 = 7872653) B7872653
theorem B1381815 : Blo 1381510 1381815 := bstep (se 1 (by rfl) ⟨1036361, by rfl⟩ : syracuseStep 1381815 = 2072723) B2072723
theorem B1381835 : Blo 1381510 1381835 := bstep (se 1 (by rfl) ⟨1036376, by rfl⟩ : syracuseStep 1381835 = 2072753) B2072753
theorem B102282709 : Blo 1381510 102282709 := bstep (se 7 (by rfl) ⟨1198625, by rfl⟩ : syracuseStep 102282709 = 2397251) B2397251
theorem B1381847 : Blo 1381510 1381847 := bstep (se 1 (by rfl) ⟨1036385, by rfl⟩ : syracuseStep 1381847 = 2072771) B2072771
theorem B4666841 : Blo 1381510 4666841 := bstep (se 2 (by rfl) ⟨1750065, by rfl⟩ : syracuseStep 4666841 = 3500131) B3500131
theorem B1381867 : Blo 1381510 1381867 := bstep (se 1 (by rfl) ⟨1036400, by rfl⟩ : syracuseStep 1381867 = 2072801) B2072801
theorem B1381879 : Blo 1381510 1381879 := bstep (se 1 (by rfl) ⟨1036409, by rfl⟩ : syracuseStep 1381879 = 2072819) B2072819
theorem B1381899 : Blo 1381510 1381899 := bstep (se 1 (by rfl) ⟨1036424, by rfl⟩ : syracuseStep 1381899 = 2072849) B2072849
theorem B1381911 : Blo 1381510 1381911 := bstep (se 1 (by rfl) ⟨1036433, by rfl⟩ : syracuseStep 1381911 = 2072867) B2072867
theorem B1381931 : Blo 1381510 1381931 := bstep (se 1 (by rfl) ⟨1036448, by rfl⟩ : syracuseStep 1381931 = 2072897) B2072897
theorem B1381943 : Blo 1381510 1381943 := bstep (se 1 (by rfl) ⟨1036457, by rfl⟩ : syracuseStep 1381943 = 2072915) B2072915
theorem B12605003 : Blo 1381510 12605003 := bstep (se 1 (by rfl) ⟨9453752, by rfl⟩ : syracuseStep 12605003 = 18907505) B18907505
theorem B22410827 : Blo 1381510 22410827 := bstep (se 1 (by rfl) ⟨16808120, by rfl⟩ : syracuseStep 22410827 = 33616241) B33616241
theorem B1381963 : Blo 1381510 1381963 := bstep (se 1 (by rfl) ⟨1036472, by rfl⟩ : syracuseStep 1381963 = 2072945) B2072945
theorem B1381975 : Blo 1381510 1381975 := bstep (se 1 (by rfl) ⟨1036481, by rfl⟩ : syracuseStep 1381975 = 2072963) B2072963
theorem B3110489 : Blo 1381510 3110489 := bstep (se 2 (by rfl) ⟨1166433, by rfl⟩ : syracuseStep 3110489 = 2332867) B2332867
theorem B1381995 : Blo 1381510 1381995 := bstep (se 1 (by rfl) ⟨1036496, by rfl⟩ : syracuseStep 1381995 = 2072993) B2072993
theorem B1382007 : Blo 1381510 1382007 := bstep (se 1 (by rfl) ⟨1036505, by rfl⟩ : syracuseStep 1382007 = 2073011) B2073011
theorem B1382027 : Blo 1381510 1382027 := bstep (se 1 (by rfl) ⟨1036520, by rfl⟩ : syracuseStep 1382027 = 2073041) B2073041
theorem B1382039 : Blo 1381510 1382039 := bstep (se 1 (by rfl) ⟨1036529, by rfl⟩ : syracuseStep 1382039 = 2073059) B2073059
theorem B1382059 : Blo 1381510 1382059 := bstep (se 1 (by rfl) ⟨1036544, by rfl⟩ : syracuseStep 1382059 = 2073089) B2073089
theorem B3110579 : Blo 1381510 3110579 := bstep (se 1 (by rfl) ⟨2332934, by rfl⟩ : syracuseStep 3110579 = 4665869) B4665869
theorem B1382071 : Blo 1381510 1382071 := bstep (se 1 (by rfl) ⟨1036553, by rfl⟩ : syracuseStep 1382071 = 2073107) B2073107
theorem B1382091 : Blo 1381510 1382091 := bstep (se 1 (by rfl) ⟨1036568, by rfl⟩ : syracuseStep 1382091 = 2073137) B2073137
theorem B2102987 : Blo 1381510 2102987 := bstep (se 1 (by rfl) ⟨1577240, by rfl⟩ : syracuseStep 2102987 = 3154481) B3154481
theorem B1382103 : Blo 1381510 1382103 := bstep (se 1 (by rfl) ⟨1036577, by rfl⟩ : syracuseStep 1382103 = 2073155) B2073155
theorem B3110615 : Blo 1381510 3110615 := bstep (se 1 (by rfl) ⟨2332961, by rfl⟩ : syracuseStep 3110615 = 4665923) B4665923
theorem B1382123 : Blo 1381510 1382123 := bstep (se 1 (by rfl) ⟨1036592, by rfl⟩ : syracuseStep 1382123 = 2073185) B2073185
theorem B1382135 : Blo 1381510 1382135 := bstep (se 1 (by rfl) ⟨1036601, by rfl⟩ : syracuseStep 1382135 = 2073203) B2073203
theorem B1382155 : Blo 1381510 1382155 := bstep (se 1 (by rfl) ⟨1036616, by rfl⟩ : syracuseStep 1382155 = 2073233) B2073233
theorem B1382167 : Blo 1381510 1382167 := bstep (se 1 (by rfl) ⟨1036625, by rfl⟩ : syracuseStep 1382167 = 2073251) B2073251
theorem B1382187 : Blo 1381510 1382187 := bstep (se 1 (by rfl) ⟨1036640, by rfl⟩ : syracuseStep 1382187 = 2073281) B2073281
theorem B1382199 : Blo 1381510 1382199 := bstep (se 1 (by rfl) ⟨1036649, by rfl⟩ : syracuseStep 1382199 = 2073299) B2073299
theorem B1382219 : Blo 1381510 1382219 := bstep (se 1 (by rfl) ⟨1036664, by rfl⟩ : syracuseStep 1382219 = 2073329) B2073329
theorem B1382231 : Blo 1381510 1382231 := bstep (se 1 (by rfl) ⟨1036673, by rfl⟩ : syracuseStep 1382231 = 2073347) B2073347
theorem B1382251 : Blo 1381510 1382251 := bstep (se 1 (by rfl) ⟨1036688, by rfl⟩ : syracuseStep 1382251 = 2073377) B2073377
theorem B16824181 : Blo 1381510 16824181 := bstep (se 5 (by rfl) ⟨788633, by rfl⟩ : syracuseStep 16824181 = 1577267) B1577267
theorem B1554295 : Blo 1381510 1554295 := bstep (se 1 (by rfl) ⟨1165721, by rfl⟩ : syracuseStep 1554295 = 2331443) B2331443
theorem B1382263 : Blo 1381510 1382263 := bstep (se 1 (by rfl) ⟨1036697, by rfl⟩ : syracuseStep 1382263 = 2073395) B2073395
theorem B1382283 : Blo 1381510 1382283 := bstep (se 1 (by rfl) ⟨1036712, by rfl⟩ : syracuseStep 1382283 = 2073425) B2073425
theorem B3110795 : Blo 1381510 3110795 := bstep (se 1 (by rfl) ⟨2333096, by rfl⟩ : syracuseStep 3110795 = 4666193) B4666193
theorem B1382295 : Blo 1381510 1382295 := bstep (se 1 (by rfl) ⟨1036721, by rfl⟩ : syracuseStep 1382295 = 2073443) B2073443
theorem B1382315 : Blo 1381510 1382315 := bstep (se 1 (by rfl) ⟨1036736, by rfl⟩ : syracuseStep 1382315 = 2073473) B2073473
theorem B1382327 : Blo 1381510 1382327 := bstep (se 1 (by rfl) ⟨1036745, by rfl⟩ : syracuseStep 1382327 = 2073491) B2073491
theorem B3110849 : Blo 1381510 3110849 := bstep (se 2 (by rfl) ⟨1166568, by rfl⟩ : syracuseStep 3110849 = 2333137) B2333137
theorem B1382347 : Blo 1381510 1382347 := bstep (se 1 (by rfl) ⟨1036760, by rfl⟩ : syracuseStep 1382347 = 2073521) B2073521
theorem B1750987 : Blo 1381510 1750987 := bstep (se 1 (by rfl) ⟨1313240, by rfl⟩ : syracuseStep 1750987 = 2626481) B2626481
theorem B2332631 : Blo 1381510 2332631 := bstep (se 1 (by rfl) ⟨1749473, by rfl⟩ : syracuseStep 2332631 = 3498947) B3498947
theorem B1382359 : Blo 1381510 1382359 := bstep (se 1 (by rfl) ⟨1036769, by rfl⟩ : syracuseStep 1382359 = 2073539) B2073539
theorem B1382379 : Blo 1381510 1382379 := bstep (se 1 (by rfl) ⟨1036784, by rfl⟩ : syracuseStep 1382379 = 2073569) B2073569
theorem B1382391 : Blo 1381510 1382391 := bstep (se 1 (by rfl) ⟨1036793, by rfl⟩ : syracuseStep 1382391 = 2073587) B2073587
theorem B1382411 : Blo 1381510 1382411 := bstep (se 1 (by rfl) ⟨1036808, by rfl⟩ : syracuseStep 1382411 = 2073617) B2073617
theorem B1382423 : Blo 1381510 1382423 := bstep (se 1 (by rfl) ⟨1036817, by rfl⟩ : syracuseStep 1382423 = 2073635) B2073635
theorem B1554475 : Blo 1381510 1554475 := bstep (se 1 (by rfl) ⟨1165856, by rfl⟩ : syracuseStep 1554475 = 2331713) B2331713
theorem B1382443 : Blo 1381510 1382443 := bstep (se 1 (by rfl) ⟨1036832, by rfl⟩ : syracuseStep 1382443 = 2073665) B2073665
theorem B1382455 : Blo 1381510 1382455 := bstep (se 1 (by rfl) ⟨1036841, by rfl⟩ : syracuseStep 1382455 = 2073683) B2073683
theorem B1382475 : Blo 1381510 1382475 := bstep (se 1 (by rfl) ⟨1036856, by rfl⟩ : syracuseStep 1382475 = 2073713) B2073713
theorem B2332759 : Blo 1381510 2332759 := bstep (se 1 (by rfl) ⟨1749569, by rfl⟩ : syracuseStep 2332759 = 3499139) B3499139
theorem B1382487 : Blo 1381510 1382487 := bstep (se 1 (by rfl) ⟨1036865, by rfl⟩ : syracuseStep 1382487 = 2073731) B2073731
theorem B3151961 : Blo 1381510 3151961 := bstep (se 2 (by rfl) ⟨1181985, by rfl⟩ : syracuseStep 3151961 = 2363971) B2363971
theorem B1382507 : Blo 1381510 1382507 := bstep (se 1 (by rfl) ⟨1036880, by rfl⟩ : syracuseStep 1382507 = 2073761) B2073761
theorem B1382519 : Blo 1381510 1382519 := bstep (se 1 (by rfl) ⟨1036889, by rfl⟩ : syracuseStep 1382519 = 2073779) B2073779
theorem B1382539 : Blo 1381510 1382539 := bstep (se 1 (by rfl) ⟨1036904, by rfl⟩ : syracuseStep 1382539 = 2073809) B2073809
theorem B1554583 : Blo 1381510 1554583 := bstep (se 1 (by rfl) ⟨1165937, by rfl⟩ : syracuseStep 1554583 = 2331875) B2331875
theorem B1382551 : Blo 1381510 1382551 := bstep (se 1 (by rfl) ⟨1036913, by rfl⟩ : syracuseStep 1382551 = 2073827) B2073827
theorem B3111065 : Blo 1381510 3111065 := bstep (se 2 (by rfl) ⟨1166649, by rfl⟩ : syracuseStep 3111065 = 2333299) B2333299
theorem B4667543 : Blo 1381510 4667543 := bstep (se 1 (by rfl) ⟨3500657, by rfl⟩ : syracuseStep 4667543 = 7001315) B7001315
theorem B1382571 : Blo 1381510 1382571 := bstep (se 1 (by rfl) ⟨1036928, by rfl⟩ : syracuseStep 1382571 = 2073857) B2073857
theorem B2660531 : Blo 1381510 2660531 := bstep (se 1 (by rfl) ⟨1995398, by rfl⟩ : syracuseStep 2660531 = 3990797) B3990797
theorem B1382583 : Blo 1381510 1382583 := bstep (se 1 (by rfl) ⟨1036937, by rfl⟩ : syracuseStep 1382583 = 2073875) B2073875
theorem B1382603 : Blo 1381510 1382603 := bstep (se 1 (by rfl) ⟨1036952, by rfl⟩ : syracuseStep 1382603 = 2073905) B2073905
theorem B1382615 : Blo 1381510 1382615 := bstep (se 1 (by rfl) ⟨1036961, by rfl⟩ : syracuseStep 1382615 = 2073923) B2073923
theorem B1382635 : Blo 1381510 1382635 := bstep (se 1 (by rfl) ⟨1036976, by rfl⟩ : syracuseStep 1382635 = 2073953) B2073953
theorem B3111155 : Blo 1381510 3111155 := bstep (se 1 (by rfl) ⟨2333366, by rfl⟩ : syracuseStep 3111155 = 4666733) B4666733
theorem B1382647 : Blo 1381510 1382647 := bstep (se 1 (by rfl) ⟨1036985, by rfl⟩ : syracuseStep 1382647 = 2073971) B2073971
theorem B1382667 : Blo 1381510 1382667 := bstep (se 1 (by rfl) ⟨1037000, by rfl⟩ : syracuseStep 1382667 = 2074001) B2074001
theorem B85104917 : Blo 1381510 85104917 := bstep (se 6 (by rfl) ⟨1994646, by rfl⟩ : syracuseStep 85104917 = 3989293) B3989293
theorem B1382679 : Blo 1381510 1382679 := bstep (se 1 (by rfl) ⟨1037009, by rfl⟩ : syracuseStep 1382679 = 2074019) B2074019
theorem B3111191 : Blo 1381510 3111191 := bstep (se 1 (by rfl) ⟨2333393, by rfl⟩ : syracuseStep 3111191 = 4666787) B4666787
theorem B1382699 : Blo 1381510 1382699 := bstep (se 1 (by rfl) ⟨1037024, by rfl⟩ : syracuseStep 1382699 = 2074049) B2074049
theorem B1382711 : Blo 1381510 1382711 := bstep (se 1 (by rfl) ⟨1037033, by rfl⟩ : syracuseStep 1382711 = 2074067) B2074067
theorem B1554763 : Blo 1381510 1554763 := bstep (se 1 (by rfl) ⟨1166072, by rfl⟩ : syracuseStep 1554763 = 2332145) B2332145
theorem B1382731 : Blo 1381510 1382731 := bstep (se 1 (by rfl) ⟨1037048, by rfl⟩ : syracuseStep 1382731 = 2074097) B2074097
theorem B1382743 : Blo 1381510 1382743 := bstep (se 1 (by rfl) ⟨1037057, by rfl⟩ : syracuseStep 1382743 = 2074115) B2074115
theorem B10492253 : Blo 1381510 10492253 := bstep (se 3 (by rfl) ⟨1967297, by rfl⟩ : syracuseStep 10492253 = 3934595) B3934595
theorem B1382763 : Blo 1381510 1382763 := bstep (se 1 (by rfl) ⟨1037072, by rfl⟩ : syracuseStep 1382763 = 2074145) B2074145
theorem B1382775 : Blo 1381510 1382775 := bstep (se 1 (by rfl) ⟨1037081, by rfl⟩ : syracuseStep 1382775 = 2074163) B2074163
theorem B1382795 : Blo 1381510 1382795 := bstep (se 1 (by rfl) ⟨1037096, by rfl⟩ : syracuseStep 1382795 = 2074193) B2074193
theorem B5757335 : Blo 1381510 5757335 := bstep (se 1 (by rfl) ⟨4318001, by rfl⟩ : syracuseStep 5757335 = 8636003) B8636003
theorem B1382807 : Blo 1381510 1382807 := bstep (se 1 (by rfl) ⟨1037105, by rfl⟩ : syracuseStep 1382807 = 2074211) B2074211
theorem B1382827 : Blo 1381510 1382827 := bstep (se 1 (by rfl) ⟨1037120, by rfl⟩ : syracuseStep 1382827 = 2074241) B2074241
theorem B1554871 : Blo 1381510 1554871 := bstep (se 1 (by rfl) ⟨1166153, by rfl⟩ : syracuseStep 1554871 = 2332307) B2332307
theorem B1382839 : Blo 1381510 1382839 := bstep (se 1 (by rfl) ⟨1037129, by rfl⟩ : syracuseStep 1382839 = 2074259) B2074259
theorem B3111371 : Blo 1381510 3111371 := bstep (se 1 (by rfl) ⟨2333528, by rfl⟩ : syracuseStep 3111371 = 4667057) B4667057
theorem B1382859 : Blo 1381510 1382859 := bstep (se 1 (by rfl) ⟨1037144, by rfl⟩ : syracuseStep 1382859 = 2074289) B2074289
theorem B1382871 : Blo 1381510 1382871 := bstep (se 1 (by rfl) ⟨1037153, by rfl⟩ : syracuseStep 1382871 = 2074307) B2074307
theorem B21559769 : Blo 1381510 21559769 := bstep (se 2 (by rfl) ⟨8084913, by rfl⟩ : syracuseStep 21559769 = 16169827) B16169827
theorem B8862169 : Blo 1381510 8862169 := bstep (se 2 (by rfl) ⟨3323313, by rfl⟩ : syracuseStep 8862169 = 6646627) B6646627
theorem B3938777 : Blo 1381510 3938777 := bstep (se 2 (by rfl) ⟨1477041, by rfl⟩ : syracuseStep 3938777 = 2954083) B2954083
theorem B1382891 : Blo 1381510 1382891 := bstep (se 1 (by rfl) ⟨1037168, by rfl⟩ : syracuseStep 1382891 = 2074337) B2074337
theorem B1382903 : Blo 1381510 1382903 := bstep (se 1 (by rfl) ⟨1037177, by rfl⟩ : syracuseStep 1382903 = 2074355) B2074355
theorem B3111425 : Blo 1381510 3111425 := bstep (se 2 (by rfl) ⟨1166784, by rfl⟩ : syracuseStep 3111425 = 2333569) B2333569
theorem B1382923 : Blo 1381510 1382923 := bstep (se 1 (by rfl) ⟨1037192, by rfl⟩ : syracuseStep 1382923 = 2074385) B2074385
theorem B17717777 : Blo 1381510 17717777 := bstep (se 2 (by rfl) ⟨6644166, by rfl⟩ : syracuseStep 17717777 = 13288333) B13288333
theorem B1382935 : Blo 1381510 1382935 := bstep (se 1 (by rfl) ⟨1037201, by rfl⟩ : syracuseStep 1382935 = 2074403) B2074403
theorem B11205155 : Blo 1381510 11205155 := bstep (se 1 (by rfl) ⟨8403866, by rfl⟩ : syracuseStep 11205155 = 16807733) B16807733
theorem B1382955 : Blo 1381510 1382955 := bstep (se 1 (by rfl) ⟨1037216, by rfl⟩ : syracuseStep 1382955 = 2074433) B2074433
theorem B1382967 : Blo 1381510 1382967 := bstep (se 1 (by rfl) ⟨1037225, by rfl⟩ : syracuseStep 1382967 = 2074451) B2074451
theorem B1382987 : Blo 1381510 1382987 := bstep (se 1 (by rfl) ⟨1037240, by rfl⟩ : syracuseStep 1382987 = 2074481) B2074481
theorem B1382999 : Blo 1381510 1382999 := bstep (se 1 (by rfl) ⟨1037249, by rfl⟩ : syracuseStep 1382999 = 2074499) B2074499
theorem B2243161 : Blo 1381510 2243161 := bstep (se 2 (by rfl) ⟨841185, by rfl⟩ : syracuseStep 2243161 = 1682371) B1682371
theorem B1555051 : Blo 1381510 1555051 := bstep (se 1 (by rfl) ⟨1166288, by rfl⟩ : syracuseStep 1555051 = 2332577) B2332577
theorem B1383019 : Blo 1381510 1383019 := bstep (se 1 (by rfl) ⟨1037264, by rfl⟩ : syracuseStep 1383019 = 2074529) B2074529
theorem B1383031 : Blo 1381510 1383031 := bstep (se 1 (by rfl) ⟨1037273, by rfl⟩ : syracuseStep 1383031 = 2074547) B2074547
theorem B1383051 : Blo 1381510 1383051 := bstep (se 1 (by rfl) ⟨1037288, by rfl⟩ : syracuseStep 1383051 = 2074577) B2074577
theorem B5249681 : Blo 1381510 5249681 := bstep (se 2 (by rfl) ⟨1968630, by rfl⟩ : syracuseStep 5249681 = 3937261) B3937261
theorem B1383063 : Blo 1381510 1383063 := bstep (se 1 (by rfl) ⟨1037297, by rfl⟩ : syracuseStep 1383063 = 2074595) B2074595
theorem B1383083 : Blo 1381510 1383083 := bstep (se 1 (by rfl) ⟨1037312, by rfl⟩ : syracuseStep 1383083 = 2074625) B2074625
theorem B4668083 : Blo 1381510 4668083 := bstep (se 1 (by rfl) ⟨3501062, by rfl⟩ : syracuseStep 4668083 = 7002125) B7002125
theorem B1383095 : Blo 1381510 1383095 := bstep (se 1 (by rfl) ⟨1037321, by rfl⟩ : syracuseStep 1383095 = 2074643) B2074643
theorem B2333387 : Blo 1381510 2333387 := bstep (se 1 (by rfl) ⟨1750040, by rfl⟩ : syracuseStep 2333387 = 3500081) B3500081
theorem B1383115 : Blo 1381510 1383115 := bstep (se 1 (by rfl) ⟨1037336, by rfl⟩ : syracuseStep 1383115 = 2074673) B2074673
theorem B1555159 : Blo 1381510 1555159 := bstep (se 1 (by rfl) ⟨1166369, by rfl⟩ : syracuseStep 1555159 = 2332739) B2332739
theorem B1383127 : Blo 1381510 1383127 := bstep (se 1 (by rfl) ⟨1037345, by rfl⟩ : syracuseStep 1383127 = 2074691) B2074691
theorem B3111641 : Blo 1381510 3111641 := bstep (se 2 (by rfl) ⟨1166865, by rfl⟩ : syracuseStep 3111641 = 2333731) B2333731
theorem B1383147 : Blo 1381510 1383147 := bstep (se 1 (by rfl) ⟨1037360, by rfl⟩ : syracuseStep 1383147 = 2074721) B2074721
theorem B1383159 : Blo 1381510 1383159 := bstep (se 1 (by rfl) ⟨1037369, by rfl⟩ : syracuseStep 1383159 = 2074739) B2074739
theorem B15964933 : Blo 1381510 15964933 := bstep (se 4 (by rfl) ⟨1496712, by rfl⟩ : syracuseStep 15964933 = 2993425) B2993425
theorem B2661131 : Blo 1381510 2661131 := bstep (se 1 (by rfl) ⟨1995848, by rfl⟩ : syracuseStep 2661131 = 3991697) B3991697
theorem B1383179 : Blo 1381510 1383179 := bstep (se 1 (by rfl) ⟨1037384, by rfl⟩ : syracuseStep 1383179 = 2074769) B2074769
theorem B1383191 : Blo 1381510 1383191 := bstep (se 1 (by rfl) ⟨1037393, by rfl⟩ : syracuseStep 1383191 = 2074787) B2074787
theorem B1383211 : Blo 1381510 1383211 := bstep (se 1 (by rfl) ⟨1037408, by rfl⟩ : syracuseStep 1383211 = 2074817) B2074817
theorem B3111731 : Blo 1381510 3111731 := bstep (se 1 (by rfl) ⟨2333798, by rfl⟩ : syracuseStep 3111731 = 4667597) B4667597
theorem B1383223 : Blo 1381510 1383223 := bstep (se 1 (by rfl) ⟨1037417, by rfl⟩ : syracuseStep 1383223 = 2074835) B2074835
theorem B2333515 : Blo 1381510 2333515 := bstep (se 1 (by rfl) ⟨1750136, by rfl⟩ : syracuseStep 2333515 = 3500273) B3500273
theorem B1383243 : Blo 1381510 1383243 := bstep (se 1 (by rfl) ⟨1037432, by rfl⟩ : syracuseStep 1383243 = 2074865) B2074865
theorem B3111767 : Blo 1381510 3111767 := bstep (se 1 (by rfl) ⟨2333825, by rfl⟩ : syracuseStep 3111767 = 4667651) B4667651
theorem B1383255 : Blo 1381510 1383255 := bstep (se 1 (by rfl) ⟨1037441, by rfl⟩ : syracuseStep 1383255 = 2074883) B2074883
theorem B1383275 : Blo 1381510 1383275 := bstep (se 1 (by rfl) ⟨1037456, by rfl⟩ : syracuseStep 1383275 = 2074913) B2074913
theorem B1383287 : Blo 1381510 1383287 := bstep (se 1 (by rfl) ⟨1037465, by rfl⟩ : syracuseStep 1383287 = 2074931) B2074931
theorem B1555339 : Blo 1381510 1555339 := bstep (se 1 (by rfl) ⟨1166504, by rfl⟩ : syracuseStep 1555339 = 2333009) B2333009
theorem B1383307 : Blo 1381510 1383307 := bstep (se 1 (by rfl) ⟨1037480, by rfl⟩ : syracuseStep 1383307 = 2074961) B2074961
theorem B1383319 : Blo 1381510 1383319 := bstep (se 1 (by rfl) ⟨1037489, by rfl⟩ : syracuseStep 1383319 = 2074979) B2074979
theorem B1383339 : Blo 1381510 1383339 := bstep (se 1 (by rfl) ⟨1037504, by rfl⟩ : syracuseStep 1383339 = 2075009) B2075009
theorem B1383351 : Blo 1381510 1383351 := bstep (se 1 (by rfl) ⟨1037513, by rfl⟩ : syracuseStep 1383351 = 2075027) B2075027
theorem B5905345 : Blo 1381510 5905345 := bstep (se 2 (by rfl) ⟨2214504, by rfl⟩ : syracuseStep 5905345 = 4429009) B4429009
theorem B4668353 : Blo 1381510 4668353 := bstep (se 2 (by rfl) ⟨1750632, by rfl⟩ : syracuseStep 4668353 = 3501265) B3501265
theorem B1383371 : Blo 1381510 1383371 := bstep (se 1 (by rfl) ⟨1037528, by rfl⟩ : syracuseStep 1383371 = 2075057) B2075057
theorem B1383383 : Blo 1381510 1383383 := bstep (se 1 (by rfl) ⟨1037537, by rfl⟩ : syracuseStep 1383383 = 2075075) B2075075
theorem B2333657 : Blo 1381510 2333657 := bstep (se 2 (by rfl) ⟨875121, by rfl⟩ : syracuseStep 2333657 = 1750243) B1750243
theorem B7003097 : Blo 1381510 7003097 := bstep (se 2 (by rfl) ⟨2626161, by rfl⟩ : syracuseStep 7003097 = 5252323) B5252323
theorem B1383403 : Blo 1381510 1383403 := bstep (se 1 (by rfl) ⟨1037552, by rfl⟩ : syracuseStep 1383403 = 2075105) B2075105
theorem B1555447 : Blo 1381510 1555447 := bstep (se 1 (by rfl) ⟨1166585, by rfl⟩ : syracuseStep 1555447 = 2333171) B2333171
theorem B1383415 : Blo 1381510 1383415 := bstep (se 1 (by rfl) ⟨1037561, by rfl⟩ : syracuseStep 1383415 = 2075123) B2075123
theorem B3111947 : Blo 1381510 3111947 := bstep (se 1 (by rfl) ⟨2333960, by rfl⟩ : syracuseStep 3111947 = 4667921) B4667921
theorem B1383435 : Blo 1381510 1383435 := bstep (se 1 (by rfl) ⟨1037576, by rfl⟩ : syracuseStep 1383435 = 2075153) B2075153
theorem B1383447 : Blo 1381510 1383447 := bstep (se 1 (by rfl) ⟨1037585, by rfl⟩ : syracuseStep 1383447 = 2075171) B2075171
theorem B1383467 : Blo 1381510 1383467 := bstep (se 1 (by rfl) ⟨1037600, by rfl⟩ : syracuseStep 1383467 = 2075201) B2075201
theorem B1383479 : Blo 1381510 1383479 := bstep (se 1 (by rfl) ⟨1037609, by rfl⟩ : syracuseStep 1383479 = 2075219) B2075219
theorem B3112001 : Blo 1381510 3112001 := bstep (se 2 (by rfl) ⟨1167000, by rfl⟩ : syracuseStep 3112001 = 2334001) B2334001
theorem B1383499 : Blo 1381510 1383499 := bstep (se 1 (by rfl) ⟨1037624, by rfl⟩ : syracuseStep 1383499 = 2075249) B2075249
theorem B2333785 : Blo 1381510 2333785 := bstep (se 2 (by rfl) ⟨875169, by rfl⟩ : syracuseStep 2333785 = 1750339) B1750339
theorem B1555627 : Blo 1381510 1555627 := bstep (se 1 (by rfl) ⟨1166720, by rfl⟩ : syracuseStep 1555627 = 2333441) B2333441
theorem B19930373 : Blo 1381510 19930373 := bstep (se 4 (by rfl) ⟨1868472, by rfl⟩ : syracuseStep 19930373 = 3736945) B3736945
theorem B1555735 : Blo 1381510 1555735 := bstep (se 1 (by rfl) ⟨1166801, by rfl⟩ : syracuseStep 1555735 = 2333603) B2333603
theorem B3939607 : Blo 1381510 3939607 := bstep (se 1 (by rfl) ⟨2954705, by rfl⟩ : syracuseStep 3939607 = 5909411) B5909411
theorem B3112217 : Blo 1381510 3112217 := bstep (se 2 (by rfl) ⟨1167081, by rfl⟩ : syracuseStep 3112217 = 2334163) B2334163
theorem B5250379 : Blo 1381510 5250379 := bstep (se 1 (by rfl) ⟨3937784, by rfl⟩ : syracuseStep 5250379 = 7875569) B7875569
theorem B3112307 : Blo 1381510 3112307 := bstep (se 1 (by rfl) ⟨2334230, by rfl⟩ : syracuseStep 3112307 = 4668461) B4668461
theorem B3112343 : Blo 1381510 3112343 := bstep (se 1 (by rfl) ⟨2334257, by rfl⟩ : syracuseStep 3112343 = 4668515) B4668515
theorem B1555915 : Blo 1381510 1555915 := bstep (se 1 (by rfl) ⟨1166936, by rfl⟩ : syracuseStep 1555915 = 2333873) B2333873
theorem B4668893 : Blo 1381510 4668893 := bstep (se 3 (by rfl) ⟨875417, by rfl⟩ : syracuseStep 4668893 = 1750835) B1750835
theorem B25230865 : Blo 1381510 25230865 := bstep (se 2 (by rfl) ⟨9461574, by rfl⟩ : syracuseStep 25230865 = 18923149) B18923149
theorem B1556023 : Blo 1381510 1556023 := bstep (se 1 (by rfl) ⟨1167017, by rfl⟩ : syracuseStep 1556023 = 2334035) B2334035
theorem B3112523 : Blo 1381510 3112523 := bstep (se 1 (by rfl) ⟨2334392, by rfl⟩ : syracuseStep 3112523 = 4668785) B4668785
theorem B5250653 : Blo 1381510 5250653 := bstep (se 3 (by rfl) ⟨984497, by rfl⟩ : syracuseStep 5250653 = 1968995) B1968995
theorem B3112577 : Blo 1381510 3112577 := bstep (se 2 (by rfl) ⟨1167216, by rfl⟩ : syracuseStep 3112577 = 2334433) B2334433
theorem B2334359 : Blo 1381510 2334359 := bstep (se 1 (by rfl) ⟨1750769, by rfl⟩ : syracuseStep 2334359 = 3501539) B3501539
theorem B3497651 : Blo 1381510 3497651 := bstep (se 1 (by rfl) ⟨2623238, by rfl⟩ : syracuseStep 3497651 = 5246477) B5246477
theorem B2072267 : Blo 1381510 2072267 := bstep (se 1 (by rfl) ⟨1554200, by rfl⟩ : syracuseStep 2072267 = 3108401) B3108401
theorem B2072279 : Blo 1381510 2072279 := bstep (se 1 (by rfl) ⟨1554209, by rfl⟩ : syracuseStep 2072279 = 3108419) B3108419
theorem B9961177 : Blo 1381510 9961177 := bstep (se 2 (by rfl) ⟨3735441, by rfl⟩ : syracuseStep 9961177 = 7470883) B7470883
theorem B1556203 : Blo 1381510 1556203 := bstep (se 1 (by rfl) ⟨1167152, by rfl⟩ : syracuseStep 1556203 = 2334305) B2334305
theorem B9969425 : Blo 1381510 9969425 := bstep (se 2 (by rfl) ⟨3738534, by rfl⟩ : syracuseStep 9969425 = 7477069) B7477069
theorem B2334487 : Blo 1381510 2334487 := bstep (se 1 (by rfl) ⟨1750865, by rfl⟩ : syracuseStep 2334487 = 3501731) B3501731
theorem B2072345 : Blo 1381510 2072345 := bstep (se 2 (by rfl) ⟨777129, by rfl⟩ : syracuseStep 2072345 = 1554259) B1554259
theorem B1556311 : Blo 1381510 1556311 := bstep (se 1 (by rfl) ⟨1167233, by rfl⟩ : syracuseStep 1556311 = 2334467) B2334467
theorem B3112793 : Blo 1381510 3112793 := bstep (se 2 (by rfl) ⟨1167297, by rfl⟩ : syracuseStep 3112793 = 2334595) B2334595
theorem B3735389 : Blo 1381510 3735389 := bstep (se 3 (by rfl) ⟨700385, by rfl⟩ : syracuseStep 3735389 = 1400771) B1400771
theorem B2072459 : Blo 1381510 2072459 := bstep (se 1 (by rfl) ⟨1554344, by rfl⟩ : syracuseStep 2072459 = 3108689) B3108689
theorem B2072471 : Blo 1381510 2072471 := bstep (se 1 (by rfl) ⟨1554353, by rfl⟩ : syracuseStep 2072471 = 3108707) B3108707
theorem B3112883 : Blo 1381510 3112883 := bstep (se 1 (by rfl) ⟨2334662, by rfl⟩ : syracuseStep 3112883 = 4669325) B4669325
theorem B2072537 : Blo 1381510 2072537 := bstep (se 2 (by rfl) ⟨777201, by rfl⟩ : syracuseStep 2072537 = 1554403) B1554403
theorem B2072591 : Blo 1381510 2072591 := bstep (se 1 (by rfl) ⟨1554443, by rfl⟩ : syracuseStep 2072591 = 3108887) B3108887
theorem B2072633 : Blo 1381510 2072633 := bstep (se 2 (by rfl) ⟨777237, by rfl⟩ : syracuseStep 2072633 = 1554475) B1554475
theorem B5251139 : Blo 1381510 5251139 := bstep (se 1 (by rfl) ⟨3938354, by rfl⟩ : syracuseStep 5251139 = 7876709) B7876709
theorem B2072711 : Blo 1381510 2072711 := bstep (se 1 (by rfl) ⟨1554533, by rfl⟩ : syracuseStep 2072711 = 3109067) B3109067
theorem B3498137 : Blo 1381510 3498137 := bstep (se 2 (by rfl) ⟨1311801, by rfl⟩ : syracuseStep 3498137 = 2623603) B2623603
theorem B2072747 : Blo 1381510 2072747 := bstep (se 1 (by rfl) ⟨1554560, by rfl⟩ : syracuseStep 2072747 = 3109121) B3109121
theorem B2072777 : Blo 1381510 2072777 := bstep (se 2 (by rfl) ⟨777291, by rfl⟩ : syracuseStep 2072777 = 1554583) B1554583
theorem B2072891 : Blo 1381510 2072891 := bstep (se 1 (by rfl) ⟨1554668, by rfl⟩ : syracuseStep 2072891 = 3109337) B3109337
theorem B3498299 : Blo 1381510 3498299 := bstep (se 1 (by rfl) ⟨2623724, by rfl⟩ : syracuseStep 3498299 = 5247449) B5247449
theorem B10502459 : Blo 1381510 10502459 := bstep (se 1 (by rfl) ⟨7876844, by rfl⟩ : syracuseStep 10502459 = 15753689) B15753689
theorem B2072951 : Blo 1381510 2072951 := bstep (se 1 (by rfl) ⟨1554713, by rfl⟩ : syracuseStep 2072951 = 3109427) B3109427
theorem B9970055 : Blo 1381510 9970055 := bstep (se 1 (by rfl) ⟨7477541, by rfl⟩ : syracuseStep 9970055 = 14955083) B14955083
theorem B2072975 : Blo 1381510 2072975 := bstep (se 1 (by rfl) ⟨1554731, by rfl⟩ : syracuseStep 2072975 = 3109463) B3109463
theorem B2073017 : Blo 1381510 2073017 := bstep (se 2 (by rfl) ⟨777381, by rfl⟩ : syracuseStep 2073017 = 1554763) B1554763
theorem B26567129 : Blo 1381510 26567129 := bstep (se 2 (by rfl) ⟨9962673, by rfl⟩ : syracuseStep 26567129 = 19925347) B19925347
theorem B7094749 : Blo 1381510 7094749 := bstep (se 3 (by rfl) ⟨1330265, by rfl⟩ : syracuseStep 7094749 = 2660531) B2660531
theorem B6644227 : Blo 1381510 6644227 := bstep (se 1 (by rfl) ⟨4983170, by rfl⟩ : syracuseStep 6644227 = 9966341) B9966341
theorem B2073095 : Blo 1381510 2073095 := bstep (se 1 (by rfl) ⟨1554821, by rfl⟩ : syracuseStep 2073095 = 3109643) B3109643
theorem B3498511 : Blo 1381510 3498511 := bstep (se 1 (by rfl) ⟨2623883, by rfl⟩ : syracuseStep 3498511 = 5247767) B5247767
theorem B2073131 : Blo 1381510 2073131 := bstep (se 1 (by rfl) ⟨1554848, by rfl⟩ : syracuseStep 2073131 = 3109697) B3109697
theorem B2073161 : Blo 1381510 2073161 := bstep (se 2 (by rfl) ⟨777435, by rfl⟩ : syracuseStep 2073161 = 1554871) B1554871
theorem B2491015 : Blo 1381510 2491015 := bstep (se 1 (by rfl) ⟨1868261, by rfl⟩ : syracuseStep 2491015 = 3736523) B3736523
theorem B2073275 : Blo 1381510 2073275 := bstep (se 1 (by rfl) ⟨1554956, by rfl⟩ : syracuseStep 2073275 = 3109913) B3109913
theorem B2073335 : Blo 1381510 2073335 := bstep (se 1 (by rfl) ⟨1555001, by rfl⟩ : syracuseStep 2073335 = 3110003) B3110003
theorem B2073359 : Blo 1381510 2073359 := bstep (se 1 (by rfl) ⟨1555019, by rfl⟩ : syracuseStep 2073359 = 3110039) B3110039
theorem B2990881 : Blo 1381510 2990881 := bstep (se 2 (by rfl) ⟨1121580, by rfl⟩ : syracuseStep 2990881 = 2243161) B2243161
theorem B3498785 : Blo 1381510 3498785 := bstep (se 2 (by rfl) ⟨1312044, by rfl⟩ : syracuseStep 3498785 = 2624089) B2624089
theorem B15737651 : Blo 1381510 15737651 := bstep (se 1 (by rfl) ⟨11803238, by rfl⟩ : syracuseStep 15737651 = 23606477) B23606477
theorem B2073401 : Blo 1381510 2073401 := bstep (se 2 (by rfl) ⟨777525, by rfl⟩ : syracuseStep 2073401 = 1555051) B1555051
theorem B2073479 : Blo 1381510 2073479 := bstep (se 1 (by rfl) ⟨1555109, by rfl⟩ : syracuseStep 2073479 = 3110219) B3110219
theorem B2073515 : Blo 1381510 2073515 := bstep (se 1 (by rfl) ⟨1555136, by rfl⟩ : syracuseStep 2073515 = 3110273) B3110273
theorem B2073545 : Blo 1381510 2073545 := bstep (se 2 (by rfl) ⟨777579, by rfl⟩ : syracuseStep 2073545 = 1555159) B1555159
theorem B1967161 : Blo 1381510 1967161 := bstep (se 2 (by rfl) ⟨737685, by rfl⟩ : syracuseStep 1967161 = 1475371) B1475371
theorem B2073659 : Blo 1381510 2073659 := bstep (se 1 (by rfl) ⟨1555244, by rfl⟩ : syracuseStep 2073659 = 3110489) B3110489
theorem B7980119 : Blo 1381510 7980119 := bstep (se 1 (by rfl) ⟨5985089, by rfl⟩ : syracuseStep 7980119 = 11970179) B11970179
theorem B2073719 : Blo 1381510 2073719 := bstep (se 1 (by rfl) ⟨1555289, by rfl⟩ : syracuseStep 2073719 = 3110579) B3110579
theorem B1401991 : Blo 1381510 1401991 := bstep (se 1 (by rfl) ⟨1051493, by rfl⟩ : syracuseStep 1401991 = 2102987) B2102987
theorem B2073743 : Blo 1381510 2073743 := bstep (se 1 (by rfl) ⟨1555307, by rfl⟩ : syracuseStep 2073743 = 3110615) B3110615
theorem B1967275 : Blo 1381510 1967275 := bstep (se 1 (by rfl) ⟨1475456, by rfl⟩ : syracuseStep 1967275 = 2950913) B2950913
theorem B2073785 : Blo 1381510 2073785 := bstep (se 2 (by rfl) ⟨777669, by rfl⟩ : syracuseStep 2073785 = 1555339) B1555339
theorem B7873793 : Blo 1381510 7873793 := bstep (se 2 (by rfl) ⟨2952672, by rfl⟩ : syracuseStep 7873793 = 5905345) B5905345
theorem B2073863 : Blo 1381510 2073863 := bstep (se 1 (by rfl) ⟨1555397, by rfl⟩ : syracuseStep 2073863 = 3110795) B3110795
theorem B2073899 : Blo 1381510 2073899 := bstep (se 1 (by rfl) ⟨1555424, by rfl⟩ : syracuseStep 2073899 = 3110849) B3110849
theorem B2073929 : Blo 1381510 2073929 := bstep (se 2 (by rfl) ⟨777723, by rfl⟩ : syracuseStep 2073929 = 1555447) B1555447
theorem B1967503 : Blo 1381510 1967503 := bstep (se 1 (by rfl) ⟨1475627, by rfl⟩ : syracuseStep 1967503 = 2951255) B2951255
theorem B7472569 : Blo 1381510 7472569 := bstep (se 2 (by rfl) ⟨2802213, by rfl⟩ : syracuseStep 7472569 = 5604427) B5604427
theorem B2074043 : Blo 1381510 2074043 := bstep (se 1 (by rfl) ⟨1555532, by rfl⟩ : syracuseStep 2074043 = 3111065) B3111065
theorem B2074103 : Blo 1381510 2074103 := bstep (se 1 (by rfl) ⟨1555577, by rfl⟩ : syracuseStep 2074103 = 3111155) B3111155
theorem B2074127 : Blo 1381510 2074127 := bstep (se 1 (by rfl) ⟨1555595, by rfl⟩ : syracuseStep 2074127 = 3111191) B3111191
theorem B2074169 : Blo 1381510 2074169 := bstep (se 2 (by rfl) ⟨777813, by rfl⟩ : syracuseStep 2074169 = 1555627) B1555627
theorem B4662845 : Blo 1381510 4662845 := bstep (se 3 (by rfl) ⟨874283, by rfl⟩ : syracuseStep 4662845 = 1748567) B1748567
theorem B10643021 : Blo 1381510 10643021 := bstep (se 3 (by rfl) ⟨1995566, by rfl⟩ : syracuseStep 10643021 = 3991133) B3991133
theorem B2074247 : Blo 1381510 2074247 := bstep (se 1 (by rfl) ⟨1555685, by rfl⟩ : syracuseStep 2074247 = 3111371) B3111371
theorem B2074283 : Blo 1381510 2074283 := bstep (se 1 (by rfl) ⟨1555712, by rfl⟩ : syracuseStep 2074283 = 3111425) B3111425
theorem B2074313 : Blo 1381510 2074313 := bstep (se 2 (by rfl) ⟨777867, by rfl⟩ : syracuseStep 2074313 = 1555735) B1555735
theorem B5252809 : Blo 1381510 5252809 := bstep (se 2 (by rfl) ⟨1969803, by rfl⟩ : syracuseStep 5252809 = 3939607) B3939607
theorem B11364097 : Blo 1381510 11364097 := bstep (se 2 (by rfl) ⟨4261536, by rfl⟩ : syracuseStep 11364097 = 8523073) B8523073
theorem B3499787 : Blo 1381510 3499787 := bstep (se 1 (by rfl) ⟨2624840, by rfl⟩ : syracuseStep 3499787 = 5249681) B5249681
theorem B3737387 : Blo 1381510 3737387 := bstep (se 1 (by rfl) ⟨2803040, by rfl⟩ : syracuseStep 3737387 = 5606081) B5606081
theorem B2074427 : Blo 1381510 2074427 := bstep (se 1 (by rfl) ⟨1555820, by rfl⟩ : syracuseStep 2074427 = 3111641) B3111641
theorem B2074487 : Blo 1381510 2074487 := bstep (se 1 (by rfl) ⟨1555865, by rfl⟩ : syracuseStep 2074487 = 3111731) B3111731
theorem B2623367 : Blo 1381510 2623367 := bstep (se 1 (by rfl) ⟨1967525, by rfl⟩ : syracuseStep 2623367 = 3935051) B3935051
theorem B2074511 : Blo 1381510 2074511 := bstep (se 1 (by rfl) ⟨1555883, by rfl⟩ : syracuseStep 2074511 = 3111767) B3111767
theorem B6997913 : Blo 1381510 6997913 := bstep (se 2 (by rfl) ⟨2624217, by rfl⟩ : syracuseStep 6997913 = 5248435) B5248435
theorem B2074553 : Blo 1381510 2074553 := bstep (se 2 (by rfl) ⟨777957, by rfl⟩ : syracuseStep 2074553 = 1555915) B1555915
theorem B2074631 : Blo 1381510 2074631 := bstep (se 1 (by rfl) ⟨1555973, by rfl⟩ : syracuseStep 2074631 = 3111947) B3111947
theorem B7096349 : Blo 1381510 7096349 := bstep (se 3 (by rfl) ⟨1330565, by rfl⟩ : syracuseStep 7096349 = 2661131) B2661131
theorem B2074667 : Blo 1381510 2074667 := bstep (se 1 (by rfl) ⟨1556000, by rfl⟩ : syracuseStep 2074667 = 3112001) B3112001
theorem B2074697 : Blo 1381510 2074697 := bstep (se 2 (by rfl) ⟨778011, by rfl⟩ : syracuseStep 2074697 = 1556023) B1556023
theorem B3737735 : Blo 1381510 3737735 := bstep (se 1 (by rfl) ⟨2803301, by rfl⟩ : syracuseStep 3737735 = 5606603) B5606603
theorem B2074811 : Blo 1381510 2074811 := bstep (se 1 (by rfl) ⟨1556108, by rfl⟩ : syracuseStep 2074811 = 3112217) B3112217
theorem B7473389 : Blo 1381510 7473389 := bstep (se 3 (by rfl) ⟨1401260, by rfl⟩ : syracuseStep 7473389 = 2802521) B2802521
theorem B2074871 : Blo 1381510 2074871 := bstep (se 1 (by rfl) ⟨1556153, by rfl⟩ : syracuseStep 2074871 = 3112307) B3112307
theorem B1968391 : Blo 1381510 1968391 := bstep (se 1 (by rfl) ⟨1476293, by rfl⟩ : syracuseStep 1968391 = 2952587) B2952587
theorem B2074895 : Blo 1381510 2074895 := bstep (se 1 (by rfl) ⟨1556171, by rfl⟩ : syracuseStep 2074895 = 3112343) B3112343
theorem B13281569 : Blo 1381510 13281569 := bstep (se 2 (by rfl) ⟨4980588, by rfl⟩ : syracuseStep 13281569 = 9961177) B9961177
theorem B2074937 : Blo 1381510 2074937 := bstep (se 2 (by rfl) ⟨778101, by rfl⟩ : syracuseStep 2074937 = 1556203) B1556203
theorem B5605691 : Blo 1381510 5605691 := bstep (se 1 (by rfl) ⟨4204268, by rfl⟩ : syracuseStep 5605691 = 8408537) B8408537
theorem B2075015 : Blo 1381510 2075015 := bstep (se 1 (by rfl) ⟨1556261, by rfl⟩ : syracuseStep 2075015 = 3112523) B3112523
theorem B3500435 : Blo 1381510 3500435 := bstep (se 1 (by rfl) ⟨2625326, by rfl⟩ : syracuseStep 3500435 = 5250653) B5250653
theorem B2075051 : Blo 1381510 2075051 := bstep (se 1 (by rfl) ⟨1556288, by rfl⟩ : syracuseStep 2075051 = 3112577) B3112577
theorem B2075081 : Blo 1381510 2075081 := bstep (se 2 (by rfl) ⟨778155, by rfl⟩ : syracuseStep 2075081 = 1556311) B1556311
theorem B6646225 : Blo 1381510 6646225 := bstep (se 2 (by rfl) ⟨2492334, by rfl⟩ : syracuseStep 6646225 = 4984669) B4984669
theorem B22432241 : Blo 1381510 22432241 := bstep (se 2 (by rfl) ⟨8412090, by rfl⟩ : syracuseStep 22432241 = 16824181) B16824181
theorem B6646283 : Blo 1381510 6646283 := bstep (se 1 (by rfl) ⟨4984712, by rfl⟩ : syracuseStep 6646283 = 9969425) B9969425
theorem B2214415 : Blo 1381510 2214415 := bstep (se 1 (by rfl) ⟨1660811, by rfl⟩ : syracuseStep 2214415 = 3321623) B3321623
theorem B2075195 : Blo 1381510 2075195 := bstep (se 1 (by rfl) ⟨1556396, by rfl⟩ : syracuseStep 2075195 = 3112793) B3112793
theorem B5605955 : Blo 1381510 5605955 := bstep (se 1 (by rfl) ⟨4204466, by rfl⟩ : syracuseStep 5605955 = 8408933) B8408933
theorem B2075255 : Blo 1381510 2075255 := bstep (se 1 (by rfl) ⟨1556441, by rfl⟩ : syracuseStep 2075255 = 3112883) B3112883
theorem B3500729 : Blo 1381510 3500729 := bstep (se 2 (by rfl) ⟨1312773, by rfl⟩ : syracuseStep 3500729 = 2625547) B2625547
theorem B1968887 : Blo 1381510 1968887 := bstep (se 1 (by rfl) ⟨1476665, by rfl⟩ : syracuseStep 1968887 = 2953331) B2953331
theorem B3738383 : Blo 1381510 3738383 := bstep (se 1 (by rfl) ⟨2803787, by rfl⟩ : syracuseStep 3738383 = 5607575) B5607575
theorem B5909395 : Blo 1381510 5909395 := bstep (se 1 (by rfl) ⟨4432046, by rfl⟩ : syracuseStep 5909395 = 8864093) B8864093
theorem B4664249 : Blo 1381510 4664249 := bstep (se 2 (by rfl) ⟨1749093, by rfl⟩ : syracuseStep 4664249 = 3498187) B3498187
theorem B3320777 : Blo 1381510 3320777 := bstep (se 2 (by rfl) ⟨1245291, by rfl⟩ : syracuseStep 3320777 = 2490583) B2490583
theorem B3935233 : Blo 1381510 3935233 := bstep (se 2 (by rfl) ⟨1475712, by rfl⟩ : syracuseStep 3935233 = 2951425) B2951425
theorem B15961205 : Blo 1381510 15961205 := bstep (se 5 (by rfl) ⟨748181, by rfl⟩ : syracuseStep 15961205 = 1496363) B1496363
theorem B11816225 : Blo 1381510 11816225 := bstep (se 2 (by rfl) ⟨4431084, by rfl⟩ : syracuseStep 11816225 = 8862169) B8862169
theorem B5049715 : Blo 1381510 5049715 := bstep (se 1 (by rfl) ⟨3787286, by rfl⟩ : syracuseStep 5049715 = 7574573) B7574573
theorem B3501427 : Blo 1381510 3501427 := bstep (se 1 (by rfl) ⟨2626070, by rfl⟩ : syracuseStep 3501427 = 5252141) B5252141
theorem B7876025 : Blo 1381510 7876025 := bstep (se 2 (by rfl) ⟨2953509, by rfl⟩ : syracuseStep 7876025 = 5907019) B5907019
theorem B3501569 : Blo 1381510 3501569 := bstep (se 2 (by rfl) ⟨1313088, by rfl⟩ : syracuseStep 3501569 = 2626177) B2626177
theorem B4664843 : Blo 1381510 4664843 := bstep (se 1 (by rfl) ⟨3498632, by rfl⟩ : syracuseStep 4664843 = 6997265) B6997265
theorem B3935803 : Blo 1381510 3935803 := bstep (se 1 (by rfl) ⟨2951852, by rfl⟩ : syracuseStep 3935803 = 5903705) B5903705
theorem B3321431 : Blo 1381510 3321431 := bstep (se 1 (by rfl) ⟨2491073, by rfl⟩ : syracuseStep 3321431 = 4982147) B4982147
theorem B4664951 : Blo 1381510 4664951 := bstep (se 1 (by rfl) ⟨3498713, by rfl⟩ : syracuseStep 4664951 = 6997427) B6997427
theorem B1748623 : Blo 1381510 1748623 := bstep (se 1 (by rfl) ⟨1311467, by rfl⟩ : syracuseStep 1748623 = 2622935) B2622935
theorem B21286577 : Blo 1381510 21286577 := bstep (se 2 (by rfl) ⟨7982466, by rfl⟩ : syracuseStep 21286577 = 15964933) B15964933
theorem B1969849 : Blo 1381510 1969849 := bstep (se 2 (by rfl) ⟨738693, by rfl⟩ : syracuseStep 1969849 = 1477387) B1477387
theorem B3739421 : Blo 1381510 3739421 := bstep (se 3 (by rfl) ⟨701141, by rfl⟩ : syracuseStep 3739421 = 1402283) B1402283
theorem B3108743 : Blo 1381510 3108743 := bstep (se 1 (by rfl) ⟨2331557, by rfl⟩ : syracuseStep 3108743 = 4663115) B4663115
theorem B4042811 : Blo 1381510 4042811 := bstep (se 1 (by rfl) ⟨3032108, by rfl⟩ : syracuseStep 4042811 = 6064217) B6064217
theorem B3108923 : Blo 1381510 3108923 := bstep (se 1 (by rfl) ⟨2331692, by rfl⟩ : syracuseStep 3108923 = 4663385) B4663385
theorem B2101307 : Blo 1381510 2101307 := bstep (se 1 (by rfl) ⟨1575980, by rfl⟩ : syracuseStep 2101307 = 3151961) B3151961
theorem B29880413 : Blo 1381510 29880413 := bstep (se 3 (by rfl) ⟨5602577, by rfl⟩ : syracuseStep 29880413 = 11205155) B11205155
theorem B3109049 : Blo 1381510 3109049 := bstep (se 2 (by rfl) ⟨1165893, by rfl⟩ : syracuseStep 3109049 = 2331787) B2331787
theorem B4665545 : Blo 1381510 4665545 := bstep (se 2 (by rfl) ⟨1749579, by rfl⟩ : syracuseStep 4665545 = 3499159) B3499159
theorem B3838223 : Blo 1381510 3838223 := bstep (se 1 (by rfl) ⟨2878667, by rfl⟩ : syracuseStep 3838223 = 5757335) B5757335
theorem B14373179 : Blo 1381510 14373179 := bstep (se 1 (by rfl) ⟨10779884, by rfl⟩ : syracuseStep 14373179 = 21559769) B21559769
theorem B2625851 : Blo 1381510 2625851 := bstep (se 1 (by rfl) ⟨1969388, by rfl⟩ : syracuseStep 2625851 = 3938777) B3938777
theorem B1749367 : Blo 1381510 1749367 := bstep (se 1 (by rfl) ⟨1312025, by rfl⟩ : syracuseStep 1749367 = 2624051) B2624051
theorem B7000505 : Blo 1381510 7000505 := bstep (se 2 (by rfl) ⟨2625189, by rfl⟩ : syracuseStep 7000505 = 5250379) B5250379
theorem B3109391 : Blo 1381510 3109391 := bstep (se 1 (by rfl) ⟨2332043, by rfl⟩ : syracuseStep 3109391 = 4664087) B4664087
theorem B3109409 : Blo 1381510 3109409 := bstep (se 2 (by rfl) ⟨1166028, by rfl⟩ : syracuseStep 3109409 = 2332057) B2332057
theorem B136376945 : Blo 1381510 136376945 := bstep (se 2 (by rfl) ⟨51141354, by rfl⟩ : syracuseStep 136376945 = 102282709) B102282709
theorem B1749691 : Blo 1381510 1749691 := bstep (se 1 (by rfl) ⟨1312268, by rfl⟩ : syracuseStep 1749691 = 2624537) B2624537
theorem B33641153 : Blo 1381510 33641153 := bstep (se 2 (by rfl) ⟨12615432, by rfl⟩ : syracuseStep 33641153 = 25230865) B25230865
theorem B2626337 : Blo 1381510 2626337 := bstep (se 2 (by rfl) ⟨984876, by rfl⟩ : syracuseStep 2626337 = 1969753) B1969753
theorem B2732843 : Blo 1381510 2732843 := bstep (se 1 (by rfl) ⟨2049632, by rfl⟩ : syracuseStep 2732843 = 4099265) B4099265
theorem B3109751 : Blo 1381510 3109751 := bstep (se 1 (by rfl) ⟨2332313, by rfl⟩ : syracuseStep 3109751 = 4664627) B4664627
theorem B4666247 : Blo 1381510 4666247 := bstep (se 1 (by rfl) ⟨3499685, by rfl⟩ : syracuseStep 4666247 = 6999371) B6999371
theorem B3109931 : Blo 1381510 3109931 := bstep (se 1 (by rfl) ⟨2332448, by rfl⟩ : syracuseStep 3109931 = 4664897) B4664897
theorem B2331767 : Blo 1381510 2331767 := bstep (se 1 (by rfl) ⟨1748825, by rfl⟩ : syracuseStep 2331767 = 3497651) B3497651
theorem B1381511 : Blo 1381510 1381511 := bstep (se 1 (by rfl) ⟨1036133, by rfl⟩ : syracuseStep 1381511 = 2072267) B2072267
theorem B1381519 : Blo 1381510 1381519 := bstep (se 1 (by rfl) ⟨1036139, by rfl⟩ : syracuseStep 1381519 = 2072279) B2072279
theorem B1750187 : Blo 1381510 1750187 := bstep (se 1 (by rfl) ⟨1312640, by rfl⟩ : syracuseStep 1750187 = 2625281) B2625281
theorem B1381563 : Blo 1381510 1381563 := bstep (se 1 (by rfl) ⟨1036172, by rfl⟩ : syracuseStep 1381563 = 2072345) B2072345
theorem B4666625 : Blo 1381510 4666625 := bstep (se 2 (by rfl) ⟨1749984, by rfl⟩ : syracuseStep 4666625 = 3499969) B3499969
theorem B1381639 : Blo 1381510 1381639 := bstep (se 1 (by rfl) ⟨1036229, by rfl⟩ : syracuseStep 1381639 = 2072459) B2072459
theorem B1381647 : Blo 1381510 1381647 := bstep (se 1 (by rfl) ⟨1036235, by rfl⟩ : syracuseStep 1381647 = 2072471) B2072471
theorem B1381691 : Blo 1381510 1381691 := bstep (se 1 (by rfl) ⟨1036268, by rfl⟩ : syracuseStep 1381691 = 2072537) B2072537
theorem B1381767 : Blo 1381510 1381767 := bstep (se 1 (by rfl) ⟨1036325, by rfl⟩ : syracuseStep 1381767 = 2072651) B2072651
theorem B23950727 : Blo 1381510 23950727 := bstep (se 1 (by rfl) ⟨17963045, by rfl⟩ : syracuseStep 23950727 = 35926091) B35926091
theorem B1381775 : Blo 1381510 1381775 := bstep (se 1 (by rfl) ⟨1036331, by rfl⟩ : syracuseStep 1381775 = 2072663) B2072663
theorem B10491281 : Blo 1381510 10491281 := bstep (se 2 (by rfl) ⟨3934230, by rfl⟩ : syracuseStep 10491281 = 7868461) B7868461
theorem B3110291 : Blo 1381510 3110291 := bstep (se 1 (by rfl) ⟨2332718, by rfl⟩ : syracuseStep 3110291 = 4665437) B4665437
theorem B2561465 : Blo 1381510 2561465 := bstep (se 2 (by rfl) ⟨960549, by rfl⟩ : syracuseStep 2561465 = 1921099) B1921099
theorem B1381819 : Blo 1381510 1381819 := bstep (se 1 (by rfl) ⟨1036364, by rfl⟩ : syracuseStep 1381819 = 2072729) B2072729
theorem B3110345 : Blo 1381510 3110345 := bstep (se 2 (by rfl) ⟨1166379, by rfl⟩ : syracuseStep 3110345 = 2332759) B2332759
theorem B1381895 : Blo 1381510 1381895 := bstep (se 1 (by rfl) ⟨1036421, by rfl⟩ : syracuseStep 1381895 = 2072843) B2072843
theorem B1381903 : Blo 1381510 1381903 := bstep (se 1 (by rfl) ⟨1036427, by rfl⟩ : syracuseStep 1381903 = 2072855) B2072855
theorem B7878167 : Blo 1381510 7878167 := bstep (se 1 (by rfl) ⟨5908625, by rfl⟩ : syracuseStep 7878167 = 11817251) B11817251
theorem B1381947 : Blo 1381510 1381947 := bstep (se 1 (by rfl) ⟨1036460, by rfl⟩ : syracuseStep 1381947 = 2072921) B2072921
theorem B2332219 : Blo 1381510 2332219 := bstep (se 1 (by rfl) ⟨1749164, by rfl⟩ : syracuseStep 2332219 = 3498329) B3498329
theorem B1382023 : Blo 1381510 1382023 := bstep (se 1 (by rfl) ⟨1036517, by rfl⟩ : syracuseStep 1382023 = 2073035) B2073035
theorem B1750663 : Blo 1381510 1750663 := bstep (se 1 (by rfl) ⟨1312997, by rfl⟩ : syracuseStep 1750663 = 2625995) B2625995
theorem B1382031 : Blo 1381510 1382031 := bstep (se 1 (by rfl) ⟨1036523, by rfl⟩ : syracuseStep 1382031 = 2073047) B2073047
theorem B1382075 : Blo 1381510 1382075 := bstep (se 1 (by rfl) ⟨1036556, by rfl⟩ : syracuseStep 1382075 = 2073113) B2073113
theorem B2332361 : Blo 1381510 2332361 := bstep (se 2 (by rfl) ⟨874635, by rfl⟩ : syracuseStep 2332361 = 1749271) B1749271
theorem B7001801 : Blo 1381510 7001801 := bstep (se 2 (by rfl) ⟨2625675, by rfl⟩ : syracuseStep 7001801 = 5251351) B5251351
theorem B1382151 : Blo 1381510 1382151 := bstep (se 1 (by rfl) ⟨1036613, by rfl⟩ : syracuseStep 1382151 = 2073227) B2073227
theorem B1382159 : Blo 1381510 1382159 := bstep (se 1 (by rfl) ⟨1036619, by rfl⟩ : syracuseStep 1382159 = 2073239) B2073239
theorem B11802419 : Blo 1381510 11802419 := bstep (se 1 (by rfl) ⟨8851814, by rfl⟩ : syracuseStep 11802419 = 17703629) B17703629
theorem B1382203 : Blo 1381510 1382203 := bstep (se 1 (by rfl) ⟨1036652, by rfl⟩ : syracuseStep 1382203 = 2073305) B2073305
theorem B1382279 : Blo 1381510 1382279 := bstep (se 1 (by rfl) ⟨1036709, by rfl⟩ : syracuseStep 1382279 = 2073419) B2073419
theorem B1382287 : Blo 1381510 1382287 := bstep (se 1 (by rfl) ⟨1036715, by rfl⟩ : syracuseStep 1382287 = 2073431) B2073431
theorem B3938195 : Blo 1381510 3938195 := bstep (se 1 (by rfl) ⟨2953646, by rfl⟩ : syracuseStep 3938195 = 5907293) B5907293
theorem B5248921 : Blo 1381510 5248921 := bstep (se 2 (by rfl) ⟨1968345, by rfl⟩ : syracuseStep 5248921 = 3936691) B3936691
theorem B1382331 : Blo 1381510 1382331 := bstep (se 1 (by rfl) ⟨1036748, by rfl⟩ : syracuseStep 1382331 = 2073497) B2073497
theorem B1554439 : Blo 1381510 1554439 := bstep (se 1 (by rfl) ⟨1165829, by rfl⟩ : syracuseStep 1554439 = 2331659) B2331659
theorem B1382407 : Blo 1381510 1382407 := bstep (se 1 (by rfl) ⟨1036805, by rfl⟩ : syracuseStep 1382407 = 2073611) B2073611
theorem B7878667 : Blo 1381510 7878667 := bstep (se 1 (by rfl) ⟨5909000, by rfl⟩ : syracuseStep 7878667 = 11818001) B11818001
theorem B1382415 : Blo 1381510 1382415 := bstep (se 1 (by rfl) ⟨1036811, by rfl⟩ : syracuseStep 1382415 = 2073623) B2073623
theorem B4667435 : Blo 1381510 4667435 := bstep (se 1 (by rfl) ⟨3500576, by rfl⟩ : syracuseStep 4667435 = 7001153) B7001153
theorem B1382459 : Blo 1381510 1382459 := bstep (se 1 (by rfl) ⟨1036844, by rfl⟩ : syracuseStep 1382459 = 2073689) B2073689
theorem B1382535 : Blo 1381510 1382535 := bstep (se 1 (by rfl) ⟨1036901, by rfl⟩ : syracuseStep 1382535 = 2073803) B2073803
theorem B3111047 : Blo 1381510 3111047 := bstep (se 1 (by rfl) ⟨2333285, by rfl⟩ : syracuseStep 3111047 = 4666571) B4666571
theorem B1382543 : Blo 1381510 1382543 := bstep (se 1 (by rfl) ⟨1036907, by rfl⟩ : syracuseStep 1382543 = 2073815) B2073815
theorem B1554619 : Blo 1381510 1554619 := bstep (se 1 (by rfl) ⟨1165964, by rfl⟩ : syracuseStep 1554619 = 2331929) B2331929
theorem B1382587 : Blo 1381510 1382587 := bstep (se 1 (by rfl) ⟨1036940, by rfl⟩ : syracuseStep 1382587 = 2073881) B2073881
theorem B5249225 : Blo 1381510 5249225 := bstep (se 2 (by rfl) ⟨1968459, by rfl⟩ : syracuseStep 5249225 = 3936919) B3936919
theorem B1382663 : Blo 1381510 1382663 := bstep (se 1 (by rfl) ⟨1036997, by rfl⟩ : syracuseStep 1382663 = 2073995) B2073995
theorem B1382671 : Blo 1381510 1382671 := bstep (se 1 (by rfl) ⟨1037003, by rfl⟩ : syracuseStep 1382671 = 2074007) B2074007
theorem B5191969 : Blo 1381510 5191969 := bstep (se 2 (by rfl) ⟨1946988, by rfl⟩ : syracuseStep 5191969 = 3893977) B3893977
theorem B1382715 : Blo 1381510 1382715 := bstep (se 1 (by rfl) ⟨1037036, by rfl⟩ : syracuseStep 1382715 = 2074073) B2074073
theorem B3111227 : Blo 1381510 3111227 := bstep (se 1 (by rfl) ⟨2333420, by rfl⟩ : syracuseStep 3111227 = 4666841) B4666841
theorem B8403335 : Blo 1381510 8403335 := bstep (se 1 (by rfl) ⟨6302501, by rfl⟩ : syracuseStep 8403335 = 12605003) B12605003
theorem B14940551 : Blo 1381510 14940551 := bstep (se 1 (by rfl) ⟨11205413, by rfl⟩ : syracuseStep 14940551 = 22410827) B22410827
theorem B2333063 : Blo 1381510 2333063 := bstep (se 1 (by rfl) ⟨1749797, by rfl⟩ : syracuseStep 2333063 = 3499595) B3499595
theorem B1382791 : Blo 1381510 1382791 := bstep (se 1 (by rfl) ⟨1037093, by rfl⟩ : syracuseStep 1382791 = 2074187) B2074187
theorem B1382799 : Blo 1381510 1382799 := bstep (se 1 (by rfl) ⟨1037099, by rfl⟩ : syracuseStep 1382799 = 2074199) B2074199
theorem B3111353 : Blo 1381510 3111353 := bstep (se 2 (by rfl) ⟨1166757, by rfl⟩ : syracuseStep 3111353 = 2333515) B2333515
theorem B1382843 : Blo 1381510 1382843 := bstep (se 1 (by rfl) ⟨1037132, by rfl⟩ : syracuseStep 1382843 = 2074265) B2074265
theorem B1382919 : Blo 1381510 1382919 := bstep (se 1 (by rfl) ⟨1037189, by rfl⟩ : syracuseStep 1382919 = 2074379) B2074379
theorem B1382927 : Blo 1381510 1382927 := bstep (se 1 (by rfl) ⟨1037195, by rfl⟩ : syracuseStep 1382927 = 2074391) B2074391
theorem B1382971 : Blo 1381510 1382971 := bstep (se 1 (by rfl) ⟨1037228, by rfl⟩ : syracuseStep 1382971 = 2074457) B2074457
theorem B1383047 : Blo 1381510 1383047 := bstep (se 1 (by rfl) ⟨1037285, by rfl⟩ : syracuseStep 1383047 = 2074571) B2074571
theorem B1555087 : Blo 1381510 1555087 := bstep (se 1 (by rfl) ⟨1166315, by rfl⟩ : syracuseStep 1555087 = 2332631) B2332631
theorem B1383055 : Blo 1381510 1383055 := bstep (se 1 (by rfl) ⟨1037291, by rfl⟩ : syracuseStep 1383055 = 2074583) B2074583
theorem B3938969 : Blo 1381510 3938969 := bstep (se 2 (by rfl) ⟨1477113, by rfl⟩ : syracuseStep 3938969 = 2954227) B2954227
theorem B1383099 : Blo 1381510 1383099 := bstep (se 1 (by rfl) ⟨1037324, by rfl⟩ : syracuseStep 1383099 = 2074649) B2074649
theorem B8411849 : Blo 1381510 8411849 := bstep (se 2 (by rfl) ⟨3154443, by rfl⟩ : syracuseStep 8411849 = 6308887) B6308887
theorem B1383175 : Blo 1381510 1383175 := bstep (se 1 (by rfl) ⟨1037381, by rfl⟩ : syracuseStep 1383175 = 2074763) B2074763
theorem B3111695 : Blo 1381510 3111695 := bstep (se 1 (by rfl) ⟨2333771, by rfl⟩ : syracuseStep 3111695 = 4667543) B4667543
theorem B1383183 : Blo 1381510 1383183 := bstep (se 1 (by rfl) ⟨1037387, by rfl⟩ : syracuseStep 1383183 = 2074775) B2074775
theorem B3111713 : Blo 1381510 3111713 := bstep (se 2 (by rfl) ⟨1166892, by rfl⟩ : syracuseStep 3111713 = 2333785) B2333785
theorem B1383227 : Blo 1381510 1383227 := bstep (se 1 (by rfl) ⟨1037420, by rfl⟩ : syracuseStep 1383227 = 2074841) B2074841
theorem B11803481 : Blo 1381510 11803481 := bstep (se 2 (by rfl) ⟨4426305, by rfl⟩ : syracuseStep 11803481 = 8852611) B8852611
theorem B56736611 : Blo 1381510 56736611 := bstep (se 1 (by rfl) ⟨42552458, by rfl⟩ : syracuseStep 56736611 = 85104917) B85104917
theorem B2366327 : Blo 1381510 2366327 := bstep (se 1 (by rfl) ⟨1774745, by rfl⟩ : syracuseStep 2366327 = 3549491) B3549491
theorem B1383303 : Blo 1381510 1383303 := bstep (se 1 (by rfl) ⟨1037477, by rfl⟩ : syracuseStep 1383303 = 2074955) B2074955
theorem B1383311 : Blo 1381510 1383311 := bstep (se 1 (by rfl) ⟨1037483, by rfl⟩ : syracuseStep 1383311 = 2074967) B2074967
theorem B7871377 : Blo 1381510 7871377 := bstep (se 2 (by rfl) ⟨2951766, by rfl⟩ : syracuseStep 7871377 = 5903533) B5903533
theorem B6994835 : Blo 1381510 6994835 := bstep (se 1 (by rfl) ⟨5246126, by rfl⟩ : syracuseStep 6994835 = 10492253) B10492253
theorem B2243513 : Blo 1381510 2243513 := bstep (se 2 (by rfl) ⟨841317, by rfl⟩ : syracuseStep 2243513 = 1682635) B1682635
theorem B1383355 : Blo 1381510 1383355 := bstep (se 1 (by rfl) ⟨1037516, by rfl⟩ : syracuseStep 1383355 = 2075033) B2075033
theorem B1383431 : Blo 1381510 1383431 := bstep (se 1 (by rfl) ⟨1037573, by rfl⟩ : syracuseStep 1383431 = 2075147) B2075147
theorem B11811851 : Blo 1381510 11811851 := bstep (se 1 (by rfl) ⟨8858888, by rfl⟩ : syracuseStep 11811851 = 17717777) B17717777
theorem B2333711 : Blo 1381510 2333711 := bstep (se 1 (by rfl) ⟨1750283, by rfl⟩ : syracuseStep 2333711 = 3500567) B3500567
theorem B1383439 : Blo 1381510 1383439 := bstep (se 1 (by rfl) ⟨1037579, by rfl⟩ : syracuseStep 1383439 = 2075159) B2075159
theorem B3497003 : Blo 1381510 3497003 := bstep (se 1 (by rfl) ⟨2622752, by rfl⟩ : syracuseStep 3497003 = 5245505) B5245505
theorem B13294637 : Blo 1381510 13294637 := bstep (se 3 (by rfl) ⟨2492744, by rfl⟩ : syracuseStep 13294637 = 4985489) B4985489
theorem B1383483 : Blo 1381510 1383483 := bstep (se 1 (by rfl) ⟨1037612, by rfl⟩ : syracuseStep 1383483 = 2075225) B2075225
theorem B5250167 : Blo 1381510 5250167 := bstep (se 1 (by rfl) ⟨3937625, by rfl⟩ : syracuseStep 5250167 = 7875251) B7875251
theorem B3112055 : Blo 1381510 3112055 := bstep (se 1 (by rfl) ⟨2334041, by rfl⟩ : syracuseStep 3112055 = 4668083) B4668083
theorem B1555591 : Blo 1381510 1555591 := bstep (se 1 (by rfl) ⟨1166693, by rfl⟩ : syracuseStep 1555591 = 2333387) B2333387
theorem B2072567 : Blo 1381510 2072567 := bstep (se 1 (by rfl) ⟨1554425, by rfl⟩ : syracuseStep 2072567 = 3108851) B3108851
theorem B3112235 : Blo 1381510 3112235 := bstep (se 1 (by rfl) ⟨2334176, by rfl⟩ : syracuseStep 3112235 = 4668353) B4668353
theorem B14179643 : Blo 1381510 14179643 := bstep (se 1 (by rfl) ⟨10634732, by rfl⟩ : syracuseStep 14179643 = 21269465) B21269465
theorem B1555771 : Blo 1381510 1555771 := bstep (se 1 (by rfl) ⟨1166828, by rfl⟩ : syracuseStep 1555771 = 2333657) B2333657
theorem B4668731 : Blo 1381510 4668731 := bstep (se 1 (by rfl) ⟨3501548, by rfl⟩ : syracuseStep 4668731 = 7003097) B7003097
theorem B4431239 : Blo 1381510 4431239 := bstep (se 1 (by rfl) ⟨3323429, by rfl⟩ : syracuseStep 4431239 = 6646859) B6646859
theorem B13286915 : Blo 1381510 13286915 := bstep (se 1 (by rfl) ⟨9965186, by rfl⟩ : syracuseStep 13286915 = 19930373) B19930373
theorem B14188061 : Blo 1381510 14188061 := bstep (se 3 (by rfl) ⟨2660261, by rfl⟩ : syracuseStep 14188061 = 5320523) B5320523
theorem B2334251 : Blo 1381510 2334251 := bstep (se 1 (by rfl) ⟨1750688, by rfl⟩ : syracuseStep 2334251 = 3501377) B3501377
theorem B3366515 : Blo 1381510 3366515 := bstep (se 1 (by rfl) ⟨2524886, by rfl⟩ : syracuseStep 3366515 = 5049773) B5049773
theorem B3112595 : Blo 1381510 3112595 := bstep (se 1 (by rfl) ⟨2334446, by rfl⟩ : syracuseStep 3112595 = 4668893) B4668893
theorem B3112649 : Blo 1381510 3112649 := bstep (se 2 (by rfl) ⟨1167243, by rfl⟩ : syracuseStep 3112649 = 2334487) B2334487
theorem B2072327 : Blo 1381510 2072327 := bstep (se 1 (by rfl) ⟨1554245, by rfl⟩ : syracuseStep 2072327 = 3108491) B3108491
theorem B10493711 : Blo 1381510 10493711 := bstep (se 1 (by rfl) ⟨7870283, by rfl⟩ : syracuseStep 10493711 = 15740567) B15740567
theorem B1556239 : Blo 1381510 1556239 := bstep (se 1 (by rfl) ⟨1167179, by rfl⟩ : syracuseStep 1556239 = 2334359) B2334359
theorem B4669217 : Blo 1381510 4669217 := bstep (se 2 (by rfl) ⟨1750956, by rfl⟩ : syracuseStep 4669217 = 3501913) B3501913
theorem B2072363 : Blo 1381510 2072363 := bstep (se 1 (by rfl) ⟨1554272, by rfl⟩ : syracuseStep 2072363 = 3108545) B3108545
theorem B44850995 : Blo 1381510 44850995 := bstep (se 1 (by rfl) ⟨33638246, by rfl⟩ : syracuseStep 44850995 = 67276493) B67276493
theorem B2072393 : Blo 1381510 2072393 := bstep (se 2 (by rfl) ⟨777147, by rfl⟩ : syracuseStep 2072393 = 1554295) B1554295
theorem B3497843 : Blo 1381510 3497843 := bstep (se 1 (by rfl) ⟨2623382, by rfl⟩ : syracuseStep 3497843 = 5246765) B5246765
theorem B3497863 : Blo 1381510 3497863 := bstep (se 1 (by rfl) ⟨2623397, by rfl⟩ : syracuseStep 3497863 = 5246795) B5246795
theorem B2490259 : Blo 1381510 2490259 := bstep (se 1 (by rfl) ⟨1867694, by rfl⟩ : syracuseStep 2490259 = 3735389) B3735389
theorem B2334649 : Blo 1381510 2334649 := bstep (se 2 (by rfl) ⟨875493, by rfl⟩ : syracuseStep 2334649 = 1750987) B1750987
theorem B2072507 : Blo 1381510 2072507 := bstep (se 1 (by rfl) ⟨1554380, by rfl⟩ : syracuseStep 2072507 = 3108761) B3108761
theorem B2072585 : Blo 1381510 2072585 := bstep (se 2 (by rfl) ⟨777219, by rfl⟩ : syracuseStep 2072585 = 1554439) B1554439
theorem B2695207 : Blo 1381510 2695207 := bstep (se 1 (by rfl) ⟨2021405, by rfl⟩ : syracuseStep 2695207 = 4042811) B4042811
theorem B2072615 : Blo 1381510 2072615 := bstep (se 1 (by rfl) ⟨1554461, by rfl⟩ : syracuseStep 2072615 = 3108923) B3108923
theorem B2072699 : Blo 1381510 2072699 := bstep (se 1 (by rfl) ⟨1554524, by rfl⟩ : syracuseStep 2072699 = 3109049) B3109049
theorem B2072825 : Blo 1381510 2072825 := bstep (se 2 (by rfl) ⟨777309, by rfl⟩ : syracuseStep 2072825 = 1554619) B1554619
theorem B17711419 : Blo 1381510 17711419 := bstep (se 1 (by rfl) ⟨13283564, by rfl⟩ : syracuseStep 17711419 = 26567129) B26567129
theorem B2072927 : Blo 1381510 2072927 := bstep (se 1 (by rfl) ⟨1554695, by rfl⟩ : syracuseStep 2072927 = 3109391) B3109391
theorem B2072939 : Blo 1381510 2072939 := bstep (se 1 (by rfl) ⟨1554704, by rfl⟩ : syracuseStep 2072939 = 3109409) B3109409
theorem B6922625 : Blo 1381510 6922625 := bstep (se 2 (by rfl) ⟨2595984, by rfl⟩ : syracuseStep 6922625 = 5191969) B5191969
theorem B2073167 : Blo 1381510 2073167 := bstep (se 1 (by rfl) ⟨1554875, by rfl⟩ : syracuseStep 2073167 = 3109751) B3109751
theorem B22413941 : Blo 1381510 22413941 := bstep (se 5 (by rfl) ⟨1050653, by rfl⟩ : syracuseStep 22413941 = 2101307) B2101307
theorem B59794037 : Blo 1381510 59794037 := bstep (se 5 (by rfl) ⟨2802845, by rfl⟩ : syracuseStep 59794037 = 5605691) B5605691
theorem B2073287 : Blo 1381510 2073287 := bstep (se 1 (by rfl) ⟨1554965, by rfl⟩ : syracuseStep 2073287 = 3109931) B3109931
theorem B2073449 : Blo 1381510 2073449 := bstep (se 2 (by rfl) ⟨777543, by rfl⟩ : syracuseStep 2073449 = 1555087) B1555087
theorem B15967151 : Blo 1381510 15967151 := bstep (se 1 (by rfl) ⟨11975363, by rfl⟩ : syracuseStep 15967151 = 23950727) B23950727
theorem B2073527 : Blo 1381510 2073527 := bstep (se 1 (by rfl) ⟨1555145, by rfl⟩ : syracuseStep 2073527 = 3110291) B3110291
theorem B2073563 : Blo 1381510 2073563 := bstep (se 1 (by rfl) ⟨1555172, by rfl⟩ : syracuseStep 2073563 = 3110345) B3110345
theorem B5252111 : Blo 1381510 5252111 := bstep (se 1 (by rfl) ⟨3939083, by rfl⟩ : syracuseStep 5252111 = 7878167) B7878167
theorem B7095347 : Blo 1381510 7095347 := bstep (se 1 (by rfl) ⟨5321510, by rfl⟩ : syracuseStep 7095347 = 10643021) B10643021
theorem B10495169 : Blo 1381510 10495169 := bstep (se 2 (by rfl) ⟨3935688, by rfl⟩ : syracuseStep 10495169 = 7871377) B7871377
theorem B2622881 : Blo 1381510 2622881 := bstep (se 2 (by rfl) ⟨983580, by rfl⟩ : syracuseStep 2622881 = 1967161) B1967161
theorem B2074031 : Blo 1381510 2074031 := bstep (se 1 (by rfl) ⟨1555523, by rfl⟩ : syracuseStep 2074031 = 3111047) B3111047
theorem B2491823 : Blo 1381510 2491823 := bstep (se 1 (by rfl) ⟨1868867, by rfl⟩ : syracuseStep 2491823 = 3737735) B3737735
theorem B3499483 : Blo 1381510 3499483 := bstep (se 1 (by rfl) ⟨2624612, by rfl⟩ : syracuseStep 3499483 = 5249225) B5249225
theorem B2074121 : Blo 1381510 2074121 := bstep (se 2 (by rfl) ⟨777795, by rfl⟩ : syracuseStep 2074121 = 1555591) B1555591
theorem B2074151 : Blo 1381510 2074151 := bstep (se 1 (by rfl) ⟨1555613, by rfl⟩ : syracuseStep 2074151 = 3111227) B3111227
theorem B2623033 : Blo 1381510 2623033 := bstep (se 2 (by rfl) ⟨983637, by rfl⟩ : syracuseStep 2623033 = 1967275) B1967275
theorem B2074235 : Blo 1381510 2074235 := bstep (se 1 (by rfl) ⟨1555676, by rfl⟩ : syracuseStep 2074235 = 3111353) B3111353
theorem B3737303 : Blo 1381510 3737303 := bstep (se 1 (by rfl) ⟨2802977, by rfl⟩ : syracuseStep 3737303 = 5605955) B5605955
theorem B10503917 : Blo 1381510 10503917 := bstep (se 3 (by rfl) ⟨1969484, by rfl⟩ : syracuseStep 10503917 = 3938969) B3938969
theorem B2074361 : Blo 1381510 2074361 := bstep (se 2 (by rfl) ⟨777885, by rfl⟩ : syracuseStep 2074361 = 1555771) B1555771
theorem B2074463 : Blo 1381510 2074463 := bstep (se 1 (by rfl) ⟨1555847, by rfl⟩ : syracuseStep 2074463 = 3111695) B3111695
theorem B2492255 : Blo 1381510 2492255 := bstep (se 1 (by rfl) ⟨1869191, by rfl⟩ : syracuseStep 2492255 = 3738383) B3738383
theorem B2623337 : Blo 1381510 2623337 := bstep (se 2 (by rfl) ⟨983751, by rfl⟩ : syracuseStep 2623337 = 1967503) B1967503
theorem B2074475 : Blo 1381510 2074475 := bstep (se 1 (by rfl) ⟨1555856, by rfl⟩ : syracuseStep 2074475 = 3111713) B3111713
theorem B37824407 : Blo 1381510 37824407 := bstep (se 1 (by rfl) ⟨28368305, by rfl⟩ : syracuseStep 37824407 = 56736611) B56736611
theorem B9963425 : Blo 1381510 9963425 := bstep (se 2 (by rfl) ⟨3736284, by rfl⟩ : syracuseStep 9963425 = 7472569) B7472569
theorem B4663223 : Blo 1381510 4663223 := bstep (se 1 (by rfl) ⟨3497417, by rfl⟩ : syracuseStep 4663223 = 6994835) B6994835
theorem B7874567 : Blo 1381510 7874567 := bstep (se 1 (by rfl) ⟨5905925, by rfl⟩ : syracuseStep 7874567 = 11811851) B11811851
theorem B3500111 : Blo 1381510 3500111 := bstep (se 1 (by rfl) ⟨2625083, by rfl⟩ : syracuseStep 3500111 = 5250167) B5250167
theorem B2074703 : Blo 1381510 2074703 := bstep (se 1 (by rfl) ⟨1556027, by rfl⟩ : syracuseStep 2074703 = 3112055) B3112055
theorem B2074823 : Blo 1381510 2074823 := bstep (se 1 (by rfl) ⟨1556117, by rfl⟩ : syracuseStep 2074823 = 3112235) B3112235
theorem B8857943 : Blo 1381510 8857943 := bstep (se 1 (by rfl) ⟨6643457, by rfl⟩ : syracuseStep 8857943 = 13286915) B13286915
theorem B2074985 : Blo 1381510 2074985 := bstep (se 2 (by rfl) ⟨778119, by rfl⟩ : syracuseStep 2074985 = 1556239) B1556239
theorem B2214287 : Blo 1381510 2214287 := bstep (se 1 (by rfl) ⟨1660715, by rfl⟩ : syracuseStep 2214287 = 3321431) B3321431
theorem B2075063 : Blo 1381510 2075063 := bstep (se 1 (by rfl) ⟨1556297, by rfl⟩ : syracuseStep 2075063 = 3112595) B3112595
theorem B14191051 : Blo 1381510 14191051 := bstep (se 1 (by rfl) ⟨10643288, by rfl⟩ : syracuseStep 14191051 = 21286577) B21286577
theorem B2075099 : Blo 1381510 2075099 := bstep (se 1 (by rfl) ⟨1556324, by rfl⟩ : syracuseStep 2075099 = 3112649) B3112649
theorem B4663817 : Blo 1381510 4663817 := bstep (se 2 (by rfl) ⟨1748931, by rfl⟩ : syracuseStep 4663817 = 3497863) B3497863
theorem B2492947 : Blo 1381510 2492947 := bstep (se 1 (by rfl) ⟨1869710, by rfl⟩ : syracuseStep 2492947 = 3739421) B3739421
theorem B3320345 : Blo 1381510 3320345 := bstep (se 2 (by rfl) ⟨1245129, by rfl⟩ : syracuseStep 3320345 = 2490259) B2490259
theorem B6998561 : Blo 1381510 6998561 := bstep (se 2 (by rfl) ⟨2624460, by rfl⟩ : syracuseStep 6998561 = 5248921) B5248921
theorem B10504889 : Blo 1381510 10504889 := bstep (se 2 (by rfl) ⟨3939333, by rfl⟩ : syracuseStep 10504889 = 7878667) B7878667
theorem B3500759 : Blo 1381510 3500759 := bstep (se 1 (by rfl) ⟨2625569, by rfl⟩ : syracuseStep 3500759 = 5251139) B5251139
theorem B6646703 : Blo 1381510 6646703 := bstep (se 1 (by rfl) ⟨4985027, by rfl⟩ : syracuseStep 6646703 = 9970055) B9970055
theorem B90917963 : Blo 1381510 90917963 := bstep (se 1 (by rfl) ⟨68188472, by rfl⟩ : syracuseStep 90917963 = 136376945) B136376945
theorem B1821895 : Blo 1381510 1821895 := bstep (se 1 (by rfl) ⟨1366421, by rfl⟩ : syracuseStep 1821895 = 2732843) B2732843
theorem B8858969 : Blo 1381510 8858969 := bstep (se 2 (by rfl) ⟨3322113, by rfl⟩ : syracuseStep 8858969 = 6644227) B6644227
theorem B4664681 : Blo 1381510 4664681 := bstep (se 2 (by rfl) ⟨1749255, by rfl⟩ : syracuseStep 4664681 = 3498511) B3498511
theorem B2952553 : Blo 1381510 2952553 := bstep (se 2 (by rfl) ⟨1107207, by rfl⟩ : syracuseStep 2952553 = 2214415) B2214415
theorem B10235261 : Blo 1381510 10235261 := bstep (se 3 (by rfl) ⟨1919111, by rfl⟩ : syracuseStep 10235261 = 3838223) B3838223
theorem B5320079 : Blo 1381510 5320079 := bstep (se 1 (by rfl) ⟨3990059, by rfl⟩ : syracuseStep 5320079 = 7980119) B7980119
theorem B3321353 : Blo 1381510 3321353 := bstep (se 2 (by rfl) ⟨1245507, by rfl⟩ : syracuseStep 3321353 = 2491015) B2491015
theorem B1707643 : Blo 1381510 1707643 := bstep (se 1 (by rfl) ⟨1280732, by rfl⟩ : syracuseStep 1707643 = 2561465) B2561465
theorem B10505861 : Blo 1381510 10505861 := bstep (se 4 (by rfl) ⟨984924, by rfl⟩ : syracuseStep 10505861 = 1969849) B1969849
theorem B39841469 : Blo 1381510 39841469 := bstep (se 3 (by rfl) ⟨7470275, by rfl⟩ : syracuseStep 39841469 = 14940551) B14940551
theorem B3108563 : Blo 1381510 3108563 := bstep (se 1 (by rfl) ⟨2331422, by rfl⟩ : syracuseStep 3108563 = 4662845) B4662845
theorem B7868279 : Blo 1381510 7868279 := bstep (se 1 (by rfl) ⟨5901209, by rfl⟩ : syracuseStep 7868279 = 11802419) B11802419
theorem B2625463 : Blo 1381510 2625463 := bstep (se 1 (by rfl) ⟨1969097, by rfl⟩ : syracuseStep 2625463 = 3938195) B3938195
theorem B4665275 : Blo 1381510 4665275 := bstep (se 1 (by rfl) ⟨3498956, by rfl⟩ : syracuseStep 4665275 = 6997913) B6997913
theorem B5246977 : Blo 1381510 5246977 := bstep (se 2 (by rfl) ⟨1967616, by rfl⟩ : syracuseStep 5246977 = 3935233) B3935233
theorem B4730899 : Blo 1381510 4730899 := bstep (se 1 (by rfl) ⟨3548174, by rfl⟩ : syracuseStep 4730899 = 7096349) B7096349
theorem B10498085 : Blo 1381510 10498085 := bstep (se 4 (by rfl) ⟨984195, by rfl⟩ : syracuseStep 10498085 = 1968391) B1968391
theorem B14954827 : Blo 1381510 14954827 := bstep (se 1 (by rfl) ⟨11216120, by rfl⟩ : syracuseStep 14954827 = 22432241) B22432241
theorem B5607899 : Blo 1381510 5607899 := bstep (se 1 (by rfl) ⟨4205924, by rfl⟩ : syracuseStep 5607899 = 8411849) B8411849
theorem B7868987 : Blo 1381510 7868987 := bstep (se 1 (by rfl) ⟨5901740, by rfl⟩ : syracuseStep 7868987 = 11803481) B11803481
theorem B1577551 : Blo 1381510 1577551 := bstep (se 1 (by rfl) ⟨1183163, by rfl⟩ : syracuseStep 1577551 = 2366327) B2366327
theorem B1495675 : Blo 1381510 1495675 := bstep (se 1 (by rfl) ⟨1121756, by rfl⟩ : syracuseStep 1495675 = 2243513) B2243513
theorem B3109499 : Blo 1381510 3109499 := bstep (se 1 (by rfl) ⟨2332124, by rfl⟩ : syracuseStep 3109499 = 4664249) B4664249
theorem B2331335 : Blo 1381510 2331335 := bstep (se 1 (by rfl) ⟨1748501, by rfl⟩ : syracuseStep 2331335 = 3497003) B3497003
theorem B3109625 : Blo 1381510 3109625 := bstep (se 2 (by rfl) ⟨1166109, by rfl⟩ : syracuseStep 3109625 = 2332219) B2332219
theorem B5247737 : Blo 1381510 5247737 := bstep (se 2 (by rfl) ⟨1967901, by rfl⟩ : syracuseStep 5247737 = 3935803) B3935803
theorem B9966365 : Blo 1381510 9966365 := bstep (se 3 (by rfl) ⟨1868693, by rfl⟩ : syracuseStep 9966365 = 3737387) B3737387
theorem B2331497 : Blo 1381510 2331497 := bstep (se 2 (by rfl) ⟨874311, by rfl⟩ : syracuseStep 2331497 = 1748623) B1748623
theorem B7877483 : Blo 1381510 7877483 := bstep (se 1 (by rfl) ⟨5908112, by rfl⟩ : syracuseStep 7877483 = 11816225) B11816225
theorem B2954159 : Blo 1381510 2954159 := bstep (se 1 (by rfl) ⟨2215619, by rfl⟩ : syracuseStep 2954159 = 4431239) B4431239
theorem B15152129 : Blo 1381510 15152129 := bstep (se 2 (by rfl) ⟨5682048, by rfl⟩ : syracuseStep 15152129 = 11364097) B11364097
theorem B3109895 : Blo 1381510 3109895 := bstep (se 1 (by rfl) ⟨2332421, by rfl⟩ : syracuseStep 3109895 = 4664843) B4664843
theorem B9458707 : Blo 1381510 9458707 := bstep (se 1 (by rfl) ⟨7094030, by rfl⟩ : syracuseStep 9458707 = 14188061) B14188061
theorem B3109967 : Blo 1381510 3109967 := bstep (se 1 (by rfl) ⟨2332475, by rfl⟩ : syracuseStep 3109967 = 4664951) B4664951
theorem B1381551 : Blo 1381510 1381551 := bstep (se 1 (by rfl) ⟨1036163, by rfl⟩ : syracuseStep 1381551 = 2072327) B2072327
theorem B1381575 : Blo 1381510 1381575 := bstep (se 1 (by rfl) ⟨1036181, by rfl⟩ : syracuseStep 1381575 = 2072363) B2072363
theorem B1381595 : Blo 1381510 1381595 := bstep (se 1 (by rfl) ⟨1036196, by rfl⟩ : syracuseStep 1381595 = 2072393) B2072393
theorem B2331895 : Blo 1381510 2331895 := bstep (se 1 (by rfl) ⟨1748921, by rfl⟩ : syracuseStep 2331895 = 3497843) B3497843
theorem B1381671 : Blo 1381510 1381671 := bstep (se 1 (by rfl) ⟨1036253, by rfl⟩ : syracuseStep 1381671 = 2072507) B2072507
theorem B1381711 : Blo 1381510 1381711 := bstep (se 1 (by rfl) ⟨1036283, by rfl⟩ : syracuseStep 1381711 = 2072567) B2072567
theorem B1381727 : Blo 1381510 1381727 := bstep (se 1 (by rfl) ⟨1036295, by rfl⟩ : syracuseStep 1381727 = 2072591) B2072591
theorem B1381755 : Blo 1381510 1381755 := bstep (se 1 (by rfl) ⟨1036316, by rfl⟩ : syracuseStep 1381755 = 2072633) B2072633
theorem B19920275 : Blo 1381510 19920275 := bstep (se 1 (by rfl) ⟨14940206, by rfl⟩ : syracuseStep 19920275 = 29880413) B29880413
theorem B1381807 : Blo 1381510 1381807 := bstep (se 1 (by rfl) ⟨1036355, by rfl⟩ : syracuseStep 1381807 = 2072711) B2072711
theorem B2332091 : Blo 1381510 2332091 := bstep (se 1 (by rfl) ⟨1749068, by rfl⟩ : syracuseStep 2332091 = 3498137) B3498137
theorem B1381831 : Blo 1381510 1381831 := bstep (se 1 (by rfl) ⟨1036373, by rfl⟩ : syracuseStep 1381831 = 2072747) B2072747
theorem B1381851 : Blo 1381510 1381851 := bstep (se 1 (by rfl) ⟨1036388, by rfl⟩ : syracuseStep 1381851 = 2072777) B2072777
theorem B3110363 : Blo 1381510 3110363 := bstep (se 1 (by rfl) ⟨2332772, by rfl⟩ : syracuseStep 3110363 = 4665545) B4665545
theorem B9582119 : Blo 1381510 9582119 := bstep (se 1 (by rfl) ⟨7186589, by rfl⟩ : syracuseStep 9582119 = 14373179) B14373179
theorem B1381927 : Blo 1381510 1381927 := bstep (se 1 (by rfl) ⟨1036445, by rfl⟩ : syracuseStep 1381927 = 2072891) B2072891
theorem B2332199 : Blo 1381510 2332199 := bstep (se 1 (by rfl) ⟨1749149, by rfl⟩ : syracuseStep 2332199 = 3498299) B3498299
theorem B7001639 : Blo 1381510 7001639 := bstep (se 1 (by rfl) ⟨5251229, by rfl⟩ : syracuseStep 7001639 = 10502459) B10502459
theorem B1750567 : Blo 1381510 1750567 := bstep (se 1 (by rfl) ⟨1312925, by rfl⟩ : syracuseStep 1750567 = 2625851) B2625851
theorem B1381967 : Blo 1381510 1381967 := bstep (se 1 (by rfl) ⟨1036475, by rfl⟩ : syracuseStep 1381967 = 2072951) B2072951
theorem B1381983 : Blo 1381510 1381983 := bstep (se 1 (by rfl) ⟨1036487, by rfl⟩ : syracuseStep 1381983 = 2072975) B2072975
theorem B1382011 : Blo 1381510 1382011 := bstep (se 1 (by rfl) ⟨1036508, by rfl⟩ : syracuseStep 1382011 = 2073017) B2073017
theorem B4667003 : Blo 1381510 4667003 := bstep (se 1 (by rfl) ⟨3500252, by rfl⟩ : syracuseStep 4667003 = 7000505) B7000505
theorem B1382063 : Blo 1381510 1382063 := bstep (se 1 (by rfl) ⟨1036547, by rfl⟩ : syracuseStep 1382063 = 2073095) B2073095
theorem B1382087 : Blo 1381510 1382087 := bstep (se 1 (by rfl) ⟨1036565, by rfl⟩ : syracuseStep 1382087 = 2073131) B2073131
theorem B1382107 : Blo 1381510 1382107 := bstep (se 1 (by rfl) ⟨1036580, by rfl⟩ : syracuseStep 1382107 = 2073161) B2073161
theorem B4667165 : Blo 1381510 4667165 := bstep (se 3 (by rfl) ⟨875093, by rfl⟩ : syracuseStep 4667165 = 1750187) B1750187
theorem B1382183 : Blo 1381510 1382183 := bstep (se 1 (by rfl) ⟨1036637, by rfl⟩ : syracuseStep 1382183 = 2073275) B2073275
theorem B22427435 : Blo 1381510 22427435 := bstep (se 1 (by rfl) ⟨16820576, by rfl⟩ : syracuseStep 22427435 = 33641153) B33641153
theorem B2332489 : Blo 1381510 2332489 := bstep (se 2 (by rfl) ⟨874683, by rfl⟩ : syracuseStep 2332489 = 1749367) B1749367
theorem B1382223 : Blo 1381510 1382223 := bstep (se 1 (by rfl) ⟨1036667, by rfl⟩ : syracuseStep 1382223 = 2073335) B2073335
theorem B1382239 : Blo 1381510 1382239 := bstep (se 1 (by rfl) ⟨1036679, by rfl⟩ : syracuseStep 1382239 = 2073359) B2073359
theorem B2332523 : Blo 1381510 2332523 := bstep (se 1 (by rfl) ⟨1749392, by rfl⟩ : syracuseStep 2332523 = 3498785) B3498785
theorem B1750891 : Blo 1381510 1750891 := bstep (se 1 (by rfl) ⟨1313168, by rfl⟩ : syracuseStep 1750891 = 2626337) B2626337
theorem B10491767 : Blo 1381510 10491767 := bstep (se 1 (by rfl) ⟨7868825, by rfl⟩ : syracuseStep 10491767 = 15737651) B15737651
theorem B1382267 : Blo 1381510 1382267 := bstep (se 1 (by rfl) ⟨1036700, by rfl⟩ : syracuseStep 1382267 = 2073401) B2073401
theorem B1382319 : Blo 1381510 1382319 := bstep (se 1 (by rfl) ⟨1036739, by rfl⟩ : syracuseStep 1382319 = 2073479) B2073479
theorem B3110831 : Blo 1381510 3110831 := bstep (se 1 (by rfl) ⟨2333123, by rfl⟩ : syracuseStep 3110831 = 4666247) B4666247
theorem B8861633 : Blo 1381510 8861633 := bstep (se 2 (by rfl) ⟨3323112, by rfl⟩ : syracuseStep 8861633 = 6646225) B6646225
theorem B1382343 : Blo 1381510 1382343 := bstep (se 1 (by rfl) ⟨1036757, by rfl⟩ : syracuseStep 1382343 = 2073515) B2073515
theorem B9459665 : Blo 1381510 9459665 := bstep (se 2 (by rfl) ⟨3547374, by rfl⟩ : syracuseStep 9459665 = 7094749) B7094749
theorem B1382363 : Blo 1381510 1382363 := bstep (se 1 (by rfl) ⟨1036772, by rfl⟩ : syracuseStep 1382363 = 2073545) B2073545
theorem B7477285 : Blo 1381510 7477285 := bstep (se 4 (by rfl) ⟨700995, by rfl⟩ : syracuseStep 7477285 = 1401991) B1401991
theorem B1382439 : Blo 1381510 1382439 := bstep (se 1 (by rfl) ⟨1036829, by rfl⟩ : syracuseStep 1382439 = 2073659) B2073659
theorem B1554511 : Blo 1381510 1554511 := bstep (se 1 (by rfl) ⟨1165883, by rfl⟩ : syracuseStep 1554511 = 2331767) B2331767
theorem B1382479 : Blo 1381510 1382479 := bstep (se 1 (by rfl) ⟨1036859, by rfl⟩ : syracuseStep 1382479 = 2073719) B2073719
theorem B1382495 : Blo 1381510 1382495 := bstep (se 1 (by rfl) ⟨1036871, by rfl⟩ : syracuseStep 1382495 = 2073743) B2073743
theorem B1382523 : Blo 1381510 1382523 := bstep (se 1 (by rfl) ⟨1036892, by rfl⟩ : syracuseStep 1382523 = 2073785) B2073785
theorem B5249195 : Blo 1381510 5249195 := bstep (se 1 (by rfl) ⟨3936896, by rfl⟩ : syracuseStep 5249195 = 7873793) B7873793
theorem B3111083 : Blo 1381510 3111083 := bstep (se 1 (by rfl) ⟨2333312, by rfl⟩ : syracuseStep 3111083 = 4666625) B4666625
theorem B1382575 : Blo 1381510 1382575 := bstep (se 1 (by rfl) ⟨1036931, by rfl⟩ : syracuseStep 1382575 = 2073863) B2073863
theorem B1382599 : Blo 1381510 1382599 := bstep (se 1 (by rfl) ⟨1036949, by rfl⟩ : syracuseStep 1382599 = 2073899) B2073899
theorem B1382619 : Blo 1381510 1382619 := bstep (se 1 (by rfl) ⟨1036964, by rfl⟩ : syracuseStep 1382619 = 2073929) B2073929
theorem B2332921 : Blo 1381510 2332921 := bstep (se 2 (by rfl) ⟨874845, by rfl⟩ : syracuseStep 2332921 = 1749691) B1749691
theorem B6994187 : Blo 1381510 6994187 := bstep (se 1 (by rfl) ⟨5245640, by rfl⟩ : syracuseStep 6994187 = 10491281) B10491281
theorem B1382695 : Blo 1381510 1382695 := bstep (se 1 (by rfl) ⟨1037021, by rfl⟩ : syracuseStep 1382695 = 2074043) B2074043
theorem B1382735 : Blo 1381510 1382735 := bstep (se 1 (by rfl) ⟨1037051, by rfl⟩ : syracuseStep 1382735 = 2074103) B2074103
theorem B1382751 : Blo 1381510 1382751 := bstep (se 1 (by rfl) ⟨1037063, by rfl⟩ : syracuseStep 1382751 = 2074127) B2074127
theorem B1382779 : Blo 1381510 1382779 := bstep (se 1 (by rfl) ⟨1037084, by rfl⟩ : syracuseStep 1382779 = 2074169) B2074169
theorem B3987841 : Blo 1381510 3987841 := bstep (se 2 (by rfl) ⟨1495440, by rfl⟩ : syracuseStep 3987841 = 2990881) B2990881
theorem B1382831 : Blo 1381510 1382831 := bstep (se 1 (by rfl) ⟨1037123, by rfl⟩ : syracuseStep 1382831 = 2074247) B2074247
theorem B1382855 : Blo 1381510 1382855 := bstep (se 1 (by rfl) ⟨1037141, by rfl⟩ : syracuseStep 1382855 = 2074283) B2074283
theorem B1554907 : Blo 1381510 1554907 := bstep (se 1 (by rfl) ⟨1166180, by rfl⟩ : syracuseStep 1554907 = 2332361) B2332361
theorem B1382875 : Blo 1381510 1382875 := bstep (se 1 (by rfl) ⟨1037156, by rfl⟩ : syracuseStep 1382875 = 2074313) B2074313
theorem B4667867 : Blo 1381510 4667867 := bstep (se 1 (by rfl) ⟨3500900, by rfl⟩ : syracuseStep 4667867 = 7001801) B7001801
theorem B2333191 : Blo 1381510 2333191 := bstep (se 1 (by rfl) ⟨1749893, by rfl⟩ : syracuseStep 2333191 = 3499787) B3499787
theorem B7879193 : Blo 1381510 7879193 := bstep (se 2 (by rfl) ⟨2954697, by rfl⟩ : syracuseStep 7879193 = 5909395) B5909395
theorem B1382951 : Blo 1381510 1382951 := bstep (se 1 (by rfl) ⟨1037213, by rfl⟩ : syracuseStep 1382951 = 2074427) B2074427
theorem B1382991 : Blo 1381510 1382991 := bstep (se 1 (by rfl) ⟨1037243, by rfl⟩ : syracuseStep 1382991 = 2074487) B2074487
theorem B1383007 : Blo 1381510 1383007 := bstep (se 1 (by rfl) ⟨1037255, by rfl⟩ : syracuseStep 1383007 = 2074511) B2074511
theorem B1383035 : Blo 1381510 1383035 := bstep (se 1 (by rfl) ⟨1037276, by rfl⟩ : syracuseStep 1383035 = 2074553) B2074553
theorem B1383087 : Blo 1381510 1383087 := bstep (se 1 (by rfl) ⟨1037315, by rfl⟩ : syracuseStep 1383087 = 2074631) B2074631
theorem B3111623 : Blo 1381510 3111623 := bstep (se 1 (by rfl) ⟨2333717, by rfl⟩ : syracuseStep 3111623 = 4667435) B4667435
theorem B1383111 : Blo 1381510 1383111 := bstep (se 1 (by rfl) ⟨1037333, by rfl⟩ : syracuseStep 1383111 = 2074667) B2074667
theorem B1383131 : Blo 1381510 1383131 := bstep (se 1 (by rfl) ⟨1037348, by rfl⟩ : syracuseStep 1383131 = 2074697) B2074697
theorem B1383207 : Blo 1381510 1383207 := bstep (se 1 (by rfl) ⟨1037405, by rfl⟩ : syracuseStep 1383207 = 2074811) B2074811
theorem B1383247 : Blo 1381510 1383247 := bstep (se 1 (by rfl) ⟨1037435, by rfl⟩ : syracuseStep 1383247 = 2074871) B2074871
theorem B1383263 : Blo 1381510 1383263 := bstep (se 1 (by rfl) ⟨1037447, by rfl⟩ : syracuseStep 1383263 = 2074895) B2074895
theorem B8854379 : Blo 1381510 8854379 := bstep (se 1 (by rfl) ⟨6640784, by rfl⟩ : syracuseStep 8854379 = 13281569) B13281569
theorem B1383291 : Blo 1381510 1383291 := bstep (se 1 (by rfl) ⟨1037468, by rfl⟩ : syracuseStep 1383291 = 2074937) B2074937
theorem B5602223 : Blo 1381510 5602223 := bstep (se 1 (by rfl) ⟨4201667, by rfl⟩ : syracuseStep 5602223 = 8403335) B8403335
theorem B1555375 : Blo 1381510 1555375 := bstep (se 1 (by rfl) ⟨1166531, by rfl⟩ : syracuseStep 1555375 = 2333063) B2333063
theorem B1383343 : Blo 1381510 1383343 := bstep (se 1 (by rfl) ⟨1037507, by rfl⟩ : syracuseStep 1383343 = 2075015) B2075015
theorem B2333623 : Blo 1381510 2333623 := bstep (se 1 (by rfl) ⟨1750217, by rfl⟩ : syracuseStep 2333623 = 3500435) B3500435
theorem B1383367 : Blo 1381510 1383367 := bstep (se 1 (by rfl) ⟨1037525, by rfl⟩ : syracuseStep 1383367 = 2075051) B2075051
theorem B1383387 : Blo 1381510 1383387 := bstep (se 1 (by rfl) ⟨1037540, by rfl⟩ : syracuseStep 1383387 = 2075081) B2075081
theorem B4430855 : Blo 1381510 4430855 := bstep (se 1 (by rfl) ⟨3323141, by rfl⟩ : syracuseStep 4430855 = 6646283) B6646283
theorem B1383463 : Blo 1381510 1383463 := bstep (se 1 (by rfl) ⟨1037597, by rfl⟩ : syracuseStep 1383463 = 2075195) B2075195
theorem B1383503 : Blo 1381510 1383503 := bstep (se 1 (by rfl) ⟨1037627, by rfl⟩ : syracuseStep 1383503 = 2075255) B2075255
theorem B2333819 : Blo 1381510 2333819 := bstep (se 1 (by rfl) ⟨1750364, by rfl⟩ : syracuseStep 2333819 = 3500729) B3500729
theorem B6732953 : Blo 1381510 6732953 := bstep (se 2 (by rfl) ⟨2524857, by rfl⟩ : syracuseStep 6732953 = 5049715) B5049715
theorem B4668569 : Blo 1381510 4668569 := bstep (se 2 (by rfl) ⟨1750713, by rfl⟩ : syracuseStep 4668569 = 3501427) B3501427
theorem B5250365 : Blo 1381510 5250365 := bstep (se 3 (by rfl) ⟨984443, by rfl⟩ : syracuseStep 5250365 = 1968887) B1968887
theorem B1555807 : Blo 1381510 1555807 := bstep (se 1 (by rfl) ⟨1166855, by rfl⟩ : syracuseStep 1555807 = 2333711) B2333711
theorem B8863091 : Blo 1381510 8863091 := bstep (se 1 (by rfl) ⟨6647318, by rfl⟩ : syracuseStep 8863091 = 13294637) B13294637
theorem B10640803 : Blo 1381510 10640803 := bstep (se 1 (by rfl) ⟨7980602, by rfl⟩ : syracuseStep 10640803 = 15961205) B15961205
theorem B2334217 : Blo 1381510 2334217 := bstep (se 2 (by rfl) ⟨875331, by rfl⟩ : syracuseStep 2334217 = 1750663) B1750663
theorem B9453095 : Blo 1381510 9453095 := bstep (se 1 (by rfl) ⟨7089821, by rfl⟩ : syracuseStep 9453095 = 14179643) B14179643
theorem B3112487 : Blo 1381510 3112487 := bstep (se 1 (by rfl) ⟨2334365, by rfl⟩ : syracuseStep 3112487 = 4668731) B4668731
theorem B7003745 : Blo 1381510 7003745 := bstep (se 2 (by rfl) ⟨2626404, by rfl⟩ : syracuseStep 7003745 = 5252809) B5252809
theorem B5250683 : Blo 1381510 5250683 := bstep (se 1 (by rfl) ⟨3938012, by rfl⟩ : syracuseStep 5250683 = 7876025) B7876025
theorem B2334379 : Blo 1381510 2334379 := bstep (se 1 (by rfl) ⟨1750784, by rfl⟩ : syracuseStep 2334379 = 3501569) B3501569
theorem B6995645 : Blo 1381510 6995645 := bstep (se 3 (by rfl) ⟨1311683, by rfl⟩ : syracuseStep 6995645 = 2623367) B2623367
theorem B1556167 : Blo 1381510 1556167 := bstep (se 1 (by rfl) ⟨1167125, by rfl⟩ : syracuseStep 1556167 = 2334251) B2334251
theorem B2244343 : Blo 1381510 2244343 := bstep (se 1 (by rfl) ⟨1683257, by rfl⟩ : syracuseStep 2244343 = 3366515) B3366515
theorem B79716149 : Blo 1381510 79716149 := bstep (se 5 (by rfl) ⟨3736694, by rfl⟩ : syracuseStep 79716149 = 7473389) B7473389
theorem B6995807 : Blo 1381510 6995807 := bstep (se 1 (by rfl) ⟨5246855, by rfl⟩ : syracuseStep 6995807 = 10493711) B10493711
theorem B3112811 : Blo 1381510 3112811 := bstep (se 1 (by rfl) ⟨2334608, by rfl⟩ : syracuseStep 3112811 = 4669217) B4669217
theorem B8855405 : Blo 1381510 8855405 := bstep (se 3 (by rfl) ⟨1660388, by rfl⟩ : syracuseStep 8855405 = 3320777) B3320777
theorem B29900663 : Blo 1381510 29900663 := bstep (se 1 (by rfl) ⟨22425497, by rfl⟩ : syracuseStep 29900663 = 44850995) B44850995
theorem B3112865 : Blo 1381510 3112865 := bstep (se 2 (by rfl) ⟨1167324, by rfl⟩ : syracuseStep 3112865 = 2334649) B2334649
theorem B2072495 : Blo 1381510 2072495 := bstep (se 1 (by rfl) ⟨1554371, by rfl⟩ : syracuseStep 2072495 = 3108743) B3108743
theorem B6995969 : Blo 1381510 6995969 := bstep (se 2 (by rfl) ⟨2623488, by rfl⟩ : syracuseStep 6995969 = 5246977) B5246977
theorem B6307865 : Blo 1381510 6307865 := bstep (se 2 (by rfl) ⟨2365449, by rfl⟩ : syracuseStep 6307865 = 4730899) B4730899
theorem B9969713 : Blo 1381510 9969713 := bstep (se 2 (by rfl) ⟨3738642, by rfl⟩ : syracuseStep 9969713 = 7477285) B7477285
theorem B2072681 : Blo 1381510 2072681 := bstep (se 2 (by rfl) ⟨777255, by rfl⟩ : syracuseStep 2072681 = 1554511) B1554511
theorem B14942627 : Blo 1381510 14942627 := bstep (se 1 (by rfl) ⟨11206970, by rfl⟩ : syracuseStep 14942627 = 22413941) B22413941
theorem B39862691 : Blo 1381510 39862691 := bstep (se 1 (by rfl) ⟨29897018, by rfl⟩ : syracuseStep 39862691 = 59794037) B59794037
theorem B2072999 : Blo 1381510 2072999 := bstep (se 1 (by rfl) ⟨1554749, by rfl⟩ : syracuseStep 2072999 = 3109499) B3109499
theorem B19939769 : Blo 1381510 19939769 := bstep (se 2 (by rfl) ⟨7477413, by rfl⟩ : syracuseStep 19939769 = 14954827) B14954827
theorem B2073083 : Blo 1381510 2073083 := bstep (se 1 (by rfl) ⟨1554812, by rfl⟩ : syracuseStep 2073083 = 3109625) B3109625
theorem B3498491 : Blo 1381510 3498491 := bstep (se 1 (by rfl) ⟨2623868, by rfl⟩ : syracuseStep 3498491 = 5247737) B5247737
theorem B5317121 : Blo 1381510 5317121 := bstep (se 2 (by rfl) ⟨1993920, by rfl⟩ : syracuseStep 5317121 = 3987841) B3987841
theorem B6644243 : Blo 1381510 6644243 := bstep (se 1 (by rfl) ⟨4983182, by rfl⟩ : syracuseStep 6644243 = 9966365) B9966365
theorem B5251655 : Blo 1381510 5251655 := bstep (se 1 (by rfl) ⟨3938741, by rfl⟩ : syracuseStep 5251655 = 7877483) B7877483
theorem B2073209 : Blo 1381510 2073209 := bstep (se 2 (by rfl) ⟨777453, by rfl⟩ : syracuseStep 2073209 = 1554907) B1554907
theorem B10101419 : Blo 1381510 10101419 := bstep (se 1 (by rfl) ⟨7576064, by rfl⟩ : syracuseStep 10101419 = 15152129) B15152129
theorem B2073263 : Blo 1381510 2073263 := bstep (se 1 (by rfl) ⟨1554947, by rfl⟩ : syracuseStep 2073263 = 3109895) B3109895
theorem B2073311 : Blo 1381510 2073311 := bstep (se 1 (by rfl) ⟨1554983, by rfl⟩ : syracuseStep 2073311 = 3109967) B3109967
theorem B6996779 : Blo 1381510 6996779 := bstep (se 1 (by rfl) ⟨5247584, by rfl⟩ : syracuseStep 6996779 = 10495169) B10495169
theorem B13280183 : Blo 1381510 13280183 := bstep (se 1 (by rfl) ⟨9960137, by rfl⟩ : syracuseStep 13280183 = 19920275) B19920275
theorem B2073575 : Blo 1381510 2073575 := bstep (se 1 (by rfl) ⟨1555181, by rfl⟩ : syracuseStep 2073575 = 3110363) B3110363
theorem B9716773 : Blo 1381510 9716773 := bstep (se 4 (by rfl) ⟨910947, by rfl⟩ : syracuseStep 9716773 = 1821895) B1821895
theorem B2491535 : Blo 1381510 2491535 := bstep (se 1 (by rfl) ⟨1868651, by rfl⟩ : syracuseStep 2491535 = 3737303) B3737303
theorem B14951623 : Blo 1381510 14951623 := bstep (se 1 (by rfl) ⟨11213717, by rfl⟩ : syracuseStep 14951623 = 22427435) B22427435
theorem B2073833 : Blo 1381510 2073833 := bstep (se 2 (by rfl) ⟨777687, by rfl⟩ : syracuseStep 2073833 = 1555375) B1555375
theorem B25216271 : Blo 1381510 25216271 := bstep (se 1 (by rfl) ⟨18912203, by rfl⟩ : syracuseStep 25216271 = 37824407) B37824407
theorem B2073887 : Blo 1381510 2073887 := bstep (se 1 (by rfl) ⟨1555415, by rfl⟩ : syracuseStep 2073887 = 3110831) B3110831
theorem B5907755 : Blo 1381510 5907755 := bstep (se 1 (by rfl) ⟨4430816, by rfl⟩ : syracuseStep 5907755 = 8861633) B8861633
theorem B3499463 : Blo 1381510 3499463 := bstep (se 1 (by rfl) ⟨2624597, by rfl⟩ : syracuseStep 3499463 = 5249195) B5249195
theorem B2074055 : Blo 1381510 2074055 := bstep (se 1 (by rfl) ⟨1555541, by rfl⟩ : syracuseStep 2074055 = 3111083) B3111083
theorem B4662791 : Blo 1381510 4662791 := bstep (se 1 (by rfl) ⟨3497093, by rfl⟩ : syracuseStep 4662791 = 6994187) B6994187
theorem B1476191 : Blo 1381510 1476191 := bstep (se 1 (by rfl) ⟨1107143, by rfl⟩ : syracuseStep 1476191 = 2214287) B2214287
theorem B2213563 : Blo 1381510 2213563 := bstep (se 1 (by rfl) ⟨1660172, by rfl⟩ : syracuseStep 2213563 = 3320345) B3320345
theorem B5252795 : Blo 1381510 5252795 := bstep (se 1 (by rfl) ⟨3939596, by rfl⟩ : syracuseStep 5252795 = 7879193) B7879193
theorem B2074409 : Blo 1381510 2074409 := bstep (se 2 (by rfl) ⟨777903, by rfl⟩ : syracuseStep 2074409 = 1555807) B1555807
theorem B2074415 : Blo 1381510 2074415 := bstep (se 1 (by rfl) ⟨1555811, by rfl⟩ : syracuseStep 2074415 = 3111623) B3111623
theorem B3500243 : Blo 1381510 3500243 := bstep (se 1 (by rfl) ⟨2625182, by rfl⟩ : syracuseStep 3500243 = 5250365) B5250365
theorem B5908727 : Blo 1381510 5908727 := bstep (se 1 (by rfl) ⟨4431545, by rfl⟩ : syracuseStep 5908727 = 8863091) B8863091
theorem B6646013 : Blo 1381510 6646013 := bstep (se 3 (by rfl) ⟨1246127, by rfl⟩ : syracuseStep 6646013 = 2492255) B2492255
theorem B2074889 : Blo 1381510 2074889 := bstep (se 2 (by rfl) ⟨778083, by rfl⟩ : syracuseStep 2074889 = 1556167) B1556167
theorem B2992457 : Blo 1381510 2992457 := bstep (se 2 (by rfl) ⟨1122171, by rfl⟩ : syracuseStep 2992457 = 2244343) B2244343
theorem B2214235 : Blo 1381510 2214235 := bstep (se 1 (by rfl) ⟨1660676, by rfl⟩ : syracuseStep 2214235 = 3321353) B3321353
theorem B6302063 : Blo 1381510 6302063 := bstep (se 1 (by rfl) ⟨4726547, by rfl⟩ : syracuseStep 6302063 = 9453095) B9453095
theorem B2074991 : Blo 1381510 2074991 := bstep (se 1 (by rfl) ⟨1556243, by rfl⟩ : syracuseStep 2074991 = 3112487) B3112487
theorem B3500455 : Blo 1381510 3500455 := bstep (se 1 (by rfl) ⟨2625341, by rfl⟩ : syracuseStep 3500455 = 5250683) B5250683
theorem B26569133 : Blo 1381510 26569133 := bstep (se 3 (by rfl) ⟨4981712, by rfl⟩ : syracuseStep 26569133 = 9963425) B9963425
theorem B26560979 : Blo 1381510 26560979 := bstep (se 1 (by rfl) ⟨19920734, by rfl⟩ : syracuseStep 26560979 = 39841469) B39841469
theorem B4663763 : Blo 1381510 4663763 := bstep (se 1 (by rfl) ⟨3497822, by rfl⟩ : syracuseStep 4663763 = 6995645) B6995645
theorem B53144099 : Blo 1381510 53144099 := bstep (se 1 (by rfl) ⟨39858074, by rfl⟩ : syracuseStep 53144099 = 79716149) B79716149
theorem B4663871 : Blo 1381510 4663871 := bstep (se 1 (by rfl) ⟨3497903, by rfl⟩ : syracuseStep 4663871 = 6995807) B6995807
theorem B2075207 : Blo 1381510 2075207 := bstep (se 1 (by rfl) ⟨1556405, by rfl⟩ : syracuseStep 2075207 = 3112811) B3112811
theorem B3500617 : Blo 1381510 3500617 := bstep (se 2 (by rfl) ⟨1312731, by rfl⟩ : syracuseStep 3500617 = 2625463) B2625463
theorem B5245519 : Blo 1381510 5245519 := bstep (se 1 (by rfl) ⟨3934139, by rfl⟩ : syracuseStep 5245519 = 7868279) B7868279
theorem B19933775 : Blo 1381510 19933775 := bstep (se 1 (by rfl) ⟨14950331, by rfl⟩ : syracuseStep 19933775 = 29900663) B29900663
theorem B2075243 : Blo 1381510 2075243 := bstep (se 1 (by rfl) ⟨1556432, by rfl⟩ : syracuseStep 2075243 = 3112865) B3112865
theorem B6998723 : Blo 1381510 6998723 := bstep (se 1 (by rfl) ⟨5249042, by rfl⟩ : syracuseStep 6998723 = 10498085) B10498085
theorem B3738599 : Blo 1381510 3738599 := bstep (se 1 (by rfl) ⟨2803949, by rfl⟩ : syracuseStep 3738599 = 5607899) B5607899
theorem B5245991 : Blo 1381510 5245991 := bstep (se 1 (by rfl) ⟨3934493, by rfl⟩ : syracuseStep 5245991 = 7868987) B7868987
theorem B10644767 : Blo 1381510 10644767 := bstep (se 1 (by rfl) ⟨7983575, by rfl⟩ : syracuseStep 10644767 = 15967151) B15967151
theorem B1969439 : Blo 1381510 1969439 := bstep (se 1 (by rfl) ⟨1477079, by rfl⟩ : syracuseStep 1969439 = 2954159) B2954159
theorem B3501407 : Blo 1381510 3501407 := bstep (se 1 (by rfl) ⟨2626055, by rfl⟩ : syracuseStep 3501407 = 5252111) B5252111
theorem B4730231 : Blo 1381510 4730231 := bstep (se 1 (by rfl) ⟨3547673, by rfl⟩ : syracuseStep 4730231 = 7095347) B7095347
theorem B1994233 : Blo 1381510 1994233 := bstep (se 2 (by rfl) ⟨747837, by rfl⟩ : syracuseStep 1994233 = 1495675) B1495675
theorem B18460333 : Blo 1381510 18460333 := bstep (se 3 (by rfl) ⟨3461312, by rfl⟩ : syracuseStep 18460333 = 6922625) B6922625
theorem B1748891 : Blo 1381510 1748891 := bstep (se 1 (by rfl) ⟨1311668, by rfl⟩ : syracuseStep 1748891 = 2623337) B2623337
theorem B3108815 : Blo 1381510 3108815 := bstep (se 1 (by rfl) ⟨2331611, by rfl⟩ : syracuseStep 3108815 = 4663223) B4663223
theorem B12611609 : Blo 1381510 12611609 := bstep (se 2 (by rfl) ⟨4729353, by rfl⟩ : syracuseStep 12611609 = 9458707) B9458707
theorem B3109193 : Blo 1381510 3109193 := bstep (se 2 (by rfl) ⟨1165947, by rfl⟩ : syracuseStep 3109193 = 2331895) B2331895
theorem B3109211 : Blo 1381510 3109211 := bstep (se 1 (by rfl) ⟨2331908, by rfl⟩ : syracuseStep 3109211 = 4663817) B4663817
theorem B4665707 : Blo 1381510 4665707 := bstep (se 1 (by rfl) ⟨3499280, by rfl⟩ : syracuseStep 4665707 = 6998561) B6998561
theorem B3936737 : Blo 1381510 3936737 := bstep (se 2 (by rfl) ⟨1476276, by rfl⟩ : syracuseStep 3936737 = 2952553) B2952553
theorem B5902919 : Blo 1381510 5902919 := bstep (se 1 (by rfl) ⟨4427189, by rfl⟩ : syracuseStep 5902919 = 8854379) B8854379
theorem B4665977 : Blo 1381510 4665977 := bstep (se 2 (by rfl) ⟨1749741, by rfl⟩ : syracuseStep 4665977 = 3499483) B3499483
theorem B2953903 : Blo 1381510 2953903 := bstep (se 1 (by rfl) ⟨2215427, by rfl⟩ : syracuseStep 2953903 = 4430855) B4430855
theorem B3109787 : Blo 1381510 3109787 := bstep (se 1 (by rfl) ⟨2332340, by rfl⟩ : syracuseStep 3109787 = 4664681) B4664681
theorem B3109985 : Blo 1381510 3109985 := bstep (se 2 (by rfl) ⟨1166244, by rfl⟩ : syracuseStep 3109985 = 2332489) B2332489
theorem B14939261 : Blo 1381510 14939261 := bstep (se 3 (by rfl) ⟨2801111, by rfl⟩ : syracuseStep 14939261 = 5602223) B5602223
theorem B17724541 : Blo 1381510 17724541 := bstep (se 3 (by rfl) ⟨3323351, by rfl⟩ : syracuseStep 17724541 = 6646703) B6646703
theorem B5903603 : Blo 1381510 5903603 := bstep (se 1 (by rfl) ⟨4427702, by rfl⟩ : syracuseStep 5903603 = 8855405) B8855405
theorem B1381663 : Blo 1381510 1381663 := bstep (se 1 (by rfl) ⟨1036247, by rfl⟩ : syracuseStep 1381663 = 2072495) B2072495
theorem B3110183 : Blo 1381510 3110183 := bstep (se 1 (by rfl) ⟨2332637, by rfl⟩ : syracuseStep 3110183 = 4665275) B4665275
theorem B1381723 : Blo 1381510 1381723 := bstep (se 1 (by rfl) ⟨1036292, by rfl⟩ : syracuseStep 1381723 = 2072585) B2072585
theorem B1381743 : Blo 1381510 1381743 := bstep (se 1 (by rfl) ⟨1036307, by rfl⟩ : syracuseStep 1381743 = 2072615) B2072615
theorem B3593609 : Blo 1381510 3593609 := bstep (se 2 (by rfl) ⟨1347603, by rfl⟩ : syracuseStep 3593609 = 2695207) B2695207
theorem B1381799 : Blo 1381510 1381799 := bstep (se 1 (by rfl) ⟨1036349, by rfl⟩ : syracuseStep 1381799 = 2072699) B2072699
theorem B1381883 : Blo 1381510 1381883 := bstep (se 1 (by rfl) ⟨1036412, by rfl⟩ : syracuseStep 1381883 = 2072825) B2072825
theorem B1381951 : Blo 1381510 1381951 := bstep (se 1 (by rfl) ⟨1036463, by rfl⟩ : syracuseStep 1381951 = 2072927) B2072927
theorem B1381959 : Blo 1381510 1381959 := bstep (se 1 (by rfl) ⟨1036469, by rfl⟩ : syracuseStep 1381959 = 2072939) B2072939
theorem B3110561 : Blo 1381510 3110561 := bstep (se 2 (by rfl) ⟨1166460, by rfl⟩ : syracuseStep 3110561 = 2332921) B2332921
theorem B1382111 : Blo 1381510 1382111 := bstep (se 1 (by rfl) ⟨1036583, by rfl⟩ : syracuseStep 1382111 = 2073167) B2073167
theorem B23615225 : Blo 1381510 23615225 := bstep (se 2 (by rfl) ⟨8855709, by rfl⟩ : syracuseStep 23615225 = 17711419) B17711419
theorem B1554223 : Blo 1381510 1554223 := bstep (se 1 (by rfl) ⟨1165667, by rfl⟩ : syracuseStep 1554223 = 2331335) B2331335
theorem B1382191 : Blo 1381510 1382191 := bstep (se 1 (by rfl) ⟨1036643, by rfl⟩ : syracuseStep 1382191 = 2073287) B2073287
theorem B1554331 : Blo 1381510 1554331 := bstep (se 1 (by rfl) ⟨1165748, by rfl⟩ : syracuseStep 1554331 = 2331497) B2331497
theorem B1382299 : Blo 1381510 1382299 := bstep (se 1 (by rfl) ⟨1036724, by rfl⟩ : syracuseStep 1382299 = 2073449) B2073449
theorem B18921401 : Blo 1381510 18921401 := bstep (se 2 (by rfl) ⟨7095525, by rfl⟩ : syracuseStep 18921401 = 14191051) B14191051
theorem B1382351 : Blo 1381510 1382351 := bstep (se 1 (by rfl) ⟨1036763, by rfl⟩ : syracuseStep 1382351 = 2073527) B2073527
theorem B1382375 : Blo 1381510 1382375 := bstep (se 1 (by rfl) ⟨1036781, by rfl⟩ : syracuseStep 1382375 = 2073563) B2073563
theorem B3110921 : Blo 1381510 3110921 := bstep (se 2 (by rfl) ⟨1166595, by rfl⟩ : syracuseStep 3110921 = 2333191) B2333191
theorem B3323929 : Blo 1381510 3323929 := bstep (se 2 (by rfl) ⟨1246473, by rfl⟩ : syracuseStep 3323929 = 2492947) B2492947
theorem B2103401 : Blo 1381510 2103401 := bstep (se 2 (by rfl) ⟨788775, by rfl⟩ : syracuseStep 2103401 = 1577551) B1577551
theorem B1382687 : Blo 1381510 1382687 := bstep (se 1 (by rfl) ⟨1037015, by rfl⟩ : syracuseStep 1382687 = 2074031) B2074031
theorem B1661215 : Blo 1381510 1661215 := bstep (se 1 (by rfl) ⟨1245911, by rfl⟩ : syracuseStep 1661215 = 2491823) B2491823
theorem B1554727 : Blo 1381510 1554727 := bstep (se 1 (by rfl) ⟨1166045, by rfl⟩ : syracuseStep 1554727 = 2332091) B2332091
theorem B1382747 : Blo 1381510 1382747 := bstep (se 1 (by rfl) ⟨1037060, by rfl⟩ : syracuseStep 1382747 = 2074121) B2074121
theorem B6388079 : Blo 1381510 6388079 := bstep (se 1 (by rfl) ⟨4791059, by rfl⟩ : syracuseStep 6388079 = 9582119) B9582119
theorem B1554799 : Blo 1381510 1554799 := bstep (se 1 (by rfl) ⟨1166099, by rfl⟩ : syracuseStep 1554799 = 2332199) B2332199
theorem B1382767 : Blo 1381510 1382767 := bstep (se 1 (by rfl) ⟨1037075, by rfl⟩ : syracuseStep 1382767 = 2074151) B2074151
theorem B4667759 : Blo 1381510 4667759 := bstep (se 1 (by rfl) ⟨3500819, by rfl⟩ : syracuseStep 4667759 = 7001639) B7001639
theorem B3111335 : Blo 1381510 3111335 := bstep (se 1 (by rfl) ⟨2333501, by rfl⟩ : syracuseStep 3111335 = 4667003) B4667003
theorem B1382823 : Blo 1381510 1382823 := bstep (se 1 (by rfl) ⟨1037117, by rfl⟩ : syracuseStep 1382823 = 2074235) B2074235
theorem B6994349 : Blo 1381510 6994349 := bstep (se 3 (by rfl) ⟨1311440, by rfl⟩ : syracuseStep 6994349 = 2622881) B2622881
theorem B7002611 : Blo 1381510 7002611 := bstep (se 1 (by rfl) ⟨5251958, by rfl⟩ : syracuseStep 7002611 = 10503917) B10503917
theorem B1382907 : Blo 1381510 1382907 := bstep (se 1 (by rfl) ⟨1037180, by rfl⟩ : syracuseStep 1382907 = 2074361) B2074361
theorem B3111443 : Blo 1381510 3111443 := bstep (se 1 (by rfl) ⟨2333582, by rfl⟩ : syracuseStep 3111443 = 4667165) B4667165
theorem B1382975 : Blo 1381510 1382975 := bstep (se 1 (by rfl) ⟨1037231, by rfl⟩ : syracuseStep 1382975 = 2074463) B2074463
theorem B1555015 : Blo 1381510 1555015 := bstep (se 1 (by rfl) ⟨1166261, by rfl⟩ : syracuseStep 1555015 = 2332523) B2332523
theorem B3111497 : Blo 1381510 3111497 := bstep (se 2 (by rfl) ⟨1166811, by rfl⟩ : syracuseStep 3111497 = 2333623) B2333623
theorem B1382983 : Blo 1381510 1382983 := bstep (se 1 (by rfl) ⟨1037237, by rfl⟩ : syracuseStep 1382983 = 2074475) B2074475
theorem B6994511 : Blo 1381510 6994511 := bstep (se 1 (by rfl) ⟨5245883, by rfl⟩ : syracuseStep 6994511 = 10491767) B10491767
theorem B6306443 : Blo 1381510 6306443 := bstep (se 1 (by rfl) ⟨4729832, by rfl⟩ : syracuseStep 6306443 = 9459665) B9459665
theorem B5249711 : Blo 1381510 5249711 := bstep (se 1 (by rfl) ⟨3937283, by rfl⟩ : syracuseStep 5249711 = 7874567) B7874567
theorem B2333407 : Blo 1381510 2333407 := bstep (se 1 (by rfl) ⟨1750055, by rfl⟩ : syracuseStep 2333407 = 3500111) B3500111
theorem B1383135 : Blo 1381510 1383135 := bstep (se 1 (by rfl) ⟨1037351, by rfl⟩ : syracuseStep 1383135 = 2074703) B2074703
theorem B1383215 : Blo 1381510 1383215 := bstep (se 1 (by rfl) ⟨1037411, by rfl⟩ : syracuseStep 1383215 = 2074823) B2074823
theorem B5905295 : Blo 1381510 5905295 := bstep (se 1 (by rfl) ⟨4428971, by rfl⟩ : syracuseStep 5905295 = 8857943) B8857943
theorem B1383323 : Blo 1381510 1383323 := bstep (se 1 (by rfl) ⟨1037492, by rfl⟩ : syracuseStep 1383323 = 2074985) B2074985
theorem B1383375 : Blo 1381510 1383375 := bstep (se 1 (by rfl) ⟨1037531, by rfl⟩ : syracuseStep 1383375 = 2075063) B2075063
theorem B3111911 : Blo 1381510 3111911 := bstep (se 1 (by rfl) ⟨2333933, by rfl⟩ : syracuseStep 3111911 = 4667867) B4667867
theorem B1383399 : Blo 1381510 1383399 := bstep (se 1 (by rfl) ⟨1037549, by rfl⟩ : syracuseStep 1383399 = 2075099) B2075099
theorem B7003259 : Blo 1381510 7003259 := bstep (se 1 (by rfl) ⟨5252444, by rfl⟩ : syracuseStep 7003259 = 10504889) B10504889
theorem B2333839 : Blo 1381510 2333839 := bstep (se 1 (by rfl) ⟨1750379, by rfl⟩ : syracuseStep 2333839 = 3500759) B3500759
theorem B14187737 : Blo 1381510 14187737 := bstep (se 2 (by rfl) ⟨5320401, by rfl⟩ : syracuseStep 14187737 = 10640803) B10640803
theorem B3112289 : Blo 1381510 3112289 := bstep (se 2 (by rfl) ⟨1167108, by rfl⟩ : syracuseStep 3112289 = 2334217) B2334217
theorem B60611975 : Blo 1381510 60611975 := bstep (se 1 (by rfl) ⟨45458981, by rfl⟩ : syracuseStep 60611975 = 90917963) B90917963
theorem B2334089 : Blo 1381510 2334089 := bstep (se 2 (by rfl) ⟨875283, by rfl⟩ : syracuseStep 2334089 = 1750567) B1750567
theorem B3497377 : Blo 1381510 3497377 := bstep (se 2 (by rfl) ⟨1311516, by rfl⟩ : syracuseStep 3497377 = 2623033) B2623033
theorem B1555879 : Blo 1381510 1555879 := bstep (se 1 (by rfl) ⟨1166909, by rfl⟩ : syracuseStep 1555879 = 2333819) B2333819
theorem B4488635 : Blo 1381510 4488635 := bstep (se 1 (by rfl) ⟨3366476, by rfl⟩ : syracuseStep 4488635 = 6732953) B6732953
theorem B3112379 : Blo 1381510 3112379 := bstep (se 1 (by rfl) ⟨2334284, by rfl⟩ : syracuseStep 3112379 = 4668569) B4668569
theorem B2276857 : Blo 1381510 2276857 := bstep (se 2 (by rfl) ⟨853821, by rfl⟩ : syracuseStep 2276857 = 1707643) B1707643
theorem B3112505 : Blo 1381510 3112505 := bstep (se 2 (by rfl) ⟨1167189, by rfl⟩ : syracuseStep 3112505 = 2334379) B2334379
theorem B5905979 : Blo 1381510 5905979 := bstep (se 1 (by rfl) ⟨4429484, by rfl⟩ : syracuseStep 5905979 = 8858969) B8858969
theorem B6823507 : Blo 1381510 6823507 := bstep (se 1 (by rfl) ⟨5117630, by rfl⟩ : syracuseStep 6823507 = 10235261) B10235261
theorem B3546719 : Blo 1381510 3546719 := bstep (se 1 (by rfl) ⟨2660039, by rfl⟩ : syracuseStep 3546719 = 5320079) B5320079
theorem B4669163 : Blo 1381510 4669163 := bstep (se 1 (by rfl) ⟨3501872, by rfl⟩ : syracuseStep 4669163 = 7003745) B7003745
theorem B7003907 : Blo 1381510 7003907 := bstep (se 1 (by rfl) ⟨5252930, by rfl⟩ : syracuseStep 7003907 = 10505861) B10505861
theorem B2072375 : Blo 1381510 2072375 := bstep (se 1 (by rfl) ⟨1554281, by rfl⟩ : syracuseStep 2072375 = 3108563) B3108563
theorem B2334521 : Blo 1381510 2334521 := bstep (se 2 (by rfl) ⟨875445, by rfl⟩ : syracuseStep 2334521 = 1750891) B1750891
theorem B4431905 : Blo 1381510 4431905 := bstep (se 2 (by rfl) ⟨1661964, by rfl⟩ : syracuseStep 4431905 = 3323929) B3323929
theorem B2072795 : Blo 1381510 2072795 := bstep (se 1 (by rfl) ⟨1554596, by rfl⟩ : syracuseStep 2072795 = 3109193) B3109193
theorem B2072807 : Blo 1381510 2072807 := bstep (se 1 (by rfl) ⟨1554605, by rfl⟩ : syracuseStep 2072807 = 3109211) B3109211
theorem B9961751 : Blo 1381510 9961751 := bstep (se 1 (by rfl) ⟨7471313, by rfl⟩ : syracuseStep 9961751 = 14942627) B14942627
theorem B26575127 : Blo 1381510 26575127 := bstep (se 1 (by rfl) ⟨19931345, by rfl⟩ : syracuseStep 26575127 = 39862691) B39862691
theorem B2072969 : Blo 1381510 2072969 := bstep (se 2 (by rfl) ⟨777363, by rfl⟩ : syracuseStep 2072969 = 1554727) B1554727
theorem B6734279 : Blo 1381510 6734279 := bstep (se 1 (by rfl) ⟨5050709, by rfl⟩ : syracuseStep 6734279 = 10101419) B10101419
theorem B2073065 : Blo 1381510 2073065 := bstep (se 2 (by rfl) ⟨777399, by rfl⟩ : syracuseStep 2073065 = 1554799) B1554799
theorem B2073191 : Blo 1381510 2073191 := bstep (se 1 (by rfl) ⟨1554893, by rfl⟩ : syracuseStep 2073191 = 3109787) B3109787
theorem B2073323 : Blo 1381510 2073323 := bstep (se 1 (by rfl) ⟨1554992, by rfl⟩ : syracuseStep 2073323 = 3109985) B3109985
theorem B5251837 : Blo 1381510 5251837 := bstep (se 3 (by rfl) ⟨984719, by rfl⟩ : syracuseStep 5251837 = 1969439) B1969439
theorem B2073353 : Blo 1381510 2073353 := bstep (se 2 (by rfl) ⟨777507, by rfl⟩ : syracuseStep 2073353 = 1555015) B1555015
theorem B16810847 : Blo 1381510 16810847 := bstep (se 1 (by rfl) ⟨12608135, by rfl⟩ : syracuseStep 16810847 = 25216271) B25216271
theorem B2073455 : Blo 1381510 2073455 := bstep (se 1 (by rfl) ⟨1555091, by rfl⟩ : syracuseStep 2073455 = 3110183) B3110183
theorem B2073707 : Blo 1381510 2073707 := bstep (se 1 (by rfl) ⟨1555280, by rfl⟩ : syracuseStep 2073707 = 3110561) B3110561
theorem B11969693 : Blo 1381510 11969693 := bstep (se 3 (by rfl) ⟨2244317, by rfl⟩ : syracuseStep 11969693 = 4488635) B4488635
theorem B2073947 : Blo 1381510 2073947 := bstep (se 1 (by rfl) ⟨1555460, by rfl⟩ : syracuseStep 2073947 = 3110921) B3110921
theorem B1402267 : Blo 1381510 1402267 := bstep (se 1 (by rfl) ⟨1051700, by rfl⟩ : syracuseStep 1402267 = 2103401) B2103401
theorem B2074223 : Blo 1381510 2074223 := bstep (se 1 (by rfl) ⟨1555667, by rfl⟩ : syracuseStep 2074223 = 3111335) B3111335
theorem B4662899 : Blo 1381510 4662899 := bstep (se 1 (by rfl) ⟨3497174, by rfl⟩ : syracuseStep 4662899 = 6994349) B6994349
theorem B17712755 : Blo 1381510 17712755 := bstep (se 1 (by rfl) ⟨13284566, by rfl⟩ : syracuseStep 17712755 = 26569133) B26569133
theorem B2074295 : Blo 1381510 2074295 := bstep (se 1 (by rfl) ⟨1555721, by rfl⟩ : syracuseStep 2074295 = 3111443) B3111443
theorem B2074331 : Blo 1381510 2074331 := bstep (se 1 (by rfl) ⟨1555748, by rfl⟩ : syracuseStep 2074331 = 3111497) B3111497
theorem B4663007 : Blo 1381510 4663007 := bstep (se 1 (by rfl) ⟨3497255, by rfl⟩ : syracuseStep 4663007 = 6994511) B6994511
theorem B13289183 : Blo 1381510 13289183 := bstep (se 1 (by rfl) ⟨9966887, by rfl⟩ : syracuseStep 13289183 = 19933775) B19933775
theorem B4204295 : Blo 1381510 4204295 := bstep (se 1 (by rfl) ⟨3153221, by rfl⟩ : syracuseStep 4204295 = 6306443) B6306443
theorem B3499807 : Blo 1381510 3499807 := bstep (se 1 (by rfl) ⟨2624855, by rfl⟩ : syracuseStep 3499807 = 5249711) B5249711
theorem B4663169 : Blo 1381510 4663169 := bstep (se 2 (by rfl) ⟨1748688, by rfl⟩ : syracuseStep 4663169 = 3497377) B3497377
theorem B2074505 : Blo 1381510 2074505 := bstep (se 2 (by rfl) ⟨777939, by rfl⟩ : syracuseStep 2074505 = 1555879) B1555879
theorem B2074607 : Blo 1381510 2074607 := bstep (se 1 (by rfl) ⟨1555955, by rfl⟩ : syracuseStep 2074607 = 3111911) B3111911
theorem B2492399 : Blo 1381510 2492399 := bstep (se 1 (by rfl) ⟨1869299, by rfl⟩ : syracuseStep 2492399 = 3738599) B3738599
theorem B7096511 : Blo 1381510 7096511 := bstep (se 1 (by rfl) ⟨5322383, by rfl⟩ : syracuseStep 7096511 = 10644767) B10644767
theorem B2074859 : Blo 1381510 2074859 := bstep (se 1 (by rfl) ⟨1556144, by rfl⟩ : syracuseStep 2074859 = 3112289) B3112289
theorem B2951417 : Blo 1381510 2951417 := bstep (se 2 (by rfl) ⟨1106781, by rfl⟩ : syracuseStep 2951417 = 2213563) B2213563
theorem B2074919 : Blo 1381510 2074919 := bstep (se 1 (by rfl) ⟨1556189, by rfl⟩ : syracuseStep 2074919 = 3112379) B3112379
theorem B2075003 : Blo 1381510 2075003 := bstep (se 1 (by rfl) ⟨1556252, by rfl⟩ : syracuseStep 2075003 = 3112505) B3112505
theorem B4663709 : Blo 1381510 4663709 := bstep (se 3 (by rfl) ⟨874445, by rfl⟩ : syracuseStep 4663709 = 1748891) B1748891
theorem B4663979 : Blo 1381510 4663979 := bstep (se 1 (by rfl) ⟨3497984, by rfl⟩ : syracuseStep 4663979 = 6995969) B6995969
theorem B8407739 : Blo 1381510 8407739 := bstep (se 1 (by rfl) ⟨6305804, by rfl⟩ : syracuseStep 8407739 = 12611609) B12611609
theorem B4205243 : Blo 1381510 4205243 := bstep (se 1 (by rfl) ⟨3153932, by rfl⟩ : syracuseStep 4205243 = 6307865) B6307865
theorem B6646475 : Blo 1381510 6646475 := bstep (se 1 (by rfl) ⟨4984856, by rfl⟩ : syracuseStep 6646475 = 9969713) B9969713
theorem B2624491 : Blo 1381510 2624491 := bstep (se 1 (by rfl) ⟨1968368, by rfl⟩ : syracuseStep 2624491 = 3936737) B3936737
theorem B2214953 : Blo 1381510 2214953 := bstep (se 2 (by rfl) ⟨830607, by rfl⟩ : syracuseStep 2214953 = 1661215) B1661215
theorem B3935279 : Blo 1381510 3935279 := bstep (se 1 (by rfl) ⟨2951459, by rfl⟩ : syracuseStep 3935279 = 5902919) B5902919
theorem B3501103 : Blo 1381510 3501103 := bstep (se 1 (by rfl) ⟨2625827, by rfl⟩ : syracuseStep 3501103 = 5251655) B5251655
theorem B4664519 : Blo 1381510 4664519 := bstep (se 1 (by rfl) ⟨3498389, by rfl⟩ : syracuseStep 4664519 = 6996779) B6996779
theorem B15756605 : Blo 1381510 15756605 := bstep (se 3 (by rfl) ⟨2954363, by rfl⟩ : syracuseStep 15756605 = 5908727) B5908727
theorem B3935735 : Blo 1381510 3935735 := bstep (se 1 (by rfl) ⟨2951801, by rfl⟩ : syracuseStep 3935735 = 5903603) B5903603
theorem B2395739 : Blo 1381510 2395739 := bstep (se 1 (by rfl) ⟨1796804, by rfl⟩ : syracuseStep 2395739 = 3593609) B3593609
theorem B16805501 : Blo 1381510 16805501 := bstep (se 3 (by rfl) ⟨3151031, by rfl⟩ : syracuseStep 16805501 = 6302063) B6302063
theorem B17034877 : Blo 1381510 17034877 := bstep (se 3 (by rfl) ⟨3194039, by rfl⟩ : syracuseStep 17034877 = 6388079) B6388079
theorem B3108527 : Blo 1381510 3108527 := bstep (se 1 (by rfl) ⟨2331395, by rfl⟩ : syracuseStep 3108527 = 4662791) B4662791
theorem B3501863 : Blo 1381510 3501863 := bstep (se 1 (by rfl) ⟨2626397, by rfl⟩ : syracuseStep 3501863 = 5252795) B5252795
theorem B12955697 : Blo 1381510 12955697 := bstep (se 2 (by rfl) ⟨4858386, by rfl⟩ : syracuseStep 12955697 = 9716773) B9716773
theorem B1994971 : Blo 1381510 1994971 := bstep (se 1 (by rfl) ⟨1496228, by rfl⟩ : syracuseStep 1994971 = 2992457) B2992457
theorem B3936509 : Blo 1381510 3936509 := bstep (se 3 (by rfl) ⟨738095, by rfl⟩ : syracuseStep 3936509 = 1476191) B1476191
theorem B19935497 : Blo 1381510 19935497 := bstep (se 2 (by rfl) ⟨7475811, by rfl⟩ : syracuseStep 19935497 = 14951623) B14951623
theorem B17707319 : Blo 1381510 17707319 := bstep (se 1 (by rfl) ⟨13280489, by rfl⟩ : syracuseStep 17707319 = 26560979) B26560979
theorem B3109175 : Blo 1381510 3109175 := bstep (se 1 (by rfl) ⟨2331881, by rfl⟩ : syracuseStep 3109175 = 4663763) B4663763
theorem B3109247 : Blo 1381510 3109247 := bstep (se 1 (by rfl) ⟨2331935, by rfl⟩ : syracuseStep 3109247 = 4663871) B4663871
theorem B4665815 : Blo 1381510 4665815 := bstep (se 1 (by rfl) ⟨3499361, by rfl⟩ : syracuseStep 4665815 = 6998723) B6998723
theorem B11809253 : Blo 1381510 11809253 := bstep (se 4 (by rfl) ⟨1107117, by rfl⟩ : syracuseStep 11809253 = 2214235) B2214235
theorem B3936863 : Blo 1381510 3936863 := bstep (se 1 (by rfl) ⟨2952647, by rfl⟩ : syracuseStep 3936863 = 5905295) B5905295
theorem B2658977 : Blo 1381510 2658977 := bstep (se 2 (by rfl) ⟨997116, by rfl⟩ : syracuseStep 2658977 = 1994233) B1994233
theorem B3035809 : Blo 1381510 3035809 := bstep (se 2 (by rfl) ⟨1138428, by rfl⟩ : syracuseStep 3035809 = 2276857) B2276857
theorem B9098009 : Blo 1381510 9098009 := bstep (se 2 (by rfl) ⟨3411753, by rfl⟩ : syracuseStep 9098009 = 6823507) B6823507
theorem B9458491 : Blo 1381510 9458491 := bstep (se 1 (by rfl) ⟨7093868, by rfl⟩ : syracuseStep 9458491 = 14187737) B14187737
theorem B24613777 : Blo 1381510 24613777 := bstep (se 2 (by rfl) ⟨9230166, by rfl⟩ : syracuseStep 24613777 = 18460333) B18460333
theorem B40407983 : Blo 1381510 40407983 := bstep (se 1 (by rfl) ⟨30305987, by rfl⟩ : syracuseStep 40407983 = 60611975) B60611975
theorem B3937319 : Blo 1381510 3937319 := bstep (se 1 (by rfl) ⟨2952989, by rfl⟩ : syracuseStep 3937319 = 5905979) B5905979
theorem B2364479 : Blo 1381510 2364479 := bstep (se 1 (by rfl) ⟨1773359, by rfl⟩ : syracuseStep 2364479 = 3546719) B3546719
theorem B1381583 : Blo 1381510 1381583 := bstep (se 1 (by rfl) ⟨1036187, by rfl⟩ : syracuseStep 1381583 = 2072375) B2072375
theorem B1381787 : Blo 1381510 1381787 := bstep (se 1 (by rfl) ⟨1036340, by rfl⟩ : syracuseStep 1381787 = 2072681) B2072681
theorem B3110471 : Blo 1381510 3110471 := bstep (se 1 (by rfl) ⟨2332853, by rfl⟩ : syracuseStep 3110471 = 4665707) B4665707
theorem B1381999 : Blo 1381510 1381999 := bstep (se 1 (by rfl) ⟨1036499, by rfl⟩ : syracuseStep 1381999 = 2072999) B2072999
theorem B13293179 : Blo 1381510 13293179 := bstep (se 1 (by rfl) ⟨9969884, by rfl⟩ : syracuseStep 13293179 = 19939769) B19939769
theorem B1382055 : Blo 1381510 1382055 := bstep (se 1 (by rfl) ⟨1036541, by rfl⟩ : syracuseStep 1382055 = 2073083) B2073083
theorem B2332327 : Blo 1381510 2332327 := bstep (se 1 (by rfl) ⟨1749245, by rfl⟩ : syracuseStep 2332327 = 3498491) B3498491
theorem B4429495 : Blo 1381510 4429495 := bstep (se 1 (by rfl) ⟨3322121, by rfl⟩ : syracuseStep 4429495 = 6644243) B6644243
theorem B1382139 : Blo 1381510 1382139 := bstep (se 1 (by rfl) ⟨1036604, by rfl⟩ : syracuseStep 1382139 = 2073209) B2073209
theorem B3110651 : Blo 1381510 3110651 := bstep (se 1 (by rfl) ⟨2332988, by rfl⟩ : syracuseStep 3110651 = 4665977) B4665977
theorem B1382175 : Blo 1381510 1382175 := bstep (se 1 (by rfl) ⟨1036631, by rfl⟩ : syracuseStep 1382175 = 2073263) B2073263
theorem B1382207 : Blo 1381510 1382207 := bstep (se 1 (by rfl) ⟨1036655, by rfl⟩ : syracuseStep 1382207 = 2073311) B2073311
theorem B4667273 : Blo 1381510 4667273 := bstep (se 2 (by rfl) ⟨1750227, by rfl⟩ : syracuseStep 4667273 = 3500455) B3500455
theorem B8853455 : Blo 1381510 8853455 := bstep (se 1 (by rfl) ⟨6640091, by rfl⟩ : syracuseStep 8853455 = 13280183) B13280183
theorem B1382383 : Blo 1381510 1382383 := bstep (se 1 (by rfl) ⟨1036787, by rfl⟩ : syracuseStep 1382383 = 2073575) B2073575
theorem B9959507 : Blo 1381510 9959507 := bstep (se 1 (by rfl) ⟨7469630, by rfl⟩ : syracuseStep 9959507 = 14939261) B14939261
theorem B1661023 : Blo 1381510 1661023 := bstep (se 1 (by rfl) ⟨1245767, by rfl⟩ : syracuseStep 1661023 = 2491535) B2491535
theorem B4667489 : Blo 1381510 4667489 := bstep (se 2 (by rfl) ⟨1750308, by rfl⟩ : syracuseStep 4667489 = 3500617) B3500617
theorem B6994025 : Blo 1381510 6994025 := bstep (se 2 (by rfl) ⟨2622759, by rfl⟩ : syracuseStep 6994025 = 5245519) B5245519
theorem B1382555 : Blo 1381510 1382555 := bstep (se 1 (by rfl) ⟨1036916, by rfl⟩ : syracuseStep 1382555 = 2073833) B2073833
theorem B1382591 : Blo 1381510 1382591 := bstep (se 1 (by rfl) ⟨1036943, by rfl⟩ : syracuseStep 1382591 = 2073887) B2073887
theorem B3938503 : Blo 1381510 3938503 := bstep (se 1 (by rfl) ⟨2953877, by rfl⟩ : syracuseStep 3938503 = 5907755) B5907755
theorem B3938537 : Blo 1381510 3938537 := bstep (se 2 (by rfl) ⟨1476951, by rfl⟩ : syracuseStep 3938537 = 2953903) B2953903
theorem B3111209 : Blo 1381510 3111209 := bstep (se 2 (by rfl) ⟨1166703, by rfl⟩ : syracuseStep 3111209 = 2333407) B2333407
theorem B2332975 : Blo 1381510 2332975 := bstep (se 1 (by rfl) ⟨1749731, by rfl⟩ : syracuseStep 2332975 = 3499463) B3499463
theorem B1382703 : Blo 1381510 1382703 := bstep (se 1 (by rfl) ⟨1037027, by rfl⟩ : syracuseStep 1382703 = 2074055) B2074055
theorem B15743483 : Blo 1381510 15743483 := bstep (se 1 (by rfl) ⟨11807612, by rfl⟩ : syracuseStep 15743483 = 23615225) B23615225
theorem B1382939 : Blo 1381510 1382939 := bstep (se 1 (by rfl) ⟨1037204, by rfl⟩ : syracuseStep 1382939 = 2074409) B2074409
theorem B1382943 : Blo 1381510 1382943 := bstep (se 1 (by rfl) ⟨1037207, by rfl⟩ : syracuseStep 1382943 = 2074415) B2074415
theorem B12614267 : Blo 1381510 12614267 := bstep (se 1 (by rfl) ⟨9460700, by rfl⟩ : syracuseStep 12614267 = 18921401) B18921401
theorem B14178989 : Blo 1381510 14178989 := bstep (se 3 (by rfl) ⟨2658560, by rfl⟩ : syracuseStep 14178989 = 5317121) B5317121
theorem B2333495 : Blo 1381510 2333495 := bstep (se 1 (by rfl) ⟨1750121, by rfl⟩ : syracuseStep 2333495 = 3500243) B3500243
theorem B23632721 : Blo 1381510 23632721 := bstep (se 2 (by rfl) ⟨8862270, by rfl⟩ : syracuseStep 23632721 = 17724541) B17724541
theorem B4430675 : Blo 1381510 4430675 := bstep (se 1 (by rfl) ⟨3323006, by rfl⟩ : syracuseStep 4430675 = 6646013) B6646013
theorem B1383259 : Blo 1381510 1383259 := bstep (se 1 (by rfl) ⟨1037444, by rfl⟩ : syracuseStep 1383259 = 2074889) B2074889
theorem B3111785 : Blo 1381510 3111785 := bstep (se 2 (by rfl) ⟨1166919, by rfl⟩ : syracuseStep 3111785 = 2333839) B2333839
theorem B3111839 : Blo 1381510 3111839 := bstep (se 1 (by rfl) ⟨2333879, by rfl⟩ : syracuseStep 3111839 = 4667759) B4667759
theorem B1383327 : Blo 1381510 1383327 := bstep (se 1 (by rfl) ⟨1037495, by rfl⟩ : syracuseStep 1383327 = 2074991) B2074991
theorem B4668407 : Blo 1381510 4668407 := bstep (se 1 (by rfl) ⟨3501305, by rfl⟩ : syracuseStep 4668407 = 7002611) B7002611
theorem B35429399 : Blo 1381510 35429399 := bstep (se 1 (by rfl) ⟨26572049, by rfl⟩ : syracuseStep 35429399 = 53144099) B53144099
theorem B1383471 : Blo 1381510 1383471 := bstep (se 1 (by rfl) ⟨1037603, by rfl⟩ : syracuseStep 1383471 = 2075207) B2075207
theorem B1383495 : Blo 1381510 1383495 := bstep (se 1 (by rfl) ⟨1037621, by rfl⟩ : syracuseStep 1383495 = 2075243) B2075243
theorem B3497327 : Blo 1381510 3497327 := bstep (se 1 (by rfl) ⟨2622995, by rfl⟩ : syracuseStep 3497327 = 5245991) B5245991
theorem B4668839 : Blo 1381510 4668839 := bstep (se 1 (by rfl) ⟨3501629, by rfl⟩ : syracuseStep 4668839 = 7003259) B7003259
theorem B2334271 : Blo 1381510 2334271 := bstep (se 1 (by rfl) ⟨1750703, by rfl⟩ : syracuseStep 2334271 = 3501407) B3501407
theorem B3153487 : Blo 1381510 3153487 := bstep (se 1 (by rfl) ⟨2365115, by rfl⟩ : syracuseStep 3153487 = 4730231) B4730231
theorem B1556059 : Blo 1381510 1556059 := bstep (se 1 (by rfl) ⟨1167044, by rfl⟩ : syracuseStep 1556059 = 2334089) B2334089
theorem B2072297 : Blo 1381510 2072297 := bstep (se 2 (by rfl) ⟨777111, by rfl⟩ : syracuseStep 2072297 = 1554223) B1554223
theorem B3112775 : Blo 1381510 3112775 := bstep (se 1 (by rfl) ⟨2334581, by rfl⟩ : syracuseStep 3112775 = 4669163) B4669163
theorem B4669271 : Blo 1381510 4669271 := bstep (se 1 (by rfl) ⟨3501953, by rfl⟩ : syracuseStep 4669271 = 7003907) B7003907
theorem B2072441 : Blo 1381510 2072441 := bstep (se 2 (by rfl) ⟨777165, by rfl⟩ : syracuseStep 2072441 = 1554331) B1554331
theorem B1556347 : Blo 1381510 1556347 := bstep (se 1 (by rfl) ⟨1167260, by rfl⟩ : syracuseStep 1556347 = 2334521) B2334521
theorem B2072543 : Blo 1381510 2072543 := bstep (se 1 (by rfl) ⟨1554407, by rfl⟩ : syracuseStep 2072543 = 3108815) B3108815
theorem B11804879 : Blo 1381510 11804879 := bstep (se 1 (by rfl) ⟨8853659, by rfl⟩ : syracuseStep 11804879 = 17707319) B17707319
theorem B2072783 : Blo 1381510 2072783 := bstep (se 1 (by rfl) ⟨1554587, by rfl⟩ : syracuseStep 2072783 = 3109175) B3109175
theorem B2072831 : Blo 1381510 2072831 := bstep (se 1 (by rfl) ⟨1554623, by rfl⟩ : syracuseStep 2072831 = 3109247) B3109247
theorem B5251337 : Blo 1381510 5251337 := bstep (se 2 (by rfl) ⟨1969251, by rfl⟩ : syracuseStep 5251337 = 3938503) B3938503
theorem B4489519 : Blo 1381510 4489519 := bstep (se 1 (by rfl) ⟨3367139, by rfl⟩ : syracuseStep 4489519 = 6734279) B6734279
theorem B7872835 : Blo 1381510 7872835 := bstep (se 1 (by rfl) ⟨5904626, by rfl⟩ : syracuseStep 7872835 = 11809253) B11809253
theorem B11207231 : Blo 1381510 11207231 := bstep (se 1 (by rfl) ⟨8405423, by rfl⟩ : syracuseStep 11207231 = 16810847) B16810847
theorem B7979795 : Blo 1381510 7979795 := bstep (se 1 (by rfl) ⟨5984846, by rfl⟩ : syracuseStep 7979795 = 11969693) B11969693
theorem B2073647 : Blo 1381510 2073647 := bstep (se 1 (by rfl) ⟨1555235, by rfl⟩ : syracuseStep 2073647 = 3110471) B3110471
theorem B2073767 : Blo 1381510 2073767 := bstep (se 1 (by rfl) ⟨1555325, by rfl⟩ : syracuseStep 2073767 = 3110651) B3110651
theorem B2802863 : Blo 1381510 2802863 := bstep (se 1 (by rfl) ⟨2102147, by rfl⟩ : syracuseStep 2802863 = 4204295) B4204295
theorem B32818369 : Blo 1381510 32818369 := bstep (se 2 (by rfl) ⟨12306888, by rfl⟩ : syracuseStep 32818369 = 24613777) B24613777
theorem B3499321 : Blo 1381510 3499321 := bstep (se 2 (by rfl) ⟨1312245, by rfl⟩ : syracuseStep 3499321 = 2624491) B2624491
theorem B4662683 : Blo 1381510 4662683 := bstep (se 1 (by rfl) ⟨3497012, by rfl⟩ : syracuseStep 4662683 = 6994025) B6994025
theorem B2074139 : Blo 1381510 2074139 := bstep (se 1 (by rfl) ⟨1555604, by rfl⟩ : syracuseStep 2074139 = 3111209) B3111209
theorem B10495655 : Blo 1381510 10495655 := bstep (se 1 (by rfl) ⟨7871741, by rfl⟩ : syracuseStep 10495655 = 15743483) B15743483
theorem B5605159 : Blo 1381510 5605159 := bstep (se 1 (by rfl) ⟨4203869, by rfl⟩ : syracuseStep 5605159 = 8407739) B8407739
theorem B2803495 : Blo 1381510 2803495 := bstep (se 1 (by rfl) ⟨2102621, by rfl⟩ : syracuseStep 2803495 = 4205243) B4205243
theorem B1869689 : Blo 1381510 1869689 := bstep (se 2 (by rfl) ⟨701133, by rfl⟩ : syracuseStep 1869689 = 1402267) B1402267
theorem B15755147 : Blo 1381510 15755147 := bstep (se 1 (by rfl) ⟨11816360, by rfl⟩ : syracuseStep 15755147 = 23632721) B23632721
theorem B2074523 : Blo 1381510 2074523 := bstep (se 1 (by rfl) ⟨1555892, by rfl⟩ : syracuseStep 2074523 = 3111785) B3111785
theorem B2074559 : Blo 1381510 2074559 := bstep (se 1 (by rfl) ⟨1555919, by rfl⟩ : syracuseStep 2074559 = 3111839) B3111839
theorem B23619599 : Blo 1381510 23619599 := bstep (se 1 (by rfl) ⟨17714699, by rfl⟩ : syracuseStep 23619599 = 35429399) B35429399
theorem B1476635 : Blo 1381510 1476635 := bstep (se 1 (by rfl) ⟨1107476, by rfl⟩ : syracuseStep 1476635 = 2214953) B2214953
theorem B2623519 : Blo 1381510 2623519 := bstep (se 1 (by rfl) ⟨1967639, by rfl⟩ : syracuseStep 2623519 = 3935279) B3935279
theorem B4204649 : Blo 1381510 4204649 := bstep (se 2 (by rfl) ⟨1576743, by rfl⟩ : syracuseStep 4204649 = 3153487) B3153487
theorem B2074745 : Blo 1381510 2074745 := bstep (se 2 (by rfl) ⟨778029, by rfl⟩ : syracuseStep 2074745 = 1556059) B1556059
theorem B10504403 : Blo 1381510 10504403 := bstep (se 1 (by rfl) ⟨7878302, by rfl⟩ : syracuseStep 10504403 = 15756605) B15756605
theorem B2623823 : Blo 1381510 2623823 := bstep (se 1 (by rfl) ⟨1967867, by rfl⟩ : syracuseStep 2623823 = 3935735) B3935735
theorem B2075129 : Blo 1381510 2075129 := bstep (se 2 (by rfl) ⟨778173, by rfl⟩ : syracuseStep 2075129 = 1556347) B1556347
theorem B2075183 : Blo 1381510 2075183 := bstep (se 1 (by rfl) ⟨1556387, by rfl⟩ : syracuseStep 2075183 = 3112775) B3112775
theorem B8637131 : Blo 1381510 8637131 := bstep (se 1 (by rfl) ⟨6477848, by rfl⟩ : syracuseStep 8637131 = 12955697) B12955697
theorem B2214697 : Blo 1381510 2214697 := bstep (se 2 (by rfl) ⟨830511, by rfl⟩ : syracuseStep 2214697 = 1661023) B1661023
theorem B2624339 : Blo 1381510 2624339 := bstep (se 1 (by rfl) ⟨1968254, by rfl⟩ : syracuseStep 2624339 = 3936509) B3936509
theorem B13290331 : Blo 1381510 13290331 := bstep (se 1 (by rfl) ⟨9967748, by rfl⟩ : syracuseStep 13290331 = 19935497) B19935497
theorem B2624575 : Blo 1381510 2624575 := bstep (se 1 (by rfl) ⟨1968431, by rfl⟩ : syracuseStep 2624575 = 3936863) B3936863
theorem B1772651 : Blo 1381510 1772651 := bstep (se 1 (by rfl) ⟨1329488, by rfl⟩ : syracuseStep 1772651 = 2658977) B2658977
theorem B6065339 : Blo 1381510 6065339 := bstep (se 1 (by rfl) ⟨4549004, by rfl⟩ : syracuseStep 6065339 = 9098009) B9098009
theorem B26938655 : Blo 1381510 26938655 := bstep (se 1 (by rfl) ⟨20203991, by rfl⟩ : syracuseStep 26938655 = 40407983) B40407983
theorem B2624879 : Blo 1381510 2624879 := bstep (se 1 (by rfl) ⟨1968659, by rfl⟩ : syracuseStep 2624879 = 3937319) B3937319
theorem B1576319 : Blo 1381510 1576319 := bstep (se 1 (by rfl) ⟨1182239, by rfl⟩ : syracuseStep 1576319 = 2364479) B2364479
theorem B16190981 : Blo 1381510 16190981 := bstep (se 4 (by rfl) ⟨1517904, by rfl⟩ : syracuseStep 16190981 = 3035809) B3035809
theorem B3108599 : Blo 1381510 3108599 := bstep (se 1 (by rfl) ⟨2331449, by rfl⟩ : syracuseStep 3108599 = 4662899) B4662899
theorem B11808503 : Blo 1381510 11808503 := bstep (se 1 (by rfl) ⟨8856377, by rfl⟩ : syracuseStep 11808503 = 17712755) B17712755
theorem B12611321 : Blo 1381510 12611321 := bstep (se 2 (by rfl) ⟨4729245, by rfl⟩ : syracuseStep 12611321 = 9458491) B9458491
theorem B3108671 : Blo 1381510 3108671 := bstep (se 1 (by rfl) ⟨2331503, by rfl⟩ : syracuseStep 3108671 = 4663007) B4663007
theorem B8859455 : Blo 1381510 8859455 := bstep (se 1 (by rfl) ⟨6644591, by rfl⟩ : syracuseStep 8859455 = 13289183) B13289183
theorem B3108779 : Blo 1381510 3108779 := bstep (se 1 (by rfl) ⟨2331584, by rfl⟩ : syracuseStep 3108779 = 4663169) B4663169
theorem B5902303 : Blo 1381510 5902303 := bstep (se 1 (by rfl) ⟨4426727, by rfl⟩ : syracuseStep 5902303 = 8853455) B8853455
theorem B6639671 : Blo 1381510 6639671 := bstep (se 1 (by rfl) ⟨4979753, by rfl⟩ : syracuseStep 6639671 = 9959507) B9959507
theorem B4731007 : Blo 1381510 4731007 := bstep (se 1 (by rfl) ⟨3548255, by rfl⟩ : syracuseStep 4731007 = 7096511) B7096511
theorem B2625691 : Blo 1381510 2625691 := bstep (se 1 (by rfl) ⟨1969268, by rfl⟩ : syracuseStep 2625691 = 3938537) B3938537
theorem B3109139 : Blo 1381510 3109139 := bstep (se 1 (by rfl) ⟨2331854, by rfl⟩ : syracuseStep 3109139 = 4663709) B4663709
theorem B8409511 : Blo 1381510 8409511 := bstep (se 1 (by rfl) ⟨6307133, by rfl⟩ : syracuseStep 8409511 = 12614267) B12614267
theorem B3109319 : Blo 1381510 3109319 := bstep (se 1 (by rfl) ⟨2331989, by rfl⟩ : syracuseStep 3109319 = 4663979) B4663979
theorem B2953783 : Blo 1381510 2953783 := bstep (se 1 (by rfl) ⟨2215337, by rfl⟩ : syracuseStep 2953783 = 4430675) B4430675
theorem B3109679 : Blo 1381510 3109679 := bstep (se 1 (by rfl) ⟨2332259, by rfl⟩ : syracuseStep 3109679 = 4664519) B4664519
theorem B22713169 : Blo 1381510 22713169 := bstep (se 2 (by rfl) ⟨8517438, by rfl⟩ : syracuseStep 22713169 = 17034877) B17034877
theorem B3109769 : Blo 1381510 3109769 := bstep (se 2 (by rfl) ⟨1166163, by rfl⟩ : syracuseStep 3109769 = 2332327) B2332327
theorem B2331551 : Blo 1381510 2331551 := bstep (se 1 (by rfl) ⟨1748663, by rfl⟩ : syracuseStep 2331551 = 3497327) B3497327
theorem B4666409 : Blo 1381510 4666409 := bstep (se 2 (by rfl) ⟨1749903, by rfl⟩ : syracuseStep 4666409 = 3499807) B3499807
theorem B11203667 : Blo 1381510 11203667 := bstep (se 1 (by rfl) ⟨8402750, by rfl⟩ : syracuseStep 11203667 = 16805501) B16805501
theorem B1381531 : Blo 1381510 1381531 := bstep (se 1 (by rfl) ⟨1036148, by rfl⟩ : syracuseStep 1381531 = 2072297) B2072297
theorem B1381627 : Blo 1381510 1381627 := bstep (se 1 (by rfl) ⟨1036220, by rfl⟩ : syracuseStep 1381627 = 2072441) B2072441
theorem B1381695 : Blo 1381510 1381695 := bstep (se 1 (by rfl) ⟨1036271, by rfl⟩ : syracuseStep 1381695 = 2072543) B2072543
theorem B2954603 : Blo 1381510 2954603 := bstep (se 1 (by rfl) ⟨2215952, by rfl⟩ : syracuseStep 2954603 = 4431905) B4431905
theorem B1381863 : Blo 1381510 1381863 := bstep (se 1 (by rfl) ⟨1036397, by rfl⟩ : syracuseStep 1381863 = 2072795) B2072795
theorem B1381871 : Blo 1381510 1381871 := bstep (se 1 (by rfl) ⟨1036403, by rfl⟩ : syracuseStep 1381871 = 2072807) B2072807
theorem B17716751 : Blo 1381510 17716751 := bstep (se 1 (by rfl) ⟨13287563, by rfl⟩ : syracuseStep 17716751 = 26575127) B26575127
theorem B1381979 : Blo 1381510 1381979 := bstep (se 1 (by rfl) ⟨1036484, by rfl⟩ : syracuseStep 1381979 = 2072969) B2072969
theorem B2659961 : Blo 1381510 2659961 := bstep (se 2 (by rfl) ⟨997485, by rfl⟩ : syracuseStep 2659961 = 1994971) B1994971
theorem B3110543 : Blo 1381510 3110543 := bstep (se 1 (by rfl) ⟨2332907, by rfl⟩ : syracuseStep 3110543 = 4665815) B4665815
theorem B1382043 : Blo 1381510 1382043 := bstep (se 1 (by rfl) ⟨1036532, by rfl⟩ : syracuseStep 1382043 = 2073065) B2073065
theorem B3110633 : Blo 1381510 3110633 := bstep (se 2 (by rfl) ⟨1166487, by rfl⟩ : syracuseStep 3110633 = 2332975) B2332975
theorem B1382127 : Blo 1381510 1382127 := bstep (se 1 (by rfl) ⟨1036595, by rfl⟩ : syracuseStep 1382127 = 2073191) B2073191
theorem B1382215 : Blo 1381510 1382215 := bstep (se 1 (by rfl) ⟨1036661, by rfl⟩ : syracuseStep 1382215 = 2073323) B2073323
theorem B1382235 : Blo 1381510 1382235 := bstep (se 1 (by rfl) ⟨1036676, by rfl⟩ : syracuseStep 1382235 = 2073353) B2073353
theorem B1382303 : Blo 1381510 1382303 := bstep (se 1 (by rfl) ⟨1036727, by rfl⟩ : syracuseStep 1382303 = 2073455) B2073455
theorem B7870445 : Blo 1381510 7870445 := bstep (se 3 (by rfl) ⟨1475708, by rfl⟩ : syracuseStep 7870445 = 2951417) B2951417
theorem B26564669 : Blo 1381510 26564669 := bstep (se 3 (by rfl) ⟨4980875, by rfl⟩ : syracuseStep 26564669 = 9961751) B9961751
theorem B1382471 : Blo 1381510 1382471 := bstep (se 1 (by rfl) ⟨1036853, by rfl⟩ : syracuseStep 1382471 = 2073707) B2073707
theorem B1382631 : Blo 1381510 1382631 := bstep (se 1 (by rfl) ⟨1036973, by rfl⟩ : syracuseStep 1382631 = 2073947) B2073947
theorem B23623973 : Blo 1381510 23623973 := bstep (se 4 (by rfl) ⟨2214747, by rfl⟩ : syracuseStep 23623973 = 4429495) B4429495
theorem B7002449 : Blo 1381510 7002449 := bstep (se 2 (by rfl) ⟨2625918, by rfl⟩ : syracuseStep 7002449 = 5251837) B5251837
theorem B1382815 : Blo 1381510 1382815 := bstep (se 1 (by rfl) ⟨1037111, by rfl⟩ : syracuseStep 1382815 = 2074223) B2074223
theorem B8862119 : Blo 1381510 8862119 := bstep (se 1 (by rfl) ⟨6646589, by rfl⟩ : syracuseStep 8862119 = 13293179) B13293179
theorem B1382863 : Blo 1381510 1382863 := bstep (se 1 (by rfl) ⟨1037147, by rfl⟩ : syracuseStep 1382863 = 2074295) B2074295
theorem B1382887 : Blo 1381510 1382887 := bstep (se 1 (by rfl) ⟨1037165, by rfl⟩ : syracuseStep 1382887 = 2074331) B2074331
theorem B3111515 : Blo 1381510 3111515 := bstep (se 1 (by rfl) ⟨2333636, by rfl⟩ : syracuseStep 3111515 = 4667273) B4667273
theorem B1383003 : Blo 1381510 1383003 := bstep (se 1 (by rfl) ⟨1037252, by rfl⟩ : syracuseStep 1383003 = 2074505) B2074505
theorem B1383071 : Blo 1381510 1383071 := bstep (se 1 (by rfl) ⟨1037303, by rfl⟩ : syracuseStep 1383071 = 2074607) B2074607
theorem B1661599 : Blo 1381510 1661599 := bstep (se 1 (by rfl) ⟨1246199, by rfl⟩ : syracuseStep 1661599 = 2492399) B2492399
theorem B4668137 : Blo 1381510 4668137 := bstep (se 2 (by rfl) ⟨1750551, by rfl⟩ : syracuseStep 4668137 = 3501103) B3501103
theorem B3111659 : Blo 1381510 3111659 := bstep (se 1 (by rfl) ⟨2333744, by rfl⟩ : syracuseStep 3111659 = 4667489) B4667489
theorem B1383239 : Blo 1381510 1383239 := bstep (se 1 (by rfl) ⟨1037429, by rfl⟩ : syracuseStep 1383239 = 2074859) B2074859
theorem B1383279 : Blo 1381510 1383279 := bstep (se 1 (by rfl) ⟨1037459, by rfl⟩ : syracuseStep 1383279 = 2074919) B2074919
theorem B6388637 : Blo 1381510 6388637 := bstep (se 3 (by rfl) ⟨1197869, by rfl⟩ : syracuseStep 6388637 = 2395739) B2395739
theorem B1383335 : Blo 1381510 1383335 := bstep (se 1 (by rfl) ⟨1037501, by rfl⟩ : syracuseStep 1383335 = 2075003) B2075003
theorem B9452659 : Blo 1381510 9452659 := bstep (se 1 (by rfl) ⟨7089494, by rfl⟩ : syracuseStep 9452659 = 14178989) B14178989
theorem B4430983 : Blo 1381510 4430983 := bstep (se 1 (by rfl) ⟨3323237, by rfl⟩ : syracuseStep 4430983 = 6646475) B6646475
theorem B1555663 : Blo 1381510 1555663 := bstep (se 1 (by rfl) ⟨1166747, by rfl⟩ : syracuseStep 1555663 = 2333495) B2333495
theorem B3112271 : Blo 1381510 3112271 := bstep (se 1 (by rfl) ⟨2334203, by rfl⟩ : syracuseStep 3112271 = 4668407) B4668407
theorem B3112361 : Blo 1381510 3112361 := bstep (se 2 (by rfl) ⟨1167135, by rfl⟩ : syracuseStep 3112361 = 2334271) B2334271
theorem B3112559 : Blo 1381510 3112559 := bstep (se 1 (by rfl) ⟨2334419, by rfl⟩ : syracuseStep 3112559 = 4668839) B4668839
theorem B2072351 : Blo 1381510 2072351 := bstep (se 1 (by rfl) ⟨1554263, by rfl⟩ : syracuseStep 2072351 = 3108527) B3108527
theorem B2334575 : Blo 1381510 2334575 := bstep (se 1 (by rfl) ⟨1750931, by rfl⟩ : syracuseStep 2334575 = 3501863) B3501863
theorem B3112847 : Blo 1381510 3112847 := bstep (se 1 (by rfl) ⟨2334635, by rfl⟩ : syracuseStep 3112847 = 4669271) B4669271
theorem B3498025 : Blo 1381510 3498025 := bstep (se 2 (by rfl) ⟨1311759, by rfl⟩ : syracuseStep 3498025 = 2623519) B2623519
theorem B6308009 : Blo 1381510 6308009 := bstep (se 2 (by rfl) ⟨2365503, by rfl⟩ : syracuseStep 6308009 = 4731007) B4731007
theorem B2072759 : Blo 1381510 2072759 := bstep (se 1 (by rfl) ⟨1554569, by rfl⟩ : syracuseStep 2072759 = 3109139) B3109139
theorem B4727069 : Blo 1381510 4727069 := bstep (se 3 (by rfl) ⟨886325, by rfl⟩ : syracuseStep 4727069 = 1772651) B1772651
theorem B2072879 : Blo 1381510 2072879 := bstep (se 1 (by rfl) ⟨1554659, by rfl⟩ : syracuseStep 2072879 = 3109319) B3109319
theorem B7471487 : Blo 1381510 7471487 := bstep (se 1 (by rfl) ⟨5603615, by rfl⟩ : syracuseStep 7471487 = 11207231) B11207231
theorem B2073119 : Blo 1381510 2073119 := bstep (se 1 (by rfl) ⟨1554839, by rfl⟩ : syracuseStep 2073119 = 3109679) B3109679
theorem B2073179 : Blo 1381510 2073179 := bstep (se 1 (by rfl) ⟨1554884, by rfl⟩ : syracuseStep 2073179 = 3109769) B3109769
theorem B4203517 : Blo 1381510 4203517 := bstep (se 3 (by rfl) ⟨788159, by rfl⟩ : syracuseStep 4203517 = 1576319) B1576319
theorem B2073695 : Blo 1381510 2073695 := bstep (se 1 (by rfl) ⟨1555271, by rfl⟩ : syracuseStep 2073695 = 3110543) B3110543
theorem B6997103 : Blo 1381510 6997103 := bstep (se 1 (by rfl) ⟨5247827, by rfl⟩ : syracuseStep 6997103 = 10495655) B10495655
theorem B17720441 : Blo 1381510 17720441 := bstep (se 2 (by rfl) ⟨6645165, by rfl⟩ : syracuseStep 17720441 = 13290331) B13290331
theorem B2073755 : Blo 1381510 2073755 := bstep (se 1 (by rfl) ⟨1555316, by rfl⟩ : syracuseStep 2073755 = 3110633) B3110633
theorem B10503431 : Blo 1381510 10503431 := bstep (se 1 (by rfl) ⟨7877573, by rfl⟩ : syracuseStep 10503431 = 15755147) B15755147
theorem B15746399 : Blo 1381510 15746399 := bstep (se 1 (by rfl) ⟨11809799, by rfl⟩ : syracuseStep 15746399 = 23619599) B23619599
theorem B2803099 : Blo 1381510 2803099 := bstep (se 1 (by rfl) ⟨2102324, by rfl⟩ : syracuseStep 2803099 = 4204649) B4204649
theorem B3499433 : Blo 1381510 3499433 := bstep (se 2 (by rfl) ⟨1312287, by rfl⟩ : syracuseStep 3499433 = 2624575) B2624575
theorem B5907977 : Blo 1381510 5907977 := bstep (se 2 (by rfl) ⟨2215491, by rfl⟩ : syracuseStep 5907977 = 4430983) B4430983
theorem B2074217 : Blo 1381510 2074217 := bstep (se 2 (by rfl) ⟨777831, by rfl⟩ : syracuseStep 2074217 = 1555663) B1555663
theorem B5908079 : Blo 1381510 5908079 := bstep (se 1 (by rfl) ⟨4431059, by rfl⟩ : syracuseStep 5908079 = 8862119) B8862119
theorem B2074343 : Blo 1381510 2074343 := bstep (se 1 (by rfl) ⟨1555757, by rfl⟩ : syracuseStep 2074343 = 3111515) B3111515
theorem B2074439 : Blo 1381510 2074439 := bstep (se 1 (by rfl) ⟨1555829, by rfl⟩ : syracuseStep 2074439 = 3111659) B3111659
theorem B17959103 : Blo 1381510 17959103 := bstep (se 1 (by rfl) ⟨13469327, by rfl⟩ : syracuseStep 17959103 = 26938655) B26938655
theorem B6998237 : Blo 1381510 6998237 := bstep (se 3 (by rfl) ⟨1312169, by rfl⟩ : syracuseStep 6998237 = 2624339) B2624339
theorem B2074847 : Blo 1381510 2074847 := bstep (se 1 (by rfl) ⟨1556135, by rfl⟩ : syracuseStep 2074847 = 3112271) B3112271
theorem B2074907 : Blo 1381510 2074907 := bstep (se 1 (by rfl) ⟨1556180, by rfl⟩ : syracuseStep 2074907 = 3112361) B3112361
theorem B7473545 : Blo 1381510 7473545 := bstep (se 2 (by rfl) ⟨2802579, by rfl⟩ : syracuseStep 7473545 = 5605159) B5605159
theorem B3737993 : Blo 1381510 3737993 := bstep (se 2 (by rfl) ⟨1401747, by rfl⟩ : syracuseStep 3737993 = 2803495) B2803495
theorem B2075039 : Blo 1381510 2075039 := bstep (se 1 (by rfl) ⟨1556279, by rfl⟩ : syracuseStep 2075039 = 3112559) B3112559
theorem B8407547 : Blo 1381510 8407547 := bstep (se 1 (by rfl) ⟨6305660, by rfl⟩ : syracuseStep 8407547 = 12611321) B12611321
theorem B2075231 : Blo 1381510 2075231 := bstep (se 1 (by rfl) ⟨1556423, by rfl⟩ : syracuseStep 2075231 = 3112847) B3112847
theorem B4426447 : Blo 1381510 4426447 := bstep (se 1 (by rfl) ⟨3319835, by rfl⟩ : syracuseStep 4426447 = 6639671) B6639671
theorem B3500891 : Blo 1381510 3500891 := bstep (se 1 (by rfl) ⟨2625668, by rfl⟩ : syracuseStep 3500891 = 5251337) B5251337
theorem B3500921 : Blo 1381510 3500921 := bstep (se 2 (by rfl) ⟨1312845, by rfl⟩ : syracuseStep 3500921 = 2625691) B2625691
theorem B10497113 : Blo 1381510 10497113 := bstep (se 2 (by rfl) ⟨3936417, by rfl⟩ : syracuseStep 10497113 = 7872835) B7872835
theorem B7474301 : Blo 1381510 7474301 := bstep (se 3 (by rfl) ⟨1401431, by rfl⟩ : syracuseStep 7474301 = 2802863) B2802863
theorem B16174237 : Blo 1381510 16174237 := bstep (se 3 (by rfl) ⟨3032669, by rfl⟩ : syracuseStep 16174237 = 6065339) B6065339
theorem B5319863 : Blo 1381510 5319863 := bstep (se 1 (by rfl) ⟨3989897, by rfl⟩ : syracuseStep 5319863 = 7979795) B7979795
theorem B3108455 : Blo 1381510 3108455 := bstep (se 1 (by rfl) ⟨2331341, by rfl⟩ : syracuseStep 3108455 = 4662683) B4662683
theorem B2952929 : Blo 1381510 2952929 := bstep (se 2 (by rfl) ⟨1107348, by rfl⟩ : syracuseStep 2952929 = 2214697) B2214697
theorem B1773307 : Blo 1381510 1773307 := bstep (se 1 (by rfl) ⟨1329980, by rfl⟩ : syracuseStep 1773307 = 2659961) B2659961
theorem B5246963 : Blo 1381510 5246963 := bstep (se 1 (by rfl) ⟨3935222, by rfl⟩ : syracuseStep 5246963 = 7870445) B7870445
theorem B12603545 : Blo 1381510 12603545 := bstep (se 2 (by rfl) ⟨4726329, by rfl⟩ : syracuseStep 12603545 = 9452659) B9452659
theorem B15749315 : Blo 1381510 15749315 := bstep (se 1 (by rfl) ⟨11811986, by rfl⟩ : syracuseStep 15749315 = 23623973) B23623973
theorem B1749215 : Blo 1381510 1749215 := bstep (se 1 (by rfl) ⟨1311911, by rfl⟩ : syracuseStep 1749215 = 2623823) B2623823
theorem B43757825 : Blo 1381510 43757825 := bstep (se 2 (by rfl) ⟨16409184, by rfl⟩ : syracuseStep 43757825 = 32818369) B32818369
theorem B4665761 : Blo 1381510 4665761 := bstep (se 2 (by rfl) ⟨1749660, by rfl⟩ : syracuseStep 4665761 = 3499321) B3499321
theorem B1749919 : Blo 1381510 1749919 := bstep (se 1 (by rfl) ⟨1312439, by rfl⟩ : syracuseStep 1749919 = 2624879) B2624879
theorem B4985837 : Blo 1381510 4985837 := bstep (se 3 (by rfl) ⟨934844, by rfl⟩ : syracuseStep 4985837 = 1869689) B1869689
theorem B10793987 : Blo 1381510 10793987 := bstep (se 1 (by rfl) ⟨8095490, by rfl⟩ : syracuseStep 10793987 = 16190981) B16190981
theorem B17036365 : Blo 1381510 17036365 := bstep (se 3 (by rfl) ⟨3194318, by rfl⟩ : syracuseStep 17036365 = 6388637) B6388637
theorem B1381567 : Blo 1381510 1381567 := bstep (se 1 (by rfl) ⟨1036175, by rfl⟩ : syracuseStep 1381567 = 2072351) B2072351
theorem B7869737 : Blo 1381510 7869737 := bstep (se 2 (by rfl) ⟨2951151, by rfl⟩ : syracuseStep 7869737 = 5902303) B5902303
theorem B7869919 : Blo 1381510 7869919 := bstep (se 1 (by rfl) ⟨5902439, by rfl⟩ : syracuseStep 7869919 = 11804879) B11804879
theorem B1381855 : Blo 1381510 1381855 := bstep (se 1 (by rfl) ⟨1036391, by rfl⟩ : syracuseStep 1381855 = 2072783) B2072783
theorem B1381887 : Blo 1381510 1381887 := bstep (se 1 (by rfl) ⟨1036415, by rfl⟩ : syracuseStep 1381887 = 2072831) B2072831
theorem B15750773 : Blo 1381510 15750773 := bstep (se 5 (by rfl) ⟨738317, by rfl⟩ : syracuseStep 15750773 = 1476635) B1476635
theorem B5986025 : Blo 1381510 5986025 := bstep (se 2 (by rfl) ⟨2244759, by rfl⟩ : syracuseStep 5986025 = 4489519) B4489519
theorem B11212681 : Blo 1381510 11212681 := bstep (se 2 (by rfl) ⟨4204755, by rfl⟩ : syracuseStep 11212681 = 8409511) B8409511
theorem B1554367 : Blo 1381510 1554367 := bstep (se 1 (by rfl) ⟨1165775, by rfl⟩ : syracuseStep 1554367 = 2331551) B2331551
theorem B3110939 : Blo 1381510 3110939 := bstep (se 1 (by rfl) ⟨2333204, by rfl⟩ : syracuseStep 3110939 = 4666409) B4666409
theorem B1382431 : Blo 1381510 1382431 := bstep (se 1 (by rfl) ⟨1036823, by rfl⟩ : syracuseStep 1382431 = 2073647) B2073647
theorem B7469111 : Blo 1381510 7469111 := bstep (se 1 (by rfl) ⟨5601833, by rfl⟩ : syracuseStep 7469111 = 11203667) B11203667
theorem B3938377 : Blo 1381510 3938377 := bstep (se 2 (by rfl) ⟨1476891, by rfl⟩ : syracuseStep 3938377 = 2953783) B2953783
theorem B1382511 : Blo 1381510 1382511 := bstep (se 1 (by rfl) ⟨1036883, by rfl⟩ : syracuseStep 1382511 = 2073767) B2073767
theorem B8861861 : Blo 1381510 8861861 := bstep (se 4 (by rfl) ⟨830799, by rfl⟩ : syracuseStep 8861861 = 1661599) B1661599
theorem B7878941 : Blo 1381510 7878941 := bstep (se 3 (by rfl) ⟨1477301, by rfl⟩ : syracuseStep 7878941 = 2954603) B2954603
theorem B11811167 : Blo 1381510 11811167 := bstep (se 1 (by rfl) ⟨8858375, by rfl⟩ : syracuseStep 11811167 = 17716751) B17716751
theorem B1382759 : Blo 1381510 1382759 := bstep (se 1 (by rfl) ⟨1037069, by rfl⟩ : syracuseStep 1382759 = 2074139) B2074139
theorem B30284225 : Blo 1381510 30284225 := bstep (se 2 (by rfl) ⟨11356584, by rfl⟩ : syracuseStep 30284225 = 22713169) B22713169
theorem B1383015 : Blo 1381510 1383015 := bstep (se 1 (by rfl) ⟨1037261, by rfl⟩ : syracuseStep 1383015 = 2074523) B2074523
theorem B1383039 : Blo 1381510 1383039 := bstep (se 1 (by rfl) ⟨1037279, by rfl⟩ : syracuseStep 1383039 = 2074559) B2074559
theorem B17709779 : Blo 1381510 17709779 := bstep (se 1 (by rfl) ⟨13282334, by rfl⟩ : syracuseStep 17709779 = 26564669) B26564669
theorem B1383163 : Blo 1381510 1383163 := bstep (se 1 (by rfl) ⟨1037372, by rfl⟩ : syracuseStep 1383163 = 2074745) B2074745
theorem B7002935 : Blo 1381510 7002935 := bstep (se 1 (by rfl) ⟨5252201, by rfl⟩ : syracuseStep 7002935 = 10504403) B10504403
theorem B4668299 : Blo 1381510 4668299 := bstep (se 1 (by rfl) ⟨3501224, by rfl⟩ : syracuseStep 4668299 = 7002449) B7002449
theorem B1383419 : Blo 1381510 1383419 := bstep (se 1 (by rfl) ⟨1037564, by rfl⟩ : syracuseStep 1383419 = 2075129) B2075129
theorem B1383455 : Blo 1381510 1383455 := bstep (se 1 (by rfl) ⟨1037591, by rfl⟩ : syracuseStep 1383455 = 2075183) B2075183
theorem B5758087 : Blo 1381510 5758087 := bstep (se 1 (by rfl) ⟨4318565, by rfl⟩ : syracuseStep 5758087 = 8637131) B8637131
theorem B3112091 : Blo 1381510 3112091 := bstep (se 1 (by rfl) ⟨2334068, by rfl⟩ : syracuseStep 3112091 = 4668137) B4668137
theorem B2072399 : Blo 1381510 2072399 := bstep (se 1 (by rfl) ⟨1554299, by rfl⟩ : syracuseStep 2072399 = 3108599) B3108599
theorem B7872335 : Blo 1381510 7872335 := bstep (se 1 (by rfl) ⟨5904251, by rfl⟩ : syracuseStep 7872335 = 11808503) B11808503
theorem B2072447 : Blo 1381510 2072447 := bstep (se 1 (by rfl) ⟨1554335, by rfl⟩ : syracuseStep 2072447 = 3108671) B3108671
theorem B5906303 : Blo 1381510 5906303 := bstep (se 1 (by rfl) ⟨4429727, by rfl⟩ : syracuseStep 5906303 = 8859455) B8859455
theorem B1556383 : Blo 1381510 1556383 := bstep (se 1 (by rfl) ⟨1167287, by rfl⟩ : syracuseStep 1556383 = 2334575) B2334575
theorem B2072519 : Blo 1381510 2072519 := bstep (se 1 (by rfl) ⟨1554389, by rfl⟩ : syracuseStep 2072519 = 3108779) B3108779
theorem B5251169 : Blo 1381510 5251169 := bstep (se 2 (by rfl) ⟨1969188, by rfl⟩ : syracuseStep 5251169 = 3938377) B3938377
theorem B11813627 : Blo 1381510 11813627 := bstep (se 1 (by rfl) ⟨8860220, by rfl⟩ : syracuseStep 11813627 = 17720441) B17720441
theorem B19923965 : Blo 1381510 19923965 := bstep (se 3 (by rfl) ⟨3735743, by rfl⟩ : syracuseStep 19923965 = 7471487) B7471487
theorem B3990683 : Blo 1381510 3990683 := bstep (se 1 (by rfl) ⟨2993012, by rfl⟩ : syracuseStep 3990683 = 5986025) B5986025
theorem B5604689 : Blo 1381510 5604689 := bstep (se 2 (by rfl) ⟨2101758, by rfl⟩ : syracuseStep 5604689 = 4203517) B4203517
theorem B2073959 : Blo 1381510 2073959 := bstep (se 1 (by rfl) ⟨1555469, by rfl⟩ : syracuseStep 2073959 = 3110939) B3110939
theorem B5907907 : Blo 1381510 5907907 := bstep (se 1 (by rfl) ⟨4430930, by rfl⟩ : syracuseStep 5907907 = 8861861) B8861861
theorem B7677449 : Blo 1381510 7677449 := bstep (se 2 (by rfl) ⟨2879043, by rfl⟩ : syracuseStep 7677449 = 5758087) B5758087
theorem B5252627 : Blo 1381510 5252627 := bstep (se 1 (by rfl) ⟨3939470, by rfl⟩ : syracuseStep 5252627 = 7878941) B7878941
theorem B7874111 : Blo 1381510 7874111 := bstep (se 1 (by rfl) ⟨5905583, by rfl⟩ : syracuseStep 7874111 = 11811167) B11811167
theorem B4982363 : Blo 1381510 4982363 := bstep (se 1 (by rfl) ⟨3736772, by rfl⟩ : syracuseStep 4982363 = 7473545) B7473545
theorem B5605031 : Blo 1381510 5605031 := bstep (se 1 (by rfl) ⟨4203773, by rfl⟩ : syracuseStep 5605031 = 8407547) B8407547
theorem B11806519 : Blo 1381510 11806519 := bstep (se 1 (by rfl) ⟨8854889, by rfl⟩ : syracuseStep 11806519 = 17709779) B17709779
theorem B3737465 : Blo 1381510 3737465 := bstep (se 2 (by rfl) ⟨1401549, by rfl⟩ : syracuseStep 3737465 = 2803099) B2803099
theorem B6998075 : Blo 1381510 6998075 := bstep (se 1 (by rfl) ⟨5248556, by rfl⟩ : syracuseStep 6998075 = 10497113) B10497113
theorem B4982867 : Blo 1381510 4982867 := bstep (se 1 (by rfl) ⟨3737150, by rfl⟩ : syracuseStep 4982867 = 7474301) B7474301
theorem B2074727 : Blo 1381510 2074727 := bstep (se 1 (by rfl) ⟨1556045, by rfl⟩ : syracuseStep 2074727 = 3112091) B3112091
theorem B1968619 : Blo 1381510 1968619 := bstep (se 1 (by rfl) ⟨1476464, by rfl⟩ : syracuseStep 1968619 = 2952929) B2952929
theorem B2075177 : Blo 1381510 2075177 := bstep (se 2 (by rfl) ⟨778191, by rfl⟩ : syracuseStep 2075177 = 1556383) B1556383
theorem B466750133 : Blo 1381510 466750133 := bstep (se 5 (by rfl) ⟨21878912, by rfl⟩ : syracuseStep 466750133 = 43757825) B43757825
theorem B4664033 : Blo 1381510 4664033 := bstep (se 2 (by rfl) ⟨1749012, by rfl⟩ : syracuseStep 4664033 = 3498025) B3498025
theorem B4205339 : Blo 1381510 4205339 := bstep (se 1 (by rfl) ⟨3154004, by rfl⟩ : syracuseStep 4205339 = 6308009) B6308009
theorem B4664573 : Blo 1381510 4664573 := bstep (se 3 (by rfl) ⟨874607, by rfl⟩ : syracuseStep 4664573 = 1749215) B1749215
theorem B4664735 : Blo 1381510 4664735 := bstep (se 1 (by rfl) ⟨3498551, by rfl⟩ : syracuseStep 4664735 = 6997103) B6997103
theorem B5246491 : Blo 1381510 5246491 := bstep (se 1 (by rfl) ⟨3934868, by rfl⟩ : syracuseStep 5246491 = 7869737) B7869737
theorem B10497599 : Blo 1381510 10497599 := bstep (se 1 (by rfl) ⟨7873199, by rfl⟩ : syracuseStep 10497599 = 15746399) B15746399
theorem B5901929 : Blo 1381510 5901929 := bstep (se 2 (by rfl) ⟨2213223, by rfl⟩ : syracuseStep 5901929 = 4426447) B4426447
theorem B11972735 : Blo 1381510 11972735 := bstep (se 1 (by rfl) ⟨8979551, by rfl⟩ : syracuseStep 11972735 = 17959103) B17959103
theorem B4665491 : Blo 1381510 4665491 := bstep (se 1 (by rfl) ⟨3499118, by rfl⟩ : syracuseStep 4665491 = 6998237) B6998237
theorem B21565649 : Blo 1381510 21565649 := bstep (se 2 (by rfl) ⟨8087118, by rfl⟩ : syracuseStep 21565649 = 16174237) B16174237
theorem B20189483 : Blo 1381510 20189483 := bstep (se 1 (by rfl) ⟨15142112, by rfl⟩ : syracuseStep 20189483 = 30284225) B30284225
theorem B2364409 : Blo 1381510 2364409 := bstep (se 2 (by rfl) ⟨886653, by rfl⟩ : syracuseStep 2364409 = 1773307) B1773307
theorem B1381599 : Blo 1381510 1381599 := bstep (se 1 (by rfl) ⟨1036199, by rfl⟩ : syracuseStep 1381599 = 2072399) B2072399
theorem B5248223 : Blo 1381510 5248223 := bstep (se 1 (by rfl) ⟨3936167, by rfl⟩ : syracuseStep 5248223 = 7872335) B7872335
theorem B1381631 : Blo 1381510 1381631 := bstep (se 1 (by rfl) ⟨1036223, by rfl⟩ : syracuseStep 1381631 = 2072447) B2072447
theorem B3937535 : Blo 1381510 3937535 := bstep (se 1 (by rfl) ⟨2953151, by rfl⟩ : syracuseStep 3937535 = 5906303) B5906303
theorem B1381679 : Blo 1381510 1381679 := bstep (se 1 (by rfl) ⟨1036259, by rfl⟩ : syracuseStep 1381679 = 2072519) B2072519
theorem B8402363 : Blo 1381510 8402363 := bstep (se 1 (by rfl) ⟨6301772, by rfl⟩ : syracuseStep 8402363 = 12603545) B12603545
theorem B1381839 : Blo 1381510 1381839 := bstep (se 1 (by rfl) ⟨1036379, by rfl⟩ : syracuseStep 1381839 = 2072759) B2072759
theorem B460543445 : Blo 1381510 460543445 := bstep (se 7 (by rfl) ⟨5396993, by rfl⟩ : syracuseStep 460543445 = 10793987) B10793987
theorem B10499543 : Blo 1381510 10499543 := bstep (se 1 (by rfl) ⟨7874657, by rfl⟩ : syracuseStep 10499543 = 15749315) B15749315
theorem B3151379 : Blo 1381510 3151379 := bstep (se 1 (by rfl) ⟨2363534, by rfl⟩ : syracuseStep 3151379 = 4727069) B4727069
theorem B1381919 : Blo 1381510 1381919 := bstep (se 1 (by rfl) ⟨1036439, by rfl⟩ : syracuseStep 1381919 = 2072879) B2072879
theorem B3110507 : Blo 1381510 3110507 := bstep (se 1 (by rfl) ⟨2332880, by rfl⟩ : syracuseStep 3110507 = 4665761) B4665761
theorem B1382079 : Blo 1381510 1382079 := bstep (se 1 (by rfl) ⟨1036559, by rfl⟩ : syracuseStep 1382079 = 2073119) B2073119
theorem B1382119 : Blo 1381510 1382119 := bstep (se 1 (by rfl) ⟨1036589, by rfl⟩ : syracuseStep 1382119 = 2073179) B2073179
theorem B3323891 : Blo 1381510 3323891 := bstep (se 1 (by rfl) ⟨2492918, by rfl⟩ : syracuseStep 3323891 = 4985837) B4985837
theorem B1382463 : Blo 1381510 1382463 := bstep (se 1 (by rfl) ⟨1036847, by rfl⟩ : syracuseStep 1382463 = 2073695) B2073695
theorem B1382503 : Blo 1381510 1382503 := bstep (se 1 (by rfl) ⟨1036877, by rfl⟩ : syracuseStep 1382503 = 2073755) B2073755
theorem B7002287 : Blo 1381510 7002287 := bstep (se 1 (by rfl) ⟨5251715, by rfl⟩ : syracuseStep 7002287 = 10503431) B10503431
theorem B2332955 : Blo 1381510 2332955 := bstep (se 1 (by rfl) ⟨1749716, by rfl⟩ : syracuseStep 2332955 = 3499433) B3499433
theorem B3938651 : Blo 1381510 3938651 := bstep (se 1 (by rfl) ⟨2953988, by rfl⟩ : syracuseStep 3938651 = 5907977) B5907977
theorem B9967981 : Blo 1381510 9967981 := bstep (se 3 (by rfl) ⟨1868996, by rfl⟩ : syracuseStep 9967981 = 3737993) B3737993
theorem B1382811 : Blo 1381510 1382811 := bstep (se 1 (by rfl) ⟨1037108, by rfl⟩ : syracuseStep 1382811 = 2074217) B2074217
theorem B3938719 : Blo 1381510 3938719 := bstep (se 1 (by rfl) ⟨2954039, by rfl⟩ : syracuseStep 3938719 = 5908079) B5908079
theorem B10500515 : Blo 1381510 10500515 := bstep (se 1 (by rfl) ⟨7875386, by rfl⟩ : syracuseStep 10500515 = 15750773) B15750773
theorem B1382895 : Blo 1381510 1382895 := bstep (se 1 (by rfl) ⟨1037171, by rfl⟩ : syracuseStep 1382895 = 2074343) B2074343
theorem B2333225 : Blo 1381510 2333225 := bstep (se 2 (by rfl) ⟨874959, by rfl⟩ : syracuseStep 2333225 = 1749919) B1749919
theorem B1382959 : Blo 1381510 1382959 := bstep (se 1 (by rfl) ⟨1037219, by rfl⟩ : syracuseStep 1382959 = 2074439) B2074439
theorem B4979407 : Blo 1381510 4979407 := bstep (se 1 (by rfl) ⟨3734555, by rfl⟩ : syracuseStep 4979407 = 7469111) B7469111
theorem B22715153 : Blo 1381510 22715153 := bstep (se 2 (by rfl) ⟨8518182, by rfl⟩ : syracuseStep 22715153 = 17036365) B17036365
theorem B1383231 : Blo 1381510 1383231 := bstep (se 1 (by rfl) ⟨1037423, by rfl⟩ : syracuseStep 1383231 = 2074847) B2074847
theorem B1383271 : Blo 1381510 1383271 := bstep (se 1 (by rfl) ⟨1037453, by rfl⟩ : syracuseStep 1383271 = 2074907) B2074907
theorem B1383359 : Blo 1381510 1383359 := bstep (se 1 (by rfl) ⟨1037519, by rfl⟩ : syracuseStep 1383359 = 2075039) B2075039
theorem B1383487 : Blo 1381510 1383487 := bstep (se 1 (by rfl) ⟨1037615, by rfl⟩ : syracuseStep 1383487 = 2075231) B2075231
theorem B4668623 : Blo 1381510 4668623 := bstep (se 1 (by rfl) ⟨3501467, by rfl⟩ : syracuseStep 4668623 = 7002935) B7002935
theorem B2333927 : Blo 1381510 2333927 := bstep (se 1 (by rfl) ⟨1750445, by rfl⟩ : syracuseStep 2333927 = 3500891) B3500891
theorem B2333947 : Blo 1381510 2333947 := bstep (se 1 (by rfl) ⟨1750460, by rfl⟩ : syracuseStep 2333947 = 3500921) B3500921
theorem B3112199 : Blo 1381510 3112199 := bstep (se 1 (by rfl) ⟨2334149, by rfl⟩ : syracuseStep 3112199 = 4668299) B4668299
theorem B10493225 : Blo 1381510 10493225 := bstep (se 2 (by rfl) ⟨3934959, by rfl⟩ : syracuseStep 10493225 = 7869919) B7869919
theorem B3546575 : Blo 1381510 3546575 := bstep (se 1 (by rfl) ⟨2659931, by rfl⟩ : syracuseStep 3546575 = 5319863) B5319863
theorem B2072303 : Blo 1381510 2072303 := bstep (se 1 (by rfl) ⟨1554227, by rfl⟩ : syracuseStep 2072303 = 3108455) B3108455
theorem B14950241 : Blo 1381510 14950241 := bstep (se 2 (by rfl) ⟨5606340, by rfl⟩ : syracuseStep 14950241 = 11212681) B11212681
theorem B2072489 : Blo 1381510 2072489 := bstep (se 2 (by rfl) ⟨777183, by rfl⟩ : syracuseStep 2072489 = 1554367) B1554367
theorem B3497975 : Blo 1381510 3497975 := bstep (se 1 (by rfl) ⟨2623481, by rfl⟩ : syracuseStep 3497975 = 5246963) B5246963
theorem B14377099 : Blo 1381510 14377099 := bstep (se 1 (by rfl) ⟨10782824, by rfl⟩ : syracuseStep 14377099 = 21565649) B21565649
theorem B13459655 : Blo 1381510 13459655 := bstep (se 1 (by rfl) ⟨10094741, by rfl⟩ : syracuseStep 13459655 = 20189483) B20189483
theorem B5251625 : Blo 1381510 5251625 := bstep (se 2 (by rfl) ⟨1969359, by rfl⟩ : syracuseStep 5251625 = 3938719) B3938719
theorem B3498815 : Blo 1381510 3498815 := bstep (se 1 (by rfl) ⟨2624111, by rfl⟩ : syracuseStep 3498815 = 5248223) B5248223
theorem B3736459 : Blo 1381510 3736459 := bstep (se 1 (by rfl) ⟨2802344, by rfl⟩ : syracuseStep 3736459 = 5604689) B5604689
theorem B307028963 : Blo 1381510 307028963 := bstep (se 1 (by rfl) ⟨230271722, by rfl⟩ : syracuseStep 307028963 = 460543445) B460543445
theorem B2073671 : Blo 1381510 2073671 := bstep (se 1 (by rfl) ⟨1555253, by rfl⟩ : syracuseStep 2073671 = 3110507) B3110507
theorem B3736687 : Blo 1381510 3736687 := bstep (se 1 (by rfl) ⟨2802515, by rfl⟩ : syracuseStep 3736687 = 5605031) B5605031
theorem B2491643 : Blo 1381510 2491643 := bstep (se 1 (by rfl) ⟨1868732, by rfl⟩ : syracuseStep 2491643 = 3737465) B3737465
theorem B311166755 : Blo 1381510 311166755 := bstep (se 1 (by rfl) ⟨233375066, by rfl⟩ : syracuseStep 311166755 = 466750133) B466750133
theorem B2803559 : Blo 1381510 2803559 := bstep (se 1 (by rfl) ⟨2102669, by rfl⟩ : syracuseStep 2803559 = 4205339) B4205339
theorem B2074799 : Blo 1381510 2074799 := bstep (se 1 (by rfl) ⟨1556099, by rfl⟩ : syracuseStep 2074799 = 3112199) B3112199
theorem B6998399 : Blo 1381510 6998399 := bstep (se 1 (by rfl) ⟨5248799, by rfl⟩ : syracuseStep 6998399 = 10497599) B10497599
theorem B3934619 : Blo 1381510 3934619 := bstep (se 1 (by rfl) ⟨2950964, by rfl⟩ : syracuseStep 3934619 = 5901929) B5901929
theorem B12610181 : Blo 1381510 12610181 := bstep (se 4 (by rfl) ⟨1182204, by rfl⟩ : syracuseStep 12610181 = 2364409) B2364409
theorem B3500779 : Blo 1381510 3500779 := bstep (se 1 (by rfl) ⟨2625584, by rfl⟩ : syracuseStep 3500779 = 5251169) B5251169
theorem B7981823 : Blo 1381510 7981823 := bstep (se 1 (by rfl) ⟨5986367, by rfl⟩ : syracuseStep 7981823 = 11972735) B11972735
theorem B13290641 : Blo 1381510 13290641 := bstep (se 2 (by rfl) ⟨4983990, by rfl⟩ : syracuseStep 13290641 = 9967981) B9967981
theorem B7875751 : Blo 1381510 7875751 := bstep (se 1 (by rfl) ⟨5906813, by rfl⟩ : syracuseStep 7875751 = 11813627) B11813627
theorem B2624825 : Blo 1381510 2624825 := bstep (se 2 (by rfl) ⟨984309, by rfl⟩ : syracuseStep 2624825 = 1968619) B1968619
theorem B13282643 : Blo 1381510 13282643 := bstep (se 1 (by rfl) ⟨9961982, by rfl⟩ : syracuseStep 13282643 = 19923965) B19923965
theorem B2625023 : Blo 1381510 2625023 := bstep (se 1 (by rfl) ⟨1968767, by rfl⟩ : syracuseStep 2625023 = 3937535) B3937535
theorem B6639209 : Blo 1381510 6639209 := bstep (se 2 (by rfl) ⟨2489703, by rfl⟩ : syracuseStep 6639209 = 4979407) B4979407
theorem B6999695 : Blo 1381510 6999695 := bstep (se 1 (by rfl) ⟨5249771, by rfl⟩ : syracuseStep 6999695 = 10499543) B10499543
theorem B2100919 : Blo 1381510 2100919 := bstep (se 1 (by rfl) ⟨1575689, by rfl⟩ : syracuseStep 2100919 = 3151379) B3151379
theorem B3501751 : Blo 1381510 3501751 := bstep (se 1 (by rfl) ⟨2626313, by rfl⟩ : syracuseStep 3501751 = 5252627) B5252627
theorem B3321575 : Blo 1381510 3321575 := bstep (se 1 (by rfl) ⟨2491181, by rfl⟩ : syracuseStep 3321575 = 4982363) B4982363
theorem B2215927 : Blo 1381510 2215927 := bstep (se 1 (by rfl) ⟨1661945, by rfl⟩ : syracuseStep 2215927 = 3323891) B3323891
theorem B4665383 : Blo 1381510 4665383 := bstep (se 1 (by rfl) ⟨3499037, by rfl⟩ : syracuseStep 4665383 = 6998075) B6998075
theorem B3321911 : Blo 1381510 3321911 := bstep (se 1 (by rfl) ⟨2491433, by rfl⟩ : syracuseStep 3321911 = 4982867) B4982867
theorem B2625767 : Blo 1381510 2625767 := bstep (se 1 (by rfl) ⟨1969325, by rfl⟩ : syracuseStep 2625767 = 3938651) B3938651
theorem B7000343 : Blo 1381510 7000343 := bstep (se 1 (by rfl) ⟨5250257, by rfl⟩ : syracuseStep 7000343 = 10500515) B10500515
theorem B3109355 : Blo 1381510 3109355 := bstep (se 1 (by rfl) ⟨2332016, by rfl⟩ : syracuseStep 3109355 = 4664033) B4664033
theorem B15143435 : Blo 1381510 15143435 := bstep (se 1 (by rfl) ⟨11357576, by rfl⟩ : syracuseStep 15143435 = 22715153) B22715153
theorem B7877209 : Blo 1381510 7877209 := bstep (se 2 (by rfl) ⟨2953953, by rfl⟩ : syracuseStep 7877209 = 5907907) B5907907
theorem B3109715 : Blo 1381510 3109715 := bstep (se 1 (by rfl) ⟨2332286, by rfl⟩ : syracuseStep 3109715 = 4664573) B4664573
theorem B3109823 : Blo 1381510 3109823 := bstep (se 1 (by rfl) ⟨2332367, by rfl⟩ : syracuseStep 3109823 = 4664735) B4664735
theorem B2364383 : Blo 1381510 2364383 := bstep (se 1 (by rfl) ⟨1773287, by rfl⟩ : syracuseStep 2364383 = 3546575) B3546575
theorem B15742025 : Blo 1381510 15742025 := bstep (se 2 (by rfl) ⟨5903259, by rfl⟩ : syracuseStep 15742025 = 11806519) B11806519
theorem B1381535 : Blo 1381510 1381535 := bstep (se 1 (by rfl) ⟨1036151, by rfl⟩ : syracuseStep 1381535 = 2072303) B2072303
theorem B9966827 : Blo 1381510 9966827 := bstep (se 1 (by rfl) ⟨7475120, by rfl⟩ : syracuseStep 9966827 = 14950241) B14950241
theorem B1381659 : Blo 1381510 1381659 := bstep (se 1 (by rfl) ⟨1036244, by rfl⟩ : syracuseStep 1381659 = 2072489) B2072489
theorem B2331983 : Blo 1381510 2331983 := bstep (se 1 (by rfl) ⟨1748987, by rfl⟩ : syracuseStep 2331983 = 3497975) B3497975
theorem B3110327 : Blo 1381510 3110327 := bstep (se 1 (by rfl) ⟨2332745, by rfl⟩ : syracuseStep 3110327 = 4665491) B4665491
theorem B2660455 : Blo 1381510 2660455 := bstep (se 1 (by rfl) ⟨1995341, by rfl⟩ : syracuseStep 2660455 = 3990683) B3990683
theorem B1382639 : Blo 1381510 1382639 := bstep (se 1 (by rfl) ⟨1036979, by rfl⟩ : syracuseStep 1382639 = 2073959) B2073959
theorem B5601575 : Blo 1381510 5601575 := bstep (se 1 (by rfl) ⟨4201181, by rfl⟩ : syracuseStep 5601575 = 8402363) B8402363
theorem B5118299 : Blo 1381510 5118299 := bstep (se 1 (by rfl) ⟨3838724, by rfl⟩ : syracuseStep 5118299 = 7677449) B7677449
theorem B5249407 : Blo 1381510 5249407 := bstep (se 1 (by rfl) ⟨3937055, by rfl⟩ : syracuseStep 5249407 = 7874111) B7874111
theorem B1383151 : Blo 1381510 1383151 := bstep (se 1 (by rfl) ⟨1037363, by rfl⟩ : syracuseStep 1383151 = 2074727) B2074727
theorem B4668191 : Blo 1381510 4668191 := bstep (se 1 (by rfl) ⟨3501143, by rfl⟩ : syracuseStep 4668191 = 7002287) B7002287
theorem B1555303 : Blo 1381510 1555303 := bstep (se 1 (by rfl) ⟨1166477, by rfl⟩ : syracuseStep 1555303 = 2332955) B2332955
theorem B3111929 : Blo 1381510 3111929 := bstep (se 2 (by rfl) ⟨1166973, by rfl⟩ : syracuseStep 3111929 = 2333947) B2333947
theorem B1555483 : Blo 1381510 1555483 := bstep (se 1 (by rfl) ⟨1166612, by rfl⟩ : syracuseStep 1555483 = 2333225) B2333225
theorem B1383451 : Blo 1381510 1383451 := bstep (se 1 (by rfl) ⟨1037588, by rfl⟩ : syracuseStep 1383451 = 2075177) B2075177
theorem B6995321 : Blo 1381510 6995321 := bstep (se 2 (by rfl) ⟨2623245, by rfl⟩ : syracuseStep 6995321 = 5246491) B5246491
theorem B3112415 : Blo 1381510 3112415 := bstep (se 1 (by rfl) ⟨2334311, by rfl⟩ : syracuseStep 3112415 = 4668623) B4668623
theorem B1555951 : Blo 1381510 1555951 := bstep (se 1 (by rfl) ⟨1166963, by rfl⟩ : syracuseStep 1555951 = 2333927) B2333927
theorem B6995483 : Blo 1381510 6995483 := bstep (se 1 (by rfl) ⟨5246612, by rfl⟩ : syracuseStep 6995483 = 10493225) B10493225
theorem B3547273 : Blo 1381510 3547273 := bstep (se 2 (by rfl) ⟨1330227, by rfl⟩ : syracuseStep 3547273 = 2660455) B2660455
theorem B19169465 : Blo 1381510 19169465 := bstep (se 2 (by rfl) ⟨7188549, by rfl⟩ : syracuseStep 19169465 = 14377099) B14377099
theorem B2072903 : Blo 1381510 2072903 := bstep (se 1 (by rfl) ⟨1554677, by rfl⟩ : syracuseStep 2072903 = 3109355) B3109355
theorem B2073143 : Blo 1381510 2073143 := bstep (se 1 (by rfl) ⟨1554857, by rfl⟩ : syracuseStep 2073143 = 3109715) B3109715
theorem B2073215 : Blo 1381510 2073215 := bstep (se 1 (by rfl) ⟨1554911, by rfl⟩ : syracuseStep 2073215 = 3109823) B3109823
theorem B204685975 : Blo 1381510 204685975 := bstep (se 1 (by rfl) ⟨153514481, by rfl⟩ : syracuseStep 204685975 = 307028963) B307028963
theorem B10494683 : Blo 1381510 10494683 := bstep (se 1 (by rfl) ⟨7871012, by rfl⟩ : syracuseStep 10494683 = 15742025) B15742025
theorem B10502945 : Blo 1381510 10502945 := bstep (se 2 (by rfl) ⟨3938604, by rfl⟩ : syracuseStep 10502945 = 7877209) B7877209
theorem B6644551 : Blo 1381510 6644551 := bstep (se 1 (by rfl) ⟨4983413, by rfl⟩ : syracuseStep 6644551 = 9966827) B9966827
theorem B2073551 : Blo 1381510 2073551 := bstep (se 1 (by rfl) ⟨1555163, by rfl⟩ : syracuseStep 2073551 = 3110327) B3110327
theorem B2073737 : Blo 1381510 2073737 := bstep (se 2 (by rfl) ⟨777651, by rfl⟩ : syracuseStep 2073737 = 1555303) B1555303
theorem B4981945 : Blo 1381510 4981945 := bstep (se 2 (by rfl) ⟨1868229, by rfl⟩ : syracuseStep 4981945 = 3736459) B3736459
theorem B2073977 : Blo 1381510 2073977 := bstep (se 2 (by rfl) ⟨777741, by rfl⟩ : syracuseStep 2073977 = 1555483) B1555483
theorem B4982249 : Blo 1381510 4982249 := bstep (se 2 (by rfl) ⟨1868343, by rfl⟩ : syracuseStep 4982249 = 3736687) B3736687
theorem B2623079 : Blo 1381510 2623079 := bstep (se 1 (by rfl) ⟨1967309, by rfl⟩ : syracuseStep 2623079 = 3934619) B3934619
theorem B8406787 : Blo 1381510 8406787 := bstep (se 1 (by rfl) ⟨6305090, by rfl⟩ : syracuseStep 8406787 = 12610181) B12610181
theorem B2074601 : Blo 1381510 2074601 := bstep (se 2 (by rfl) ⟨777975, by rfl⟩ : syracuseStep 2074601 = 1555951) B1555951
theorem B2074619 : Blo 1381510 2074619 := bstep (se 1 (by rfl) ⟨1555964, by rfl⟩ : syracuseStep 2074619 = 3111929) B3111929
theorem B4663547 : Blo 1381510 4663547 := bstep (se 1 (by rfl) ⟨3497660, by rfl⟩ : syracuseStep 4663547 = 6995321) B6995321
theorem B2074943 : Blo 1381510 2074943 := bstep (se 1 (by rfl) ⟨1556207, by rfl⟩ : syracuseStep 2074943 = 3112415) B3112415
theorem B4663655 : Blo 1381510 4663655 := bstep (se 1 (by rfl) ⟨3497741, by rfl⟩ : syracuseStep 4663655 = 6995483) B6995483
theorem B4426139 : Blo 1381510 4426139 := bstep (se 1 (by rfl) ⟨3319604, by rfl⟩ : syracuseStep 4426139 = 6639209) B6639209
theorem B2214383 : Blo 1381510 2214383 := bstep (se 1 (by rfl) ⟨1660787, by rfl⟩ : syracuseStep 2214383 = 3321575) B3321575
theorem B8858429 : Blo 1381510 8858429 := bstep (se 3 (by rfl) ⟨1660955, by rfl⟩ : syracuseStep 8858429 = 3321911) B3321911
theorem B10095623 : Blo 1381510 10095623 := bstep (se 1 (by rfl) ⟨7571717, by rfl⟩ : syracuseStep 10095623 = 15143435) B15143435
theorem B3501083 : Blo 1381510 3501083 := bstep (se 1 (by rfl) ⟨2625812, by rfl⟩ : syracuseStep 3501083 = 5251625) B5251625
theorem B6999209 : Blo 1381510 6999209 := bstep (se 2 (by rfl) ⟨2624703, by rfl⟩ : syracuseStep 6999209 = 5249407) B5249407
theorem B35892413 : Blo 1381510 35892413 := bstep (se 3 (by rfl) ⟨6729827, by rfl⟩ : syracuseStep 35892413 = 13459655) B13459655
theorem B1576255 : Blo 1381510 1576255 := bstep (se 1 (by rfl) ⟨1182191, by rfl⟩ : syracuseStep 1576255 = 2364383) B2364383
theorem B6999533 : Blo 1381510 6999533 := bstep (se 3 (by rfl) ⟨1312412, by rfl⟩ : syracuseStep 6999533 = 2624825) B2624825
theorem B3412199 : Blo 1381510 3412199 := bstep (se 1 (by rfl) ⟨2559149, by rfl⟩ : syracuseStep 3412199 = 5118299) B5118299
theorem B4665599 : Blo 1381510 4665599 := bstep (se 1 (by rfl) ⟨3499199, by rfl⟩ : syracuseStep 4665599 = 6998399) B6998399
theorem B5321215 : Blo 1381510 5321215 := bstep (se 1 (by rfl) ⟨3990911, by rfl⟩ : syracuseStep 5321215 = 7981823) B7981823
theorem B8860427 : Blo 1381510 8860427 := bstep (se 1 (by rfl) ⟨6645320, by rfl⟩ : syracuseStep 8860427 = 13290641) B13290641
theorem B7476157 : Blo 1381510 7476157 := bstep (se 3 (by rfl) ⟨1401779, by rfl⟩ : syracuseStep 7476157 = 2803559) B2803559
theorem B1750015 : Blo 1381510 1750015 := bstep (se 1 (by rfl) ⟨1312511, by rfl⟩ : syracuseStep 1750015 = 2625023) B2625023
theorem B4666463 : Blo 1381510 4666463 := bstep (se 1 (by rfl) ⟨3499847, by rfl⟩ : syracuseStep 4666463 = 6999695) B6999695
theorem B2954569 : Blo 1381510 2954569 := bstep (se 2 (by rfl) ⟨1107963, by rfl⟩ : syracuseStep 2954569 = 2215927) B2215927
theorem B3110255 : Blo 1381510 3110255 := bstep (se 1 (by rfl) ⟨2332691, by rfl⟩ : syracuseStep 3110255 = 4665383) B4665383
theorem B1750511 : Blo 1381510 1750511 := bstep (se 1 (by rfl) ⟨1312883, by rfl⟩ : syracuseStep 1750511 = 2625767) B2625767
theorem B4666895 : Blo 1381510 4666895 := bstep (se 1 (by rfl) ⟨3500171, by rfl⟩ : syracuseStep 4666895 = 7000343) B7000343
theorem B2332543 : Blo 1381510 2332543 := bstep (se 1 (by rfl) ⟨1749407, by rfl⟩ : syracuseStep 2332543 = 3498815) B3498815
theorem B1382447 : Blo 1381510 1382447 := bstep (se 1 (by rfl) ⟨1036835, by rfl⟩ : syracuseStep 1382447 = 2073671) B2073671
theorem B1661095 : Blo 1381510 1661095 := bstep (se 1 (by rfl) ⟨1245821, by rfl⟩ : syracuseStep 1661095 = 2491643) B2491643
theorem B1554655 : Blo 1381510 1554655 := bstep (se 1 (by rfl) ⟨1165991, by rfl⟩ : syracuseStep 1554655 = 2331983) B2331983
theorem B4667705 : Blo 1381510 4667705 := bstep (se 2 (by rfl) ⟨1750389, by rfl⟩ : syracuseStep 4667705 = 3500779) B3500779
theorem B207444503 : Blo 1381510 207444503 := bstep (se 1 (by rfl) ⟨155583377, by rfl⟩ : syracuseStep 207444503 = 311166755) B311166755
theorem B1383199 : Blo 1381510 1383199 := bstep (se 1 (by rfl) ⟨1037399, by rfl⟩ : syracuseStep 1383199 = 2074799) B2074799
theorem B3734383 : Blo 1381510 3734383 := bstep (se 1 (by rfl) ⟨2800787, by rfl⟩ : syracuseStep 3734383 = 5601575) B5601575
theorem B10501001 : Blo 1381510 10501001 := bstep (se 2 (by rfl) ⟨3937875, by rfl⟩ : syracuseStep 10501001 = 7875751) B7875751
theorem B3112127 : Blo 1381510 3112127 := bstep (se 1 (by rfl) ⟨2334095, by rfl⟩ : syracuseStep 3112127 = 4668191) B4668191
theorem B8855095 : Blo 1381510 8855095 := bstep (se 1 (by rfl) ⟨6641321, by rfl⟩ : syracuseStep 8855095 = 13282643) B13282643
theorem B2801225 : Blo 1381510 2801225 := bstep (se 2 (by rfl) ⟨1050459, by rfl⟩ : syracuseStep 2801225 = 2100919) B2100919
theorem B4669001 : Blo 1381510 4669001 := bstep (se 2 (by rfl) ⟨1750875, by rfl⟩ : syracuseStep 4669001 = 3501751) B3501751
theorem B2072873 : Blo 1381510 2072873 := bstep (se 2 (by rfl) ⟨777327, by rfl⟩ : syracuseStep 2072873 = 1554655) B1554655
theorem B6996455 : Blo 1381510 6996455 := bstep (se 1 (by rfl) ⟨5247341, by rfl⟩ : syracuseStep 6996455 = 10494683) B10494683
theorem B51118573 : Blo 1381510 51118573 := bstep (se 3 (by rfl) ⟨9584732, by rfl⟩ : syracuseStep 51118573 = 19169465) B19169465
theorem B5906951 : Blo 1381510 5906951 := bstep (se 1 (by rfl) ⟨4430213, by rfl⟩ : syracuseStep 5906951 = 8860427) B8860427
theorem B7094953 : Blo 1381510 7094953 := bstep (se 2 (by rfl) ⟨2660607, by rfl⟩ : syracuseStep 7094953 = 5321215) B5321215
theorem B2073503 : Blo 1381510 2073503 := bstep (se 1 (by rfl) ⟨1555127, by rfl⟩ : syracuseStep 2073503 = 3110255) B3110255
theorem B2950759 : Blo 1381510 2950759 := bstep (se 1 (by rfl) ⟨2213069, by rfl⟩ : syracuseStep 2950759 = 4426139) B4426139
theorem B11806793 : Blo 1381510 11806793 := bstep (se 2 (by rfl) ⟨4427547, by rfl⟩ : syracuseStep 11806793 = 8855095) B8855095
theorem B2074751 : Blo 1381510 2074751 := bstep (se 1 (by rfl) ⟨1556063, by rfl⟩ : syracuseStep 2074751 = 3112127) B3112127
theorem B39872837 : Blo 1381510 39872837 := bstep (se 4 (by rfl) ⟨3738078, by rfl⟩ : syracuseStep 39872837 = 7476157) B7476157
theorem B11209049 : Blo 1381510 11209049 := bstep (se 2 (by rfl) ⟨4203393, by rfl⟩ : syracuseStep 11209049 = 8406787) B8406787
theorem B4729697 : Blo 1381510 4729697 := bstep (se 2 (by rfl) ⟨1773636, by rfl⟩ : syracuseStep 4729697 = 3547273) B3547273
theorem B2214793 : Blo 1381510 2214793 := bstep (se 2 (by rfl) ⟨830547, by rfl⟩ : syracuseStep 2214793 = 1661095) B1661095
theorem B3321499 : Blo 1381510 3321499 := bstep (se 1 (by rfl) ⟨2491124, by rfl⟩ : syracuseStep 3321499 = 4982249) B4982249
theorem B1748719 : Blo 1381510 1748719 := bstep (se 1 (by rfl) ⟨1311539, by rfl⟩ : syracuseStep 1748719 = 2623079) B2623079
theorem B8859401 : Blo 1381510 8859401 := bstep (se 2 (by rfl) ⟨3322275, by rfl⟩ : syracuseStep 8859401 = 6644551) B6644551
theorem B3109031 : Blo 1381510 3109031 := bstep (se 1 (by rfl) ⟨2331773, by rfl⟩ : syracuseStep 3109031 = 4663547) B4663547
theorem B3109103 : Blo 1381510 3109103 := bstep (se 1 (by rfl) ⟨2331827, by rfl⟩ : syracuseStep 3109103 = 4663655) B4663655
theorem B2101673 : Blo 1381510 2101673 := bstep (se 2 (by rfl) ⟨788127, by rfl⟩ : syracuseStep 2101673 = 1576255) B1576255
theorem B7000667 : Blo 1381510 7000667 := bstep (se 1 (by rfl) ⟨5250500, by rfl⟩ : syracuseStep 7000667 = 10501001) B10501001
theorem B6730415 : Blo 1381510 6730415 := bstep (se 1 (by rfl) ⟨5047811, by rfl⟩ : syracuseStep 6730415 = 10095623) B10095623
theorem B4666139 : Blo 1381510 4666139 := bstep (se 1 (by rfl) ⟨3499604, by rfl⟩ : syracuseStep 4666139 = 6999209) B6999209
theorem B4666355 : Blo 1381510 4666355 := bstep (se 1 (by rfl) ⟨3499766, by rfl⟩ : syracuseStep 4666355 = 6999533) B6999533
theorem B3110057 : Blo 1381510 3110057 := bstep (se 2 (by rfl) ⟨1166271, by rfl⟩ : syracuseStep 3110057 = 2332543) B2332543
theorem B2274799 : Blo 1381510 2274799 := bstep (se 1 (by rfl) ⟨1706099, by rfl⟩ : syracuseStep 2274799 = 3412199) B3412199
theorem B3110399 : Blo 1381510 3110399 := bstep (se 1 (by rfl) ⟨2332799, by rfl⟩ : syracuseStep 3110399 = 4665599) B4665599
theorem B1381935 : Blo 1381510 1381935 := bstep (se 1 (by rfl) ⟨1036451, by rfl⟩ : syracuseStep 1381935 = 2072903) B2072903
theorem B1382095 : Blo 1381510 1382095 := bstep (se 1 (by rfl) ⟨1036571, by rfl⟩ : syracuseStep 1382095 = 2073143) B2073143
theorem B1382143 : Blo 1381510 1382143 := bstep (se 1 (by rfl) ⟨1036607, by rfl⟩ : syracuseStep 1382143 = 2073215) B2073215
theorem B7001963 : Blo 1381510 7001963 := bstep (se 1 (by rfl) ⟨5251472, by rfl⟩ : syracuseStep 7001963 = 10502945) B10502945
theorem B1382367 : Blo 1381510 1382367 := bstep (se 1 (by rfl) ⟨1036775, by rfl⟩ : syracuseStep 1382367 = 2073551) B2073551
theorem B3110975 : Blo 1381510 3110975 := bstep (se 1 (by rfl) ⟨2333231, by rfl⟩ : syracuseStep 3110975 = 4666463) B4666463
theorem B1382491 : Blo 1381510 1382491 := bstep (se 1 (by rfl) ⟨1036868, by rfl⟩ : syracuseStep 1382491 = 2073737) B2073737
theorem B272914633 : Blo 1381510 272914633 := bstep (se 2 (by rfl) ⟨102342987, by rfl⟩ : syracuseStep 272914633 = 204685975) B204685975
theorem B1382651 : Blo 1381510 1382651 := bstep (se 1 (by rfl) ⟨1036988, by rfl⟩ : syracuseStep 1382651 = 2073977) B2073977
theorem B3111263 : Blo 1381510 3111263 := bstep (se 1 (by rfl) ⟨2333447, by rfl⟩ : syracuseStep 3111263 = 4666895) B4666895
theorem B4979177 : Blo 1381510 4979177 := bstep (se 2 (by rfl) ⟨1867191, by rfl⟩ : syracuseStep 4979177 = 3734383) B3734383
theorem B5905021 : Blo 1381510 5905021 := bstep (se 3 (by rfl) ⟨1107191, by rfl⟩ : syracuseStep 5905021 = 2214383) B2214383
theorem B4668029 : Blo 1381510 4668029 := bstep (se 3 (by rfl) ⟨875255, by rfl⟩ : syracuseStep 4668029 = 1750511) B1750511
theorem B1383067 : Blo 1381510 1383067 := bstep (se 1 (by rfl) ⟨1037300, by rfl⟩ : syracuseStep 1383067 = 2074601) B2074601
theorem B1383079 : Blo 1381510 1383079 := bstep (se 1 (by rfl) ⟨1037309, by rfl⟩ : syracuseStep 1383079 = 2074619) B2074619
theorem B2333353 : Blo 1381510 2333353 := bstep (se 2 (by rfl) ⟨875007, by rfl⟩ : syracuseStep 2333353 = 1750015) B1750015
theorem B3111803 : Blo 1381510 3111803 := bstep (se 1 (by rfl) ⟨2333852, by rfl⟩ : syracuseStep 3111803 = 4667705) B4667705
theorem B1383295 : Blo 1381510 1383295 := bstep (se 1 (by rfl) ⟨1037471, by rfl⟩ : syracuseStep 1383295 = 2074943) B2074943
theorem B6642593 : Blo 1381510 6642593 := bstep (se 2 (by rfl) ⟨2490972, by rfl⟩ : syracuseStep 6642593 = 4981945) B4981945
theorem B138296335 : Blo 1381510 138296335 := bstep (se 1 (by rfl) ⟨103722251, by rfl⟩ : syracuseStep 138296335 = 207444503) B207444503
theorem B3939425 : Blo 1381510 3939425 := bstep (se 2 (by rfl) ⟨1477284, by rfl⟩ : syracuseStep 3939425 = 2954569) B2954569
theorem B5905619 : Blo 1381510 5905619 := bstep (se 1 (by rfl) ⟨4429214, by rfl⟩ : syracuseStep 5905619 = 8858429) B8858429
theorem B2334055 : Blo 1381510 2334055 := bstep (se 1 (by rfl) ⟨1750541, by rfl⟩ : syracuseStep 2334055 = 3501083) B3501083
theorem B23928275 : Blo 1381510 23928275 := bstep (se 1 (by rfl) ⟨17946206, by rfl⟩ : syracuseStep 23928275 = 35892413) B35892413
theorem B1867483 : Blo 1381510 1867483 := bstep (se 1 (by rfl) ⟨1400612, by rfl⟩ : syracuseStep 1867483 = 2801225) B2801225
theorem B3112667 : Blo 1381510 3112667 := bstep (se 1 (by rfl) ⟨2334500, by rfl⟩ : syracuseStep 3112667 = 4669001) B4669001
theorem B2072687 : Blo 1381510 2072687 := bstep (se 1 (by rfl) ⟨1554515, by rfl⟩ : syracuseStep 2072687 = 3109031) B3109031
theorem B2072735 : Blo 1381510 2072735 := bstep (se 1 (by rfl) ⟨1554551, by rfl⟩ : syracuseStep 2072735 = 3109103) B3109103
theorem B68158097 : Blo 1381510 68158097 := bstep (se 2 (by rfl) ⟨25559286, by rfl⟩ : syracuseStep 68158097 = 51118573) B51118573
theorem B2073371 : Blo 1381510 2073371 := bstep (se 1 (by rfl) ⟨1555028, by rfl⟩ : syracuseStep 2073371 = 3110057) B3110057
theorem B7873361 : Blo 1381510 7873361 := bstep (se 2 (by rfl) ⟨2952510, by rfl⟩ : syracuseStep 7873361 = 5905021) B5905021
theorem B2073599 : Blo 1381510 2073599 := bstep (se 1 (by rfl) ⟨1555199, by rfl⟩ : syracuseStep 2073599 = 3110399) B3110399
theorem B5604461 : Blo 1381510 5604461 := bstep (se 3 (by rfl) ⟨1050836, by rfl⟩ : syracuseStep 5604461 = 2101673) B2101673
theorem B184395113 : Blo 1381510 184395113 := bstep (se 2 (by rfl) ⟨69148167, by rfl⟩ : syracuseStep 184395113 = 138296335) B138296335
theorem B2073983 : Blo 1381510 2073983 := bstep (se 1 (by rfl) ⟨1555487, by rfl⟩ : syracuseStep 2073983 = 3110975) B3110975
theorem B7472699 : Blo 1381510 7472699 := bstep (se 1 (by rfl) ⟨5604524, by rfl⟩ : syracuseStep 7472699 = 11209049) B11209049
theorem B2074175 : Blo 1381510 2074175 := bstep (se 1 (by rfl) ⟨1555631, by rfl⟩ : syracuseStep 2074175 = 3111263) B3111263
theorem B3319451 : Blo 1381510 3319451 := bstep (se 1 (by rfl) ⟨2489588, by rfl⟩ : syracuseStep 3319451 = 4979177) B4979177
theorem B2074535 : Blo 1381510 2074535 := bstep (se 1 (by rfl) ⟨1555901, by rfl⟩ : syracuseStep 2074535 = 3111803) B3111803
theorem B3033065 : Blo 1381510 3033065 := bstep (se 2 (by rfl) ⟨1137399, by rfl⟩ : syracuseStep 3033065 = 2274799) B2274799
theorem B3934345 : Blo 1381510 3934345 := bstep (se 2 (by rfl) ⟨1475379, by rfl⟩ : syracuseStep 3934345 = 2950759) B2950759
theorem B15952183 : Blo 1381510 15952183 := bstep (se 1 (by rfl) ⟨11964137, by rfl⟩ : syracuseStep 15952183 = 23928275) B23928275
theorem B2075111 : Blo 1381510 2075111 := bstep (se 1 (by rfl) ⟨1556333, by rfl⟩ : syracuseStep 2075111 = 3112667) B3112667
theorem B4664303 : Blo 1381510 4664303 := bstep (se 1 (by rfl) ⟨3498227, by rfl⟩ : syracuseStep 4664303 = 6996455) B6996455
theorem B4428395 : Blo 1381510 4428395 := bstep (se 1 (by rfl) ⟨3321296, by rfl⟩ : syracuseStep 4428395 = 6642593) B6642593
theorem B2626283 : Blo 1381510 2626283 := bstep (se 1 (by rfl) ⟨1969712, by rfl⟩ : syracuseStep 2626283 = 3939425) B3939425
theorem B3937079 : Blo 1381510 3937079 := bstep (se 1 (by rfl) ⟨2952809, by rfl⟩ : syracuseStep 3937079 = 5905619) B5905619
theorem B4428665 : Blo 1381510 4428665 := bstep (se 2 (by rfl) ⟨1660749, by rfl⟩ : syracuseStep 4428665 = 3321499) B3321499
theorem B2331625 : Blo 1381510 2331625 := bstep (se 2 (by rfl) ⟨874359, by rfl⟩ : syracuseStep 2331625 = 1748719) B1748719
theorem B1381915 : Blo 1381510 1381915 := bstep (se 1 (by rfl) ⟨1036436, by rfl⟩ : syracuseStep 1381915 = 2072873) B2072873
theorem B363886177 : Blo 1381510 363886177 := bstep (se 2 (by rfl) ⟨136457316, by rfl⟩ : syracuseStep 363886177 = 272914633) B272914633
theorem B3937967 : Blo 1381510 3937967 := bstep (se 1 (by rfl) ⟨2953475, by rfl⟩ : syracuseStep 3937967 = 5906951) B5906951
theorem B4667111 : Blo 1381510 4667111 := bstep (se 1 (by rfl) ⟨3500333, by rfl⟩ : syracuseStep 4667111 = 7000667) B7000667
theorem B4486943 : Blo 1381510 4486943 := bstep (se 1 (by rfl) ⟨3365207, by rfl⟩ : syracuseStep 4486943 = 6730415) B6730415
theorem B3110759 : Blo 1381510 3110759 := bstep (se 1 (by rfl) ⟨2333069, by rfl⟩ : syracuseStep 3110759 = 4666139) B4666139
theorem B1382335 : Blo 1381510 1382335 := bstep (se 1 (by rfl) ⟨1036751, by rfl⟩ : syracuseStep 1382335 = 2073503) B2073503
theorem B3110903 : Blo 1381510 3110903 := bstep (se 1 (by rfl) ⟨2333177, by rfl⟩ : syracuseStep 3110903 = 4666355) B4666355
theorem B9459937 : Blo 1381510 9459937 := bstep (se 2 (by rfl) ⟨3547476, by rfl⟩ : syracuseStep 9459937 = 7094953) B7094953
theorem B3111137 : Blo 1381510 3111137 := bstep (se 2 (by rfl) ⟨1166676, by rfl⟩ : syracuseStep 3111137 = 2333353) B2333353
theorem B4667975 : Blo 1381510 4667975 := bstep (se 1 (by rfl) ⟨3500981, by rfl⟩ : syracuseStep 4667975 = 7001963) B7001963
theorem B7871195 : Blo 1381510 7871195 := bstep (se 1 (by rfl) ⟨5903396, by rfl⟩ : syracuseStep 7871195 = 11806793) B11806793
theorem B1383167 : Blo 1381510 1383167 := bstep (se 1 (by rfl) ⟨1037375, by rfl⟩ : syracuseStep 1383167 = 2074751) B2074751
theorem B26581891 : Blo 1381510 26581891 := bstep (se 1 (by rfl) ⟨19936418, by rfl⟩ : syracuseStep 26581891 = 39872837) B39872837
theorem B3112019 : Blo 1381510 3112019 := bstep (se 1 (by rfl) ⟨2334014, by rfl⟩ : syracuseStep 3112019 = 4668029) B4668029
theorem B3112073 : Blo 1381510 3112073 := bstep (se 2 (by rfl) ⟨1167027, by rfl⟩ : syracuseStep 3112073 = 2334055) B2334055
theorem B3153131 : Blo 1381510 3153131 := bstep (se 1 (by rfl) ⟨2364848, by rfl⟩ : syracuseStep 3153131 = 4729697) B4729697
theorem B11812229 : Blo 1381510 11812229 := bstep (se 4 (by rfl) ⟨1107396, by rfl⟩ : syracuseStep 11812229 = 2214793) B2214793
theorem B2489977 : Blo 1381510 2489977 := bstep (se 2 (by rfl) ⟨933741, by rfl⟩ : syracuseStep 2489977 = 1867483) B1867483
theorem B5906267 : Blo 1381510 5906267 := bstep (se 1 (by rfl) ⟨4429700, by rfl⟩ : syracuseStep 5906267 = 8859401) B8859401
theorem B3736307 : Blo 1381510 3736307 := bstep (se 1 (by rfl) ⟨2802230, by rfl⟩ : syracuseStep 3736307 = 5604461) B5604461
theorem B122930075 : Blo 1381510 122930075 := bstep (se 1 (by rfl) ⟨92197556, by rfl⟩ : syracuseStep 122930075 = 184395113) B184395113
theorem B4981799 : Blo 1381510 4981799 := bstep (se 1 (by rfl) ⟨3736349, by rfl⟩ : syracuseStep 4981799 = 7472699) B7472699
theorem B2212967 : Blo 1381510 2212967 := bstep (se 1 (by rfl) ⟨1659725, by rfl⟩ : syracuseStep 2212967 = 3319451) B3319451
theorem B2991295 : Blo 1381510 2991295 := bstep (se 1 (by rfl) ⟨2243471, by rfl⟩ : syracuseStep 2991295 = 4486943) B4486943
theorem B2073839 : Blo 1381510 2073839 := bstep (se 1 (by rfl) ⟨1555379, by rfl⟩ : syracuseStep 2073839 = 3110759) B3110759
theorem B2073935 : Blo 1381510 2073935 := bstep (se 1 (by rfl) ⟨1555451, by rfl⟩ : syracuseStep 2073935 = 3110903) B3110903
theorem B2074091 : Blo 1381510 2074091 := bstep (se 1 (by rfl) ⟨1555568, by rfl⟩ : syracuseStep 2074091 = 3111137) B3111137
theorem B2074679 : Blo 1381510 2074679 := bstep (se 1 (by rfl) ⟨1556009, by rfl⟩ : syracuseStep 2074679 = 3112019) B3112019
theorem B2074715 : Blo 1381510 2074715 := bstep (se 1 (by rfl) ⟨1556036, by rfl⟩ : syracuseStep 2074715 = 3112073) B3112073
theorem B485181569 : Blo 1381510 485181569 := bstep (se 2 (by rfl) ⟨181943088, by rfl⟩ : syracuseStep 485181569 = 363886177) B363886177
theorem B3319969 : Blo 1381510 3319969 := bstep (se 2 (by rfl) ⟨1244988, by rfl⟩ : syracuseStep 3319969 = 2489977) B2489977
theorem B7874819 : Blo 1381510 7874819 := bstep (se 1 (by rfl) ⟨5906114, by rfl⟩ : syracuseStep 7874819 = 11812229) B11812229
theorem B8088173 : Blo 1381510 8088173 := bstep (se 3 (by rfl) ⟨1516532, by rfl⟩ : syracuseStep 8088173 = 3033065) B3033065
theorem B5245793 : Blo 1381510 5245793 := bstep (se 2 (by rfl) ⟨1967172, by rfl⟩ : syracuseStep 5245793 = 3934345) B3934345
theorem B2952263 : Blo 1381510 2952263 := bstep (se 1 (by rfl) ⟨2214197, by rfl⟩ : syracuseStep 2952263 = 4428395) B4428395
theorem B2624719 : Blo 1381510 2624719 := bstep (se 1 (by rfl) ⟨1968539, by rfl⟩ : syracuseStep 2624719 = 3937079) B3937079
theorem B2952443 : Blo 1381510 2952443 := bstep (se 1 (by rfl) ⟨2214332, by rfl⟩ : syracuseStep 2952443 = 4428665) B4428665
theorem B2625311 : Blo 1381510 2625311 := bstep (se 1 (by rfl) ⟨1968983, by rfl⟩ : syracuseStep 2625311 = 3937967) B3937967
theorem B35442521 : Blo 1381510 35442521 := bstep (se 2 (by rfl) ⟨13290945, by rfl⟩ : syracuseStep 35442521 = 26581891) B26581891
theorem B3108833 : Blo 1381510 3108833 := bstep (se 2 (by rfl) ⟨1165812, by rfl⟩ : syracuseStep 3108833 = 2331625) B2331625
theorem B85078309 : Blo 1381510 85078309 := bstep (se 4 (by rfl) ⟨7976091, by rfl⟩ : syracuseStep 85078309 = 15952183) B15952183
theorem B5247463 : Blo 1381510 5247463 := bstep (se 1 (by rfl) ⟨3935597, by rfl⟩ : syracuseStep 5247463 = 7871195) B7871195
theorem B3109535 : Blo 1381510 3109535 := bstep (se 1 (by rfl) ⟨2332151, by rfl⟩ : syracuseStep 3109535 = 4664303) B4664303
theorem B2102087 : Blo 1381510 2102087 := bstep (se 1 (by rfl) ⟨1576565, by rfl⟩ : syracuseStep 2102087 = 3153131) B3153131
theorem B3937511 : Blo 1381510 3937511 := bstep (se 1 (by rfl) ⟨2953133, by rfl⟩ : syracuseStep 3937511 = 5906267) B5906267
theorem B1381791 : Blo 1381510 1381791 := bstep (se 1 (by rfl) ⟨1036343, by rfl⟩ : syracuseStep 1381791 = 2072687) B2072687
theorem B1381823 : Blo 1381510 1381823 := bstep (se 1 (by rfl) ⟨1036367, by rfl⟩ : syracuseStep 1381823 = 2072735) B2072735
theorem B12613249 : Blo 1381510 12613249 := bstep (se 2 (by rfl) ⟨4729968, by rfl⟩ : syracuseStep 12613249 = 9459937) B9459937
theorem B45438731 : Blo 1381510 45438731 := bstep (se 1 (by rfl) ⟨34079048, by rfl⟩ : syracuseStep 45438731 = 68158097) B68158097
theorem B1382247 : Blo 1381510 1382247 := bstep (se 1 (by rfl) ⟨1036685, by rfl⟩ : syracuseStep 1382247 = 2073371) B2073371
theorem B5248907 : Blo 1381510 5248907 := bstep (se 1 (by rfl) ⟨3936680, by rfl⟩ : syracuseStep 5248907 = 7873361) B7873361
theorem B1382399 : Blo 1381510 1382399 := bstep (se 1 (by rfl) ⟨1036799, by rfl⟩ : syracuseStep 1382399 = 2073599) B2073599
theorem B1382655 : Blo 1381510 1382655 := bstep (se 1 (by rfl) ⟨1036991, by rfl⟩ : syracuseStep 1382655 = 2073983) B2073983
theorem B1382783 : Blo 1381510 1382783 := bstep (se 1 (by rfl) ⟨1037087, by rfl⟩ : syracuseStep 1382783 = 2074175) B2074175
theorem B3111407 : Blo 1381510 3111407 := bstep (se 1 (by rfl) ⟨2333555, by rfl⟩ : syracuseStep 3111407 = 4667111) B4667111
theorem B1383023 : Blo 1381510 1383023 := bstep (se 1 (by rfl) ⟨1037267, by rfl⟩ : syracuseStep 1383023 = 2074535) B2074535
theorem B1383407 : Blo 1381510 1383407 := bstep (se 1 (by rfl) ⟨1037555, by rfl⟩ : syracuseStep 1383407 = 2075111) B2075111
theorem B3111983 : Blo 1381510 3111983 := bstep (se 1 (by rfl) ⟨2333987, by rfl⟩ : syracuseStep 3111983 = 4667975) B4667975
theorem B7003421 : Blo 1381510 7003421 := bstep (se 3 (by rfl) ⟨1313141, by rfl⟩ : syracuseStep 7003421 = 2626283) B2626283
theorem B2073023 : Blo 1381510 2073023 := bstep (se 1 (by rfl) ⟨1554767, by rfl⟩ : syracuseStep 2073023 = 3109535) B3109535
theorem B1401391 : Blo 1381510 1401391 := bstep (se 1 (by rfl) ⟨1051043, by rfl⟩ : syracuseStep 1401391 = 2102087) B2102087
theorem B81953383 : Blo 1381510 81953383 := bstep (se 1 (by rfl) ⟨61465037, by rfl⟩ : syracuseStep 81953383 = 122930075) B122930075
theorem B6996617 : Blo 1381510 6996617 := bstep (se 2 (by rfl) ⟨2623731, by rfl⟩ : syracuseStep 6996617 = 5247463) B5247463
theorem B3499271 : Blo 1381510 3499271 := bstep (se 1 (by rfl) ⟨2624453, by rfl⟩ : syracuseStep 3499271 = 5248907) B5248907
theorem B323454379 : Blo 1381510 323454379 := bstep (se 1 (by rfl) ⟨242590784, by rfl⟩ : syracuseStep 323454379 = 485181569) B485181569
theorem B3499625 : Blo 1381510 3499625 := bstep (se 2 (by rfl) ⟨1312359, by rfl⟩ : syracuseStep 3499625 = 2624719) B2624719
theorem B2074271 : Blo 1381510 2074271 := bstep (se 1 (by rfl) ⟨1555703, by rfl⟩ : syracuseStep 2074271 = 3111407) B3111407
theorem B5392115 : Blo 1381510 5392115 := bstep (se 1 (by rfl) ⟨4044086, by rfl⟩ : syracuseStep 5392115 = 8088173) B8088173
theorem B9963485 : Blo 1381510 9963485 := bstep (se 3 (by rfl) ⟨1868153, by rfl⟩ : syracuseStep 9963485 = 3736307) B3736307
theorem B2074655 : Blo 1381510 2074655 := bstep (se 1 (by rfl) ⟨1555991, by rfl⟩ : syracuseStep 2074655 = 3111983) B3111983
theorem B1968175 : Blo 1381510 1968175 := bstep (se 1 (by rfl) ⟨1476131, by rfl⟩ : syracuseStep 1968175 = 2952263) B2952263
theorem B1968295 : Blo 1381510 1968295 := bstep (se 1 (by rfl) ⟨1476221, by rfl⟩ : syracuseStep 1968295 = 2952443) B2952443
theorem B23628347 : Blo 1381510 23628347 := bstep (se 1 (by rfl) ⟨17721260, by rfl⟩ : syracuseStep 23628347 = 35442521) B35442521
theorem B4426625 : Blo 1381510 4426625 := bstep (se 2 (by rfl) ⟨1659984, by rfl⟩ : syracuseStep 4426625 = 3319969) B3319969
theorem B5901245 : Blo 1381510 5901245 := bstep (se 3 (by rfl) ⟨1106483, by rfl⟩ : syracuseStep 5901245 = 2212967) B2212967
theorem B113437745 : Blo 1381510 113437745 := bstep (se 2 (by rfl) ⟨42539154, by rfl⟩ : syracuseStep 113437745 = 85078309) B85078309
theorem B3321199 : Blo 1381510 3321199 := bstep (se 1 (by rfl) ⟨2490899, by rfl⟩ : syracuseStep 3321199 = 4981799) B4981799
theorem B15953573 : Blo 1381510 15953573 := bstep (se 4 (by rfl) ⟨1495647, by rfl⟩ : syracuseStep 15953573 = 2991295) B2991295
theorem B7000829 : Blo 1381510 7000829 := bstep (se 3 (by rfl) ⟨1312655, by rfl⟩ : syracuseStep 7000829 = 2625311) B2625311
theorem B10500029 : Blo 1381510 10500029 := bstep (se 3 (by rfl) ⟨1968755, by rfl⟩ : syracuseStep 10500029 = 3937511) B3937511
theorem B1382559 : Blo 1381510 1382559 := bstep (se 1 (by rfl) ⟨1036919, by rfl⟩ : syracuseStep 1382559 = 2073839) B2073839
theorem B1382623 : Blo 1381510 1382623 := bstep (se 1 (by rfl) ⟨1036967, by rfl⟩ : syracuseStep 1382623 = 2073935) B2073935
theorem B1382727 : Blo 1381510 1382727 := bstep (se 1 (by rfl) ⟨1037045, by rfl⟩ : syracuseStep 1382727 = 2074091) B2074091
theorem B30292487 : Blo 1381510 30292487 := bstep (se 1 (by rfl) ⟨22719365, by rfl⟩ : syracuseStep 30292487 = 45438731) B45438731
theorem B1383119 : Blo 1381510 1383119 := bstep (se 1 (by rfl) ⟨1037339, by rfl⟩ : syracuseStep 1383119 = 2074679) B2074679
theorem B1383143 : Blo 1381510 1383143 := bstep (se 1 (by rfl) ⟨1037357, by rfl⟩ : syracuseStep 1383143 = 2074715) B2074715
theorem B5249879 : Blo 1381510 5249879 := bstep (se 1 (by rfl) ⟨3937409, by rfl⟩ : syracuseStep 5249879 = 7874819) B7874819
theorem B3497195 : Blo 1381510 3497195 := bstep (se 1 (by rfl) ⟨2622896, by rfl⟩ : syracuseStep 3497195 = 5245793) B5245793
theorem B16817665 : Blo 1381510 16817665 := bstep (se 2 (by rfl) ⟨6306624, by rfl⟩ : syracuseStep 16817665 = 12613249) B12613249
theorem B4668947 : Blo 1381510 4668947 := bstep (se 1 (by rfl) ⟨3501710, by rfl⟩ : syracuseStep 4668947 = 7003421) B7003421
theorem B2072555 : Blo 1381510 2072555 := bstep (se 1 (by rfl) ⟨1554416, by rfl⟩ : syracuseStep 2072555 = 3108833) B3108833
theorem B1868521 : Blo 1381510 1868521 := bstep (se 2 (by rfl) ⟨700695, by rfl⟩ : syracuseStep 1868521 = 1401391) B1401391
theorem B20194991 : Blo 1381510 20194991 := bstep (se 1 (by rfl) ⟨15146243, by rfl⟩ : syracuseStep 20194991 = 30292487) B30292487
theorem B3499919 : Blo 1381510 3499919 := bstep (se 1 (by rfl) ⟨2624939, by rfl⟩ : syracuseStep 3499919 = 5249879) B5249879
theorem B2951083 : Blo 1381510 2951083 := bstep (se 1 (by rfl) ⟨2213312, by rfl⟩ : syracuseStep 2951083 = 4426625) B4426625
theorem B3934163 : Blo 1381510 3934163 := bstep (se 1 (by rfl) ⟨2950622, by rfl⟩ : syracuseStep 3934163 = 5901245) B5901245
theorem B22423553 : Blo 1381510 22423553 := bstep (se 2 (by rfl) ⟨8408832, by rfl⟩ : syracuseStep 22423553 = 16817665) B16817665
theorem B10635715 : Blo 1381510 10635715 := bstep (se 1 (by rfl) ⟨7976786, by rfl⟩ : syracuseStep 10635715 = 15953573) B15953573
theorem B2624233 : Blo 1381510 2624233 := bstep (se 2 (by rfl) ⟨984087, by rfl⟩ : syracuseStep 2624233 = 1968175) B1968175
theorem B2624393 : Blo 1381510 2624393 := bstep (se 2 (by rfl) ⟨984147, by rfl⟩ : syracuseStep 2624393 = 1968295) B1968295
theorem B4664411 : Blo 1381510 4664411 := bstep (se 1 (by rfl) ⟨3498308, by rfl⟩ : syracuseStep 4664411 = 6996617) B6996617
theorem B7000019 : Blo 1381510 7000019 := bstep (se 1 (by rfl) ⟨5250014, by rfl⟩ : syracuseStep 7000019 = 10500029) B10500029
theorem B4428265 : Blo 1381510 4428265 := bstep (se 2 (by rfl) ⟨1660599, by rfl⟩ : syracuseStep 4428265 = 3321199) B3321199
theorem B431272505 : Blo 1381510 431272505 := bstep (se 2 (by rfl) ⟨161727189, by rfl⟩ : syracuseStep 431272505 = 323454379) B323454379
theorem B75625163 : Blo 1381510 75625163 := bstep (se 1 (by rfl) ⟨56718872, by rfl⟩ : syracuseStep 75625163 = 113437745) B113437745
theorem B2331463 : Blo 1381510 2331463 := bstep (se 1 (by rfl) ⟨1748597, by rfl⟩ : syracuseStep 2331463 = 3497195) B3497195
theorem B1381703 : Blo 1381510 1381703 := bstep (se 1 (by rfl) ⟨1036277, by rfl⟩ : syracuseStep 1381703 = 2072555) B2072555
theorem B1382015 : Blo 1381510 1382015 := bstep (se 1 (by rfl) ⟨1036511, by rfl⟩ : syracuseStep 1382015 = 2073023) B2073023
theorem B4667219 : Blo 1381510 4667219 := bstep (se 1 (by rfl) ⟨3500414, by rfl⟩ : syracuseStep 4667219 = 7000829) B7000829
theorem B109271177 : Blo 1381510 109271177 := bstep (se 2 (by rfl) ⟨40976691, by rfl⟩ : syracuseStep 109271177 = 81953383) B81953383
theorem B2332847 : Blo 1381510 2332847 := bstep (se 1 (by rfl) ⟨1749635, by rfl⟩ : syracuseStep 2332847 = 3499271) B3499271
theorem B2333083 : Blo 1381510 2333083 := bstep (se 1 (by rfl) ⟨1749812, by rfl⟩ : syracuseStep 2333083 = 3499625) B3499625
theorem B1382847 : Blo 1381510 1382847 := bstep (se 1 (by rfl) ⟨1037135, by rfl⟩ : syracuseStep 1382847 = 2074271) B2074271
theorem B3594743 : Blo 1381510 3594743 := bstep (se 1 (by rfl) ⟨2696057, by rfl⟩ : syracuseStep 3594743 = 5392115) B5392115
theorem B6642323 : Blo 1381510 6642323 := bstep (se 1 (by rfl) ⟨4981742, by rfl⟩ : syracuseStep 6642323 = 9963485) B9963485
theorem B1383103 : Blo 1381510 1383103 := bstep (se 1 (by rfl) ⟨1037327, by rfl⟩ : syracuseStep 1383103 = 2074655) B2074655
theorem B15752231 : Blo 1381510 15752231 := bstep (se 1 (by rfl) ⟨11814173, by rfl⟩ : syracuseStep 15752231 = 23628347) B23628347
theorem B3112631 : Blo 1381510 3112631 := bstep (se 1 (by rfl) ⟨2334473, by rfl⟩ : syracuseStep 3112631 = 4668947) B4668947
theorem B287515003 : Blo 1381510 287515003 := bstep (se 1 (by rfl) ⟨215636252, by rfl⟩ : syracuseStep 287515003 = 431272505) B431272505
theorem B14180953 : Blo 1381510 14180953 := bstep (se 2 (by rfl) ⟨5317857, by rfl⟩ : syracuseStep 14180953 = 10635715) B10635715
theorem B3498977 : Blo 1381510 3498977 := bstep (se 2 (by rfl) ⟨1312116, by rfl⟩ : syracuseStep 3498977 = 2624233) B2624233
theorem B2491361 : Blo 1381510 2491361 := bstep (se 2 (by rfl) ⟨934260, by rfl⟩ : syracuseStep 2491361 = 1868521) B1868521
theorem B2622775 : Blo 1381510 2622775 := bstep (se 1 (by rfl) ⟨1967081, by rfl⟩ : syracuseStep 2622775 = 3934163) B3934163
theorem B15739109 : Blo 1381510 15739109 := bstep (se 4 (by rfl) ⟨1475541, by rfl⟩ : syracuseStep 15739109 = 2951083) B2951083
theorem B2075087 : Blo 1381510 2075087 := bstep (se 1 (by rfl) ⟨1556315, by rfl⟩ : syracuseStep 2075087 = 3112631) B3112631
theorem B50416775 : Blo 1381510 50416775 := bstep (se 1 (by rfl) ⟨37812581, by rfl⟩ : syracuseStep 50416775 = 75625163) B75625163
theorem B3108617 : Blo 1381510 3108617 := bstep (se 2 (by rfl) ⟨1165731, by rfl⟩ : syracuseStep 3108617 = 2331463) B2331463
theorem B13463327 : Blo 1381510 13463327 := bstep (se 1 (by rfl) ⟨10097495, by rfl⟩ : syracuseStep 13463327 = 20194991) B20194991
theorem B72847451 : Blo 1381510 72847451 := bstep (se 1 (by rfl) ⟨54635588, by rfl⟩ : syracuseStep 72847451 = 109271177) B109271177
theorem B2396495 : Blo 1381510 2396495 := bstep (se 1 (by rfl) ⟨1797371, by rfl⟩ : syracuseStep 2396495 = 3594743) B3594743
theorem B4428215 : Blo 1381510 4428215 := bstep (se 1 (by rfl) ⟨3321161, by rfl⟩ : syracuseStep 4428215 = 6642323) B6642323
theorem B1749595 : Blo 1381510 1749595 := bstep (se 1 (by rfl) ⟨1312196, by rfl⟩ : syracuseStep 1749595 = 2624393) B2624393
theorem B3109607 : Blo 1381510 3109607 := bstep (se 1 (by rfl) ⟨2332205, by rfl⟩ : syracuseStep 3109607 = 4664411) B4664411
theorem B4666679 : Blo 1381510 4666679 := bstep (se 1 (by rfl) ⟨3500009, by rfl⟩ : syracuseStep 4666679 = 7000019) B7000019
theorem B3110777 : Blo 1381510 3110777 := bstep (se 2 (by rfl) ⟨1166541, by rfl⟩ : syracuseStep 3110777 = 2333083) B2333083
theorem B5904353 : Blo 1381510 5904353 := bstep (se 2 (by rfl) ⟨2214132, by rfl⟩ : syracuseStep 5904353 = 4428265) B4428265
theorem B3111479 : Blo 1381510 3111479 := bstep (se 1 (by rfl) ⟨2333609, by rfl⟩ : syracuseStep 3111479 = 4667219) B4667219
theorem B2333279 : Blo 1381510 2333279 := bstep (se 1 (by rfl) ⟨1749959, by rfl⟩ : syracuseStep 2333279 = 3499919) B3499919
theorem B14949035 : Blo 1381510 14949035 := bstep (se 1 (by rfl) ⟨11211776, by rfl⟩ : syracuseStep 14949035 = 22423553) B22423553
theorem B1555231 : Blo 1381510 1555231 := bstep (se 1 (by rfl) ⟨1166423, by rfl⟩ : syracuseStep 1555231 = 2332847) B2332847
theorem B10501487 : Blo 1381510 10501487 := bstep (se 1 (by rfl) ⟨7876115, by rfl⟩ : syracuseStep 10501487 = 15752231) B15752231
theorem B1597663 : Blo 1381510 1597663 := bstep (se 1 (by rfl) ⟨1198247, by rfl⟩ : syracuseStep 1597663 = 2396495) B2396495
theorem B2073071 : Blo 1381510 2073071 := bstep (se 1 (by rfl) ⟨1554803, by rfl⟩ : syracuseStep 2073071 = 3109607) B3109607
theorem B383353337 : Blo 1381510 383353337 := bstep (se 2 (by rfl) ⟨143757501, by rfl⟩ : syracuseStep 383353337 = 287515003) B287515003
theorem B18907937 : Blo 1381510 18907937 := bstep (se 2 (by rfl) ⟨7090476, by rfl⟩ : syracuseStep 18907937 = 14180953) B14180953
theorem B2073641 : Blo 1381510 2073641 := bstep (se 2 (by rfl) ⟨777615, by rfl⟩ : syracuseStep 2073641 = 1555231) B1555231
theorem B2073851 : Blo 1381510 2073851 := bstep (se 1 (by rfl) ⟨1555388, by rfl⟩ : syracuseStep 2073851 = 3110777) B3110777
theorem B2074319 : Blo 1381510 2074319 := bstep (se 1 (by rfl) ⟨1555739, by rfl⟩ : syracuseStep 2074319 = 3111479) B3111479
theorem B48564967 : Blo 1381510 48564967 := bstep (se 1 (by rfl) ⟨36423725, by rfl⟩ : syracuseStep 48564967 = 72847451) B72847451
theorem B2952143 : Blo 1381510 2952143 := bstep (se 1 (by rfl) ⟨2214107, by rfl⟩ : syracuseStep 2952143 = 4428215) B4428215
theorem B9966023 : Blo 1381510 9966023 := bstep (se 1 (by rfl) ⟨7474517, by rfl⟩ : syracuseStep 9966023 = 14949035) B14949035
theorem B7000991 : Blo 1381510 7000991 := bstep (se 1 (by rfl) ⟨5250743, by rfl⟩ : syracuseStep 7000991 = 10501487) B10501487
theorem B8975551 : Blo 1381510 8975551 := bstep (se 1 (by rfl) ⟨6731663, by rfl⟩ : syracuseStep 8975551 = 13463327) B13463327
theorem B2332651 : Blo 1381510 2332651 := bstep (se 1 (by rfl) ⟨1749488, by rfl⟩ : syracuseStep 2332651 = 3498977) B3498977
theorem B1660907 : Blo 1381510 1660907 := bstep (se 1 (by rfl) ⟨1245680, by rfl⟩ : syracuseStep 1660907 = 2491361) B2491361
theorem B2332793 : Blo 1381510 2332793 := bstep (se 2 (by rfl) ⟨874797, by rfl⟩ : syracuseStep 2332793 = 1749595) B1749595
theorem B3111119 : Blo 1381510 3111119 := bstep (se 1 (by rfl) ⟨2333339, by rfl⟩ : syracuseStep 3111119 = 4666679) B4666679
theorem B10492739 : Blo 1381510 10492739 := bstep (se 1 (by rfl) ⟨7869554, by rfl⟩ : syracuseStep 10492739 = 15739109) B15739109
theorem B1383391 : Blo 1381510 1383391 := bstep (se 1 (by rfl) ⟨1037543, by rfl⟩ : syracuseStep 1383391 = 2075087) B2075087
theorem B1555519 : Blo 1381510 1555519 := bstep (se 1 (by rfl) ⟨1166639, by rfl⟩ : syracuseStep 1555519 = 2333279) B2333279
theorem B3497033 : Blo 1381510 3497033 := bstep (se 2 (by rfl) ⟨1311387, by rfl⟩ : syracuseStep 3497033 = 2622775) B2622775
theorem B33611183 : Blo 1381510 33611183 := bstep (se 1 (by rfl) ⟨25208387, by rfl⟩ : syracuseStep 33611183 = 50416775) B50416775
theorem B2072411 : Blo 1381510 2072411 := bstep (se 1 (by rfl) ⟨1554308, by rfl⟩ : syracuseStep 2072411 = 3108617) B3108617
theorem B15744941 : Blo 1381510 15744941 := bstep (se 3 (by rfl) ⟨2952176, by rfl⟩ : syracuseStep 15744941 = 5904353) B5904353
theorem B6644015 : Blo 1381510 6644015 := bstep (se 1 (by rfl) ⟨4983011, by rfl⟩ : syracuseStep 6644015 = 9966023) B9966023
theorem B8520869 : Blo 1381510 8520869 := bstep (se 4 (by rfl) ⟨798831, by rfl⟩ : syracuseStep 8520869 = 1597663) B1597663
theorem B2074025 : Blo 1381510 2074025 := bstep (se 2 (by rfl) ⟨777759, by rfl⟩ : syracuseStep 2074025 = 1555519) B1555519
theorem B2074079 : Blo 1381510 2074079 := bstep (se 1 (by rfl) ⟨1555559, by rfl⟩ : syracuseStep 2074079 = 3111119) B3111119
theorem B1968095 : Blo 1381510 1968095 := bstep (se 1 (by rfl) ⟨1476071, by rfl⟩ : syracuseStep 1968095 = 2952143) B2952143
theorem B22407455 : Blo 1381510 22407455 := bstep (se 1 (by rfl) ⟨16805591, by rfl⟩ : syracuseStep 22407455 = 33611183) B33611183
theorem B10496627 : Blo 1381510 10496627 := bstep (se 1 (by rfl) ⟨7872470, by rfl⟩ : syracuseStep 10496627 = 15744941) B15744941
theorem B255568891 : Blo 1381510 255568891 := bstep (se 1 (by rfl) ⟨191676668, by rfl⟩ : syracuseStep 255568891 = 383353337) B383353337
theorem B64753289 : Blo 1381510 64753289 := bstep (se 2 (by rfl) ⟨24282483, by rfl⟩ : syracuseStep 64753289 = 48564967) B48564967
theorem B2331355 : Blo 1381510 2331355 := bstep (se 1 (by rfl) ⟨1748516, by rfl⟩ : syracuseStep 2331355 = 3497033) B3497033
theorem B1381607 : Blo 1381510 1381607 := bstep (se 1 (by rfl) ⟨1036205, by rfl⟩ : syracuseStep 1381607 = 2072411) B2072411
theorem B4429085 : Blo 1381510 4429085 := bstep (se 3 (by rfl) ⟨830453, by rfl⟩ : syracuseStep 4429085 = 1660907) B1660907
theorem B3110201 : Blo 1381510 3110201 := bstep (se 2 (by rfl) ⟨1166325, by rfl⟩ : syracuseStep 3110201 = 2332651) B2332651
theorem B1382047 : Blo 1381510 1382047 := bstep (se 1 (by rfl) ⟨1036535, by rfl⟩ : syracuseStep 1382047 = 2073071) B2073071
theorem B12605291 : Blo 1381510 12605291 := bstep (se 1 (by rfl) ⟨9453968, by rfl⟩ : syracuseStep 12605291 = 18907937) B18907937
theorem B4667327 : Blo 1381510 4667327 := bstep (se 1 (by rfl) ⟨3500495, by rfl⟩ : syracuseStep 4667327 = 7000991) B7000991
theorem B1382427 : Blo 1381510 1382427 := bstep (se 1 (by rfl) ⟨1036820, by rfl⟩ : syracuseStep 1382427 = 2073641) B2073641
theorem B1382567 : Blo 1381510 1382567 := bstep (se 1 (by rfl) ⟨1036925, by rfl⟩ : syracuseStep 1382567 = 2073851) B2073851
theorem B1382879 : Blo 1381510 1382879 := bstep (se 1 (by rfl) ⟨1037159, by rfl⟩ : syracuseStep 1382879 = 2074319) B2074319
theorem B1555195 : Blo 1381510 1555195 := bstep (se 1 (by rfl) ⟨1166396, by rfl⟩ : syracuseStep 1555195 = 2332793) B2332793
theorem B11967401 : Blo 1381510 11967401 := bstep (se 2 (by rfl) ⟨4487775, by rfl⟩ : syracuseStep 11967401 = 8975551) B8975551
theorem B6995159 : Blo 1381510 6995159 := bstep (se 1 (by rfl) ⟨5246369, by rfl⟩ : syracuseStep 6995159 = 10492739) B10492739
theorem B59753213 : Blo 1381510 59753213 := bstep (se 3 (by rfl) ⟨11203727, by rfl⟩ : syracuseStep 59753213 = 22407455) B22407455
theorem B2073467 : Blo 1381510 2073467 := bstep (se 1 (by rfl) ⟨1555100, by rfl⟩ : syracuseStep 2073467 = 3110201) B3110201
theorem B2073593 : Blo 1381510 2073593 := bstep (se 2 (by rfl) ⟨777597, by rfl⟩ : syracuseStep 2073593 = 1555195) B1555195
theorem B6997751 : Blo 1381510 6997751 := bstep (se 1 (by rfl) ⟨5248313, by rfl⟩ : syracuseStep 6997751 = 10496627) B10496627
theorem B4663439 : Blo 1381510 4663439 := bstep (se 1 (by rfl) ⟨3497579, by rfl⟩ : syracuseStep 4663439 = 6995159) B6995159
theorem B5680579 : Blo 1381510 5680579 := bstep (se 1 (by rfl) ⟨4260434, by rfl⟩ : syracuseStep 5680579 = 8520869) B8520869
theorem B3108473 : Blo 1381510 3108473 := bstep (se 2 (by rfl) ⟨1165677, by rfl⟩ : syracuseStep 3108473 = 2331355) B2331355
theorem B340758521 : Blo 1381510 340758521 := bstep (se 2 (by rfl) ⟨127784445, by rfl⟩ : syracuseStep 340758521 = 255568891) B255568891
theorem B43168859 : Blo 1381510 43168859 := bstep (se 1 (by rfl) ⟨32376644, by rfl⟩ : syracuseStep 43168859 = 64753289) B64753289
theorem B5248253 : Blo 1381510 5248253 := bstep (se 3 (by rfl) ⟨984047, by rfl⟩ : syracuseStep 5248253 = 1968095) B1968095
theorem B4429343 : Blo 1381510 4429343 := bstep (se 1 (by rfl) ⟨3322007, by rfl⟩ : syracuseStep 4429343 = 6644015) B6644015
theorem B11810893 : Blo 1381510 11810893 := bstep (se 3 (by rfl) ⟨2214542, by rfl⟩ : syracuseStep 11810893 = 4429085) B4429085
theorem B1382683 : Blo 1381510 1382683 := bstep (se 1 (by rfl) ⟨1037012, by rfl⟩ : syracuseStep 1382683 = 2074025) B2074025
theorem B1382719 : Blo 1381510 1382719 := bstep (se 1 (by rfl) ⟨1037039, by rfl⟩ : syracuseStep 1382719 = 2074079) B2074079
theorem B8403527 : Blo 1381510 8403527 := bstep (se 1 (by rfl) ⟨6302645, by rfl⟩ : syracuseStep 8403527 = 12605291) B12605291
theorem B3111551 : Blo 1381510 3111551 := bstep (se 1 (by rfl) ⟨2333663, by rfl⟩ : syracuseStep 3111551 = 4667327) B4667327
theorem B7978267 : Blo 1381510 7978267 := bstep (se 1 (by rfl) ⟨5983700, by rfl⟩ : syracuseStep 7978267 = 11967401) B11967401
theorem B28779239 : Blo 1381510 28779239 := bstep (se 1 (by rfl) ⟨21584429, by rfl⟩ : syracuseStep 28779239 = 43168859) B43168859
theorem B3498835 : Blo 1381510 3498835 := bstep (se 1 (by rfl) ⟨2624126, by rfl⟩ : syracuseStep 3498835 = 5248253) B5248253
theorem B2074367 : Blo 1381510 2074367 := bstep (se 1 (by rfl) ⟨1555775, by rfl⟩ : syracuseStep 2074367 = 3111551) B3111551
theorem B15747857 : Blo 1381510 15747857 := bstep (se 2 (by rfl) ⟨5905446, by rfl⟩ : syracuseStep 15747857 = 11810893) B11810893
theorem B2952895 : Blo 1381510 2952895 := bstep (se 1 (by rfl) ⟨2214671, by rfl⟩ : syracuseStep 2952895 = 4429343) B4429343
theorem B4665167 : Blo 1381510 4665167 := bstep (se 1 (by rfl) ⟨3498875, by rfl⟩ : syracuseStep 4665167 = 6997751) B6997751
theorem B3108959 : Blo 1381510 3108959 := bstep (se 1 (by rfl) ⟨2331719, by rfl⟩ : syracuseStep 3108959 = 4663439) B4663439
theorem B22409405 : Blo 1381510 22409405 := bstep (se 3 (by rfl) ⟨4201763, by rfl⟩ : syracuseStep 22409405 = 8403527) B8403527
theorem B10637689 : Blo 1381510 10637689 := bstep (se 2 (by rfl) ⟨3989133, by rfl⟩ : syracuseStep 10637689 = 7978267) B7978267
theorem B7574105 : Blo 1381510 7574105 := bstep (se 2 (by rfl) ⟨2840289, by rfl⟩ : syracuseStep 7574105 = 5680579) B5680579
theorem B39835475 : Blo 1381510 39835475 := bstep (se 1 (by rfl) ⟨29876606, by rfl⟩ : syracuseStep 39835475 = 59753213) B59753213
theorem B1382311 : Blo 1381510 1382311 := bstep (se 1 (by rfl) ⟨1036733, by rfl⟩ : syracuseStep 1382311 = 2073467) B2073467
theorem B1382395 : Blo 1381510 1382395 := bstep (se 1 (by rfl) ⟨1036796, by rfl⟩ : syracuseStep 1382395 = 2073593) B2073593
theorem B2072315 : Blo 1381510 2072315 := bstep (se 1 (by rfl) ⟨1554236, by rfl⟩ : syracuseStep 2072315 = 3108473) B3108473
theorem B227172347 : Blo 1381510 227172347 := bstep (se 1 (by rfl) ⟨170379260, by rfl⟩ : syracuseStep 227172347 = 340758521) B340758521
theorem B2072639 : Blo 1381510 2072639 := bstep (se 1 (by rfl) ⟨1554479, by rfl⟩ : syracuseStep 2072639 = 3108959) B3108959
theorem B19186159 : Blo 1381510 19186159 := bstep (se 1 (by rfl) ⟨14389619, by rfl⟩ : syracuseStep 19186159 = 28779239) B28779239
theorem B151448231 : Blo 1381510 151448231 := bstep (se 1 (by rfl) ⟨113586173, by rfl⟩ : syracuseStep 151448231 = 227172347) B227172347
theorem B14183585 : Blo 1381510 14183585 := bstep (se 2 (by rfl) ⟨5318844, by rfl⟩ : syracuseStep 14183585 = 10637689) B10637689
theorem B4665113 : Blo 1381510 4665113 := bstep (se 2 (by rfl) ⟨1749417, by rfl⟩ : syracuseStep 4665113 = 3498835) B3498835
theorem B20197613 : Blo 1381510 20197613 := bstep (se 3 (by rfl) ⟨3787052, by rfl⟩ : syracuseStep 20197613 = 7574105) B7574105
theorem B10498571 : Blo 1381510 10498571 := bstep (se 1 (by rfl) ⟨7873928, by rfl⟩ : syracuseStep 10498571 = 15747857) B15747857
theorem B3937193 : Blo 1381510 3937193 := bstep (se 2 (by rfl) ⟨1476447, by rfl⟩ : syracuseStep 3937193 = 2952895) B2952895
theorem B1381543 : Blo 1381510 1381543 := bstep (se 1 (by rfl) ⟨1036157, by rfl⟩ : syracuseStep 1381543 = 2072315) B2072315
theorem B3110111 : Blo 1381510 3110111 := bstep (se 1 (by rfl) ⟨2332583, by rfl⟩ : syracuseStep 3110111 = 4665167) B4665167
theorem B14939603 : Blo 1381510 14939603 := bstep (se 1 (by rfl) ⟨11204702, by rfl⟩ : syracuseStep 14939603 = 22409405) B22409405
theorem B1382911 : Blo 1381510 1382911 := bstep (se 1 (by rfl) ⟨1037183, by rfl⟩ : syracuseStep 1382911 = 2074367) B2074367
theorem B26556983 : Blo 1381510 26556983 := bstep (se 1 (by rfl) ⟨19917737, by rfl⟩ : syracuseStep 26556983 = 39835475) B39835475
theorem B2073407 : Blo 1381510 2073407 := bstep (se 1 (by rfl) ⟨1555055, by rfl⟩ : syracuseStep 2073407 = 3110111) B3110111
theorem B17704655 : Blo 1381510 17704655 := bstep (se 1 (by rfl) ⟨13278491, by rfl⟩ : syracuseStep 17704655 = 26556983) B26556983
theorem B9455723 : Blo 1381510 9455723 := bstep (se 1 (by rfl) ⟨7091792, by rfl⟩ : syracuseStep 9455723 = 14183585) B14183585
theorem B6999047 : Blo 1381510 6999047 := bstep (se 1 (by rfl) ⟨5249285, by rfl⟩ : syracuseStep 6999047 = 10498571) B10498571
theorem B2624795 : Blo 1381510 2624795 := bstep (se 1 (by rfl) ⟨1968596, by rfl⟩ : syracuseStep 2624795 = 3937193) B3937193
theorem B3110075 : Blo 1381510 3110075 := bstep (se 1 (by rfl) ⟨2332556, by rfl⟩ : syracuseStep 3110075 = 4665113) B4665113
theorem B1381759 : Blo 1381510 1381759 := bstep (se 1 (by rfl) ⟨1036319, by rfl⟩ : syracuseStep 1381759 = 2072639) B2072639
theorem B13465075 : Blo 1381510 13465075 := bstep (se 1 (by rfl) ⟨10098806, by rfl⟩ : syracuseStep 13465075 = 20197613) B20197613
theorem B25581545 : Blo 1381510 25581545 := bstep (se 2 (by rfl) ⟨9593079, by rfl⟩ : syracuseStep 25581545 = 19186159) B19186159
theorem B9959735 : Blo 1381510 9959735 := bstep (se 1 (by rfl) ⟨7469801, by rfl⟩ : syracuseStep 9959735 = 14939603) B14939603
theorem B100965487 : Blo 1381510 100965487 := bstep (se 1 (by rfl) ⟨75724115, by rfl⟩ : syracuseStep 100965487 = 151448231) B151448231
theorem B2073383 : Blo 1381510 2073383 := bstep (se 1 (by rfl) ⟨1555037, by rfl⟩ : syracuseStep 2073383 = 3110075) B3110075
theorem B134620649 : Blo 1381510 134620649 := bstep (se 2 (by rfl) ⟨50482743, by rfl⟩ : syracuseStep 134620649 = 100965487) B100965487
theorem B6303815 : Blo 1381510 6303815 := bstep (se 1 (by rfl) ⟨4727861, by rfl⟩ : syracuseStep 6303815 = 9455723) B9455723
theorem B6639823 : Blo 1381510 6639823 := bstep (se 1 (by rfl) ⟨4979867, by rfl⟩ : syracuseStep 6639823 = 9959735) B9959735
theorem B17953433 : Blo 1381510 17953433 := bstep (se 2 (by rfl) ⟨6732537, by rfl⟩ : syracuseStep 17953433 = 13465075) B13465075
theorem B4666031 : Blo 1381510 4666031 := bstep (se 1 (by rfl) ⟨3499523, by rfl⟩ : syracuseStep 4666031 = 6999047) B6999047
theorem B1749863 : Blo 1381510 1749863 := bstep (se 1 (by rfl) ⟨1312397, by rfl⟩ : syracuseStep 1749863 = 2624795) B2624795
theorem B1382271 : Blo 1381510 1382271 := bstep (se 1 (by rfl) ⟨1036703, by rfl⟩ : syracuseStep 1382271 = 2073407) B2073407
theorem B11803103 : Blo 1381510 11803103 := bstep (se 1 (by rfl) ⟨8852327, by rfl⟩ : syracuseStep 11803103 = 17704655) B17704655
theorem B17054363 : Blo 1381510 17054363 := bstep (se 1 (by rfl) ⟨12790772, by rfl⟩ : syracuseStep 17054363 = 25581545) B25581545
theorem B4202543 : Blo 1381510 4202543 := bstep (se 1 (by rfl) ⟨3151907, by rfl⟩ : syracuseStep 4202543 = 6303815) B6303815
theorem B11968955 : Blo 1381510 11968955 := bstep (se 1 (by rfl) ⟨8976716, by rfl⟩ : syracuseStep 11968955 = 17953433) B17953433
theorem B89747099 : Blo 1381510 89747099 := bstep (se 1 (by rfl) ⟨67310324, by rfl⟩ : syracuseStep 89747099 = 134620649) B134620649
theorem B7868735 : Blo 1381510 7868735 := bstep (se 1 (by rfl) ⟨5901551, by rfl⟩ : syracuseStep 7868735 = 11803103) B11803103
theorem B4666301 : Blo 1381510 4666301 := bstep (se 3 (by rfl) ⟨874931, by rfl⟩ : syracuseStep 4666301 = 1749863) B1749863
theorem B8853097 : Blo 1381510 8853097 := bstep (se 2 (by rfl) ⟨3319911, by rfl⟩ : syracuseStep 8853097 = 6639823) B6639823
theorem B3110687 : Blo 1381510 3110687 := bstep (se 1 (by rfl) ⟨2333015, by rfl⟩ : syracuseStep 3110687 = 4666031) B4666031
theorem B1382255 : Blo 1381510 1382255 := bstep (se 1 (by rfl) ⟨1036691, by rfl⟩ : syracuseStep 1382255 = 2073383) B2073383
theorem B11369575 : Blo 1381510 11369575 := bstep (se 1 (by rfl) ⟨8527181, by rfl⟩ : syracuseStep 11369575 = 17054363) B17054363
theorem B11206781 : Blo 1381510 11206781 := bstep (se 3 (by rfl) ⟨2101271, by rfl⟩ : syracuseStep 11206781 = 4202543) B4202543
theorem B7979303 : Blo 1381510 7979303 := bstep (se 1 (by rfl) ⟨5984477, by rfl⟩ : syracuseStep 7979303 = 11968955) B11968955
theorem B2073791 : Blo 1381510 2073791 := bstep (se 1 (by rfl) ⟨1555343, by rfl⟩ : syracuseStep 2073791 = 3110687) B3110687
theorem B5245823 : Blo 1381510 5245823 := bstep (se 1 (by rfl) ⟨3934367, by rfl⟩ : syracuseStep 5245823 = 7868735) B7868735
theorem B15159433 : Blo 1381510 15159433 := bstep (se 2 (by rfl) ⟨5684787, by rfl⟩ : syracuseStep 15159433 = 11369575) B11369575
theorem B59831399 : Blo 1381510 59831399 := bstep (se 1 (by rfl) ⟨44873549, by rfl⟩ : syracuseStep 59831399 = 89747099) B89747099
theorem B3110867 : Blo 1381510 3110867 := bstep (se 1 (by rfl) ⟨2333150, by rfl⟩ : syracuseStep 3110867 = 4666301) B4666301
theorem B11804129 : Blo 1381510 11804129 := bstep (se 2 (by rfl) ⟨4426548, by rfl⟩ : syracuseStep 11804129 = 8853097) B8853097
theorem B7471187 : Blo 1381510 7471187 := bstep (se 1 (by rfl) ⟨5603390, by rfl⟩ : syracuseStep 7471187 = 11206781) B11206781
theorem B39887599 : Blo 1381510 39887599 := bstep (se 1 (by rfl) ⟨29915699, by rfl⟩ : syracuseStep 39887599 = 59831399) B59831399
theorem B2073911 : Blo 1381510 2073911 := bstep (se 1 (by rfl) ⟨1555433, by rfl⟩ : syracuseStep 2073911 = 3110867) B3110867
theorem B20212577 : Blo 1381510 20212577 := bstep (se 2 (by rfl) ⟨7579716, by rfl⟩ : syracuseStep 20212577 = 15159433) B15159433
theorem B21278141 : Blo 1381510 21278141 := bstep (se 3 (by rfl) ⟨3989651, by rfl⟩ : syracuseStep 21278141 = 7979303) B7979303
theorem B7869419 : Blo 1381510 7869419 := bstep (se 1 (by rfl) ⟨5902064, by rfl⟩ : syracuseStep 7869419 = 11804129) B11804129
theorem B1382527 : Blo 1381510 1382527 := bstep (se 1 (by rfl) ⟨1036895, by rfl⟩ : syracuseStep 1382527 = 2073791) B2073791
theorem B3497215 : Blo 1381510 3497215 := bstep (se 1 (by rfl) ⟨2622911, by rfl⟩ : syracuseStep 3497215 = 5245823) B5245823
theorem B4980791 : Blo 1381510 4980791 := bstep (se 1 (by rfl) ⟨3735593, by rfl⟩ : syracuseStep 4980791 = 7471187) B7471187
theorem B53183465 : Blo 1381510 53183465 := bstep (se 2 (by rfl) ⟨19943799, by rfl⟩ : syracuseStep 53183465 = 39887599) B39887599
theorem B4662953 : Blo 1381510 4662953 := bstep (se 2 (by rfl) ⟨1748607, by rfl⟩ : syracuseStep 4662953 = 3497215) B3497215
theorem B5246279 : Blo 1381510 5246279 := bstep (se 1 (by rfl) ⟨3934709, by rfl⟩ : syracuseStep 5246279 = 7869419) B7869419
theorem B14185427 : Blo 1381510 14185427 := bstep (se 1 (by rfl) ⟨10639070, by rfl⟩ : syracuseStep 14185427 = 21278141) B21278141
theorem B1382607 : Blo 1381510 1382607 := bstep (se 1 (by rfl) ⟨1036955, by rfl⟩ : syracuseStep 1382607 = 2073911) B2073911
theorem B13475051 : Blo 1381510 13475051 := bstep (se 1 (by rfl) ⟨10106288, by rfl⟩ : syracuseStep 13475051 = 20212577) B20212577
theorem B35455643 : Blo 1381510 35455643 := bstep (se 1 (by rfl) ⟨26591732, by rfl⟩ : syracuseStep 35455643 = 53183465) B53183465
theorem B3320527 : Blo 1381510 3320527 := bstep (se 1 (by rfl) ⟨2490395, by rfl⟩ : syracuseStep 3320527 = 4980791) B4980791
theorem B3108635 : Blo 1381510 3108635 := bstep (se 1 (by rfl) ⟨2331476, by rfl⟩ : syracuseStep 3108635 = 4662953) B4662953
theorem B8983367 : Blo 1381510 8983367 := bstep (se 1 (by rfl) ⟨6737525, by rfl⟩ : syracuseStep 8983367 = 13475051) B13475051
theorem B37827805 : Blo 1381510 37827805 := bstep (se 3 (by rfl) ⟨7092713, by rfl⟩ : syracuseStep 37827805 = 14185427) B14185427
theorem B3497519 : Blo 1381510 3497519 := bstep (se 1 (by rfl) ⟨2623139, by rfl⟩ : syracuseStep 3497519 = 5246279) B5246279
theorem B5988911 : Blo 1381510 5988911 := bstep (se 1 (by rfl) ⟨4491683, by rfl⟩ : syracuseStep 5988911 = 8983367) B8983367
theorem B23637095 : Blo 1381510 23637095 := bstep (se 1 (by rfl) ⟨17727821, by rfl⟩ : syracuseStep 23637095 = 35455643) B35455643
theorem B4427369 : Blo 1381510 4427369 := bstep (se 2 (by rfl) ⟨1660263, by rfl⟩ : syracuseStep 4427369 = 3320527) B3320527
theorem B2331679 : Blo 1381510 2331679 := bstep (se 1 (by rfl) ⟨1748759, by rfl⟩ : syracuseStep 2331679 = 3497519) B3497519
theorem B50437073 : Blo 1381510 50437073 := bstep (se 2 (by rfl) ⟨18913902, by rfl⟩ : syracuseStep 50437073 = 37827805) B37827805
theorem B2072423 : Blo 1381510 2072423 := bstep (se 1 (by rfl) ⟨1554317, by rfl⟩ : syracuseStep 2072423 = 3108635) B3108635
theorem B2951579 : Blo 1381510 2951579 := bstep (se 1 (by rfl) ⟨2213684, by rfl⟩ : syracuseStep 2951579 = 4427369) B4427369
theorem B3108905 : Blo 1381510 3108905 := bstep (se 2 (by rfl) ⟨1165839, by rfl⟩ : syracuseStep 3108905 = 2331679) B2331679
theorem B15970429 : Blo 1381510 15970429 := bstep (se 3 (by rfl) ⟨2994455, by rfl⟩ : syracuseStep 15970429 = 5988911) B5988911
theorem B33624715 : Blo 1381510 33624715 := bstep (se 1 (by rfl) ⟨25218536, by rfl⟩ : syracuseStep 33624715 = 50437073) B50437073
theorem B15758063 : Blo 1381510 15758063 := bstep (se 1 (by rfl) ⟨11818547, by rfl⟩ : syracuseStep 15758063 = 23637095) B23637095
theorem B1381615 : Blo 1381510 1381615 := bstep (se 1 (by rfl) ⟨1036211, by rfl⟩ : syracuseStep 1381615 = 2072423) B2072423
theorem B2072603 : Blo 1381510 2072603 := bstep (se 1 (by rfl) ⟨1554452, by rfl⟩ : syracuseStep 2072603 = 3108905) B3108905
theorem B10505375 : Blo 1381510 10505375 := bstep (se 1 (by rfl) ⟨7879031, by rfl⟩ : syracuseStep 10505375 = 15758063) B15758063
theorem B85175621 : Blo 1381510 85175621 := bstep (se 4 (by rfl) ⟨7985214, by rfl⟩ : syracuseStep 85175621 = 15970429) B15970429
theorem B44832953 : Blo 1381510 44832953 := bstep (se 2 (by rfl) ⟨16812357, by rfl⟩ : syracuseStep 44832953 = 33624715) B33624715
theorem B7870877 : Blo 1381510 7870877 := bstep (se 3 (by rfl) ⟨1475789, by rfl⟩ : syracuseStep 7870877 = 2951579) B2951579
theorem B29888635 : Blo 1381510 29888635 := bstep (se 1 (by rfl) ⟨22416476, by rfl⟩ : syracuseStep 29888635 = 44832953) B44832953
theorem B5247251 : Blo 1381510 5247251 := bstep (se 1 (by rfl) ⟨3935438, by rfl⟩ : syracuseStep 5247251 = 7870877) B7870877
theorem B56783747 : Blo 1381510 56783747 := bstep (se 1 (by rfl) ⟨42587810, by rfl⟩ : syracuseStep 56783747 = 85175621) B85175621
theorem B1381735 : Blo 1381510 1381735 := bstep (se 1 (by rfl) ⟨1036301, by rfl⟩ : syracuseStep 1381735 = 2072603) B2072603
theorem B7003583 : Blo 1381510 7003583 := bstep (se 1 (by rfl) ⟨5252687, by rfl⟩ : syracuseStep 7003583 = 10505375) B10505375
theorem B3498167 : Blo 1381510 3498167 := bstep (se 1 (by rfl) ⟨2623625, by rfl⟩ : syracuseStep 3498167 = 5247251) B5247251
theorem B37855831 : Blo 1381510 37855831 := bstep (se 1 (by rfl) ⟨28391873, by rfl⟩ : syracuseStep 37855831 = 56783747) B56783747
theorem B39851513 : Blo 1381510 39851513 := bstep (se 2 (by rfl) ⟨14944317, by rfl⟩ : syracuseStep 39851513 = 29888635) B29888635
theorem B4669055 : Blo 1381510 4669055 := bstep (se 1 (by rfl) ⟨3501791, by rfl⟩ : syracuseStep 4669055 = 7003583) B7003583
theorem B26567675 : Blo 1381510 26567675 := bstep (se 1 (by rfl) ⟨19925756, by rfl⟩ : syracuseStep 26567675 = 39851513) B39851513
theorem B50474441 : Blo 1381510 50474441 := bstep (se 2 (by rfl) ⟨18927915, by rfl⟩ : syracuseStep 50474441 = 37855831) B37855831
theorem B2332111 : Blo 1381510 2332111 := bstep (se 1 (by rfl) ⟨1749083, by rfl⟩ : syracuseStep 2332111 = 3498167) B3498167
theorem B3112703 : Blo 1381510 3112703 := bstep (se 1 (by rfl) ⟨2334527, by rfl⟩ : syracuseStep 3112703 = 4669055) B4669055
theorem B17711783 : Blo 1381510 17711783 := bstep (se 1 (by rfl) ⟨13283837, by rfl⟩ : syracuseStep 17711783 = 26567675) B26567675
theorem B2075135 : Blo 1381510 2075135 := bstep (se 1 (by rfl) ⟨1556351, by rfl⟩ : syracuseStep 2075135 = 3112703) B3112703
theorem B3109481 : Blo 1381510 3109481 := bstep (se 2 (by rfl) ⟨1166055, by rfl⟩ : syracuseStep 3109481 = 2332111) B2332111
theorem B33649627 : Blo 1381510 33649627 := bstep (se 1 (by rfl) ⟨25237220, by rfl⟩ : syracuseStep 33649627 = 50474441) B50474441
theorem B2072987 : Blo 1381510 2072987 := bstep (se 1 (by rfl) ⟨1554740, by rfl⟩ : syracuseStep 2072987 = 3109481) B3109481
theorem B11807855 : Blo 1381510 11807855 := bstep (se 1 (by rfl) ⟨8855891, by rfl⟩ : syracuseStep 11807855 = 17711783) B17711783
theorem B44866169 : Blo 1381510 44866169 := bstep (se 2 (by rfl) ⟨16824813, by rfl⟩ : syracuseStep 44866169 = 33649627) B33649627
theorem B1383423 : Blo 1381510 1383423 := bstep (se 1 (by rfl) ⟨1037567, by rfl⟩ : syracuseStep 1383423 = 2075135) B2075135
theorem B29910779 : Blo 1381510 29910779 := bstep (se 1 (by rfl) ⟨22433084, by rfl⟩ : syracuseStep 29910779 = 44866169) B44866169
theorem B1381991 : Blo 1381510 1381991 := bstep (se 1 (by rfl) ⟨1036493, by rfl⟩ : syracuseStep 1381991 = 2072987) B2072987
theorem B7871903 : Blo 1381510 7871903 := bstep (se 1 (by rfl) ⟨5903927, by rfl⟩ : syracuseStep 7871903 = 11807855) B11807855
theorem B19940519 : Blo 1381510 19940519 := bstep (se 1 (by rfl) ⟨14955389, by rfl⟩ : syracuseStep 19940519 = 29910779) B29910779
theorem B5247935 : Blo 1381510 5247935 := bstep (se 1 (by rfl) ⟨3935951, by rfl⟩ : syracuseStep 5247935 = 7871903) B7871903
theorem B3498623 : Blo 1381510 3498623 := bstep (se 1 (by rfl) ⟨2623967, by rfl⟩ : syracuseStep 3498623 = 5247935) B5247935
theorem B13293679 : Blo 1381510 13293679 := bstep (se 1 (by rfl) ⟨9970259, by rfl⟩ : syracuseStep 13293679 = 19940519) B19940519
theorem B17724905 : Blo 1381510 17724905 := bstep (se 2 (by rfl) ⟨6646839, by rfl⟩ : syracuseStep 17724905 = 13293679) B13293679
theorem B2332415 : Blo 1381510 2332415 := bstep (se 1 (by rfl) ⟨1749311, by rfl⟩ : syracuseStep 2332415 = 3498623) B3498623
theorem B11816603 : Blo 1381510 11816603 := bstep (se 1 (by rfl) ⟨8862452, by rfl⟩ : syracuseStep 11816603 = 17724905) B17724905
theorem B1554943 : Blo 1381510 1554943 := bstep (se 1 (by rfl) ⟨1166207, by rfl⟩ : syracuseStep 1554943 = 2332415) B2332415
theorem B2073257 : Blo 1381510 2073257 := bstep (se 2 (by rfl) ⟨777471, by rfl⟩ : syracuseStep 2073257 = 1554943) B1554943
theorem B7877735 : Blo 1381510 7877735 := bstep (se 1 (by rfl) ⟨5908301, by rfl⟩ : syracuseStep 7877735 = 11816603) B11816603
theorem B5251823 : Blo 1381510 5251823 := bstep (se 1 (by rfl) ⟨3938867, by rfl⟩ : syracuseStep 5251823 = 7877735) B7877735
theorem B1382171 : Blo 1381510 1382171 := bstep (se 1 (by rfl) ⟨1036628, by rfl⟩ : syracuseStep 1382171 = 2073257) B2073257
theorem B3501215 : Blo 1381510 3501215 := bstep (se 1 (by rfl) ⟨2625911, by rfl⟩ : syracuseStep 3501215 = 5251823) B5251823
theorem B2334143 : Blo 1381510 2334143 := bstep (se 1 (by rfl) ⟨1750607, by rfl⟩ : syracuseStep 2334143 = 3501215) B3501215
theorem B1556095 : Blo 1381510 1556095 := bstep (se 1 (by rfl) ⟨1167071, by rfl⟩ : syracuseStep 1556095 = 2334143) B2334143
theorem B2074793 : Blo 1381510 2074793 := bstep (se 2 (by rfl) ⟨778047, by rfl⟩ : syracuseStep 2074793 = 1556095) B1556095
theorem B1383195 : Blo 1381510 1383195 := bstep (se 1 (by rfl) ⟨1037396, by rfl⟩ : syracuseStep 1383195 = 2074793) B2074793

theorem C0 (j : ℕ) (h1 : 345377 ≤ j) (h2 : j ≤ 345876) : Blo 1381510 (4 * j + 3) := by
  interval_cases j
  · exact B1381511
  · exact B1381515
  · exact B1381519
  · exact B1381523
  · exact B1381527
  · exact B1381531
  · exact B1381535
  · exact B1381539
  · exact B1381543
  · exact B1381547
  · exact B1381551
  · exact B1381555
  · exact B1381559
  · exact B1381563
  · exact B1381567
  · exact B1381571
  · exact B1381575
  · exact B1381579
  · exact B1381583
  · exact B1381587
  · exact B1381591
  · exact B1381595
  · exact B1381599
  · exact B1381603
  · exact B1381607
  · exact B1381611
  · exact B1381615
  · exact B1381619
  · exact B1381623
  · exact B1381627
  · exact B1381631
  · exact B1381635
  · exact B1381639
  · exact B1381643
  · exact B1381647
  · exact B1381651
  · exact B1381655
  · exact B1381659
  · exact B1381663
  · exact B1381667
  · exact B1381671
  · exact B1381675
  · exact B1381679
  · exact B1381683
  · exact B1381687
  · exact B1381691
  · exact B1381695
  · exact B1381699
  · exact B1381703
  · exact B1381707
  · exact B1381711
  · exact B1381715
  · exact B1381719
  · exact B1381723
  · exact B1381727
  · exact B1381731
  · exact B1381735
  · exact B1381739
  · exact B1381743
  · exact B1381747
  · exact B1381751
  · exact B1381755
  · exact B1381759
  · exact B1381763
  · exact B1381767
  · exact B1381771
  · exact B1381775
  · exact B1381779
  · exact B1381783
  · exact B1381787
  · exact B1381791
  · exact B1381795
  · exact B1381799
  · exact B1381803
  · exact B1381807
  · exact B1381811
  · exact B1381815
  · exact B1381819
  · exact B1381823
  · exact B1381827
  · exact B1381831
  · exact B1381835
  · exact B1381839
  · exact B1381843
  · exact B1381847
  · exact B1381851
  · exact B1381855
  · exact B1381859
  · exact B1381863
  · exact B1381867
  · exact B1381871
  · exact B1381875
  · exact B1381879
  · exact B1381883
  · exact B1381887
  · exact B1381891
  · exact B1381895
  · exact B1381899
  · exact B1381903
  · exact B1381907
  · exact B1381911
  · exact B1381915
  · exact B1381919
  · exact B1381923
  · exact B1381927
  · exact B1381931
  · exact B1381935
  · exact B1381939
  · exact B1381943
  · exact B1381947
  · exact B1381951
  · exact B1381955
  · exact B1381959
  · exact B1381963
  · exact B1381967
  · exact B1381971
  · exact B1381975
  · exact B1381979
  · exact B1381983
  · exact B1381987
  · exact B1381991
  · exact B1381995
  · exact B1381999
  · exact B1382003
  · exact B1382007
  · exact B1382011
  · exact B1382015
  · exact B1382019
  · exact B1382023
  · exact B1382027
  · exact B1382031
  · exact B1382035
  · exact B1382039
  · exact B1382043
  · exact B1382047
  · exact B1382051
  · exact B1382055
  · exact B1382059
  · exact B1382063
  · exact B1382067
  · exact B1382071
  · exact B1382075
  · exact B1382079
  · exact B1382083
  · exact B1382087
  · exact B1382091
  · exact B1382095
  · exact B1382099
  · exact B1382103
  · exact B1382107
  · exact B1382111
  · exact B1382115
  · exact B1382119
  · exact B1382123
  · exact B1382127
  · exact B1382131
  · exact B1382135
  · exact B1382139
  · exact B1382143
  · exact B1382147
  · exact B1382151
  · exact B1382155
  · exact B1382159
  · exact B1382163
  · exact B1382167
  · exact B1382171
  · exact B1382175
  · exact B1382179
  · exact B1382183
  · exact B1382187
  · exact B1382191
  · exact B1382195
  · exact B1382199
  · exact B1382203
  · exact B1382207
  · exact B1382211
  · exact B1382215
  · exact B1382219
  · exact B1382223
  · exact B1382227
  · exact B1382231
  · exact B1382235
  · exact B1382239
  · exact B1382243
  · exact B1382247
  · exact B1382251
  · exact B1382255
  · exact B1382259
  · exact B1382263
  · exact B1382267
  · exact B1382271
  · exact B1382275
  · exact B1382279
  · exact B1382283
  · exact B1382287
  · exact B1382291
  · exact B1382295
  · exact B1382299
  · exact B1382303
  · exact B1382307
  · exact B1382311
  · exact B1382315
  · exact B1382319
  · exact B1382323
  · exact B1382327
  · exact B1382331
  · exact B1382335
  · exact B1382339
  · exact B1382343
  · exact B1382347
  · exact B1382351
  · exact B1382355
  · exact B1382359
  · exact B1382363
  · exact B1382367
  · exact B1382371
  · exact B1382375
  · exact B1382379
  · exact B1382383
  · exact B1382387
  · exact B1382391
  · exact B1382395
  · exact B1382399
  · exact B1382403
  · exact B1382407
  · exact B1382411
  · exact B1382415
  · exact B1382419
  · exact B1382423
  · exact B1382427
  · exact B1382431
  · exact B1382435
  · exact B1382439
  · exact B1382443
  · exact B1382447
  · exact B1382451
  · exact B1382455
  · exact B1382459
  · exact B1382463
  · exact B1382467
  · exact B1382471
  · exact B1382475
  · exact B1382479
  · exact B1382483
  · exact B1382487
  · exact B1382491
  · exact B1382495
  · exact B1382499
  · exact B1382503
  · exact B1382507
  · exact B1382511
  · exact B1382515
  · exact B1382519
  · exact B1382523
  · exact B1382527
  · exact B1382531
  · exact B1382535
  · exact B1382539
  · exact B1382543
  · exact B1382547
  · exact B1382551
  · exact B1382555
  · exact B1382559
  · exact B1382563
  · exact B1382567
  · exact B1382571
  · exact B1382575
  · exact B1382579
  · exact B1382583
  · exact B1382587
  · exact B1382591
  · exact B1382595
  · exact B1382599
  · exact B1382603
  · exact B1382607
  · exact B1382611
  · exact B1382615
  · exact B1382619
  · exact B1382623
  · exact B1382627
  · exact B1382631
  · exact B1382635
  · exact B1382639
  · exact B1382643
  · exact B1382647
  · exact B1382651
  · exact B1382655
  · exact B1382659
  · exact B1382663
  · exact B1382667
  · exact B1382671
  · exact B1382675
  · exact B1382679
  · exact B1382683
  · exact B1382687
  · exact B1382691
  · exact B1382695
  · exact B1382699
  · exact B1382703
  · exact B1382707
  · exact B1382711
  · exact B1382715
  · exact B1382719
  · exact B1382723
  · exact B1382727
  · exact B1382731
  · exact B1382735
  · exact B1382739
  · exact B1382743
  · exact B1382747
  · exact B1382751
  · exact B1382755
  · exact B1382759
  · exact B1382763
  · exact B1382767
  · exact B1382771
  · exact B1382775
  · exact B1382779
  · exact B1382783
  · exact B1382787
  · exact B1382791
  · exact B1382795
  · exact B1382799
  · exact B1382803
  · exact B1382807
  · exact B1382811
  · exact B1382815
  · exact B1382819
  · exact B1382823
  · exact B1382827
  · exact B1382831
  · exact B1382835
  · exact B1382839
  · exact B1382843
  · exact B1382847
  · exact B1382851
  · exact B1382855
  · exact B1382859
  · exact B1382863
  · exact B1382867
  · exact B1382871
  · exact B1382875
  · exact B1382879
  · exact B1382883
  · exact B1382887
  · exact B1382891
  · exact B1382895
  · exact B1382899
  · exact B1382903
  · exact B1382907
  · exact B1382911
  · exact B1382915
  · exact B1382919
  · exact B1382923
  · exact B1382927
  · exact B1382931
  · exact B1382935
  · exact B1382939
  · exact B1382943
  · exact B1382947
  · exact B1382951
  · exact B1382955
  · exact B1382959
  · exact B1382963
  · exact B1382967
  · exact B1382971
  · exact B1382975
  · exact B1382979
  · exact B1382983
  · exact B1382987
  · exact B1382991
  · exact B1382995
  · exact B1382999
  · exact B1383003
  · exact B1383007
  · exact B1383011
  · exact B1383015
  · exact B1383019
  · exact B1383023
  · exact B1383027
  · exact B1383031
  · exact B1383035
  · exact B1383039
  · exact B1383043
  · exact B1383047
  · exact B1383051
  · exact B1383055
  · exact B1383059
  · exact B1383063
  · exact B1383067
  · exact B1383071
  · exact B1383075
  · exact B1383079
  · exact B1383083
  · exact B1383087
  · exact B1383091
  · exact B1383095
  · exact B1383099
  · exact B1383103
  · exact B1383107
  · exact B1383111
  · exact B1383115
  · exact B1383119
  · exact B1383123
  · exact B1383127
  · exact B1383131
  · exact B1383135
  · exact B1383139
  · exact B1383143
  · exact B1383147
  · exact B1383151
  · exact B1383155
  · exact B1383159
  · exact B1383163
  · exact B1383167
  · exact B1383171
  · exact B1383175
  · exact B1383179
  · exact B1383183
  · exact B1383187
  · exact B1383191
  · exact B1383195
  · exact B1383199
  · exact B1383203
  · exact B1383207
  · exact B1383211
  · exact B1383215
  · exact B1383219
  · exact B1383223
  · exact B1383227
  · exact B1383231
  · exact B1383235
  · exact B1383239
  · exact B1383243
  · exact B1383247
  · exact B1383251
  · exact B1383255
  · exact B1383259
  · exact B1383263
  · exact B1383267
  · exact B1383271
  · exact B1383275
  · exact B1383279
  · exact B1383283
  · exact B1383287
  · exact B1383291
  · exact B1383295
  · exact B1383299
  · exact B1383303
  · exact B1383307
  · exact B1383311
  · exact B1383315
  · exact B1383319
  · exact B1383323
  · exact B1383327
  · exact B1383331
  · exact B1383335
  · exact B1383339
  · exact B1383343
  · exact B1383347
  · exact B1383351
  · exact B1383355
  · exact B1383359
  · exact B1383363
  · exact B1383367
  · exact B1383371
  · exact B1383375
  · exact B1383379
  · exact B1383383
  · exact B1383387
  · exact B1383391
  · exact B1383395
  · exact B1383399
  · exact B1383403
  · exact B1383407
  · exact B1383411
  · exact B1383415
  · exact B1383419
  · exact B1383423
  · exact B1383427
  · exact B1383431
  · exact B1383435
  · exact B1383439
  · exact B1383443
  · exact B1383447
  · exact B1383451
  · exact B1383455
  · exact B1383459
  · exact B1383463
  · exact B1383467
  · exact B1383471
  · exact B1383475
  · exact B1383479
  · exact B1383483
  · exact B1383487
  · exact B1383491
  · exact B1383495
  · exact B1383499
  · exact B1383503
  · exact B1383507

theorem solution (m : ℕ) (hlo : 1381510 ≤ m) (hhi : m ≤ 1383510) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 345377 ≤ j := by omega
    have hj2 : j ≤ 345876 := by omega
    have hb : Blo 1381510 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
